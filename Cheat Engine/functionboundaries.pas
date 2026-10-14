unit FunctionBoundaries;

{
Finds the function that contains a given code address.

Every non-leaf function in a 64-bit Windows module has an entry in the
exception directory (.pdata) of the PE file: a list of RUNTIME_FUNCTION records
(BeginAddress, EndAddress, UnwindInfoAddress, all RVA's) sorted on
BeginAddress. That list is read from the target process once per module and
cached, after which a lookup is a binary search.

Leaf functions (no stack frame, no calls) and 32-bit modules have no such
entries, so for those the lookup fails.
}

{$mode Delphi}

interface

uses
  Classes, SysUtils;

type
  TFunctionRange=record
    start: ptruint;
    stop: ptruint; //exclusive
  end;

function FindFunctionRange(address: ptruint; out range: TFunctionRange): boolean;
function GetFunctionDescription(address: ptruint): string;
procedure ClearFunctionRangeCache;

implementation

uses syncobjs, NewKernelHandler, ProcessHandlerUnit, symbolhandler, symbolhandlerstructs;

resourcestring
  rsUnknownFunction = '? (leaf or no unwind info)';

const
  UNW_FLAG_CHAININFO = 4;
  MAXCHAINDEPTH = 32;

type
  TRuntimeFunction=packed record
    BeginAddress: dword;
    EndAddress: dword;
    UnwindInfoAddress: dword;
  end;

  TModuleFunctionTable=record
    processhandle: THandle;
    base: ptruint;
    size: ptruint;
    entries: array of TRuntimeFunction;
  end;

var
  cache: array of TModuleFunctionTable;
  cachecs: TCriticalSection;

function ReadMemory(address: ptruint; buffer: pointer; size: integer): boolean;
var br: ptruint;
begin
  br:=0;
  result:=ReadProcessMemory(processhandle, pointer(address), buffer, size, br) and (br=ptruint(size));
end;

function LoadFunctionTable(base, size: ptruint; var table: TModuleFunctionTable): boolean;
var
  e_lfanew: dword;
  signature: dword;
  magic: word;
  numberOfRvaAndSizes: dword;
  dir: packed record
    va: dword;
    size: dword;
  end;
  optionalheader: ptruint;
  count: integer;
begin
  result:=false;
  table.processhandle:=processhandle;
  table.base:=base;
  table.size:=size;
  setlength(table.entries, 0);

  if not ReadMemory(base+$3c, @e_lfanew, 4) then exit;
  if (e_lfanew=0) or (e_lfanew>$1000) then exit;

  if (not ReadMemory(base+e_lfanew, @signature, 4)) or (signature<>$00004550) then exit; //'PE'#0#0

  //the optional header follows the 4 byte signature and the 20 byte file header
  optionalheader:=base+e_lfanew+24;
  if (not ReadMemory(optionalheader, @magic, 2)) or (magic<>$20b) then exit; //only PE32+ has x64 unwind data

  //PE32+: NumberOfRvaAndSizes at 108, DataDirectory at 112, exception directory is entry 3
  if (not ReadMemory(optionalheader+108, @numberOfRvaAndSizes, 4)) or (numberOfRvaAndSizes<=3) then exit;
  if not ReadMemory(optionalheader+112+3*8, @dir, sizeof(dir)) then exit;
  if (dir.va=0) or (dir.size<sizeof(TRuntimeFunction)) or (dir.va>=size) then exit;

  count:=dir.size div sizeof(TRuntimeFunction);
  setlength(table.entries, count);
  if not ReadMemory(base+dir.va, @table.entries[0], count*sizeof(TRuntimeFunction)) then
  begin
    setlength(table.entries, 0);
    exit;
  end;

  result:=true;
end;

function GetFunctionTable(const mi: TModuleInfo): integer;
{
Returns the index in the cache of the table for this module, loading it if needed.
Must be called inside cachecs
}
var i: integer;
begin
  for i:=0 to length(cache)-1 do
    if (cache[i].base=mi.baseaddress) and (cache[i].processhandle=processhandle) then
      exit(i);

  //not loaded yet. Also cache failures (empty table) so they aren't retried every hit
  result:=length(cache);
  setlength(cache, result+1);
  LoadFunctionTable(mi.baseaddress, mi.basesize, cache[result]);
end;

function FindEntry(const table: TModuleFunctionTable; rva: dword): integer;
var l, h, m: integer;
begin
  result:=-1;
  l:=0;
  h:=length(table.entries)-1;
  while l<=h do
  begin
    m:=(l+h) div 2;
    if rva<table.entries[m].BeginAddress then
      h:=m-1
    else
    if rva>=table.entries[m].EndAddress then
      l:=m+1
    else
      exit(m);
  end;
end;

function FindFunctionRange(address: ptruint; out range: TFunctionRange): boolean;
var
  mi: TModuleInfo;
  tableindex, index, depth: integer;
  base: ptruint;
  entry: TRuntimeFunction;
  unwindheader: array [0..3] of byte;
begin
  result:=false;
  range.start:=0;
  range.stop:=0;

  if (symhandler=nil) or (not symhandler.getmodulebyaddress(address, mi)) then exit;
  if not mi.is64bitmodule then exit;

  base:=mi.baseaddress;

  cachecs.Enter;
  try
    tableindex:=GetFunctionTable(mi);
    index:=FindEntry(cache[tableindex], address-base);
    if index=-1 then exit;
    entry:=cache[tableindex].entries[index];
  finally
    cachecs.Leave;
  end;

  //a function can be split into several chunks. Follow the chain back to the primary entry
  for depth:=1 to MAXCHAINDEPTH do
  begin
    if (entry.UnwindInfoAddress and 1)<>0 then
    begin
      //the unwind info field points directly to another RUNTIME_FUNCTION
      if not ReadMemory(base+(entry.UnwindInfoAddress and (not dword(1))), @entry, sizeof(entry)) then break;
      continue;
    end;

    //UNWIND_INFO: byte 0 = version (3 bits) and flags (5 bits), byte 2 = number of unwind codes
    if not ReadMemory(base+entry.UnwindInfoAddress, @unwindheader, 4) then break;
    if ((unwindheader[0] shr 3) and UNW_FLAG_CHAININFO)=0 then break;

    //the chained RUNTIME_FUNCTION follows the unwind codes array (2 bytes per code, padded to an even count)
    if not ReadMemory(base+entry.UnwindInfoAddress+4+((unwindheader[2]+1) and (not 1))*2, @entry, sizeof(entry)) then break;
  end;

  range.start:=base+entry.BeginAddress;
  range.stop:=base+entry.EndAddress;
  result:=true;
end;

function GetFunctionDescription(address: ptruint): string;
var range: TFunctionRange;
begin
  if FindFunctionRange(address, range) then
    result:=symhandler.getNameFromAddress(range.start)+' +'+inttohex(address-range.start, 1)
  else
    result:=rsUnknownFunction;
end;

procedure ClearFunctionRangeCache;
begin
  cachecs.Enter;
  try
    setlength(cache, 0);
  finally
    cachecs.Leave;
  end;
end;

initialization
  cachecs:=TCriticalSection.Create;

finalization
  freeandnil(cachecs);

end.
