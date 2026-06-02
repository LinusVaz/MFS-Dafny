newtype {:nativeType "byte"}   byte   = b:int | 0 <= b < 256
newtype {:nativeType "ushort"} uint16 = i:int | 0 <= i < 0x10000
newtype {:nativeType "int"}    int32  = i:int | -0x80000000 <= i < 0x80000000
newtype {:nativeType "uint"}   uint32 = i:int | 0 <= i < 0x100000000
newtype {:nativeType "ulong"}  uint64 = i:int | 0 <= i < 0x10000000000000000
newtype {:nativeType "int"}     nat32 = i:int | 0 <= i < 0x80000000


class HostEnvironment
{
    ghost var constants:HostConstants?
    ghost var ok:OkState?
    ghost var files:FileSystemState?

    constructor {:axiom} () requires false
    {}

    ghost predicate Valid()
        reads this
    {
           constants != null && ok != null && files != null
    }

}

//////////////////////////////////////////////////////////////////////////////
// Per-host constants
//////////////////////////////////////////////////////////////////////////////

class HostConstants
{
    constructor{:axiom} () requires false
    {}

    // result of C# System.Environment.GetCommandLineArgs(); argument 0 is name of executable    
    ghost function {:axiom} CommandLineArgs():seq<seq<char>> reads this 

    static method {:axiom} {:extern} NumCommandLineArgs(ghost env:HostEnvironment) returns(n:uint32)
        requires env.Valid()
        ensures  n as int == |env.constants.CommandLineArgs()|

    static method {:axiom} {:extern} GetCommandLineArg(i:uint64, ghost env:HostEnvironment) returns(arg:array<char>)
        requires env.Valid()
        requires 0 <= i as int < |env.constants.CommandLineArgs()|
        ensures  fresh(arg)
        ensures  arg[..] == env.constants.CommandLineArgs()[i]
}


//////////////////////////////////////////////////////////////////////////////
// Failure
//////////////////////////////////////////////////////////////////////////////

// not failed; IO operations only allowed when ok() == true
class OkState
{
    constructor {:axiom} () requires false {}
    ghost function {:axiom} ok():bool reads this
}


//////////////////////////////////////////////////////////////////////////////
// File System
//////////////////////////////////////////////////////////////////////////////

class FileSystemState
{
    constructor {:axiom} () requires false {}
    ghost function {:axiom} state() : map<seq<char>,seq<byte>>   // File system maps file names (sequences of characters) to their contents
        reads this
}

class FileStream
{
    ghost var env:HostEnvironment
    ghost function {:axiom} Name():seq<char> reads this
    ghost function {:axiom} IsOpen():bool reads this
    constructor {:axiom} () requires false {}

    static method {:axiom} {:extern} FileExists(name:array<char>, ghost env:HostEnvironment?) returns(result:bool)
        requires env != null && env.Valid()
        requires env.ok.ok()
        ensures  result <==> old(name[..]) in env.files.state()        

    static method {:axiom} {:extern} FileLength(name:array<char>, ghost env:HostEnvironment) returns(success:bool, len:int32)
        requires env.Valid()
        requires env.ok.ok()
        requires name[..] in env.files.state()
        modifies env.ok
        ensures  env.ok.ok() == success
        ensures  success ==> len as int == |env.files.state()[name[..]]|

    static method {:axiom} {:extern} Open(name:array<char>, ghost env:HostEnvironment) returns(ok:bool, f:FileStream)
        requires env.Valid()
        requires env.ok.ok()
        modifies env.ok
        modifies env.files
        ensures  env.ok.ok() == ok        
        ensures  ok ==> fresh(f) && f.env == env && f.IsOpen() && f.Name() == name[..] &&          // FileStream object is initialized
                        env.files.state() == if name[..] in old(env.files.state()) then old(env.files.state())  // If the file exists, then the file contents are unchanged
                                             else old(env.files.state())[name[..] := []]                        // Otherwise, the file now exists with no content
        
    method {:axiom} {:extern} Close() returns(ok:bool)
        requires env.Valid()
        requires env.ok.ok()
        requires IsOpen()
        modifies this
        modifies env.ok
        ensures  env == old(env)
        ensures  env.ok.ok() == ok
        ensures  !IsOpen()

    method {:axiom} {:extern} Read(file_offset:nat32, buffer:array?<byte>, start:int32, num_bytes:int32) returns(ok:bool)      
        requires env.Valid()
        requires env.ok.ok()
        requires IsOpen()
        requires buffer != null
        requires Name() in env.files.state()
        requires file_offset as int + num_bytes as int <= |env.files.state()[Name()]|    // Don't read beyond the end of the file
        requires 0 <= start as int <= start as int + num_bytes as int <= buffer.Length   // Don't write outside the buffer        
        modifies this
        modifies env.ok
        modifies env.files
        modifies buffer
        ensures  env == old(env)
        ensures  env.ok.ok() == ok
        ensures  ok ==> env.files.state() == old(env.files.state())
        ensures  Name() == old(Name())
        ensures  ok ==> IsOpen()        
        ensures  ok ==> buffer[..] == buffer[..start] + env.files.state()[Name()][file_offset..file_offset as int + num_bytes as int] + buffer[start as int + num_bytes as int..]
            
    method {:axiom} {:extern} Write(file_offset:nat32, buffer:array?<byte>, start:int32, num_bytes:int32) returns(ok:bool)        
        requires env.Valid()
        requires env.ok.ok()
        requires IsOpen()
        requires buffer != null
        requires Name() in env.files.state()
        requires file_offset as int <= |env.files.state()[Name()]|  // Writes must start within existing content (no support for zero-extending the file)
        requires 0 <= start as int <= start as int + num_bytes as int <= buffer.Length  // Don't read outside the buffer
        modifies this
        modifies env.ok
        modifies env.files
        ensures  env == old(env)
        ensures  env.ok.ok() == ok
        ensures  Name() == old(Name())
        ensures  ok ==> IsOpen()                 
        ensures  ok ==> 
                  var old_file := old(env.files.state()[Name()]);
                  env.files.state() == old(env.files.state())[Name() := old_file[..file_offset] 
                                                                      + buffer[start..start as int + num_bytes as int] 
                                                                      + if file_offset as int + num_bytes as int > |old_file| then [] 
                                                                        else old_file[file_offset as int + num_bytes as int..]]

}

