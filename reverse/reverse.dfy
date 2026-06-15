/*
  Challenge 1: reverse the lines of a file.

  The program expects two file names. It only creates the destination file
  when the source exists and the destination does not already exist.

  In the specification a file is a sequence of bytes, so I use byte 10 as
  the newline character.
*/

include "Io.dfy"

const newline: byte := 10 as byte

// Returns the index where the last line starts.
function LastLineStart(contents: seq<byte>): nat
  ensures LastLineStart(contents) <= |contents|
  decreases |contents|
{
  if |contents| == 0 then
    0
  else if contents[|contents| - 1] == newline then
    |contents|
  else
    LastLineStart(contents[..|contents| - 1])
}

// Reverse the lines of a file that does not end with a final newline.
function ReverseWithoutFinalNewline(contents: seq<byte>): seq<byte>
  decreases |contents|
{
  if |contents| == 0 then
    []
  else
    var lastStart := LastLineStart(contents);
    if lastStart == 0 then
      contents
    else
      contents[lastStart..] + [newline] +
        ReverseWithoutFinalNewline(contents[..lastStart - 1])
}

// If the file has a final newline, keep it at the end of the result.
function ReverseLines(contents: seq<byte>): seq<byte>
{
  if |contents| > 0 && contents[|contents| - 1] == newline then
    ReverseWithoutFinalNewline(contents[..|contents| - 1]) + [newline]
  else
    ReverseWithoutFinalNewline(contents)
}

// Reversing lines only changes their order, not the number of bytes.
lemma ReverseWithoutFinalNewlineKeepsLength(contents: seq<byte>)
  ensures |ReverseWithoutFinalNewline(contents)| == |contents|
  decreases |contents|
{
  if |contents| != 0 {
    var lastStart := LastLineStart(contents);
    if lastStart != 0 {
      ReverseWithoutFinalNewlineKeepsLength(contents[..lastStart - 1]);
      assert |contents[lastStart..]| == |contents| - lastStart;
      assert |contents[..lastStart - 1]| == lastStart - 1;
    }
  }
}

lemma ReverseLinesKeepsLength(contents: seq<byte>)
  ensures |ReverseLines(contents)| == |contents|
{
  if |contents| > 0 && contents[|contents| - 1] == newline {
    ReverseWithoutFinalNewlineKeepsLength(contents[..|contents| - 1]);
  } else {
    ReverseWithoutFinalNewlineKeepsLength(contents);
  }
}

/*
  Creates a new file and writes the whole byte sequence to it.

  This keeps the file-writing proof out of Main, because the postcondition
  of FileStream.Write is a bit detailed.
*/
method WriteNewFile(
    name: array<char>,
    contents: seq<byte>,
    len: int32,
    ghost env: HostEnvironment?)
  returns (success: bool)

  requires env != null && env.Valid() && env.ok.ok()
  requires name[..] !in env.files.state()
  requires 0 <= len as int == |contents|

  modifies env.ok
  modifies env.files

  ensures env.ok.ok() == success
  ensures success ==>
    env.files.state() == old(env.files.state())[name[..] := contents]
{
  var buffer := new byte[|contents|](i =>
    if 0 <= i < |contents| then contents[i] else newline);
  assert buffer[..] == contents;

  ghost var filesBeforeOpen := env.files.state();
  var openSuccess, file := FileStream.Open(name, env);
  if !openSuccess {
    success := false;
    return;
  }

  assert env.files.state() == filesBeforeOpen[name[..] := []];
  assert file.Name() == name[..];

  ghost var filesBeforeWrite := env.files.state();
  assert filesBeforeWrite[name[..]] == [];
  assert buffer[0..len as int] == contents;

  var writeSuccess := file.Write(0 as nat32, buffer, 0 as int32, len);
  if !writeSuccess {
    success := false;
    return;
  }

  // The destination was empty and the write starts at offset 0.
  assert filesBeforeWrite[file.Name()] == [];
  assert filesBeforeWrite[file.Name()][..0] == [];

  if len as int == 0 {
    assert filesBeforeWrite[file.Name()][len as int..] == [];
  } else {
    assert len as int > |filesBeforeWrite[file.Name()]|;
  }

  assert
    (if len as int > |filesBeforeWrite[file.Name()]|
     then []
     else filesBeforeWrite[file.Name()][len as int..]) == [];

  assert
    filesBeforeWrite[file.Name()][..0] +
    buffer[0..len as int] +
    (if len as int > |filesBeforeWrite[file.Name()]|
     then []
     else filesBeforeWrite[file.Name()][len as int..])
    == contents;

  assert env.files.state() ==
    filesBeforeWrite[file.Name() :=
      filesBeforeWrite[file.Name()][..0] +
      buffer[0..len as int] +
      (if len as int > |filesBeforeWrite[file.Name()]|
       then []
       else filesBeforeWrite[file.Name()][len as int..])];

  assert env.files.state() == filesBeforeWrite[name[..] := contents];
  assert filesBeforeWrite[name[..] := contents] ==
    filesBeforeOpen[name[..] := contents];

  var closeSuccess := file.Close();
  if !closeSuccess {
    success := false;
    return;
  }

  success := true;
}

/*
  Main says the important property of the program:
  when the arguments are valid, the source exists, and the destination does not,
  the destination is created with the reversed contents of the source.
*/
method {:main} Main(ghost env: HostEnvironment?)
  requires env != null && env.Valid() && env.ok.ok()

  modifies env.ok
  modifies env.files

  ensures
    env.ok.ok()
    && |old(env.constants.CommandLineArgs())| == 3
    && old(env.constants.CommandLineArgs())[1]
       in old(env.files.state())
    && old(env.constants.CommandLineArgs())[2]
       !in old(env.files.state())
    ==>
      env.files.state()
      == old(env.files.state())[
          old(env.constants.CommandLineArgs())[2] :=
            ReverseLines(
              old(env.files.state())[
                old(env.constants.CommandLineArgs())[1]])]
{
  ghost var args := env.constants.CommandLineArgs();
  ghost var initialFiles := env.files.state();

  var argumentCount := HostConstants.NumCommandLineArgs(env);
  if argumentCount as int != 3 {
    print "Usage: reverse SourceFile DestinationFile\n";
    return;
  }

  assert |args| == 3;

  var sourceName := HostConstants.GetCommandLineArg(1 as uint64, env);
  var destinationName := HostConstants.GetCommandLineArg(2 as uint64, env);
  assert sourceName[..] == args[1];
  assert destinationName[..] == args[2];

  var sourceExists := FileStream.FileExists(sourceName, env);
  if !sourceExists {
    print "Source file does not exist\n";
    return;
  }
  assert sourceName[..] in initialFiles;

  var destinationExists := FileStream.FileExists(destinationName, env);
  if destinationExists {
    print "Destination file already exists\n";
    return;
  }
  assert destinationName[..] !in initialFiles;

  var lengthSuccess, sourceLength := FileStream.FileLength(sourceName, env);
  if !lengthSuccess {
    return;
  }

  var openSuccess, sourceFile := FileStream.Open(sourceName, env);
  if !openSuccess {
    return;
  }

  var sourceBuffer := new byte[sourceLength as int];
  var readSuccess := sourceFile.Read(
    0 as nat32,
    sourceBuffer,
    0 as int32,
    sourceLength);

  if !readSuccess {
    return;
  }
  assert sourceBuffer[..] == initialFiles[sourceName[..]];

  var closeSuccess := sourceFile.Close();
  if !closeSuccess {
    return;
  }

  var sourceContents := sourceBuffer[..];
  var destinationContents := ReverseLines(sourceContents);

  ReverseLinesKeepsLength(sourceContents);
  assert |destinationContents| == sourceLength as int;

  var writeSuccess := WriteNewFile(
    destinationName,
    destinationContents,
    sourceLength,
    env);

  if !writeSuccess {
    return;
  }

  assert initialFiles[sourceName[..]] == sourceContents;
  assert env.files.state()
      == initialFiles[destinationName[..] := destinationContents];
  assert env.files.state()
      == initialFiles[args[2] := ReverseLines(initialFiles[args[1]])];
}
