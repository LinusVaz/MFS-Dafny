/*
 * This is the skeleton for your line reverse utility.
 *
 */

include "Io.dfy"

const newline: byte := 10 as byte

// Find where the last line starts
function lastLineStart(text: seq<byte>): nat
    ensures lastLineStart(text) <= |text|
    decreases |text|
{
    if |text| == 0 then
        0
    else if text[|text| - 1] == newline then
        |text|
    else
        lastLineStart(text[..|text| - 1])
}

// Reverse the lines when the text does not end with '\n'
function reverseNoFinalNewline(text: seq<byte>): seq<byte>
    decreases |text|
{
    if |text| == 0 then
        []
    else
        var start := lastLineStart(text);
        if start == 0 then
            text
        else
            text[start..] + [newline] + reverseNoFinalNewline(text[..start - 1])
}

function reverseLines(text: seq<byte>): seq<byte>
{
    if |text| > 0 && text[|text| - 1] == newline then
        reverseNoFinalNewline(text[..|text| - 1]) + [newline]
    else
        reverseNoFinalNewline(text)
}

lemma reverseNoFinalNewlineKeepsLength(text: seq<byte>)
    ensures |reverseNoFinalNewline(text)| == |text|
    decreases |text|
{
    if |text| != 0 {
        var start := lastLineStart(text);
        if start != 0 {
            reverseNoFinalNewlineKeepsLength(text[..start - 1]);
            assert |text[start..]| == |text| - start;
            assert |text[..start - 1]| == start - 1;
        }
    }
}

lemma reverseLinesKeepsLength(text: seq<byte>)
    ensures |reverseLines(text)| == |text|
{
    if |text| > 0 && text[|text| - 1] == newline {
        reverseNoFinalNewlineKeepsLength(text[..|text| - 1]);
    } else {
        reverseNoFinalNewlineKeepsLength(text);
    }
}

method writeNewFile(name: array<char>, content: seq<byte>, len: int32, ghost env: HostEnvironment?)
    returns (ok: bool)
    requires env != null && env.Valid() && env.ok.ok()
    requires name[..] !in env.files.state()
    requires 0 <= len as int == |content|
    modifies env.ok
    modifies env.files
    ensures env.ok.ok() == ok
    ensures ok ==> env.files.state() == old(env.files.state())[name[..] := content]
{
    // Convert the sequence of bytes into an array, so it can be written
    var buffer := new byte[|content|](i =>
        if 0 <= i < |content| then content[i] else newline);
    assert buffer[..] == content;

    // Create the destination file
    ghost var beforeOpen := env.files.state();
    var openOk, file := FileStream.Open(name, env);
    if !openOk {
        ok := false;
        return;
    }

    assert env.files.state() == beforeOpen[name[..] := []];
    assert file.Name() == name[..];

    // Write the reversed content to the empty file
    ghost var beforeWrite := env.files.state();
    assert beforeWrite[name[..]] == [];
    assert buffer[0..len as int] == content;

    var writeOk := file.Write(0 as nat32, buffer, 0 as int32, len);
    if !writeOk {
        ok := false;
        return;
    }

    // These asserts are only to unfold the specification of Write
    assert beforeWrite[file.Name()] == [];
    assert beforeWrite[file.Name()][..0] == [];
    if len as int == 0 {
        assert beforeWrite[file.Name()][len as int..] == [];
    } else {
        assert len as int > |beforeWrite[file.Name()]|;
    }
    assert (if len as int > |beforeWrite[file.Name()]| then [] else beforeWrite[file.Name()][len as int..]) == [];
    assert beforeWrite[file.Name()][..0] + buffer[0..len as int] +
        (if len as int > |beforeWrite[file.Name()]| then [] else beforeWrite[file.Name()][len as int..]) == content;
    assert env.files.state() == beforeWrite[file.Name() :=
        beforeWrite[file.Name()][..0] + buffer[0..len as int] +
        if len as int > |beforeWrite[file.Name()]| then [] else beforeWrite[file.Name()][len as int..]];
    assert env.files.state() == beforeWrite[name[..] := content];
    assert beforeWrite[name[..] := content] == beforeOpen[name[..] := content];

    var closeOk := file.Close();
    if !closeOk {
        ok := false;
        return;
    }
    ok := true;
}

method {:main} Main(ghost env: HostEnvironment?)
    requires env != null && env.Valid() && env.ok.ok()
    modifies env.ok
    modifies env.files
    ensures env.ok.ok() &&
        |old(env.constants.CommandLineArgs())| == 3 &&
        old(env.constants.CommandLineArgs())[1] in old(env.files.state()) &&
        old(env.constants.CommandLineArgs())[2] !in old(env.files.state())
        ==> env.files.state() == old(env.files.state())[
            old(env.constants.CommandLineArgs())[2] :=
                reverseLines(old(env.files.state())[old(env.constants.CommandLineArgs())[1]])]
{
    ghost var args := env.constants.CommandLineArgs();
    ghost var oldFiles := env.files.state();

    // Check for 3 arguments (program, source file and destination file)
    var numArgs := HostConstants.NumCommandLineArgs(env);
    if numArgs as int != 3 {
        print "Wrong usage\n";
        return;
    }
    assert |args| == 3;

    // Get both file names
    var source := HostConstants.GetCommandLineArg(1 as uint64, env);
    var destination := HostConstants.GetCommandLineArg(2 as uint64, env);
    assert source[..] == args[1];
    assert destination[..] == args[2];

    // Check if source exists
    var sourceExists := FileStream.FileExists(source, env);
    if !sourceExists {
        print "Source file does not exist\n";
        return;
    }
    assert source[..] in oldFiles;

    // Check that destination does not exist
    var destinationExists := FileStream.FileExists(destination, env);
    if destinationExists {
        print "Destination file already exists\n";
        return;
    }
    assert destination[..] !in oldFiles;

    // Get source file length
    var success, len := FileStream.FileLength(source, env);
    if !success {
        print "Could not get file length\n";
        return;
    }

    // Open source file
    var open, fileStream := FileStream.Open(source, env);
    if !open {
        print "Could not open file\n";
        return;
    }

    // Read file content
    var buffer := new byte[len as int];
    var read := fileStream.Read(0 as nat32, buffer, 0 as int32, len);
    if !read {
        print "Could not read file\n";
        return;
    }
    assert buffer[..] == oldFiles[source[..]];

    var close := fileStream.Close();
    if !close {
        print "Could not close file\n";
        return;
    }

    // Reverse lines and write the destination
    var sourceContent := buffer[..];
    var result := reverseLines(sourceContent);
    reverseLinesKeepsLength(sourceContent);
    assert |result| == len as int;

    var written := writeNewFile(destination, result, len, env);
    if !written {
        print "Could not write destination file\n";
        return;
    }

    assert oldFiles[source[..]] == sourceContent;
    assert env.files.state() == oldFiles[destination[..] := result];
    assert env.files.state() == oldFiles[args[2] := reverseLines(oldFiles[args[1]])];
}
