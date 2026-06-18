/*  
 * This is the skeleton for the grep utility.
 * In this folder you should include a grep utility based
 * on the "naive" string matching algorithm.
 *
 */

include "Io.dfy"

// A line is "no-newline" if none of its characters is '\n'.
// Used to characterise the output of getLines: each emitted line
// cannot contain the byte we split on.
predicate noNewlines(line: seq<char>)
{
    forall k :: 0 <= k < |line| ==> line[k] != '\n'
}

predicate matchAt(text: seq<char>, pattern: array<char>, i: int)
    requires 0 <= i
    requires i + pattern.Length <= |text|
    reads pattern
{
    forall k :: 0 <= k < pattern.Length ==> text[i + k] == pattern[k]
}

method naiveSearch(text: seq<char>, pattern: array<char>) returns (pos: int)
    requires pattern.Length > 0
    ensures pos == -1 || (0 <= pos && pos + pattern.Length <= |text| && matchAt(text, pattern, pos))
    ensures pos == -1 ==> forall k :: 0 <= k <= |text| - pattern.Length ==> !matchAt(text, pattern, k)
{
    pos := -1;
    if pattern.Length > |text| { return; }
    var i := 0;
    while i <= |text| - pattern.Length
        invariant 0 <= i
        invariant forall k :: 0 <= k < i && k + pattern.Length <= |text| ==> !matchAt(text, pattern, k)
    {
        var j := 0;
        var matched := true;
        while j < pattern.Length
            invariant 0 <= j <= pattern.Length
            invariant matched ==> forall k :: 0 <= k < j ==> text[i + k] == pattern[k]
        {
            if text[i + j] != pattern[j] {
                matched := false;
                break;
            }
            j := j + 1;
        }
        if matched {
            pos := i;
            return;
        }
        i := i + 1;
    }
}

// Split a byte buffer into lines on the '\n' character.
// The post-condition guarantees that every emitted line is newline-free,
// which is exactly the property the search algorithm relies on.
method getLines(text: array<byte>) returns (lines: seq<seq<char>>)
    ensures forall i :: 0 <= i < |lines| ==> noNewlines(lines[i])
{
    var result: seq<seq<char>> := [];
    var current: seq<char> := [];
    var i := 0;
    while i < text.Length
        invariant 0 <= i <= text.Length
        invariant forall j :: 0 <= j < |result| ==> noNewlines(result[j])
        invariant noNewlines(current)
    {
        if text[i] as char == '\n' {
            result := result + [current];
            current := [];
        } else {
            current := current + [text[i] as char];
        }
        i := i + 1;
    }
    // Add the trailing line only when it actually accumulated something.
    // Previous version compared against "\n" (a single-char sequence) which
    // never matches an accumulator built from non-newline characters, so an
    // empty trailing line slipped through whenever the file ended with '\n'.
    if current != [] {
        result := result + [current];
    }
    lines := result;
}

method {:main} Main(ghost env:HostEnvironment?)
  requires env != null && env.Valid() && env.ok.ok()
  modifies env.ok, env.files
{
  // Check for 3 arguments (./grep, word and file)
  var numArgs := HostConstants.NumCommandLineArgs(env);
  if numArgs != 3 {
      print numArgs as int;
      print "Wrong usage\n";
      return;
  }

  // Get both arguments
  var word := HostConstants.GetCommandLineArg(1, env);
  var file := HostConstants.GetCommandLineArg(2, env);


  // Check if word is valid (important later when validating the search)
  if word.Length <= 0 {
      print "Invalid Word\n";
      return;
  }

  // Check if file exists
  var exist := FileStream.FileExists(file, env);
  if (!exist) {
    print "File does not exist\n";
    return;
  }

  // Get file length
  var success, len := FileStream.FileLength(file, env);
  if !success {
      print "Could not get file length\n";
      return;
  }
    
  // Open file  
  var fileStream: FileStream;
  var open: bool;
  open, fileStream := FileStream.Open(file, env);
  if !open {
      print "Could not open file\n";
      return;
  }

  // Read file content (entire file is storeed in buffer)
  var buffer := new byte[len];
  var read := fileStream.Read(0, buffer, 0, len);
  if !read {
      print "Could not read file\n";
      return;
  }

  // Split into lines and search each one
  var lines := getLines(buffer);
  var found := false;
  var i := 0;
  while i < |lines|
      invariant 0 <= i <= |lines|
  {
      var line_match := naiveSearch(lines[i], word); // naiveSearch returns -1 if not found 
      if line_match != -1 {
          found := true;
          print lines[i];   // Print the entire line
          print "\n";
      }
      i := i + 1;
  }
  if !found {
      print "No matching lines\n";
  }
}
