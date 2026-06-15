# MFS Project 2

## Group Elements

Identify all group elements (numbers and names).

- upXXXXX Name of element 1
- upXXXXX Name of element 2
- upXXXXX Name of element 3

## Accomplished Work

### Reverse
In reverse.dfy (on the reverse folder) we implemented the file reverse utility. The program expects a source file and a destination file as command-line arguments. If the source file exists and the destination file does not already exist, the program creates the destination file with the same lines as the source, but in reverse order.

The line reversal is specified using the "reverseLines" function. Since files are represented as sequences of bytes, the implementation treats byte 10 as the newline character. The auxiliary function "lastLineStart" is used to find the beginning of the last line, and "reverseNoFinalNewline" recursively builds the reversed file contents.

The correctness of the reverse operation is supported by lemmas proving that reversing the lines preserves the total number of bytes. This is needed because the destination buffer must have the same length as the contents that are written to the file.

The actual file creation and writing is done in the "writeNewFile" method. This method proves that, if it succeeds, the resulting file system is the old file system plus the new destination file containing the reversed source contents.
### Grep-Naive

In grep.dfy (on the grep-naive folder) we implemented the grep utility using a naive string matching algorithm. The algorithm is very simple and works by attempting to match the string over each text position, resulting in quadratic time complexity.

The correctness of the grep utility is guaranteed in the "naiveSearch" method, which returns the position of the pattern in the text if it exists, or -1 if it does not. The matching of the string at each text position makes use of the "matchAt" predicate.

While the "naiveSearch" method returns the position, this was only used in an earlier simpler implementation of the grep utility where we only returned a YES/NO output with the position of the first pattern occurrence (if it occurred of course).

This grep utility implementation now prints all lines where the string matched with the text or "No matching lines" if there are no matches. For this, an auxiliary method "getLines" was developed, which simply splits the entire text file into a sequence of lines, which are then used to perform naive seach on each one.

### Grep-KMP
