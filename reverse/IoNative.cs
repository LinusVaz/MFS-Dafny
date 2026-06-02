using System;
using System.Numerics;
using System.Diagnostics;
using System.Threading;
using System.Collections.Concurrent;
using System.Collections.Generic;
using FStream = System.IO.FileStream;

// If using Dafny 2.2.0, use @__default; if using Dafny 2.3.0, use _module
//namespace @__default {
namespace _module {

    public partial class HostConstants
    {
        public static uint NumCommandLineArgs()
        {
            return (uint)System.Environment.GetCommandLineArgs().Length;
        }

        public static Dafny.Rune[] GetCommandLineArg(ulong i)
        {
            var arg = new List<Dafny.Rune>();
            foreach (var rune in Dafny.Rune.Enumerate(System.Environment.GetCommandLineArgs()[i]))
            {
                arg.Add(rune);
            }
            return arg.ToArray();
        }
    }

    public partial class FileStream
    {
        internal FStream fstream = null!;
        internal FileStream(FStream fstream) { this.fstream = fstream; }

        private static string NameToString(Dafny.Rune[] name)
        {
            var s = new System.Text.StringBuilder();
            foreach (var rune in name)
            {
                s.Append(char.ConvertFromUtf32(rune.Value));
            }
            return s.ToString();
        }

        public static bool FileExists(Dafny.Rune[] name)
        {
            return System.IO.File.Exists(NameToString(name));      
        }

        public static void FileLength(Dafny.Rune[] name, out bool success, out int len)
        {
        len = 42;
        try
        {
            System.IO.FileInfo fi = new System.IO.FileInfo(NameToString(name));
            if (fi.Length < System.Int32.MaxValue)  // We only support small files
            {
            len = (int)fi.Length;
            success = true;
            }
            else
            {
            success = false;
            }
            
        }
        catch (Exception e)
        {
            System.Console.Error.WriteLine(e);
            success = false;
        }     
        }

        public static void Open(Dafny.Rune[] name, out bool ok, out FileStream f)
        {
            try
            {
                f = new FileStream(new FStream(NameToString(name), System.IO.FileMode.OpenOrCreate, System.IO.FileAccess.ReadWrite));
                ok = true;
            }
            catch (Exception e)
            {
                System.Console.Error.WriteLine(e);
                f = null;
                ok = false;
            }
        }

        public bool Close()
        {
            try
            {
                fstream.Close();
                return true;
            }
            catch (Exception e)
            {
                System.Console.Error.WriteLine(e);
                return false;
            }
        }

        public bool Read(int file_offset, byte[] buffer, int start, int num_bytes)
        {
            try
            {
                fstream.Seek(file_offset, System.IO.SeekOrigin.Begin);
                fstream.Read(buffer, start, num_bytes);
                return true;
            }
            catch (Exception e)
            {
                System.Console.Error.WriteLine(e);
                return false;
            }
        }

        public bool Write(int file_offset, byte[] buffer, int start, int num_bytes)
        {
            try
            {
                fstream.Seek(file_offset, System.IO.SeekOrigin.Begin);
                fstream.Write(buffer, start, num_bytes);
                return true;
            }
            catch (Exception e)
            {
                System.Console.Error.WriteLine(e);
                return false;
            }
        }
    }

}
