using System;
using System.IO;
 
namespace Demo
{
    class Program
    {
        static void Main(string[] args)
        {
            long n = long.Parse(Console.ReadLine());
            
            long t = n*(n+1)/2;
            
            /*
            for (long i = u; i <= v; ++i) {
                t += i;
            }
            */
            
            Console.WriteLine(t);           
        }
    }
}
