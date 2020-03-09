#light

   module Sim900.Parameters
  
  // Elliott 900 Simulator command line parameter decoding

        open Sim900.Version
        open Sim900.Bits
        open Sim900.Telecodes
        open Sim900.Models
        open Sim900.Devices
        open Sim900.Memory
        open Sim900.Formatting
        open Sim900.Machine

        exception Syntax of string

        type Info       = {name: string ; memSize: string; memSpeed: int; ptrSpeed: int}
        let Generic900  = {name="900"; memSize="64K"; memSpeed=0; ptrSpeed=0}
 
        let mutable on  = false // true after ON command

        // remember default console
        let consoleIn  = System.Console.In
        let consoleOut = System.Console.Out

        // ERRORS
        let BadCommand     () = raise (Syntax "Eh?")        
        let BadParameter   () = raise (Syntax "Parameter error")        
        let BadInstruction () = raise (Syntax "Wrongly formatted instruction")  
        let BadNumber      () = raise (Syntax "Number out of range")
        
        // PARAMETER DECODING

        let GetNumber (text: string) = // integer or fraction
            if   text.Length > 0 && text.[0] = '.'
            then // fraction
                 try int ((float text) * 131072.0) with _ -> BadParameter ()
            else // integer
                 try (int text) with _ -> BadParameter ()  

        let GetNatural (text: string) = // Natural number (unsigned)
            try (int text) with _ -> BadParameter ()  

        let GetAddress (text: string) = // Address in module format e.g., 1^1024
            let arrow = text.IndexOf '^'
            if   arrow = -1
            then // no module prefix 
                 GetNatural text
            else let offset   = GetNatural (text.[0..(arrow-1)])
                 let moduleNo = GetNatural (text.[(arrow+1)..])
                 if moduleNo > 15 || offset > 8191
                 then BadParameter ()
                 else (moduleNo <<< 13) ||| offset 

        let GetInstruction (fn: string) addr = // instruction F N or /F N
            if fn.Length < 2
            then BadParameter ()
            elif fn.[0] <> '='
            then  BadParameter ()
            elif fn.[1] = '/'
            then InstructionToWord (1, (GetNatural fn.[2..]), (GetNatural addr))
            else InstructionToWord (0, (GetNatural fn.[1..]), (GetNatural addr))
            
        let GetOctal (text: string) = // Octal group &ddddddd
            let rec OctalHelper index count value =
                if  count = 0
                then value
                else let digit = text.[index]
                     if   '0' <= digit && digit <= '7'
                     then OctalHelper (index+1) (count-1) ((value <<< 3) ||| ((int text.[index]) - (int '0')))
                     else BadParameter ()
            OctalHelper 1 (text.Length-1) 0
        
        let GetConstant (n: string) = // Octal group, signed integer or natural number
            let value =
                match  n.[0] with
                | '&' -> int (GetOctal n)
                | '+' -> int (GetNumber n.[1..])
                | '-' -> int -(GetNumber n.[1..])
                | _   -> int (GetAddress n)
            if   value > mask18 
            then BadNumber ()
            elif value < 0
            then value &&& mask18
            else value

        // display range        
        let rec DisplayRange2 f l =
            if   l < f
            then DisplayRange2 l f
            else StoreWordPut (Some(f)) (ReadStore f)
                 for addr = f+1 to l do StoreWordPut (if (addr%5)=0 then Some(addr) else None) (ReadStore addr)

