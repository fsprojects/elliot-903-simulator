#light

// Formatting functions for Elliott 903 Data Types
//
// Format objects provide Elliot 903 formatted output to a StreamWriter
// (generally a file or system console).
//
// By default a mapping of F# (UTF) characters to Elliott 900 series telecode is used:
// if the t900Out flag is set the Elliott 903 telecode mapping is applied.

module Sim900.Formatting
    open System
    open System.IO
    open System.Text
    open Sim900.Bits
    open Sim900.Telecodes
    open Sim900.Memory
    open Sim900.Models
    open Sim900.Devices
    
    module private LoggingHelper =
        
        let mutable logFile: StreamWriter option = None

    open LoggingHelper

    exception NoLog

    let LogToFile (f: string) = 
        match logFile with
        | Some(s) -> s.Close ()
        | None    -> ()
        logFile <- Some (new StreamWriter (f, true)) // open in append mode

    let Log f = 
        match logFile with
        | Some(s) -> let old = stdout
                     Console.SetOut s
                     f ()
                     Console.SetOut old
        | None    -> ()

    let CloseLog () =
        match logFile with
        | Some (s) -> s.Close ()
        | None     -> ()

    let LogFileOpen () =
        match logFile with
        | Some(s) -> true
        | None    -> false

    // 900 SIR STYLE FORMATTING OF BASIC DATA TYPES

    let AddressStr word =
        sprintf "%4d^%02d" (AddressField word) (ModuleField  word) 
                       
    let AddressPut (word: int) =
        stdout.Write (AddressStr word)
             
    let AlphanumPut word = // use 900 telecode representation 
        printf "\\"
        for pos in [12;6;0] do
            let code = (word>>>pos)&&&mask6
            if   code = 1
            then printf "^"
            else printf "%s" ((SIRSymbolOf code).ToString())
                     
    let EnsureNewLine () = // force a newline if text has been output on current line
        if System.Console.CursorLeft > 0 then printfn ""
                    
    let FractionPut word =
        let fraction = (float(Normalize(int word)))/131072.0
        let text = sprintf "%+8.6f" fraction
        let sign = if fraction >= 0.0 then '+' else '-'
        printf "%c%s" sign (text.Substring (2))

    let LongSignedF word =
        sprintf "%+7d" (Normalize word)

    let LongSignedPut word = 
        stdout.Write (LongSignedF word)
                                                       
    let ShortNaturalPut word = // output 18 bit unsigned value in decimal
        printf "%d"   (Normalize word)

    let InstructionF word =
        // output word in instruction format
        let modify = ModifyField   word
        let fn     = FunctionField word
        let addr   = AddressField  word
        (if   modify <> 0
         then sprintf (if fn < 10 then " /" else "/")
            else sprintf (if fn < 10 then "  " else " ")) +
               (sprintf "%d%5d" fn addr)

    let InstructionPut word = 
        printf "%s" (InstructionF word)
                            
    let MessagePut item = // output a simulator message
        EnsureNewLine ()
        printfn "SIM900: %s" item
 
    let OctalPut word =
        printf "&%06o" word
                                         
    let Prompt () = 
        YieldToDevices ()
        EnsureNewLine ()
        printf "SIM900> " 

    let WordPut word =
        // output word in signed integer format
        printf "  "
        LongSignedPut word
        // output word in signed fraction format
        printf "  "
        FractionPut word
        // output word in octal
        printf "  "
        OctalPut word
        // output word in instruction format
        printf "  "
        InstructionPut word                  
        // output word in alphanumeric 6 bit code
        printf "  "
        AlphanumPut word 
        // end line
        printfn ""

    let RegisterPut name value f =
        printf "%c=" name
        f value       
                 
    let TracePut i s instruction a q b =
        let spaces () = printf "   "
        printf "L%1d   " i
        AddressPut s
        spaces () 
        InstructionPut instruction
        spaces ()
        RegisterPut 'A' a LongSignedPut
        spaces ()  
        RegisterPut 'Q' q LongSignedPut
        spaces ()  
        RegisterPut 'B' b AddressPut
        printf "  ("
        LongSignedPut  b 
        printfn ")"

    let StoreWordPut (address: int option) value = 
        match address with
        | Some (address) -> AddressPut address 
        | None           -> printf "       "       
        // output word in modifier function code address format
        printf "   "
        WordPut value   
                                
    let TeleCodePut code telecode = // Output as UTF equivalent of 900 or 903 telecode character
        match code with
        | 0uy   -> ()                     // BLANK
        | 10uy  -> printfn ""             // NL
        | 135uy -> System.Console.Beep () // BEL
        | 141uy -> ()                     // CR
        | _    -> printf "%s" (UTFOf telecode code) 
                        
    let TimesPut (cpuTime: int64, elTime: int64, pcTime: int64, machineName: string, iCount: int64) =
        let exeTime = System.TimeSpan.FromMilliseconds ((double cpuTime) / 10000.0)
        let totTime = System.TimeSpan.FromMilliseconds ((double elTime)  / 10000.0)
        let pcTime  = System.TimeSpan.FromMilliseconds (double pcTime)
        let ToString (t: TimeSpan) = 
            let hrs    = t.Hours
            let hs     = if hrs = 1 then "hour " else "hours"
            let mins   = t.Minutes % 60
            let ms     = if mins = 1 then "min " else "mins"
            let secs   = t.TotalSeconds % 60.0
            let ss     = if secs = 1.0  then "sec" else "secs"
            (if hrs > 0 then sprintf "%3d %s" hrs hs else "         ") +
                (if mins > 0 then sprintf " %2d %s" mins ms else "        ") +
                    (sprintf " %6.3f %s" secs ss)
        MessagePut (sprintf "Instructions     = %29d" iCount)
        MessagePut (sprintf "%s cpu time     = %s" machineName (ToString exeTime))
        MessagePut (sprintf "%s elapsed time = %s" machineName (ToString totTime))
        MessagePut (sprintf "%s elapsed time = %s" ("PC".PadRight (machineName.Length)) (ToString pcTime))  

    let ConfigPut () =
        MessagePut (sprintf "Elliott %s with %dK of %d microsec store and %d ch/s tape reader" 
                        machineName (memorySize/1024) memorySpeed (10000000L / ptrCharTime))

    let MFAlgol word =
                        let n = word&&&mask13
                        let f = (word>>>13) &&& 31
                        match f with
                        | 00 -> "TA"     | 01 -> "TIA"    | 02 -> "TIR"   | 03 -> "TRA"   | 04 -> "TRR"   
                        | 05 -> "INDFS"  | 06 -> "MAMPS"  | 07 -> "IFJ"   | 08 -> "UJ"    | 09 -> "GTS"   
                        | 10 -> "GT"     | 11 -> "GTF"    | 12 -> "INDA"  | 13 -> "INDR"  | 14 -> "GTFS"  
                        | 15 -> if n < 32 then "INOUT" else "TASIR"
                                         | 16 -> "MKTHK"  | 17 -> "TICA"  | 18 -> "TIC"   | 19 -> "TRCA"  
                        | 20 -> "TRC"    | 21 -> "CF"     | 22 -> "CFF"   | 23 -> "PE"    | 24 -> "TF"  
                        | 25 -> "GETAD"  | 26 -> "TRCN"   | 27 -> "INDS"  | 28 -> "IFUN"  | 29 -> "RFUN"  
                        | 30 -> if n < 32 then "PEM" else "CFSIR"        
                        | 31 -> ""
                        | _  -> sprintf "ERROR %d %d" f n
                        
    let Prim word =
                        match word &&& 8191 with
                        | 01 -> "CBL"     | 02 -> "CHECKB"  | 03 -> "CHECKI"  | 04 -> "CHECKR" | 05 -> "CHECKS"
                        | 06 -> "DO"      | 07 -> "STW"     | 08 -> "FINISH"  | 09 -> "FOR"    | 10 -> "FR"
                        | 11 -> "FSE"     | 12 -> "DIV"     | 13 -> "ITOR1"   | 14 -> "ITOR2"  | 15 -> "NEGI"
                        | 16 -> "NEGR"    | 17 -> "RETURN"  | 18 -> "RTOI1"   | 20             | 23 -> "ST"
                        | 21 -> "STA"     | 22 -> "STEP"    | 24 -> "WAIT"    | 25 -> "STEP2"  | 26 -> "UNTIL"
                        | 27 -> "UP"      | 28 -> "R:=R^I"  | 29 -> "WHILE"   | 30 -> "I:=I+I" | 31 -> "R:=R+R"
                        | 32 -> "I:=I-I"  | 33 -> "R:=R-R"  | 34 -> "I:=I*I"  | 35 -> "R:=R*R" | 36 -> "R:=I/I"
                        | 37 -> "R:=R/R"  | 38 -> "I:=I^I"  | 39 -> "R:=I^I"  | 40 -> "R:=R^R" | 41 -> "B:=I<I"
                        | 42 -> "B:=R<R"  | 43 -> "B:= I<=I"| 44 -> "B:=R<=R" | 45 -> "B:=I=I" | 46 -> "B:=R=R"
                        | 47 -> "B:=I<>I" | 48 -> "B:=R<>R" | 49 -> "B:=I>I"  | 50 -> "B:=R>R" | 51 -> "B:=I>=I"
                        | 52 -> "B:=R>=R" | 53 -> "B:=B&B"  | 54 -> "B:=B|B"  | 55 -> "B:=B=B" | 56 -> "B:=B=>B"
                        | 57 -> "B:=~B"   | 58 -> "abs"     | 59 -> "entier"  | 60 -> "exp"    | 61 -> "ln"
                        | 62 -> "sign"    | _  -> sprintf "CON%d"  ((word&&&8191)-60)

    let algolPut pp instruction =
        AddressPut pp
        stdout.Write "  "
        let mf = MFAlgol instruction
        if   mf = ""
        then stdout.WriteLine (Prim instruction)
        else printfn "%s  %4d" mf (instruction&&&mask13) 

                 