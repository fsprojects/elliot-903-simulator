#light

// Elliott 903 Algol simulator commands

module Sim900.Commands

        open System.Text
        open System.IO
        open System.Windows.Forms

        open Sim900.Version
        open Sim900.Bits
        open Sim900.Telecodes
        open Sim900.Models
        open Sim900.Devices
        open Sim900.Memory
        open Sim900.Formatting
        open Sim900.Machine
        open Sim900.Parameters
        open Sim900.Legible
        open Sim900.RLB
        open Sim900.FileHandling
        open Sim900.Loaders

        exception Quit
   
        // breakpoints
        let BreakCmd (words: string[]) =
            if   words.Length < 1 
            then BadCommand ()
            elif words.Length < 2
            then BadCommand ()
            match words.[0] with
            | "ON"  ->  for w in words.[1..] do BreakpointOn   (GetAddress w)
            | "OFF" ->  for w in words.[1..] do BreakpointOff (GetAddress w)
            | _     ->  BadCommand ()

        // display breakpoints
        let BreakpointsPut () =
            let b = Breakpoints ()
            if b.Count = 0
            then stdout.WriteLine "No breakpoints set"
            else stdout.WriteLine "Breakpoints"
                 for addr in b do 
                    AddressPut addr
                    stdout.WriteLine ()

        // change directory
        let ChangeDir d =
            if   Directory.Exists d 
            then System.Environment.CurrentDirectory <- d
            else raise (Syntax (sprintf "Cannot open directory %s" d))
            
        let DisplayRange first last =
            DisplayRange2 (GetAddress first) (GetAddress last)

        // display register
        let DisplayRegisters () =
            stdout.Write "A="; LongSignedPut (AGet ()); stdout.Write "  "; AddressPut (AGet()); stdout.Write "    "
            stdout.Write "Q="; LongSignedPut (QGet ()); stdout.Write "  "; AddressPut (QGet()); stdout.WriteLine ()
            stdout.Write "B="; LongSignedPut (BGet ()); stdout.Write "  "; AddressPut (BGet()); stdout.Write "    "
            stdout.Write "S="; LongSignedPut (SGet ()); stdout.Write "  "; AddressPut (SGet()); stdout.WriteLine ()

        // display after a problem reported
        let MiniDump () =
            let s = OldSGet ()
            stdout.WriteLine ()
            try DisplayRange2 s s with | _ -> () // mask any addressing error
            stdout.WriteLine ()
            DisplayRegisters ()

        // display at a monitored location
        let MonitorPut m =
            // show location
            stdout.WriteLine ()
            stdout.Write "*"
            AddressPut (m.addr)
            stdout.WriteLine ()
            stdout.WriteLine ()
            DisplayRegisters ()
            for r in m.regions do
                stdout.WriteLine ()            
                let rec indirect addr (l: list<int>) =
                    if   l.IsEmpty
                    then addr
                    else indirect ((ReadStore addr) + l.Head) l.Tail
                let start  = indirect r.start.Head  r.start.Tail
                let finish = indirect r.finish.Head r.finish.Tail
                DisplayRange2 start finish            
        
        // display location
        let DisplayLocation text =
            let addr = GetAddress text
            StoreWordPut (Some(addr)) (ReadStore addr)

        // enter value
        let Enter loc value =
            match loc with
            | "A" -> APut value
            | "Q" -> QPut value
            | "B" -> BPut value
            | _   -> WriteStore (GetAddress loc) value

        let Find value =
            for addr = 0 to memorySize - 1 do
                if   (ReadStore addr) = value
                then AddressPut addr; stdout.WriteLine ()

        // monitor
        let MonitorOnCmd (words: string[]) = 
            if   words.Length < 1
            then BadCommand ()
            let addr = GetAddress words.[0]
            let GetNumber (s: string) =
                if s.Length < 1 then BadParameter ()
                match s.[0] with
                | '+'   ->    GetNatural s.[1..]
                | '-'   ->  -(GetNatural s.[1..])
                | _     ->  failwith "Internal error1 in MonitorCmd" // shouldn't happen
            let rec nextIndirect (s: string) =
                let pos = s.[1..].IndexOfAny [|'+';'-'|] // split out number
                if   pos < 0
                then (GetNumber s):: [] 
                else (GetNumber s.[..pos])::(nextIndirect s.[(pos+1)..])
            let parseIndirect (s: string) =
                let pos = s.IndexOfAny [|'+';'-'|]
                if   pos < 0
                then // no indirections
                     (GetNatural s)::[] 
                else // build list of indirections
                     (GetNatural s.[..(pos-1)])::(nextIndirect s.[pos..])
            let rec parseRegions i =
                if   i >= words.Length
                then // all regions parsed
                     []
                else // unpick next region
                     let region = words.[i]
                     // parse start/finish
                     let ss = region.Split [|'/'|]
                     if ss.Length > 2 then BadParameter ()
                     let start  = parseIndirect ss.[0]
                     let finish = (if ss.Length = 1 then start else parseIndirect ss.[1])
                     {start=start; finish=finish}::(parseRegions (i+1))
            let regions = parseRegions 1
            MonitorOn {addr=addr; regions=regions}
            
        let MonitorCmd (words: string[]) =
            if   words.Length < 1 
            then BadCommand ()
            else match words.[0] with
                 | "ON"  ->  MonitorOnCmd words.[1..]
                 | "OFF" ->  if   words.Length < 2
                             then MonitorOffAll ()
                             else for w in words.[1..] do MonitorOff (GetAddress w)
                 | _     ->  BadCommand ()

        // display monitor points
        let MonitorsPut () =
            let mm  = Monitors ()
            if   Seq.length mm = 0
            then stdout.WriteLine "No monitor points set"
            else stdout.WriteLine "Monitors"
                 for m in mm do
                    let addr, regions = m
                    AddressPut addr
                    stdout.Write "   "
                    for r in regions do
                        stdout.Write " "
                        let indirectPut (l: list<int>) =
                            stdout.Write l.Head
                            for i in l.Tail do
                                printf "%+d" i
                        indirectPut r.start
                        stdout.Write '/'
                        indirectPut r.finish
                    stdout.WriteLine ()            

        // wait for user input
        let Pause () =
            consoleOut.Write "SIM900: Paused - type RETURN to continue...."
            while consoleIn.Read () <> (int '\r') do ()
  
        // PERT dump
        let Pert (first, last) =
            let ASCIIOut (code) =
                match code &&& 127uy with
                    | 000uy  -> "\\0"   // blank
                    | 013uy  -> "\\r"   // return
                    | 127uy  -> "<! 255 !>" // erase 
                    | 007uy  -> "<! bell !>"
                    | 010uy  -> "\\n"
                    | 020uy  -> "<! halt !>"
                    | i      -> UTFOf T900 i 

            for addr in first..last do
                AddressPut addr
                stdout.Write "   "
                let word = ReadStore addr
                let ch1 = ((word >>> 8) &&& 255) 
                let ch2 = (word &&& 255)
                printf "%3d  '%s'     %3d  '%s'    "  ch1 (ASCIIOut(byte ch1)) ch2 (ASCIIOut(byte ch2)) 
                OctalPut word
                stdout.WriteLine ()

        // QCHECK (based on 903 QCHECK utility)
        let QCheck (words: string[]) =
            let rec Helper prev (words: string[]) =
                if  words.Length = 0
                then () // done
                elif words.Length < 3
                then raise (Syntax "<from> <to> <format> expected")
                else let first = GetAddress words.[0]
                     let last  = GetAddress words.[1]
                     if first <> (prev+1) then printfn "^%d" first
                     for addr = first to last do
                         if   addr%5=0
                         then stdout.Write '('
                              AddressPut addr
                              stdout.Write ")    "
                         else stdout.Write "             "
                         let word = ReadStore addr
                         match words.[2] with
                         | "F"   ->                     FractionPut      word
                         | "I"   ->  stdout.Write " ";  LongSignedPut    word
                         | "B"   ->  stdout.Write "  "; OctalPut         word
                         | "O"   ->  stdout.Write " ";  InstructionPut   word
                         | _     -> raise (Syntax ("Format " + words.[2] + " invalid"))
                         stdout.WriteLine ()
                     Helper last words.[3..]
            Helper -1 words
            stdout.WriteLine "%" 
            
        // show Algol stack
        let Stack () =
            let epLoc  = 137
            let evnLoc =  16
            let spLoc  = 136
            let ppLoc  = 135
            let bnLoc  = 139
            let ep     = ReadStore epLoc
            let evn    = ReadStore evnLoc
            let bn     = ReadStore bnLoc
            let pp     = ReadStore ppLoc

            // Output current stack information
            stdout.Write "EP=  "; AddressPut      ep;  stdout.WriteLine ()
            stdout.Write "ENV= "; AddressPut      evn; stdout.WriteLine ()
            stdout.Write "BN=  "; ShortNaturalPut bn;  stdout.WriteLine ()
            stdout.Write "PP=  "; AddressPut (ReadStore ppLoc);  stdout.Write "  "
            // identify current instruction and print
            let instruction = ReadStore (pp-1)
            let block = instruction &&& 0o017760
            let op = MFAlgol instruction
            if    op = ""
            then stdout.Write (Prim instruction)
            else stdout.Write op; stdout.Write ' '; ShortNaturalPut (instruction&&&mask13)
            stdout.Write"  Block= "; stdout.WriteLine block
            stdout.Write "SP=  "; AddressPut (ReadStore spLoc);  stdout.WriteLine ()
            stdout.WriteLine (); stdout.WriteLine ()

            // print a stack recursively
            let rec Entry ep evn bn block count =
                let evnNext = ReadStore (ep+4)
                let bnNext  = ReadStore (ep+3)
                let spNext  = ReadStore (ep+2)
                let ppNext  = ReadStore (ep+1)
                let epNext  = ReadStore ep
                let forEntry = spNext &&& bit18 = bit18
                // output stack frame
                stdout.Write "          "; 
                if   forEntry then stdout.Write "*******" else AddressPut evnNext
                stdout.WriteLine ()
                stdout.Write "          "; AddressPut bnNext;  stdout.WriteLine ()
                stdout.Write "          "; AddressPut spNext;  stdout.WriteLine ()
                stdout.Write "          "; AddressPut ppNext;  stdout.WriteLine ()
                AddressPut ep; stdout.Write "   "; AddressPut epNext; 
                // output stack frame type
                if forEntry 
                then stdout.Write " FOR" 
                elif bn = 16
                then stdout.Write " THUNK"
                else printf " PROC %4d" bn
                // print arguments
                if    count > 10
                then stdout.WriteLine "\n          etc, etc"
                else let Formals () = 
                         // print out arguments
                         let rec Helper i =
                             if  i >= epNext+4
                             then printfn "          %+7d %+7d %+7d" 
                                            (Normalize (ReadStore i)) 
                                            (Normalize (ReadStore (i+1))) 
                                            (Normalize (ReadStore (i+2)))
                                  Helper (i-3)
                         Helper (ep-3)                
                     if epNext <> ep
                     then // not at base of stack
                          if    ep = evn
                          then // found right environment
                               stdout.Write " *" 
                               if   bn = block
                               then stdout.WriteLine " <<<<"; stdout.WriteLine (); Formals (); stdout.WriteLine ()
                                    Entry epNext -1 bnNext -1 (count+1) // stop looking for block
                               else stdout.WriteLine ();      stdout.WriteLine (); Formals (); stdout.WriteLine ()
                                    Entry epNext evnNext bnNext block (count+1) // continue looking for block
                          else // still looking for environment
                               stdout.WriteLine (); stdout.WriteLine (); Formals (); stdout.WriteLine ()
                               Entry epNext evn bnNext block (count+1)

            // print stack
            Entry ep ep bn block 1  
            
        // display trace buffer
        let TraceBuffer () =
            for i in TraceBuffer () do
                stdout.Write "   "; AddressPut i.scr;  stdout.Write "    "; LongSignedPut i.acc; stdout.WriteLine ()                                          
             
        let mutable nonStop = false; // set true to continue after stops

        // tidy up
        let TidyUp () =
            TidyUpTelecodes ()
            TidyUpDevices ()
            TidyUpMachine ()
            nonStop  <- false

        // turn off machine - finalize any output
        let turnOff () =
            TidyUpDevices ()
            TidyUpMachine ()
            on <- false

        // turn on machine in specified configuration                  
        let turnOn arch memSize memSpeed ptrSpeed =
            CheckConfiguration arch memSize memSpeed ptrSpeed // set up required configuration
            ConfigPut ()
            on <- true
            Reset ()
            TidyUp ()

       (* // track execution against trace from 903
        let Track fileName startAddr =
            let codes = File.ReadAllBytes fileName
            let Address s index =
                let relative = (int codes.[index]) &&& 15
                s + (if relative > 7 then relative-8 else relative)
            let s0   s index = 
                        Address s index
            let sX   s index =
                let s = Address s index
                let x = ((((int codes.[index+1]) <<< 16) + ((int codes.[index+2]) <<< 8) + (int codes.[index+3])))        &&& mask18
                (s, x)
            let sXY  s index = 
                let s =  Address s index
                let x = ((((int codes.[index+1]) <<< 14) + ((int codes.[index+2]) <<< 6) + ((int codes.[index+3])) >>> 2)) &&& mask18                
                let y = ((((int codes.[index+3]) <<< 16) + ((int codes.[index+4]) <<< 8) +  (int codes.[index+5])))        &&& mask18
                (s, x, y)
            let sQAB s index = 
                let s =  Address s index
                let q = ((((int codes.[index+1]) <<< 12) + ((int codes.[index+2]) <<< 4) + ((int codes.[index+2])) >>> 4))  &&& mask18
                let a = ((((int codes.[index+2]) <<< 14) + ((int codes.[index+3]) <<< 6) + ((int codes.[index+4])) >>> 2))  &&& mask18
                let b = ((((int codes.[index+4]) <<< 16) + ((int codes.[index+6]) <<< 8) +  (int codes.[index+7])))         &&& mask18
                (s, q, a , b)
            let S0   index = 
                        (((int codes.[index+1]) <<<  8) + (int codes.[index+2])) &&& mask16
            let SX   index = 
                let s = S0 index
                let x = ((((int codes.[index+3]) <<< 16) + ((int codes.[index+4]) <<< 8) + (int codes.[index+5])))         &&& mask18
                (s, x)
            let SXY  index =
                let s = S0 index
                let x = ((((int codes.[index+3]) <<< 14) + ((int codes.[index+4]) <<< 6) + ((int codes.[index+5])) >>> 2)) &&& mask18                
                let y = ((((int codes.[index+5]) <<< 16) + ((int codes.[index+6]) <<< 8) +  (int codes.[index+7])))        &&& mask18
                (s, x, y)
            let SQAB index =  
                let s = S0 index
                let q = ((((int codes.[index+3]) <<< 12) + ((int codes.[index+4]) <<< 4) + ((int codes.[index+4])) >>> 4)) &&& mask18
                let a = ((((int codes.[index+4]) <<< 14) + ((int codes.[index+5]) <<< 6) + ((int codes.[index+6])) >>> 2)) &&& mask18
                let b = ((((int codes.[index+6]) <<< 16) + ((int codes.[index+8]) <<< 8) +  (int codes.[index+9])))        &&& mask18
                (s, q, a , b)
            let rec Decode index a q b s =
                if   index = codes.Length
                then printfn "Finished Tracking"
                elif index > codes.Length
                then failwith "Decoding Error (shouldn't happen)"
                else let ci = int codes.[index]
                     if    ci = 0
                     then Decode (index+1) a q b s
                     else let fn = ci >>> 4
                          let regs = [|"s---"; "s--Q"; "s-A-"; "s-AQ"; "sB--"; "sB-Q"; "sBA-"; "sBAQ"; "S---"; "S--Q"; "S-A-"; "S-AQ"; "SB--"; "SB-Q"; "SBA-"; "SBAQ"|]
                          printf "%s " regs.[fn]
                          match fn with
                            |  0   ->   // s
                                        let s = Address s index
                                        TracePut 4 s 0 a q b
                                        Decode (index+1) a q b s
                            |  1   ->   // sQ
                                        let s, q = sX s index
                                        TracePut 4 s 0 a q b
                                        Decode (index+4)  a q b s
                            |  2   ->   // sA
                                        let s, a = sX s index
                                        TracePut 4 s 0 a q b
                                        Decode (index+4) a q b s
                            |  3   ->   // sQA
                                        let s, q, a = sXY s index
                                        TracePut 4 s 0 a q b
                                        Decode (index+6) a q b s
                            |  4   ->   // sB
                                        let ss b = sX s index
                                        TracePut 4 s 0 a q b
                                        Decode (index+4) a q b s
                            |  5   ->   // sQB
                                        let s, q, b = sXY s index
                                        TracePut 4 s 0 a q b
                                        Decode (index+6) a q b s
                            |  6   ->   // sAB
                                        let s, a, b = sXY s index
                                        TracePut 4 s 0 a q b
                                        Decode (index+6) a q b s
                            |  7   ->   // sQAB
                                        let s, q, a, b = sQAB s index
                                        TracePut 4 s 0 a q b
                                        Decode (index+8) a q b s
                            |  8   ->   // S
                                        let s = S0 index
                                        TracePut 4 s 0 a q b
                                        Decode (index+3) a q b s
                            |  9   ->   // SQ
                                        let s, q = SX index
                                        TracePut 4 s 0 a q b
                                        Decode (index+6) a q b s
                            | 10   ->   // SA
                                        let s, a = SX index
                                        TracePut 4 s 0 a q b
                                        Decode (index+6) a q b s
                            | 11   ->   // SQA
                                        let s, q, a = SXY index
                                        TracePut 4 s 0 a q b
                                        Decode (index+8) a q b s
                            | 12   ->   // SB
                                        let s, b = SX index
                                        TracePut 4 s 0 a q b
                                        Decode (index+8) a q b s
                            | 13  ->    // SQB
                                        let s, q, b = SXY index
                                        TracePut 4 s 0 a q b
                                        Decode (index+8) a q b s
                            | 14   ->   // SAB
                                        let s, a, b = SXY index
                                        TracePut 4 s 0 a q b
                                        Decode (index+8) a q b s
                            | 15   ->   // SQAB
                                        TracePut 4 s 0 a q b
                                        let s, q, a, b = SQAB index
                                        Decode (index+10) a q b s
                            |  _   ->   failwith "Internal Error in Tracker (shouldn't happen!)"
            Decode 0 0 0 0 0*)

        
