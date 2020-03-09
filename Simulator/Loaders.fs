#light

module Sim900.Loaders

        open System.IO
        open System.Text

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

        // Elliott 900 Simulator loader format decoding

        // Sum checked binary tape decode
        let rec SCBDecode () =

            let NextChar () = int (GetReaderChar ())

            // initial instructions loader format
            let IILdr () =
                let rec helper acc =
                    let  ch    = NextChar ()
                    let newacc = acc <<< 7 ||| ch
                    if    newacc &&& bit18 <> 0
                    then (newacc <<< 7 ||| (int (GetReaderChar ()))) &&& mask18
                    else helper newacc
                helper 0

            // functions to handle triples
            let Triple ch1 =
                let ch2 = NextChar ()
                let ch3 = NextChar ()
                ((ch1 <<< 14)  ||| (ch2 <<< 7) ||| ch3) &&& mask18

            let rec FindTriple () =
                let ch1 = NextChar ()
                if   ch1 = 0
                then FindTriple ()
                else Triple ch1
                
            let rec GetTriple () =
                Triple (NextChar ())
                
            // Simple Loader
            let SimpleLdr version =
                MessagePut (sprintf "Found Simple Loader (%s)" version)
                let rec LoadRegion start checksum  signature =
                    let rec helper address checksum  signature =
                        let word = GetTriple ()
                        if   word <> 0
                        then WriteStore address word
                             helper (address+1) ((checksum - word) &&& mask18) (signature+word)
                        else (address-1, checksum)
                    let finish, checksum = helper start checksum signature
                    // finished loading region
                    MessagePut (sprintf "Block  %d to %d loaded" start finish)
                    let directory = GetTriple ()
                    if  directory = 0
                    then MessagePut "Simple Loader finished"
                         MessagePut (sprintf "Checksum &%o %s" checksum (if checksum = 0 then "OK" else "Wrong"))
                         MessagePut (sprintf "Signature %d" signature)
                    else // load next region
                         LoadRegion directory checksum (signature+directory)
                let start = FindTriple ()
                LoadRegion start (ReadStore 8179) 0

            let ACDLdr () = 
            
                MessagePut "Found ACD Loader"
                
                let rec ReadWords first b n checksum = 
                    // printfn "Readwords first=%d b=%d n=%d" first b n
                    let ch1 = NextChar ()
                    if   ch1 <> 0
                    then let wd = Triple ch1
                         WriteStore (b+n) wd
                         ReadWords first b (n+1) (checksum+wd)
                    else MessagePut (sprintf "Block %5d to %5d loaded" (first+b) (b+n-1))
                         checksum 

                and CheckForEnd b checksum = 
                    // printfn "CheckForEnd b=%d" b
                    let wd1 = FindTriple () + 1
                    if   wd1 <> (8 <<< fShift) + 8181
                    then ReadBlock b wd1 checksum+wd1-1
                    elif GetTriple () <> 0
                    then raise (Syntax "Blank 4 Missing")
                    else checksum+wd1-1

                and ReadBlock b wd1 checksum = 
                    // printfn "Readblock b=%d" b
                    let order = (wd1 >>> fShift) &&&  31
                    match order with
                    |  5 -> printfn "5 case %d" (wd1 &&& operandMask)
                            if wd1 &&& operandMask <> 1 then raise (Syntax "5 N, N<>0")
                            let newb = GetTriple ()
                            // printf "New B %d" newb
                            if   NextChar () <> 0 then raise (Syntax "Blank 2 missing")
                            let wd2 = GetTriple () + 1
                            if   (wd2 >>> fShift) &&& 31 <> 21 
                            then raise (Syntax "Missing /5 N")
                            else let first = wd2 &&& operandMask
                                 let cs = ReadWords first newb first (checksum+newb+wd2-1)
                                 CheckForEnd newb cs
                    | 21 -> printfn "/5 case"
                            let first = wd1 &&& operandMask
                            let cs = ReadWords first b first checksum
                            CheckForEnd b cs
                    | _  -> raise (Syntax (sprintf "Missing 5 0 or /5 N  %d %d" (wd1>>>fShift&&&31) (wd1&&&operandMask)))
                
                if   NextChar () <> 0
                then raise (Syntax "Blank 1 Missing")
                else let wd1 = GetTriple () + 1
                     let checksum = ReadBlock 0 wd1 (wd1-1)
                     MessagePut "ACD Loader completed"
                     MessagePut (sprintf "Checksum  = %d" (checksum &&& mask18))
                     SCBDecode ()

            let PERTLdr () =
                MessagePut "Found PERT Loader"
                let Error opCode addr = raise (Syntax (sprintf "Unexpected %s%d %d" (if opCode > 15 then "/" else "") (opCode &&& 15) addr))
                let rec helper first last next checksum  =
                    let ReportBlock () = 
                        if   last >= first
                        then MessagePut (sprintf "Block %5d to %5d loaded" (first+1) (last+1))
                    let ch1 = int (GetReaderChar ())
                    if   ch1 = 0
                    then let order      = GetTriple ()
                         let opCode     = order >>> 13
                         let address    = order &&& 8191
                         match opCode with
                         |  5   ->  //  5 x
                                    ReportBlock ()
                                    helper address last address (checksum + order)
                         |  8   ->  // 8 8180
                                    if   address <> 8164
                                    then Error opCode address
                                    else ReportBlock ()
                                         let chk1 = GetTriple ()
                                         let chk2 = (checksum+order) &&& mask18
                                         MessagePut "PERT Loader completed"
                                         MessagePut (sprintf "Checksum &%o %s" chk2 (if chk1 = chk2 then "OK" else "Wrong"))
                                         MessagePut (sprintf "Signature %d" chk1)
                         | _    ->  Error opCode address
                    else let ch2 = NextChar ()
                         let ch3 = NextChar ()
                         let order = ((ch1 <<< 14) ||| (ch2 <<< 7) ||| ch3) &&& mask18
                         WriteStore (next+1) order
                         helper first next (next+1) (checksum + order)
                helper 0 -1 0 0 

            let T23Ldr twoChecksums offset =
                let rec Block ch1 first last next dsum wdsum signature =
                    if ch1 &&& 128 <> 0
                    then // directory
                         if   last >= first
                         then MessagePut (sprintf "Block %5d to %5d loaded" first last)
                         let directory = Triple ch1
                         printfn "Directory %7d" directory
                         if   directory = 0
                         then // directory = 0 => sum checks
                              let sc1     = GetTriple ()
                              let wdsum18 = wdsum &&& mask18
                              if   sc1 <> wdsum18 then MessagePut (sprintf "Word sum check failed      %7d %7d" sc1 wdsum18)
                              if twoChecksums
                              then let sc2    = GetTriple ()
                                   let dsum18 = dsum &&& mask18
                                   if   sc2 <> dsum18  then MessagePut (sprintf "Directory sum check failed %7d %7d" sc2 dsum18)
                              MessagePut "T23 Complete - checksum ok"
                              MessagePut (sprintf "Signature = %d" signature)
                         else // directory is address at which to load next word
                              Block (NextChar ()) directory last directory (dsum+directory) 
                                        (if twoChecksums then  wdsum else wdsum+directory) 
                                            (signature+directory)
                    else // word to load
                         let wd = Triple ch1
                         WriteStore (if offset <> -1 then next+(ReadStore 15) else next) wd
                         Block(NextChar ()) first next (next+1) dsum (wdsum+wd) (signature+wd)

                let rec GetFirst () =
                    let ch1 = NextChar ()
                    if   ch1 = 0
                    then GetFirst ()
                    else ch1
                    
                Block (GetFirst ()) 0 -1 0 0 0 0
                         
            let AldRLB () =
                MessagePut "Found AldRLB T23 Loader"
                let rec Helper count sum =
                    let ch = NextChar ()
                    let relative = ch &&& 64 <> 0
                    let w = Triple ch
                    if   relative && (w &&& mask18 = 0)
                    then MessagePut (sprintf " %6d words loaded" count)
                         let check = GetTriple ()
                         if   ((sum+w) &&& mask18) <> check
                         then MessagePut (sprintf "Check failed - expected: %d, found %d" sum check)
                         else MessagePut "Checksum OK"
                    else Helper (count+1) (sum+w)
                Helper 0 0

            let T23 () =
                MessagePut "Found: T23 Loader"
                T23Ldr true -1

            let Algol version =
                MessagePut (sprintf "Found: ALGOL T23 (%s)" version)
                T23Ldr true -1

            let Masir () =
                MessagePut "Found: MASIR"
                T23Ldr false -1

            let Maplod () =
                MessagePut "Found: MAPLOD"
                T23Ldr true 15

            let CandG () =
                MessagePut "Found: C&G Mnemonic Code"
                for i= 1 to 24  do
                    WriteStore (5180-i) (ReadStore (8180-i))                           
                let rec helper loc check =
                    let mkr = NextChar ()
                    if   mkr <> 0
                    then let wd = (((mkr<<<14)+(NextChar()<<<7)+(NextChar()))&&&mask18)
                         let newCheck = ((Normalize check) - (Normalize wd)) &&& mask18
                         if   mkr > 32
                         then helper (loc+1) newCheck
                         else MessagePut (sprintf "Loaded locations 8-%d" loc)
                              if   newCheck <> 0 
                              then MessagePut (sprintf "Checksum failed: %d" newCheck)
                              else MessagePut "Checksum OK"
                    else helper loc check
                helper 8 (ReadStore 8179)

            let AlgolClearStore () =
                MessagePut "Found: Clear Store 2-8175 (903 ALGOL)"
                for i = 2 to 8175 do WriteStore i 0

            let Jump8181 () =
                MessagePut "Initial instructions loader started"
                // read three words
                for i = 0 to 2 do WriteStore (8177+i) (IILdr ())
                // check contents
                if   (ReadStore 8177) <> (InstructionToWord (0, 0, 8179)) && 
                     (ReadStore 8178) <> (InstructionToWord (0, 8, 8182))
                then DisplayRange2 8177 8179
                     raise (Syntax "Non-standard stage 1")
                MessagePut "Stage 1 complete"
                let wds = -(Normalize (ReadStore 8179))
                MessagePut (sprintf "Stage 2 complete - read %d words %d-8179" wds (8180-wds))
                let mutable signature = 0
                for i = 0 to wds-1 do 
                    let word = IILdr ()
                    signature <- signature + word
                    WriteStore (8180-wds+i) word
                // filter out checksums
                if    wds = 6
                then signature - (ReadStore 8174) - (ReadStore 8175) // ACD sumcheck
                elif wds = 24
                then signature - (ReadStore 8156) // AldRLB Locator
                else signature - (ReadStore 8179) // X12/17
            // see if we can match loaded program to a known program
            let signature = Jump8181 ()
            match signature with
            
            |  +268228      ->  MessagePut "Found: ACD trailer"
                                MessagePut (sprintf "Checksum = %d" (ReadStore 8174))
                                let trigger = (ReadStore 8175) &&& 8191
                                if   trigger = 8175
                                then MessagePut "Loop Stop"
                                else MessagePut (sprintf "Jump to %d" trigger)

            |  +278489      ->  MessagePut "Found ACD Clear Basic Store"
                                ClearModule 0
                                SCBDecode ()

            |  +401384      ->  MessagePut "Found: Clear Store 2-8175 (X2, X12, X17, X400)"
                                for i = 2 to 8175 do WriteStore i 0
                                SCBDecode ()

            |  +401385      ->  AlgolClearStore (); SCBDecode ()

            |  +491462      ->  MessagePut "Found ACD Clear Extended Store"
                                let count = 8192 - (Normalize (ReadStore 8179))
                                MessagePut (sprintf "Clear Extended Store from 8192 to %d" count)
                                for i = 1 to count/8192+1 do ClearModule i
                                SCBDecode ()

            |  +507887      ->  MessagePut "Found 903 FORTRAN 16K Clear Store"
                                for i = 1 to 8174 do
                                    WriteStore i        0
                                    WriteStore (i+8191) 0
                                SCBDecode ()

            |  +565217      -> MessagePut "Found 903 ALGOL LP Clear Store 8192-16383 "
                               for i = 0 to 8191 do WriteStore (8192+i) 0
                               SCBDecode ()

            |  +718718      ->  ACDLdr ()

            |  +810931      ->  MessagePut "Found: Clear Store 2-8169 (X1, X3, X4, X5, 903 FORTRAN)"
                                for i = 2 to 8169 do WriteStore i 0
                                SCBDecode ()

            |  +947993      ->  PERTLdr ()

            |  +1252995     ->  MessagePut "Found: AldRLB Locator"; SCBDecode ()

            |  +1411244     ->  MessagePut "Found: SIR Loader"

            |  +2252553     ->  SimpleLdr "Found: X12/X17"

            |  +2260719     ->  SimpleLdr "Found: 920 ALGOL"

            |  +2358776     ->  CandG ()

            |  +2891048     ->  AldRLB ()

            |  +3094030     ->  T23 ()

            |  +3153433     ->  Masir ()

            |  +3347998     ->  Algol "Found: 16K LG HUNTER translator"
                                let s = Jump8181 ()
                                if   s = +401385
                                then AlgolClearStore ()
                                     let s = Jump8181 ()
                                     MessagePut (sprintf "%+d" s)
                                     if   s = +3347998
                                     then Algol "16K LG HUNTER interpreter"
                                     else MessagePut "Interpreter expected"
                                else MessagePut "Clear store expected"

            |  +3352251     ->  Algol "16K LP ISSUE 6 Part 1"
                                Algol "16K LP ISSUE 6 Part 2"

            |  +3356159     ->  Algol "8K DUMPER"

            |  +3356169     ->  AldRLB ()

            |  +3372189     ->  Maplod ()

            | _             ->  // if wds < 50 then DisplayRange2 (8180-wds) 8179
                                MessagePut (sprintf "Unknown - Signature %d" signature)
                 
 