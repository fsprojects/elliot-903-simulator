#light

module Sim900.RLB

        open System.IO
        open System.Text
        open System.Collections.Generic

        open Printf

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

        // Elliott 903 Algol relocatable binary decoding

        type SumCheck () = 
            let mutable chksum = 0
            member s.Add (bytes: byte[]) from count =
                for i in {from..3..from+count-1} do
                    chksum <- chksum + (int bytes.[i]) + (int bytes.[i+1]) + (int bytes.[i+2])

            member s.Total () = chksum &&& mask18

            member s.Reset () = chksum <- 0

        let DecodeRLB algol (bytes: byte[]) =

            let sc = new SumCheck ()

            let rec Helper i cpa cpar =

                let Error msg = 
                    TTYPrint "RLB Error: "
                    TTYPrint msg
                    TTYPrint "\n"

                if   i >= bytes.Length
                then Error "run off end of file"
                elif bytes.[i] = 0uy 
                then // blank runout
                     Helper (i+1) cpa cpar
                elif (i+2) < bytes.Length
                then // read a directive
                     let directive = ((int bytes.[i])<<<14) ||| ((int bytes.[i+1])<<<7) 
                                            ||| (int bytes.[i+2])
                     let code = directive>>>18 &&& 7
                     let word = directive &&& mask18
                     let value = Normalize word

                     let SIRId word1 word2 =
                        let buffer = new StringBuilder (6)
                        for j in seq[3;2;1] do
                            buffer.Append (SIRSymbolOf ((word1>>>((j-1)*6))&&&63)) |> ignore
                        for j in seq[3;2;1] do
                            buffer.Append (SIRSymbolOf ((word2>>>((j-1)*6))&&&63)) |> ignore
                        (buffer.ToString ()).TrimEnd ()

                     let MFSIR word =
                        let m = if word &&& bit18 <> 0 then "/" else ""
                        let f = (word>>>13) &&& 15
                        (sprintf "%s%d" m f) 

                     let SIRCode absolute word =
                        let mf = MFSIR word
                        let addr = word&&&8191
                        TTYPrint mf
                        TTYPrint (if absolute then sprintf "\t%d\t(%+d)" addr word else sprintf "\t%d;" addr)

                     let Algol absolute word =  
                        let mf = MFAlgol word
                        if   mf = ""
                        then TTYPrint (Prim word)
                             if   absolute 
                             then TTYPrint (sprintf "\t\t(%+d)" value)
                        else TTYPrint mf
                             TTYPrint (sprintf "\t%d" (word&&&8191))
                             if   absolute 
                             then TTYPrint (sprintf "\t(%+d)" value)
                             else TTYPrint ";"

                     let Address () =
                        TTYPrint (if cpar <> -1 then sprintf "(%4d)\t" cpa else sprintf " %4d;\t" cpa)
                       
                     let Word absolute word =
                        Address ()
                        (if   algol then Algol else SIRCode) absolute word
                        TTYPrint "\n"

                     let Reference () =
                        if   (i+9) < bytes.Length
                        then let word2 = ((int bytes.[i+3])<<<14) ||| ((int bytes.[i+4])<<<7) ||| (int bytes.[i+5]) &&& mask18
                             let offset = Normalize word2
                             let word3 = ((int bytes.[i+6])<<<14) ||| ((int bytes.[i+7])<<<7) ||| (int bytes.[i+8]) &&& mask18 
                             if   word&&&bit15 <> 0 // is location to be fixed absolute or relative?
                             then TTYPrint (sprintf "Fix up chain at %4d  with " (word&&&mask14))
                             else TTYPrint (sprintf "Fix up chain at %4d; with " (word&&&mask14))                            
                             if   word3 <> 0
                             then // fix absolute
                                   TTYPrint (sprintf "%4d%+d\n" (word3&&&mask17) offset)
                             else // fix relative to cpa
                                  TTYPrint (sprintf "%4d;%+d\n" cpa offset)
                             (i+9, cpa)
                        else Error "fix up chain (word missing)"; (0, 0)

                     let Global () =
                        if   (i+5) < bytes.Length
                        then let word2 = (((int bytes.[i+3])&&&127)<<<14) ||| (((int bytes.[i+4])&&&127)<<<7) 
                                                        ||| ((int bytes.[i+5])&&&127)
                             let code2 = word2>>>18 &&& 7
                             let words34 () =
                                if (i+11) < bytes.Length
                                then ((Normalize ((int bytes.[i+6])<<<14) ||| ((int bytes.[i+7])<<<7) 
                                                            ||| (int bytes.[i+8])),
                                       (Normalize ((int bytes.[i+9])<<<14) ||| ((int bytes.[i+10])<<<7) 
                                                            ||| (int bytes.[i+11])))
                                elif (i+8) < bytes.Length
                                then Error ("global - word 4 missing"); (0, 0)
                                else Error ("global - word 3 missing"); (0, 0)
                             match code2 with
                             | 0    ->  // set cpa relative to already loaded global
                                        let word3, word4 = words34 ()
                                        TTYPrint (sprintf "^%s+%d\n" (SIRId word word2) word3) 
                                        (i+12, 0)
                             | 1    ->  // Locate Global (relative)
                                        TTYPrint (sprintf "%s=%d;\n" (SIRId word word2) cpa)
                                        (i+6, cpa)
                             | 2    ->  // Reference Global
                                        let word3, word4 = words34 ()
                                        if   (i+11) < bytes.Length
                                        then Address ()
                                             TTYPrint (sprintf "%s\t%s%+d\n" 
                                                        ((if algol then MFAlgol else MFSIR) word3) (SIRId word word2) word4) 
                                             (i+12, cpa+1)
                                        else Error "Forward reference to global (word missing)"; (0, 0)
                             | 3     -> // Locate Global (absolute)
                                        let word3, word4 = words34 ()
                                        let addr = word3 &&& mask17
                                        TTYPrint (sprintf "%s=%d\n" (SIRId word word2) addr)
                                        (i+12, addr)
                             | _    -> Error ("global (unknown sub command "+(code2.ToString())+")"); (0, 0)
                        else Error "global (word 2 missing)"; (0, 0)
                        
                     match code with
                     | 0    ->  // PATCH
                                let newcpa = word &&& mask17
                                if newcpa = 131071
                                then let newcpa = if cpar = -1 then 0 else cpar
                                     TTYPrint (sprintf "$ (CPA=%d;)\n" newcpa)
                                     sc.Add bytes i 3 
                                     Helper (i+3) newcpa -1
                                else TTYPrint (sprintf "^%d\n" newcpa)
                                     sc.Add bytes i 3                                     
                                     Helper (i+3) newcpa cpa // cpar <- cpa             
                     | 1    ->  // ABSOLUTE
                                Word true word
                                sc.Add bytes i 3
                                Helper (i+3) (cpa+1) cpar
                     | 2    ->  // RELATIVE
                                Word false word
                                sc.Add bytes i 3 
                                Helper (i+3) (cpa+1) cpar
                     | 3    ->  // REFERENCE
                                let ii, ll = Reference ()
                                sc.Add bytes i (ii-i)
                                if ii <> 0 then Helper ii ll cpar
                     | 4    ->  // GLOBAL
                                let ii, ll = Global () 
                                sc.Add bytes i (ii-i)
                                if ii <> 0 then Helper ii ll cpar
                     | 5    ->  // SKIP
                                sc.Add bytes i 3
                                (if cpar <> -1 then (sprintf "(%4d) >+%d\n" cpa value) else (sprintf " %4d; >+%d\n" cpa value)) |> TTYPrint
                                Helper (i+3) (cpa+value) cpar
                     | 6    ->  // CHECKSUM
                                let expected = value
                                let found    = sc.Total ()
                                sc.Reset ()
                                TTYPrint (sprintf "Checksum %+d" expected)
                                if  expected <> found 
                                then TTYPrint (sprintf " (found %+d)\n" found)
                                else TTYPrint (sprintf "\n")
                                Helper (i+3) 0 -1
                     | 7    ->  // HALT
                                TTYPrint (sprintf "Halt %d\n" value) 
                                if algol && value = 15 then Helper (i+3) cpa cpar
                     | _    ->  failwith ("RLB problem (shouldn't happen) ("+(code.ToString())+")")

            Helper 0 0 -1

        let DecodeALGRLB = DecodeRLB true

        let DecodeSIRRLB = DecodeRLB false

        let FixRLB (fromFile: string)  (toFile: string) mode =

            let BadFile f = raise (Syntax  "Input file not .RLB, .BIN or .RAW")
            let bytes =
                if  fromFile.Length < 5
                then BadFile ()
                else let extn = fromFile.Substring ((fromFile.Length-4), 4)
                     match extn with
                     | ".BIN" | ".RLB"          -> File.ReadAllText fromFile |> TranslateFromBinary mode
                     |".RAW"                    -> File.ReadAllBytes fromFile
                     | _                        -> BadFile ()

            let sc = new SumCheck ()
            let repaired = bytes // carry over leading and trailing runout from original

            let rec Helper i  =

                let Error msg = 
                    raise (Syntax ("RLB Error: " + msg))

                if   i >= bytes.Length
                then Error "run off end of file"
                elif bytes.[i] = 0uy 
                then // blank runout
                     Helper (i+1) 
                elif (i+2) < bytes.Length
                then // read a directive
                     let directive = ((int bytes.[i])<<<14) ||| ((int bytes.[i+1])<<<7) 
                                            ||| (int bytes.[i+2])
                     let code = directive>>>18 &&& 7
                     let word = directive &&& mask18
                     let value = Normalize word
                     
                     let Global () =
                        if   (i+5) < bytes.Length
                        then let word2 = (((int bytes.[i+3])&&&127)<<<14) ||| (((int bytes.[i+4])&&&127)<<<7) 
                                                        ||| ((int bytes.[i+5])&&&127)
                             let code2 = word2>>>18 &&& 7
                             let words34 () =
                                if (i+11) >= bytes.Length
                                then Error ("global - word 4 missing")
                                elif (i+8) >= bytes.Length
                                then Error ("global - word 3 missing")
                             match code2 with
                             | 0    ->  // set cpa relative to already loaded global
                                        i+12
                             | 1    ->  // Locate Global (relative)
                                        i+6
                             | 2    ->  // Reference Global
                                        if   (i+11) >= bytes.Length
                                        then Error "Forward reference to global (word missing)"
                                        i+12
                             | 3     -> // Locate Global (absolute)
                                        i+12
                             | _    -> Error ("global (unknown sub command "+(code2.ToString())+")")
                        else Error "global (word 2 missing)"
                        
                     match code with
                     | 0        // PATCH       
                     | 1        // ABSOLUTE
                     | 2        // RELATIVE
                     | 5    ->  // SKIP
                                sc.Add bytes i 3 
                                Helper (i+3) 
                     | 3    ->  // REFERENCE
                                sc.Add bytes i 9
                                Helper (i+9) 
                     | 4    ->  // GLOBAL
                                let ii = Global () 
                                sc.Add bytes i (ii-i)
                                Helper ii
                     | 6    ->  // CHECKSUM
                                let expected = value
                                let found    = sc.Total ()
                                sc.Reset ()
                                if  expected <> found 
                                then TTYPrint (sprintf " (checksum adjusted from %+d to %+d)\n" expected found)
                                     repaired.[i]   <- (6uy <<< 4) ||| ((byte (found >>> 14)) &&& 7uy)
                                     repaired.[i+2] <- (byte ((found >>> 7) &&& 127))
                                     repaired.[i+3] <- (byte (found &&& 127))
                                Helper (i+3)                                 
                     | 7    ->  // HALT
                               ()
                     | _    ->  failwith ("RLB problem (shouldn't happen) ("+(code.ToString())+")")

            Helper 0

            if mode = Mode1 
            then // put revised back into mode 1
                for i = 0 to repaired.Length-1 do
                    repaired.[i] <- ToMode1 repaired.[i]

            let BadFile f = 
                raise (Syntax "to file not .BIN, .RLB or .RAW");

            let WriteBinaryFile (toFile: string) (bytes: byte[]) =
                let out = new StreamWriter (toFile)
                try
                    for i = 0 to repaired.Length-1 do
                        out.Write (sprintf "%4d" repaired.[i])
                        if i%20 = 19 then out.WriteLine ()
                finally out.Close ()

            if  toFile.Length < 5
            then BadFile ()
            else let extn = toFile.Substring ((toFile.Length-4), 4)
                 match extn with
                 | ".BIN" | ".RLB"          -> WriteBinaryFile toFile repaired
                 | ".RAW"                   -> File.WriteAllBytes (toFile, repaired)
                 | _                        -> BadFile ()


        let RLBtoSIR (fromFile: string) (toFile: string) mode =

            let BadFile f = raise (Syntax  "Input file not .RLB, .BIN or .RAW")

            let bytes =
                if  fromFile.Length < 5
                then BadFile ()
                else let extn = fromFile.Substring ((fromFile.Length-4), 4)
                     match extn with
                     | ".BIN" | ".RLB"          -> File.ReadAllText fromFile |> TranslateFromBinary mode
                     |".RAW"                    -> File.ReadAllBytes fromFile
                     | _                        -> BadFile ()

            let store = Array.zeroCreate (8192)

            let Error msg = raise (Syntax ("RLB Error: "+msg))

            let sc = new SumCheck ()

            let globals = new List<string> ()

            let rec FirstPass i blk cpa cpar =

                if   i >= bytes.Length
                then Error "run off end of file"
                elif bytes.[i] = 0uy 
                then // blank runout
                     FirstPass (i+1) blk cpa cpar
                elif (i+2) < bytes.Length
                then // read a directive
                     let directive = ((int bytes.[i])<<<14) ||| ((int bytes.[i+1])<<<7) 
                                            ||| (int bytes.[i+2])
                     let code = directive>>>18 &&& 7
                     let word = directive &&& mask18
                     let value = Normalize word

                     let SIRId word1 word2 =
                        let buffer = new StringBuilder (6)
                        for j in seq[3;2;1] do
                            buffer.Append (SIRSymbolOf ((word1>>>((j-1)*6))&&&63)) |> ignore
                        for j in seq[3;2;1] do
                            buffer.Append (SIRSymbolOf ((word2>>>((j-1)*6))&&&63)) |> ignore
                        (buffer.ToString ()).TrimEnd ()

                     let Reference () =
                        let rec Fix absolute loc addr count = // fix up chain of forward references 
                            // printfn "    chain location %d to %d" loc addr
                            if count >= 8192 then Error "Looping when fixing up forward references"
                            if loc   >  8190 then Error "Broken forward reference chain in RLB"
                            let prev = if store.[loc] < 8192 then store.[loc] else store.[loc]-8192
                            store.[loc] <- if absolute then addr else addr+8192
                            // 8191 is end of chain sentinel
                            if   prev <> 8191
                            then Fix absolute (if absolute then prev else prev+blk) addr (count+1)
                            
                        if   (i+9) < bytes.Length
                        then let absolute  = word &&& bit15 = bit15
                             let addrToFix = (word &&& mask14) + (if absolute then 0 else blk)
                             let word2     = ((int bytes.[i+3])<<<14) ||| ((int bytes.[i+4])<<<7) ||| (int bytes.[i+5]) &&& mask18
                             let offset    = Normalize word2
                             let word3     = ((int bytes.[i+6])<<<14) ||| ((int bytes.[i+7])<<<7) ||| (int bytes.[i+8]) &&& mask18
                             let addrToUse = (if word3 = 0 then cpa-blk else word3) + offset
                             Fix absolute addrToFix addrToUse 0
                             (i+9, cpa)
                        else Error "fix up chain (word missing)"

                     let Global () =
                        if   (i+5) < bytes.Length
                        then let word2 = (((int bytes.[i+3])&&&127)<<<14) ||| (((int bytes.[i+4])&&&127)<<<7) 
                                                        ||| ((int bytes.[i+5])&&&127)
                             let symbol = SIRId word word2
                             if not (globals.Contains symbol) then globals.Add symbol                        
                             let code2 = word2>>>18 &&& 7
                             let words34 () =
                                if (i+11) < bytes.Length
                                then ((Normalize ((int bytes.[i+6])<<<14) ||| ((int bytes.[i+7])<<<7) 
                                                            ||| (int bytes.[i+8])),
                                       (Normalize ((int bytes.[i+9])<<<14) ||| ((int bytes.[i+10])<<<7) 
                                                            ||| (int bytes.[i+11])))
                                elif (i+8) < bytes.Length
                                then Error ("global - word 4 missing"); (0, 0)
                                else Error ("global - word 3 missing"); (0, 0)
                             match code2 with
                             | 0    ->  // set cpa relative to already loaded global
                                        let word3, word4 = words34 ()
                                        (i+12, 0)
                             | 1    ->  // Locate Global (relative)
                                        (i+6, cpa)
                             | 2    ->  // Reference Global
                                        let word3, word4 = words34 ()
                                        if   (i+11) >= bytes.Length
                                        then Error "Forward reference to global (word missing)"
                                        else (i+12, cpa+1)
                             | 3     -> // Locate Global (absolute)
                                        let word3, word4 = words34 ()
                                        let addr = word3 &&& mask17
                                        (i+12, addr)
                             | _    -> Error ("global (unknown sub command "+(code2.ToString())+")")
                        else Error "global (word 2 missing)"
                        
                     match code with
                     | 0    ->  // PATCH
                                let newcpa = word &&& mask17
                                if newcpa = 131071
                                then let newcpa = if cpar = -1 then 0 else cpar
                                     sc.Add bytes i 3 
                                     FirstPass (i+3) blk newcpa -1
                                else sc.Add bytes i 3                                     
                                     FirstPass (i+3) blk newcpa cpa // cpar <- cpa             
                     | 1    ->  // ABSOLUTE
                                store.[cpa] <- word &&& 8191
                                sc.Add bytes i 3 
                                FirstPass (i+3) blk (cpa+1) cpar
                     | 2    ->  // RELATIVE
                                store.[cpa] <- (word &&& 8191)+8192
                                sc.Add bytes i 3 
                                FirstPass (i+3) blk (cpa+1) cpar
                     | 3    ->  // REFERENCE
                                let ii, ll = Reference ()
                                sc.Add bytes i (ii-i)
                                FirstPass ii blk ll cpar
                     | 4    ->  // GLOBAL
                                let ii, ll = Global () 
                                sc.Add bytes i (ii-i)
                                FirstPass ii blk ll cpar
                     | 5    ->  // SKIP
                                sc.Add bytes i 3
                                FirstPass (i+3) blk (cpa+value) cpar
                     | 6    ->  // CHECKSUM
                                let expected = value
                                let found    = sc.Total ()
                                sc.Reset ()
                                if  expected <> found 
                                then MessagePut "Checksum error in RLB file (ignored)"
                                FirstPass (i+3) cpa cpa -1
                     | 7    ->  // HALT
                                ()
                     | _    ->  failwith ("RLB problem (shouldn't happen) ("+(code.ToString())+")")
                
            FirstPass 0 0 0 -1
             
            globals.Sort ()

            let out = new StreamWriter (toFile)
            let GlobalsList () =
                fprintfn out "["
                for  g in globals do 
                    fprintf out " "
                    fprintfn out "%s" g
                fprintfn out "]"
                fprintfn out ""

            let rec SecondPass i blk cpa cpar = 

                if bytes.[i] = 0uy 
                then // blank runout
                     SecondPass (i+1) blk cpa cpar
                else // read a directive
                     let directive = ((int bytes.[i])<<<14) ||| ((int bytes.[i+1])<<<7) 
                                            ||| (int bytes.[i+2])
                     let code = directive>>>18 &&& 7
                     let word = directive &&& mask18
                     let value = Normalize word

                     let SIRId word1 word2 =
                        let buffer = new StringBuilder (6)
                        for j in seq[3;2;1] do
                            buffer.Append (SIRSymbolOf ((word1>>>((j-1)*6))&&&63)) |> ignore
                        for j in seq[3;2;1] do
                            buffer.Append (SIRSymbolOf ((word2>>>((j-1)*6))&&&63)) |> ignore
                        (buffer.ToString ()).TrimEnd ()

                     let Reference () =
                             (i+9, cpa)

                     let Global () =
                        let word2 = (((int bytes.[i+3])&&&127)<<<14) ||| (((int bytes.[i+4])&&&127)<<<7) 
                                                        ||| ((int bytes.[i+5])&&&127)
                        let code2 = word2>>>18 &&& 7
                        let words34 () =
                                ((Normalize ((int bytes.[i+6])<<<14) ||| ((int bytes.[i+7])<<<7) 
                                                            ||| (int bytes.[i+8])),
                                 (Normalize ((int bytes.[i+9])<<<14) ||| ((int bytes.[i+10])<<<7) 
                                                            ||| (int bytes.[i+11])))
                        match code2 with
                             | 0    ->  // set cpa relative to already loaded global
                                        let word3, word4 = words34 ()
                                        fprintfn out "^%s+%d" (SIRId word word2) word3 
                                        (i+12, 0)
                             | 1    ->  // Locate Global (relative)
                                        fprintfn out "%s" (SIRId word word2)
                                        (i+6, cpa)
                             | 2    ->  // Reference Global
                                        let word3, word4 = words34 ()
                                        let m = if word3 &&& bit18 <> 0 then "/" else ""
                                        let f = (word3>>>13) &&& 15
                                        fprintfn out "\t%s%d\t%s%+d" m f (SIRId word word2) word4 
                                        (i+12, cpa+1)
                             | 3     -> // Locate Global (absolute)
                                        let word3, word4 = words34 ()
                                        let addr = word3 &&& mask17
                                        fprintfn out "%s=%d" (SIRId word word2) addr
                                        (i+12, addr)
                             | _    -> Error ("global (unknown sub command "+(code2.ToString())+")")
                        
                     match code with
                     | 0    ->  // PATCH
                                let newcpa = word &&& mask17
                                if newcpa = 131071
                                then fprintfn out "$" 
                                     SecondPass (i+3) blk newcpa -1
                                else fprintfn out "^%d;" newcpa                
                                     SecondPass (i+3) blk newcpa cpa // cpar <- cpa             
                     | 1        // ABSOLUTE
                     | 2    ->  // RELATIVE
                                let rel = cpa-blk
                                if rel%10=0 then fprintf out "(%3d;)" rel
                                let m = if word &&& bit18 <> 0 then "/" else ""
                                let f = (word>>>13) &&& 15
                                let v        = Normalize word
                                let fraction = (float v) / 131072.0
                                let text     = sprintf "%+8.6f" fraction
                                let digits   = text.Substring (2)
                                let sign     = if fraction >= 0.0 then '+' else '-'
                                if   store.[cpa] < 8192 
                                then fprintfn out ("\t%s%d\t%d\t(%+7d %c%s &%06o)")  m f  store.[cpa] v sign digits word                            
                                else fprintfn out ("\t%s%d\t%d;")  m f (store.[cpa]-8192)
                                SecondPass (i+3) blk (cpa+1) cpar
                     | 3    ->  // REFERENCE
                                let ii, ll = Reference ()
                                SecondPass ii blk ll cpar
                     | 4    ->  // GLOBAL
                                let ii, ll = Global () 
                                SecondPass ii blk ll cpar
                     | 5    ->  // SKIP
                                sc.Add bytes i 3
                                fprintfn out "\t>+%d"  value 
                                SecondPass (i+3) blk (cpa+value) cpar
                     | 6    ->  // CHECKSUM
                                fprintfn out ""
                                GlobalsList ()
                                SecondPass (i+3) cpa cpa -1
                     | 7    ->  // HALT
                                fprintfn out "%%"
                                fprintfn out "<! halt !>"
                     | _    ->  failwith ("RLB problem (shouldn't happen) ("+(code.ToString())+")")

            fprintfn out "*1"
            GlobalsList ()
            SecondPass 0 0 0 -1
            out.Close ()