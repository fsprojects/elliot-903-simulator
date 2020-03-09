#light

module Sim900.FileHandling

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

        // Elliott 903 Algol simulator file handling commands

        // Delete
        let Delete file =
            try File.Delete file with
            | e -> MessagePut e.Message

        // Open file to 900 paper tape stream
        let FileOpen (f: string) mode =
            if  f.Length < 5
            then OpenReaderRaw mode f
            else let extn = f.Substring ((f.Length-4), 4)
                 match extn with
                 | ".900" | ".DAT" | ".TXT" -> OpenReaderText T900 mode f
                 | ".ACD"                   -> OpenReaderText TACD mode f
                 | ".903"                   -> OpenReaderText T903 mode f
                 | ".920"                   -> OpenReaderText T920 mode f
                 | ".BIN" | ".RLB"          -> OpenReaderBin mode f
                 |".RAW"                    
                 | _                        -> OpenReaderRaw mode f

        // change directory
        let ChangeDir d =
            if   Directory.Exists d 
            then System.Environment.CurrentDirectory <- d
            else raise (Syntax (sprintf "Cannot open directory %s" d))

        // IMAGES are dumps of memory write out as four bytes per word.
        // words 0-7 are not included in the file
        // (this format is due to Terry Froggatt)

        // dump image -- size is the total memory size, from 0
        let DumpImage fileName size =
            File.WriteAllBytes (fileName, (DumpImage size))

        // load image -- load a previously dumped image
        let LoadImage fileName =
            let fi = fileName+".IMG"
            let f = if File.Exists fileName then fileName elif File.Exists fi then fi else fileName
            let bytes = File.ReadAllBytes f
            if bytes.Length % 4 <> 0 then raise (Syntax "Wrong number of bytes in file")
            LoadImage bytes

        // MODULES are dumps of a store module encoded as pairs of integers representing consecutive half words
        // (this format is due to Don Hunter)

        // load module
        let LoadModule moduleNo fileName =
            let fd = fileName+".DAT"
            let f = if File.Exists fileName then fileName elif File.Exists fd then fd else fileName
            let file = File.ReadAllText (f) 
            let words = file.Split ([|' '; '\t'; '\n'; '\r'|], System.StringSplitOptions.RemoveEmptyEntries) 
            let values = 
                try 
                    Seq.map (fun word -> int word) words |> Seq.toArray 
                with | err -> raise (Syntax (sprintf "Error decoding file - %s" err.Message))
            if  values.Length = 0 || values.Length > 16384 || values.Length % 2 <> 0 
            then raise (Syntax "Wrong number of words in file")
            let maxAddr = (values.Length)/2-1
            let words: int[] = Array.zeroCreate (maxAddr+1)                
            for addr = 0 to maxAddr do 
                let index = addr * 2
                words.[addr] <- (values.[index] <<< 13) ||| values.[index+1]
            LoadModule moduleNo words

        // dump as SIR 
        let DumpAsSir fileName literals =
            let tw = File.CreateText fileName
        
            // build list of possible labels
            let labels: bool[] = Array.create memorySize false

            let rec SetLabels prevF prevAddr loc lastLiteral =
                if   loc < literals
                then let contents = ReadStore loc
                     let f = FunctionField contents
                     let addr = AddressField contents
                     if   addr > literals && addr < lastLiteral && (f = 3 || f = 5 || f = 11)
                     then labels.[addr] <- true
                          SetLabels prevF prevAddr loc addr
                     elif  addr >= 8              // exclude registers
                          && abs (addr-loc) >  5 // exclude relative addresses
                          && 0 < f && f < 14     // exclude 14, 15 instructions
                     then if prevF = 11 && (addr=prevAddr+1 || addr=prevAddr+2)
                          then SetLabels f addr  (loc+1) lastLiteral // exclude subroutine calls
                          elif addr < literals
                          then labels.[addr] <- true
                               SetLabels f addr (loc+1) lastLiteral
                          else SetLabels f addr (loc+1) lastLiteral
                     else SetLabels f addr (loc+1) lastLiteral
                else lastLiteral

            let lastLiteral = SetLabels -1 -1 8 8192

            if   literals <> memorySize
            then MessagePut (sprintf "Literals from %d to %d" literals lastLiteral)

            let Comment contents = 
                let number = Normalize contents
                // print as octal
                tw.Write (sprintf "\t(&%06o" contents)
                // print as integer
                tw.Write (sprintf " %+8d " number)
                // print as instruction
                tw.Write "\\"
                for i in [12;6;0] do
                        let ch = (contents>>>i)&&&mask6
                        tw.Write (match ch with
                                 |  1 -> '^'
                                 |  5    // % -- to avoid terminating program
                                 |  9    // ) -- to avoid closing comment
                                     -> '?'
                                 | _  -> SIRSymbolOf ch)
                let modify = ModifyField contents
                let f = FunctionField contents
                if modify = 0 then tw.Write ' '
                if f < 10 then tw.Write ' '
                tw.Write ' '
                if modify <> 0 then tw.Write '/'
                tw.Write (sprintf "%d %d" f (AddressField contents))
                tw.WriteLine ')'

            let rec Words prevF prevAddr loc limit =
                if loc <= limit
                then let contents = ReadStore loc
                     let number = Normalize contents
                     let modify = ModifyField contents
                     let m = if modify = 0 then "" else "/"
                     let f = FunctionField contents
                     let addr = AddressField contents
                     // if location is referenced, output label
                     if   labels.[loc] 
                     then tw.Write (sprintf "L%d\t" loc)
                     else tw.Write "\t"
                     let addr = AddressField contents
                     if   -8192 < number && number < 0
                     then // /15 n
                          tw.Write (sprintf"%+d" number)
                     elif 0 <= number && number < 8192 && number < literals && (not labels.[number])
                     then // 0 n
                          tw.Write (sprintf "%+d" number)
                     elif f >= 14
                     then // special case 14 and 15 instructions
                          tw.Write (sprintf "%s%d %d" m f addr)
                     elif limit <= 8192 && literals <= addr && addr <= lastLiteral 
                          && (f <= 2 || f = 4 || f = 6 || f = 12 || f = 13)
                     then // special case literals
                          tw.Write (sprintf "%s%d " m f)
                          let value = ReadStore addr
                          let f = FunctionField value
                          let m = if (ModifyField value) = 0 then "" else "/"
                          let number = Normalize value
                          if    number = 0
                          then tw.Write "+0"
                          elif   (AddressField value) = 0 
                          then // e.g. =11 0 
                               tw.Write (sprintf "=%s%d 0" m f)
                          elif -8192 < number && number < 8192
                          then // e.g., +1 -16
                               tw.Write (sprintf "%+d"   number)
                          else // all others as octal
                               tw.Write (sprintf "&%06o" value)
                     elif prevF = 11 && labels.[prevAddr] && (addr = prevAddr+1 || addr = prevAddr+2)
                     then // special case subroutine entry
                          tw.Write (sprintf "%s%d L%d+%d" m f prevAddr (addr-prevAddr))
                     elif abs(addr-loc) <= 5
                     then tw.Write (sprintf "%s%d ;%+d" m f (addr-loc))
                     elif labels.[addr] 
                     then // addressing labelled location
                          tw.Write (sprintf "%s%d L%d" m f addr)
                     elif addr < literals
                     then tw.Write (sprintf "%s%d %d" m f addr)
                     else tw.Write (sprintf "&%06o" contents)
                     Comment contents
                     Words f addr (loc+1) limit

            tw.WriteLine (sprintf "\n\n(output from DUMPASSIR %s %s)\n"
                                    (System.DateTime.Now.ToShortDateString ())
                                    (System.DateTime.Now.ToShortTimeString ()))
            let limit = min 8166 literals // 8166 is maximum location allowed in module 0 by 2-pass SIR
            // comment output labels for addresses above literals
            for loc=lastLiteral to 8191 do
                if labels.[loc]
                then tw.WriteLine (sprintf "L%d=%d" loc loc)
            if   memorySize = 4096
            then tw.WriteLine "*16 (start at 8)"
                 Words -1 -1 8 memorySize
            elif memorySize = 8192
            then tw.WriteLine "*8192"
                 tw.WriteLine "*16 (clear 8K, start at 8)"
                 Words -1 -1 8 limit
            else tw.WriteLine "*16384"
                 tw.WriteLine "*16 (clear 16K, start at 8)"
                 Words -1 -1 8 limit // stop at limit for 2-pass SIR
                 if   memorySize > 8192
                 then tw.WriteLine "^8192"
                      Words -1 -1 8192 16383
            tw.WriteLine "%"
            tw.WriteLine "<! Halt !>"
            tw.Close ()             
                 
        // list directory
        let ListDirectory () =
            Directory.EnumerateFileSystemEntries "." 
                |> Seq.iter (fun s -> printfn "%s" s.[2..])

        // pretty printer
        let TabText  telecode (chars: byte[]) =
            let rec tabs inx out =
                if   inx < chars.Length
                then let text = UTFOf telecode chars.[inx]
                     if   text = "\r\n" || text = "\n"  // 920 telecode maps \n to \r\n
                     then TTYPrint "\r\n"
                          tabs (inx+1) 1
                     elif text = "\r"  
                     then tabs (inx+1) 1 // ignore return  
                     elif text <> "\t"
                     then (sprintf "%s" text) |> TTYPrint
                          tabs (inx+1) (out+text.Length)
                     else let col =
                             if out < 11 then 11 else (out + 3) / 10 * 10 + 7 // 1,11,17,27,37,47,...
                          // printfn "\n inx %3d out %3d col %3d" inx out col 
                          for i = out to col-1 do TTYPrint " "
                          tabs (inx+1) col
            tabs 0 0

        let Title f = (sprintf "\r\n\nPrint File %s\n\n" f) |> TTYPrint

        let PrettyACD f = 
            Title f
            File.ReadAllText f |> TranslateFromText TACD Mode3 |> TabText TACD

        let Pretty900 f = 
            Title f
            File.ReadAllText f |> TranslateFromText T900 Mode3 |> TabText T900

        let Pretty903 f = 
            Title f
            File.ReadAllText f |> TranslateFromText T903 Mode3 |> TabText T903

        let Pretty920 f = 
            Title f
            File.ReadAllText f |> TranslateFromText T920 Mode3 |> TabText T920

        let TabBinary (bytes: byte[]) =
            for i = 0 to bytes.Length-1 do
                    (sprintf "%4d" bytes.[i]) |> TTYPrint
                    if i%20 = 19 then TTYPrint "\n"

        let PrettyBin f mode = 
            Title f
            TranslateFromBinary mode (File.ReadAllText  f) |> TabBinary

        let PrettySIRRLB f mode =  
            Title f     
            TranslateFromBinary mode (File.ReadAllText  f) |> DecodeSIRRLB

        let PrettyALGRLB f mode =  
            Title f      
            TranslateFromBinary mode (File.ReadAllText  f) |> DecodeALGRLB
        
        let PrettyDat f = 
            Title f
            TTYPrint (File.ReadAllText f)   

        let PrettyRaw f mode = 
            Title f            
            TranslateFromRaw mode (File.ReadAllBytes  f) |> TabBinary

        let Print (f: string) mode =
            if f.Length > 4
            then let extn = f.[f.Length-4..]
                 match extn with 
                 | ".ACD" -> PrettyACD f
                 | ".900" -> Pretty900 f 
                 | ".903" -> Pretty903 f 
                 | ".920" -> Pretty920 f
                 | ".BIN" -> PrettyBin f mode 
                 | ".RLB" -> PrettySIRRLB f mode
                 | ".RAW" -> PrettyRaw f mode
                 | ".DAT" 
                 | ".TXT" -> PrettyDat f
                 | _      -> raise (Syntax "Not a DAT, TXT, 900, 903, 920, BIN, RLB or RAW file")
             else raise (Syntax "File name does not include an extension, e.g., .903")                 

        // read inline text
        let ReadInlineText () =
            let s = new StringBuilder ()
            let rec nextLine () =
                let line = System.Console.ReadLine ()
                if   line = null   // end of file terminates
                then s.ToString () // return as string
                elif line.EndsWith "<!!>"
                then // <!!> at end of line terminates
                     s.Append(line.Substring (0, line.Length-4)).ToString()
                else (s.Append line).Append ("\n") |> ignore
                     nextLine () 
            let out = nextLine () 
            // printfn "INLINE %s INLINE" (VisibleWhiteSpace out)
            out

        // binary files tabulation
        let WriteBinary (out: StreamWriter) bytes = 
            bytes |> Array.iteri (fun i b ->  (if i%20=19 then out.WriteLine (sprintf "%4d" b) 
                                                          else out.Write     (sprintf "%4d" b)))
            out.Close ()
             
        let Reverse (f: string)  =
            if f.Length > 4
            then let extn = f.[f.Length-4..]
                 match extn with 
                 | ".BIN" -> TranslateFromBinary Mode3 (File.ReadAllText  f) |> Array.rev |> WriteBinary (new StreamWriter (f))
                 | ".RLB" -> TranslateFromBinary Mode3 (File.ReadAllText  f) |> Array.rev |> WriteBinary (new StreamWriter (f)) 
                 | ".RAW" -> File.WriteAllBytes (f, (File.ReadAllBytes f |> Array.rev))
                 | _      -> raise (Syntax "Not a BIN, RLB or RAW file")
             else raise (Syntax "File name does not include an extension, e.g., .BIN")         

        // convert file to binary format
        let ToBinary (f: string)  =
            let bytes =
                if f.EndsWith ".RAW"
                then File.ReadAllBytes f |> TranslateFromRaw Mode3
                elif f.EndsWith ".acd" 
                then File.ReadAllText  f |> TranslateFromText TACD Mode3
                elif f.EndsWith ".900" || f.EndsWith ".DAT" || f.EndsWith ".TXT"
                then File.ReadAllText f  |> TranslateFromText T900 Mode3
                elif f.EndsWith ".903"
                then File.ReadAllText  f |> TranslateFromText T903 Mode3
                elif f.EndsWith ".920"
                then File.ReadAllText f |> TranslateFromText T920 Mode3
                else raise (Syntax "File extension must be .RAW, .900, .903 or .920")
            let prefix = f.[..(f.Length-5)]
            use out = new StreamWriter (prefix+".BIN")
            WriteBinary out bytes
            out.Close ()

        // remove leading and trailing blanks from a byte array
        let Trim (bytes: byte[]) =
            let rec TrimLeft i =
                    if   i >= (bytes.Length)
                    then 0
                    elif bytes.[i] = 0uy 
                    then TrimLeft (i+1) 
                    else i
            let rec TrimRight i =
                if   i = 0
                then 0
                elif bytes.[i] = 0uy 
                then TrimRight (i-1) 
                else i
            let start  = TrimLeft 0 
            let finish = TrimRight (bytes.Length-1)
            (start, finish)

        // convert file to raw bytes
        let ToRaw (f: string)  =
            let bytes =
                if f.EndsWith ".BIN" || f.EndsWith ".RLB"
                then File.ReadAllText f |> TranslateFromBinary Mode3
                elif f.EndsWith ".acd" 
                then File.ReadAllText f |> TranslateFromText TACD Mode3
                elif f.EndsWith ".900" || f.EndsWith ".DAT" || f.EndsWith ".TXT"
                then File.ReadAllText f |> TranslateFromText T900 Mode3
                elif f.EndsWith ".903"
                then File.ReadAllText f |> TranslateFromText T903 Mode3
                elif f.EndsWith ".920"
                then File.ReadAllText f |> TranslateFromText T920 Mode3
                else raise (Syntax "File extension must be .BIN, .RLB, .900, .903 or .920")
            let start, finish = Trim bytes
            let output: byte[] = Array.zeroCreate (finish-start+1+360)
            for i=start to finish do output.[i-start+180] <- bytes.[i]
            let prefix = f.[..(f.Length-5)]
            File.WriteAllBytes ((prefix+".RAW"), output)     

        // convert file to telecode format
        let ToTelecode (f: string) telecode =
            let BadFile () = raise (Syntax "File extension must be .ACD, .BIN, .RAW, .DAT, .TXT, .900, .903 or .920")
            if   f.Length < 5
            then BadFile ()
            else let extn = f.Substring(f.Length-4, 4)
                 let bytes =
                    match extn with
                    | ".BIN"                    -> File.ReadAllText f  |> TranslateFromBinary    Mode3
                    | ".RAW"                    -> File.ReadAllBytes f |> TranslateFromRaw       Mode3
                    | ".ACD"                    -> File.ReadAllText f  |> TranslateFromText TACD Mode3
                    | ".900" | ".DAT" | ".TXT"  -> File.ReadAllText f  |> TranslateFromText T900 Mode3
                    | ".903"                    -> File.ReadAllText f  |> TranslateFromText T903 Mode3
                    | ".920"                    -> File.ReadAllText f  |> TranslateFromText T920 Mode3
                    | _                         -> BadFile () 
                 let prefix = f.[..(f.Length-5)]
                 let extn = 
                    match telecode with
                    TACD -> ".ACD" | T900 -> ".900" | T903 -> ".903" | T920 -> ".920" | TTXT -> ".TXT"
                 use out = new StreamWriter (prefix+extn)
                 for b in bytes do out.Write (UTFOf telecode b)
                 out.Close ()

        // compare files
        let Compare (master: string) (copy: string)  =
            let BadFile f = raise (Syntax (f + " file extension must be .ACD, .BIN, .RLB, .RAW, .DAT, .TXT, .900, .903 or .920"))
            if   master.Length < 5
            then BadFile master
            elif copy.Length < 5
            then BadFile copy
            else let mextn = master.Substring(master.Length-4, 4)
                 let mbytes =
                    match mextn with
                    | ".BIN" | ".RLB"           -> File.ReadAllText master  |> TranslateFromBinary    Mode3
                    | ".RAW"                    -> File.ReadAllBytes master |> TranslateFromRaw       Mode3
                    | ".ACD"                    -> File.ReadAllText master  |> TranslateFromText TACD Mode3
                    | ".900" | ".DAT" | ".TXT"  -> File.ReadAllText master  |> TranslateFromText T900 Mode3
                    | ".903"                    -> File.ReadAllText master  |> TranslateFromText T903 Mode3
                    | ".920"                    -> File.ReadAllText master  |> TranslateFromText T920 Mode3
                    | _                         -> BadFile master
                 let cextn = copy.Substring(copy.Length-4, 4)
                 let cbytes =
                    match cextn with
                    | ".BIN" | ".RLB"           -> File.ReadAllText copy  |> TranslateFromBinary    Mode3
                    | ".RAW"                    -> File.ReadAllBytes copy |> TranslateFromRaw       Mode3
                    | ".ACD"                    -> File.ReadAllText copy  |> TranslateFromText TACD Mode3
                    | ".900" | ".DAT" | ".TXT"  -> File.ReadAllText copy  |> TranslateFromText T900 Mode3
                    | ".903"                    -> File.ReadAllText copy  |> TranslateFromText T903 Mode3
                    | ".920"                    -> File.ReadAllText copy  |> TranslateFromText T920 Mode3
                    | _                         -> BadFile copy
                 let sm, fm = Trim mbytes
                 let lm = fm-sm+1
                 let sc, fc = Trim cbytes
                 let lc = fc-sc+1
                 if   lm < lc
                 then printfn "Master file (%s) is smaller than copy (%s): %d %d" master copy lm lc
                 else let rec Scan midx cidx errors =
                        if   midx <= fm
                        then // still have bytes to scan
                             if   mbytes.[midx] = cbytes.[cidx]
                             then // match
                                  Scan (midx+1) (cidx+1) errors
                             elif (midx+1) <= fm
                             then // more bytes left to scan
                                  if   mbytes.[midx+1] = cbytes.[cidx]
                                  then // dropped character
                                       printfn "%6d %4d (Missing byte)" (midx-sm) mbytes.[midx]
                                       Scan (midx+2) (cidx+1) (errors+1)
                                  elif mbytes.[midx+1] = cbytes.[cidx+1]
                                  then // mispunch
                                       printfn "%6d %4d (Mispunch)" (midx-sm) (256+(int mbytes.[midx]))
                                       Scan (midx+1) (cidx+1) (errors+1)
                                  else // other error
                                       printfn "Compare abandoned - files diverge at byte %d" (midx+1)
                             else // at last byte
                                  printfn "%6d %+3d (Mispunch)" (midx-sm) (256+(int mbytes.[midx]))
                                  Scan (midx+1) (cidx+1) (errors+1)
                        elif cidx <= fc
                        then  printfn "Problem: %d unused bytes in copy file" (fc-cidx+1)
                        elif errors > 0 
                        then printfn "%6d %6d (Complete)" -1 (lc-1)
                        else printfn "No mismatches found in %d bytes" (fm-sm+1)
                      Scan sm sc  0                                    
                        
        // verify image
        let VerifyImage fileName =
            let fi = fileName+".IMG"
            let f = if File.Exists fileName then fileName elif File.Exists fi then fi else fileName
            let bytes = File.ReadAllBytes f
            if bytes.Length % 4 <> 0 then raise (Syntax "Wrong number of bytes in file")
            VerifyImage bytes        


