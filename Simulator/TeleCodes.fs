#light

// Telecodes: Elliott 900 Series Telecodes, Punched Card Code and SIR Internal Code
//
// This module provides functions to translate between F# character symbols (UTF-16) and the symbols
// used by  Elliott teleprinters and flexowriters (essentailly early variants of ASCII).
// The Elliott 900 series had three 8 bit telecodes:  
//     Elliott 920 telecode was derived from Elliott 503 telecode
//     Elliott 903 telecode which  aligns to early versions of ANSI ASCII. 
//     Elliott 900 telecode which aligns with later versions of ANSI ASCII.  
// In addition there was a variant of 900 Telecode used by the Airbourne COmputing Division (ACD)
//
// In the simulator we take text input and map UTF symbols to the corresponding 
// Elliott telecode values for each telecode.  To facilitate use of standard PC keyboards 
// we provide some alternative representations for the more exotic symbols.  
//
// The simulator also allows for input as raw bytes or as a series of integers in the range
// 0..255, one per character, called "binary" format.
//
// When reading raw or binary format, the simulator can set the paper tape readers 
// into one of three modes:
//
// Mode 1: read tracks 8,7,6,4,3,2,1 as a seven bit code (i.e., track 5 is ignored)
// Mode 2: read tracks 7,6,5,4,3,2,1 as a seven bit code (i.e., track 8 is ignored)
// Mode 3: read all 8 tracks as an eight bit code.
//
// Mode 1 is intended for use with 920 telecode and was the only mode for the 920A. 
// The paper tape stations required to connect a teleprinter (MC*66F, e.g. MCM66F) 
// only supported Mode 3, unless an in-line mode switch in the cable connecting
// the reader.  Computers with  MC*60 tape stations (e.g., MCB60 on 920A)
// had a mode switch to select between modes, but could not connect a teleprinter. 
// (This information is taken from "903/905/920 Useful Notes" by TJ Froggatt.)

module Sim900.Telecodes
        
    open System.Collections.Generic
    open System.Text
    open Sim900.Bits

    exception Code of string

    type Telecodes = 
        | T920  // 920 telecode encoded in UTF-8
        | T903  // 903 telecode encoded in UTF-8
        | T900  // 900 telecode encoded in UTF-8
        | TACD  // ACD internal code encoded in UTF-8
        | TTXT  // any telecode converted to ASCII

    type ReaderModes =
        | Mode1
        | Mode2
        | Mode3  
                    
    // printable representation of newline, return and tab
    let VisibleWhiteSpace (str: string) =
            (((str.Replace ("\\", "\\\\")).Replace ("\n", "\\n")).Replace ("\t", "\\t")).Replace ("\r", "\\r")

    let mutable nonPrinting = true  // if true show non-printing characters
    let mutable addRunout   = false // true if runout to be added to text files

    module private TelecodeHelper =

        // Escape sequences for UTF representations of telecodes
        let runoutIn = "<! R !>"
        let haltIn1 = "<! HALT !>"
        let haltIn2 = "<! HALT CODE !>"
        let haltIn3 = "<! H !>"
        let bellIn  = "<! BELL !>"
        let haltOut () = if nonPrinting then "<! Halt !>" else ""
        let bellOut () = if nonPrinting then "<! Bell !>" else ""
            
        // ELLIOTT TELECODES

        let TelecodeName code =
            match code with
            | T920 -> "Elliott 920 Telecode"
            | T903 -> "Elliott 903 Telecode"
            | T900 -> "Elliott 900 Telecode"
            | TACD -> "Elliott ACD Telecode"
            | TTXT -> "ASCII"

        
        // ASCII version of 903/900 telecode                                                                               
        let teleCodeTXT   = "¬¬¬¬¬¬¬¬¬\t"       + "\n¬¬\r¬¬¬¬¬¬" + "¬¬¬¬¬¬¬¬¬¬"    + "¬¬ !\"$#%&'" + 
                            "()*+,-./01"        + "23456789:;"   +  "<=>?@ABCDE"   + "FGHIJKLMNO"  + 
                            "PQRSTUVWXY"        + "Z[\\]^_`abc"  +  "defghijklm"   + "nopqrstuvw"  + 
                            "xyz{|}‾¬"  // note ‾ renders as ? on console

        // Mappings between Elliott telecode symbols and equivalent Unicode symbols.
        // Each teleCode9xx string shows the Unicode equivalent symbol for the corresponding
        // Elliott telecode symbol whose value, less parity, is given by its position in
        // the string (indexed from 0 through to 127). Where alternate characters are shown the 
        // first one is the output representation. ¬ denotes no character at that position in the code. 
        //
        // 920 TELECODE
        //         00   10   20   30    40    50    60    70   100    110   120   130   140   150   160 
        // 
        // 0      blank (    0     8     :     H     P     X    sp          [      ?      h     p     x                                    
        // 1            )    1     9     A     I     Q     Y                ]      a      i     q     y
        // 2      lf    ,    2     10    B     J     R     Z              @ º      b      j     r     z  
        // 3      (pt)  £    3     11    C     K     S                halt  <      c      k     s                             
        // 4      tab   :    4     =     D     L     T                      >      d      l     t      
        // 5      (bsp) &    5     +     E     M     U                    ^ ↑      e      m     u     
        // 6            *    6     -     F     N     V     |                ~      f      n     v     _
        // 7            /    7     .     G     O     W                      %      g      o     w    erase 
        // pt = paper throw, bsp = backspace. | and _ are non-escaping
        // Certain composite symbols built using | are recognized by some applications as follows:
        // |. = !, |= # , |S = $, |< = ‘, |> = ’, |2 = ½, |a = @, |6 = {, |9 = }.
        // |S, |< and |> are recognized by 920 SIR and Algol.  The others are due to T.J. Froggatt.
        //
        let teleCode920 = "¬¬\n¬\t¬¬¬()" + ",£:&*/0123" + "456789⑩⑪=+"  + "-.;ABCDEFG" + "HIJKLMNOPQ" +
                          "RSTUVWXYZ¬"   + "¬¬|¬ ¬¬¬¬¬" + "¬¬¬¬¬¬¬¬¬¬"  + "¬¬¬¬¬¬¬¬[]" + "º<>↑~%?abc" +
                          "defghijklm"   + "nopqrstuvw" + "xyz¬¬¬_¬" 
        // 903 TELECODE
        //         00   10   20   30    40    50    60    70   100    110   120   130   140   150   160 
        // 
        // 0      blank            sp    (     0     8   ` ’     H     P     X     @     h     p     x                                                 
        // 1            tab        !     )     1     9     A     I     Q     Y     a     i     q     y
        // 2            lf         "     *     2     :     B     J     R     Z     b     j     r     z   
        // 3                     # ½     +     3     ;     C     K     S     [     c     k     s                           
        // 4           halt        $     ,     4     <     D     L     T     £     d     l     t      
        // 5            cr         %     -     5     =     E     M     U     ]     e     m     u     
        // 6                       &     .     6     >     F     N     V   ^ ↑     f     n     v    
        // 7       bell          ' ‘     /     7  ?  º     G     O     W   _ ←     g     o     w    erase   
        //
        let teleCode903   = "¬¬¬¬¬¬¬¬¬\t"  + "\n¬¬\r¬¬¬¬¬¬" + "¬¬¬¬¬¬¬¬¬¬"  + "¬¬ !\"½$%&‘" +
                            "()*+,-./01"   + "23456789:;"   + "<=>º’ABCDE"  + "FGHIJKLMNO"  + 
                            "PQRSTUVWXY"   + "Z[£]↑←@abc"   + "defghijklm"  + "nopqrstuvw"  +
                            "xyz¬¬¬¬¬"
                                                                                          
        // 900 Series TELECODE
        //         00   10   20   30    40    50    60    70   100    110   120   130   140   150   160 
        // 
        // 0      blank            sp    (     0     8     @     H     P     X   ’ `     h     p     x                                                                        ‘                                           
        // 1            tab        !     )     1     9     A     I     Q     Y     a     i     q     y
        // 2            lf         "     *     2     :     B     J     R     Z     b     j     r     z   
        // 3                     # £     +     3     ;     C     K     S     [     c     k     s     {                        
        // 4            halt       $     ,     4     <     D     L     T     \     d     l     t     |
        // 5            cr         %     -     5     =     E     M     U     ]     e     m     u     }
        // 6                       &     .     6     >     F     N     V   ↑ ^     f     n     v     ‾
        // 7       bell          ‘ '     /     7     ?     G     O     W   ← _     g     o     w    erase    
        //                                                                                   
        let teleCode900   = "¬¬¬¬¬¬¬¬¬\t"       + "\n¬¬\r¬¬¬¬¬¬" + "¬¬¬¬¬¬¬¬¬¬"    + "¬¬ !\"£$%&'" + 
                            "()*+,-./01"        + "23456789:;"   +  "<=>?@ABCDE"   + "FGHIJKLMNO"  + 
                            "PQRSTUVWXY"        + "Z[\\]^_`abc"  +  "defghijklm"   + "nopqrstuvw"  + 
                            "xyz{|}‾¬"  // note ‾ renders as ? on console
        
        // ACD TELECODE
        //         00   10   20   30    40    50    60    70   100    110   120   130   140   150   160 
        // 
        // 0      blank            sp    (     0     8     @     H     P     X   ’ `     h     p     x                                                                        ‘                                           
        // 1            tab        !     )     1     9     A     I     Q     Y     a     i     q     y
        // 2            lf         "     *     2     :     B     J     R     Z     b     j     r     z   
        // 3                       £     +     3     ;     C     K     S     [     c     k     s                              
        // 4            halt       $     ,     4     <     D     L     T   # £     d     l     t      
        // 5                       %     -     5     =     E     M     U     ]     e     m     u      
        // 6                       &     .     6     >     F     N     V   ↑ ^     f     n     v      
        // 7       bell          ‘ '     /     7   º ?     G     O     W   ← _     g     o     w    erase    
        //                                                                                  
        let teleCodeACDi  = "¬¬¬¬¬¬¬¬¬\t"       + "\n¬¬\r¬¬¬¬¬¬" + "¬¬¬¬¬¬¬¬¬¬"    + "¬¬ !\"£$%&'" + // input
                            "()*+,-./01"        + "23456789:;"   +  "<=>?`ABCDE"   + "FGHIJKLMNO"  + 
                            "PQRSTUVWXY"        + "Z[¬]^_¬abc"   + "defghijklm"    + "nopqrstuvw"  + 
                            "xyz¬¬¬¬¬"
                            
        let teleCodeACDo  = "¬¬¬¬¬¬¬¬¬\t"       + "\n¬¬\r¬¬¬¬¬¬" + "¬¬¬¬¬¬¬¬¬¬"    + "¬¬ !\"£$%&'" + // output 
                            "()*+,-./01"        + "23456789:;"   +  "<=>?`ABCDE"   + "FGHIJKLMNO"  + 
                            "PQRSTUVWXY"        + "Z[£]↑←`abc"   + "defghijklm"    + "nopqrstuvw"  + 
                            "xyz¬¬¬¬¬"   
        
        // All Elliott telecodes use even parity.  For 920 telecode the parity is in track 5, for 900 and
        // 903, track 8.  
        let BitCount code =
           let count = [| 0; 1; 1; 2; 1; 2; 2; 3; 1; 2; 2; 3; 2; 3; 3; 4 |]
           let rec Shift residual =
               if   residual = 0
               then 0
               else count.[residual &&& 0xf] + Shift (residual >>> 4)
           Shift code
           
        let OddParity code = ((BitCount code) &&& bit1) = bit1  

        // Dictionaries to map symbols to internal codes
        let teleCode920Dict = new Dictionary<char, int> ()
        let teleCode903Dict = new Dictionary<char, int> ()
        let teleCode900Dict = new Dictionary<char, int> ()
        let teleCodeACDDict = new Dictionary<char, int> ()
        let telecodeTXTDict = new Dictionary<char, int> ()

        // Initialize telecode dictionaries
        // NB parity is track 5 for 920, track 8 for 903 and 900
        for i = 0 to 127 do
            let ch920 = teleCode920.[i]
            if   ch920 <> '¬' 
            then let top3 = (i &&& 0x70) <<< 1
                 let bot4 = (i &&& 0x0f)
                 let code = top3 + (if OddParity i then bit5 ||| bot4 else bot4)
                 teleCode920Dict.[ch920] <- code
            let ch903 = teleCode903.[i]
            if   ch903 <> '¬' 
            then teleCode903Dict.[ch903] <- (if OddParity i then bit8 ||| i else i)
            let ch900 = teleCode900.[i]
            if   ch900 <> '¬' 
            then teleCode900Dict.[ch900] <- (if OddParity i then bit8 ||| i else i)
            let chACD = teleCodeACDi.[i]
            if   chACD <> '¬' 
            then teleCodeACDDict.[chACD] <- (if OddParity i then bit8 ||| i else i)
        
        // add alternatives to dictionaries
        
        teleCode920Dict.['#']    <- teleCode920Dict.['£']   // 920: # for £
        teleCode920Dict.['❿']    <- teleCode920Dict.['º']   // 920: ❿ for º
        teleCode920Dict.['@']    <- teleCode920Dict.['º']   // 920: @ for º
        teleCode920Dict.['^']    <- teleCode920Dict.['↑']   // 920: ^ for ↑
        
        teleCode903Dict.['?']    <- teleCode903Dict.['º']   // 903: ? for º
        teleCode903Dict.['❿']    <- teleCode903Dict.['º']   // 903: ❿ for º
        teleCode903Dict.['\'']   <- teleCode903Dict.['‘']   // 903: ' for ‘
        teleCode903Dict.['`']    <- teleCode903Dict.['’']   // 903: ` for ’
        teleCode903Dict.['#']    <- teleCode903Dict.['£']   // 903: # for £
        teleCode903Dict.['^']    <- teleCode903Dict.['↑']   // 903: ^ for ↑
        teleCode903Dict.['_']    <- teleCode903Dict.['←']   // 903: _ for ←
        
        teleCode900Dict.['‘']    <- teleCode900Dict.['\'']  // 900: ‘ for '
        teleCode900Dict.['’']    <- teleCode900Dict.['`']   // 900: ’ for `
        teleCode900Dict.['#']    <- teleCode900Dict.['£']   // 900: # for £
        teleCode900Dict.['½']    <- teleCode900Dict.['£']   // 900: ½ for £  
        teleCode900Dict.['↑']    <- teleCode900Dict.['^']   // 900: ↑ for ^
        teleCode900Dict.['←']    <- teleCode900Dict.['_']   // 900: ← for _
        teleCode900Dict.['~']    <- teleCode900Dict.['‾']   // 900: ~ for ‾
        
        teleCodeACDDict.['‘']    <- teleCodeACDDict.['\'']  // ACD: ‘ for '
        teleCodeACDDict.['’']    <- teleCodeACDDict.['`']   // ACD: ’ for `
        teleCodeACDDict.['#']    <- teleCodeACDDict.['£']   // ACD: £ for # for £
        teleCodeACDDict.['½']    <- teleCodeACDDict.['£']   // ACD: ½ for £
        teleCodeACDDict.['º']    <- teleCodeACDDict.['?']   // ACD: º for ?
        teleCodeACDDict.['❿']    <- teleCodeACDDict.['?']   // ACD: ❿ for ?  
        teleCodeACDDict.['↑']    <- teleCodeACDDict.['^']   // ACD: ^ for ↑
        teleCodeACDDict.['←']    <- teleCodeACDDict.['_']   // ACD: _ for ←
        
        let TelecodeDict code =
            match code with
             | T920 -> teleCode920Dict
             | T903 -> teleCode903Dict
             | T900 -> teleCode900Dict
             | TACD -> teleCodeACDDict
             | TTXT -> telecodeTXTDict

        let TelecodeChars code =
            match code with
             | T920 -> teleCode920
             | T903 -> teleCode903
             | T900 -> teleCode900
             | TACD -> teleCodeACDo
             | TTXT -> teleCodeTXT

    open TelecodeHelper  
    
    let Parity (code: byte) = byte ((BitCount (int code)) &&& 1) 

    let TelecodeOf telecode ch = // map UTF character to equivalent in one of Elliott telecodes
        let found, code = (TelecodeDict telecode).TryGetValue (ch)
        if   found
        then byte code
        else raise (Code (ch.ToString ()))
    
    let FromMode1 code = ((code >>> 1) &&& 0x70uy)+(code &&& 0xfuy)
    let FromMode2 code = code &&& 0x7fuy

    let ToMode1   code = ((code <<< 1) &&& 0xe0uy)+(code &&& 0xfuy)

    let cr900 = 141uy
    let lf900 = 010uy
    let nl920 = 002uy
        
    let UTFOf teleCode (code: byte) = // map Elliott telecode to UTF representation
        let BadSymbol () = if nonPrinting then sprintf "<! %03d !>" code else  "" // illegal char
        match teleCode with
        | T920 ->   match FromMode1 code with
                    | 000uy          // blank
                    | 127uy -> ""    // erase 
                    | 076uy -> haltOut ()
                    | 002uy -> "\n"
                    | i     -> match (TelecodeChars T920).[int i] with
                               | '¬'  -> BadSymbol ()
                               | ch   -> ch.ToString () 
        | T900
        | T903
        | TACD
        | TTXT  ->  match FromMode2 code with
                    | 000uy        // blank
                    | 013uy        // return
                    | 127uy  -> "" // erase 
                    | 007uy  -> bellOut ()
                    | 010uy  -> "\n"
                    | 020uy  -> haltOut ()
                    | i      -> match (TelecodeChars teleCode).[int i] with                     
                                | '¬'  -> BadSymbol ()
                                | ch   -> ch.ToString ()

    let LegibleOf (code: byte) =
        let s = new StringBuilder ()
        for bit in [|128; 64; 32; 16; 8; 4; 2; 1|] do 
            s.Append (if (int(code)&&&bit) = 0   then '.' else 'O') |> ignore
            if bit = 8 then s.Append 'o' |> ignore
        s.ToString ()
    
    module private SIRHelper =
    
        // ELLIOTT SIR INTERNAL CODE
        // This is the 6 bit internal code used by Elliott Algol rendered using 
        // Elliott 900 telecode symbols. 
        
        //      00     10     20     30     40     50     60     70
        // 
        // 0   space    (      0      8      @      H      P      X               
        // 1    nl      )      1      9      A      I      Q      Y      
        // 2     "      *      2      :      B      J      R      Z
        // 3    £#      +      3      ;      C      K      S      [
        // 4     $      ,      4      <      D      L      T      \ 
        // 5     %      -      5      =      E      M      U      ]
        // 6     &      .      6      >      F      N      V      ^ 
        // 7     '      /      7      ?      G      O      W      _                
            
        let sirCodes = // SIR internal code to equivalent UTF symbols (900 telecode)
            " \n\"#$%&'()*+,-./0123456789:;<=>?@ABCDEFGHIJKLMNOPQRSTUVWXYZ[\\]^_"                        

        let sirCodeDict = new Dictionary<char, int> ()

        // Initialize SIR code dictionaries
        for i = 0 to sirCodes.Length - 1 do
            sirCodeDict.[sirCodes.[i]] <- i

    open SIRHelper

    let SIRSymbolOf (code) = // Elliott internal 6 bit character code to char       
        sirCodes.[code] 
            
    let SIRCodeOf ch =
        let found, code = sirCodeDict.TryGetValue (ch)
        if   found
        then (byte code)
        else failwith ("Character not in SIR internal code '" + ch.ToString () + "'")

    // TRANSLATE TEXT STRINGS TO TELECODE SYMBOLS
    // Assumes text string only uses characters available in the selected telecode
    // Escape sequences <! R !>, <! Bell !>, <! Halt !> allowed
    // Also <! nnn !>

    // 900 and 903 telecode mapping
    let TranslateFromText telecode mode (text: string)  =
        let legibleBegin = "<! Legible Header "
        let legibleEnd1  = " !>\n"  // for unix style newline
        let legibleEnd2  = "!>\r\n" // for dos style newline
        let escBegin     = "<! "
        let escEnd       = " !>"
        let CharError inp =
                let chCode = (int text.[inp]).ToString ()
                raise (Code (VisibleWhiteSpace ("Invalid character <" + (text.[inp].ToString()) + "> ("
                                        + chCode + ") in ... " 
                                        + text.[(max 0 (inp-15))..inp-1]
                                        + "<<<" + (text.[inp].ToString()) + ">>>" 
                                        + text.[inp+1..(min (inp+10) (text.Length-1))])))
        let EscapeError  inp = 
                raise (Code (VisibleWhiteSpace ("Invalid escape sequence in ... "
                        + text.[(max 0 (inp-5))..(min (inp+15) (text.Length-1))])))
        let Mode m code =
            match m with 
            | Mode1 -> FromMode1 code 
            | Mode2 -> FromMode2 code
            | Mode3 -> code

        if   telecode <> T920
        then // 900 or 903 telecodes
             let chars: byte[] = Array.zeroCreate (text.Length*2)
             let rec copy (inp, outp, lastCh) =
                 if   inp >= text.Length
                 then chars.[..(outp-1+(if addRunout then 30 else 0))]
                 elif text.[inp] ='\n' // turn newline into newline, carriage return sequence
                 then if lastCh <> lf900 
                      then chars.[outp] <- cr900
                           chars.[outp+1] <- lf900
                           copy (inp+1, outp+2, lf900)
                      else chars.[outp] <- lf900
                           copy(inp+1, outp+1, lf900)
                 elif text.[inp] = '<'
                 then let a, b = escape (inp, outp)
                      copy (a, b, 0uy)
                 else chars.[outp] <- 
                          try Mode mode (TelecodeOf telecode text.[inp]) with
                          | e ->    CharError inp (int text.[inp])
                      copy (inp+1, outp+1, 0uy)
             and escape (inp, outp) =
                 let t  = text.[inp..]
                 let tu = t.[..(min (haltIn2.Length-1) (t.Length-1))].ToUpper ()
                 if   tu.StartsWith runoutIn
                 then chars.[outp] <- 0uy
                      (inp+runoutIn.Length, outp+1)
                 elif  tu.StartsWith bellIn
                 then chars.[outp] <- Mode mode (135uy)  // ASCII bell
                      (inp+bellIn.Length, outp+1)  
                 elif tu.StartsWith haltIn1 
                 then chars.[outp] <- Mode mode (020uy)  // ASCII halt 
                      (inp+haltIn1.Length, outp+1)
                 elif tu.StartsWith haltIn2 
                 then chars.[outp] <- Mode mode (020uy)  // ASCII halt
                      (inp+haltIn2.Length, outp+1) 
                 elif tu.StartsWith haltIn3 
                 then chars.[outp] <- Mode mode (020uy)  // ASCII halt
                      (inp+haltIn3.Length, outp+1) 
                 elif t.StartsWith legibleBegin          // n.b. t not tu
                 then let last = t.IndexOf legibleEnd1   // Legible header
                      if   last <> -1
                      then (inp+last+legibleEnd1.Length, outp)
                      else let last = t.IndexOf legibleEnd2   // Legible header
                           if last <> -1
                           then (inp+last+legibleEnd2.Length, outp)
                           else EscapeError inp
                              
                 elif t.StartsWith escBegin
                 then  // assume e.g., <! 255 !>
                      let last  = t.IndexOf escEnd
                      let code = 
                        try System.Byte.Parse (t.Substring (escBegin.Length, last-escBegin.Length)) with
                        _ -> EscapeError inp
                      chars.[outp] <- code
                      (inp+last+escEnd.Length, outp+1)
                 else // not an escape
                      chars.[outp] <- TelecodeOf telecode '<'
                      (inp+1, outp+1)
                     
             copy (0, (if addRunout then 30 else 0), 0uy)

        else // 920 telecode mapping: n.b. only dollar, open quote and close quote are "Elliott standard" mappings, others are
             // due to TJ Froggatt
             let chars: byte[] = Array.zeroCreate (text.Length*2+60) // fudge factor for expansion of escapes
             let rec copy (inp, outp) =
                 if   inp >= text.Length
                 then chars.[..(outp-1+(if addRunout then 30 else 0))]
                 else match text.[inp] with
                      | '<'  -> copy (escape (inp, outp))      
                      | '!'  -> copy (vertbar (inp, outp) '.')
                      //| '#'  -> copy (vertbar (inp, outp) '=')
                      | '$'  -> copy (vertbar (inp, outp) 'S')
                      | '\'' 
                      | '‘'  -> copy (vertbar (inp, outp) '<')
                      | '`' 
                      | '’'  -> copy (vertbar (inp, outp) '>')
                      | '½'  -> copy (vertbar (inp, outp) '2')
                      | '@'  -> copy (vertbar (inp, outp) 'a')
                      | '{'  -> copy (vertbar (inp, outp) '6')
                      | '}'  -> copy (vertbar (inp, outp) '9')
                      | '\r' -> copy (inp+1, outp)  // return is ignored
                      | _    -> chars.[outp] <- 
                                    try Mode mode (TelecodeOf T920 text.[inp]) with
                                    | e -> CharError inp
                                copy (inp+1, outp+1)
             and escape (inp, outp) =
                 let t  = text.[inp..]
                 let tu = t.[..(min (haltIn2.Length-1) (t.Length-1))].ToUpper ()
                 if   tu.StartsWith runoutIn
                 then chars.[outp] <- 0uy
                      (inp+runoutIn.Length, outp+1)
                 elif tu.StartsWith haltIn1 || tu.StartsWith haltIn2 || tu.StartsWith haltIn3
                 then chars.[outp] <- Mode mode (156uy); (inp+haltIn2.Length, outp+1) // 920 stop code
                 elif t.StartsWith legibleBegin          // n.b. t not tu
                 then let last = t.IndexOf legibleEnd1   // Legible header unix end of line
                      if    last <> -1
                      then (inp+last+legibleEnd1.Length, outp)    
                      else let last = t.IndexOf legibleEnd2  // legible header dos end of line
                           if last <> -1
                           then (inp+last+legibleEnd2.Length, outp) 
                           else EscapeError inp    
                 elif t.StartsWith escBegin
                 then  // assume e.g., <! 255 !>
                      let last  = t.IndexOf escEnd
                      let code = 
                        try System.Byte.Parse (t.Substring(escBegin.Length,last-1)) with
                        _ -> EscapeError inp
                      chars.[outp] <- code
                      (inp+last+escEnd.Length, outp+1)
                 else // not an escape
                      chars.[outp] <- Mode mode (TelecodeOf telecode '<')
                      (inp+1, outp+1)

             and vertbar (inp, outp) ch =
                 chars.[outp]   <- Mode mode (TelecodeOf T920 '|')
                 chars.[outp+1] <- Mode mode (TelecodeOf T920 ch)
                 (inp+1, outp+2)

             copy (0, if addRunout then 30 else 0)

    let TranslateFromBinary mode (text: string) = // no padding for binary
        let chars: byte[] = Array.zeroCreate (text.Length/2) 
        let rec copy (inp, outp) =
            if   inp >= text.Length
            then chars.[..outp-1]
            else match text.[inp] with
                    | ' '
                    | '\t'
                    | '\r'
                    | '\n'     -> copy (inp+1, outp) // skip white space
                    | ch when '0' <= ch && ch <= '9'
                               -> copy (extract (inp, outp))  // number found
                    | '('      -> copy (comment (inp, outp))
                    | ch       -> raise (Code (sprintf "Error decoding binary format - '%c' unexpected" ch))
            
        and extract (inp, outp) =  // read next character as a natural number
            let first = inp
            let rec skip inp =
                if   inp >= text.Length
                then inp
                else let ch = text.[inp]
                     if   '0' <= ch && ch <= '9' 
                     then skip (inp+1)
                     else inp
            let next = skip (inp+1) // skip over digits
            let code = byte text.[first..(next-1)]
            chars.[outp] <- 
                match mode with
                | Mode1 -> FromMode1 code
                | Mode2 -> FromMode2 code
                | Mode3 -> code
            (next, outp+1)

        and comment (inp, outp) = // skip over comment ( .... ) 
            let rec skip inp =   
                if inp >= text.Length
                then raise (Code "Missing ')' in binary format file")
                elif text.[inp] <> ')' 
                then  skip (inp+1)
                else (inp+1, outp)
            skip (inp+1) // search for end of comment

        copy (0, 0)

    let TranslateFromRaw mode (bytes: byte[]) =  // no padding for raw tapes
        let select code =
            match mode with
            | Mode1 -> FromMode1 code
            | Mode2 -> FromMode2 code
            | Mode3 -> code
        bytes |> Array.map select

    let TidyUpTelecodes () =
        nonPrinting <- true
        addRunout   <- false


    module Cards =
        // PUNCHED CARDS
        // Elliotts did not define a punched card code, instead the programmer was left to
        // define their own mapping from card column images to SIR Internal code.
        //
        // In the simulator we allow "text" files to be attached to the card reader and the
        // following function  maps telecode characters to IBM 029 "FORTRAN" card punch codes.
        // Note that the Elliott reader inputs columns inverted (i.e., the ms bit of the code 
        // corresponds to the bottom row of the card column).  The card code &7777 is used
        // to denote telecode for which there is no equivalent card code.
        let cardCodes = [|    
                0o7777;0o7777;0o7777;0o7777;0o7777;0o7777;0o7777;0o7777; //
                0o7777;0o7777;0o7777;0o7777;0o7777;0o7777;0o7777;0o7777; //
                0o7777;0o7777;0o7777;0o7777;0o7777;0o7777;0o7777;0o7777; //
                0o7777;0o7777;0o7777;0o7777;0o7777;0o7777;0o7777;0o7777; //
                0o0000;0o2022;0o3000;0o2040;0o2042;0o2104;0o0001;0o2200; //  !"#$%&'
                0o2201;0o2202;0o2102;0o2401;0o2044;0o0002;0o2041;0o0014; // ()*+,-./
                0o0004;0o0010;0o0020;0o0040;0o0100;0o0200;0o0400;0o1000; // 01234567
                0o2000;0o4000;0o2020;0o2402;0o2101;0o2400;0o2404;0o3004; // 89:;<=>?
                0o2100;0o0011;0o0021;0o0041;0o0101;0o0201;0o0401;0o1001; // @ABCDEFG
                0o2001;0o4001;0o0012;0o0022;0o0042;0o0102;0o0202;0o0402; // HIJKLMNO
                0o1002;0o2002;0o4002;0o0024;0o0044;0o0104;0o0204;0o0404; // PQRSTUVW
                0o1004;0o2004;0o4004;0o2021;0o3002;0o2024;0o3001;0o2204; // XYZ[\]^_
                0o7777;0o0011;0o0021;0o0041;0o0101;0o0201;0o0401;0o1001; //  abcdefg
                0o2001;0o4001;0o0012;0o0022;0o0042;0o0102;0o0202;0o0402; // hijklmno
                0o1002;0o2002;0o4002;0o0024;0o0044;0o0104;0o0204;0o0404; // pqrstuvw
                0o1004;0o2004;0o4004;0o7777;0o7777;0o7777;0o7777;0o7777|]// xyz       

    open Cards
    
    let CardCode ch =
        if   OddParity ch
        then raise (Code (sprintf "parity error (%d) in card input" ch))
        let cardCh = cardCodes.[ch &&& 127]
        if   cardCh = 0o7777
        then raise (Code (sprintf "invalid character '%c'(%d) in card input" (char ch) ch))
        else cardCh

    