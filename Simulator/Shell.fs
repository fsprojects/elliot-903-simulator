#light

module Sim900.Shell

open System.Text
open System.IO
open System.Windows.Forms

open Sim900.Version
open Sim900.Bits
open Sim900.Telecodes
open Sim900.Models
open Sim900.Devices
open Sim900.Memory
open Sim900.Machine
open Sim900.Formatting
open Sim900.Machine
open Sim900.Parameters
open Sim900.Legible
open Sim900.RLB
open Sim900.FileHandling
open Sim900.Loaders
open Sim900.Commands
open Sim900.Help

    module ShellHelper =

        // COMMAND INPUT & DECODING
        exception Finished // signals end of command input

        //lexical scanner
        let Lexer interactive =
            YieldToDevices ()
            Prompt ()
            let line = System.Console.In.ReadLine ()
            if line = null then raise Finished
            if not interactive then printfn "%s" line
            let words = line.Split([|' '; '\t'|], 
                           System.StringSplitOptions.RemoveEmptyEntries) 
                                |> Array.map (fun word -> word.ToUpper ()) 
            words        

        // Decoder
        let rec Decoder interactive =
            let words = Lexer interactive
            let BadExtension () = raise (Syntax "Inappropriate file extension")
            match (on, words) with 

            | (true,  [|"ALG"; "OFF"|]) 
            | (true,  [|"ALGOL"; "OFF"|])   -> AlgolOff ()

            | (true,  [|"ALG"; "ON"|]) 
            | (true,  [|"ALGOL"; "ON"|])    
                                            -> AlgolOn ()

            | (true,  [|"AT";     "CRD"; "FILE"; f|])
            | (true,  [|"ATTACH"; "CRD"; "FILE"; f|])
                                            -> if   f.EndsWith ".900" || f.EndsWith ".DAT" || f.EndsWith ".TXT"
                                               then OpenCardTxt f T900
                                               elif f.EndsWith ".903"
                                               then OpenCardTxt f T903
                                               elif f.EndsWith ".ACD"
                                               then OpenCardTxt f TACD
                                               else BadExtension ()

            | (true,  [|"AT";     "CRD"; "INLINE"|])
            | (true,  [|"ATTACH"; "CRD"; "INLINE"|])
                                            -> OpenCardTextString (DefaultTelecode ()) (ReadInlineText ())

            | (true,  [|"AT";     "LPR"|])
            | (true,  [|"ATTACH"; "LPR"|])
                                            -> OpenLinePrinter ()

            | (true,  [| "AT";     "MT"; n; file; |])
            | (true,  [| "ATTACH"; "MT"; n; file; |])
                                            -> MTMount (GetNatural n) file false

            | (true,  [| "AT";     "MT"; n; file; "WP"|])
            | (true,  [| "ATTACH"; "MT"; n; file; "WP"|])
                                            -> MTMount (GetNatural n) file true

            | (true,  [|"AT";     "PLT";|])
            | (true,  [|"ATTACH"; "PLT";|])  -> OpenPlotter ()
 
            | (true,  [|"AT";     "PTP"; "FILE"; f|]) 
            | (true,  [|"ATTACH"; "PTP"; "FILE"; f|])
                                            ->  if   f.EndsWith ".900" || f.EndsWith ".DAT" || f.EndsWith ".TXT"
                                                then OpenPunchTxt f T900
                                                elif f.EndsWith ".ACD"
                                                then OpenPunchTxt f TACD
                                                elif f.EndsWith ".903"
                                                then OpenPunchTxt f T903
                                                elif f.EndsWith ".920"
                                                then OpenPunchTxt f T920
                                                elif f.EndsWith ".BIN" || f.EndsWith ".RLB"
                                                then OpenPunchBin f 
                                                elif f.EndsWith ".RAW"
                                                then OpenPunchRaw f 
                                                else BadExtension ()

            | (true,  [|"AT";     "PTP"; "FILE"; f; "LEGIBLE"|]) 
            | (true,  [|"ATTACH"; "PTP"; "FILE"; f; "LEGIBLE"|])
                                            -> OpenPunchLegible f
                                            

            | (true,  [|"AT";     "PTP"; "FILE"; f; "900"|]) 
            | (true,  [|"ATTACH"; "PTP"; "FILE"; f; "900"|])
                                            -> OpenPunchTxt f T900

            | (true,  [|"AT";     "PTP"; "FILE"; f; "903"|]) 
            | (true,  [|"ATTACH"; "PTP"; "FILE"; f; "903"|])
                                            -> OpenPunchTxt f T900

            | (true,  [|"AT";     "PTP"; "FILE"; f; "920"|]) 
            | (true,  [|"ATTACH"; "PTP"; "FILE"; f; "920"|])
                                            -> OpenPunchTxt f T920

            | (true,  [|"AT";     "PTP"; "FILE"; f; "ACD"|]) 
            | (true,  [|"ATTACH"; "PTP"; "FILE"; f; "ACD"|])
                                            -> OpenPunchTxt f TACD   
   
            | (true,  [|"AT";     "PTR"; "INLINE"|]) 
            | (true,  [|"ATTACH"; "PTR"; "INLINE"|]) 
                                            -> OpenReaderTextString (DefaultTelecode ()) Mode3 (ReadInlineText ())                                                      
            | (true,  [|"AT";     "PTR"; "INLINE"; "903"|])          
            | (true,  [|"ATTACH"; "PTR"; "INLINE"; "903"|]) 
                                            ->  OpenReaderTextString T903 Mode3 (ReadInlineText ())   
                                            
            | (true,  [|"AT";     "PTR"; "INLINE"; "920"|]) 
            | (true,  [|"ATTACH"; "PTR"; "INLINE"; "920"|])   
            | (true,  [|"AT";     "PTR"; "INLINE"; "920"; "MODE1"|]) 
            | (true,  [|"ATTACH"; "PTR"; "INLINE"; "920"; "MODE1"|])
                                            -> OpenReaderTextString T920 Mode1 (ReadInlineText ())
                                            
            | (true,  [|"AT";     "PTR"; "INLINE"; "920"; "MODE3"|]) 
            | (true,  [|"ATTACH"; "PTR"; "INLINE"; "920"; "MODE3"|])   
                                            -> OpenReaderTextString T920 Mode3 (ReadInlineText ()) 

            | (true,  [|"AT";     "PTR"; "INLINE"; "900"|])  
            | (true,  [|"ATTACH"; "PTR"; "INLINE"; "900"|])              
                                            ->  OpenReaderTextString T900 Mode3 (ReadInlineText ()) 

            | (true,  [|"AT";     "PTR"; "INLINE"; "ACD"|])  
            | (true,  [|"ATTACH"; "PTR"; "INLINE"; "ACD"|]) 
                                            ->  OpenReaderTextString TACD Mode3 (ReadInlineText ()) 
                                            

            | (true,  [|"AT";     "PTR"; "INLINE"; "BIN"; "MODE1"|])
            | (true,  [|"ATTACH"; "PTR"; "INLINE"; "BIN"; "MODE1"|])
                                            ->  OpenReaderBinaryString Mode1 (ReadInlineText ()) 

            | (true,  [|"AT";     "PTR"; "INLINE"; "BIN"; "MODE2"|])
            | (true,  [|"ATTACH"; "PTR"; "INLINE"; "BIN"; "MODE2"|])
                                            ->  OpenReaderBinaryString Mode2 (ReadInlineText ()) 

            | (true,  [|"AT";     "PTR"; "INLINE"; "BIN"; "MODE3"|]) 
            | (true,  [|"AT";     "PTR"; "INLINE"; "BIN"; "MODE3"|])
            | (true,  [|"AT";     "PTR"; "INLINE"; "BIN"|]) 
            | (true,  [|"ATTACH"; "PTR"; "INLINE"; "BIN"|])
                                            ->  OpenReaderBinaryString Mode3 (ReadInlineText ()) 

            | (true,  [|"AT";     "PTR"; "FILE"; f; "920"|]) 
            | (true,  [|"ATTACH"; "PTR"; "FILE"; f; "920"|])
            | (true,  [|"AT";     "PTR"; "FILE"; f; "920"; "MODE1"|]) 
            | (true,  [|"ATTACH"; "PTR"; "FILE"; f; "920"; "MODE1"|]) 
                                            ->  OpenReaderText T920 Mode1 f 

            | (true,  [|"AT";     "PTR"; "FILE"; f; "920"; "MODE3"|]) 
            | (true,  [|"ATTACH"; "PTR"; "FILE"; f; "920"; "MODE3"|]) 
                                            ->  OpenReaderText T920 Mode3 f 

            | (true,  [|"AT";     "PTR"; "FILE"; f; "903"|]) 
            | (true,  [|"ATTACH"; "PTR"; "FILE"; f; "903"|]) 
                                            ->  OpenReaderText T903 Mode3 f
            | (true,  [|"AT";     "PTR"; "FILE"; f; "900"|]) 
            | (true,  [|"ATTACH"; "PTR"; "FILE"; f; "900"|])
                                            -> OpenReaderText T900 Mode3 f
            | (true,  [|"AT";     "PTR"; "FILE"; f; "ACD"|]) 
            | (true,  [|"ATTACH"; "PTR"; "FILE"; f; "ACD"|])
                                            -> OpenReaderText TACD Mode3 f

            | (true,  [|"AT";     "PTR"; "FILE"; f|]) 
            | (true,  [|"ATTACH"; "PTR"; "FILE"; f|])  
                                            ->  FileOpen f Mode3

            | (true,  [|"AT";     "PTR"; "FILE"; f; "MODE1"|]) 
            | (true,  [|"ATTACH"; "PTR"; "FILE"; f; "MODE1"|])
                                             ->  FileOpen f Mode1

            | (true,  [|"AT";     "PTR"; "FILE"; f; "MODE2"|]) 
            | (true,  [|"ATTACH"; "PTR"; "FILE"; f; "MODE2"|])
                                            ->  FileOpen f Mode2  

            | (true,  [|"AT";     "TTY"; "CONSOLE"|])   
            | (true,  [|"ATTACH"; "TTY"; "CONSOLE"|])
                                            -> OpenTTYConsole T900
     
            | (true,  [|"AT";     "TTY"; "INLINE"|])   
            | (true,  [|"ATTACH"; "TTY"; "INLINE"|])                                    
                                            ->  OpenTTYInTextString (ReadInlineText ()) (DefaultTelecode ()) Mode3
                                                                     
            | (true,  [|"AT";     "TTY"; "INLINE"; "ACD"|])   
            | (true,  [|"ATTACH"; "TTY"; "INLINE"; "ACD"|])                                    
                                            ->  OpenTTYInTextString (ReadInlineText ()) TACD Mode3
                                                                    
            | (true,  [|"AT";     "TTY"; "INLINE"; "900"|])   
            | (true,  [|"ATTACH"; "TTY"; "INLINE"; "900";|])                                    
                                            ->  OpenTTYInTextString (ReadInlineText ()) T900 Mode3
                                                                    
            | (true,  [|"AT";     "TTY"; "INLINE"; "903"|])   
            | (true,  [|"ATTACH"; "TTY"; "INLINE"; "903"|])                                    
                                            ->  OpenTTYInTextString (ReadInlineText ()) T903 Mode3  
                                                                    
            | (true,  [|"AT";     "TTY"; "INLINE"; "920"|])   
            | (true,  [|"ATTACH"; "TTY"; "INLINE"; "920"|]) 
            | (true,  [|"AT";     "TTY"; "INLINE"; "920"; "MODE3"|])   
            | (true,  [|"ATTACH"; "TTY"; "INLINE"; "920"; "MODE3"|])                                    
                                            ->  OpenTTYInTextString (ReadInlineText ()) T920 Mode3                                                                       

            | (true,  [|"AT";     "TTY"; "INLINE"; "920"; "MODE1"|])   
            | (true,  [|"ATTACH"; "TTY"; "INLINE"; "920"; "MODE1"|])                                    
                                            ->  OpenTTYInTextString (ReadInlineText ()) T920 Mode1  
                                                                 
            | (true,  [|"AT";     "TTY"; "INLINE"; "BIN"; "MODE1"|])
            | (true,  [|"ATTACH"; "TTY"; "INLINE"; "BIN"; "MODE1"|])
                                            ->  OpenTTYInBinaryString Mode1 (ReadInlineText ()) 

            | (true,  [|"AT";     "TTY"; "INLINE"; "BIN"; "MODE2"|])
            | (true,  [|"ATTACH"; "TTY"; "INLINE"; "BIN"; "MODE2"|])
                                            ->  OpenTTYInBinaryString Mode2 (ReadInlineText ()) 

            | (true,  [|"AT";     "TTY"; "INLINE"; "BIN"; "MODE3"|]) 
            | (true,  [|"AT";     "TTY"; "INLINE"; "BIN"; "MODE3"|])
            | (true,  [|"AT";     "TTY"; "INLINE"; "BIN"|]) 
            | (true,  [|"ATTACH"; "TTY"; "INLINE"; "BIN"|])
                                            ->  OpenTTYInBinaryString Mode3 (ReadInlineText ()) 

            | (true,  [|"AUTO"|])           ->  WordGeneratorPut 8177; Jump TracePut MonitorPut
            | (true,  [|"B"; "OFF"; n|]) 
            | (true,  [|"BREAK"; "OFF"; n|])
                                            ->  BreakpointOff (GetAddress n)

            | (true,  [|"B"; "OFF"|])
            | (true,  [|"BREAK"; "OFF"|])   ->  BreakpointOffAll ()

            | (true,  [|"B"; "ON"; n|]) 
            | (true,  [|"BREAK"; "ON"; n|]) ->  BreakpointOn (GetAddress n)

            | (_,     [|"CD"; d|])
            | (_,     [|"CHANGEDIR"; d|])   -> ChangeDir d

            | (true,  [|"CL"|]) | (true, [|"CLEAR"|])
                                            -> ClearStore ()

            | (true,  [|"CL"; n|]) | (true, [|"CLEAR"; n|])  
                                            -> ClearModule (GetAddress n)

            | (_,     [|"COMP";    m; c|])
            | (_,     [|"COMPARE"; m; c|])  -> Compare m c

            | (true,  [|"DE";     "CRD"|]) 
            | (true,  [|"DETACH"; "CRD"|])  -> CloseCardReader ()

            | (true,  [|"DE";     "LPR"|]) 
            | (true,  [|"DETACH"; "LPR"|])  -> CloseLinePrinter ()

            | (true,  [|"DE";     "MT"; n |])
            | (true,  [|"DETACH"; "MT"; n |])
                                            -> MTUnmount (GetNatural n)

            | (true,  [|"DE";     "PLT"|]) 
            | (true,  [|"DETACH"; "PLT"|])  -> ClosePlotter ()

            | (true,  [|"DE";     "PTP"|]) 
            | (true,  [|"DETACH"; "PTP"|])  -> ClosePunch ()

            | (true,  [|"DE";     "PTR"|]) 
            | (true,  [|"DETACH"; "PTR"|])  -> CloseReader ()

            | (true,  [|"DE";     "TTY"|]) 
            | (true,  [|"DETACH"; "TTY"|])  -> CloseTTY ()

            | (_,     [|"DEL";    file|])
            | (_,     [|"DELETE"; file|])   -> Delete file

            | (true,  [|"D";       first; last|]) 
            | (true,  [|"DISPLAY"; first; last|])    
                                            -> DisplayRange first last

            | (true,  [|"D";       addr|]) 
            | (true,  [|"DISPLAY"; addr|])  -> DisplayLocation addr 

            | (true,  [|"D"|]) 
            | (true,  [|"DISPLAY"|])        -> DisplayRegisters ()

            | (_,     [|"DIR"|])
            | (_,     [|"DIRECTORY"|])      -> ListDirectory ()

            | (true,  [|"DAS";       file|])
            | (true,  [|"DUMPASSIR"; file|]) 
                                            -> DumpAsSir file memorySize // no literals
                                            
            | (true,  [|"DAS";       file; literals|])
            | (true,  [|"DUMPASSIR"; file; literals|]) 
                                            -> DumpAsSir file (GetAddress literals)

            | (true,  [|"DU"; n; f|]) 
            | (true,  [|"DUMPIMAGE"; n; f|]) 
                                            -> DumpImage f (GetNatural n)

            | (true,  [|"E"; loc; value|]) 
            | (true,  [|"ENTER"; loc; value|])   
                                            -> Enter loc (GetConstant value)

            | (true,  [|"E"; loc; f; n|]) 
            | (true,  [|"ENTER"; loc; f; n|])
                                            -> Enter loc (GetInstruction f n)

            | (true,  [|"F"; value|])               
            | (true,  [|"FIND"; value|])    -> Find (GetConstant value)

            | (true,  [|"F"; f; n|])               
            | (true,  [|"FIND"; f; n|])     -> Find (GetInstruction f n)
             
            
            | (true,  [|"FAST"|])           -> Fast ()

            | (_,     [|"FIXRLB"; fromFile; toFile|])       
                                            -> FixRLB fromFile toFile Mode3

            | (_,     [|"FIXRLB"; fromFile; toFile; "MODE1"|])       
                                            -> FixRLB fromFile toFile Mode1

            | (_,     [|"H"|]) | (true, [|"HELP"|])
                                            -> Help ""
            | (_,     [|"H"; t|]) 
            | (_,     [|"HELP"; t|])
                                            -> Help t

            | (true,  [|"INT"; level|]) 
            | (true,  [|"INTERRUPT"; level|])
                                            -> ManualInterrupt (int (GetNatural level))

            | (true,  [| "J";    "II"|])
            | (true,  [| "JUMP"; "II"|])    -> JumpII TracePut MonitorPut

            | (true,  [| "J";    k|])
            | (true,  [| "JUMP"; k|])       -> WordGeneratorPut (GetConstant k); Jump TracePut MonitorPut
            
            | (true,  [|"J"|]) | (true, [|"JUMP"|])          
                                            -> Jump TracePut MonitorPut

            | (true,  [|"K"; n|]) 
            | (true,  [|"KEYS"; n|])        -> WordGeneratorPut (GetConstant n)

            | (true,  [|"K"; f; n|]) 
            | (true,  [|"KEYS"; f; n|])     -> WordGeneratorPut (GetInstruction f n)

            | (_,     [|"LD"|])
            | (_,     [|"LS"|])            
            | (_,     [|"LISTDIRECTORY"|])  -> ListDirectory ()

            | (true,  [|"LM"; m; f|])
            | (true,  [|"LOADMODULE"; m; f|])
                                            -> LoadModule (GetNatural m) f

            | (true,  [|"LO"; f|]) 
            | (true,  [|"LOADIMAGE"; f|])   -> LoadImage f

            | (_,     [|"LOG"; o|])         ->  if   o = "ON"
                                                then LoggingOn ()
                                                elif o = "OFF"
                                                then LoggingOff ()
                                                else LogToFile o
                                                     LoggingOn ()
                   
            | (_,     [|"NL";      "OFF"|])
            | (_,     [|"NEWLINE"; "OFF"|]) -> SetTTYNewline false                                                    
                                            
            | (_,     [|"NL";      "ON"|])
            | (_,     [|"NEWLINE"; "ON"|])  -> SetTTYNewline true
            
            | (_,     [|"NS";      "OFF"|])
            | (_,     [|"NONSTOP"; "OFF"|])  
                                            -> nonStop <- false
                                            
            | (_,     [|"NS";      "ON"|])
            | (_,     [|"NONSTOP"; "ON"|])  
                                            -> nonStop <- true

            | (_,     [|"NP";          "OFF"|])
            | (_,     [|"NONPRINTING"; "OFF"|])  
                                            -> nonPrinting <- false

            | (_,     [|"NP";         "ON"|])
            | (_,     [|"NONPRINTING";"ON"|])   
                                            -> nonPrinting <- true
            
            | (true,  [|"OBEY"|])           -> Obey ()  

            | (_,     [|"OFF"|])            -> turnOff ()
                         
            | (_,     [|"ON"; a; mz; ms; ps|])
                                            -> turnOn a mz (GetNatural ms) (GetNatural ps)
            | (_,     [|"ON"; a; mz; ms|])
                                            -> turnOn a mz (GetNatural ms) 0
            | (_,     [|"ON"; a; mz|])              
                                            -> turnOn a mz 0 0

            | (_,     [|"ON"; a|])          -> turnOn a "8K" 0 0
            | (_,     [|"ON"|])
                                            -> turnOn Generic900.name Generic900.memSize Generic900.memSpeed Generic900.ptrSpeed

            | (true,  [|"O";      x; y|])
            | (true,  [|"ORIGIN"; x; y|])   -> SetOrigin (GetNatural x) (GetNatural y)

            | (_,     [|"P"|])
            | (_,     [|"PAUSE"|])          -> Pause ()

            | (true,  [|"PERT"; first; last|])
                                            -> Pert ((GetNatural first), (GetNatural last))

            | (_,     [|"PR";    f|])
            | (_,     [|"PRINT"; f|])       
            | (_,     [|"PR";    f; "MODE3"|])
            | (_,     [|"PRINT"; f; "MODE3"|])       
                                            -> Print f Mode3   
                                               
            | (_,     [|"PR";    f; "MODE1"|])
            | (_,     [|"PRINT"; f; "MODE1"|])       
                                            -> Print f Mode3

            | (_,     [|"PRA";        f|])
            | (_,     [|"PRINTALGOL"; f|])       
            | (_,     [|"PRA";        f; "MODE3"|])
            | (_,     [|"PRINTALGOL"; f; "MODE3"|])       
                                            -> PrettyALGRLB f Mode3   
                                               
            | (_,     [|"PRA";        f; "MODE1"|])
            | (_,     [|"PRINTALGOL"; f; "MODE1"|])       
                                            -> PrettyALGRLB f Mode3

            | (_,     [|"REV"; f |])
            | (_,     [|"REVERSE"; f |])    -> Reverse f

            | (true,  [|"RW";     "CRD"|])
            | (true,  [|"REWIND"; "CRD"|])  -> RewindCard ()

            | (true,  [|"RW" |])
            | (true,  [|"REWIND" |])
            | (true,  [|"RW";     "PTR"|])
            | (true,  [|"REWIND"; "PTR"|])  -> RewindReader ()

            | (true,  [|"RESET"|])          -> Reset ()

            | (true,  [|"R"|])
            | (true,  [|"RESTART"|])        -> Restart TracePut MonitorPut -1

            | (true,  [|"R"; n|])
            | (true,  [|"RESTART"; n|])     -> let addr = GetAddress n
                                               Restart TracePut MonitorPut addr

            | (_,     [|"RLBTOSIR"; src; dest |])
                                            -> RLBtoSIR src dest Mode3

            | (_,     [|"RLBTOSIR"; src; dest; "MODE1" |])
                                            -> RLBtoSIR src dest Mode1

            | (_,     [|"RUNOUT"; "OFF"|])  -> addRunout <- false

            | (_,     [|"RUNOUT"; "ON"|])   -> addRunout <- true

            | (true,  [|"SCALE"; n|])       -> SetScale (GetNatural n)

            | (true,  [|"SCB"|])
            | (true,  [|"SCBDECODE"|])      -> SCBDecode ()

            | (true,  [|"SEL";    "IN"; "PTR"|])
            | (true,  [|"SELECT"; "IN"; "PTR"|])
                                            -> InputSelectReader ()

            | (true,  [|"SEL";    "IN"; "AUTO"|])
            | (true,  [|"SELECT"; "IN"; "AUTO"|])
                                            -> InputSelectAuto ()

            | (true,  [|"SEL";    "IN"; "TTY"|])
            | (true,  [|"SELECT"; "IN"; "TTY"|])
                                            -> InputSelectTeleprinter ()

            | (true,  [|"SEL";    "OUT"; "PTP"|])
            | (true,  [|"SELECT"; "OUT"; "PTP"|])
                                            -> OutputSelectPunch ()

            | (true,  [|"SEL";    "OUT"; "AUTO"|])
            | (true,  [|"SELECT"; "OUT"; "AUTO"|])
                                            -> OutputSelectAuto ()

            | (true,  [|"SEL";    "OUT"; "TTY"|])
            | (true,  [|"SELECT"; "OUT"; "TTY"|])
                                            -> OutputSelectTeleprinter ()

            | (true,  [|"SH"; "B";|]) 
            | (true,  [|"SHOW"; "BREAKPOINTS"|])   
                                            -> BreakpointsPut ()

            | (true,  [|"SH"; "C"|]) 
            | (true,  [|"SHOW"; "CONF"|])
            | (true,  [|"SHOW"; "CONFIGURATION"|])         
                                            -> ConfigPut ()

            | (true,  [|"SH"; "M";|]) 
            | (true,  [|"SHOW"; "MONITORS"|])     
                                            -> MonitorsPut ()

            | (true,  [|"SH"; "T";|]) 
            | (true,  [|"SHOW"; "TIME"|])
            | (true,  [|"SHOW"; "TIMES"|])         
                                            -> TimesPut (Times ())

            | (true,  [| "SH" |])
            | (true,  [| "SHOW" |])         -> ConfigPut ()
                                               TimesPut (Times())
                                               MonitorsPut ()
                                               BreakpointsPut ()

            | (true, [|"SKIP"|])            -> SkipReader ()

            | (true,  [|"SL"|])
            | (true,  [|"SLOW"|])           -> Slow ()

            | (true,  [|"S"; n|]) 
            | (true,  [|"STEP"; n|])        -> Steps (GetNatural n)

            | (true,  [|"S"|]) 
            | (true,  [|"STEP"|])           -> Steps 1; Restart TracePut MonitorPut -1

            | (true,  [|"STACK"|])          -> Stack ()

            | (true,  [|"ST";      n|]) 
            | (true,  [|"STOP";    n|])
            | (true,  [|"STOPPED"; n|])     -> if   SGet () <> (GetAddress n)
                                               then raise Finished

            | (true,  [|"SWAPXY"|])         -> SwapXY ()

            | (_,     [|"TC";       "ACD"|])
            | (_,     [|"TELECODE"; "ACD"|])
                                            -> SetDefaultTelecode T900 
            | (_,     [|"TC";       "900"|])
            | (_,     [|"TELECODE"; "900"|])
                                            -> SetDefaultTelecode T900 

            | (_,     [|"TC";       "903"|])
            | (_,     [|"TELECODE"; "903"|])
                                            -> SetDefaultTelecode T903 
            | (_,     [|"TC";       "920"|])
            | (_,     [|"TELECODE"; "920"|])
                                            -> SetDefaultTelecode T920
            | (_,     [|"T"|])
            | (_,     [|"TIDY"|])
            | (_,     [|"TIDYUP"|])         -> TidyUp ()
            
            | (_,     [|"TOBINARY"; f|])     
            | (_,     [|"TOBIN";    f|])    -> ToBinary f

            | (_,     [|"TORAW"; f|])       -> ToRaw f

            | (_,     [|"TOTELE";     f; "920"|])
            | (_,     [|"TOTELECODE"; f; "920"|])
                                            -> ToTelecode f T920

            | (_,     [|"TOTELE";     f; "903"|])
            | (_,     [|"TOTELECODE"; f; "903"|])
                                            -> ToTelecode f T903 

            | (_,     [|"TOTELE";     f; "900"|])
            | (_,     [|"TOTELECODE"; f; "900"|])
            | (_,     [|"TOTELE";     f|])
            | (_,     [|"TOTELECODE"; f|]) 
                                            -> ToTelecode f T900 

            | (_,     [|"TOTELE";     f; "ACD"|])
            | (_,     [|"TOTELECODE"; f; "ACD"|])
                                            -> ToTelecode f TACD 

            | (_,     [|"TOTELE";     f; "ASCII"|])
            | (_,     [|"TOTELECODE"; f; "ASCII"|])
                                            -> ToTelecode f TTXT

            | (true,  [|"TR"; "OFF"|]) 
            | (true,  [|"TRACE"; "OFF"|])   -> TraceOff 0

            | (true,  [|"TR"; "OFF"; level|]) 
            | (true,  [|"TRACE"; "OFF"; level|])    
                                            -> let l = GetNatural level
                                               if l <= 0 || l > 4 then BadParameter ()
                                               TraceOff l

            | (true,  [|"TR"; "ON"; level|]) 
            | (true,  [|"TRACE"; "ON"; level|])     
                                            -> let l = GetNatural level
                                               if l <= 0 || l > 4 then BadParameter ()
                                               TraceOn l

            | (true,  [|"TR"; "ON"|]) 
            | (true,  [|"TRACE"; "ON"|])    -> TraceOn 0  

            | (true,  [|"TRACEINTERRUPT"; level; "OFF"|]) 
            | (true,  [|"TINT";           level; "OFF"|])
                                            -> TraceInterruptOff (int (GetNatural level))

            | (true,  [|"TRACEBUFFER"|])
            | (true,  [|"TB"|])             -> TraceBuffer ()

            | (true,  [|"TRACEINTERRUPT"; level; "ON"|])
            | (true,  [|"TINT";           level; "ON"|])
                                            -> TraceInterruptOn (int (GetNatural level))            

            | (true,  [|"TRACEREGION"; "OFF"|])
            | (true,  [|"TR";          "OFF"|])
                                            -> TraceRegion -1 0

            | (true,  [|"TRACEREGION"; start; finish|])
            | (true,  [|"TR";          start; finish|])
                                            -> TraceRegion (GetAddress start) (GetAddress finish)

           (* | (true, [|"TRACK"; f; start|]) -> Track f (GetAddress start) *)

            | (true, [|"WATCH"; "OFF"|])
            | (true, [|"W";     "OFF"|])    -> WatchOff ()


            | (true, [|"WATCH"; "ON"; n|])
            | (true, [|"W";     "ON"; n|])  -> WatchOn (GetAddress n)

            | (true,  [|"VERIFYIMAGE"; f|])  
            | (true,  [|"VI";          f|]) -> VerifyImage f             

            | (_,     [| "Q" |])
            | (_,     [| "QUIT" |])         -> raise Quit

            | (_,     [||])                 -> () // empty line

            | _                             ->  match (on, words.[0]) with
                                                | (true,  "B")
                                                | (true,  "BREAK")   -> BreakCmd words.[1..]
                                                | (_,     "C")
                                                | (_,     "COMMENT") -> ()
                                                | (_,     "DO") when words.Length >= 2
                                                                     -> ReadCommandsFromFile words.[1] words.[2..]
                                                | (_,     "LEG")  
                                                | (_,     "LEGIBLE") -> Legible words.[1..]
                                                | (true,  "M")
                                                | (true,  "MONITOR") -> MonitorCmd words.[1..]
                                                | (true,  "QCHECK")
                                                | (true,  "QC" )     -> QCheck words.[1..]
                                                | _                  -> BadCommand ()               
                               
        // READ COMMANDS 
        and ReadCommands interactive =
            let rec Decode () = 
                Decoder interactive 
                Decode ()
            YieldToDevices ()
            try Decode () with
            | Code c       ->   MessagePut (sprintf "%s" c);                         if not nonStop then raise Finished
            | Break        ->   MessagePut "Breakpoint reached";   MiniDump ();      if not nonStop then raise Finished
            | Device  s    ->   MessagePut s;                                        if not nonStop then raise Finished
            | Finished     ->   raise Finished // end of current command level
            | LoopStop     ->   MessagePut (sprintf "Loop stop at location %s" (AddressStr(SGet ())))
            | Machine s    ->   MessagePut s;                                        if not nonStop then raise Finished
            | NoLog        ->   MessagePut "No log file";                            if not nonStop then raise Finished
            | StopAddr     ->   MessagePut "Stop address reached"; MiniDump ();      if not nonStop then raise Finished
            | StopLimit    ->   MessagePut "Step limit reached";   MiniDump ();      if not nonStop then raise Finished
            | Syntax s     ->   MessagePut s;                                        if not nonStop then raise Finished
            | Watch        ->   MessagePut "Watch location accessed"; MiniDump ();   if not nonStop then raise Finished
            | Quit         ->   raise Quit 
            | err          ->   MessagePut err.Message;                              if not nonStop then raise Finished
            ReadCommands interactive

        // read commands from file
        and ReadCommandsFromFile file (args: string[]) =
            // read commands from file
            let stdin = System.Console.In // remember current console
            try
                let fe = file+".DAT"
                let f = if File.Exists file then file elif File.Exists fe then fe else file
                let mutable commands = File.ReadAllText f 
                // substitute parameters
                for i in 0..(args.Length-1) do
                    let pi = "%"+(i+1).ToString ()
                    commands <- commands.Replace (pi, args.[i]) 
                let reader = new StringReader (commands)
                System.Console.SetIn reader
                try ReadCommands false with | Finished -> ()
            finally
                System.Console.SetIn stdin

        and ReadCommandsFromConsole () = 
            FlushTTY ()
            try ReadCommands true with 
            | Finished -> ReadCommandsFromConsole ()

    open ShellHelper

    let CommandLineInterpreter () = 
        try 
            try ReadCommandsFromConsole () with | Quit -> ()
        finally     
            CloseLog ()
            Application.Exit ()

