#light

// Elliott 900 CENTRAL PROCESSING UNIT

module Sim900.Machine
                
    open System
    open System.Text
    open System.Diagnostics
    open System.IO
    open System.Collections.Generic

    open Sim900.Bits
    open Sim900.Telecodes
    open Sim900.Models    
    open Sim900.Devices
    open Sim900.Memory
    open Sim900.Formatting
                 
    exception Watch       
    exception LoopStop
    exception StopAddr
    exception StopLimit
    exception Break
    exception Trace 

    // MONITOR POINTS
    // Monitor points are a debugging facility based on the Elliott MONITOR/QCHECK utility.
    // If execution reaches a monitor point a dump is made of the machine registers and
    // a specified series of memory regions.  The start and end of each region is defined
    // by either address or a calculated address formed by chaining through a specified
    // series of indirections        
    type monitor = {
        addr: int;
        regions: list<region>}
    and region = {
        start:  list<int>;
        finish: list<int>}

    // INSTRUCTION TRACE RECORD
    // A buffer of the addresses of the most recently executed instructions and the acumulator value they
    // produce is available
    type TraceRec = {
        scr: int; // address of instruction
        acc: int  // accumulator value
        }

    // MACHINE INTERNAL STATE

    // Initial values are for 64K 920b

    module private MachineStateHelper =

        // STORE

        // For machines before 920C memory is max 8 * 8K modules
        // For 920C max is either 8 * 8K modules or 8 * 16K modules
        // For simplicity work in units of 8K
        let memory: int[]     = Array.zeroCreate (8*16*1024)
  
        // Initial instructions
        //
        // 903: On 903 processors fitted with more that 8192 words of core store [these locations]
        // may be used as the normal core store when the initial instructions are 'disabled'.  The
        // instructions are disabled whenever a 15 7168 is obeyed.  They are enabled when the jump 
        // or reset button is pressed.  The contents of 8180 to 8191 will be preserved unless program  
        // is obeyed from those locations.  The effect of reading these locations on a basic machine
        // or while the instructions are enabled should be regarded as undefined.
        //
        // 905: These instructions are brought into use when a program is entered (JUMP) and remain 
        // in use until a 15 7168 or 15 7177 is obeyed.  While the instructions are in use the
        // contents of the locations are fixed and cannot be changed in any way.  The locations can 
        // be used normally after one of the above instructions has been obeyed.

        let mutable initialInstructionsEnabled = true

        let mutable initialInstructionsBase    = 0

        let initialInstructions () = 
            match machineType with
                | E920a when memorySize = 4096 ->
                    [|  InstructionToWord (1, 15, 8189);  // -3      
                        InstructionToWord (0,  0, 8180-4096);
                        InstructionToWord (0,  4, 8189-4096);
                        InstructionToWord (0, 15, 4094); 
                        InstructionToWord (0,  9, 8186-4096); 
                        InstructionToWord (0,  8, 8183-4096); 
                        InstructionToWord (0, 15, if machineType = E920a then 4094 else 2048); 
                        InstructionToWord (1,  5, 8180-4096); 
                        InstructionToWord (0 ,10,    1); 
                        InstructionToWord (0,  4,    1); 
                        InstructionToWord (0,  9, 8182-4096); 
                        InstructionToWord (0,  8, 8177-4096)  |]
                
                | _ ->         
                    [|  InstructionToWord (1, 15, 8189);  // -3      
                        InstructionToWord (0,  0, 8180);
                        InstructionToWord (0,  4, 8189);
                        InstructionToWord (0, 15, if machineType = E920a then 4094 else 2048); 
                        InstructionToWord (0,  9, 8186); 
                        InstructionToWord (0,  8, 8183); 
                        InstructionToWord (0, 15, 2048); 
                        InstructionToWord (1,  5, 8180); 
                        InstructionToWord (0 ,10,    1); 
                        InstructionToWord (0,  4,    1); 
                        InstructionToWord (0,  9, 8182); 
                        InstructionToWord (0,  8, 8177)  |]

        let mutable initialInstructionStore = initialInstructions ()

        let EnableInitialInstructions () =
            initialInstructionsEnabled <- true
            initialInstructionStore <- initialInstructions ()
            match machineType with
            | E920a                         -> initialInstructionsBase    <- if memorySize = 4096 then 4084 else 8180  
            | _                             -> initialInstructionsBase    <- 8180     
                

        let mutable watchLoc       = -1 // if set > 0 then generate a watch if this location is accessed
        let mutable watch          = false 
       
        let  ReadMem addr = 

            let address =
                      match machineType with
                      | E920a -> addr &&& mask13
                      | E920b
                      | E920m
                      | E900  -> addr &&& mask16
                      | E920c -> addr &&& mask17

            if   address = watchLoc then watch <- true
            if   address < 0 || address >= memorySize
            then raise (Machine (sprintf "Read from store address %d outside memory bounds" address))
            if initialInstructionsEnabled
            then if  address < initialInstructionsBase || address > (initialInstructionsBase+11)
                 then memory.[address]
                 else let w = initialInstructionStore.[address-initialInstructionsBase]
                      memory.[address] <- w
                      w
            else memory.[address]

        let WriteMem addr contents =

            let address =
                      match machineType with
                      | E920a -> addr &&& mask13
                      | E920b
                      | E920m
                      | E900  -> addr &&& mask16
                      | E920c -> addr &&& mask17

            if   address = watchLoc then watch <- true
            if   address < 0 || address >= memorySize
            then raise (Machine (sprintf "Write to store address %d outside memory bounds" address))
            elif initialInstructionsEnabled
            then if  address < initialInstructionsBase || address > (initialInstructionsBase+11)
                 then memory.[address] <- contents
                 else memory.[address] <- initialInstructionStore.[address-initialInstructionsBase] ||| contents 
            else memory.[address] <- contents

        // CENTRAL PROCESSING UNIT
        // Instruction decoding, interrupt handling and monitoring 
        
        // REGISTERS etc
        let mutable accumulator                = 0       // held as int
        let mutable qRegister                  = 0       // extension accumulator
        let mutable bRegisterAddr              = 1       // index register
        let mutable scrAddr                    = 0       // sequence control register in memory
        let mutable sequenceControlRegister    = 0       // 
        let mutable oldSequenceControlRegister = 0       // copy of SCR before incremented in instruction decode
        let mutable iRegister                  = 0       // function code
        let mutable pRegister                  = 0       // peripheral i/o
        let mutable relative                   = 0       // bit18 for 920C style absolute addressing
        let mutable holdUp                     = true    // true if paper tape station i/o is blocking, false otherwise

        let mutable wordGenerator     = 0     // setting of keys on control panel

        // TIMING
        let mutable cpuTime           = 0L    // execution time in microseconds * 10
        let mutable elapsedTime       = 0L    // i/o time in microseconds * 10 
        let mutable ptrTime           = 0L    // time when reader next free 
        let mutable ptpTime           = 0L    // time when punch next free    
        let mutable ttyTime           = 0L    // time when tty next free    
        let mutable pltTime           = 0L    // time when plotter next free 
        let mutable lpTime            = 0L    // time when line printer next free
        let mutable crTime            = 0L    // time when next card data ready 
        let mutable mtTime            = 0L    // time when magnetic tape next ready
        let mutable mtIntTime         = 0L    //  time when next magnetic tape interrupt due                                   
        let         realTimer         = new System.Diagnostics.Stopwatch ()  
        let mutable iCount            = 0L    // instructions executed since last reset
        
        let Elapsed () = max elapsedTime (max ptrTime (max ptpTime (max ttyTime pltTime)))

        let ResetTimes () =
            iCount      <- 0L
            ptrTime     <- 0L
            ptpTime     <- 0L
            ttyTime     <- 0L
            pltTime     <- 0L
            crTime      <- 0L
            lpTime      <- 0L
            mtTime      <- 0L
            mtIntTime   <- 0L
            cpuTime     <- 0L
            elapsedTime <- 0L
            realTimer.Reset ()

        // Speed of simulation
        let mutable slow = false   
        
        let SlowDown () =
            if   slow
            then YieldToDevices ()
                 let elapsed = Elapsed () / 10000L
                 let pause = (int (elapsed - realTimer.ElapsedMilliseconds)) 
                 if pause > 1000
                 then raise (Machine (sprintf "Problem in SLOW mode - 903 %d  PC %d"  
                                elapsed realTimer.ElapsedMilliseconds))
                 elif pause > 0
                 then System.Threading.Thread.Sleep pause

        // MONITORING
        let mutable stopped           = true                             // stop button pushed
        let mutable reset             = true                             // reset button pushed
        let mutable stopAddr          = -1                               // stop after restart
        let mutable stepCount         = -1                               // counter for STEP command
        let mutable tracing           = false                            // true to turn on instruction by instruction trace output
        let mutable algolTracing      = false                            // true to turn on Algol tracing
        let mutable nxpordAddr        = -1                               // location of nxpord in Algol interpreter
        let mutable traceLevel        = [|true; true; true; true; true|] // which levels should appear in a trace    
        let mutable traceStart        = -1                               // if >= 0, start of region to trace
        let mutable traceFinish       = 0                                // if traceStart >= 0, end of region to trace        
        let mutable logging           = false                            // true to turn on logging of instruction execution
        let mutable strobe            = false                            // true if any monitoring function is enabled

        let monitors    = new Dictionary<int, list<region>> ()
        let breakpoints = new List<int> ()

        let nullTraceRec = {scr=1; acc=0}

        let traceBufLen = 64
        let traceBuffer: TraceRec[] = Array.create traceBufLen nullTraceRec
        let mutable traceBufPtr = 0;

        let TraceBufferClear () = 
            for i=0 to traceBufLen-1 do 
                traceBuffer.[i] <- nullTraceRec

        let CheckForStrobe () = 
            strobe <- Seq.length monitors > 0 || breakpoints.Count > 0 ||  stepCount >= 0 || stopAddr >= 0
            || tracing || algolTracing || logging || lpTime > elapsedTime || crTime > elapsedTime 
            || mtIntTime > elapsedTime || watchLoc >= 0
                      
        // INTERRUPTS 
        let mutable interruptLevel             = 1                   // current interrupt level 1..4 
        let mutable takeInterrupt              = false               // true if interrupt is outstanding
        let mutable protect                    = false               // set true if interrupts have to be deferred
        // NB use of five elements in following vectors is laziness to simplify initialization.
        let levelActive      = [|false; true;  false; false; false|] // true if level n is runnable
        let interruptPending = [|false; false; false; false; false|] // true if interrupt pending 
                                                                     // on level 1-3
        let interruptTrace   = [|false; false; false; false; false|] // true if trace interrupt set 
                                                                     // on level 1-3  
        let LevelCheck level = 
            if   level < 0 || level > 3 
            then raise (Machine "Interrupt level not in range 1..3")

        let HighestActiveLevel () =
            if   levelActive.[1]
            then 1
            elif levelActive.[2]
            then 2
            elif levelActive.[3]
            then 3
            else 4

        let DisableInitialInstructions () =
            initialInstructionsEnabled <- false 
    
        // INTERRUPTS
        let InterruptOn level = // handle a new interrupt           
            if   levelActive.[level] 
            then interruptPending.[level] <- true // pend until target level terminates
            else levelActive.[level]      <- true // set level active  
            if   level < interruptLevel
            then takeInterrupt <- true

        let Modify N = N + (Normalize memory.[bRegisterAddr])

        // SCR on 920C has bit18 = relative, bits 17-1 address,
        // on other models just bits 16-1.
        // 920C SCR is held in a register and only dumped to memory
        // on a level switch
        let GetSCR () =
            match machineType with
            | E920a
            | E920b
            | E920m
            | E900  -> sequenceControlRegister <- memory.[scrAddr]
                       sequenceControlRegister
            | E920c -> sequenceControlRegister

        let SetSCR address =
            match machineType with
            | E920a -> sequenceControlRegister <- address &&& mask13
                       memory.[scrAddr] <-  sequenceControlRegister      
            | E920b
            | E920m
            | E900  -> sequenceControlRegister <- address &&& mask16
                       memory.[scrAddr] <-  sequenceControlRegister 
            | E920c -> sequenceControlRegister <- address &&& mask17

        let AdvanceSCR () =
            oldSequenceControlRegister <- GetSCR ()
            SetSCR (oldSequenceControlRegister+1)

        let SaveSCRH () =
            memory.[scrAddr] <- sequenceControlRegister ||| relative
            
        let EnterLevel level =  
            // printfn "ENTER %d" level
            SaveSCRH ()
            interruptLevel <- level
            levelActive.[level] <- true
            scrAddr <- (level-1) * 2
            bRegisterAddr <- scrAddr+1
            let SCRH = memory.[scrAddr]
            sequenceControlRegister <- SCRH &&& mask17
            relative <- SCRH &&& bit18

        let ExitLevel () =
            // printfn "EXIT %d" interruptLevel
            if interruptLevel <= 3
            then protect <- true // hold off interrupts for one instruction
                 SaveSCRH ()
                 DisableInitialInstructions ()  // in case leaving level 1
                 levelActive.[interruptLevel] <- false // deactivate ourselves
                 let oldLevel = interruptLevel
                 let rec DropLevel target = 
                    if   target = 4
                    then 4
                    elif levelActive.[target]
                    then target
                    else DropLevel (target+1)
                 EnterLevel (DropLevel (interruptLevel+1))
                 // check to see if trace interrupts enabled
                 if interruptTrace.[oldLevel] then InterruptOn oldLevel

        // 903 MULTIPLEXOR
        //
        // If a 903 has multiple peripherals they are connected through a multiplexor of up to
        // eight channels divided into two groups of 4 called A and B.
        //
        // In the simulator we assume all devices are attached via group A

        let mutable muxGroupA = true  // set false to disable this group
        let mutable muxGroupB = true  // set false to disable this group

        let CheckMuxGroupA () =
            if not muxGroupA  then raise (Machine "Multiplexor Group A not enabled")

        let ResetMux () =
            muxGroupA <- true; muxGroupB <- true


        // 4100 DEVICE INTERFACE for 903/920B
        //
        // Via a 4100 series interface matching unit, Elliott 4100 series peripherals could be connected to a 900
        // series machine.  The available devices included a line printer and a card reader.  Both devices used
        // an asynchrnous i/o model, raising interrupts to signal when ready for the next transfer.
        //
        
        // Interrupt driven devices (line printer, card reader) remain busy while acting on an i/o request.
        // This is handled by using the strobe facility to check for the busy period being complete.
        // (Time for card reader not known).

        let mutable crAttention = false
        let mutable crInterrupt = false
        let mutable lpInterrupt = false
        let mutable lpAttention = false

        let ResetIMU () =
            crInterrupt <- false
            crAttention <- false
            lpInterrupt <- false
            lpAttention <- false

        let IMUStatus () = // get status of 4100 peripherals
            CheckMuxGroupA ()
            let mutable status = bit17 ||| bit18 // VALID & COMPLETE signals
            if   crInterrupt
            then status <- status ||| bit1
            if   lpInterrupt 
            then status <- status ||| bit2       
            if   crAttention
            then status <- status ||| bit9
            if   lpAttention
            then status <- status ||| bit10
            ~~~status

        // CARD READER for 903/920B

        // status indications
        let mutable crManual           = true
        let mutable crBusy             = false
        let mutable crInterruptEnabled = false
        let mutable crMissedTransfer   = false
        let mutable crHopperEmpty      = false
        let mutable crDataLeft         = false

        // card being transferred
        let mutable card       = None 
        let mutable crInCount  = 0 // count of columns read by reader
        let mutable crOutCount = 0 // count of chars read by program

        let ResetCR () = // card reader hardware reset
            crManual            <- false
            crBusy              <- false
            crInterruptEnabled  <- false
            crInterrupt         <- false
            crMissedTransfer    <- false  
            crHopperEmpty       <- false
            crDataLeft          <- false   
            crTime              <- 0L  
            card                <- None
            crInCount           <- 0        
            crOutCount          <- 0        

        // guesses at card timings based on 300 cards/min 200ms/card
        let crFeedTime = 25000L   // assume 2.5ms to feed card into hopper
        let crColTime  = 25000L   // assume 2.5ms per column - 80*2.5=200ms

        let CRDelay interval = // set time to next interrupt
            crTime <- elapsedTime+interval
            crBusy <- true
            strobe <- true

        let CRCancel () = // abandon any transfer in process
            crBusy      <- false
            crTime      <- 0L
            CheckForStrobe ()

        let CRAttention () = // signal a card reader attention
            CRCancel ()
            if crInterruptEnabled 
            then  crAttention <- true
                  InterruptOn 2

        let CRControl w = // write card reader control word 
            CheckMuxGroupA () 
            if   w &&& bit1 = bit1
            then // disable interrupts
                 crInterruptEnabled <- false
            elif w &&& bit2 = bit2
            then // enable interrupts
                 crInterruptEnabled <- true
            elif w &&& 3 = 3 || w &&& 0o674 <> 0
            then raise (Device (sprintf "Unexpected card reader control word &%o" w))
            if   w &&& bit7 = bit7 
            then // feed a new card
                 match card with
                 | Some(c)  ->  // previous card still in reader - treat as data left error
                                crDataLeft  <- true
                                CRAttention ()
                 | _        ->  // previous card (if any) complete - get next card
                                crManual <- false // reset manual state
                                try card  <- GetCard () with
                                | CRManual  ->  crManual <- true
                                                CRAttention ()
                                match card with
                                | Some(c)   ->  // new card successfully read, set up interrupts for columns
                                                CRDelay crFeedTime
                                                crInCount <- 0; crOutCount <- 0 
                                                crBusy <- true
                                | _         ->  // failed to read card - treat as empty hopper error condition
                                                crHopperEmpty <- true
                                                CRAttention ()

        let CRInterruptCheck () = // next column ready to be read 
            crInCount <- crInCount+1
            if   crInCount < 80 // 
            then // intermediate column
                 CRDelay crColTime  // remain busy until all of card is read 
            else // last column
                 crBusy <- false
                 crTime <- 0L
                 CheckForStrobe ()
            if   crInterruptEnabled 
            then crInterrupt <- true
                 InterruptOn 2

        let CRReadData () = // read waiting card data
            CheckMuxGroupA ()
            crOutCount <- crOutCount+1
            let MissedTransfer () =
                 crMissedTransfer <- true
                 CRAttention ()
                 0 // spurious data
            match card with
            | Some (buf) ->  // card in reader
                            let col  = (crOutCount+1)/2
                            let slot = (crOutCount-1)/2
                            if   col <> crInCount
                            then // program has fallen behind reader
                                 MissedTransfer ()
                            else let ch =
                                    if crOutCount &&& 1 = 1
                                    then buf.[slot] >>> 6
                                    else buf.[slot] &&& 63
                                 if   crOutCount = 160
                                 then // last column processed, remove card from reader
                                      card   <- None
                                 crInterrupt <- false // interrupt serviced
                                 ch
            | _         ->  // card has exited reader
                            raise (Device "Transfer attempted when no card in reader")
                 
        let CRStatus () = // read card reader status  
            CheckMuxGroupA ()
            crAttention <- false; crInterrupt <- false
            let mutable status = 0
            if   crBusy 
            then status <- bit1 
            if   crManual
            then status <- status ||| bit2 
            if   not crInterruptEnabled
            then status <- status ||| bit3
            if   crMissedTransfer
            then status <- status ||| bit4
            if   crHopperEmpty  || crDataLeft || (not (CheckCard ()))
            then status <- status ||| bit5
            status

        // LINE PRINTER for 903/920B
        let mutable lpManual          = false
        let mutable lpInterruptEnabled = false 
        let mutable lpBusy             = false
        let mutable lpNRE              = false   

        let ResetLP () =
            lpInterruptEnabled <- false
            lpInterrupt        <- false
            lpAttention        <- false
            lpBusy             <- false
            lpManual           <- false
            lpNRE              <- false
            lpTime             <- 0L      

        let LPCancel () =
            lpBusy <- false
            lpTime <- 0L
            CheckForStrobe ()
        
        let LPControl w = // set printer control word
            CheckMuxGroupA ()
            lpInterrupt <- false
            if   w = 1
            then // disable interrupts
                 lpInterruptEnabled <- false
            elif w = 2
            then // enable interrupts
                 lpInterruptEnabled <- true
                 if   not lpBusy
                 then lpInterrupt <- true
                      InterruptOn 2
                 
        let LPInterruptCheck () = // previous transfer completed
            lpTime <- 0L
            CheckForStrobe ()
            lpBusy <- false
            if   lpInterruptEnabled 
            then lpInterrupt <- true
                 InterruptOn 2

        let LPStatus () = // read line printer status  
            CheckMuxGroupA ()
            lpAttention <- false; lpInterrupt <- false
            let mutable status = 0
            if   lpBusy 
            then status <- bit1 
            if lpManual 
            then status <- status ||| bit2
            if not lpInterruptEnabled
            then status <- status ||| bit3
            if   lpNRE
            then status <- status ||| bit6
            status
            
        let lineTime = 60L*10000000L/315L // printer operates at 315 lines/minute

        let LPTransfer buffer = // transfer buffer to printer
            CheckMuxGroupA ()
            lpInterrupt <- false
            lpManual <- false // will be reset if detached
            if   not lpBusy
            then let lines =
                    try PutLPChars buffer with
                    | LPManual  ->  lpManual <- true; -1L
                    | exn       -> raise exn
                 if   lines >= 0L
                 then lpTime <- elapsedTime+lines*lineTime 
                      // printfn " wait = %d" (lpTime-elapsedTime)
                      lpBusy <- true
                      strobe <- true
            else raise (Device "Transfer attempted while line printer busy")

        
        // MAGNETIC TAPE SYSTEM  for 903/920B

        //  Tape speed 45 in/s
        //  Tape length 2,400 ft
        //  Data transfer rate 3000 wds/s
        //  Packing density 200 ch/in = 66.3 wds/in
        //  Inter block gap 0.75in, 150 ch / 50 wds
        //  Erase writes 4in blank tape
        //  Rewind speed 180 in/sec

        // do nothing write 9ms
        // do nothing read 14ms
        // data interrupts must be answered within 250us
        // data interrupts very 333us
        // tape start 11.8ms stop 20ms
        // null operation time not known


        let charTime             =    1110L     // 111us
        let wordTime             =    3330L     // 333us
        let limitTime            =    2500L     // 250us 
        let readDoNothingTime    =   90000L     //   9ms  
        let tapeStartTimeR       = readDoNothingTime+wordTime
        let writeDoNothingTime   =  140000L     //  14ms
        let tapeStartTimeW       = writeDoNothingTime+wordTime
        let tapeStopTimeWW       =  250000L     //  25ms - manual says 20ms, XMT71 expects 25ms after write word
        let tapeStopTimeWB       =  200000L     //  20ms
        let tapeStopTimeR        =  118000L     //   11.8 ms
        let eraseTime            = 1110000L     // erase writes 4" of blank tape - (XMT71 max 111ms)
        let backspaceTime        = tapeStartTimeR+tapeStopTimeR // positioning time, also need to add in block time  
     

        // buffer for collecting data comprising a block
        let mutable buffer: int[] = [||]      // arbitrary limit, Elliott software imposes max of 2047
        let mutable bufPos        = 0         // next slot in buffer to fill
        let mutable mtReading     = false     // set true in a read transfer    
        let mutable mtWriting     = false     // set true in a write transfer 
        let mutable mtTapemark    = false     // set true to write a tape mark
        let mutable mtOddParity   = true      // set false for even parity
        let mutable wroteWord     = true      // false if last write was a write block

        type Handler =    { tape:           Tape;          // attached file
                            manual:         bool;          // true if in manual
                            busyUntil:      int64;         // elapsed time when handler will become idle
                            missedTransfer: bool;          // true if missed a transfer
                            shortTransfer : bool;          // true if a short transfer occurs (fewer bytes read than in tape block)
                            longTransfer:   bool;          // true if a long transfer occurs (more bytes read than in tape block)
                            zeroCharacter:  bool;          // true if reading blank tape
                            doneNothing:    bool;          // true if last instruction was a do nothing
                            parityError:    bool;          // true if parity error in last read
                            } 

        let mutable currentHandler = 0                     // current handler accepting commands

        let mutable mtInterruptEnabled  = false
        
        let mtHandler = [| None; None; None; None |]

        let NoTape hdlr = raise (Device (sprintf "No tape attached to handler %d" hdlr))

        let MTCheckHandler hdlr =
            if hdlr < 0 || hdlr > 3 then raise (Machine (sprintf "Handler number %d not valid" hdlr))

        // MTMount & MTUnmount at end

        let MTPrepareToRead h = 
            //printfn "MTPrepareToRead %d" currentHandler
            mtReading <- true
            let p, b = h.tape.ReadBlock ()
            if p <> mtOddParity 
            then mtHandler.[currentHandler] <- Some { h with parityError=true }
            buffer    <- b
            bufPos    <- 0
            mtTime    <- elapsedTime + tapeStartTimeR 
            if mtInterruptEnabled then mtIntTime <- mtTime-limitTime
            
        let MTWPrepare h opName = 
            // helper  for MTPrepareToWrite & MTPrepareToWriteTapemark 
            //printfn "%s %d" opName currentHandler
            if   not h.tape.WritePermit
            then mtHandler.[currentHandler] <- Some { h with doneNothing=true }
                 mtTime <- elapsedTime + readDoNothingTime
                 buffer <- Array.zeroCreate 8192 // this will be expanded if required
            else mtTime <- elapsedTime + tapeStartTimeW 
                 buffer <- [||]
            bufPos <- 0
            if mtInterruptEnabled then mtIntTime <- mtTime-limitTime
 
        let MTPrepareToWrite h = 
            MTWPrepare h "PrepareToWrite" 
            mtWriting <- true

        let MTPrepareToWriteTapemark h = 
            MTWPrepare h "PrepareToWriteTapemark" 
            mtTapemark <- true

        let MTErase h =
           //printfn "MTErase %d" currentHandler
           if   not h.tape.WritePermit
           then mtHandler.[currentHandler] <- Some { h with doneNothing=true }
                mtTime <- elapsedTime+writeDoNothingTime
           else h.tape.Erase ()
                mtTime <- elapsedTime+eraseTime
           if mtInterruptEnabled then mtIntTime <- mtTime-limitTime   

        let MTBackSpace h = 
            //printfn "MTBackspace %d" currentHandler
            if   h.tape.AtLoadPoint
            then mtHandler.[currentHandler] <- Some { h with doneNothing=true }
                 mtTime <- mtTime+readDoNothingTime
            else let chars = h.tape.Backspace ()
                 mtTime <- tapeStartTimeR+chars*charTime+tapeStopTimeR
            if mtInterruptEnabled then mtIntTime <- mtTime-limitTime

        let MTRewind h manual = 
            // rewind tape on handler hdlr, putting into manual if required
            //printfn "MTRewind %d %s " currentHandler (if manual then "in manual" else "")
            if manual 
            then mtHandler.[currentHandler] <- Some { h with manual=manual }
            else let rewindChars = h.tape.Rewind ()
                 let rewindTime  = rewindChars * 10000000L / 200L / 180L
                 mtHandler.[currentHandler] <- Some { h with busyUntil=elapsedTime+rewindTime }

        let ZeroCharCheck w h =
            if   not mtOddParity || h.parityError
            then if   (w &&& 0o770000) = 0 || (w &&& 0o7700) = 0 || (w &&& 0o77) = 0
                 then mtHandler.[currentHandler] <- Some { h with zeroCharacter=true }

        let NoTransfer () =
            mtTime <- elapsedTime+wordTime 
            if mtInterruptEnabled then mtIntTime <- mtTime 

        let MissedTransfer () =
            elapsedTime > mtTime ||
              ( (not mtInterruptEnabled) && mtTime-elapsedTime < limitTime ) 

        let MTReadWord () = 
            //printfn "MTReadWord hdlr %d" currentHandler
            CheckMuxGroupA ()
            mtIntTime <- 0L // clear any pending interrupt
            match mtHandler.[currentHandler] with
            | Some (h)  ->  // check read is prepared
                            if   not mtReading
                            then raise (Machine ("Mag tape \"ReadWord\" not prepared"))
                            // check to see if transfer is still viable
                            if MissedTransfer ()
                            then // missed the transfer                                 
                                 mtHandler.[currentHandler] <- Some { h with missedTransfer=true }
                                 NoTransfer (); 0
                            elif h.zeroCharacter || h.shortTransfer
                            then NoTransfer (); 0
                            elif h.manual
                            then mtHandler.[currentHandler] <- Some { h with doneNothing=true    }
                                 NoTransfer (); 0
                            elif buffer.Length = 0 // no block to read
                            then mtHandler.[currentHandler] <- Some { h with zeroCharacter=true  }
                                 NoTransfer (); 0
                            elif buffer.Length-bufPos <= 0 // no data to read
                            then mtHandler.[currentHandler] <- Some { h with shortTransfer=true  }
                                 NoTransfer (); 0
                            else // wait for controller, transfer one word, ready next transfer or close
                                 elapsedTime <- mtTime// complete current word
                                 mtTime      <- mtTime+wordTime
                                 if   mtInterruptEnabled 
                                 then mtIntTime   <- mtTime-limitTime // interrupt 250 usec before ready for next transfer
                                 let data = buffer.[bufPos]
                                 ZeroCharCheck data h
                                 bufPos <- bufPos+1 
                                 data                              
            | None      ->  NoTape currentHandler  

        let MTReadBlock a q12  =
            //printfn "MTReadBlock hdlr %d a %d q %d"  currentHandler a q12
            CheckMuxGroupA ()
            mtIntTime <- 0L // clear any pending interrupt
            match mtHandler.[currentHandler] with
            | Some (h)  ->  // check read is prepared
                            if   not mtReading
                            then raise (Machine ("Mag tape \"ReadBlock\" not prepared"))
                            // check to see if transfer is still viable
                            if   MissedTransfer ()
                            then // missed the transfer                                 
                                 mtHandler.[currentHandler] <- Some { h with missedTransfer=true }
                                 NoTransfer (); 0
                            elif h.zeroCharacter || h.shortTransfer // did a previous transfer fail?
                            then NoTransfer (); 0
                            elif h.manual
                            then mtHandler.[currentHandler] <- Some { h with doneNothing=true    }
                                 NoTransfer (); 0
                            elif buffer.Length = 0 // no block to read
                            then mtHandler.[currentHandler] <- Some { h with zeroCharacter=true  }
                                 NoTransfer (); 0
                            else // wait for controller, transfer block, ready next transfer or close
                                 let words = min q12 (buffer.Length-bufPos)       
                                 if   words < q12
                                 then mtHandler.[currentHandler] <- Some { h with shortTransfer=true  }                                   
                                 // wait for controller, transfer block, ready next transfer or close
                                 elapsedTime <- mtTime+(int64 (words-1))*wordTime
                                 mtTime      <- elapsedTime+wordTime
                                 if   mtInterruptEnabled 
                                 then mtIntTime   <- mtTime-limitTime // interrupt 250 usec before ready for next transfer
                                 // copy words
                                 for w=0 to words-1 do
                                    let data = buffer.[bufPos]
                                    bufPos <- bufPos+1   
                                    ZeroCharCheck data h
                                    WriteMem (a+w) data 
                                 buffer.[bufPos-1]                                                        
            | None      ->  NoTape currentHandler  

        let MTBufferGrow n =
            if bufPos+n >= buffer.Length 
            then let newBuf: int[] = Array.zeroCreate (buffer.Length+8192)
                 buffer.CopyTo (newBuf, 0)
                 buffer <- newBuf

        let MTWriteWord a = 
            //printfn "MTWriteWord hdlr %d a %d" currentHandler a
            CheckMuxGroupA ()
            mtIntTime <- 0L // clear any pending interrupt
            wroteWord <- true
            match mtHandler.[currentHandler] with
            | Some (h)  ->  if   not (mtWriting || mtTapemark)
                            then raise (Machine "Mag tape \"WriteWord\" not prepared")
                            elif  h.manual || not h.tape.WritePermit
                            then mtHandler.[currentHandler] <- Some { h with doneNothing=true } 
                                 NoTransfer () |> ignore
                            elif MissedTransfer ()
                            then mtHandler.[currentHandler] <- Some { h with missedTransfer=true }
                                 NoTransfer () |> ignore
                            else // wait for controller, transfer one word, ready next transfer or close
                                 elapsedTime <- mtTime
                                 mtTime      <- mtTime+wordTime
                                 if   mtInterruptEnabled 
                                 then mtIntTime   <- mtTime-limitTime // interrupt 250 usec before ready for next transfer
                                 MTBufferGrow 1 // expand buffer if necessary
                                 buffer.[bufPos] <- a
                                 bufPos <- bufPos+1
                                 ZeroCharCheck a h 
            | None      ->  NoTape currentHandler

        let MTWriteBlock a q12 = 
            //printfn "MTWriteBlock hdlr %d a %d q %d" currentHandler a q12
            CheckMuxGroupA ()
            mtIntTime <- 0L // clear any pending interrupt
            wroteWord <- false
            match mtHandler.[currentHandler] with
            | Some (h)  ->  if   not mtWriting
                            then raise (Machine "Mag tape \"WriteBlock\" not prepared")
                            elif  h.manual || not h.tape.WritePermit
                            then mtHandler.[currentHandler] <- Some { h with doneNothing=true } 
                                 NoTransfer (); 0
                            elif MissedTransfer ()
                            then mtHandler.[currentHandler] <- Some { h with missedTransfer=true }
                                 NoTransfer (); 0
                            else // wait for controller, transfer block, ready next transfer or close
                                 elapsedTime <- mtTime+(int64 (q12-1))*wordTime
                                 mtTime      <- elapsedTime+wordTime
                                 if   mtInterruptEnabled 
                                 then mtIntTime   <- mtTime-limitTime // interrupt 250 usec before ready for next transfer
                                 MTBufferGrow q12     
                                 let last = bufPos+q12-1
                                 for i = 0 to q12-1 do
                                     let data = ReadMem (a+i)
                                     ZeroCharCheck data h
                                     buffer.[bufPos+i] <- data
                                 bufPos <- bufPos+q12 
                                 if q12 = 0 then 0 else buffer.[bufPos-1]
            | None      -> NoTape currentHandler

        let MTCloseBlock () =
            let writeTapeStopTime () =
                if wroteWord then tapeStopTimeWW else tapeStopTimeWB
            //printfn "MTCloseBlock %d" currentHandler
            CheckMuxGroupA ()
            mtIntTime <- 0L // clear any pending interrupt
            match mtHandler.[currentHandler] with
            | Some (h)  ->  if   h.doneNothing 
                            then mtReading <- false; mtWriting <- false; mtTapemark <- false 
                                 elapsedTime <- max elapsedTime mtTime
                                 mtTime <- elapsedTime
                                 if mtInterruptEnabled then mtIntTime <- elapsedTime+limitTime // XMT71 requires at least elapsedTime+1 here       
                            elif MissedTransfer ()
                            then mtHandler.[currentHandler] <- Some { h with missedTransfer=true }
                                 mtReading <- false; mtWriting <- false; mtTapemark <- false;
                                 mtTime    <- elapsedTime+( if mtReading then tapeStopTimeR else writeTapeStopTime () ) 
                                 mtIntTime <- mtTime
                            elif  mtReading 
                            then // wait for controller
                                 elapsedTime <- mtTime
                                 mtReading <- false;
                                 if bufPos < buffer.Length
                                 then mtHandler.[currentHandler] <- Some { h with longTransfer=true } 
                                 if mtInterruptEnabled then mtIntTime <- elapsedTime+tapeStopTimeR
                            elif mtWriting || mtTapemark
                            then // wait for controller
                                 elapsedTime <- mtTime
                                 mtWriting <- false; mtTapemark <- false
                                 h.tape.WriteBlock buffer.[..bufPos-1] mtOddParity 
                                 if mtInterruptEnabled then mtIntTime <- elapsedTime+writeTapeStopTime ()
                            else raise  (Machine "Mag tape \"CloseBlock\" not prepared")
            | None      -> NoTape currentHandler

        let MTControl a = 
            //printfn "MTControl &%o" a
            CheckMuxGroupA ()
            mtIntTime <- 0L // clear any pending interrupt
            if mtTime > elapsedTime then elapsedTime <- mtTime // wait for controller
            if   mtReading || mtWriting || mtTapemark
            then raise (Device "Magnetic tape controller hang due to out of order control word")
            currentHandler <- a&&&3
            match mtHandler.[currentHandler] with
            | Some (h)  ->  // reset status bits
                            mtHandler.[currentHandler] <- 
                                    Some { h with missedTransfer=false; shortTransfer=false; longTransfer=false; 
                                                  zeroCharacter=false;  doneNothing=false;   parityError=false }
                            // see if control word has to be delayed while handler is busy
                            if h.busyUntil > elapsedTime then elapsedTime <- h.busyUntil
                            mtIntTime <- 0L
                            if   a&&&bit5=bit5 
                            then mtInterruptEnabled <- true;  strobe <- true
                            else mtInterruptEnabled <- false; CheckForStrobe ()
                            match (a>>>5)&&&3 with
                            | 0 ->  () // no change in parity
                            | 1 ->  mtOddParity <- true
                            | 2 ->  mtOddParity <- false
                            | _ ->  () // strictly, effect is undefined
                            if   h.manual
                            then mtHandler.[currentHandler] <- 
                                    Some { h with missedTransfer=false; shortTransfer=false; longTransfer=false; 
                                                  zeroCharacter=false;  doneNothing=true;    parityError=false }
                            else match (a>>>7)&&&7 with
                                    | 0 -> (*printfn "No Motion"*) ()
                                    | 1 -> MTErase h
                                    | 2 -> MTBackSpace h
                                    | 3 -> MTRewind h false // rewind and remain online
                                    | 4 -> MTPrepareToWriteTapemark h
                                    | 5 -> MTPrepareToRead h
                                    | 6 -> MTPrepareToWrite h
                                    | 7 -> MTRewind h true // rewind and go manual
                                    |_  -> failwith "Internal error in MTControl (shouldn't happen)"
            | None      ->  // only permit handler selection if no tape present
                            if   (a>>>7)&&&7 <> 0
                            then NoTape currentHandler ()
            
        let rec MTStatus () = // read status of current handler
            //printf "MTStatus"
            CheckMuxGroupA ()
            mtIntTime <- 0L // clear any pending interrupt
            CheckForStrobe ()
            let mutable status = 0
            match mtHandler.[currentHandler] with
            | Some (h)  ->  if mtReading || mtWriting || mtTapemark 
                            then MTCloseBlock ()
                                 status <- MTStatus ()
                            elif mtTime > elapsedTime 
                            then elapsedTime <- mtTime // wait for controller
                            if   h.busyUntil > elapsedTime then status <- status ||| bit1
                            if   h.manual 
                            then status <- status ||| bit2
                            else // handler in remote
                                 if   h.missedTransfer 
                                 then status <- status ||| bit3
                                 if   h.parityError
                                 then status <- status ||| bit4
                                 if   h.shortTransfer
                                 then status <- status ||| bit5
                                 if  h.longTransfer
                                 then status <- status ||| bit6
                                 if   h.tape.WritePermit 
                                 then status <- status ||| bit7
                                 if   h.tape.AtLoadPoint
                                 then status <- status ||| bit8 
                                 if   h.tape.AtEndOfTape
                                 then status <- status ||| bit9
                                 if   h.zeroCharacter
                                 then status <- status ||| bit10
                                 if h.doneNothing
                                 then status <- status ||| bit11
                            mtInterruptEnabled <- false // and disable further interrupts
                            mtHandler.[currentHandler] <- Some { h with missedTransfer=false; longTransfer=false; shortTransfer=false; 
                                                                        zeroCharacter=false ; parityError=false;  doneNothing=false }
            | None     ->   status <- bit2 // manual
            //printfn "=&%o" status
            status
                     
        let ResetMT () =
            mtReading <- false
            mtWriting <- false
            mtTime    <- 0L
            mtIntTime <- 0L
            mtInterruptEnabled <- false
            mtOddParity <- true

        let TidyUpMT () = 
            for hdlr = 0 to 3 do 
                match mtHandler.[hdlr] with
                | Some (h)  ->  h.tape.Close ()
                | None      -> ()
                mtHandler.[hdlr] <- None
            ResetMT ()
                  
        // ERROR HANDLING                                                  
        let BadInstruction F N =
            raise (Machine (sprintf "Instruction %d %d is not supported" F N))

        let Bad15Instruction Z = BadInstruction 15 Z
            
        let StoppedError ()    = 
            raise (Machine "Machine in stopped state")
        let NotStoppedError () = 
            raise (Machine "Machine not in stopped state") 
            
        // PAPER TAPE STATION
        // Setting of paper tape station control switches on front desk
        // Input selection can be READER, AUTO or TELEPRINTER
        // Output selection can be PUNCH, AUTO or TELEPRINTER
        // Auto discriminates based on peripheral address

        let ReaderInput Z =
            pRegister <- Z
            let cpu = int64 timing.[22]
            cpuTime     <- cpuTime + cpu
            elapsedTime <- elapsedTime + cpu
            let read =
                if   elapsedTime < ptrTime
                then // device is busy 
                     if   holdUp 
                     then // wait
                          elapsedTime <- ptrTime
                          true
                     else false                                                                        
                 else // device is ready
                      true
            if   read
            then ptrTime <- ptrTime + ptrCharTime 
                 try // reset SCR if error signalled
                    let ch = int (GetReaderChar ())
                    accumulator <- (accumulator <<< 7 ||| ch) &&& mask18
                 with
                 | e -> SetSCR oldSequenceControlRegister
                        raise e
            else  accumulator <- accumulator <<< 7 

        let PunchOutput Z =
            pRegister <- Z
            let cpu = int64 timing.[22]
            cpuTime     <- cpuTime + cpu
            elapsedTime <- elapsedTime + cpu
            let write =
                if   elapsedTime < ptpTime
                then // device is busy 
                        if   holdUp 
                        then // wait
                             elapsedTime <- ptpTime 
                             true
                        else false                                                                        
                else // device is ready
                        true
            if   write
            then ptpTime <- elapsedTime + ptpCharTime                         
                 try 
                        PutPunchChar (byte (accumulator &&& mask8))  
                 with
                 | e ->  SetSCR oldSequenceControlRegister
                         raise e  
        let TTYInput Z =
            pRegister <- Z
            let cpu = int64 timing.[22]
            cpuTime     <- cpuTime + cpu
            elapsedTime <- elapsedTime + cpu
            let read =
                if   elapsedTime < ttyTime
                then // device is busy 
                     if holdUp
                     then // have to wait for device and data
                          elapsedTime <- ttyTime 
                          while not (TTYInputReady ()) do YieldToDevices () 
                          true 
                     else false                                                                   
                else // device is ready
                     TTYInputReady ()
            if   read
            then ttyTime <- elapsedTime+ttyCharTime
                 try // reset SCR if EOF signalled
                    let ch = int (GetTTYChar ())
                    // printfn "TTYIN @%d ch=%d" sequenceControlRegister ch
                    accumulator <- (accumulator <<< 7 ||| ch) &&& mask18
                 with
                 | e -> SetSCR oldSequenceControlRegister
                        raise e
            else  accumulator <- accumulator <<< 7

        let TTYOutput Z =
            pRegister <- Z
            let cpu = int64 timing.[22]
            cpuTime     <- cpuTime + cpu
            elapsedTime <- elapsedTime + cpu
            let write =
                if   elapsedTime < ttyTime
                then // device is busy 
                     if   holdUp 
                     then // wait
                          elapsedTime <- ttyTime 
                          true
                     else false                                                                        
                else // device is ready
                     true
            if   write
            then ttyTime <- elapsedTime + ttyCharTime 
                 try 
                    PutTTYChar (byte (accumulator &&& mask8))  
                 with
                 | e ->  SetSCR oldSequenceControlRegister
                         raise e                             
        type Input = 
            | ReaderIn
            | AutoIn
            | TeleprinterIn

        type Output = 
            | PunchOut
            | AutoOut
            | TeleprinterOut

        let mutable SelectInput  = AutoIn
        let mutable SelectOutput = AutoOut

        let Reader Z = 
            match SelectInput with
            | ReaderIn
            | AutoIn        -> ReaderInput Z
            |teleprinterIn  -> TTYInput Z

        let TTYIn Z =
            match SelectInput with
            | ReaderIn      -> ReaderInput Z
            | AutoIn
            | TeleprinterIn -> TTYInput Z

        let Punch Z =
            match SelectOutput with
            | PunchOut
            | AutoOut         -> PunchOutput Z
            | teleprinterOut  -> TTYOutput Z

        let TTYOut Z =
            match SelectOutput with
            | PunchOut        -> PunchOutput Z
            | AutoOut
            | TeleprinterOut  -> TTYOutput Z


        // INSTRUCTION DECODING          
        let Execute word =  
            // Arithmetic is two's complement fixed point
            // A is the accumulator 
            // B is the B register
            // Q is the Qregister bits [18..2]
            // M is (S[16..14}+n)[16..1] or (S[16..14]+B+n)[16..1] if modified
            // m is the contents memory location M
            // Z = N or (N+B)[13..1]
           
            // SHIFT operators for combined accumulator and Q register
            let aqShiftLeft () =
                accumulator <- (accumulator <<< 1) &&& mask18
                if qRegister >= bit18 then accumulator <- accumulator ||| 1
                qRegister <- (qRegister <<< 1) &&& mask18
                
            let aqShiftRight () =
                qRegister <- qRegister >>> 1
                if accumulator &&& 1 <> 0 then qRegister <- qRegister ||| bit18
                if accumulator >= bit18
                then accumulator <- bit18 ||| ((accumulator >>> 1) &&& mask17)
                else accumulator <- (accumulator >>> 1) &&& mask17

            // INSTRUCTION DECODING
            // Calculate operation address from instruction /F N
            // M is (S[17/16..14}+N)[17..1] or (S[17/16..14]+B+N)[16..1] if modified 
            // 17 bits is for 920C, 16 bits for 920A,B,M, generic 900

            let modify  = ModifyField   word // modify bit
            iRegister <-  FunctionField word // function code
            let N       = AddressField  word // N is instruction operand field

            // Check for B modification
            let mutable modifyTime = 0L
            let  M, MJump = // MJump is modified operand field for 7, 8, 9, M is for other functions
                if   modify <> 0
                then // apply B modification - Q is affected
                     modifyTime  <- int64 timing.[0]
                     cpuTime     <- cpuTime + modifyTime
                     elapsedTime <- elapsedTime + modifyTime
                     let m = Modify N
                     match machineType with
                     | E900              -> // Generic 900 leaves Q unchanged, 920M effect not known
                                            let mm = (m+(oldSequenceControlRegister &&& aModuleMask))
                                            (mm, mm)
                     | E920a             -> qRegister <- word                                           
                                            let mm = m &&& mask13 // max 8K store
                                            (mm, mm)
                     | E920b             -> qRegister <- N                                           
                                            let mm = (m+(oldSequenceControlRegister &&& aModuleMask))
                                            if   mm = 65552
                                            then printfn "N =%d B=%d (%d) m=%d (%d)" N memory.[bRegisterAddr] 
                                                         (Normalize memory.[bRegisterAddr])
                                                         m (Normalize m)
                                            (mm, mm)
                     | E920m              -> // 920M "affected" but not known how
                                            qRegister <- N
                                            let mm = (m+(oldSequenceControlRegister &&& aModuleMask))
                                            (mm, mm)  
                     | E920c             -> // Q effect not known
                                            let mm = (m+(oldSequenceControlRegister &&& cModuleMask))
                                            ((if relative = 0 then mm else m), mm)              
                 elif machineType = E920c
                 then // 920C unmodified - 17 bits, relative or absolute mode
                      let mm = (N+(oldSequenceControlRegister &&& cModuleMask))
                      ((if relative = 0 then mm else N), mm)
                 else // all others - 16 bits
                      let mm = (N+(oldSequenceControlRegister &&& aModuleMask))
                      (mm, mm)            
            
            // Helper functions for jump instructions
            let I () = if modify <> 0 then Modify word else word
            let adjust modifyTime =
                // on 920C conditionals are tested BEFORE B modification
                if   machineType = E920c && modify = 0 
                then cpuTime <- cpuTime - modifyTime; elapsedTime <- elapsedTime - modifyTime     
                      
            // ORDER CODE
            match iRegister with
                |  0  -> // set B register 
                         // B:=Q[18..1]:=m
                         let t = int64 timing.[1]
                         cpuTime     <- cpuTime + t
                         elapsedTime <- elapsedTime + t
                         let newb = ReadMem M
                         memory.[bRegisterAddr] <- newb
                         qRegister <- newb
                         protect <- true // interrupts are deferred after a 0 instruction
                         
                |  1  -> // Add
                         //A:=A+m
                         let t = int64 timing.[2]
                         cpuTime     <- cpuTime + t
                         elapsedTime <- elapsedTime + t
                         accumulator <- ((ReadMem M) + accumulator) &&& mask18
                       
                |  2  -> // Negate & add
                         // A:=m-A; Q[18..1]:=m
                         let t = int64 timing.[3]
                         cpuTime     <- cpuTime + t
                         elapsedTime <- elapsedTime + t
                         qRegister <- ReadMem M
                         accumulator <- (qRegister - accumulator) &&& mask18
                        
                |  3  -> // store Q register
                         // m[18]:=0; m[17..1]:=Q[18..2]
                         let t = int64 timing.[4]
                         cpuTime     <- cpuTime + t
                         elapsedTime <- elapsedTime + t
                         WriteMem M (qRegister >>> 1)
                 
                |  4  -> // read memory
                         // A:=m
                         let t = int64 timing.[5]
                         cpuTime     <- cpuTime + t
                         elapsedTime <- elapsedTime + t
                         accumulator <- ReadMem M
              
                |  5  -> // write memory
                         // m:=A
                         let t = int64 timing.[6]
                         cpuTime     <- cpuTime + t
                         elapsedTime <- elapsedTime + t
                         // WriteMem M accumulator
                         if  M = 65552
                         then raise (Machine (sprintf "B=%d (%d) N=%d S=%d SMod=%d"
                                                       memory.[bRegisterAddr] (Normalize memory.[bRegisterAddr])
                                                       N oldSequenceControlRegister (oldSequenceControlRegister&&&cModuleMask)))
                         WriteMem M accumulator
              
                |  6  -> // collate
                         // A:=A and m; Q affected (920A)
                         let t = int64 timing.[7]
                         cpuTime     <- cpuTime + t
                         elapsedTime <- elapsedTime + t
                         let n = ReadMem M
                         accumulator <- accumulator &&& n
                         if   machineType = E920a 
                         then qRegister <- (accumulator+n) &&& mask18
                        
                |  7  -> // jump if zero
                         // if A=0 then S:=M; Q:=affected (920A,B,M)
                         // M is always relative
                         match machineType with
                         | E900  
                         | E920c -> ()
                         | E920a -> qRegister <- I ()                     
                         | E920b 
                         | E920m -> qRegister <- N 
                         if   accumulator < 0
                         then let t = int64 timing.[8]
                              cpuTime     <- cpuTime + t
                              elapsedTime <- elapsedTime + t
                              adjust modifyTime
                         elif accumulator > 0 
                         then let t = int64 timing.[9]
                              cpuTime     <- cpuTime + t
                              elapsedTime <- elapsedTime + t
                              adjust modifyTime 
                         else let t = int64 timing.[10]
                              cpuTime     <- cpuTime + t
                              elapsedTime <- elapsedTime + t
                              SetSCR MJump                        

                |  8  -> // jump unconditional
                         // S:=M
                         // Q affected (920A only)
                         // M is always relative
                         let t = int64 timing.[11]
                         cpuTime     <- cpuTime + t
                         elapsedTime <- elapsedTime + t
                         if   machineType = E920a 
                         then qRegister <- I ()
                         SetSCR MJump
                        
                |  9  -> // jump if negative
                         // if A<0 then S:=M; 
                         // 920A, 920B Q affected, 920M, 920C not affected
                         // M is always relative
                         match machineType with 
                         | E920a  -> qRegister <- I ()
                         | E920b  
                         | E920m  -> qRegister <- N
                         | _      -> ()
                         if   accumulator < bit18 
                         then let t = int64 timing.[12]
                              cpuTime     <- cpuTime + t
                              elapsedTime <- elapsedTime + t     
                              adjust modifyTime
                         else let t = int64 timing.[13]
                              cpuTime     <- cpuTime + t
                              elapsedTime <- elapsedTime + t
                              SetSCR MJump

                | 10  -> // count in store
                         // m:=m+1
                         let t = int64 timing.[14]
                         cpuTime     <- cpuTime +  t                        
                         elapsedTime <- elapsedTime + t
                         memory.[M] <- ((ReadMem M) + 1) &&& mask18

                | 11  -> // store Sequence Control Register
                         // m[13..1]:=(S+1)[13..1]; Q[17..14]:=(S+1)[17..14]; Q[13..1]:=0
                         // S[16..14] for machines before 920C
                         // 920A Q:=S
                         let t = int64 timing.[15]
                         cpuTime     <- cpuTime + t
                         elapsedTime <- elapsedTime + t
                         qRegister <-
                             match machineType with
                             | E920a -> sequenceControlRegister
                             | E900
                             | E920b
                             | E920m -> sequenceControlRegister &&& aModuleMask
                             | E920c -> sequenceControlRegister &&& cModuleMask
                         WriteMem M (sequenceControlRegister &&& operandMask)

                | 12  -> // fixed point multiply 
                         // (A,Q[18..2]):=A*m; Q1:=1 if A<0 otherwise 0
                         // this code fully emulates 900 series microcode implementation
                         let t = int64 timing.[16]
                         cpuTime     <- cpuTime + t
                         elapsedTime <- elapsedTime + t
                         let m = ReadMem M
                         for processCounter = 1 to 18 do
                            let xBits =
                                if   processCounter = 1
                                then qRegister <- accumulator
                                     accumulator <- 0
                                     qRegister <<< 1
                                else let x = qRegister
                                     aqShiftRight() 
                                     x                                      
                            match (xBits &&& 3) with
                            | 1  -> accumulator <- (accumulator + m) &&& mask18
                            | 2  -> accumulator <- (accumulator - m) &&& mask18
                            | _  -> ()
                         if   m = bit18 && accumulator <> 0
                         then // correct for using 18 bits where hardware uses 19 bits
                              // (See T.J. Froggat "The Bug in SIM900 Multiply")
                              accumulator <- bit19 - accumulator
                        
                | 13  -> // divide
                         // A:=(A,Q[18..2])/m  +/- 2^-17; Q[18..2]:=A +/- 2^-17; A[1]:=1; Q[1]:=0
                         // this code fully emulates 900 series microcode implementation
                         let t = int64 timing.[17]
                         cpuTime     <- cpuTime + t
                         elapsedTime <- elapsedTime + t
                         let m = ReadMem M
                         qRegister <- (qRegister &&& not1) // clear out bottom bit of Q
                         let mutable xBits = accumulator
                         for step = 1 to 18 do
                            if (xBits >= bit18) = (m >= bit18)
                            then qRegister <- qRegister + bit1
                                 accumulator <- (accumulator - m) &&& mask18
                            else accumulator <- (accumulator + m) &&& mask18
                            xBits <- accumulator
                            aqShiftLeft()
                         accumulator <- qRegister + bit1
                                
                | 14  -> // shift, i/o
                         // (A,q) := ((A, Q) + Q[1]) * 2^Z left shift, 2^8192-Z right shift
                         // Or block transfer
                         let Z = M &&& operandMask
                         let leftShift Z =
                             for step = 1 to (int Z) do aqShiftLeft ()                              
                             let t = int64 (timing.[18] + 
                                       timing.[19] * (int Z))
                             cpuTime     <- cpuTime + t
                             elapsedTime <- elapsedTime + t
                         let rightShift Z =
                             for step = (int Z) to 8191 do aqShiftRight ()                              
                             let t = int64 (timing.[18] + 
                                       timing.[19] * (8192-(int Z)))
                             cpuTime     <- cpuTime + t
                             elapsedTime <- elapsedTime + t
                         match (N, machineType) with
                         | (_, E900)  when Z <= 2047 -> leftShift Z     
                         | (_, E900)  when Z >= 6144 -> rightShift Z
                         | (_, E920b) when Z <= 2047 -> leftShift Z     
                         | (_, E920b) when Z >= 6144 -> rightShift Z
                         | (_, E920c) when Z <=   36 -> leftShift Z     
                         | (_, E920c) when Z >= 8156 -> rightShift Z 
                         | (_, E920a) when Z <= 4095 -> leftShift (Z &&& mask12)  
                         | (_, E920a) when Z >= 4096 -> rightShift Z                       
                         | (_, E920m) when Z <= 2047 -> let z = Z &&& mask6
                                                        leftShift (if z <= 48 then z else z-16) 
                         | (_, E920m) when Z >= 6144 -> let z = (Z&&&mask6)
                                                        let x = 64-z
                                                        rightShift (if x <= 48 then 8192-x else 8192-48-z)
                         | (5120, E920b)             -> // write a block to magnetic tape
                                                        let q12 = qRegister &&& mask12
                                                        let cpu = int64 (timing.[22]+q12*memorySpeed*10)
                                                        cpuTime <- cpuTime+cpu
                                                        accumulator <- MTWriteBlock accumulator q12
                         | (3072, E920b)             -> // read a block from magnetic tape
                                                        let q12 = qRegister &&& mask12
                                                        let cpu = int64 (timing.[22]+(q12*memorySpeed*10))
                                                        cpuTime <- cpuTime+cpu
                                                        accumulator <-  MTReadBlock accumulator qRegister
                         | (4864, E920b) 
                         | (4864, E900)              -> // output block to plotter
                                                        pRegister <- Z
                                                        let cpu = 330L // this time comes from 903 Fact Book
                                                        cpuTime   <- cpuTime + cpu
                                                        let ioTime = elapsedTime + cpu
                                                        for addr = accumulator to accumulator+(qRegister&&&mask12)-1 do
                                                            let data = ReadMem addr
                                                            if   ioTime < pltTime
                                                            then // need to wait for device
                                                                  elapsedTime <- pltTime
                                                                  pltTime <- pltTime + (PlotTime word)                                                                      
                                                            else // device is ready
                                                                  pltTime <- ioTime + (PlotTime word)
                                                                  elapsedTime <- ioTime
                                                                  PutPlotter word
                         | (5697, E920b)             -> // line printer output data, packed 
                                                        let q12 = qRegister &&& mask12                        
                                                        let cpu = int64 (timing.[18]+q12*memorySpeed*10)
                                                        cpuTime <- cpuTime+cpu
                                                        elapsedTime <- elapsedTime+cpu
                                                        let count = q12-1 // first word in buffer unused
                                                        let buffer = Array.zeroCreate count
                                                        for i=0 to count-1 do buffer.[i] <- ReadMem (accumulator+i+1)
                                                        LPTransfer buffer                                                            
                         | (_, _)                    -> BadInstruction 14 Z                   
                             
                | 15  -> // input/output
                         let Z = M &&& operandMask
                         match  (machineType, Z) with
                         | (_,     2048) 
                         | (E920a, _   ) when Z <= 4095
                                             ->  // input from paper tape
                                                 Reader Z

                         | (E920b,     1024) ->  // read a word from mag tape
                                                 let cpu = int64 timing.[22]
                                                 cpuTime <- cpuTime+cpu
                                                 accumulator <- MTReadWord ()

                         | (E920b,     1025) -> // mag tape status word
                                                let cpu = int64 timing.[22]
                                                cpuTime <- cpuTime + cpu
                                                accumulator <- MTStatus ()                                    

                         | (E920b,     1536) -> // card reader get character
                                                let cpu = int64 timing.[22]
                                                cpuTime <- cpuTime + cpu
                                                elapsedTime <- elapsedTime+cpu
                                                accumulator <- CRReadData ()

                         | (E920b,     1568) -> // read card reader status
                                                let cpu = int64 timing.[22]
                                                cpuTime <- cpuTime + cpu
                                                elapsedTime <- elapsedTime+cpu
                                                accumulator <- CRStatus ()

                         | (E920b,     1569) -> // read line printer status
                                                let cpu = int64 timing.[22]
                                                cpuTime <- cpuTime + cpu
                                                elapsedTime <- elapsedTime+cpu 
                                                accumulator <- LPStatus ()

                         | (E920b,     1600) -> // read 4100 IMU status
                                                let cpu = int64 timing.[22]
                                                cpuTime <- cpuTime + cpu
                                                elapsedTime <- elapsedTime+cpu                                                 
                                                accumulator <- IMUStatus ()

                         | (E920b,     2049)
                         | (E920c,     2049) -> // read paper tape station status word
                                                pRegister <- Z
                                                let cpu = int64 timing.[22]
                                                cpuTime     <- cpuTime + cpu
                                                elapsedTime <- elapsedTime + cpu
                                                accumulator <- 
                                                    if   elapsedTime >= ptrTime
                                                    then 1
                                                    else 0 
                                                accumulator <- accumulator +
                                                    if   elapsedTime >= ptpTime
                                                    then 2
                                                    else 0
                                                accumulator <- accumulator +
                                                    if   elapsedTime >= ttyTime 
                                                    then if   TTYInputReady () 
                                                         then 12 
                                                         else 8
                                                    else 0

                         // | (E920a,     2052)     // Non-standard, to support Aldenham modified 920A                      
                         // | (E920b,     2052)
                         // | (E920c,     2052) 
                         // | (E920m,     2052)
                         // | (E900,      2052) 
                         | (_,         2052) ->  TTYIn Z

                         | (E920b,     5120) ->  // write a word to mag tape
                                                 let cpu = int64 timing.[22]
                                                 cpuTime <- cpuTime+cpu
                                                 MTWriteWord accumulator

                         | (E920b,     5121) ->  // output mag tape control word
                                                 let cpu = int64 timing.[22]
                                                 cpuTime <- cpuTime+cpu
                                                 elapsedTime <- elapsedTime+cpu
                                                 MTControl accumulator

                         | (E920b,     5122) ->  // close mag tape block
                                                 let cpu = int64 timing.[22]
                                                 cpuTime <- cpuTime+cpu
                                                 MTCloseBlock () 

                         | (E920b,     5664) ->  // output card reader control word
                                                 let cpu = int64 timing.[22]
                                                 cpuTime <- cpuTime + cpu
                                                 elapsedTime <- elapsedTime+cpu
                                                 CRControl accumulator

                         | (E920b,     5665) ->  // output line printer control word
                                                 let cpu = int64 timing.[22]
                                                 cpuTime <- cpuTime + cpu
                                                 elapsedTime <- elapsedTime+cpu
                                                 LPControl accumulator  
                                                 
                         | (E920b,     6016) ->  // disable multiplexor
                                                 let cpu = int64 timing.[22]
                                                 cpuTime <- cpuTime + cpu
                                                 elapsedTime <- elapsedTime+cpu
                                                 muxGroupA <- false; muxGroupB <- false
                                                 
                         | (e920b,     6017) ->  // enable A disable B
                                                 let cpu = int64 timing.[22]
                                                 cpuTime <- cpuTime + cpu
                                                 elapsedTime <- elapsedTime+cpu
                                                 muxGroupA <- true; muxGroupB <- false                                                       
                                                 
                         | (E920b,     6018) ->  // disable A enable B
                                                 let cpu = int64 timing.[22]
                                                 cpuTime <- cpuTime + cpu
                                                 elapsedTime <- elapsedTime+cpu
                                                 muxGroupA <- false; muxGroupB <- true                                                      
                                                 
                         | (E920b,     6019) ->  // enable multiplexor
                                                 let cpu = int64 timing.[22]
                                                 cpuTime <- cpuTime + cpu
                                                 elapsedTime <- elapsedTime+cpu
                                                 muxGroupA <- true; muxGroupB <- true                                                     

                         | (_,         6144) ->  // output to paper tape  
                                                 Punch Z

                         | (E920b,     6145)
                         | (E920c,     6145) ->  // output paper tape control word
                                                 let cpu = int64 timing.[22]
                                                 cpuTime     <- cpuTime + cpu
                                                 elapsedTime <- elapsedTime + cpu
                                                 holdUp <- accumulator = 0

                         //| (E920a,   6148)    
                         //| (E920b,   6148) 
                         //| (E920m,   6148)
                         //| (E920c,   6148)
                         //| (E900,    6148) 
                         | (_,         6148) -> // output to teletype
                                                TTYOut Z
                         
                         | (E920c,     7169) -> // test standardized: 
                                                // skip next instruction if A > 0.5 or A < -0.5 or A = 0
                                                if   accumulator = 0 || (accumulator &&& bit17) <> 0 
                                                then let t = int64 timing.[26]
                                                     cpuTime <- cpuTime + t
                                                     elapsedTime <- elapsedTime + t
                                                     SetSCR (sequenceControlRegister+1)
                                                else let t = int64 timing.[25]
                                                     cpuTime <- cpuTime + t
                                                     elapsedTime <- elapsedTime + t
                               
                         | (E920c,     7170) -> // increment and skip
                                                // B := B+1; skip next instruction if B[13..1] = 0
                                                let inc = (memory.[bRegisterAddr] + 1) &&& mask18
                                                memory.[int bRegisterAddr] <- inc
                                                if   inc &&& mask13 = 0 
                                                then let t = int64 timing.[28]
                                                     cpuTime <- cpuTime + t
                                                     elapsedTime <- elapsedTime + t
                                                     SetSCR (sequenceControlRegister+1)
                                                else let t = int64 timing.[27]
                                                     cpuTime <- cpuTime + t
                                                     elapsedTime <- elapsedTime + t

                         | (E920c,     7171) -> // read word generator
                                                let t = int64 timing.[29]
                                                cpuTime <- cpuTime + t
                                                elapsedTime <- elapsedTime + t
                                                accumulator <- wordGenerator

                         | (E920c,     7172) -> // A to Q; Q[18..2] := A[17..1]
                                                let t = int64 timing.[30]
                                                cpuTime <- cpuTime + t
                                                elapsedTime <- elapsedTime + t
                                                qRegister <- (accumulator <<< 1) &&& mask18
                               
                         | (E920c,     7173) -> // Q to A; A[17..1] := Q[18..2]
                                                let t = int64 timing.[31]
                                                cpuTime <- cpuTime + t
                                                elapsedTime <- elapsedTime + t
                                                accumulator <- (qRegister >>> 1) 
                               
                         | (E920c,     7174) -> // A to B: B := A
                                                let t = int64 timing.[32]
                                                cpuTime <- cpuTime + t
                                                elapsedTime <- elapsedTime + t
                                                memory.[int bRegisterAddr] <- accumulator
                               
                         | (E920c,     7175) -> // B to A; A := B
                                                let t = int64 timing.[33]
                                                cpuTime <- cpuTime + t
                                                elapsedTime <- elapsedTime + t
                                                accumulator <- memory.[int bRegisterAddr]
                               
                         | (E920c,     7176) -> // Set relative addressing
                                                let t = int64 timing.[34]
                                                cpuTime <- cpuTime + t
                                                elapsedTime <- elapsedTime + t
                                                relative <- 0
                                                SaveSCRH ()
                               
                         | (E920c,     7177) -> // Set absolute addressing
                                                let t = int64 timing.[35]
                                                cpuTime <- cpuTime + t
                                                elapsedTime <- elapsedTime + t
                                                relative <- bit18
                                                SaveSCRH ()
                                                DisableInitialInstructions ()

                         | (E920b, _) when 7184 <= Z -> // Machine stop
                                                stopped <- true
                                                raise (Machine (sprintf "Stopped by 15 %d" Z)) 

                         | (_, _) when 7168 <= Z -> // Program terminate
                                                let t = int64 timing.[24]
                                                cpuTime <- cpuTime + t
                                                elapsedTime <- elapsedTime + t
                                                ExitLevel ()
                                                                                       
                         | (E900,      4864)
                         | (E920b,     4864) -> // output code to plotter
                                                pRegister <- Z
                                                let cpu = 330L // this time comes from 903 Fact Book
                                                cpuTime   <- cpuTime + cpu
                                                let ioTime = elapsedTime + cpu
                                                if   ioTime < pltTime
                                                then // need to wait for device
                                                      elapsedTime <- pltTime
                                                      pltTime <- pltTime + (PlotTime accumulator)                                                                      
                                                else // device is ready
                                                      pltTime <- ioTime + (PlotTime accumulator)
                                                      elapsedTime <- ioTime
                                                PutPlotter accumulator

                         | (E900,      0123) -> // invented instruction due to Don Hunter, 
                                                // prints date and time on console
                                                let dt = System.DateTime.Now
                                                let str = sprintf "\n%s %s\n" (dt.ToLongDateString ()) (dt.ToLongTimeString ())
                                                for ch in str do PutTTYChar (TelecodeOf T900 ch)                           
                                  
                         | (E900,      4865) -> // initialize plotter X coord 
                                                // (this is an invented instruction used by the plotter library for  
                                                // the Ada version of the simulator written by Don Hunter)
                                                PlotterSetX accumulator
                         
                         | (E900,      4866) -> // initialize plotter Y coord (also an invented instruction)
                                                PlotterSetY accumulator 

                         | (_,         _)    -> Bad15Instruction Z 

                | _   -> failwith "instruction code not in range 0..15 - shouldn't happen"     
    
    open MachineStateHelper 
     
    // DEBUGGING FACILITIES  

    let AlgolOff () = 
        algolTracing <- false
        CheckForStrobe ()

    let AlgolOn ()  = 
        let rec Helper n = // look for NXPORD in interpreter
            if    n >= 4000
            then raise(Machine "NXPORD not found")
            elif (memory.[n]   = 135) &&
                 (memory.[n+1] = (bit18+bit16)) &&
                 (memory.[n+2] = (bit17+bit15+135))
            then // found NXPORD sequence
                 n+2
            else Helper (n+1)
        nxpordAddr <- Helper 8
        algolTracing <- true
        strobe <- true

    let MonitorOn (m: monitor) = // add a monitor, merging with any pre-existing monitor for same address
        let found, regions = monitors.TryGetValue m.addr
        if   found
        then // merge regions
             monitors.Remove m.addr |> ignore
             monitors.[m.addr] <- List.append regions m.regions
        else monitors.[m.addr] <- m.regions
        strobe <- true  
        
    let MonitorOff addr = 
        if   not (monitors.Remove addr)
        then raise (Machine (sprintf "Monitor at %d not set" addr))
        else CheckForStrobe ()

    let MonitorOffAll () = 
        monitors.Clear ()
        CheckForStrobe ()

    let Monitors () = 
        let k = monitors.Keys 
        let v = monitors.Values
        let z = Seq.zip k v
        z

    let Breakpoints () = breakpoints

    let BreakpointOn  addr =
        breakpoints.Remove addr |> ignore // avoid duplicates 
        breakpoints.Add addr
        strobe <- true

    let BreakpointOff addr = 
        if   not (breakpoints.Remove addr)
        then raise (Machine (sprintf "Breakpoint at %d not set" addr))
        else CheckForStrobe ()

    let BreakpointOffAll () =
        breakpoints.Clear ()
        CheckForStrobe ()

    let LoggingOn () =
        if   LogFileOpen ()
        then logging <- true
             strobe  <- true

    let LoggingOff () =
        logging <- false
        CheckForStrobe ()

    let Steps count  = 
        stepCount <- count
        strobe <- true

    let TraceRegion start finish =
        traceStart  <- start
        traceFinish <- finish

    let TraceOn level = 
        tracing <- true 
        strobe <- true
        if   level = 0
        then for i = 1 to 4 do traceLevel.[i] <- true
        else traceLevel.[level] <- true

    let TraceOff level =
        tracing <- false
        if   level = 0
        then for i = 1 to 4 do traceLevel.[i] <- false
             tracing <- false
        else traceLevel.[level] <- false
             for i = 1 to 4 do tracing <- tracing || traceLevel.[i]
        CheckForStrobe ()
        
    // ACCESS REGISTERS
    let AGet ()     = accumulator 
    let APut value  = accumulator <- value &&& mask18
    let QGet ()     = qRegister 
    let QPut value  = qRegister   <- value &&& mask18
    let BGet ()     = memory.[bRegisterAddr] 
    let BPut value  = memory.[bRegisterAddr] <- value &&& mask18
    let SGet        = GetSCR
    let OldSGet ()  = oldSequenceControlRegister
    let SPut value  = SetSCR value 
    let RelGet ()   = relative = 0

    // ACCESS MEMORY     
    
    let ReadStore = ReadMem
    
    let WriteStore = WriteMem       
         
    let ClearStore () = // clear entire store to zero
        for i = 0 to memorySize-1 do memory.[i] <- 0

    let ClearModule address =
        let startAddress = ((int address) / 8192) * 8192  
        if startAddress < memorySize
        then for i = startAddress to startAddress+8191 do memory.[i] <- 0 

    // Image files consist of raw bytes, 4 per word in little endian order, starting from location 8

    // DUMP IMAGE
    let DumpImage count  = 
        let maxAddr = count-1
        ReadMem (maxAddr) |> ignore
        let bytes: byte[] = Array.zeroCreate ((count-8)*4)
        for i = 8 to count-1 do // don't dump words 0-7
            let iv = (i-8)*4
            let word = memory.[i]
            bytes.[iv]   <- byte   word
            bytes.[iv+1] <- byte ((word >>>  8) &&& mask8)
            bytes.[iv+2] <- byte  (word >>> 16)
            // bytes.[iv+3] <- 0
        bytes          

    // LOAD IMAGE
    let LoadImage (bytes: byte[]) =
        let maxAddr = 8+bytes.Length/4-1
        ReadMem maxAddr |> ignore // ensure with maxMemory
        for i = 0 to maxAddr-8 do
        let iv = i*4
        memory.[i+8] <- (int bytes.[iv]) ||| ((int bytes.[iv+1]) <<< 8) ||| ((int bytes.[iv+2]) <<< 16) 

    let VerifyImage (bytes: byte[]) =
        if (bytes.Length+8*4) % (8192*4) <> 0 then raise (Machine "Not an image file (byte count not a multiple of 32768)")
        let maxAddr = bytes.Length / 4 - 1 + 8
        ReadMem (maxAddr) |> ignore // ensure with maxMemory
        let rec Scan i errs =
            let addr = i+8
            let iv   = i*4
            if   iv < bytes.Length
            then let word = (int bytes.[iv]) ||| ((int bytes.[iv+1]) <<< 8) ||| ((int bytes.[iv+2]) <<< 16) 
                 if   word <> (ReadMem addr) && (8180 > addr || 8191 < addr) // ignore initial instructions
                 then AddressPut addr; stdout.WriteLine ()
                      stdout.Write "Memory"; WordPut memory.[addr]; stdout.WriteLine ()
                      stdout.Write "File  "; WordPut word;          stdout.WriteLine ()
                      if   errs < 50
                      then Scan (i+1) (errs+1)
                      else raise (Machine "Abandoned after 50 differences detected")
                 else Scan (i+1) errs
        Scan 0 0

    // LOAD MODULE       
    let LoadModule moduleNo (words: int[]) =
        let index = moduleNo * 8192
        let maxAddr = words.Length-1
        ReadMem (moduleNo + maxAddr) |> ignore
        for i = 0 to maxAddr do memory.[index+i] <- words.[i]        
             
    // RESTART after STOP         
    let Restart tracePut monitorPut addr = // keep executing instructions until SCR = addr (or loop stop)  
        if not stopped then NotStoppedError ()
        traceBufPtr <- 0
        stopped  <- false
        reset    <- false
        stopAddr <- addr
        if stopAddr >= 0 then strobe <- true
        try
            realTimer.Start ()
            while not stopped do
                // Handle interrupts if not protected
                // (Protect is set to stop an interrupt intruding between 0 and following instruction) 
                if   takeInterrupt
                then if not protect
                     then takeInterrupt <- false
                          EnterLevel (HighestActiveLevel ())
                          if tracing then printfn "INTERRUPT (%d)" interruptLevel
                          // update timers
                          let intTime = (int64 timing.[23])
                          cpuTime <- cpuTime + intTime
                          elapsedTime <- elapsedTime + intTime 
                          // re-enable initial instructions if going to level 1
                // clear interrupt protection
                protect <- false
               
                let oldLevel = interruptLevel // 15 7168 might change the interrupt level

                // SCR is incremented after instruction fetch, before decode
                AdvanceSCR ()
                try
                    Execute (ReadMem (oldSequenceControlRegister))
                with
                | exn -> stopped <- true 
                         raise exn
            
                // increment instruction count
                iCount <- iCount+1L
                
                // update instruction trace     
                traceBuffer.[traceBufPtr] <- {scr=oldSequenceControlRegister; acc=accumulator}
                traceBufPtr <- (traceBufPtr+1) % traceBufLen   
                
                // check for any strobes (breakpoints etc)
                if   strobe
                then YieldToDevices ()
                     if   logging
                     then Log (fun () -> TracePut oldLevel oldSequenceControlRegister 
                                                     (ReadStore oldSequenceControlRegister)
                                                      accumulator qRegister memory.[bRegisterAddr])
                     if   tracing 
                     then if traceLevel.[oldLevel] && (traceStart < 0 
                                                   || (traceStart <= oldSequenceControlRegister 
                                                   && oldSequenceControlRegister <= traceFinish))
                          then tracePut oldLevel oldSequenceControlRegister 
                                             (ReadStore oldSequenceControlRegister)
                                                accumulator qRegister memory.[bRegisterAddr]

                     if   algolTracing && sequenceControlRegister = nxpordAddr
                     then let pp = ReadStore 135
                          algolPut pp (ReadStore pp)

                     if watch
                     then YieldToDevices ()
                          watch <- false
                          stopped <- true
                          raise Watch 
                     let found, regions = monitors.TryGetValue oldSequenceControlRegister
                     if   found
                     then YieldToDevices ()
                          monitorPut {addr=oldSequenceControlRegister; regions=regions}
                     if   breakpoints.Contains oldSequenceControlRegister
                     then YieldToDevices ()
                          stopped <- true
                          raise Break // hit breakpoint
                     if   stepCount > 0 // step count is -1 if not set
                     then stepCount <- stepCount - 1
                     if   stepCount = 0 
                     then YieldToDevices ()
                          stepCount <- -1
                          stopped <- true
                          raise StopLimit // step count reached
                     if   oldSequenceControlRegister = stopAddr // after Restart addr
                     then YieldToDevices ()
                          stopped <- true
                          raise StopAddr
                     if   lpTime > 0L && lpTime <= elapsedTime
                     then LPInterruptCheck ()  
                     if   crTime > 0L && crTime <= elapsedTime
                     then CRInterruptCheck ()
                     if   mtIntTime > 0L && mtIntTime <= elapsedTime 
                     then mtTime    <- mtIntTime+limitTime
                          mtIntTime <- 0L
                          InterruptOn 2 //; printfn "MT Interrupt at %d" elapsedTime
                elif iCount % 5000L = 0L
                then // give i/o a chance to intervene
                     YieldToDevices ()
                
                if   interruptLevel = oldLevel && sequenceControlRegister = oldSequenceControlRegister 
                then if   lpTime = 0L && crTime = 0L && mtIntTime = 0L && not takeInterrupt // let asynchronous activity complete
                     then YieldToDevices ()
                          stopped <- true
                          raise LoopStop

                SlowDown ()

        finally realTimer.Stop ()  
                YieldToDevices ()        
        
    // JUMP START EXECUTION 
    
    let JumpInit () =
       relative        <- 0
       scrAddr         <- 0
       bRegisterAddr   <- 1
       interruptLevel  <- 1  
       levelActive.[1] <- true
       EnableInitialInstructions ()  
                  
    let JumpToAddr tracePut monitorPut address =
        // JUMP forces level 1 on 920A, 920B & 920M
        if address < 0 || address > 8191 then raise (Machine "Jump address not in range 0-8191")
        TraceBufferClear () 
        SetSCR address
        SaveSCRH ()
        Restart tracePut monitorPut -1 
        
    let Jump tracePut monitorPut = 
        if machineType <> E920c then JumpInit ()
        JumpToAddr tracePut monitorPut (wordGenerator &&& mask13)
                  
    let JumpII tracePut monitorPut = 
        if machineType <> E920c
        then raise (Machine ("JUMP II only available for 920C"))
        else JumpInit () 
             JumpToAddr tracePut monitorPut 8181
            
    // GENERATE A MANUAL INTERRUPT      
    let ManualInterrupt level = // Signal a manual interrupt
        LevelCheck level
        interruptTrace.[level] <- false // manual and trace interrupts are mutually exclusive
        InterruptOn level

    // EXECUTE SINGLE INSTRUCTION
    let Obey () = // Execute one instruction from word generator
        if not stopped then NotStoppedError ()
        try Execute wordGenerator finally stopped <- true

    // MACHINE RESET
    let Reset () =    
        accumulator     <- 0       
        qRegister       <- 0       
        bRegisterAddr   <- 1       
        scrAddr         <- 0      
        iRegister       <- 0       
        pRegister       <- 0       
        relative        <- 0
        interruptLevel  <- 1         
        takeInterrupt   <- false        
        protect         <- false 
        reset           <- true
        stopped         <- true  
        holdUp          <- true
        ResetMux ()
        ResetIMU ()
        ResetLP  ()
        ResetCR  ()
        ResetMT  ()
        for i = 0 to 4 do
            levelActive.[i]      <- false
            interruptPending.[i] <- false
            interruptTrace.[i]   <- false
        levelActive.[1] <- true
        EnableInitialInstructions ()
   
    // STOP execution
    let Stop () =
        stopped <- true

    // SPEED
    let Slow () = 
        slow <- true
        ResetTimes ()

    let Fast () = 
        slow <- false
        ResetTimes ()
        
    // TIDYUP
    let TidyUpMachine () =
        slow <- false
        Reset ()
        watchLoc <- -1
        iCount <- 0L
        stepCount <- -1   
        TraceOff 0
        TraceRegion -1 0
        BreakpointOffAll ()   
        MonitorOffAll ()                            
        ResetTimes ()
        SelectInput  <- AutoIn
        SelectOutput <- AutoOut
        TidyUpMT ()
        algolTracing <- false
        
    // TIMING INFO
    let Times () = 
        let pcTime = realTimer.ElapsedMilliseconds
        let ct = cpuTime
        let et = Elapsed ()
        let ic = iCount
        ResetTimes ()
        (ct, et, pcTime, machineName, ic)     
        
    // TRACE BUFFER
    let TraceBuffer () =
        printfn("TraceBuffer")
        Array.append traceBuffer.[traceBufPtr..traceBufLen-1] traceBuffer.[0..traceBufPtr-1]   
            |> Array.filter (fun (t: TraceRec) -> t.scr <> -1) 
                        
    // TRACE INTERRUPTS
    let TraceInterruptOn level =
        LevelCheck level
        interruptTrace.[level] <- true
        InterruptOn level

    let TraceInterruptOff level =
        LevelCheck level
        interruptTrace.[level] <- false
        
    // WORD GENERATOR (control panel keys)    
    let WordGeneratorGet () = wordGenerator 
         
    let WordGeneratorPut value = 
        wordGenerator <- value &&& mask18

    // PAPER TAPE STATION
    let InputSelectReader ()       = SelectInput  <- ReaderIn
    let InputSelectAuto ()         = SelectInput  <- AutoIn
    let InputSelectTeleprinter ()  = SelectInput  <- TeleprinterIn
    let OutputSelectPunch ()       = SelectOutput <- PunchOut
    let OutputSelectAuto ()        = SelectOutput <- AutoOut
    let OutputSelectTeleprinter () = SelectOutput <- TeleprinterOut

    // Memory watch
    let WatchOn loc = 
        watchLoc <- loc
        strobe <- true

    let WatchOff () = 
        watchLoc <- -1
        CheckForStrobe ()

    // MAGNETIC TAPE
    let MTMount hdlr fileName wp = 
        // Attach command for MT - open file
        MTCheckHandler hdlr
        match mtHandler.[hdlr] with
        | Some (h)  ->  h.tape.Close () // close any previous tape
        | None      -> ()
        mtHandler.[hdlr] <- Some {
            tape=NewTape (fileName, wp); 
            manual=false; busyUntil=0L; missedTransfer=false; zeroCharacter=false;
            shortTransfer=false; longTransfer=false; doneNothing=false ; parityError=false;
            }

    let MTUnmount hdlr =
        // Detach command for MT - close file 
        MTCheckHandler hdlr
        match mtHandler.[hdlr] with
        | Some (h)  ->  h.tape.Close ()
                        mtHandler.[hdlr] <- None
        | None      ->  NoTape hdlr

        
    let CloseMT = TidyUpMT

