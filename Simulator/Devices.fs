#light

module Sim900.Devices

// DEVICES
// The Elliott 900 series were essentially paper tape machines.  The basic
// system had a paper tape reader and punch.  There was an option for connecting
// a teleprinter on machines after the 920A.  As a machine designed for the
// embedded systems market there was provision to add interfaces to a wide variety
// of other devices including line printers, magnetic tape drives and graph 
// plotters.
// 
// The simulator supports seven i/o devices: magenetic tape unit, line printer, card reader, 
// digital graph plotter, paper tape reader, paper tape punch and teletype.
//
// (The plotter is driven in one of 2 modes: if the machine type is "900" it assumes DGNH's
// scheme for plotting to a VGA screen, used in the HUNTER ALGOL demonstrations.  For all 
// other machine types plotting to a 34cm Benson-Lehner plotter is assumed with a 0.005"
// step size.
//  
// Reader input can be directed to teletype and vice versa.
// Punch output can be directed to teletype and vice versa.
    
    open System
    open System.IO
    open System.Drawing
    open System.Windows.Forms
    open System.Collections
    open System.Text
    open Sim900.Bits
    open Sim900.Telecodes
    open Sim900.Models
    
    exception Device of string
    exception CRManual          // attempt to use card reader when no file attached
    exception LPManual          // attempt to use line printer when detached (i.e., offline)

    let YieldToDevices () =     // Allow other threads to run
        System.Threading.Thread.Yield () |> ignore

    // provide a dummy context to represent console "form"
    let  dummyForm  = new System.Windows.Forms.Form(Visible=false)
    // Capture the synchronization context of the hosting user interface thread
    // in order to automatically re-route events onto that thread.
    let context = System.Threading.SynchronizationContext.Current
    do assert (context <> null)

    // Event signalling
    let triggerEvent     (e: Event<_>) args = context.Post((fun _ -> e.Trigger args), null)  // send event asynchronously
    let triggerEventSend (e: Event<_>) args = context.Send((fun _ -> e.Trigger args), null)  // send event synchronously
     
    // PAPER TAPE READER                               
    module private PaperTapeReader =

        let mutable tapeIn: byte[] option = None 
        let mutable tapeInPos = 0  

    open PaperTapeReader    
            
    let OpenReaderBinaryString text rdrMode = 
        // take binary format input from command stream
        tapeIn <- Some (TranslateFromBinary text rdrMode)                
        tapeInPos <- 0    
            
    let OpenReaderBin rdrMode fileName = 
        // take binary format file for paper tape input
        let text = File.ReadAllText fileName
        OpenReaderBinaryString rdrMode text

    let OpenReaderRaw rdrMode fileName = 
        // take binary format file for paper tape input
        let bytes = File.ReadAllBytes fileName
        tapeIn <- Some (TranslateFromRaw rdrMode bytes)               
        tapeInPos <- 0

    let OpenReaderTextString teleCode rdrMode text = 
        // take text input from command stream
        tapeIn <- Some (
                        match teleCode with
                             | T900 -> TranslateFromText    T900 rdrMode text
                             | T903 -> TranslateFromText    T903 rdrMode text
                             | T920 -> TranslateFromText    T920 rdrMode text                           
                             | TACD -> TranslateFromText    TACD rdrMode text
                             | TTXT -> TranslateFromText    TTXT rdrMode text) 
        tapeInPos <- 0 
        
    let OpenReaderText teleCode rdrMode fileName =
        // use text file for paper tape input
        let text = File.ReadAllText fileName
        OpenReaderTextString teleCode rdrMode text
                 
    let GetReaderChar () = // get a character from the paper tape reader
        let ti =
            match tapeIn with
            | Some ti   -> ti
            | _         -> raise (Device "No input attached to tape reader")
        if   tapeInPos >= ti.Length
        then raise (Device "Run off end of paper tape input")
        else let code = ti.[tapeInPos]
             tapeInPos <- tapeInPos+1
             code
  
    let RewindReader () =
        match tapeIn with
        | Some ti   ->  tapeInPos <- 0
        | _         ->  raise (Device "No paper tape input to rewind")

    let SkipReader () = 
        // skip over e.g., legible header by scanning to next non-blank then looking for 20 blanks
        let blanks = 20
        let rec SkipBlanks ()    = if GetReaderChar () =  0uy then SkipBlanks ()
        let rec SkipNonBlanks () = if GetReaderChar () <> 0uy then SkipNonBlanks ()
        let rec FindBlanks n     = 
            if GetReaderChar () =  0uy
            then if n > 0 
                 then FindBlanks (n-1) 
            else SkipNonBlanks (); FindBlanks blanks
        SkipBlanks ()
        SkipNonBlanks ()
        FindBlanks blanks

    let CloseReader () = 
        // Close tape reader - clear buffer and reset character position
        tapeIn <- None; tapeInPos <- 0     


    // PAPER TAPE PUNCH

    // Punch output modes       
    type PunchModes =
        | PACD
        | P900
        | P903
        | P920
        | PTXT
        | PBin
        | PRaw
        | PLegible

    type Encoding =
        | Binary of ReaderModes
        | Text   of Telecodes

    module private PaperTapePunch =

        let mutable punchStream: StreamWriter option = None
        let mutable punchMode      = P900
        let mutable punchOutPos    = 0
        let mutable lastPunchCode  = 0uy  // last code punched
        let mutable lastPunchCount = 0    // count of how many times last code punched

     open PaperTapePunch
        
    let PutPunchChar (code: byte) = // output a character to the punch
        match (punchStream, punchMode) with
        | (Some (sw), P900)  -> sw.Write (UTFOf T900 code)     // output as UTF character
        | (Some (sw), P903)  -> sw.Write (UTFOf T903 code)     // output as UTF character
        | (Some (sw), P920)  -> sw.Write (UTFOf T920 code)     // output as UTF character
        | (Some (sw), PBin)  -> sw.Write (sprintf "%4d" code)  // output as a number, 20 per line
                                punchOutPos <- (punchOutPos+1)%20
                                if punchOutPos = 0 then sw.WriteLine ()
        | (Some (sw), PACD)  -> sw.Write (UTFOf TACD code)     // output as UTF character
        | (Some (sw), PTXT)  -> sw.Write (UTFOf TTXT code)     // output as ASCII character
        | (Some (sw), PRaw)  -> sw.BaseStream.WriteByte code   // output as raw byte
        | (Some (sw), PLegible)                                // output as legible image
                             -> sw.WriteLine (LegibleOf code) 
        | (None, _)          -> raise (Device (sprintf "No file attached to punch"))
        if      code = lastPunchCode
        then    if lastPunchCount = 10000
                then lastPunchCount <- 0 
                     raise (Device (sprintf "Continuously punching &%03o" code))
                else lastPunchCount <- lastPunchCount+1
        else lastPunchCode  <- code
             lastPunchCount <- 1   
                         
    let ClosePunch () = 
        // close punch output file if open, otherwise does nothing.
        match punchStream with
        | Some (sw) -> if punchMode = PBin then for i=1 to 30 do PutPunchChar 0uy        
                       sw.Close ()
        | _         -> () 
        punchOutPos <- 0
        punchStream <- None

    let OpenPunchTxt (fileName: string) telecode =
        // open text file for paper tape punch output
        ClosePunch () // finalize last use, if any
        punchStream <- Some (new StreamWriter (fileName))
        punchMode <- match telecode with | T900 -> P900 | T903 -> P903 | T920 -> P920 | TACD -> PACD | TTXT -> PTXT

    let OpenPunchBin (fileName: string) = 
        // open binary format file for paper tape punch output
        ClosePunch () // finalize last use, if any
        punchStream <- Some (new StreamWriter (fileName))
        punchMode   <- PBin
        for i=1 to 20 do PutPunchChar 0uy
        
    let OpenPunchLegible (fileName: string) = 
        // open legible format file for paper tape punch output
        ClosePunch () // finalize last use, if any
        punchStream <- Some (new StreamWriter (fileName))
        punchMode   <- PLegible
        
    let OpenPunchRaw (fileName: string) = 
        // open raw byte file for paper tape punch output
        ClosePunch () // finalize last use, if any
        punchStream <- Some (new StreamWriter (fileName))
        punchMode   <- PRaw
        for i=1 to 20 do PutPunchChar 0uy       


    // TELEPRINTER 
    module private Teleprinter =
                                                      
        // Telecode
        let mutable defaultTelecode = T900
        let mutable ttyInChs        = ""                // tty characters waiting to be read
        let mutable ttyOutChs       = false             // true if characters are waiting to be rendered
        let mutable ttyPushPending  = false             // true if timer running to push tty
        let mutable ttyIn: byte[] option = None         // buffer for use when teletype input is INLINE
        let mutable ttyInPos        = 0 
        let mutable ttyTelecode     = defaultTelecode   // telecode for use when input is INLINE 
        let mutable ttyInline       = false
        let mutable ttyNewline      = true              // true if newlines passed through to simulation
        let mutable ttyReturnSeen   = false             // set true when GetTTYChar sees start of \r\n from tty input
        let mutable ttyLastChOut    = -1
        let mutable ttyLastChCnt    = 0         

        // Direct TTY output to a separate window
        type TTYWindow() as tty = 
            inherit Form() 
            let mutable ttyWindowOpen = true // set false if closed
            let textBox = new RichTextBox(Dock=DockStyle.Fill, 
                                      ContextMenu   = new ContextMenu(),
                                      Font          = new Font("Lucida Console",10.0f,FontStyle.Regular), 
                                      ForeColor     = Color.Black,
                                      AcceptsTab    = true,
                                      Multiline     = true,
                                      DetectUrls    = false,
                                      ShortcutsEnabled = false,
                                      ReadOnly      = false, // toggle this false to disable input
                                      ScrollBars    = RichTextBoxScrollBars.Vertical ) 
            let mi = new MenuItem ("Copy")                           
            
            // Text is buffered line by line to give better display performance output. 
            // The buffer is flushed when TTY input is required, or at each '\n' character.                            
            let mutable nextPos = 0 
            let buffer = new StringBuilder()
            let renderBuffer() = 
                // printfn "Render"
                if ttyWindowOpen
                then let s = buffer.ToString()
                     if   s.Length<>0 
                     then buffer.Clear() |> ignore
                          textBox.SuspendLayout()
                          textBox.AppendText s  // add text to text box
                          nextPos <- textBox.Text.Length
                          textBox.Select (nextPos, 0) // move cursor to end
                          textBox.Show ()
                          textBox.ResumeLayout()

            do mi.Click.Add (fun arg -> Clipboard.SetData(DataFormats.Rtf, textBox.SelectedRtf))
            do textBox.ContextMenu.MenuItems.Add(mi) |> ignore
            do tty.Closing.Add (fun arg -> ttyWindowOpen <- false; ())
            do tty.SetStyle (ControlStyles.AllPaintingInWmPaint ||| ControlStyles.Opaque, true)
            do tty.Controls.Add textBox // put textbox on form
            do textBox.TextChanged.Add (fun arg ->  // handle input to textbox 
                                            if   textBox.ReadOnly
                                            then // writing happened
                                                 if ttyInChs.Length = 0 then textBox.ReadOnly <- false
                                            else // must have had some input
                                                 if   nextPos < textBox.Text.Length 
                                                 then ttyInChs <- ttyInChs + textBox.Text.[nextPos..] 
                                                      textBox.ReadOnly <- true                                           
                                            nextPos  <- textBox.Text.Length
                                            textBox.Select (nextPos, 0))

            member tty.Push () =
                // printfn "tty.Push"
                while ttyOutChs do
                    ttyOutChs <- false
                    renderBuffer ()
                if ttyInChs.Length = 0 then textBox.ReadOnly <- false
            
            member tty.Write (s :string) =
                // printfn "tty.Write %s" s
                textBox.ReadOnly <- true // lock out input
                buffer.Append s |> ignore
                if   s.EndsWith "\n" 
                then ttyOutChs <- false
                     renderBuffer()
                else ttyOutChs <- true

            member tty.Open () = ttyWindowOpen

        let ensureTTYEvent     = new Event<_>() // new tty window needed
        let ttyWriteEvent      = new Event<_>() // tty output ready
        let ttyPushEvent       = new Event<_>() // simulator needs tty input

        let EnsureTTYEvent     = ensureTTYEvent.Publish        
        let TTYWriteEvent      = ttyWriteEvent.Publish
        let TTYPushEvent       = ttyPushEvent.Publish
        
        let mutable latestTTY: TTYWindow option = None
        
        TTYWriteEvent.Add (fun s ->
            match latestTTY with 
            | Some tty ->   tty.Write s 
            | None     ->   ())
               
        EnsureTTYEvent.Add (fun () ->
            let ttyScreen = System.Drawing.Size (700, 800)
            let tty = new TTYWindow (Text =  "Elliott Teletype", Visible = true, 
                                     MinimumSize = ttyScreen, MaximumSize = ttyScreen)
            latestTTY <- Some tty 
            tty.Show ())

        TTYPushEvent.Add (fun () -> 
            match latestTTY with
            | Some tty -> tty.Push ()
            | None     -> ())

        let EnsureTTY () =
            // Ensure a tty window is open 
            match latestTTY with
            | None      ->  triggerEventSend ensureTTYEvent ()
            | Some(tty) ->  if   not (tty.Open())
                            then triggerEventSend ensureTTYEvent ()  

        let TTYCharsAvailable () = ttyInChs.Length > 0

        let ReadFromTTY () =
            // printfn "ReadFromTTY"
            while ttyInChs.Length <= 0 do 
                 EnsureTTY ()
                 triggerEventSend ttyPushEvent ()
                 YieldToDevices () 
            let ch = ttyInChs.[0] 
            // printfn "ReadFromTTY gets %3d" (int ch)
            ttyInChs <- ttyInChs.[1..]
            triggerEventSend ttyPushEvent ()
            (int ch)

        let WriteToTTY (s: string) =
            // printfn "WriteToTTY %s" s
            EnsureTTY ()
            triggerEventSend ttyWriteEvent s
            if  not ttyPushPending
            then async { do! Async.Sleep 10
                         // printfn "Endsleep"
                         ttyPushPending <- false
                         triggerEvent ttyPushEvent ()
                       } |> Async.Start
                 ttyPushPending <- true
            YieldToDevices ()
    
        let TidyUpTTY () = 
            latestTTY <- None 
            ttyInline <- false  

    open Teleprinter
   
    let DefaultTelecode () = defaultTelecode 
    
    let SetDefaultTelecode telecode = defaultTelecode <- telecode

    let SetTTYNewline status = ttyNewline <- status

    let OpenTTYInBinaryString text rdrMode =
        // take binary input from command stream
        ttyInline    <- true
        ttyIn        <- Some (TranslateFromBinary text rdrMode)
        ttyInPos     <- 0

    let OpenTTYConsole telecode =
        ttyTelecode <- telecode
        ttyInline   <- false
        ttyLastChOut <- -1
        ttyLastChCnt <- 0

    let OpenTTYInTextString text telecode mode = 
        ttyTelecode <- telecode
        ttyInline   <- true
        ttyInPos    <- 0
        ttyIn       <- Some (
                            match telecode with
                                    | T900 -> TranslateFromText    T900 mode text
                                    | T903 -> TranslateFromText    T903 mode text
                                    | T920 -> TranslateFromText    T920 mode text
                                    | TACD -> TranslateFromText    TACD mode text
                                    | TTXT -> TranslateFromText    TTXT mode text) 

    let TTYInputReady () =
        if ttyInline
        then true
        else TTYCharsAvailable ()

    let rec GetTTYChar () =  
        let telecode = if ttyInline then ttyTelecode else defaultTelecode
        // get character
        let ch =        
            if   ttyInline
            then let ti =
                    match ttyIn with
                    | Some ti   ->  ti
                    | _         ->  raise (Device "No input attached to teleprinter")
                 if  ttyInPos >= ti.Length
                 then raise (Device "Run off end of teleprinter input")
                 else let ch = ti.[ttyInPos]
                      ttyInPos <- ttyInPos+1
                      ch
            else TelecodeOf telecode (char (ReadFromTTY ()))
        // printfn "GetTTYChar %3d %b" ch ttyNewline
        // decide how to handle returns and newlines
        let Echo ch = 
            if ttyInline then WriteToTTY (UTFOf telecode ch)
            ch
        match telecode with
        | T920 ->   Echo ch
        | _    ->   if   ch = lf900
                    then ttyReturnSeen <- true
                         Echo (if ttyNewline then lf900 else cr900)
                    else Echo ch
                   
    let PutTTYChar ch =  
        // printfn "PutTTYChar %3d" ch
        let telecode = (if ttyInline then ttyTelecode else defaultTelecode)
        match  telecode with
        | T920  ->  WriteToTTY  (UTFOf telecode ch)
        | _     ->  if   ttyInline
                    then // taking input from a file
                         if   ttyReturnSeen
                         then if   ch = cr900
                              then () // following 010uy will output \r\n
                              elif ch = lf900
                              then ttyReturnSeen <- false
                                   WriteToTTY (UTFOf telecode ch)
                              else ttyReturnSeen <- false
                                   WriteToTTY (UTFOf telecode ch)
                         else WriteToTTY (UTFOf telecode ch)
                    elif ttyReturnSeen && (ch = 010uy || ch = 141uy)
                    then ttyReturnSeen <- false // interactive console will already have echoed \r \n
                    else ttyReturnSeen <- false
                         WriteToTTY (UTFOf telecode ch) // no pending return, or other than newline sequence
        let chi = int ch
        if  chi = ttyLastChOut
        then if ttyLastChCnt = 1000
             then ttyLastChCnt <- 0 
                  raise (Device (sprintf "Continuously typing &%03o" chi))
             else ttyLastChCnt <- ttyLastChCnt+1
        else ttyLastChOut  <- chi
             ttyLastChCnt <- 1     

    let FlushTTY () =
        // Force out any buffered tty output
        match latestTTY with
        | Some(tty) -> if   tty.Open()
                       then triggerEventSend ttyPushEvent ()
                            YieldToDevices ()
        | None      -> () 
                  
    let CloseTTY () =
        // close TTY window if open, reset to direct input
        FlushTTY ()
        TidyUpTTY ()

     
    // GRAPH PLOTTER   

    // There are two models of plotting.  For E900 we reproduce Don Hunter's simulator
    // VGA screen with y vertically and x horizontally.  For all other aechitectures
    // we simulate an Elliott plotter with y as the long horizontal axis and x as the 
    // shorter vertical axis.  However, the window is not as long in the x-axis as a 
    // real plotter, so the SCALE command is available.  SCALE 3 fits a 13.750" wide
    // plot (i.e. a 903 Benson Lehner plotter) into the window.

    module private GraphPlotter =     

        let mutable x       = 0     // current x position
        let mutable y       = 0     // current y position
        let mutable swapxy  = false // controls x, y orientation - see ensure graph
        let mutable maxx    = 0     // maximum value of x 
        let mutable height  = 0     // height of window
        let mutable width   = 0     // width of window
        let mutable maxy    = 0     // maximum value of y
        let mutable xInit   = -1    // initial x coordinate
        let mutable yInit   = -1    // initial y coordinate
        let mutable scale   = 1     // scaling factor

        let mutable down         = false // state of pen
        let mutable plotting     = false

        // width in pixels of window margins around bitmap
        let xMargin = 16
        let yMargin = 38

        let mutable plotsWaiting = false
        
        // Plotter events
        let pixelEvent       = new Event<_>()
        let ensureGraphEvent = new Event<_>()
        let pushGraphEvent   = new Event<_>()     
                 
        let PixelEvent          = pixelEvent.Publish
        let EnsureGraphEvent    = ensureGraphEvent.Publish
        let PushGraphEvent      = pushGraphEvent.Publish 
                
        let PushGraph () =
            // Update graph on screen
            if   plotting
            then triggerEvent pushGraphEvent ()

        let EnsureGraph () =
            // set up new plotting window 
            if   not plotting
            then plotting <- true
                 if   machineType = E900
                 then maxx   <- 639 
                      maxy   <- 479 // 640*480 VGA screen
                      width  <- maxx+1+xMargin
                      height <- maxy+1+yMargin
                      if yInit = -1 then yInit <- 160
                      x      <- xInit     
                      y      <- yInit 
                 else maxx   <- 1799 // 2675 = 13.375"
                      maxy   <-  749   
                      width  <- maxx+1+xMargin
                      height <- maxy+1+yMargin 
                      maxx   <- maxx*(int scale)
                      maxy   <- maxy*(int scale)
                      if xInit = -1 then xInit <- 0
                      if yInit = -1 then yInit <- 0
                      x      <- if swapxy then xInit      else yInit
                      y      <- if swapxy then maxy-yInit else maxx-xInit
                 down <- false
                 triggerEvent ensureGraphEvent ()
                    
        let Pixel (x, y) =
            triggerEvent pixelEvent (x, y)

        type PlotterWindow () as plotter =
            inherit Form ()

            let mutable bitmap = new Bitmap (maxx+1, maxy+1, Imaging.PixelFormat.Format24bppRgb)

            let paintBitmap (g: Graphics) =
                plotsWaiting <- false
                g.DrawImage (bitmap, new Point (0, 0))
            // initialize bit map
            do for x = 0 to bitmap.Width-1 do 
                    for y = 0 to bitmap.Height-1 do 
                        bitmap.SetPixel (x, y, Color.White)

            // stop windows from drawing the background for this form
            do plotter.SetStyle (ControlStyles.AllPaintingInWmPaint|||
                            ControlStyles.Opaque, true)
            do plotter.Text          <- "Elliott Plotter"
            do plotter.Visible       <- true
            do plotter.CreateGraphics().Clear(Color.White)
            do plotter.Paint.Add  (fun e -> paintBitmap e.Graphics)
            do plotter.Resize.Add (fun _ ->
                        plotter.CreateGraphics().Clear(Color.White)
                        plotter.Invalidate())

            member plotter.DrawPixel (x, y) =
                bitmap.SetPixel (x, y, Color.Black)     

        // Direct plotting events to the most recent window           
        let mutable latestPlot: PlotterWindow option = None 

        PixelEvent.Add (fun (x, y) -> 
                        match latestPlot with 
                        | Some plotter -> plotter.DrawPixel (x, y)
                        | None         -> raise (Device "Plotter offline")
                                          plotting <- false)

        EnsureGraphEvent.Add (fun () ->
            let plotSize = System.Drawing.Size (width, height)
            let plotter = new PlotterWindow (MinimumSize = plotSize, MaximumSize = plotSize)
            plotter.Show ()
            latestPlot <- Some plotter)
               
        PushGraphEvent.Add (fun () ->
            match latestPlot with 
            | Some graph -> try graph.Invalidate () with _ -> latestPlot <- None
            | None -> ())    
            
        let RenewPlotter () =
            PushGraph ()
            plotting <- false
            
        let TidyUpPlotter () = 
            RenewPlotter ()  
            xInit <- -1
            yInit <- -1
            swapxy <- machineType = E900 
            scale <- 1
                                                          
    open GraphPlotter  

    let OpenPlotter () =   
        // Set up plotter for a new graph
        TidyUpPlotter ()
     
    let PutPlotter code =
        // make sure we have a graph window
        EnsureGraph ()
        if   not plotsWaiting
        then // set up a deferred task to push out pending plots
             async { do! Async.Sleep 25
                     PushGraph () } |> Async.Start
             YieldToDevices ()
        // decode plotter command
        let badCode () = raise (Device (sprintf "Bad Plotter Code &%o2" code))
        let oldDown = down
        if (code &&&  1) <> 0 then x <- x + 1
        if (code &&&  2) <> 0 then x <- x - 1
        if (code &&&  3) =  3 then badCode ()
        if (code &&&  4) <> 0 then y <- y - 1
        if (code &&&  8) <> 0 then y <- y + 1
        if (code &&& 12) = 12 then badCode ()
        if (code &&& 16) <> 0 then down <- false
        if (code &&& 32) <> 0 then down <- true
        if (code &&& 48) = 48 then badCode ()
        if (code &&& 48) <> 0 && (code &&& 15) <> 0 then badCode ()
        if   not down && x < 0 // moving to left hand side
        then x <- 0
        // clip to screen
        if   down 
        then if   swapxy
             then if 0 <= x && x <= maxx && 0 <= y && y <= maxy then Pixel ((x)/scale,      (y)/scale)
             else if 0 <= x && x <= maxy && 0 <= y && y <= maxx then Pixel ((maxx-y)/scale, (x)/scale)

    let PlotterSetX value = 
        // set x coordinate for plotting
        EnsureGraph ()
        x <- value
               
    let PlotterSetY value = 
        // set y coordinate for plotting
        EnsureGraph ()
        y <- value

    let SetScale s = 
        RenewPlotter ()
        scale <- s

    let SetOrigin x0 y0 =
        RenewPlotter ()
        xInit <- x0; yInit <- y0 

    let SwapXY () = 
        RenewPlotter ()
        swapxy <- machineType <> E900;
           
    let ClosePlotter () = 
        // Close plotting the current graph, if any.  Ensures graph is displayed and reset 
        // plotting system ready for another graph to be drawn.
        PushGraph ()   
        TidyUpPlotter ()


    // CARD READER
    module private CardReader =

        let mutable cardIn: byte[] option = None  // input text for card reader
        let mutable cardInPos             = 0     // next character to read in cardIn
        
        let blankCol   = CardCode 160 // space

    open CardReader

    let OpenCardTextString teleCode text =
        // take text input from command stream
        cardIn <- Some (
                        match teleCode with
                             | TACD -> TranslateFromText    TACD Mode3 text
                             | T900 -> TranslateFromText    T900 Mode3 text
                             | T903 -> TranslateFromText    T903 Mode3 text
                             | _    -> raise (Device "Inappropriate telecode for card reader")) 

    let OpenCardTxt (fileName: string) teleCode =
        // take card reader input from text file
        let text = File.ReadAllText fileName
        OpenCardTextString teleCode  text

    let CheckCard () = // check to see if another card can be read
        match cardIn with
        | Some ci   -> cardInPos < ci.Length 
        | _         -> false

    let GetCard () = // read in next card
        let ci =
            match cardIn with
            | Some ci   -> ci 
            | _         -> raise CRManual
        if   cardInPos >= ci.Length
        then None
        else let buffer = Array.zeroCreate 80
             let mutable cardOutPos = 0
             let mutable filling    = true
             while filling do
                if   cardInPos >= ci.Length
                then // no more data to read
                     filling <- false 
                else // read next card
                     let ch = ci.[cardInPos]
                     cardInPos <- cardInPos+1 // advance character pointer
                     match ch with
                     | 141uy 
                     | 000uy 
                     | 255uy    ->  // ignore carriage return, blank, erase
                                    ()
                     | 010uy    ->  filling <- false
                     | _        ->  if   cardOutPos < 80 // ignore characters after 80th column
                                    then buffer.[cardOutPos] <- CardCode (int ch)
                                         cardOutPos  <- cardOutPos+1
                     // pack out unfilled columns if any
                     for i = cardOutPos to 79 do buffer.[i] <- blankCol
             Some(buffer)
        
    let RewindCard () =
        match cardIn with
        | Some ci   ->  cardInPos <- 0
        | _         ->  raise (Device "No card input to rewind")
    
    let CloseCardReader () =
        cardIn <- None; cardInPos <- 0


    // LINE PRINTER
    module private LinePrinter =

        // Direct line printer output to a separate window
        type LPWindow() as lp = 
            inherit Form() 
            let mutable lpWindowOpen = true // set false if closed
            let textBox = new RichTextBox(Dock=DockStyle.Fill, 
                                      Font = new Font("Lucida Console",10.0f,FontStyle.Regular), 
                                      ForeColor = Color.Black,
                                      AcceptsTab = true,
                                      Multiline = true,
                                      ReadOnly = true, 
                                      DetectUrls = false,
                                      ShortcutsEnabled = false,
                                      ScrollBars = RichTextBoxScrollBars.Vertical)                            
            
            do lp.Closing.Add (fun arg -> lpWindowOpen <- false; ())
            do lp.SetStyle (ControlStyles.AllPaintingInWmPaint ||| ControlStyles.Opaque, true)
            do lp.Controls.Add textBox // put textbox on form 
            
            member lp.Write (s :string) =
                    textBox.AppendText s  // add text to text box
                    textBox.Show ()

            member lp.Open () = lpWindowOpen

        let ensureLPEvent    = new Event<_>() // new lp window needed
        let lpWriteEvent     = new Event<_>() // send next lp buffer

        let EnsureLPEvent     = ensureLPEvent.Publish        
        let LPWriteEvent      = lpWriteEvent.Publish 
        
        let mutable latestLP: LPWindow option = None
        
        LPWriteEvent.Add (fun s -> 
            match latestLP with 
            | Some lp  ->   lp.Write s 
            | None     ->   ())
               
        EnsureLPEvent.Add (fun () ->
            let lpScreen = System.Drawing.Size (1020, 800)
            let lp = new LPWindow (Text =  "Elliott Line Printer", Visible = true, 
                                     MinimumSize = lpScreen, MaximumSize = lpScreen)
            latestLP <- Some lp 
            lp.Show ())

        let OpenLP () = triggerEventSend ensureLPEvent () 
            
        let WriteToLP s =
            // Ensure a lp window is open 
            match latestLP with
            | None      ->  raise LPManual
            | Some(lp)  ->  if   not (lp.Open())
                            then raise LPManual
            triggerEvent lpWriteEvent s
    
        let ResetLP () = latestLP <- None      

    open LinePrinter

    let OpenLinePrinter = OpenLP

    let PutLPChars (buffer: int[]) =  
        // printer receives a buffer of SIR internal code characters packed 3 per word
        let PrinterSymbolOf code =
            match code with
            | 0     ->  " "
            | 1     ->  "!" // instead of newline
            | 63    ->  UTFOf T903 (byte 64) // line printer code 63 should output close quote
            |_  ->  UTFOf T903 (byte (code+32)) // convert SIR internal to ASCII without parity
        // output character to line printer
        if buffer.Length > 120 then raise (Device "Attempt to output more than 120 characters to the lineprinter")
        let throw = buffer.[0] >>> 12
        for i = 2 to throw do WriteToLP "\n" // deal with line feed count
        let output = new StringBuilder ()
        for i = 0 to buffer.Length-1 do
            let bufi = buffer.[i]
            output.Append (PrinterSymbolOf (bufi >>> 12)) |> ignore
            output.Append (PrinterSymbolOf ((bufi >>> 6) &&& 63)) |> ignore
            output.Append (PrinterSymbolOf (bufi &&& 63)) |> ignore
        let bufstr = output.ToString ()
        let text = bufstr.Substring (1) // omit line feed count
        WriteToLP (text+"\n")
        int64 throw

    let CloseLinePrinter () = 
        latestLP <- None
        ttyInPos <- 0


    // MAGNETIC TAPE
    // Magnetic tapes are represented as streams of bytes organized into segments.
    // Each segment is structured as follows:
    // byte 0: sentinel = 127
    // byte 1: parity - 0 = even 1 = odd
    // byte 2: segment type
    //  0: data block
    //  1: erase
    //  2: tape mark
    //  bytes 3-5: position of previous segment in stream (0 if none)
    //  bytes 6-8: segment length in 24 bit words, excluding the header
    //  bytes 9 onward segment data as written by computer
    //  After data we leave interblock gap - size of header (9) bytes so that file length
    //  approximates tape legth in characters.

    //  tape reel length 2400 ft
    //  recording density 200 ch/in 
    //  interblock gap 0.75in

    let maxTapeChars = int64 (2400 * 12 * 200 - 10000) // 2400 foot reel at 200 ch/in

    let sentinel    = 127uy     // used to mark start of block
    let stopper     = 0o777777  // used to indicate no previous block
    let oddParity   = 1uy
    let evenParity  = 0uy

    let interBlockGap = 200L*3L/4L+4L   // 0.75 in gap plus check word
    let hdrLen        = 9L           
    let gap           = interBlockGap-hdrLen

    type Tape (fs: FileStream, wp: bool) =
         
        let mutable prevBlockStart = stopper // start of previous block on tape 

        let TapeError msg = raise (Device ("Mag tape file format error: "+msg))

        member private t.WriteWord (w: int) =
            fs.WriteByte (byte (w >>> 16 &&& 255))
            fs.WriteByte (byte (w >>>  8 &&& 255))
            fs.WriteByte (byte (w        &&& 255))

        member private t.ReadWord () =
            let b3 = fs.ReadByte ()
            let b2 = fs.ReadByte ()
            let b1 = fs.ReadByte ()
            (b3 <<< 16) ||| (b2 <<< 8) ||| b1

        member t.ReadBlock () = 
            //printfn "t.ReadBlock pos=%d prev=%d" fs.Position prevBlockStart
            if   fs.Position >= fs.Length
            then (true, [||]) // attempt to read beyond file
            else try
                    prevBlockStart <- int fs.Position
                    if fs.ReadByte () <> (int sentinel) then TapeError "sentinel missing - readblock"
                    let odd = fs.ReadByte () = 1
                    let c = fs.ReadByte ()
                    let p = t.ReadWord ()  // previous block start
                    let l = t.ReadWord ()  // length of segment
                    match c with
                    | 0 ->  // data block
                            let buf: int[] = Array.zeroCreate l
                            for i = 0 to l-1 do
                                buf.[i] <- t.ReadWord ()
                            fs.Position <- fs.Position+gap // skip to next block
                            (odd, buf)
                    | 1 -> // tape mark
                           let buf: int[] = Array.zeroCreate 1
                           buf.[0] <- (int (fs.ReadByte ())) <<< 12
                           (odd, buf)
                    | 2 -> // erase - return null buffer
                           fs.Position <- int64 prevBlockStart
                           (odd, [||])
                    | _ -> TapeError (sprintf "unknown block type %d" c)   
                 with
                 | _ -> TapeError "short block header"
                       
        member t.WriteBlock (buffer: int[]) odd = 
            // printfn "t.WriteBlock pos=%d prev=%d" fs.Position prevBlockStart
            let start = int fs.Position
            fs.WriteByte sentinel 
            fs.WriteByte (if odd then oddParity else evenParity) 
            fs.WriteByte 0uy // data block
            t.WriteWord prevBlockStart
            t.WriteWord buffer.Length
            for i = 0 to buffer.Length-1 do
                t.WriteWord buffer.[i]
            prevBlockStart <- start
            // leave inter block gap
            let pos = fs.Position+gap
            // put an erase block after written block if not at end of file
            t.Erase ()
            // but arrange that next write will overwrite the erase
            fs.Position <- pos

        member t.Backspace () = 
            // printfn "t.backspace pos=%d prev=%d" fs.Position prevBlockStart
            let pos = fs.Position
            if prevBlockStart <> stopper
            then fs.Position <- int64 prevBlockStart
                 if   fs.ReadByte () <> (int sentinel)
                 then TapeError "sentinel missing - backspace"
                 else let p   = fs.ReadByte ()
                      let c   = fs.ReadByte () 
                      let prev = t.ReadWord ()
                      fs.Position <- int64 prevBlockStart
                      prevBlockStart <- prev
                      pos-fs.Position // number of characters stepped back
            else 0L

        member t.Rewind () =
            // calculate tape length - length in characters to feet, 180 ft/sec to usec*10
            let length = fs.Position
            // set tape at beginning
            fs.Position <- 0L
            prevBlockStart <- stopper
            length

        member t.Erase () = 
            fs.WriteByte sentinel
            fs.WriteByte oddParity
            fs.WriteByte 1uy // erase segment
            t.WriteWord prevBlockStart

        member t.TapeMark a = 
            let prev = fs.Position
            fs.WriteByte 127uy // sentinel
            fs.WriteByte 2uy // tapemark segment
            t.WriteWord prevBlockStart
            t.WriteWord (a &&& 63)
            prevBlockStart <- (int prev)

        member t.Position = fs.Position

        member t.AtLoadPoint  = fs.Position=0L

        member t.AtEndOfTape  = 
            fs.Position >= maxTapeChars

        member t.WritePermit = wp

        member t.Close () = fs.Close ()

    let NewTape (fileName, wp) =
        try
            let fs = new FileStream (fileName, (if wp then FileMode.OpenOrCreate else FileMode.Open))
            Tape (fs, wp)
        with
        | e -> raise (Device e.Message)

    let TidyUpTape () = ()
     
    // GENERAL FUNCTIONS

    let TTYPrint  = // used by print command etc
        WriteToTTY 

    let TidyUpDevices () =
            CloseCardReader ()
            CloseLinePrinter ()
            CloseReader ()
            ClosePunch ()
            CloseTTY ()
            ClosePlotter ()
            TidyUpPlotter ()
            TidyUpTTY ()
            TidyUpTape ()
            SetDefaultTelecode T900
            SetTTYNewline true

    let StartDevices () = () // to force initialization of this module
 