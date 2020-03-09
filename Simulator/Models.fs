#light

// MODELS 
//
// Range of models in Elliott 900 Series computers
//
// The 900 series computers were built by Elliott Brothers (which became part
// of GEC-Marconi and eventually BAe Systems) from the mid 1960's to the mid 1970's.  
// They found use in industrial automation, military systems and to a lesser 
// degree in schools and colleges.
//
// The range consisted of the following machines:
//
//      920A:     the first version, used in some military systems, relatively 
//                few made and relatively little surviving documentation
//      920B:     the next version, used in military embedded systems
//      903:      a civilian version of the 920B for the general purpose computing
//                market, popular with schools and colleges
//      ARCH900:  a civilan version of the 920B used in civil embedded systems
//      920C:     an extended and faster version of the 920B used in military
//                embedded systems
//      905:      the civilian general purpose computer version of the 920C
//      ARCH9000: the civilian embedded systems version of the 920C
//      920M:     a miniaturized version of the 920C primarily for the military market
//      920ATC:   no information known
//
// The memory for a 900 series machine consisted of a series of 8K modules (16K modules 
// for later varients).  The maximum memory configuration varied between models.
// For some models fast and slow memory options were available.
// 
// The 900 series had provision for paper tape input and output and for an optional teletype.
// Various speed tape readers were available.
//
// Further differences between machines in the series are identified in higher level modules
// as follows:
//
// Module TELECODES: different character sets used as the range evolved
// Module DEVICES:   paper tape, teleprinter and graph plotting facilities
//                   (other 900 series peripherals are not yet supported)
// Module MACHINE:   variations in instruction sets (changes in order code and
//                   behaviour of side effects features.
//
// Most of the information used to build the simulator was taken from Terry Froggat's 
// and Don Hunters web sites (http://www.tjfroggatt.plus.com/, 
// http://www.gnhunter.demon.co.uk/.

module Sim900.Models

    exception Machine of string

    type MachineType = 
            | E920a  // 
            | E920b  // also 903 and ARCH9000
            | E920m  // 
            | E920c  // 920C/905 / ARCH9050 
            | E900   // generic 900 series 

    let mutable machineType   = E900
    let mutable machineName   = ""
    let mutable memory        = 0     // memory size in 4K units
    let mutable memorySpeed   = 0     // in micrososeconds
    let mutable memorySize    = 0
    let mutable timing: int[] = [||]  // instruction timing 
    
         
    // IO TIMES in microseconds * 10

    let mutable ptrCharTime =    10000L     // 1000 c/s
    let ptpCharTime         =   100000L     //  100 c/s
    let ttyCharTime         =  1000000L     //   10 c/s
    let pltXYTime           =    33000L     //    3.3  milliseconds
    let pltUpDnTime         =   200000L     //   20.0  milliseonds
        
    let PlotTime cmd =
        (if cmd &&& 0xf  <> 0 then pltXYTime   else 0L) +
        (if cmd &&& 0x30 <> 0 then pltUpDnTime else 0L)   
    
    // Check for valid configurations        
    let CheckConfiguration name memSize memSpeed ptrSpeed =

        // MACHINE NAME
        machineName <- name

        // MACHINE TYPE
        machineType <- match name with
                            | "920A" | "901"              -> E920a
                            | "920B" | "903" | "ARCH9000" -> E920b
                            | "920C" | "905" | "ARCH9050" -> E920c
                            | "920M"                      -> E920m
                            | "900"                       -> E900
                            | _                           -> raise (Machine (sprintf "Unknown machine type '%s'" name))
        
        // INSTRUCTION TIMES in microseconds * 10, taken from Terry Froggat's "Elliott 900 Series
        // Instruction Set and Times" document.  (Note times for 920A 4usec are an estimate).
        //      /,    0,    1,    2,    3,    4,    5,     6,   7<,   7>, 
        //     7=,    8,   9<,  9>=,   10,   11,   12,    13,   14,    n, // 14 shift n
        //     14,    n,   15,    I, 7168, 7169, 7169,  7170, 7170, 7170, // 14 i/o n;
                                                                          // interrupt
                                                                          // 15 no skip / skip
        //   7171, 7172, 7173, 7174, 7175, 7176, 7177        
        timing <- 
                match (machineType, memSpeed, memSize) with
                
                | (E920a, 6, "4K")
                | (E920a, 0, "4K")       ->  [|060;270;210;270;210;210;210;270;210;240;
                                               300;210;270;210;240;300;1800;1860;240;090;
                                               000;000;240;000;240;000;000;000;000;000;
                                               000;000;000;000;000;000|]
                | (E920a, 8, "8K")
                | (E920a, 0, "8K")       ->  [|080;330;270;330;270;270;270;330;250;280;
                                               360;270;330;250;250;300;1860;1920;280;090;
                                               000;000;280;000;280;000;000;000;000;000;
                                               000;000;000;000;000;000|]
                | (E920b, 6, _)
                | (E920b, 0, _)          ->  [|065;285;240;270;235;240;235;235;200;215;
                                               265;240;200;260;240;316;765;795;220;030;
                                               235;095;205;000;205;000;000;000;000;000;
                                               000;000;000;000;000;000|]

                | (E920m, 5, _)          ->  [|006;220;190;210;200;190;200;190;160;170;
                                               210;190;150;190;200;250;380;390;160;010;
                                               180;010;200;000;200;000;000;000;000;000;
                                               000;000;000;000;000;000|]
                | (E920m, 2, _)
                | (E920m, 0, _)          ->  [|032;108;106;126;116;106;116;106;104;114;
                                               126;106;094;106;116;178;296;306;104;010;
                                               124;072;144;000;144;000;000;000;000;000;
                                               000;000;000;000;000;000|]

                | (E920c, 2, _)          ->  [|022;066;044;053;053;044;053;044;022;022;
                                               022;022;022;022;056;053;122;213;039;009;
                                               048;065;065;056;114;049;058;083;092;057;
                                               047;047;061;061;057;057|]
                | (E920c, 1, _)
                | (E920c, 0, _)          ->  [|012;036;024;033;033;024;033;024;012;012;
                                               012;012;012;012;036;033;102;193;029;009;
                                               038;055;055;036;074;029;038;053;062;037;
                                               037;037;041;041;037;037|]

                | (E900, 0, _)           ->  [|065;285;240;270;235;240;235;235;200;215; // 920B/903 times by default
                                               265;240;200;260;240;316;765;795;220;030;
                                               235;095;205;000;205;000;000;000;000;000;
                                               000;000;000;000;000;000|]
                | _                      -> raise (Machine ("Unsupported system configuration for " + name))

        // Paper tape reader speed
        ptrCharTime <- match ptrSpeed with
                        |    0                     // default 
                        |  250 -> 40000L           //  250 c/s
                        |  500 -> 20000L           //  500 c/s          
                        | 1000 -> 10000L           // 1000 c/s
                        | _    -> raise (Machine "Tape speed must be 250, 500 or 1000 characters per second")

        // Store size
        let BadSize () = raise (Machine (sprintf "Inappropriate memory size for %s" machineName))
        memory <- match machineType with
                   | E920a -> match memSize with
                              | "4K" -> 1
                              | "8K" -> 2
                              | ""   -> 2
                              | _    -> BadSize ()
                   | E920b -> match memSize with
                              |  "8K" ->   2 | "16K" ->   4 | "24K" ->   6 | "32K" ->   8 
                              | "40K" ->  10 | "48K" ->  12 | "56K" ->  14 | "64K" ->  16 
                              |    "" ->   2   
                              | _ -> BadSize ()
                   | E920m -> match memSize with
                              |  "8K" ->  2 | "16K" ->  4   
                              |    "" ->  2
                              | _ -> BadSize ()                   
                   | E920c
                   | E900  -> match memSize with
                              |  "8K" ->   2 | "16K" ->   4 | "24K" ->  6 |  "32K" ->  8 |  "40K" -> 10 |  "48K" -> 12
                              | "56K" ->  14 | "64K" ->  16 | "80K" -> 20 |  "96K" -> 24 | "112K" -> 28 | "128K" -> 32
                              |   ""  ->  2
                              | _ -> BadSize ()

        memorySize <- memory * 4096

        memorySpeed <- 
            if   memSpeed = 0
            then match machineType with 
                       | E920a when memSize="4K"    -> 6
                       | E920a                      -> 8 
                       | E900 | E920b               -> 6 
                       | E920m                      -> 2 
                       | E920c                      -> 1
            else memSpeed