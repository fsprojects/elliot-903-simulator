#light

// Elliott 903 Algol simulator HELP command

module Sim900.Help

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
        open Sim900.Commands

        let Help word =
            let helptxt = [|
                    "ALGol ON | OFF";
                    "    Trace Algol parameter words";
                    "ATtach CRD FILE filename";
                    "    Take card reader input from file";
                    "ATtach CRD INLINE";
                    "    Take card reader input from command input as text";
                    "ATtach MT n file [WP]";
                    "    Atatch file to magenetic tape drive number n [with write permit ring fitted";
                    "ATtach PLT";
                    "    Open new plotter window";
                    "ATtach PTP FILE filename [telecode]";
                    "   Send punch output to file";
                    "ATtach PTR INLINE [telecode [mode]]";
                    "   Take paper tape reader input from command input as text";
                    "ATtach PTR INLINE BIN [mode]";
                    "    Take paper tape reader input from command input as binary";
                    "ATtach PTR FILE filename [telecode [mode]]";
                    "   Take paper tape reader input from file";
                    "ATtach TTY INLINE telecode [mode]";
                    "   Take teleprinter input from command input as text";
                    "ATtach TTY INLINE BIN [mode]"
                    "    Take teleprinter input from command input as binary";
                    "AUTO";
                    "    Simulate an AUTOSTART";
                    "Break OFF";
                    "   Disable all breakpoints";
                    "Break OFF address {address}";
                    "   Disable breakpoint (if any) at addresses";
                    "Break ON  address {address}";
                    "   Enable breakpoint at specified addresses";
                    "Comment ....";
                    "   Comment";
                    "ChangeDirectory dirname";
                    "   Set current directory";
                    "CLear";
                    "   Clear all of store";
                    "CLear address";
                    "   Clear 8K store module which includes address";
                    "COMPare copy master";
                    "   Compare two paper tape files";
                    "DELete file";
                    "    Delete file";
                    "DEtach CRD";
                    "    Disconnect card reader from current input (if any)";
                    "DEtach MT n";
                    "    Disconnet file attached to magenetic tape drive n";
                    "DEtach PLT";
                    "   Finalize plotting on current window";
                    "DEtach PTP";
                    "   Disconnect punch from current output (if any)";
                    "DEtach PTR";
                    "   Disconnect reader from current input (if any)";
                    "DIRectory";
                    "   List files in current directory";
                    "Display first last";
                    "   Show contents of memory in range first..last";
                    "Display address"; 
                    "   Show contents of specified memory location";
                    "Display";
                    "   Show contents of registers A, Q, B and S"; 
                    "DumpAsSir file [literals]";
                    "    Dump all of memory as a SIR program to specified file";
                    "DUmpimage words file";
                    "   Dump a memory image of size specified from memory location 0 upwards to file";  
                    "Enter address value";
                    "   Store value in specified memory location";
                    "Find value";
                    "   Report locations in store cotaining specified value";
                    "FIXrlb from to";
                    "   Repair checksum in rlb";
                    "FAST";
                    "   Run simulation at full speed";
                    "Help ";
                    "   Show help"; 
                    "INTerrupt level";
                    "   Generate interrupt at specified level";
                    "Jump";
                    "   Jump to address specified on word generator";
                    "Jump keys";
                    "   Set word generator to specified value and jump";
                    "Keys value";
                    "   Set word generator to specified value";
                    "LEGible file text...";
                    "   Write text as legible header at front of file";
                    "ListDirectory / LiStdirectory";
                    "   List current directory contents"
                    "LOadimage file";
                    "   Load image file into memory";
                    "LoadModule moduleNo file";
                    "   Load memory module from file";
                    "LOG OFF";
                    "   Switch off logging";
                    "LOG ON";
                    "   Switch on logging";
                    "LOG filename";
                    "   Send logging output to specified file";
                    "MONitor ON address regions";
                    "   Display memory regions if execution reaches specified address";
                    "MONITOR OFF address";
                    "   Stop monitoring address";
                    "NewLine ON | OFF"
                    "    Pass through newlines on input (or not)"
                    "NonPrinting ON";
                    "    Make non printing characters visible";
                    "NonPrinting OFF";
                    "    Hide non-printing characters"
                    "NonStop ON";
                    "    Don't exit command level on stop conditions";
                    "NonStop ON";
                    "    Exit command level on stop conditions";
                    "OBEY";
                    "   Execute word generator as an instruction";
                    "OFF"; "Switch machine off";
                    "ON";
                    "   Switch machine on";
                    "ON architecture";
                    "   Switch machine on, with specified architecture"
                    "ON architecture memory";
                    "   Switch machine on with specified architecture and memory size";
                    "ON architecture memory speed";
                    "   Switch machine on with specified architecture, memory size and cycle time";
                    "ON architecture memory speed rate";
                    "   Switch machine on with specified architecture, memory cycle time and reader input rate";
                    "Origin x y";
                    "    Set plotter origin relative to (0, 0)";
                    "Pause";
                    "   Wait for input before continuing"
                    "PERT first last";
                    "    Display PERT message table between addresses";
                    "PRint file [mode]";
                    "   Pretty print file (format based on extension; mode applies to .RAW, .BIN and .RLB input)";
                    "PRintAlgol file [mode]";
                    "   Pretty print file as ALGOL intermediate code";
                    "QCheck from to format [from to format]";
                    "   Output memory in AMEND format"
                    "Quit";
                    "Exit the simulator";
                    "RESET";
                    "   Reset machine (must be stopped)";
                    "Restart [addr]";
                    "   Continue after a stop [stopping next at addr]";
                    "REVerse file";
                    "   reverse the contents of the file";
                    "ReWind";
                    "   Rewind paper tape input";
                    "ReWind CRD";
                    "    Rewind card reader input";
                    "ReWind PTR";
                    "   Rewind paper tape input"
                    "RLBTOSIR src dest [MODE1]";
                    "    Read RLB from file src and output as SIR to file dest";
                    "RUNOUT ON | OFF";
                    "    Turn on (off) addition of runout padding to text files";
                    "SCALE n";
                    "    Scale plotting by 1/n";
                    "SCBdecode";
                    "    Decode sum checked binary tape";
                    "SELECT IN PTR | AUTO | TTY"
                    "    Select paper tape input device";
                    "SELECT OUT PTP | AUTO | TTY";
                    "    Select paper tape output device";
                    "SHow Configuration";
                    "   Show the configuration of the current machine";
                    "SHow TIMEs";
                    "   Show execution and elapsed times";
                    "SKIP";
                    "   Skip over e.g., legible header in tape reader";
                    "SLow";
                    "   Run simulation at real time";
                    "Step";
                    "   Continue from stop for one instruction";
                    "Step count";
                    "   Continue from stop for specified number of instructions";
                    "STop(ped) address";
                    "   Quit command level if not stopped at specified address";
                    "SWAPXY";
                    "    Plot in landscape format";
                    "TeleCode telecode";
                    "    Set default telecode";
                    "TOBINary file";
                    "   Convert file to binary format based on extension";
                    "TORAW file";
                    "   Convert file to raw format based on extension";
                    "TOTELEcode file telecode";
                    "   Convert to specified telecode. e.g. ACD, 900, 903, 920"
                    "TRace OFF";
                    "   Turn off tracing"; 
                    "TRace ON";
                    "   Turn on tracing";
                    "TraceINTerrupt level ON";
                    "   Enable trace interrupts for level";
                    "TraceBuffer";
                    "   Print trace of most recently executed instructions";
                    "TraceINTerrupt level OFF";
                    "    Disable trace interrupts for level";
                    "TraceRegion OFF";
                    "    Apply tracing to entire store"; 
                    "TraceRegion from to";
                    "    Restrict tracing to specified address range";
                    (*"TRACK file start";
                    "    Run tracking against file, triggering at address";*)
                    "Watch ON loc";
                    "    Monitor store location";
                    "Watch OFF";
                    "    STop monitoring store";
                    "VerifyImage file";
                    "    Check image file against memory contents";|]
            if   word = ""
            then helptxt |> Array.iter (fun t -> printfn "%s" t)
            else helptxt |> Array.iteri 
                                (fun i t -> if   (t.ToUpper ()).StartsWith word 
                                            then printfn "%s\n%s" t helptxt.[i+1])

