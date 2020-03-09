#light

// The simulator runs as a command line interpreter on the system console.
// Plotter output is projected on a window representing a DOS screen to
// model the user experience of the Ada simulator.  Each separate program run 
// creates its own window.
// The windows are fixed size and can only be closed or minimized.

module Sim900.GUI

    open System.Windows.Forms
    open System.Drawing
    open Sim900.Devices
    open Sim900.Machine


    (* type ControlForm() as form = 
        inherit System.Windows.Forms.Form() 

        let button = new Button(Text = "Stop")
        do button.Click.Add (fun _ -> Stop ()) 
        do form.Controls.Add button *)
