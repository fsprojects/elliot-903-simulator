#light

// Elliott 900 Series simulator main program

module Sim900.Main


open Sim900.Version
open Sim900.Formatting
open Sim900.Devices
open Sim900.Shell
open System
open System.Windows
open System.Windows.Forms

// MAIN PROGRAM
[<STAThread>]
do
    CloseReader () // force devices to initialize

    MessagePut simulatorVersion
    MessagePut "Simulation Starting"

    // Run commands
    async { CommandLineInterpreter () } |> Async.Start

    Application.Run()

