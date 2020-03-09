#light

module Sim900.Legible

open Sim900.Version
open Sim900.Bits
open Sim900.Telecodes
open Sim900.Models
open Sim900.Devices
open Sim900.Memory
open Sim900.Formatting
open Sim900.Machine
open Sim900.Parameters

// Legible paper tape characters for Elliott 900 Series Simulator

// Table of pairs of 9 bit legible character representations in collating sequence, omitting invalid
// and non-printing characters

module private LegibleHelper =

    let codes = [|  0o000000; 0o000000; 0o000000; 0o000277; 0o003400; 0o003630; 0o177231; 0o114602;
                    0o100106; 0o104777; 0o177611; 0o071207; 0o042447; 0o010010; 0o000344; 0o121341;
                    0o073211; 0o110646; 0o040240; 0o002002; 0o000474; 0o041201; 0o100502; 0o036102;
                    0o022020; 0o177420; 0o022102; 0o004010; 0o004176; 0o004010; 0o004260; 0o070010;
                    0o004010; 0o004010; 0o004010; 0o140300; 0o100100; 0o020020; 0o004000; 0o002002;
                    0o000474; 0o041201; 0o100601; 0o041074; 0o101377; 0o100302; 0o120621; 0o104601;
                    0o103102; 0o100611; 0o104611; 0o073010; 0o004014; 0o005377; 0o004217; 0o104611;
                    0o104611; 0o070576; 0o104611; 0o104611; 0o071003; 0o100501; 0o020421; 0o004407;
                    0o073211; 0o104611; 0o104566; 0o043211; 0o104611; 0o104576; 0o143306; 0o133166;
                    0o004020; 0o022102; 0o100444; 0o022044; 0o022044; 0o022044; 0o100502; 0o022020;
                    0o004370; 0o000160; 0o104210; 0o070001; 0o001004; 0o177011; 0o004411; 0o004776;
                    0o177611; 0o104611; 0o104566; 0o077201; 0o100601; 0o100502; 0o177601; 0o100601;
                    0o100576; 0o177611; 0o104611; 0o100777; 0o004411; 0o004401; 0o077201; 0o100601;
                    0o110562; 0o010377; 0o004010; 0o004010; 0o177601; 0o177601; 0o040601; 0o100577;
                    0o000401; 0o000777; 0o004020; 0o022102; 0o100777; 0o100200; 0o100200; 0o100377;
                    0o001004; 0o004004; 0o001377; 0o177404; 0o000010; 0o010040; 0o177576; 0o100601;
                    0o100601; 0o100576; 0o177411; 0o004411; 0o004406; 0o036102; 0o100601; 0o120502;
                    0o136377; 0o004431; 0o024511; 0o103106; 0o104611; 0o104611; 0o071001; 0o000401;
                    0o177401; 0o000401; 0o077600; 0o100200; 0o100177; 0o017440; 0o040200; 0o040040;
                    0o017577; 0o100100; 0o020100; 0o100177; 0o141444; 0o010010; 0o010044; 0o141401;
                    0o001004; 0o174004; 0o001001; 0o140641; 0o110611; 0o100605; 0o101777; 0o100601;
                    0o100630; 0o177231; 0o114602; 0o100201; 0o100601; 0o177404; 0o001377; 0o001004 
                    0o004030; 0o026010; 0o004010; 0o00400 |]   

    // table of indices into codes
    let index = [|  0o000007; 0o010013; 0o021027; 0o040046; 0o051054; 0o057066; 0o075077; 0o106110;
                    0o121130; 0o133141; 0o147155; 0o163171; 0o200206; 0o214216; 0o220225; 0o234241;
                    0o247252; 0o260266; 0o274302; 0o307314; 0o323331; 0o334343; 0o351357; 0o366375;
                    0o404412; 0o421427; 0o435444; 0o452461; 0o470477; 0o506515; 0o521527; 0o533540;
                    0o547000 |]

    // character symbols in collating sequence
    let symbols = "                                 !\"£$%&'()*+,-./0123456789:;<=>?@" +
                    "ABCDEFGHIJKLMNOPQRSTUVWXYZ[\]^_`abcdefghijklmnopqrstuvwxyz"
open LegibleHelper
open System.IO

// look up legible representation of ch
let LegibleOf (ch: char) =
    let bytes: int[] = Array.zeroCreate 10
    let pos = (
        let p = symbols.IndexOf ch
        if   p < 32
        then 0
        elif p <= 96
        then p-32
        else p-64)
    let first, last = (
        let j = pos >>> 1
        if    pos &&& 1 = 0
        then (index.[j]>>>9,     index.[j]&&&0o777)
        else (index.[j]&&&0o777, index.[j+1]>>>9))
    for k = first to last-1 do
        let pattern = (
            if  k % 2 = 0
            then codes.[k/2] >>> 8
            else codes.[k/2] &&& 0o377)
        bytes.[k-first] <- pattern
    bytes.[0..last-first]

let Raw (words: string[]) fileName =
    let oldFile =
        try File.ReadAllBytes fileName with | _ -> Array.empty
    let newFile = File.Create fileName
    let Runout () = for i=1 to 60 do newFile.WriteByte 0uy
    Runout ()
    for w in words do
        for ch in w do 
            let codes = LegibleOf ch
            for ch in codes do newFile.WriteByte (byte ch)
    Runout ()
    let rec Copy idx  =
        if   idx < oldFile.Length
        then if oldFile.[idx] = 0uy 
             then Copy (idx+1)  
             else newFile.Write (oldFile, idx, oldFile.Length-idx)
    Copy 0
    newFile.Close ()

let space = (LegibleOf ' ').Length
    
let TextFile (words: string[]) fileName binary =
    // if file exists write header at front, else just create a file containing the header.
    let input   = if File.Exists fileName then File.ReadAllText fileName else ""
    let outFile = File.Create fileName
    let output  = new StreamWriter (outFile)
    let buffer: int[] = Array.zeroCreate 120000  // one reel of tape!
    let mutable index = 0
    // build up a buffer of codes
    for w in words do
       for ch in w do 
            let bytes = LegibleOf ch
            for b in bytes do   
                buffer.[index] <- b
                index <- index+1
            index <- index+2 // space out characters
       index <- index+space // space out words
    // print out the bits
    for row in seq[1; 2; 4; 8; 16; 32; 64; 128] do
        output.Write (if binary then "( Legible Header " else "<! Legible Header ")
        for i = 0 to index-space-4 do // miss off trailing space
            output.Write (if (int buffer.[i]) &&& row = 0 then ' ' else  'O')
        output.WriteLine (if binary then " )" else " !>")
    // output original content of file
    output.Write input
    output.Close ()
    
// insert a legible header at start of a file
let Legible (words: string[])  =
    if words.Length < 2
    then raise (Syntax "File name and string expected")
    let fileName = words.[0].ToUpper ()
    let BadFile () = raise (Syntax  "File extension not valid")
    if  fileName.Length < 5
    then BadFile ()
    let extn = fileName.Substring ((fileName.Length-4), 4)
    match extn with
    | ".900" | ".DAT" | ".TXT" 
    | ".ACD" | ".903" | ".920" -> TextFile words.[1..] fileName false
    | ".BIN" | ".RLB"          -> TextFile words.[1..] fileName true
    | ".RAW"                   -> Raw      words.[1..] fileName
    | _                        -> BadFile ()

                    

