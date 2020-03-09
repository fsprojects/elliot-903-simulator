#light

module Sim900.Memory

    open Sim900.Bits  

    // Address layout
    let moduleShift = 13                         // module number
    let aModuleMask = bit16 ||| bit15 ||| bit14  // 900, 920A,B,M have 16 bit address bus
    let cModuleMask = bit17 ||| aModuleMask      // 920C has 17 bit address bus
        
    // Instruction layout
    let mShift      = 17                                  // B modification flag (bit18)
    let fShift      = 13                                  // function (op) code field (bits 17-14)
    let fMask       = bit17 ||| bit16 ||| bit15 ||| bit14 //  
    let operandMask = mask13                              // operand field (13 bits)     
        
    // PACK AND UNPACK INSTRUCTIONS   
    let InstructionToWord (m, f, o) = 
        ((m <<< mShift) ||| (f <<< fShift) ||| o)  
    
    // Functions to unpick words and addresses               
    let AddressField  word = word &&& operandMask
    let FunctionField word = (word &&& fMask) >>> fShift
    let ModifyField   addr = (addr >>> mShift) &&& bit1 
    let ModuleField   addr = (addr &&& cModuleMask) >>> moduleShift


