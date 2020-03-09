#light

// BITS
// The Elliott 900 series has an 18 bit 2's complement architecture.
// Elliott 900 arithmetic is performed using uint32 values masked
// to 18 bits. (Bit 19 is needed for multiplication).
//
// This module provides a type 'bits' for such values and
// defines a range of useful bits constants. 

module Sim900.Bits
    
    let bit1   =      0x1
    let bit2   =      0x2
    let bit3   =      0x4
    let bit4   =      0x8
    let bit5   =     0x10
    let bit6   =     0x20
    let bit7   =     0x40
    let bit8   =     0x80
    let bit9   =    0x100
    let bit10  =    0x200
    let bit11  =    0x400
    let bit12  =    0x800
    let bit13  =   0x1000
    let bit14  =   0x2000
    let bit15  =   0x4000
    let bit16  =   0x8000
    let bit17  =  0x10000
    let bit18  =  0x20000
    let bit19  =  0x40000 // used to detect overflow
    let mask3  =      0x7
    let mask4  =      0xf
    let mask6  =     0x3f
    let mask7  =     0x7f
    let mask8  =     0xff
    let mask12 =    0xfff
    let mask13 =   0x1fff
    let mask14 =   0x3fff
    let mask15 =   0x7fff
    let mask16 =   0xffff 
    let mask17 =  0x1ffff
    let mask18 =  0x3ffff
    let mask19 =  0x7ffff
    let mask20 =  0xfffff
    let mask21 = 0x1fffff

    let not1   =  0X3fffe // relative to 18 bits
    
    // Convert from 18 to 32 bit arithmetic
    let Normalize word = if word >= 131072 then (word%131072)-131072 else word
      