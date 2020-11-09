module Hdr

open FStar.Integers
open FStar.Int
open FStar.Int.Cast
open FStar.Printf

let rm = 0x544f4952ul (*RIOTBOOT_MAGIC*)

type rb_hdr_t = {magic_number : UInt32.t; 
                 version : UInt32.t; 
                 start_addr : UInt32.t; 
                 chksum : UInt32.t}

let rb_hdr_print (h: rb_hdr_t)  = 
sprintf "Image magic_number: 0x%ul\n Image Version: 0x%ul\n Image start address: 0x%ul\n Header chksum: 0x%ul\n" h.magic_number h.version h.start_addr h.chksum
(*\n? no 08 no multi sprintf statement*)

val rb_hdr_checksum : rb_hdr_t -> UInt32.t

open Fletcher32

let rb_hdr_checksum h = Fletcher32.f32 0xd300us 6us (*here we give a random address, current version without pointers or memory models*)

val rb_hdr_validate : rb_hdr_t -> int

let rb_hdr_validate h =
  if (h.magic_number = rm) && (rb_hdr_checksum(h) = h.chksum) then 
    0
  else 
    -1
