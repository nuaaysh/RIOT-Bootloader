module Hdr

open FStar.Integers
open FStar.Int

type point_ty = int

val rb_hdr_print : point_ty -> unit

val rb_hdr_validate : point_ty -> int

val rb_hdr_checksum : point_ty -> UInt32.t
