module Fletcher32

open FStar.Integers
open FStar.Int
open FStar.Int.Cast

(*
@original:
do {
     sum2 += sum1 += unaligned_get_u16(data++);
} while (--tlen);
=>(trans)

do {
  sum1 = sum1 + *(data++);
  sum2 = sum2 + sum1;
  tlen = tlen - 1;
} while (tlen != 0)
=> (to_caml)
*)

val dowhile : tlen:UInt32.t{tlen >= 0ul} -> UInt16.t -> UInt32.t -> UInt32.t -> Tot (UInt16.t & UInt32.t & UInt32.t) (decreases (v tlen))

let rec dowhile tlen d s1 s2 =
    match tlen with
    | 0ul -> (d, (UInt32.add_mod s1 (UInt32.uint_to_t (UInt16.v d))), s2)
    | _ ->        
      let data =UInt16.add_mod d 16us in
        let sum1 =UInt32.add_mod s1 (UInt32.uint_to_t (UInt16.v data)) in
          let sum2 = UInt32.add_mod s2 sum1 in
            dowhile (tlen - 1ul) data s1 s2
(*
@comment testing code

val test1 : d:UInt16.t{size ((v d) + 1) 16} -> UInt32.t

val test1 : d:UInt16.t{size ((v d) + (v 1us)) 16} -> UInt32.t


let test1 d = 
  let d1 = d + 1us in
    assert (size (v d1) 16);
    UInt32.uint_to_t (UInt16.v d1)

val test2 : int -> (int & int)
let test2 (d:int) = (d,d)
*)

(*
@original:
 uint32_t sum1 = 0xffff, sum2 = 0xffff;
 while (words) {
   unsigned tlen = words > 359 ? 359 : words;
   words -= tlen; 
   //...dowhile        
   sum1 = (sum1 & 0xffff) + (sum1 >> 16);
   sum2 = (sum2 & 0xffff) + (sum2 >> 16);
 }     
 sum1 = (sum1 & 0xffff) + (sum1 >> 16);
 sum2 = (sum2 & 0xffff) + (sum2 >> 16);
 *)

val  while_t : (words : UInt16.t{words >= 0us}) -> UInt16.t -> UInt32.t -> UInt32.t -> Tot (UInt32.t & UInt32.t) (decreases (v words))

let rec while_t words data s1 s2 =
  match words with
  | 0us -> (s1, s2)
  | _ -> 
    let tlen = if words > 359us then 359us else words in
     assert (words >= 0us);
     assert ((words - tlen) >= 0us);
     assert (tlen >= 0us);     
    let (data, sum1, sum2) = dowhile (uint16_to_uint32 tlen) data s1 s2 in
    let sum11 = UInt32.add_mod (UInt32.logand sum1 0xfffful) (sum1 >>^ 16ul) in     
    let sum21 = UInt32.add_mod (UInt32.logand sum2 0xfffful) (sum2 >>^ 16ul) in
     while_t (UInt16.sub_mod words tlen) data sum11 sum21

let f32 (data words : UInt16.t) =
  let (sum1,sum2) = while_t words data 0xfffful 0xfffful in
  let sum11 = UInt32.add_mod (sum1 &^ 0xfffful) (sum1 >>^ 16ul) in
  let sum21 = UInt32.add_mod (sum2 &^ 0xfffful) (sum2 >>^ 16ul) in
  (sum21 <<^ 16ul) |^ sum11
