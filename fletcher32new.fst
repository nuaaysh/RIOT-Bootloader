module Fletcher32new

open FStar.Integers
open FStar.Int
open FStar.Int.Cast


(*val callForlen : UInt32.t -> UInt32.t -> UInt16.t -> len : UInt32.t{len>= 0ul} -> UInt32.t*)

let rec callForlen (c0 c1: UInt32.t) (data: UInt16.t) (len: UInt32.t{len>=0ul /\ (len % 2ul == 0ul)})
  : Tot UInt32.t
        (decreases (v len))
  = 
  match len with
  | 0ul -> ( c1 <<^  16ul ) |^ c0
 (* | 1ul -> 0ul*)
  | _   -> callForlen c0 c1 data (len - 2ul)

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
open FStar.UInt16

(*val test1 : d:UInt16.t{size ((v d) + 1) 16} -> UInt32.t*)
(*
val test1 : d:UInt16.t{size ((v d) + (v 1us)) 16} -> UInt32.t


let test1 d = 
  let d1 = d + 1us in
    assert (size (v d1) 16);
    UInt32.uint_to_t (UInt16.v d1)

val test2 : int -> (int & int)
let test2 (d:int) = (d,d)*)


val dowhile : tlen:UInt16.t{tlen >= 0us} -> (d:UInt16.t{size ((v d) + (v tlen)) 16}) -> (s1:UInt32.t{size ((UInt32.v s1)+ ( UInt32.v (UInt32.uint_to_t ((v d)+(v tlen))) )) 32}) -> (s2:UInt32.t) -> Tot (UInt32.t & UInt32.t) (decreases %[tlen])

let rec dowhile tlen d s1 s2 =
    match tlen with
    | 0us -> (s1+(UInt32.uint_to_t (UInt16.v d)), s2)
    | _ ->        
      let data = d + 1us in
        assert (size (v data) 16);
        let sum1 = s1 + (UInt32.uint_to_t (UInt16.v data)) in
          assert (size (UInt32.v sum1) 32);
        (*let sum2 = s2 + sum1 in*)
          dowhile (tlen-1us) data s1 s2
    

