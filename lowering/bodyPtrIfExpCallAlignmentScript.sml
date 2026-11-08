Theory bodyPtrIfExpCallAlignment
Ancestors bodyPtrIfExpCallShape bodyPtrIfExpUnwrapContract exprLowering

(* Exact internal-call return-tag alignment does not hold for compatible
   memory bytestring widening. Allocating arms instead exclude calls. *)
