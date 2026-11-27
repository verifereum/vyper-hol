(* Transport source observations from a variable operand to its lookup address. *)
Theory bodyConvertSourceWindowTransport
Ancestors
  compileEnv vyperState

Theorem mload_clean_transport:
  !z t a w n dirty.
    lookup_var z t = SOME a /\
    eval_operand (Var z) t = SOME w /\
    mload (w2n w) t = n2w n /\
    (!i. w2n w <= i /\ i < w2n w + 32 ==> i NOTIN dirty) /\
    (!i. w2n w + 32 <= i /\ i < w2n w + 32 + n ==> i NOTIN dirty) ==>
    mload (w2n a) t = n2w n /\
    (!i. w2n a <= i /\ i < w2n a + 32 ==> i NOTIN dirty) /\
    (!i. w2n a + 32 <= i /\ i < w2n a + 32 + n ==> i NOTIN dirty)
Proof
  rpt strip_tac >>
  Cases_on `lookup_var z t` >>
  gvs[venomStateTheory.eval_operand_def]
QED
