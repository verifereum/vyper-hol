Theory bodyFullAbiDecodeBytesArithmetic
Ancestors
  words arithmetic vyperValue

(* Used at the head guard with (off,32), then at the payload guard
   with (off+32,c).  Lower and upper machine checks exclude wrapping. *)
Theorem abi_decode_checked_add_bound:
  !x y h.
    x < dimword (:256) /\ y < dimword (:256) /\
    h < dimword (:256) /\
    x <= w2n (n2w (x+y) : bytes32) /\
    w2n (n2w (x+y) : bytes32) <= h ==> x+y <= h
Proof
  simp[wordsTheory.w2n_n2w] >> rpt strip_tac >>
  Cases_on `x+y < dimword (:256)`
  >- gvs[LESS_MOD] >>
  `(x+y) MOD dimword (:256) = x+y-dimword (:256)` by
    (irule MOD_UNIQUE >> qexists_tac `1` >> simp[] >> decide_tac) >>
  gvs[] >> decide_tac
QED
