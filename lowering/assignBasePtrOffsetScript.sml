(* Address-specific offset coverage: provenance sites need not have bounded ends. *)
Theory assignBasePtrOffset
Ancestors bodyPtrDefs words finite_map venomState ptrDiscipline

Theorem assign_base_ptr_covers_offset_address:
  !G tn p s total w b cap off n G' tn' q s'.
    ptr_covers G tn p s total /\ lookup_var p s = SOME w /\
    FLOOKUP G p = SOME (b,cap) /\
    w2n w + off < dimword(:256) /\ off + n <= total /\
    lookup_var q s' = SOME (w + n2w off) /\
    FLOOKUP G' q = SOME (b,cap) /\
    op_taint tn' (Var q) = {} ==>
    ptr_covers G' tn' q s' n
Proof
  rpt strip_tac >> gvs[ptr_covers_def] >>
  `off < dimword(:256)` by (simp[] >> decide_tac) >>
  simp[ptr_covers_def, w2n_add_2, w2n_n2w, arithmeticTheory.LESS_MOD] >>
  decide_tac
QED

(* This is only an interface counterexample, not an assignment counterexample. *)
Theorem assign_base_ptr_covers_wrap_witness:
  ?G tn s.
    lookup_var "p" s = SOME (n2w (dimword(:256)-32)) /\
    lookup_var "q" s = SOME (n2w (dimword(:256)-32) + 32w) /\
    FLOOKUP G "p" = SOME (dimword(:256)-32,96) /\
    FLOOKUP G "q" = SOME (dimword(:256)-32,96) /\
    op_taint tn (Var "p") = {} /\ op_taint tn (Var "q") = {} /\
    ptr_covers G tn "p" s 96 /\ ~ptr_covers G tn "q" s 32
Proof
  qexistsl [`FEMPTY |+ ("p",(dimword(:256)-32,96)) |+
                        ("q",(dimword(:256)-32,96))`,
            `entry_taint`,
            `ARB with vs_vars := FEMPTY |+ ("p",n2w (dimword(:256)-32)) |+
                    ("q",n2w (dimword(:256)-32) + 32w)`] >>
  simp[ptr_covers_def, lookup_var_def, op_taint_def, entry_taint_def,
       FLOOKUP_UPDATE, w2n_add_2, w2n_n2w, dimword_def] >> CONV_TAC wordsLib.WORD_EVAL_CONV >> EVAL_TAC
QED
