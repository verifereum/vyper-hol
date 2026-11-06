(* The semantic placement post, not arbitrary ghost coverage, rules out
   payload ADD wrap.  Reuse the general footprint bound at its owner. *)
Theory bodyPtrTypeBuiltinsFrameProbe
Ancestors stmtSimReturn words arithmetic

Theorem expr_val_at_payload_nonwrap:
  stmt_state_rel ctx func cenv cx es s /\
  expr_val_at cenv cx t sa sb es v op s /\
  evaluate_type (get_tenv cx) t = SOME tv /\ ~is_word_type t /\
  eval_operand op s = SOME w /\ 32 <= val_footprint tv v ==>
  w2n w + 32 < dimword(:256)
Proof
  rpt strip_tac >> drule_all expr_val_at_bound >> decide_tac
QED

Theorem wrapped_payload_address:
  (n2w (dimword(:256)-32) : 256 word) + 32w = 0w /\
  ~(w2n (n2w (dimword(:256)-32) : 256 word) + 32 < dimword(:256))
Proof
  simp[wordsTheory.dimword_def, wordsTheory.word_add_n2w,
       wordsTheory.word_2comp_n2w, wordsTheory.n2w_11] >> EVAL_TAC
QED

Theorem expr_val_at_excludes_wrapped_payload:
  stmt_state_rel ctx func cenv cx es s /\
  expr_val_at cenv cx t sa sb es v op s /\
  evaluate_type (get_tenv cx) t = SOME tv /\ ~is_word_type t /\
  32 <= val_footprint tv v ==>
  eval_operand op s <> SOME (n2w (dimword(:256)-32))
Proof
  rpt strip_tac >> drule_all expr_val_at_payload_nonwrap >>
  simp[wrapped_payload_address]
QED
