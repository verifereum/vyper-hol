(* The semantic placement post, not arbitrary ghost coverage, rules out
   payload ADD wrap.  Reuse the general footprint bound at its owner. *)
Theory bodyPtrSignedConvertFrame
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
