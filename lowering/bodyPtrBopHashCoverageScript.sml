Theory bodyPtrBopHashCoverage
Ancestors
  typedCopyPtr loweringPosts valueEncoding valueEncodingDefs allocationPtr exprLoweringProps

Theorem bop_bytes_payload_footprint:
  val_wf tv (BytesV bs) /\ tv <> BaseTV AddressT /\
  (!k. tv <> BaseTV (BytesT (Fixed k))) ==>
  32 + LENGTH bs <= val_footprint tv (BytesV bs)
Proof
  Cases_on `tv` >> simp[val_wf_def, val_footprint_def] >>
  Cases_on `b` >> simp[] >> Cases_on `b'` >> simp[]
QED

Theorem bop_string_payload_footprint:
  val_wf tv (StringV str) ==>
  32 + LENGTH str <= val_footprint tv (StringV str)
Proof
  Cases_on `tv` >> simp[val_wf_def, val_footprint_def] >>
  Cases_on `b` >> simp[]
QED

Theorem bop_bytes_payload_covers:
  stmt_state_rel ctx func cenv cx es s /\
  expr_val_at cenv cx t sa sb es (BytesV bs) (Var p) s /\
  ptr_val_ok cx t (BytesV bs) (Var p) G tn s /\
  evaluate_type (get_tenv cx) t = SOME tv /\ ~is_word_type t /\
  tv <> BaseTV AddressT /\ (!k. tv <> BaseTV (BytesT (Fixed k))) /\
  lookup_var p s = SOME w /\ lookup_var q s' = SOME (w + 32w) /\
  FLOOKUP G' q = FLOOKUP G p /\ op_taint tn' (Var q) = {} ==>
  0 < LENGTH bs ==> ptr_covers G' tn' q s' (LENGTH bs)
Proof
  rpt strip_tac >>
  `val_wf tv (BytesV bs)` by metis_tac[expr_val_at_def] >>
  `32 + LENGTH bs <= val_footprint tv (BytesV bs)` by
    metis_tac[bop_bytes_payload_footprint] >>
  drule_all expr_val_at_ptr_offset_read_covers >> simp[]
QED

Theorem bop_string_payload_covers:
  stmt_state_rel ctx func cenv cx es s /\
  expr_val_at cenv cx t sa sb es (StringV str) (Var p) s /\
  ptr_val_ok cx t (StringV str) (Var p) G tn s /\
  evaluate_type (get_tenv cx) t = SOME tv /\ ~is_word_type t /\
  lookup_var p s = SOME w /\ lookup_var q s' = SOME (w + 32w) /\
  FLOOKUP G' q = FLOOKUP G p /\ op_taint tn' (Var q) = {} ==>
  0 < LENGTH str ==> ptr_covers G' tn' q s' (LENGTH str)
Proof
  rpt strip_tac >>
  `val_wf tv (StringV str)` by metis_tac[expr_val_at_def] >>
  `32 + LENGTH str <= val_footprint tv (StringV str)` by
    metis_tac[bop_string_payload_footprint] >>
  drule_all expr_val_at_ptr_offset_read_covers >> simp[]
QED

Theorem bop_payload_offset_no_wrap:
  stmt_state_rel ctx func cenv cx es s /\
  expr_val_at cenv cx t sa sb es v (Var p) s /\
  evaluate_type (get_tenv cx) t = SOME tv /\ ~is_word_type t /\
  lookup_var p s = SOME w /\ 0 < n /\
  32 + n <= val_footprint tv v ==>
  w2n (w + 32w) = w2n w + 32
Proof
  rpt strip_tac >>
  `eval_operand (Var p) s = SOME w` by
    simp[venomStateTheory.eval_operand_def] >>
  `w2n w <= w2n w + 32 /\
   w2n w + 32 < w2n w + val_footprint tv v` by decide_tac >>
  `w2n w + 32 < s.vs_alloca_next` by
    (drule_all expr_val_at_below_frontier >> simp[]) >>
  `s.vs_alloca_next < dimword(:256)` by
    (irule alloca_room_next_lt >>
     fs[stmt_state_rel_def] >> metis_tac[]) >>
  simp[wordsTheory.w2n_add_2, wordsTheory.w2n_n2w,
       arithmeticTheory.LESS_MOD] >> decide_tac
QED
