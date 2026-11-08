Theory bodyPtrBopHashSemantic
Ancestors
  bodyPtrBopHashRun bodyPtrBopHashFootprint bodyPtrBopHashCoverage
  bodyPtrDefs exprSimProps loweringPosts valueEncoding venomState

Theorem bop_hash_semantic_ranges:
  stmt_state_rel ctx func cenv cx es s /\
  expr_val_at cenv cx ty sa sb es v (Var p) s /\
  ptr_val_ok cx ty v (Var p) G tn s /\
  evaluate_type (get_tenv cx) ty = SOME tv /\ ~is_word_type ty /\
  lookup_var p s = SOME w /\ 32 + n <= val_footprint tv v ==>
  ptr_covers G tn p s 32 /\
  ?b sz. FLOOKUP G p = SOME (b,sz) /\
    (0 < n ==> b <= w2n (w + 32w) /\ w2n (w + 32w) + n <= b + sz)
Proof
  strip_tac >>
  `ptr_mem_ok cx ty v (Var p) G tn s /\ op_taint tn (Var p) = {}` by
    gvs[ptr_val_ok_def] >>
  `eval_operand (Var p) s = SOME w` by simp[eval_operand_def] >>
  `val_footprint tv v <> 0` by decide_tac >>
  drule_all ptr_mem_ok_bounds >> strip_tac >> gvs[] >>
  qspecl_then [`tv`, `v`] assume_tac val_footprint_le_store_size >>
  conj_tac
  >- (simp[ptr_covers_def, eval_operand_def] >>
      goal_assum (drule_at Any) >> decide_tac) >>
  strip_tac >>
  `32 + n <= val_footprint tv v` by decide_tac >>
  `w2n (w + 32w) = w2n w + 32` by
    (drule_all bop_payload_offset_no_wrap >> simp[]) >>
  simp[] >> decide_tac
QED

Theorem bop_bytes_hash_run_ptr:
  p <> q /\ l <> q /\ ~ctx_has_dalloca ctx /\
  stmt_state_rel ctx func cenv cx es s /\
  expr_val_at cenv cx ty sa sb es (BytesV bs) (Var p) s /\
  ptr_val_ok cx ty (BytesV bs) (Var p) G tn s /\
  evaluate_type (get_tenv cx) ty = SOME tv /\ ~is_word_type ty /\
  tv <> BaseTV AddressT /\ (!k. tv <> BaseTV (BytesT (Fixed k))) /\
  lookup_var p s = SOME w /\ LENGTH bs < dimword(:256) /\
  iA = mk_inst aId ADD [Var p; Lit 32w] [q] /\
  iL = mk_inst lId MLOAD [Var p] [l] /\
  iH = mk_inst hId SHA3 [Var q; Var l] [h] /\
  ~s.vs_halted /\
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  isPREFIX [iA;iL;iH] (DROP s.vs_inst_idx bb.bb_instructions) /\
  run_inst_seq [iA;iL;iH] s = OK t ==>
  ?G' tn'.
    gas_path_ptr D 0 ctx fn PG G tn s 0 G' tn'
      (OK (t with vs_inst_idx := s.vs_inst_idx + 3)) /\
    op_prov G' (Var h) = NONE /\ op_taint tn' (Var h) = {} /\
    tn'.t_mem = tn.t_mem /\ tn'.t_stor = tn.t_stor /\ tn'.t_trans = tn.t_trans /\
    (!x. x <> q /\ x <> l /\ x <> h ==>
      FLOOKUP G' x = FLOOKUP G x /\ FLOOKUP tn'.t_var x = FLOOKUP tn.t_var x)
Proof
  strip_tac >>
  `val_wf tv (BytesV bs)` by metis_tac[expr_val_at_def] >>
  `32 + LENGTH bs <= val_footprint tv (BytesV bs)` by
    metis_tac[bop_bytes_payload_footprint] >>
  drule_all bop_hash_semantic_ranges >> strip_tac >>
  `ptr_mem_ok cx ty (BytesV bs) (Var p) G tn s` by
    gvs[ptr_val_ok_def] >>
  `eval_operand (Var p) s = SOME w` by simp[eval_operand_def] >>
  drule_all ptr_mem_ok_bytes_length >> strip_tac >>
  drule_all ptr_mem_ok_bytes_clean >> strip_tac >>
  `!i. w2n (w + 32w) <= i /\ i < w2n (w + 32w) + LENGTH bs ==>
       i NOTIN tn.t_mem` by
    (Cases_on `LENGTH bs = 0` >- simp[] >>
     `0 < LENGTH bs` by decide_tac >>
     drule_all bop_payload_offset_no_wrap >> simp[]) >>
  drule_all bop_hash_run_ptr >>
  disch_then (qspecl_then [`PG`, `D`] strip_assume_tac) >>
  goal_assum (drule_at Any) >> simp[]
QED

Theorem bop_string_hash_run_ptr:
  p <> q /\ l <> q /\ ~ctx_has_dalloca ctx /\
  stmt_state_rel ctx func cenv cx es s /\
  expr_val_at cenv cx ty sa sb es (StringV str) (Var p) s /\
  ptr_val_ok cx ty (StringV str) (Var p) G tn s /\
  evaluate_type (get_tenv cx) ty = SOME tv /\ ~is_word_type ty /\
  lookup_var p s = SOME w /\ LENGTH str < dimword(:256) /\
  iA = mk_inst aId ADD [Var p; Lit 32w] [q] /\
  iL = mk_inst lId MLOAD [Var p] [l] /\
  iH = mk_inst hId SHA3 [Var q; Var l] [h] /\
  ~s.vs_halted /\
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  isPREFIX [iA;iL;iH] (DROP s.vs_inst_idx bb.bb_instructions) /\
  run_inst_seq [iA;iL;iH] s = OK t ==>
  ?G' tn'.
    gas_path_ptr D 0 ctx fn PG G tn s 0 G' tn'
      (OK (t with vs_inst_idx := s.vs_inst_idx + 3)) /\
    op_prov G' (Var h) = NONE /\ op_taint tn' (Var h) = {} /\
    tn'.t_mem = tn.t_mem /\ tn'.t_stor = tn.t_stor /\ tn'.t_trans = tn.t_trans /\
    (!x. x <> q /\ x <> l /\ x <> h ==>
      FLOOKUP G' x = FLOOKUP G x /\ FLOOKUP tn'.t_var x = FLOOKUP tn.t_var x)
Proof
  strip_tac >>
  `val_wf tv (StringV str)` by metis_tac[expr_val_at_def] >>
  `32 + LENGTH str <= val_footprint tv (StringV str)` by
    metis_tac[bop_string_payload_footprint] >>
  drule_all bop_hash_semantic_ranges >> strip_tac >>
  `ptr_mem_ok cx ty (StringV str) (Var p) G tn s` by
    gvs[ptr_val_ok_def] >>
  `eval_operand (Var p) s = SOME w` by simp[eval_operand_def] >>
  drule_all ptr_mem_ok_string_length >> strip_tac >>
  drule_all ptr_mem_ok_string_clean >> strip_tac >>
  `!i. w2n (w + 32w) <= i /\ i < w2n (w + 32w) + LENGTH str ==>
       i NOTIN tn.t_mem` by
    (Cases_on `LENGTH str = 0` >- simp[] >>
     `0 < LENGTH str` by decide_tac >>
     drule_all bop_payload_offset_no_wrap >> simp[]) >>
  drule_all bop_hash_run_ptr >>
  disch_then (qspecl_then [`PG`, `D`] strip_assume_tac) >>
  goal_assum (drule_at Any) >> simp[]
QED
