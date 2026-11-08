(* Fixed-byte hashing writes a clean word to a 32-byte scratch allocation. *)
Theory bodyPtrEnvBuiltinsFixedHash
Ancestors bodyPtrEnvBuiltinsSelectorSuffix bodyPtrEnvBuiltinsMemoryHash
  bodyPtrEnvBuiltinsSelectorBuffer bodyPtrEnvBuiltinsEdges bodyPtrEnvBuiltinsHashStep
  bodyPtrEnvBuiltinsGhostCompose bodyPtrEnvBuiltinsAllocation loweringHalt
  typedCopyPtr allocationPtr
  fragExecPtr fragGasSeqPtr fragGasPathPtr bodyPtrDefs ptrDiscipline venomInst venomState
  venomExecSemantics instIdxIndep compileEnv exprSimProps exprLoweringProps
  finite_map pred_set words list

Theorem fixed_hash_store_certificate:
  ptr_covers G tn p s 32 /\ lookup_var p s = SOME a /\
  eval_operand value s = SOME w /\ op_taint tn value = {} /\
  ghost_inv d cenv cx es G tn s /\ local_ptrs_rel fn cenv es.scopes s /\
  ghost_kept cenv es0 sa G0 tn0 s0 G tn /\
  (!name b sz. local_region cenv es.scopes s name b sz ==>
     b+sz <= w2n a \/ w2n a+32 <= b) /\
  ~ctx_has_dalloca ctx /\
  u = mstore (w2n a) w s /\
  tn1 = step_taint (mk_inst id MSTORE [Var p; value] []) s u tn ==>
  inst_seq_ptr D 0 ctx fn PG G tn [mk_inst id MSTORE [Var p; value] []] s G tn1 /\
  ghost_inv d cenv cx es G tn1 u /\
  ghost_kept cenv es0 sa G0 tn0 s0 G tn1 /\
  ptr_covers G tn1 p u 32 /\ lookup_var p u = SOME a /\
  (!i. w2n a <= i /\ i < w2n a+32 ==> i NOTIN tn1.t_mem)
Proof
  strip_tac >> drule_all mstore_ghost_frame >>
  disch_then (qspecl_then [`PG`, `G`, `id`] strip_assume_tac) >>
  `tn1.t_imm = tn.t_imm` by simp[mstore_imm_taint] >>
  conj_tac >- suspend "checks" >>
  conj_tac
  >- (gvs[] >> irule ghost_inv_mstore_clean >> simp[] >> metis_tac[]) >>
  conj_tac
  >- (irule ghost_kept_clean_suffix >> qexistsl_tac [`G`, `tn`] >>
      simp[op_taint_def, SUBSET_DEF] >> gvs[]) >>
  conj_tac >- gvs[ptr_covers_def, op_taint_def, lookup_var_def, mstore_def] >>
  conj_tac >- gvs[lookup_var_def, mstore_def] >> gvs[IN_DIFF]
QED

Resume fixed_hash_store_certificate[checks]:
  `step_inst_base (mk_inst id MSTORE [Var p; value] []) s = OK u` by
    (PURE_ONCE_REWRITE_TAC[step_inst_base_def] >>
     simp[mk_inst_def, exec_write2_def, eval_operand_def]) >>
  simp[Once inst_seq_ptr_def] >> conj_tac
  >- (irule ptr_inst_ok_mstore >> simp[]) >>
  simp[mk_inst_def, is_terminator_def, inst_seq_ptr_def] >> gvs[]
QED

Finalise fixed_hash_store_certificate

Theorem fixed_hash_tail_certificate:
  code = [mk_inst sid MSTORE [Var p; value] [];
          mk_inst hid SHA3 [Var p; Lit (n2w m)] [out]] /\
  ptr_covers G tn p s 32 /\ lookup_var p s = SOME a /\ m <= 32 /\
  eval_operand value s = SOME w /\ op_taint tn value = {} /\
  ghost_inv d cenv cx es G tn s /\ local_ptrs_rel fn cenv es.scopes s /\
  ghost_kept cenv es0 sa G0 tn0 s0 G tn /\
  (!name b sz. local_region cenv es.scopes s name b sz ==>
     b+sz <= w2n a \/ w2n a+32 <= b) /\
  local_ptrs_reserved cenv sa /\ ~not_fresh_at sa out /\
  (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  ~ctx_has_dalloca ctx /\ run_inst_seq code s = OK t ==>
  ?G' tn'. inst_seq_ptr D 0 ctx fn PG G tn code (s with vs_inst_idx := k) G' tn' /\
    ptr_val_ok cx (BaseT (BytesT (Fixed 32))) result (Var out) G' tn' t /\
    ghost_inv d cenv cx es G' tn' t /\
    ghost_kept cenv es0 sa G0 tn0 s0 G' tn'
Proof
  strip_tac >>
  qabbrev_tac `u = mstore (w2n a) w s` >>
  qabbrev_tac `tn1 = step_taint (mk_inst sid MSTORE [Var p; value] []) s u tn` >>
  `inst_seq_ptr D 0 ctx fn PG G tn [mk_inst sid MSTORE [Var p; value] []] s G tn1 /\
   ghost_inv d cenv cx es G tn1 u /\ ghost_kept cenv es0 sa G0 tn0 s0 G tn1 /\
   ptr_covers G tn1 p u 32 /\ lookup_var p u = SOME a /\
   (!i. w2n a <= i /\ i < w2n a+32 ==> i NOTIN tn1.t_mem)` by
    (irule fixed_hash_store_certificate >> simp[Abbr `u`, Abbr `tn1`] >> metis_tac[]) >>
  `step_inst_base (mk_inst sid MSTORE [Var p; value] []) s = OK u` by
    (PURE_ONCE_REWRITE_TAC[step_inst_base_def] >>
     simp[mk_inst_def, exec_write2_def, eval_operand_def, Abbr `u`]) >>
  `step_inst_base (mk_inst hid SHA3 [Var p; Lit (n2w m)] [out]) u = OK t` by
    (qpat_x_assum `run_inst_seq _ _ = _` mp_tac >> simp[run_inst_seq_def, AllCaseEqs()]) >>
  qexistsl_tac [`step_prov PG G (mk_inst hid SHA3 [Var p; Lit (n2w m)] [out]) t`,
    `step_taint (mk_inst hid SHA3 [Var p; Lit (n2w m)] [out]) u t tn1`] >>
  conj_tac >- suspend "checks" >>
  conj_tac >- irule hash_output_clean >>
  `?w. t = update_var out w u` by
    (qpat_x_assum `step_inst_base (mk_inst hid _ _ _) _ = _` mp_tac >>
     PURE_ONCE_REWRITE_TAC[step_inst_base_def] >>
     simp[mk_inst_def, AllCaseEqs()] >> metis_tac[]) >>
  gvs[] >> irule hash_update_ghosts >> simp[]
QED

Resume fixed_hash_tail_certificate[checks]:
  `m < dimword (:256)` by (simp[dimword_def] >> decide_tac) >>
  `ptr_inst_ok D 0 0 ctx fn G tn1
     (mk_inst hid SHA3 [Var p; Lit (n2w m)] [out]) u` by
    (irule hash_covered_payload_ok >> simp[eval_operand_def, op_taint_def] >>
     gvs[ptr_covers_def] >> decide_tac) >>
  qpat_x_assum `inst_seq_ptr _ _ _ _ _ _ _ [_] _ _ _` mp_tac >>
  simp[inst_seq_ptr_def, mk_inst_def, is_terminator_def] >> strip_tac >>
  simp[Once inst_seq_ptr_def, step_inst_inst_idx_indep, exec_result_map_def] >>
  gvs[mk_inst_def, is_terminator_def, inst_seq_ptr_def, Abbr `tn1`,
      step_inst_inst_idx_indep, exec_result_map_def] >>
  qpat_x_assum `G = step_prov _ _ _ _` (fn th => rewrite_tac[GSYM th]) >>
  pure_rewrite_tac[GSYM mk_inst_def] >> conj_tac
  >- (irule ptr_inst_ok_mstore >>
      gvs[ptr_covers_def, op_taint_def, lookup_var_def]) >>
  irule hash_covered_payload_ok >>
  simp[eval_operand_def, op_taint_def, ptr_covers_def, lookup_var_def] >>
  gvs[ptr_covers_def, op_taint_def, lookup_var_def, mk_inst_def] >>
  rpt gen_tac >> disch_tac >> first_x_assum irule >> decide_tac
QED

Finalise fixed_hash_tail_certificate

Theorem fixed_hash_prefix_certificate:
  code = [mk_inst ia ALLOCA [Lit 32w] [p];
          mk_inst sid MSTORE [Var p; value] [];
          mk_inst hid SHA3 [Var p; Lit (n2w m)] [out]] /\
  stmt_state_rel ctx fn cenv cx es s /\ ghost_inv d cenv cx es G tn s /\
  fn_inst_ids_distinct fn /\
  MEM (mk_inst ia ALLOCA [Lit 32w] [p]) (fn_insts fn) /\
  ~ctx_has_dalloca ctx /\ local_ptrs_reserved cenv sa /\
  ~not_fresh_at sa p /\ ~not_fresh_at sa out /\
  (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!x. value = Var x ==> x <> p) /\ m <= 32 /\
  eval_operand value s = SOME w /\ op_taint tn value = {} /\
  run_inst_seq code s = OK t ==>
  ?G' tn'. inst_seq_ptr D 0 ctx fn PG G tn code s G' tn' /\
    ptr_val_ok cx (BaseT (BytesT (Fixed 32))) result (Var out) G' tn' t /\
    ghost_inv d cenv cx es G' tn' t /\
    ghost_kept cenv es sa G tn s G' tn'
Proof
  strip_tac >> gvs[] >>
  qpat_x_assum `run_inst_seq _ _ = _` mp_tac >>
  simp[Once run_inst_seq_def] >>
  Cases_on `step_inst_base (mk_inst ia ALLOCA [Lit 32w] [p]) s` >>
  simp[] >> strip_tac >> rename1 `step_inst_base _ s = OK s1` >>
  `32 < dimword (:256)` by simp[dimword_def] >>
  drule_all builtin_allocation_certificate >>
  disch_then (qspecl_then [`PG`, `D`] strip_assume_tac) >>
  `local_ptrs_rel fn cenv es.scopes s1` by
    fs[stmt_state_rel_def, state_rel_def] >>
  `eval_operand value s1 = SOME w /\ op_taint tn1 value = {}` by
    suspend "value_frame" >>
  `?G' tn'. inst_seq_ptr D 0 ctx fn PG G1 tn1
     [mk_inst sid MSTORE [Var p; value] [];
      mk_inst hid SHA3 [Var p; Lit (n2w m)] [out]]
     (s1 with vs_inst_idx := SUC s.vs_inst_idx) G' tn' /\
     ptr_val_ok cx (BaseT (BytesT (Fixed 32))) result (Var out) G' tn' t /\
     ghost_inv d cenv cx es G' tn' t /\
     ghost_kept cenv es sa G tn s G' tn'` by
    (drule_at (Pat `run_inst_seq _ _ = _`) fixed_hash_tail_certificate >>
     disch_then irule >> simp[eval_operand_def] >>
     qexists_tac `n2w b` >> fs[eval_operand_def] >> metis_tac[]) >>
  qexistsl_tac [`G'`, `tn'`] >> simp[] >>
  qpat_x_assum `inst_seq_ptr _ _ _ _ _ _ _ [_] _ _ _`
    (strip_assume_tac o SRULE [inst_seq_ptr_def]) >>
  PURE_ONCE_REWRITE_TAC[inst_seq_ptr_def] >> gvs[]
QED

Resume fixed_hash_prefix_certificate[value_frame]:
  drule_all alloca_step_frame_effects >>
  disch_then (qspecl_then [`PG`, `G`, `tn`] strip_assume_tac) >>
  qpat_x_assum `inst_seq_ptr _ _ _ _ _ _ _ [_] _ _ _` mp_tac >>
  simp[inst_seq_ptr_def] >> strip_tac >>
  qspecl_then [`ia`, `32w`, `p`, `s`] strip_assume_tac step_alloca_frame >>
  gvs[] >> Cases_on `value` >> gvs[eval_operand_def, op_taint_def] >>
  metis_tac[op_taint_def]
QED

Finalise fixed_hash_prefix_certificate

Theorem fixed_hash_prefix_counted:
  code = [mk_inst ia ALLOCA [Lit 32w] [p];
          mk_inst sid MSTORE [Var p; value] [];
          mk_inst hid SHA3 [Var p; Lit (n2w m)] [out]] /\
  stmt_state_rel ctx fn cenv cx es s /\ ghost_inv d cenv cx es G tn s /\
  fn_inst_ids_distinct fn /\
  MEM (mk_inst ia ALLOCA [Lit 32w] [p]) (fn_insts fn) /\
  ~ctx_has_dalloca ctx /\ local_ptrs_reserved cenv sa /\
  ~not_fresh_at sa p /\ ~not_fresh_at sa out /\
  (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!x. value = Var x ==> x <> p) /\ m <= 32 /\
  eval_operand value s = SOME w /\ op_taint tn value = {} /\
  ~s.vs_halted /\ lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  isPREFIX code (DROP s.vs_inst_idx bb.bb_instructions) /\
  run_inst_seq code s = OK t ==>
  ?G' tn'. gas_path_ptr D 0 ctx fn PG G tn s 0 G' tn'
    (OK (t with vs_inst_idx := s.vs_inst_idx + LENGTH code)) /\
    ptr_val_ok cx (BaseT (BytesT (Fixed 32))) result (Var out) G' tn' t /\
    ghost_inv d cenv cx es G' tn' t /\ ghost_kept cenv es sa G tn s G' tn'
Proof
  strip_tac >>
  drule_at (Pat `_ = [_;_;_]`) fixed_hash_prefix_certificate >>
  disch_then drule_all >> disch_then (qspecl_then [`result`, `PG`, `D`] strip_assume_tac) >>
  qexistsl_tac [`G'`, `tn'`] >> simp[] >>
  `EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode) code` by
    simp[mk_inst_def, is_terminator_def] >>
  drule_all run_inst_seq_gas_path_ptr >> simp[mk_inst_def]
QED
