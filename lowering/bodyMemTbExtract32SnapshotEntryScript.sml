(* Complete control and state boundary for the extract32 source snapshot. *)
Theory bodyMemTbExtract32SnapshotEntry
Ancestors
  bodyMemTbExtract32Cuts allocaHistoryFragment exprSimProps
  exprLoweringProps exprOperandVar builtinBytes emitHelper emitHelperProps
  compileEnv venomInst rich_list loweringPosts fragExec
  bodyMemTbExtract32Source fragGasSeqMem list venomState venomExecSemantics

Theorem extract32_snapshot_code[local]:
  compile_bytestring_src src sa = ((len,data),sb) ==>
  same_blocks sa sb /\
  sb.cs_current_insts = sa.cs_current_insts ++ emitted_insts sa sb /\
  LENGTH sb.cs_current_insts = LENGTH sa.cs_current_insts + 2
Proof
  simp[compile_bytestring_src_def, emit_op_def, comp_bind_def,
       comp_ignore_bind_def, comp_return_def, fresh_var_def, fresh_id_def, emit_def] >>
  strip_tac >> gvs[] >> simp[same_blocks_def, emitted_insts_def] >>
  pure_rewrite_tac[GSYM APPEND_ASSOC] >> simp[DROP_LENGTH_APPEND]
QED

Theorem extract32_snapshot_code_prefix[local]:
  compile_bytestring_src src sa = ((len,data),sb) /\
  fn_has_code sa sb func /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?bb rest. lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
    DROP s.vs_inst_idx bb.bb_instructions = emitted_insts sa sb ++ rest
Proof
  strip_tac >> drule extract32_snapshot_code >> strip_tac >>
  gvs[fn_has_code_def, same_blocks_def, IS_PREFIX_APPEND] >>
  qexists_tac `l` >> pure_rewrite_tac[GSYM APPEND_ASSOC] >>
  pure_rewrite_tac[DROP_LENGTH_APPEND] >> REFL_TAC
QED

Theorem extract32_snapshot_entry_frame:
  stmt_state_rel ctx func cenv cx es s /\ local_ptrs_reserved cenv sa /\
  (t with vs_vars := s.vs_vars) = s /\
  (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s) ==>
  stmt_state_rel ctx func cenv cx es (t with vs_inst_idx := n)
Proof
  strip_tac >>
  `t = s with vs_vars := t.vs_vars` by
    (qpat_x_assum `t with vs_vars := _ = s` (SUBST1_TAC o SYM) >> simp[]) >>
  `stmt_state_rel ctx func cenv cx es (s with vs_vars := t.vs_vars)` by
    (irule stmt_state_rel_vars_frame >> simp[] >> rpt strip_tac >>
     `not_fresh_at sa p` by (fs[local_ptrs_reserved_def] >> metis_tac[]) >>
     metis_tac[]) >>
  simp[stmt_state_rel_inst_idx] >> metis_tac[]
QED

Theorem extract32_snapshot_entry[local]:
  compile_bytestring_src src sa = ((len_op,data_op),sb) /\
  fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
  local_ptrs_reserved cenv sa /\ stmt_state_rel ctx func cenv cx es s /\
  alloca_history func s /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  (!x. src = Var x ==> not_fresh_at sa x) /\
  eval_operand src s = SOME (n2w b) /\
  mem_word_at b s.vs_memory = n2w len /\
  b + 32 < dimword (:256) /\ len < dimword (:256) /\
  b + 32 + len <= s.vs_alloca_next ==>
  ?u. gas_path_mem ctx func s 0 (OK u) /\
    stmt_state_rel ctx func cenv cx es u /\ alloca_history func u /\
    ~u.vs_halted /\ u.vs_current_bb = sb.cs_current_bb /\
    u.vs_inst_idx = LENGTH sb.cs_current_insts /\
    local_ptrs_reserved cenv sb /\
    eval_operand len_op u = SOME (n2w len) /\
    eval_operand data_op u = SOME (n2w (b + 32)) /\
    w2n (n2w (b + 32):bytes32) + w2n (n2w len:bytes32) <= u.vs_alloca_next /\
    (u with <|vs_vars := s.vs_vars; vs_inst_idx := s.vs_inst_idx|>) = s /\
    (!x. not_fresh_at sa x ==> lookup_var x u = lookup_var x s) /\
    (!x. len_op = Var x \/ data_op = Var x ==> not_fresh_at sb x)
Proof
  strip_tac >> drule_all extract32_snapshot_code_prefix >> strip_tac >>
  drule extract32_snapshot_code >> strip_tac >>
  drule extract32_snapshot_shape >> strip_tac >>
  drule_all extract32_source_snapshot >> strip_tac >>
  `alloca_inv s` by fs[stmt_state_rel_def] >>
  `EVERY (\i. ~is_terminator i.inst_opcode) (emitted_insts sa sb)` by
    fs[EVERY_MEM] >>
  drule_all alloca_history_run_inst_seq >> strip_tac >>
  `isPREFIX (emitted_insts sa sb) (DROP s.vs_inst_idx bb.bb_instructions)` by
    simp[IS_PREFIX_APPEND] >>
  `gas_path_mem ctx func s 0 (OK (t with vs_inst_idx := s.vs_inst_idx + 2))` by
    (drule_all run_inst_seq_gas_path_mem >> simp[]) >>
  `stmt_state_rel ctx func cenv cx es (t with vs_inst_idx := s.vs_inst_idx + 2)` by
    (irule extract32_snapshot_entry_frame >> goal_assum (drule_at Any) >> simp[]) >>
  `local_ptrs_reserved cenv sb` by
    (irule compiler_ci_mono_reserved >> qexists_tac `sa` >> simp[] >>
     metis_tac[ci_mono_compile_bytestring_src, pairTheory.SND]) >>
  `t.vs_halted = s.vs_halted` by
    (qpat_x_assum `t with vs_vars := _ = s`
       (mp_tac o Q.AP_TERM `\u. u.vs_halted`) >> simp[]) >>
  `t.vs_current_bb = s.vs_current_bb` by
    (qpat_x_assum `t with vs_vars := _ = s`
       (mp_tac o Q.AP_TERM `\u. u.vs_current_bb`) >> simp[]) >>
  `t.vs_inst_idx = s.vs_inst_idx` by
    (qpat_x_assum `t with vs_vars := _ = s`
       (mp_tac o Q.AP_TERM `\u. u.vs_inst_idx`) >> simp[]) >>
  qexists_tac `t with vs_inst_idx := s.vs_inst_idx + 2` >>
  gvs[same_blocks_def, eval_operand_def, lookup_var_def] >>
  reverse conj_tac >- metis_tac[] >>
  gvs[venom_state_component_equality]
QED

Theorem extract32_source_snapshot_entry:
  expr_post ctx func cenv cx e es s0c sa s0 es' (BytesV bs) src s /\
  expr_type e = BaseT (BytesT (Dynamic cap)) /\
  evaluate_type (get_tenv cx) (expr_type e) = SOME (BaseTV (BytesT (Dynamic cap))) /\
  expr_store_bound cx (expr_type e) (BytesV bs) src s /\
  compile_bytestring_src src sa = ((len_op,data_op),sb) /\
  fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
  local_ptrs_reserved cenv sa /\ alloca_history func s /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  (!x. src = Var x ==> not_fresh_at sa x) ==>
  ?b u. gas_path_mem ctx func s 0 (OK u) /\
    stmt_state_rel ctx func cenv cx es' u /\ alloca_history func u /\
    ~u.vs_halted /\ u.vs_current_bb = sb.cs_current_bb /\
    u.vs_inst_idx = LENGTH sb.cs_current_insts /\ local_ptrs_reserved cenv sb /\
    eval_operand len_op u = SOME (n2w (LENGTH bs)) /\
    eval_operand data_op u = SOME (n2w (b + 32)) /\
    mem_bytes_at (b + 32) (LENGTH bs) u.vs_memory = bs /\
    b + 32 < dimword (:256) /\ LENGTH bs < dimword (:256) /\
    w2n (n2w (b + 32):bytes32) + w2n (n2w (LENGTH bs):bytes32) <= u.vs_alloca_next /\
    (u with <|vs_vars := s.vs_vars; vs_inst_idx := s.vs_inst_idx|>) = s /\
    (!x. not_fresh_at sa x ==> lookup_var x u = lookup_var x s) /\
    (!x. len_op = Var x \/ data_op = Var x ==> not_fresh_at sb x)
Proof
  strip_tac >> drule_all extract32_source_post_view >> strip_tac >>
  `stmt_state_rel ctx func cenv cx es' s` by fs[expr_post_def] >>
  drule_all extract32_snapshot_entry >> strip_tac >>
  `u.vs_memory = s.vs_memory` by
    (qpat_x_assum `u with <|vs_vars := _; vs_inst_idx := _|> = s`
       (mp_tac o Q.AP_TERM `\v. v.vs_memory`) >> simp[]) >>
  qexistsl_tac [`b`,`u`] >> simp[] >> metis_tac[]
QED
