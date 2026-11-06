(* Result-post composition across extract32's readonly snapshot and suffix. *)
Theory bodyMemTbExtract32SuffixPost
Ancestors
  bodyMemTbExtract32TypedSuffix bodyMemTbExtract32SnapshotEntry
  exprSimWordArgs exprSimProps exprSimHash exprLoweringProps
  loweringPosts compileEnv venomState venomExecSemantics list finite_map
  vyperTypeConversions exprSimMemDefs fragExec rich_list allocaHistoryFragment
  bodyMemTbExtract32Readonly

Theorem extract32_operands_frame:
  expr_post ctx func cenv cx src es sa s1 s0 es1 v1 src_op s /\
  expr_post ctx func cenv cx off es1 s2 s3 u es2 v2 off_op t /\
  stmt_state_rel ctx func cenv cx es s0 /\ local_ptrs_reserved cenv sa /\
  MAP FDOM es.scopes = MAP FDOM es1.scopes /\
  ci_mono sa s1 /\ ci_mono s1 s2 /\
  (u with <|vs_vars := s.vs_vars; vs_inst_idx := s.vs_inst_idx|>) = s /\
  (!x. not_fresh_at s1 x ==> lookup_var x u = lookup_var x s) ==>
  wb_frame cenv es sa s0 t
Proof
  strip_tac >>
  `wb_frame cenv es sa s0 s` by metis_tac[expr_post_frame] >>
  `u.vs_memory = s.vs_memory /\ u.vs_allocas = s.vs_allocas` by
    (qpat_x_assum `u with <|vs_vars := _; vs_inst_idx := _|> = s` mp_tac >>
     simp[venom_state_component_equality]) >>
  `wb_frame cenv es sa s0 u` by
    (irule wb_frame_readonly_tail >> goal_assum (drule_at Any) >>
     qexists_tac `s1` >> fs[ci_mono_def] >> metis_tac[]) >>
  `wb_frame cenv es1 s2 u t` by metis_tac[expr_post_frame] >>
  irule wb_frame_trans >> goal_assum (drule_at Any) >>
  fs[ci_mono_def] >> metis_tac[arithmeticTheory.LESS_EQ_TRANS]
QED

Theorem extract32_suffix_word_post:
  stmt_state_rel ctx func cenv cx es' s /\ wb_frame cenv es sa s0 s /\
  local_ptrs_reserved cenv sm /\ sa.cs_next_var <= sm.cs_next_var /\
  t = s with vs_vars := t.vs_vars /\
  (!x. not_fresh_at sm x ==> lookup_var x t = lookup_var x s) /\
  eval_operand op t = SOME (typed_val_to_w256 (BaseTV bt) v) /\
  expr_type e = BaseT bt /\ is_word_type (BaseT bt) ==>
  vv_post ctx func cenv cx e es sa sb s0 es' (Value v) (StackValue (BaseT bt) op)
    (t with vs_inst_idx := n) /\
  vv_store_bound cx (BaseT bt) lt es' (Value v) (StackValue (BaseT bt) op)
    (t with vs_inst_idx := n)
Proof
  strip_tac >>
  `(t with vs_vars := s.vs_vars) = s` by
    (qpat_x_assum `t = s with vs_vars := _` SUBST1_TAC >> simp[]) >>
  `stmt_state_rel ctx func cenv cx es' (t with vs_inst_idx := n)` by
    (irule extract32_snapshot_entry_frame >> goal_assum (drule_at Any) >>
     qexists_tac `sm` >> simp[]) >>
  `wb_frame cenv es sa s0 (t with vs_inst_idx := n)` by
    (irule wb_frame_readonly_tail >> goal_assum (drule_at Any) >>
     qexists_tac `s` >> simp[lookup_var_def] >>
     qpat_x_assum `t = s with vs_vars := _` SUBST1_TAC >>
     fs[lookup_var_def]) >>
  conj_tac
  >- (irule vv_post_word_intro >> simp[] >>
      metis_tac[evaluate_type_BaseT_SOME]) >>
  simp[exprSimMemDefsTheory.vv_store_bound_def]
QED

Theorem extract32_load_code[local]:
  compile_extract32_load l d off sa = (op,sb) ==>
  same_blocks sa sb /\
  sb.cs_current_insts = sa.cs_current_insts ++ emitted_insts sa sb
Proof
  simp[builtinBytesTheory.compile_extract32_load_def,
       builtinBytesTheory.compile_assert_slice_bounds_def,
       emitHelperTheory.emit_op_def, emitHelperTheory.emit_void_def,
       compileEnvTheory.comp_bind_def, compileEnvTheory.comp_ignore_bind_def,
       compileEnvTheory.comp_return_def, compileEnvTheory.fresh_var_def,
       compileEnvTheory.fresh_id_def, compileEnvTheory.emit_def] >>
  strip_tac >> gvs[] >> simp[same_blocks_def, emitted_insts_def] >>
  pure_rewrite_tac[GSYM APPEND_ASSOC] >> simp[rich_listTheory.DROP_LENGTH_APPEND]
QED

Theorem extract32_clamp_code[local]:
  !v ty sa op sb. compile_clamp_basetype v ty sa = (op,sb) ==>
  same_blocks sa sb /\
  sb.cs_current_insts = sa.cs_current_insts ++ emitted_insts sa sb
Proof
  recInduct exprLoweringTheory.compile_clamp_basetype_ind >>
  rpt conj_tac >> rpt gen_tac >>
  simp[exprLoweringTheory.compile_clamp_basetype_def,
       exprLoweringTheory.clamp_and_return_def, exprLoweringTheory.compile_clamp_def,
       emitHelperTheory.emit_op_def, emitHelperTheory.emit_void_def,
       compileEnvTheory.comp_bind_def, compileEnvTheory.comp_ignore_bind_def,
       compileEnvTheory.comp_return_def, compileEnvTheory.fresh_var_def,
       compileEnvTheory.fresh_id_def, compileEnvTheory.emit_def] >>
  rpt IF_CASES_TAC >> rpt strip_tac >>
  gvs[compileEnvTheory.type_bounds_def, compileEnvTheory.is_signed_type_def,
      compileEnvTheory.comp_bind_def, compileEnvTheory.comp_ignore_bind_def,
      compileEnvTheory.comp_return_def, compileEnvTheory.fresh_var_def,
      compileEnvTheory.fresh_id_def, compileEnvTheory.emit_def] >>
  simp[same_blocks_def, emitted_insts_def] >>
  pure_rewrite_tac[GSYM APPEND_ASSOC] >> simp[rich_listTheory.DROP_LENGTH_APPEND]
QED

Theorem extract32_suffix_code_prefix[local]:
  compile_extract32_load l d off sa = (raw,sc) /\
  compile_clamp_basetype raw (BaseT bt) sc = (op,sb) /\
  fn_has_code sa sb func /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?bb rest. lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
    DROP s.vs_inst_idx bb.bb_instructions =
      (emitted_insts sa sc ++ emitted_insts sc sb) ++ rest /\
    LENGTH sb.cs_current_insts = s.vs_inst_idx +
      LENGTH (emitted_insts sa sc ++ emitted_insts sc sb) /\
    sb.cs_current_bb = sa.cs_current_bb
Proof
  strip_tac >> drule extract32_load_code >> strip_tac >>
  drule extract32_clamp_code >> strip_tac >>
  gvs[fn_has_code_def, same_blocks_def, IS_PREFIX_APPEND] >>
  qexists_tac `l'` >>
  pure_rewrite_tac[GSYM APPEND_ASSOC] >>
  pure_rewrite_tac[rich_listTheory.DROP_LENGTH_APPEND] >> simp[]
QED

Theorem extract32_suffix_success_entry:
  compile_extract32_load l d off sa = (raw,sc) /\
  compile_clamp_basetype raw (BaseT bt) sc = (op,sb) /\
  code = emitted_insts sa sc ++ emitted_insts sc sb /\
  fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\ alloca_history func s /\
  stmt_state_rel ctx func cenv cx es' s /\ wb_frame cenv es s0c s0 s /\
  local_ptrs_reserved cenv sa /\ s0c.cs_next_var <= sa.cs_next_var /\
  expr_type e = BaseT bt /\ is_word_type (BaseT bt) /\
  eval_operand l s = SOME (n2w (LENGTH bs)) /\
  eval_operand d s = SOME (n2w (p + 32)) /\
  eval_operand off s = SOME (n2w n) /\
  (!x. l = Var x \/ d = Var x \/ off = Var x ==> not_fresh_at sa x) /\
  LENGTH bs < dimword (:256) /\ n < dimword (:256) /\
  n + 32 <= LENGTH bs /\ p + 32 + n < dimword (:256) /\
  p + 32 < dimword (:256) /\ p + 32 + LENGTH bs <= s.vs_alloca_next /\
  val_in_memory (BaseTV (BytesT (Dynamic cap))) (BytesV bs) p s.vs_memory /\
  extract32_result_base_ok bt /\ well_formed_type tenv (BaseT bt) /\
  evaluate_extract32 bs n bt = INL v /\ ~s.vs_halted ==>
  ?u. gas_path_mem ctx func s (LENGTH (FILTER (\i. i.inst_opcode = GAS) code)) (OK u) /\
    vv_post ctx func cenv cx e es s0c sb s0 es' (Value v)
      (StackValue (BaseT bt) op) u /\
    vv_store_bound cx (BaseT bt) lt es' (Value v) (StackValue (BaseT bt) op) u /\
    alloca_history func u /\ ~u.vs_halted /\
    u.vs_current_bb = sb.cs_current_bb /\
    u.vs_inst_idx = LENGTH sb.cs_current_insts /\
    s.vs_alloca_next <= u.vs_alloca_next
Proof
  strip_tac >> drule_all extract32_suffix_code_prefix >> strip_tac >>
  `isPREFIX code (DROP s.vs_inst_idx bb.bb_instructions)` by
    simp[rich_listTheory.IS_PREFIX_APPEND] >>
  drule_all extract32_suffix_success_separated_path >>
  disch_then (qspec_then `ctx` strip_assume_tac) >>
  `DROP s.vs_inst_idx bb.bb_instructions = code ++ rest` by simp[] >>
  `alloca_inv s` by fs[stmt_state_rel_def] >>
  `EVERY (\i. ~is_terminator i.inst_opcode) code` by
    (drule_all extract32_suffix_output_range >> strip_tac >>
     fs[listTheory.EVERY_MEM] >> rpt strip_tac >>
     res_tac >> gvs[venomInstTheory.is_terminator_def]) >>
  drule_all alloca_history_run_inst_seq >> strip_tac >>
  drule_all extract32_suffix_word_post >> strip_tac >>
  qexists_tac `t with vs_inst_idx := s.vs_inst_idx + LENGTH code` >>
  gvs[] >> qpat_x_assum `t = s with vs_vars := _` SUBST1_TAC >>
  fs[eval_operand_def, fresh_vars_wrt_def]
QED

Theorem extract32_suffix_revert_entry:
  compile_extract32_load l d off sa = (raw,sc) /\
  compile_clamp_basetype raw (BaseT bt) sc = (op,sb) /\
  code = emitted_insts sa sc ++ emitted_insts sc sb /\
  fn_has_code sa sb func /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  eval_operand l s = SOME (n2w (LENGTH bs)) /\
  eval_operand d s = SOME (n2w (p + 32)) /\
  eval_operand off s = SOME (n2w n) /\
  (!x. l = Var x \/ d = Var x \/ off = Var x ==> not_fresh_at sa x) /\
  LENGTH bs < dimword (:256) /\ n < dimword (:256) /\
  (n + 32 <= LENGTH bs ==> p + 32 + n < dimword (:256)) /\
  p + 32 < dimword (:256) /\ p + 32 + LENGTH bs <= s.vs_alloca_next /\
  val_in_memory (BaseTV (BytesT (Dynamic cap))) (BytesV bs) p s.vs_memory /\
  extract32_result_base_ok bt /\ well_formed_type tenv (BaseT bt) /\
  evaluate_extract32 bs n bt = INR (RuntimeError msg) /\ ~s.vs_halted ==>
  ?t k j. gas_path_mem ctx func s k (Abort Revert_abort (t with vs_inst_idx := j))
Proof
  strip_tac >> drule_all extract32_suffix_code_prefix >> strip_tac >>
  `isPREFIX code (DROP s.vs_inst_idx bb.bb_instructions)` by
    simp[rich_listTheory.IS_PREFIX_APPEND] >>
  drule_all extract32_suffix_revert_separated_path >> simp[]
QED
