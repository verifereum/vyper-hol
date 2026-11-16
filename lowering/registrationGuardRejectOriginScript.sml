(* The rejecting calldata pointer guard.  The abort edge keeps the ghosts
   produced by its two scalar prefix instructions, uniformly in the dead set. *)
Theory registrationGuardRejectOrigin
Ancestors registrationGuardPtr fragGasEmitCtrl bodyPtrEnvBuiltinsGuards
  augAssignPtrScalarSafety augAssignPtrScalarCertificate unitTransformDefs calldataClampPtr
  decoderNavigationPtr fragGasOriginPtr fragGasSeqPtr instMemFrontier
  memSafeRun gasCount gasEvents venomInstProofs moduleLowering emitHelperProps abiEncoder
  compileEnv emitHelper exprLoweringProps fragExec venomInst words arithmetic
  list rich_list ptrDiscipline ptrSafeRun venomState venomExecSemantics
  finite_map pred_set codegenRel contextCodegenRel

Theorem registration_ptr_guard_reject_origin:
  compile_abi_arg_ptr_guard CALLDATALOAD src (Lit 4w) sa = ((),sb) /\
  eval_operand src s = SOME w /\ w <+ 4w /\
  (!x. src = Var x ==> not_fresh_at sa x) /\
  op_taint tn src = {} /\ op_prov G src = NONE /\
  fn_has_code sa sb fn /\ fn_inst_ids_distinct fn /\ fresh_vars_wrt sa s /\
  allocas_from lo s /\ ~ctx_has_dalloca ctx /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts
  ==>
  ?z H u. z.vs_returndata = [] /\
    (!D explicit. gas_origin_ptr_path (D,lo,explicit,ctx,fn,PG)
       (s,G,tn) [] (Abort Revert_abort z,H,u))
Proof
  strip_tac >>
  `sb.cs_current_bb = sa.cs_current_bb /\
   sb.cs_current_insts = sa.cs_current_insts ++ emitted_insts sa sb /\
   emitted_insts sa sb =
    [mk_inst sa.cs_next_id LT [src; Lit 4w] ["%" ++ toString sa.cs_next_var];
     mk_inst (sa.cs_next_id + 1) ISZERO [Var ("%" ++ toString sa.cs_next_var)]
       ["%" ++ toString (sa.cs_next_var + 1)];
     mk_inst (sa.cs_next_id + 2) ASSERT
       [Var ("%" ++ toString (sa.cs_next_var + 1))] []]` by
    (qpat_x_assum `compile_abi_arg_ptr_guard _ _ _ _ = _` mp_tac >>
     simp[compile_abi_arg_ptr_guard_def, comp_bind_def, comp_ignore_bind_def,
       comp_return_def, emit_op_def, emit_void_def, emit_inst_def,
       fresh_var_def, fresh_id_def, emit_def] >>
     strip_tac >> gvs[emitted_insts_def, APPEND_ASSOC, DROP_PREFIX]) >>
  qabbrev_tac `v0 = "%" ++ toString sa.cs_next_var` >>
  qabbrev_tac `v1 = "%" ++ toString (sa.cs_next_var + 1)` >>
  qabbrev_tac `i0 = mk_inst sa.cs_next_id LT [src; Lit 4w] [v0]` >>
  qabbrev_tac `i1 = mk_inst (sa.cs_next_id + 1) ISZERO [Var v0] [v1]` >>
  qabbrev_tac `i2 = mk_inst (sa.cs_next_id + 2) ASSERT [Var v1] []` >>
  qabbrev_tac `t1 = update_var v0 1w s` >>
  qabbrev_tac `s1 = t1 with vs_inst_idx := SUC s.vs_inst_idx` >>
  qabbrev_tac `t2 = update_var v1 0w s1` >>
  qabbrev_tac `s2 = t2 with vs_inst_idx := SUC s1.vs_inst_idx` >>
  qabbrev_tac `G1 = step_prov PG G i0 t1` >>
  qabbrev_tac `tn1 = step_taint i0 s t1 tn` >>
  qabbrev_tac `G2 = step_prov PG G1 i1 t2` >>
  qabbrev_tac `tn2 = step_taint i1 s1 t2 tn1` >>
  `step_inst_base i0 s = OK t1` by
    (qspecl_then [`src`, `Lit 4w`, `w`, `4w`, `sa.cs_next_id`, `v0`, `s`]
       mp_tac step_LT >>
     simp[Abbr `i0`, Abbr `t1`, eval_operand_def, bool_to_word_def, GSYM WORD_LO]) >>
  `step_inst_base i1 s1 = OK t2` by
    (qspecl_then [`Var v0`, `1w`, `sa.cs_next_id + 1`, `v1`, `s1`]
       mp_tac step_ISZERO >>
     simp[Abbr `i1`, Abbr `t2`, Abbr `s1`, Abbr `t1`, eval_operand_def,
       lookup_var_def, update_var_def, FLOOKUP_UPDATE, bool_to_word_def]) >>
  `op_prov G1 (Var v0) = NONE /\ op_taint tn1 (Var v0) = {}` by
    (simp[Abbr `G1`, Abbr `tn1`, Abbr `i0`] >>
     irule guard_compare_output_clean >> simp[]) >>
  `op_prov G2 (Var v1) = NONE /\ op_taint tn2 (Var v1) = {}` by
    (simp[Abbr `G2`, Abbr `tn2`, Abbr `i1`] >>
     irule clamp_scalar_output_ghost >> simp[]) >>
  `?bb. lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
    get_instruction bb s.vs_inst_idx = SOME i0 /\
    get_instruction bb s1.vs_inst_idx = SOME i1 /\
    get_instruction bb s2.vs_inst_idx = SOME i2` by
    (drule_all fn_has_code_same_block >> strip_tac >>
     qexists_tac `bb` >> simp[Abbr `s1`, Abbr `s2`, Abbr `t1`, Abbr `t2`, update_var_def] >>
     first_x_assum (fn th => map_every (fn n => mp_tac (Q.SPEC n th))
       [`0`, `1`, `2`]) >> simp[Abbr `i0`, Abbr `i1`, Abbr `i2`, ADD1]) >>
  suspend "paths"
QED

Resume registration_ptr_guard_reject_origin[paths]:
  qexistsl_tac [`revert_state (set_returndata [] s2)`, `G2`, `tn2`] >>
  conj_tac >- simp[revert_state_def, set_returndata_def] >>
  rpt gen_tac >>
  `gas_origin_ptr_path (D,lo,explicit,ctx,fn,PG) (s,G,tn) [] (OK s1,G1,tn1)` by
    (simp_tac (srw_ss()) [Abbr `s1`, Abbr `G1`, Abbr `tn1`] >>
     irule straight_line_step_origin >>
     goal_assum $ drule_at Any >> fs[Abbr `i0`, mk_inst_def,
       is_terminator_def, inst_mem_below_frontier_def, inst_dload_in_section_def,
       source_memory_read_ranges_def, source_memory_write_ranges_def] >>
     conj_tac >- metis_tac[] >>
     irule scalar_ptr_inst_ok_lo >>
     gvs[mk_inst_def, scalar_shape_def, scalar_binary_def,
       scalar_unary_def, op_taint_def, op_prov_def]) >>
  `gas_origin_ptr_path (D,lo,explicit,ctx,fn,PG) (s1,G1,tn1) [] (OK s2,G2,tn2)` by
    (simp[Abbr `s2`, Abbr `G2`, Abbr `tn2`] >>
     irule straight_line_step_origin >>
     goal_assum $ drule_at Any >> simp[Abbr `i1`, mk_inst_def,
       is_terminator_def, inst_mem_below_frontier_def, inst_dload_in_section_def,
       source_memory_read_ranges_def, source_memory_write_ranges_def,
       Abbr `s1`, Abbr `t1`, update_var_def] >>
     conj_tac >- (qexists_tac `bb` >> gvs[mk_inst_def]) >>
     irule scalar_ptr_inst_ok_lo >>
     gvs[mk_inst_def, scalar_shape_def, scalar_binary_def,
       scalar_unary_def, allocas_from_def, op_taint_def, op_prov_def] >>
     metis_tac[]) >>
  suspend "exit"
QED

Resume registration_ptr_guard_reject_origin[exit]:
  `step_inst_base i2 s2 = Abort Revert_abort (revert_state (set_returndata [] s2))` by
    (simp[Abbr `i2`] >> irule step_ASSERT_revert >>
     simp[Abbr `s2`, Abbr `t2`, eval_operand_def, lookup_var_def,
       update_var_def, FLOOKUP_UPDATE]) >>
  `gas_origin_ptr_path (D,lo,explicit,ctx,fn,PG) (s2,G2,tn2) []
      (Abort Revert_abort (revert_state (set_returndata [] s2)),G2,tn2)` by
    (irule exit_inst_origin_ptr >>
     simp_tac (srw_ss()) [exit_result_def] >>
     conj_tac >- gvs[Abbr `s2`, Abbr `t2`, Abbr `s1`, Abbr `t1`, update_var_def] >>
     qexistsl_tac [`bb`, `i2`] >>
     simp[Abbr `i2`, mk_inst_def, exit_result_def,
       gas_events_step_def, gas_count_step_def, mem_safe_step_non_invoke,
       inst_mem_below_frontier_def, inst_dload_in_section_def,
       source_memory_read_ranges_def, source_memory_write_ranges_def] >>
     conj_tac >- fs[step_inst_non_invoke, mk_inst_def] >>
     conj_tac >- gvs[Abbr `s2`, Abbr `t2`, Abbr `s1`, Abbr `t1`, update_var_def] >>
     irule scalar_ptr_inst_ok_lo >>
     gvs[scalar_shape_def, scalar_binary_def, scalar_unary_def,
       allocas_from_def, Abbr `s2`, Abbr `t2`, Abbr `s1`, Abbr `t1`, update_var_def,
       op_prov_def, op_taint_def] >> metis_tac[]) >>
  qpat_x_assum `gas_origin_ptr_path _ (s,G,tn) _ _` mp_tac >>
  qpat_x_assum `gas_origin_ptr_path _ (s1,G1,tn1) _ _` mp_tac >>
  qpat_x_assum `gas_origin_ptr_path _ (s2,G2,tn2) _ _` mp_tac >>
  POP_ASSUM_LIST (K all_tac) >> rpt strip_tac >>
  metis_tac[gas_origin_ptr_path_append, APPEND_NIL]
QED

Finalise registration_ptr_guard_reject_origin
