(* Static LOG exits from the prepared fixed-data window. *)
Theory bodyRawLogFixedStaticEmitMods
Ancestors
  logEmitStep rawLogPtrInst fragGasEmitCtrl placeTypedCopyPath instMemFrontier
  bodyPtrDefs ptrSafeRun ptrDiscipline exprLoweringProps stateRelProj
  loweringStateRelDefs emitHelper compileEnv fragExec memSafeRun gasEvents gasCount
  venomExecSemantics venomInst venomState vyperEvent vyperState words list
  finite_map arithmetic

Theorem raw_log_fixed_static_emit_mods:
  cx.txn.is_static /\
  emit_inst LOG (Lit (n2w (LENGTH ops)) :: REVERSE ops ++ [Lit 32w;Var p]) [] s1 = ((),sb) /\
  fn_has_code s1 sb func /\
  LENGTH ops < dimword (:256) /\
  eval_operands ops z = SOME (MAP event_value_to_word vals) /\
  eval_operand (Var p) z = SOME w /\ ptr_covers G tf p z 32 /\
  EVERY (\op. op_taint tf op = {}) ops /\
  (!k. w2n w <= k /\ k < w2n w + 32 ==> k NOTIN tf.t_mem) /\
  w2n w + 32 <= z.vs_alloca_next /\
  allocas_from lo z /\ (ctx_has_dalloca ctx ==> allocas_below_fmp z) /\
  stor_taint_ok_at D tf z /\ stmt_state_rel H ctx func cenv cx ee z /\
  ~z.vs_halted /\ z.vs_current_bb = s1.cs_current_bb /\
  z.vs_inst_idx = LENGTH s1.cs_current_insts ==>
  gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (z,G,tf) []
    (Abort ExHalt_abort (halt_state (set_returndata [] z)),G,tf)
Proof
  strip_tac >>
  drule_all place_copy_emit_instruction >> strip_tac >>
  qmatch_asmsub_abbrev_tac `get_instruction _ _ = SOME j` >>
  `z.vs_call_ctx.cc_static` by
    (fs[stmt_state_rel_def] >> drule state_rel_call_ctx_rel >>
     simp[call_ctx_rel_def]) >>
  `step_inst_base j z = Abort ExHalt_abort (halt_state (set_returndata [] z))` by
    (irule log_emit_static_step >> simp[Abbr `j`, mk_inst_def, eval_operand_def] >>
     metis_tac[]) >>
  `access_ok 0 G func j z` by
    (simp[Abbr `j`] >> irule (SRULE [] log_access_ok) >>
     gvs[ptr_covers_def, eval_operand_def, dimword_def] >> metis_tac[]) >>
  `access_ok lo G func j z` by
    (fs[access_ok_def] >> rpt strip_tac >> metis_tac[ADD_EQ_0]) >>
  `taint_ok func tf j z` by
    (simp[Abbr `j`] >> irule (SRULE [] log_taint_ok) >>
     simp[eval_operand_def, op_taint_def, dimword_def] >>
     gvs[ptr_covers_def, eval_operand_def, op_taint_def]) >>
  `!fuel. step_inst fuel ctx j z = Abort ExHalt_abort (halt_state (set_returndata [] z))` by
    simp[step_inst_non_invoke, Abbr `j`, mk_inst_def] >>
  `ptr_inst_ok D lo 0 ctx func G tf j z` by simp[ptr_inst_ok_def] >>
  `inst_mem_below_frontier j z` by
    simp[Abbr `j`, SRULE [] (Q.SPECL [`s1.cs_next_id`, `LENGTH ops`, `REVERSE ops`]
                           below_frontier_LOG), eval_operand_def, dimword_def] >>
    gvs[eval_operand_def] >>
  irule exit_inst_origin_ptr >> simp[exit_result_def] >>
  gvs[Abbr `j`, mk_inst_def, mem_safe_step_non_invoke,
      dalloca_no_wrap_non_dalloca, inst_dload_in_section_other,
      gas_events_step_def, gas_count_step_def]
QED
