(* Joint rejection of a linear selector miss. *)
Theory entryDispatchRevert
Ancestors entryPrefixPtr fragGasEmitCtrl gasPathPtrExec fragExecPtr
  fragGasOriginPtr fragGasOrigin fragGasPathMem fragGasPathPtr
  entryDispatchPtr moduleLoweringProps emitHelperProps contextCodegenRel
  fragExec venomInst venomState venomExecSemantics ptrDiscipline ptrSafeRun
  fragGasMode compileEnv words list codegenRel

Theorem linear_dispatch_fallback_revert_joint:
  compile_selector_dispatch_linear selectors fallback st = ((),st') /\
  fn_has_code st st' fn /\
  EVERY (\(sel,lbl). sel < 2 ** 32) selectors /\
  LENGTH ss.vs_call_ctx.cc_calldata < dimword (:256) /\
  fresh_vars_wrt st ss /\ ~ss.vs_halted /\
  ss.vs_current_bb = st.cs_current_bb /\
  ss.vs_inst_idx = LENGTH st.cs_current_insts /\
  allocas_from lo ss /\ ~ctx_has_dalloca ctx /\
  linear_dispatch_target ss.vs_call_ctx.cc_calldata selectors fallback = fallback /\
  sa.cs_current_bb = fallback /\ sa.cs_current_insts = [] /\
  emit_inst REVERT [Lit 0w; Lit 0w] [] sa = ((),sb) /\
  fn_has_code sa sb fn ==>
  ?s G' tn'.
    s.vs_returndata = [] /\
    gas_path_mem ctx fn ss 0 (Abort Revert_abort s) /\
    (!D explicit. gas_origin_ptr_path (D,lo,explicit,ctx,fn,PG)
      (ss,G,tn) [] (Abort Revert_abort s,G',tn')) /\
    (!D fuel. ptr_safe_run D lo fuel ctx fn PG G tn ss)
Proof
  strip_tac >>
  `?bb. lookup_block fallback fn.fn_blocks = SOME bb /\
    get_instruction bb 0 = SOME (mk_inst sa.cs_next_id REVERT [Lit 0w; Lit 0w] [])` by
    (drule emit_inst_extends >> strip_tac >>
     drule_all fn_has_code_same_block >> strip_tac >>
     first_x_assum (qspec_then `0` mp_tac) >> gvs[]) >>
  `!bb. lookup_block fallback fn.fn_blocks = SOME bb ==>
    phi_prefix_length bb.bb_instructions = 0` by
    (rpt strip_tac >> gvs[] >>
     Cases_on `bb.bb_instructions` >>
     gvs[get_instruction_def, phi_prefix_length_def, mk_inst_def]) >>
  `ctx_has_dalloca ctx ==> allocas_below_fmp ss` by simp[] >>
  `!bb. lookup_block (linear_dispatch_target ss.vs_call_ctx.cc_calldata selectors fallback)
    fn.fn_blocks = SOME bb ==> phi_prefix_length bb.bb_instructions = 0` by simp[] >>
  drule_all compile_selector_dispatch_linear_ptr_endpoint >>
  disch_then (qspecl_then [`tn`, `PG`, `G`] strip_assume_tac) >>
  rename1 `vars_pc_only ss tt` >>
  `allocas_from lo tt` by
    (gvs[vars_pc_only_def, venom_state_component_equality, allocas_from_def] >> metis_tac[]) >>
  `!D explicit. gas_origin_ptr_path (D,lo,explicit,ctx,fn,PG)
     (tt,G',tn') [] (Abort Revert_abort (revert_state (set_returndata [] tt)),G',tn')` by
    (rpt gen_tac >> irule emit_abort_origin_ptr >> simp[] >>
     qexistsl_tac [`REVERT`, `[Lit 0w; Lit 0w]`, `sa`, `sb`] >>
     simp[mk_inst_def, step_inst_base_opcode_eqs, eval_operand_def]) >>
  `!D explicit. gas_origin_ptr_path (D,lo,explicit,ctx,fn,PG)
     (ss,G,tn) [] (Abort Revert_abort (revert_state (set_returndata [] tt)),G',tn')` by
    (metis_tac[gas_origin_ptr_path_append, APPEND]) >>
  qexistsl_tac [`revert_state (set_returndata [] tt)`, `G'`, `tn'`] >>
  simp[revert_state_def, set_returndata_def] >> conj_tac
  >- (qpat_assum `!D explicit. gas_origin_ptr_path _ (ss,G,tn) [] (Abort _ _,_,_)`
        (qspecl_then [`ARB`, `ARB`] mp_tac) >>
      disch_then (mp_tac o MATCH_MP gas_origin_ptr_path_projections) >> strip_tac >>
      drule gas_origin_path_erase >>
      simp[gas_marked_path_def, revert_state_def, set_returndata_def]) >>
  rpt gen_tac >>
  qpat_x_assum `!D. _ ==> !fuel. ptr_safe_run _ _ _ _ _ _ _ _ ss`
    (qspec_then `D` irule) >>
  irule ptr_safe_blocks_from_phi_free_run >> simp[] >>
  gen_tac >> simp[ptr_safe_run_def, Once ptr_safe_block_def] >>
  simp[ptr_safe_step_def, ptr_inst_ok_def, access_ok_def, taint_ok_def,
    mk_inst_def, source_memory_write_ranges_def, source_memory_read_ranges_def,
    memory_range_of_operands_def, eval_operand_def, op_taint_def,
    step_inst_non_invoke, step_inst_base_opcode_eqs, about_to_revert_def]
QED
