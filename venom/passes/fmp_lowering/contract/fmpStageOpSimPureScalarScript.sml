(* Clean scalar instructions at the FMP boundary. *)
Theory fmpStageOpSimPureScalar
Ancestors
  fmpStageOpBase fmpStageRel o1LowerDloadRelocationKernel
  ptrStaticDiscipline ptrDiscipline o1PassContract contextCodegenRel
  venomExecSemantics venomState venomInst pointerConfinedDefs
  finite_map list pred_set words memLocDefs arithmetic

Theorem fmp_clean_operand[local]:
  fmp_stage_ctx rpolicy D C C' vs vs' fmp eom /\
  frame_reachable vs C stk PG G tn fn inst s /\ active_inst fn inst s /\
  fmp_stage_rel D C' sm fmp0 raw0 eom restored stk PG G tn fn s lo t ts /\
  MEM inst.inst_opcode [MUL; Div; Mod; SDIV; SMOD; Exp; ADDMOD; MULMOD;
    SLT; SGT; ISZERO; AND; OR; XOR; NOT; SIGNEXTEND; BYTE; OFFSET] /\
  MEM op inst.inst_operands /\ eval_operand op s = SOME x ==>
  eval_operand op t = SOME x
Proof
  strip_tac >> drule_all fmp_stage_frame_facts >> strip_tac >>
  drule fmp_stage_prov_support >>
  disch_then (qspec_then `P` mp_tac) >> simp[] >> strip_tac >>
  `fn_static_ptr_ok P fn` by metis_tac[EVERY_MEM] >>
  `ptr_use_static_ok P (fn_pv P fn) inst` by
    metis_tac[fn_static_ptr_ok_def] >>
  `op_prov G op = NONE` by
    (Cases_on `op` >>
     gvs[op_prov_def, FLOOKUP_DEF, SUBSET_DEF, ptr_use_static_ok_def,
         mem_read_ops_def, mem_write_ops_def, is_pointer_preserving_op_def,
         MEM] >> metis_tac[]) >>
  `op_taint tn op = {}` by (gvs[taint_ok_def] >> metis_tac[]) >>
  `!v. op = Var v ==> ~retpc_var fn v` by
    (rpt strip_tac >>
     `opaque_use_ok fn` by
       gvs[o1_fn_shape_def, unitShapeDefsTheory.fn_shape_ok_def] >>
     gvs[] >> drule_all unitShapeDefsTheory.opaque_use_ok_retpc_use >>
     gvs[unitShapeDefsTheory.retpc_use_ok_def, MEM]) >>
  `inst.inst_opcode <> PHI` by gvs[MEM] >>
  drule_all fmp_stage_operand >>
  simp[fmp_value_rel_def] >> metis_tac[ld_value_agree_clean]
QED

Theorem fmp_clean_step[local]:
  fmp_stage_ctx rpolicy D C C' vs vs' fmp eom /\
  frame_reachable vs C stk PG G tn fn inst s /\ active_inst fn inst s /\
  fmp_stage_rel D C' sm fmp0 raw0 eom restored stk PG G tn fn s lo t ts /\
  MEM inst.inst_opcode [MUL; Div; Mod; SDIV; SMOD; Exp; ADDMOD; MULMOD;
    SLT; SGT; ISZERO; AND; OR; XOR; NOT; SIGNEXTEND; BYTE; OFFSET] /\
  step_inst k C inst s = OK s1 ==>
  ?out x. inst.inst_outputs = [out] /\ s1 = update_var out x s /\
    step_inst k C' inst t = OK (update_var out x t)
Proof
  strip_tac >>
  `!op x. MEM op inst.inst_operands /\ eval_operand op s = SOME x ==>
      eval_operand op t = SOME x` by metis_tac[fmp_clean_operand] >>
  qpat_x_assum `step_inst _ C inst s = _` mp_tac >> fs[MEM] >>
  (simp[step_inst_non_invoke] >>
   asm_simp_tac (srw_ss()) [step_inst_base_opcode_eqs] >>
   simp[exec_pure1_def, exec_pure2_def, exec_pure3_def, AllCaseEqs()] >>
   strip_tac >> gvs[] >>
   qmatch_goalsub_abbrev_tac `update_var out value s` >>
   metis_tac[])
QED

Theorem fmp_clean_terminating_result[local]:
  MEM inst.inst_opcode [MUL; Div; Mod; SDIV; SMOD; Exp; ADDMOD; MULMOD;
    SLT; SGT; ISZERO; AND; OR; XOR; NOT; SIGNEXTEND; BYTE; OFFSET] /\
  step_inst k C inst s = r /\ terminates r ==>
  ?s1. r = OK s1
Proof
  strip_tac >> fs[MEM] >>
  qpat_x_assum `step_inst _ _ _ _ = _` mp_tac >>
  simp[step_inst_non_invoke] >>
  asm_simp_tac (srw_ss()) [step_inst_base_opcode_eqs] >>
  gvs[exec_pure1_def, exec_pure2_def, exec_pure3_def, AllCaseEqs(),
      passSimulationDefsTheory.terminates_def] >>
  strip_tac >> gvs[passSimulationDefsTheory.terminates_def]
QED

Theorem fmp_clean_update_taint[local]:
  MEM inst.inst_opcode [MUL; Div; Mod; SDIV; SMOD; Exp; ADDMOD; MULMOD;
    SLT; SGT; ISZERO; AND; OR; XOR; NOT; SIGNEXTEND; BYTE; OFFSET] /\
  inst.inst_outputs = [out] ==>
  step_taint inst s (update_var out x s) tn =
    tn with t_var := tn.t_var |+ (out,{})
Proof
  strip_tac >> fs[MEM] >>
  (simp[step_taint_def, out_taint_def, set_var_taint_def,
      mem_taint_def, store_taint_def, adopt_reset_def, imm_taint_def,
      update_var_def, new_site_bytes_def, written_taint_def, step_writes_def,
      codegenRelTheory.source_memory_write_ranges_def, range_bytes_def,
      taint_component_equality] >>
  gvs[FLOOKUP_DEF, SF CONJ_ss] >>
  Cases_on `inst.inst_operands` >> simp[] >>
  rename1 `inst.inst_operands = a::ops` >> Cases_on `ops` >> simp[]
  >- (Cases_on `eval_operand a s` >> simp[]) >>
  rename1 `inst.inst_operands = a::b::ops` >> Cases_on `ops` >> simp[]
  >- (Cases_on `eval_operand a s` >> simp[]) >>
  rename1 `inst.inst_operands = a::b::c::ops` >> Cases_on `ops` >> simp[])
QED

Theorem fmp_clean_update_value[local]:
  MEM inst.inst_opcode [MUL; Div; Mod; SDIV; SMOD; Exp; ADDMOD; MULMOD;
    SLT; SGT; ISZERO; AND; OR; XOR; NOT; SIGNEXTEND; BYTE; OFFSET] /\
  inst.inst_outputs = [out] ==>
  (!v. ~MEM v inst.inst_outputs ==>
    FLOOKUP (update_var out x s).vs_vars v = FLOOKUP s.vs_vars v /\
    FLOOKUP (update_var out x t).vs_vars v = FLOOKUP t.vs_vars v) /\
  (!v z. MEM v inst.inst_outputs /\
    FLOOKUP (update_var out x s).vs_vars v = SOME z ==>
    ?w. FLOOKUP (update_var out x t).vs_vars v = SOME w /\
     (~retpc_var fn v ==>
      fmp_value_rel sm (FLOOKUP (step_prov PG G inst (update_var out x s)) v)
       (op_taint (step_taint inst s (update_var out x s) tn) (Var v)) z w))
Proof
  strip_tac >> drule_all fmp_clean_update_taint >> strip_tac >>
  fs[MEM] >>
  simp[update_var_def, FLOOKUP_UPDATE, op_taint_def, step_prov_def,
       out_prov_def, set_prov_def, FLOOKUP_DRESTRICT, fmp_value_rel_def,
       ld_value_agree_scalar, word_agree_except_def]
QED

Theorem fmp_clean_update_post[local]:
  MEM inst.inst_opcode [MUL; Div; Mod; SDIV; SMOD; Exp; ADDMOD; MULMOD;
    SLT; SGT; ISZERO; AND; OR; XOR; NOT; SIGNEXTEND; BYTE; OFFSET] /\
  inst.inst_outputs = [out] /\ s1 = update_var out x s /\
  t1 = update_var out x t /\
  ld_memory_agree (fmp_ld_sites sm) eom tn.t_mem s.vs_memory t.vs_memory /\
  ld_shared_agree D s.vs_call_ctx.cc_address tn s t /\
  s.vs_returndata = t.vs_returndata /\ ~s.vs_halted /\ ~t.vs_halted ==>
  (!v. ~MEM v inst.inst_outputs ==>
    FLOOKUP s1.vs_vars v = FLOOKUP s.vs_vars v /\
    FLOOKUP t1.vs_vars v = FLOOKUP t.vs_vars v) /\
  (!v z. MEM v inst.inst_outputs /\ FLOOKUP s1.vs_vars v = SOME z ==>
    ?w. FLOOKUP t1.vs_vars v = SOME w /\
      (~retpc_var fn v ==>
        fmp_value_rel sm (FLOOKUP (step_prov PG G inst s1) v)
          (op_taint (step_taint inst s s1 tn) (Var v)) z w)) /\
  ld_memory_agree (fmp_ld_sites sm) eom
    (step_taint inst s s1 tn).t_mem s1.vs_memory t1.vs_memory /\
  ld_shared_agree D s.vs_call_ctx.cc_address (step_taint inst s s1 tn) s1 t1 /\
  s1.vs_returndata = t1.vs_returndata /\ ~s1.vs_halted /\ ~t1.vs_halted /\
  s1.vs_current_bb = s.vs_current_bb /\ s1.vs_prev_bb = s.vs_prev_bb /\
  s1.vs_inst_idx = s.vs_inst_idx /\ s1.vs_params = s.vs_params /\
  s1.vs_call_ctx = s.vs_call_ctx /\ s1.vs_tx_ctx = s.vs_tx_ctx /\
  s1.vs_block_ctx = s.vs_block_ctx /\
  s1.vs_data_section = s.vs_data_section /\
  s1.vs_labels = s.vs_labels /\ s1.vs_code = s.vs_code /\
  s1.vs_prev_hashes = s.vs_prev_hashes /\
  s1.vs_initial_fmp = s.vs_initial_fmp /\ s1.vs_fmp = s.vs_fmp /\
  t1.vs_current_bb = t.vs_current_bb /\ t1.vs_prev_bb = t.vs_prev_bb /\
  t1.vs_inst_idx = t.vs_inst_idx /\ t1.vs_params = t.vs_params /\
  t1.vs_call_ctx = t.vs_call_ctx /\ t1.vs_tx_ctx = t.vs_tx_ctx /\
  t1.vs_block_ctx = t.vs_block_ctx /\
  t1.vs_data_section = t.vs_data_section /\
  t1.vs_labels = t.vs_labels /\ t1.vs_code = t.vs_code /\
  t1.vs_prev_hashes = t.vs_prev_hashes /\
  t1.vs_initial_fmp = t.vs_initial_fmp /\ t1.vs_fmp = t.vs_fmp
Proof
  strip_tac >>
  qpat_x_assum `s1 = _` SUBST_ALL_TAC >>
  qpat_x_assum `t1 = _` SUBST_ALL_TAC >>
  conj_tac >- metis_tac[fmp_clean_update_value] >>
  conj_tac >- metis_tac[fmp_clean_update_value] >>
  drule_all fmp_clean_update_taint >>
  disch_then (qspecl_then [`x`,`tn`,`s`] assume_tac) >>
  gvs[update_var_def, o1LowerDloadSharedTheory.ld_shared_agree_def]
QED

Theorem fmp_stage_sim_clean:
  fmp_stage_ctx rpolicy D C C' vs vs' fmp eom /\
  fmp0 = w2n vs'.vs_initial_fmp /\ raw0 = w2n fmp /\
  frame_reachable vs C stk PG G tn fn inst s /\ active_inst fn inst s /\
  ~s.vs_halted /\ ~in_revert_forward fn s /\
  MEM inst.inst_opcode [MUL; Div; Mod; SDIV; SMOD; Exp; ADDMOD; MULMOD;
    SLT; SGT; ISZERO; AND; OR; XOR; NOT; SIGNEXTEND; BYTE; OFFSET] /\
  fmp_stage_rel D C' sm fmp0 raw0 eom F stk PG G tn fn s lo t ts /\
  step_inst k C inst s = r /\ terminates r ==>
  ?k' r'. step_inst k' C' inst t = r' /\
    case r of
      OK s1 => ?t1. r' = OK t1 /\
        (!v. ~MEM v inst.inst_outputs ==>
             FLOOKUP s1.vs_vars v = FLOOKUP s.vs_vars v /\
             FLOOKUP t1.vs_vars v = FLOOKUP t.vs_vars v) /\
        (!v x. MEM v inst.inst_outputs /\ FLOOKUP s1.vs_vars v = SOME x ==>
           ?y. FLOOKUP t1.vs_vars v = SOME y /\
               (~retpc_var fn v ==>
                fmp_value_rel sm (FLOOKUP (step_prov PG G inst s1) v)
                  (op_taint (step_taint inst s s1 tn) (Var v)) x y)) /\
        ld_memory_agree (fmp_ld_sites sm) eom
          (step_taint inst s s1 tn).t_mem s1.vs_memory t1.vs_memory /\
        ld_shared_agree D s.vs_call_ctx.cc_address
          (step_taint inst s s1 tn) s1 t1 /\
        s1.vs_returndata = t1.vs_returndata /\
        ~s1.vs_halted /\ ~t1.vs_halted /\
        s1.vs_current_bb = s.vs_current_bb /\ s1.vs_prev_bb = s.vs_prev_bb /\
        s1.vs_inst_idx = s.vs_inst_idx /\ s1.vs_params = s.vs_params /\
        s1.vs_call_ctx = s.vs_call_ctx /\ s1.vs_tx_ctx = s.vs_tx_ctx /\
        s1.vs_block_ctx = s.vs_block_ctx /\
        s1.vs_data_section = s.vs_data_section /\
        s1.vs_labels = s.vs_labels /\ s1.vs_code = s.vs_code /\
        s1.vs_prev_hashes = s.vs_prev_hashes /\
        s1.vs_initial_fmp = s.vs_initial_fmp /\ s1.vs_fmp = s.vs_fmp /\
        t1.vs_current_bb = t.vs_current_bb /\ t1.vs_prev_bb = t.vs_prev_bb /\
        t1.vs_inst_idx = t.vs_inst_idx /\ t1.vs_params = t.vs_params /\
        t1.vs_call_ctx = t.vs_call_ctx /\ t1.vs_tx_ctx = t.vs_tx_ctx /\
        t1.vs_block_ctx = t.vs_block_ctx /\
        t1.vs_data_section = t.vs_data_section /\
        t1.vs_labels = t.vs_labels /\ t1.vs_code = t.vs_code /\
        t1.vs_prev_hashes = t.vs_prev_hashes /\
        t1.vs_initial_fmp = t.vs_initial_fmp /\ t1.vs_fmp = t.vs_fmp
    | Halt se => dead_result_rel D r r'
    | Abort ab se => dead_result_rel D r r'
    | _ => F
Proof
  strip_tac >> drule_all fmp_clean_terminating_result >> strip_tac >>
  qpat_x_assum `r = _` SUBST_ALL_TAC >>
  drule_all fmp_clean_step >> strip_tac >>
  qabbrev_tac `t1 = update_var out x t` >>
  qexistsl [`k`,`OK t1`] >> simp_tac (srw_ss()) [] >>
  conj_tac >- simp[Abbr `t1`] >>
  irule fmp_clean_update_post >>
  fs[fmp_stage_rel_def] >> qexists `x` >> simp[Abbr `t1`] >> gvs[]
QED
