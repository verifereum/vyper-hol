(* Affine arithmetic at the FMP stage boundary. *)
Theory fmpStageOpSimPureAffine
Ancestors
  fmpStageOpBase fmpStageRel o1LowerDloadRelocationKernel
  ptrStaticDiscipline ptrDiscipline o1PassContract contextCodegenRel
  venomExecSemantics venomState venomInst pointerConfinedDefs
  finite_map list pred_set words

Theorem fmp_value_rel_add[local]:
  fmp_value_rel sm h1 {} x1 y1 /\ fmp_value_rel sm h2 {} x2 y2 /\
  (h1 = NONE \/ h2 = NONE) /\
  h = (case h1 of NONE => h2 | SOME id => h1) ==>
  fmp_value_rel sm h {} (x1 + x2) (y1 + y2)
Proof
  Cases_on `h1` >> Cases_on `h2` >>
  simp[fmp_value_rel_def] >> rpt strip_tac >>
  imp_res_tac ld_value_agree_clean >> gvs[] >>
  gvs[ld_value_agree_pointer, ld_value_agree_scalar, word_agree_except_def] >>
  qexistsl [`b`,`c`,`z`] >> simp[] >> wordsLib.WORD_DECIDE_TAC
QED

Theorem fmp_value_rel_sub[local]:
  fmp_value_rel sm h {} x1 y1 /\ fmp_value_rel sm NONE {} x2 y2 ==>
  fmp_value_rel sm h {} (x1 - x2) (y1 - y2)
Proof
  Cases_on `h` >> simp[fmp_value_rel_def] >> rpt strip_tac >>
  imp_res_tac ld_value_agree_clean >> gvs[] >>
  gvs[ld_value_agree_pointer, ld_value_agree_scalar, word_agree_except_def] >>
  qexistsl [`b`,`c`,`z`] >> simp[] >> wordsLib.WORD_DECIDE_TAC
QED

Theorem fmp_affine_provenance[local]:
  FDOM G SUBSET fn_pv P fn /\ fn_static_ptr_ok P fn /\
  MEM inst (fn_insts fn) /\ MEM inst.inst_opcode [ADD; SUB] /\
  inst.inst_operands = [op1;op2] ==>
  (op_prov G op1 = NONE \/ op_prov G op2 = NONE) /\
  (inst.inst_opcode = SUB ==> op_prov G op2 = NONE)
Proof
  strip_tac >>
  `?bb. MEM bb fn.fn_blocks /\ MEM inst bb.bb_instructions` by
    (gvs[fn_insts_def, fn_insts_blocks_MEM] >> metis_tac[]) >>
  `affine_pointer_ops fn (ptr_roots P fn)` by
    gvs[fn_static_ptr_ok_def] >>
  qpat_x_assum `affine_pointer_ops _ _`
    (mp_tac o SRULE [affine_pointer_ops_def, LET_THM]) >>
  disch_then (qspecl_then [`bb`,`inst`,`op1`,`op2`] mp_tac) >>
  simp[] >> strip_tac >>
  Cases_on `op1` >> Cases_on `op2` >>
  gvs[op_prov_def, fn_pv_def, FLOOKUP_DEF, SUBSET_DEF] >> metis_tac[]
QED

Theorem fmp_affine_operand[local]:
  fmp_stage_ctx rpolicy D C C' vs vs' fmp eom /\
  frame_reachable vs C stk PG G tn fn inst s /\ active_inst fn inst s /\
  fmp_stage_rel D C' sm fmp0 raw0 eom restored stk PG G tn fn s lo t ts /\
  MEM inst.inst_opcode [ADD; SUB] /\ MEM op inst.inst_operands /\
  eval_operand op s = SOME x ==>
  ?y. eval_operand op t = SOME y /\
      fmp_value_rel sm (op_prov G op) {} x y
Proof
  strip_tac >>
  drule_all fmp_stage_frame_facts >> strip_tac >>
  `op_taint tn op = {}` by
    (gvs[taint_ok_def] >> metis_tac[]) >>
  `!v. op = Var v ==> ~retpc_var fn v` by
    (rpt strip_tac >>
     `opaque_use_ok fn` by
       gvs[o1_fn_shape_def, unitShapeDefsTheory.fn_shape_ok_def] >>
     gvs[] >> drule_all unitShapeDefsTheory.opaque_use_ok_retpc_use >>
     gvs[unitShapeDefsTheory.retpc_use_ok_def]) >>
  `inst.inst_opcode <> PHI` by gvs[] >>
  drule_all fmp_stage_operand >> simp[]
QED


Theorem fmp_affine_step[local]:
  fmp_stage_ctx rpolicy D C C' vs vs' fmp eom /\
  frame_reachable vs C stk PG G tn fn inst s /\ active_inst fn inst s /\
  fmp_stage_rel D C' sm fmp0 raw0 eom restored stk PG G tn fn s lo t ts /\
  MEM inst.inst_opcode [ADD; SUB] /\ step_inst k C inst s = OK s1 ==>
  ?out x y. inst.inst_outputs = [out] /\ s1 = update_var out x s /\
    step_inst k C' inst t = OK (update_var out y t) /\
    fmp_value_rel sm (out_prov PG G inst s1) {} x y
Proof
  strip_tac >> drule_all fmp_stage_frame_facts >> strip_tac >>
  drule fmp_stage_prov_support >>
  disch_then (qspec_then `P` mp_tac) >> simp[] >> strip_tac >>
  `fn_static_ptr_ok P fn` by metis_tac[EVERY_MEM] >>
  qpat_x_assum `step_inst _ _ _ _ = _` mp_tac >> fs[MEM] >>
  (gvs[step_inst_non_invoke, step_inst_base_def, exec_pure2_def, AllCaseEqs()] >>
   strip_tac >> gvs[] >>
   rename1 `eval_operand op1 s = SOME x1` >>
   rename1 `eval_operand op2 s = SOME x2` >>
   `?y1. eval_operand op1 t = SOME y1 /\
     fmp_value_rel sm (op_prov G op1) {} x1 y1` by
     metis_tac[fmp_affine_operand, MEM] >>
   `?y2. eval_operand op2 t = SOME y2 /\
     fmp_value_rel sm (op_prov G op2) {} x2 y2` by
     metis_tac[fmp_affine_operand, MEM] >>
   `(op_prov G op1 = NONE \/ op_prov G op2 = NONE) /\
    (inst.inst_opcode = SUB ==> op_prov G op2 = NONE)` by
     metis_tac[fmp_affine_provenance, MEM] >>
   qmatch_goalsub_abbrev_tac `update_var out value s` >>
   qexistsl [`value`,
     `if inst.inst_opcode = ADD then y1 + y2 else y1 - y2`] >>
   simp[out_prov_def, first_prov_def, Abbr `value`]) >>
  (Cases_on `inst.inst_opcode = ADD`
   >- (irule fmp_value_rel_add >>
       qexistsl [`op_prov G op1`,`op_prov G op2`] >>
       Cases_on `op_prov G op1` >> Cases_on `op_prov G op2` >> gvs[]) >>
   gvs[] >> Cases_on `op_prov G op1` >> gvs[] >>
   rewrite_tac[WORD_SUB_INTRO] >> irule fmp_value_rel_sub >> simp[])
QED

Theorem fmp_affine_terminating_result[local]:
  MEM inst.inst_opcode [ADD; SUB] /\
  step_inst k C inst s = r /\ terminates r ==>
  ?s1. r = OK s1
Proof
  strip_tac >> fs[MEM] >>
  gvs[step_inst_non_invoke, step_inst_base_def, exec_pure2_def,
      AllCaseEqs(), passSimulationDefsTheory.terminates_def]
QED

Theorem fmp_affine_update_taint[local]:
  MEM inst.inst_opcode [ADD; SUB] /\ inst.inst_operands = [op1;op2] /\
  inst.inst_outputs = [out] ==>
  step_taint inst s (update_var out x s) tn =
    tn with t_var := tn.t_var |+ (out,{})
Proof
  strip_tac >> fs[MEM] >>
  gvs[step_taint_def, out_taint_def, set_var_taint_def,
      mem_taint_def, store_taint_def, adopt_reset_def, imm_taint_def,
      update_var_def, new_site_bytes_def, written_taint_def, step_writes_def,
      codegenRelTheory.source_memory_write_ranges_def, range_bytes_def,
      FLOOKUP_DEF, SF CONJ_ss, AllCaseEqs(), taint_component_equality] >>
  Cases_on `eval_operand op1 s` >> simp[]
QED

Theorem fmp_affine_update_value[local]:
  MEM inst.inst_opcode [ADD; SUB] /\ inst.inst_operands = [op1;op2] /\
  inst.inst_outputs = [out] /\
  fmp_value_rel sm (out_prov PG G inst (update_var out x s)) {} x y ==>
  (!v. ~MEM v inst.inst_outputs ==>
     FLOOKUP (update_var out x s).vs_vars v = FLOOKUP s.vs_vars v /\
     FLOOKUP (update_var out y t).vs_vars v = FLOOKUP t.vs_vars v) /\
  (!v z. MEM v inst.inst_outputs /\
      FLOOKUP (update_var out x s).vs_vars v = SOME z ==>
    ?w. FLOOKUP (update_var out y t).vs_vars v = SOME w /\
      (~retpc_var fn v ==>
       fmp_value_rel sm (FLOOKUP (step_prov PG G inst (update_var out x s)) v)
        (op_taint (step_taint inst s (update_var out x s) tn) (Var v)) z w))
Proof
  strip_tac >> drule_all fmp_affine_update_taint >> strip_tac >>
  simp[update_var_def, FLOOKUP_UPDATE, op_taint_def, step_prov_def] >>
  Cases_on `out_prov PG G inst (update_var out x s)` >>
  gvs[set_prov_def, FLOOKUP_UPDATE, FLOOKUP_DRESTRICT, update_var_def]
QED

Theorem fmp_affine_update_agree[local]:
  MEM inst.inst_opcode [ADD; SUB] /\ inst.inst_operands = [op1;op2] /\
  inst.inst_outputs = [out] /\
  ld_memory_agree (fmp_ld_sites sm) eom tn.t_mem s.vs_memory t.vs_memory /\
  ld_shared_agree D s.vs_call_ctx.cc_address tn s t ==>
  ld_memory_agree (fmp_ld_sites sm) eom
    (step_taint inst s (update_var out x s) tn).t_mem
    (update_var out x s).vs_memory (update_var out y t).vs_memory /\
  ld_shared_agree D s.vs_call_ctx.cc_address
    (step_taint inst s (update_var out x s) tn)
    (update_var out x s) (update_var out y t)
Proof
  strip_tac >> drule_all fmp_affine_update_taint >> strip_tac >>
  gvs[update_var_def, o1LowerDloadSharedTheory.ld_shared_agree_def]
QED

Theorem fmp_affine_update_post[local]:
  MEM inst.inst_opcode [ADD; SUB] /\ inst.inst_operands = [op1;op2] /\
  inst.inst_outputs = [out] /\
  s1 = update_var out x s /\ t1 = update_var out y t /\
  fmp_value_rel sm (out_prov PG G inst s1) {} x y /\
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
  drule_all fmp_affine_update_value >>
  disch_then (qspecl_then [`tn`,`t`,`fn`] strip_assume_tac) >>
  drule_all fmp_affine_update_agree >>
  disch_then (qspecl_then [`y`,`x`] strip_assume_tac) >>
  gvs[update_var_def]
QED

Theorem fmp_stage_sim_affine:
  fmp_stage_ctx rpolicy D C C' vs vs' fmp eom /\
  fmp0 = w2n vs'.vs_initial_fmp /\ raw0 = w2n fmp /\
  frame_reachable vs C stk PG G tn fn inst s /\ active_inst fn inst s /\
  ~s.vs_halted /\ ~in_revert_forward fn s /\
  MEM inst.inst_opcode [ADD; SUB] /\
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
  strip_tac >>
  drule_all fmp_affine_terminating_result >> strip_tac >>
  qpat_x_assum `r = _` SUBST_ALL_TAC >>
  drule_all fmp_affine_step >> strip_tac >>
  `?op1 op2. inst.inst_operands = [op1;op2]` by
    (qpat_x_assum `step_inst _ C inst s = _` mp_tac >> fs[MEM] >>
     simp[step_inst_non_invoke, step_inst_base_def, exec_pure2_def,
          AllCaseEqs()] >> metis_tac[]) >>
  qabbrev_tac `t1 = update_var out y t` >>
  qexistsl [`k`,`OK t1`] >>
  simp_tac (srw_ss()) [] >>
  conj_tac >- simp[Abbr `t1`] >>
  irule fmp_affine_update_post >>
  fs[fmp_stage_rel_def] >>
  qexistsl [`x`,`y`] >> simp[Abbr `t1`] >> gvs[]
QED
