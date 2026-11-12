(* Unsigned comparisons at the FMP boundary. *)
Theory fmpStageOpSimPureCompare
Ancestors
  fmpStageOpBase fmpStageRel o1LowerDloadRelocationKernel
  o1LowerDloadAddressArithmetic fmpLowerSequenceExec
  ptrStaticDiscipline ptrDiscipline o1PassContract contextCodegenRel
  venomExecSemantics venomState venomInst pointerConfinedDefs
  finite_map list pred_set words memLocDefs arithmetic

Theorem fmp_compare_pointer_values[local]:
  fmp_sites_ok sm fmp0 raw0 lo raw /\
  fmp_frontier_rel fmp0 raw0 lo raw /\ 0 < z /\
  b <= w2n x /\ w2n x <= b+z /\ b <= w2n y /\ w2n y <= b+z /\
  fmp_value_rel sm (SOME (b,z)) {} x x' /\
  fmp_value_rel sm (SOME (b,z)) {} y y' ==>
  (w2n x < w2n y <=> w2n x' < w2n y') /\
  (w2n y < w2n x <=> w2n y' < w2n x') /\ (x = y <=> x' = y')
Proof
  strip_tac >>
  `z <> 0` by decide_tac >>
  gvs[fmp_value_rel_def, ld_value_agree_pointer, FLOOKUP_fmp_ld_sites,
      AllCaseEqs()] >>
  `lo <= w2n raw` by metis_tac[fmp_frontier_rel_le] >>
  `b+z < dimword (:256) /\ c+z < dimword (:256)` by
    (gvs[fmp_sites_ok_def] >>
     qpat_x_assum `!b z c id. _ ==> 0 < z /\ _`
       (qspecl_then [`b`,`z`,`c`,`id`] mp_tac) >> simp[] >> strip_tac >>
     mp_tac (Q.ISPEC `raw:bytes32` w2n_lt) >> decide_tac) >>
  `w2n (x + n2w c - n2w b) = c + (w2n x-b)` by
    (irule lower_dload_translate_endpoint >> metis_tac[]) >>
  `w2n (y + n2w c - n2w b) = c + (w2n y-b)` by
    (irule lower_dload_translate_endpoint >> metis_tac[]) >>
  pure_once_rewrite_tac[GSYM w2n_11] >> decide_tac
QED

Theorem fmp_compare_operand[local]:
  fmp_stage_ctx rpolicy D C C' vs vs' fmp eom /\
  frame_reachable vs C stk PG G tn fn inst s /\ active_inst fn inst s /\
  fmp_stage_rel D C' sm fmp0 raw0 eom restored stk PG G tn fn s lo t ts /\
  MEM inst.inst_opcode [LT; GT; EQ] /\ MEM op inst.inst_operands /\
  eval_operand op s = SOME x ==>
  ?y. eval_operand op t = SOME y /\
      fmp_value_rel sm (op_prov G op) {} x y
Proof
  strip_tac >> drule_all fmp_stage_frame_facts >> strip_tac >>
  `op_taint tn op = {}` by (gvs[taint_ok_def] >> metis_tac[]) >>
  `!v. op = Var v ==> ~retpc_var fn v` by
    (rpt strip_tac >>
     `opaque_use_ok fn` by
       gvs[o1_fn_shape_def, unitShapeDefsTheory.fn_shape_ok_def] >>
     gvs[] >> drule_all unitShapeDefsTheory.opaque_use_ok_retpc_use >>
     gvs[unitShapeDefsTheory.retpc_use_ok_def, MEM]) >>
  `inst.inst_opcode <> PHI` by gvs[MEM] >>
  drule_all fmp_stage_operand >> simp[]
QED

Theorem fmp_compare_variable_operands[local]:
  FDOM G SUBSET fn_pv P fn /\ fn_static_ptr_ok P fn /\
  MEM inst (fn_insts fn) /\ MEM inst.inst_opcode [LT;GT;EQ] /\
  inst.inst_operands = [p;q] /\
  (op_prov G p <> NONE \/ op_prov G q <> NONE) ==>
  ?u w. p = Var u /\ q = Var w /\ (u IN FDOM G \/ w IN FDOM G)
Proof
  strip_tac >>
  `ptr_use_static_ok P (fn_pv P fn) inst` by
    metis_tac[fn_static_ptr_ok_def] >>
  Cases_on `p` >> Cases_on `q` >>
  gvs[op_prov_def, FLOOKUP_DEF, SUBSET_DEF, ptr_use_static_ok_def,
      mem_read_ops_def, mem_write_ops_def, is_pointer_preserving_op_def, MEM] >>
  metis_tac[]
QED

Theorem fmp_compare_operand_results[local]:
  fmp_stage_ctx rpolicy D C C' vs vs' fmp eom /\
  frame_reachable vs C stk PG G tn fn inst s /\ active_inst fn inst s /\
  fmp_stage_rel D C' sm fmp0 raw0 eom restored stk PG G tn fn s lo t ts /\
  MEM inst.inst_opcode [LT;GT;EQ] /\ inst.inst_operands = [p;q] /\
  eval_operand p s = SOME x /\ eval_operand q s = SOME y ==>
  ?x' y'. eval_operand p t = SOME x' /\ eval_operand q t = SOME y' /\
    (w2n x < w2n y <=> w2n x' < w2n y') /\
    (w2n y < w2n x <=> w2n y' < w2n x') /\ (x = y <=> x' = y')
Proof
  strip_tac >> drule_all fmp_stage_frame_facts >> strip_tac >>
  `?x'. eval_operand p t = SOME x' /\
    fmp_value_rel sm (op_prov G p) {} x x'` by
    metis_tac[fmp_compare_operand, MEM] >>
  `?y'. eval_operand q t = SOME y' /\
    fmp_value_rel sm (op_prov G q) {} y y'` by
    metis_tac[fmp_compare_operand, MEM] >>
  qexistsl [`x'`,`y'`] >> simp[] >>
  Cases_on `op_prov G p = NONE /\ op_prov G q = NONE`
  >- (gvs[fmp_value_rel_def] >>
      `x = x' /\ y = y'` by metis_tac[ld_value_agree_clean] >> gvs[]) >>
  drule fmp_stage_prov_support >>
  disch_then (qspec_then `P` mp_tac) >> simp[] >> strip_tac >>
  `fn_static_ptr_ok P fn` by metis_tac[EVERY_MEM] >>
  `?u w. p = Var u /\ q = Var w /\ (u IN FDOM G \/ w IN FDOM G)` by
    metis_tac[fmp_compare_variable_operands] >> gvs[] >>
  `?b z. FLOOKUP G u = SOME (b,z) /\ FLOOKUP G w = SOME (b,z) /\
      0 < z /\ b <= w2n x /\ w2n x <= b+z /\
      b <= w2n y /\ w2n y <= b+z` by
    (qpat_x_assum `access_ok _ _ _ _ _` mp_tac >>
     gvs[access_ok_def, MEM] >> metis_tac[]) >>
  irule fmp_compare_pointer_values >>
  qexistsl [`b`,`fmp0`,`lo`,`s.vs_fmp`,`raw0`,`sm`,`z`] >>
  gvs[fmp_stage_rel_def, fmp_frame_rel_def, op_prov_def] >> metis_tac[]
QED

Theorem fmp_compare_step[local]:
  fmp_stage_ctx rpolicy D C C' vs vs' fmp eom /\
  frame_reachable vs C stk PG G tn fn inst s /\ active_inst fn inst s /\
  fmp_stage_rel D C' sm fmp0 raw0 eom restored stk PG G tn fn s lo t ts /\
  MEM inst.inst_opcode [LT;GT;EQ] /\ step_inst k C inst s = OK s1 ==>
  ?out x p q. inst.inst_outputs = [out] /\ inst.inst_operands = [p;q] /\
    s1 = update_var out x s /\
    step_inst k C' inst t = OK (update_var out x t)
Proof
  strip_tac >>
  `?p q out x y. inst.inst_operands = [p;q] /\ inst.inst_outputs = [out] /\
    eval_operand p s = SOME x /\ eval_operand q s = SOME y` by
    (qpat_x_assum `step_inst _ _ _ _ = _` mp_tac >> fs[MEM] >>
     simp[step_inst_non_invoke, step_inst_base_def, exec_pure2_def,
          AllCaseEqs()] >> metis_tac[]) >>
  drule_all fmp_compare_operand_results >> strip_tac >>
  qpat_x_assum `step_inst _ C inst s = _` mp_tac >> fs[MEM] >>
  (simp[step_inst_non_invoke] >>
   asm_simp_tac (srw_ss()) [step_inst_base_opcode_eqs] >>
   simp[exec_pure2_def, GREATER_DEF] >>
   strip_tac >> gvs[] >>
   qmatch_goalsub_abbrev_tac `update_var out value s` >>
   qexists `value` >> simp[])
QED

Theorem fmp_compare_terminating_result[local]:
  MEM inst.inst_opcode [LT;GT;EQ] /\
  step_inst k C inst s = r /\ terminates r ==>
  ?s1. r = OK s1
Proof
  strip_tac >> fs[MEM] >>
  qpat_x_assum `step_inst _ _ _ _ = _` mp_tac >>
  simp[step_inst_non_invoke] >>
  asm_simp_tac (srw_ss()) [step_inst_base_opcode_eqs] >>
  gvs[exec_pure2_def, AllCaseEqs(), passSimulationDefsTheory.terminates_def] >>
  strip_tac >> gvs[passSimulationDefsTheory.terminates_def]
QED

Theorem fmp_compare_update_taint[local]:
  MEM inst.inst_opcode [LT;GT;EQ] /\ inst.inst_operands = [p;q] /\
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
  Cases_on `eval_operand p s` >> simp[]
QED

Theorem fmp_compare_update_value[local]:
  MEM inst.inst_opcode [LT;GT;EQ] /\ inst.inst_operands = [p;q] /\
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
  strip_tac >> drule_all fmp_compare_update_taint >> strip_tac >>
  fs[MEM] >>
  simp[update_var_def, FLOOKUP_UPDATE, op_taint_def, step_prov_def,
       out_prov_def, set_prov_def, FLOOKUP_DRESTRICT, fmp_value_rel_def,
       ld_value_agree_scalar, word_agree_except_def]
QED

Theorem fmp_compare_update_post[local]:
  MEM inst.inst_opcode [LT;GT;EQ] /\ inst.inst_operands = [p;q] /\
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
  conj_tac >- metis_tac[fmp_compare_update_value] >>
  conj_tac >- metis_tac[fmp_compare_update_value] >>
  drule_all fmp_compare_update_taint >>
  disch_then (qspecl_then [`x`,`tn`,`s`] assume_tac) >>
  gvs[update_var_def, o1LowerDloadSharedTheory.ld_shared_agree_def]
QED

Theorem fmp_stage_sim_compare:
  fmp_stage_ctx rpolicy D C C' vs vs' fmp eom /\
  fmp0 = w2n vs'.vs_initial_fmp /\ raw0 = w2n fmp /\
  frame_reachable vs C stk PG G tn fn inst s /\ active_inst fn inst s /\
  ~s.vs_halted /\ ~in_revert_forward fn s /\
  MEM inst.inst_opcode [LT; GT; EQ] /\
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
  strip_tac >> drule_all fmp_compare_terminating_result >> strip_tac >>
  qpat_x_assum `r = _` SUBST_ALL_TAC >>
  drule_all fmp_compare_step >> strip_tac >>
  qabbrev_tac `t1 = update_var out x t` >>
  qexistsl [`k`,`OK t1`] >> simp_tac (srw_ss()) [] >>
  conj_tac >- simp[Abbr `t1`] >>
  irule fmp_compare_update_post >>
  fs[fmp_stage_rel_def] >> qexists `x` >> simp[Abbr `t1`] >> gvs[]
QED
