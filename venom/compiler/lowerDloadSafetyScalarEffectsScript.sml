(* Non-pointer pure arithmetic, separated from selected affine arithmetic. *)
Theory lowerDloadSafetyScalarEffects
Ancestors
  lowerDloadSafetyPureSteps lowerDloadSafetyUpdates lowerDloadSafetyValues
  lowerDloadSafetyRelation lowerDloadSafetyKernel ptrDiscipline unitShapeDefs
  venomState venomInst venomExecSemantics pointerConfinedDefs memLocDefs codegenRel
  finite_map list pred_set

Theorem ld_scalar_operands_equal[local]:
  ld_vars P A f /\ f.lf_src.vs_labels = f.lf_tgt.vs_labels /\
  tn.t_var = f.lf_tv /\ fn_ptr_ok P f.lf_fn /\ fn_shape_ok f.lf_fn /\
  MEM inst (fn_insts f.lf_fn) /\ taint_ok f.lf_fn tn inst f.lf_src /\
  MEM inst.inst_opcode
    [MUL; Div; Mod; SDIV; SMOD; Exp; ADDMOD; MULMOD; SLT; SGT;
     ISZERO; AND; OR; XOR; NOT; SIGNEXTEND; BYTE; OFFSET] ==>
  eval_operands inst.inst_operands f.lf_src =
  eval_operands inst.inst_operands f.lf_tgt
Proof
  strip_tac >> drule ld_vars_numeric_operands_equal >> disch_then irule >> simp[] >>
  reverse conj_tac
  >- (conj_tac >- (gvs[] >> simp[]) >> qexists_tac `tn` >> simp[]) >>
  rpt gen_tac >> strip_tac >> conj_tac
  >- (irule ld_inst_input_ir >> metis_tac[]) >>
  irule ld_ptr_use_scalar >> simp[] >> qexists_tac `inst` >> simp[] >>
  gvs[] >> simp[is_pointer_preserving_op_def, mem_write_ops_def, mem_read_ops_def]
QED

Theorem ld_scalar_vars[local]:
  ld_vars P A f /\ MEM inst (fn_insts f.lf_fn) /\
  eval_operands inst.inst_operands f.lf_src =
    eval_operands inst.inst_operands f.lf_tgt /\
  MEM inst.inst_opcode
    [MUL; Div; Mod; SDIV; SMOD; Exp; ADDMOD; MULMOD; SLT; SGT;
     ISZERO; AND; OR; XOR; NOT; SIGNEXTEND; BYTE; OFFSET] /\
  step_inst_base inst f.lf_tgt = OK ts ==>
  ?ss. step_inst_base inst f.lf_src = OK ss /\
    ld_vars P A (f with <| lf_src := ss; lf_tgt := ts;
      lf_H := set_prov f.lf_H inst.inst_outputs NONE;
      lf_tv := set_var_taint f.lf_tv inst.inst_outputs {} |> )
Proof
  strip_tac >>
  `!v. MEM v inst.inst_outputs ==> MEM v (fn_ir_vars f.lf_fn)` by
    metis_tac[ld_inst_output_ir] >>
  gvs[MEM] >>
  qpat_x_assum `step_inst_base inst f.lf_tgt = OK ts` mp_tac >>
  pure_once_rewrite_tac[step_inst_base_def] >>
  asm_rewrite_tac[opcode_case_def] >> strip_tac >>
  FIRST [drule_all ld_vars_exec_pure1, drule_all ld_vars_exec_pure2,
         drule_all ld_vars_exec_pure3] >>
  strip_tac >> qexists_tac `ss` >> simp[Once step_inst_base_def]
QED

Theorem ld_scalar_success[local]:
  MEM inst.inst_opcode
    [MUL; Div; Mod; SDIV; SMOD; Exp; ADDMOD; MULMOD; SLT; SGT;
     ISZERO; AND; OR; XOR; NOT; SIGNEXTEND; BYTE; OFFSET] /\
  step_inst_base inst s = OK s' ==>
  ?out x. inst.inst_outputs = [out] /\ s' = update_var out x s
Proof
  strip_tac >> gvs[MEM] >>
  qpat_x_assum `step_inst_base inst s = OK s'` mp_tac >>
  pure_once_rewrite_tac[step_inst_base_def] >>
  asm_rewrite_tac[opcode_case_def] >>
  simp[exec_pure1_def, exec_pure2_def, exec_pure3_def, AllCaseEqs()] >>
  rpt strip_tac >> gvs[] >> metis_tac[]
QED

Theorem ld_scalar_taint[local]:
  MEM inst.inst_opcode
    [MUL; Div; Mod; SDIV; SMOD; Exp; ADDMOD; MULMOD; SLT; SGT;
     ISZERO; AND; OR; XOR; NOT; SIGNEXTEND; BYTE; OFFSET;
     INITIAL_FMP; BUMP] /\ s'.vs_allocas = s.vs_allocas /\
  s'.vs_fmp = s.vs_fmp ==>
  step_taint inst s s' tn =
    tn with t_var := set_var_taint tn.t_var inst.inst_outputs {}
Proof
  strip_tac >>
  `inst.inst_opcode <> MLOAD /\ inst.inst_opcode <> ILOAD /\
   inst.inst_opcode <> SLOAD /\ inst.inst_opcode <> TLOAD /\
   inst.inst_opcode <> ASSIGN /\ inst.inst_opcode <> SHL /\
   inst.inst_opcode <> SHR /\ inst.inst_opcode <> SAR /\
   inst.inst_opcode <> MSTORE /\ inst.inst_opcode <> ISTORE /\
   inst.inst_opcode <> MCOPY /\ inst.inst_opcode <> SSTORE /\
   inst.inst_opcode <> TSTORE /\ inst.inst_opcode <> CALL` by (gvs[MEM] >> simp[]) >>
  `out_taint tn inst s = {}` by
    (namedCases_on `inst.inst_operands` ["", "a rest"]
     >- simp[out_taint_def] >>
     namedCases_on `rest` ["", "b tail"]
     >- (Cases_on `eval_operand a s` >> simp[out_taint_def]) >>
     Cases_on `tail`
     >- (Cases_on `eval_operand a s` >> simp[out_taint_def]) >>
     simp[out_taint_def]) >>
  `written_taint tn inst s = {}` by
    (namedCases_on `inst.inst_operands` ["", "a rest"]
     >- simp[written_taint_def] >>
     namedCases_on `rest` ["", "b tail"]
     >- simp[written_taint_def] >>
     namedCases_on `tail` ["", "c more"]
     >- simp[written_taint_def] >>
     Cases_on `more` >> simp[written_taint_def]) >>
  `source_memory_write_ranges inst s = []` by
    (gvs[MEM] >> simp[source_memory_write_ranges_def]) >>
  simp[step_taint_def, mem_taint_def, update_var_def,
       new_site_bytes_def, step_writes_def, range_bytes_def,
       store_taint_def, adopt_reset_def, imm_taint_def,
       FLOOKUP_DEF, taint_component_equality] >> SET_TAC[]
QED
Theorem ld_scalar_pure_effect:
  ld_vars P A f /\ f.lf_src.vs_labels = f.lf_tgt.vs_labels /\
  tn.t_var = f.lf_tv /\ fn_ptr_ok P f.lf_fn /\ fn_shape_ok f.lf_fn /\
  MEM inst (fn_insts f.lf_fn) /\ taint_ok f.lf_fn tn inst f.lf_src /\
  MEM inst.inst_opcode
    [MUL; Div; Mod; SDIV; SMOD; Exp; ADDMOD; MULMOD; SLT; SGT;
     ISZERO; AND; OR; XOR; NOT; SIGNEXTEND; BYTE; OFFSET] /\
  step_inst_base inst f.lf_tgt = OK ts /\
  ld_memory lo A tn f.lf_src f.lf_tgt /\
  ld_nonghost tn f.lf_src f.lf_tgt ==>
  ?ss. step_inst_base inst f.lf_src = OK ss /\
    ld_vars P A (f with <| lf_src := ss; lf_tgt := ts;
      lf_H := set_prov f.lf_H inst.inst_outputs NONE;
      lf_tv := (step_taint inst f.lf_src ss tn).t_var |> ) /\
    ld_memory lo A (step_taint inst f.lf_src ss tn) ss ts /\
    ld_nonghost (step_taint inst f.lf_src ss tn) ss ts /\
    ld_erase A o_f set_prov f.lf_H inst.inst_outputs NONE =
      step_prov PG (ld_erase A o_f f.lf_H) inst ss /\
    ss.vs_allocas = f.lf_src.vs_allocas /\
    ss.vs_alloca_next = f.lf_src.vs_alloca_next /\
    ss.vs_params = f.lf_src.vs_params /\
    ss.vs_current_bb = f.lf_src.vs_current_bb /\
    ss.vs_prev_bb = f.lf_src.vs_prev_bb /\
    ss.vs_inst_idx = f.lf_src.vs_inst_idx /\
    ts.vs_allocas = f.lf_tgt.vs_allocas /\
    ts.vs_alloca_next = f.lf_tgt.vs_alloca_next /\
    ts.vs_params = f.lf_tgt.vs_params /\
    ts.vs_current_bb = f.lf_tgt.vs_current_bb /\
    ts.vs_prev_bb = f.lf_tgt.vs_prev_bb /\
    ts.vs_inst_idx = f.lf_tgt.vs_inst_idx
Proof
  strip_tac >> drule_all ld_scalar_operands_equal >> strip_tac >>
  drule_all ld_scalar_vars >> strip_tac >>
  drule_all ld_scalar_success >> strip_tac >>
  qpat_x_assum `step_inst_base inst f.lf_tgt = OK ts` mp_tac >>
  strip_tac >> drule_all ld_scalar_success >> strip_tac >> gvs[] >>
  (`step_taint inst f.lf_src (update_var out x f.lf_src) tn =
     tn with t_var := set_var_taint tn.t_var inst.inst_outputs {}` by
    (irule ld_scalar_taint >> simp[update_var_def]) >>
  simp[] >>
  conj_tac
  >- (irule ld_memory_update_var >> simp[]) >>
  conj_tac
  >- (irule ld_nonghost_update_var >> simp[]) >>
  simp[ld_erase_set_prov, step_prov_def, out_prov_def, update_var_def])
QED

Theorem ld_residual_scalar_vars[local]:
  ld_vars P A f /\ MEM inst (fn_insts f.lf_fn) /\
  eval_operands inst.inst_operands f.lf_src =
    eval_operands inst.inst_operands f.lf_tgt /\
  f.lf_src.vs_initial_fmp = f.lf_tgt.vs_initial_fmp /\
  MEM inst.inst_opcode [INITIAL_FMP;BUMP] /\
  step_inst_base inst f.lf_tgt = OK ts ==>
  ?ss. step_inst_base inst f.lf_src = OK ss /\
    ld_vars P A (f with <|lf_src := ss; lf_tgt := ts;
      lf_H := set_prov f.lf_H inst.inst_outputs NONE;
      lf_tv := set_var_taint f.lf_tv inst.inst_outputs {}|>)
Proof
  strip_tac >>
  `!v. MEM v inst.inst_outputs ==> MEM v (fn_ir_vars f.lf_fn)` by
    metis_tac[ld_inst_output_ir] >>
  gvs[MEM] >>
  qpat_x_assum `step_inst_base inst f.lf_tgt = OK ts` mp_tac >>
  pure_once_rewrite_tac[step_inst_base_def] >>
  asm_rewrite_tac[opcode_case_def] >>
  simp[AllCaseEqs()] >> strip_tac >> gvs[]
  >- (pure_rewrite_tac[update_var_def] >> irule ld_vars_write >>
      simp[set_var_taint_def, FLOOKUP_UPDATE, ld_word_agree_empty]) >>
  gvs[eval_operands_def, AllCaseEqs()] >>
  simp[set_prov_def, set_var_taint_def] >>
  irule ld_vars_write_two >> simp[]
QED

Theorem ld_residual_scalar_effect:
  ld_vars P A f /\ f.lf_src.vs_labels = f.lf_tgt.vs_labels /\
  tn.t_var = f.lf_tv /\ fn_ptr_ok P f.lf_fn /\ fn_shape_ok f.lf_fn /\
  MEM inst (fn_insts f.lf_fn) /\ taint_ok f.lf_fn tn inst f.lf_src /\
  MEM inst.inst_opcode [INITIAL_FMP;BUMP] /\
  step_inst_base inst f.lf_tgt = OK ts /\
  ld_memory lo A tn f.lf_src f.lf_tgt /\
  ld_nonghost tn f.lf_src f.lf_tgt ==>
  ?ss. step_inst_base inst f.lf_src = OK ss /\
    ld_vars P A (f with <|lf_src := ss; lf_tgt := ts;
      lf_H := set_prov f.lf_H inst.inst_outputs NONE;
      lf_tv := (step_taint inst f.lf_src ss tn).t_var|>) /\
    ld_memory lo A (step_taint inst f.lf_src ss tn) ss ts /\
    ld_nonghost (step_taint inst f.lf_src ss tn) ss ts /\
    ld_erase A o_f set_prov f.lf_H inst.inst_outputs NONE =
      step_prov PG (ld_erase A o_f f.lf_H) inst ss /\
    ss.vs_allocas = f.lf_src.vs_allocas /\
    ss.vs_alloca_next = f.lf_src.vs_alloca_next /\
    ss.vs_params = f.lf_src.vs_params /\
    ss.vs_current_bb = f.lf_src.vs_current_bb /\
    ss.vs_prev_bb = f.lf_src.vs_prev_bb /\
    ss.vs_inst_idx = f.lf_src.vs_inst_idx /\
    ts.vs_allocas = f.lf_tgt.vs_allocas /\
    ts.vs_alloca_next = f.lf_tgt.vs_alloca_next /\
    ts.vs_params = f.lf_tgt.vs_params /\
    ts.vs_current_bb = f.lf_tgt.vs_current_bb /\
    ts.vs_prev_bb = f.lf_tgt.vs_prev_bb /\
    ts.vs_inst_idx = f.lf_tgt.vs_inst_idx
Proof
  strip_tac >>
  `eval_operands inst.inst_operands f.lf_src =
   eval_operands inst.inst_operands f.lf_tgt` by
    (Cases_on `inst.inst_opcode = BUMP`
     >- (drule_all ld_vars_bump_operands_equal >> simp[]) >>
     gvs[MEM] >>
     qpat_x_assum `step_inst_base inst f.lf_tgt = OK ts` mp_tac >>
     simp[Once step_inst_base_def, AllCaseEqs()] >>
     strip_tac >> gvs[eval_operands_def]) >>
  `f.lf_src.vs_initial_fmp = f.lf_tgt.vs_initial_fmp` by
    metis_tac[ld_nonghost_initial_fmp] >>
  drule_all ld_residual_scalar_vars >> strip_tac >>
  `ss.vs_allocas = f.lf_src.vs_allocas /\ ss.vs_fmp = f.lf_src.vs_fmp` by
    (qpat_x_assum `step_inst_base inst f.lf_src = OK ss` mp_tac >>
     gvs[MEM] >> pure_once_rewrite_tac[step_inst_base_def] >>
     asm_rewrite_tac[opcode_case_def] >>
     simp[AllCaseEqs()] >> rpt strip_tac >> gvs[update_var_def]) >>
  `step_taint inst f.lf_src ss tn =
   tn with t_var := set_var_taint tn.t_var inst.inst_outputs {}` by
    (irule ld_scalar_taint >> simp[]) >>
  qexists_tac `ss` >> asm_rewrite_tac[] >>
  gvs[MEM] >>
  map_every (fn pat => qpat_x_assum pat mp_tac)
    [`step_inst_base inst f.lf_src = OK ss`,
     `step_inst_base inst f.lf_tgt = OK ts`] >>
  pure_once_rewrite_tac[step_inst_base_def] >>
  asm_rewrite_tac[opcode_case_def] >>
  simp[AllCaseEqs()] >> rpt strip_tac >> gvs[] >>
  FIRST [
    (irule ld_memory_update_var >> simp[]),
    (irule ld_nonghost_update_var >> simp[]),
    simp[ld_erase_set_prov, step_prov_def, out_prov_def, update_var_def]] >>
  FIRST [
    (qmatch_goalsub_abbrev_tac `ld_memory lo A tn src tgt` >>
     `ld_memory lo A (tn with t_var := tn.t_var) src tgt` suffices_by simp[] >>
     unabbrev_all_tac >> irule ld_memory_update_var >> simp[]),
    (qmatch_goalsub_abbrev_tac `ld_nonghost tn src tgt` >>
     `ld_nonghost (tn with t_var := tn.t_var) src tgt` suffices_by simp[] >>
     unabbrev_all_tac >> irule ld_nonghost_update_var >> simp[])]
QED

val _ = if null (hyp ld_residual_scalar_effect) andalso
           null (hyp ld_vars_write_two) then ()
        else raise Fail "residual scalar boundary has hypotheses";
