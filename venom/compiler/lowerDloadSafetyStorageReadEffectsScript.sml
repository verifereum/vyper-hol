(* Keyed storage observations and ordinary read effects. *)
Theory lowerDloadSafetyStorageReadEffects
Ancestors
  lowerDloadSafetyKernel lowerDloadSafetyReadSteps lowerDloadSafetyUpdates
  lowerDloadSafetyValues ptrDiscipline venomState venomExecSemantics
  vfmState finite_map list pred_set unitShapeDefs memLocDefs codegenRel
  contextCodegenRel venomInst pointerConfinedDefs

Theorem ld_nonghost_sload:
  ld_nonghost tn s t ==>
  word_agree_except (key_taint tn.t_stor k) (sload k s) (sload k t)
Proof
  simp[ld_nonghost_def] >> strip_tac >>
  qpat_x_assum `!a. (_ with storage := _) = _ /\ _`
    (qspec_then `s.vs_call_ctx.cc_address` mp_tac) >>
  simp[storage_agree_except_def, sload_def, contract_storage_def,
       lookup_account_def, lookup_storage_def]
QED

Theorem ld_nonghost_tload:
  ld_nonghost tn s t ==>
  word_agree_except (key_taint tn.t_trans k) (tload k s) (tload k t)
Proof
  simp[ld_nonghost_def] >> strip_tac >>
  qpat_x_assum `!a. storage_agree_except _ _ _`
    (qspec_then `s.vs_call_ctx.cc_address` mp_tac) >>
  simp[storage_agree_except_def, tload_def, contract_transient_def,
       lookup_storage_def]
QED

Theorem ld_storage_read_operands[local]:
  ld_vars P A f /\ ld_nonghost tn f.lf_src f.lf_tgt /\
  fn_ptr_ok P f.lf_fn /\ fn_shape_ok f.lf_fn /\
  MEM inst (fn_insts f.lf_fn) /\ taint_ok f.lf_fn tn inst f.lf_src /\
  tn.t_var = f.lf_tv /\ MEM inst.inst_opcode [SLOAD;TLOAD] ==>
  eval_operands inst.inst_operands f.lf_src =
  eval_operands inst.inst_operands f.lf_tgt
Proof
  strip_tac >> irule ld_vars_numeric_operands_equal >> simp[] >>
  `f.lf_src.vs_labels = f.lf_tgt.vs_labels` by
    gvs[ld_nonghost_def] >>
  simp[] >> conj_tac >- gvs[MEM] >>
  reverse conj_tac >- (qexists_tac `tn` >> simp[]) >>
  qexistsl_tac [`A`, `P`] >> simp[] >>
  gen_tac >> strip_tac >> conj_tac >- metis_tac[ld_inst_input_ir] >>
  irule ld_ptr_use_scalar >> simp[] >> qexists_tac `inst` >>
  gvs[MEM, is_pointer_preserving_op_def, mem_write_ops_def, mem_read_ops_def]
QED

Theorem ld_storage_read_vars[local]:
  ld_vars P A f /\ ld_nonghost tn f.lf_src f.lf_tgt /\
  fn_ptr_ok P f.lf_fn /\ fn_shape_ok f.lf_fn /\
  MEM inst (fn_insts f.lf_fn) /\ taint_ok f.lf_fn tn inst f.lf_src /\
  tn.t_var = f.lf_tv /\ MEM inst.inst_opcode [SLOAD;TLOAD] /\
  step_inst_base inst f.lf_tgt = OK ts ==>
  ?ss. step_inst_base inst f.lf_src = OK ss /\
    ld_vars P A (f with <| lf_src := ss; lf_tgt := ts;
      lf_H := set_prov f.lf_H inst.inst_outputs NONE;
      lf_tv := set_var_taint f.lf_tv inst.inst_outputs (out_taint tn inst f.lf_src) |> )
Proof
  strip_tac >> drule_all ld_storage_read_operands >> strip_tac >>
  `!v. MEM v inst.inst_outputs ==> MEM v (fn_ir_vars f.lf_fn)` by
    metis_tac[ld_inst_output_ir] >>
  gvs[MEM] >>
  qpat_x_assum `step_inst_base inst f.lf_tgt = OK ts` mp_tac >>
  pure_once_rewrite_tac[step_inst_base_def] >>
  asm_rewrite_tac[opcode_case_def] >> strip_tac >>
  pure_once_rewrite_tac[step_inst_base_def] >>
  asm_rewrite_tac[opcode_case_def] >>
  irule ld_vars_exec_read1 >> simp[] >>
  rpt strip_tac >>
  qpat_x_assum `exec_read1 _ _ _ = OK ts` mp_tac >>
  simp[exec_read1_def, AllCaseEqs()] >> rpt strip_tac >> gvs[] >>
  gvs[eval_operands_def, AllCaseEqs()] >>
  simp[out_taint_def] >>
  metis_tac[ld_nonghost_sload, ld_nonghost_tload]
QED

Theorem ld_storage_read_success[local]:
  MEM inst.inst_opcode [SLOAD;TLOAD] /\ step_inst_base inst s = OK s' ==>
  ?out x. inst.inst_outputs = [out] /\ s' = update_var out x s
Proof
  strip_tac >> gvs[MEM] >>
  qpat_x_assum `step_inst_base inst s = OK s'` mp_tac >>
  pure_once_rewrite_tac[step_inst_base_def] >>
  asm_rewrite_tac[opcode_case_def] >>
  simp[exec_read1_def, AllCaseEqs()] >> rpt strip_tac >> gvs[] >> metis_tac[]
QED

Theorem ld_storage_read_taint[local]:
  MEM inst.inst_opcode [SLOAD;TLOAD] ==>
  step_taint inst s (update_var v x s) tn =
    tn with t_var := set_var_taint tn.t_var inst.inst_outputs (out_taint tn inst s)
Proof
  strip_tac >>
  `written_taint tn inst s = {}` by
    (namedCases_on `inst.inst_operands` ["", "a rest"]
     >- gvs[MEM, written_taint_def] >>
     namedCases_on `rest` ["", "b tail"]
     >- gvs[MEM, written_taint_def] >>
     namedCases_on `tail` ["", "c more"]
     >- gvs[MEM, written_taint_def] >>
     Cases_on `more` >> gvs[MEM, written_taint_def]) >>
  gvs[MEM] >>
  simp[step_taint_def, mem_taint_def, update_var_def,
       new_site_bytes_def, step_writes_def, range_bytes_def,
       source_memory_write_ranges_def, store_taint_def, adopt_reset_def,
       imm_taint_def, FLOOKUP_DEF, taint_component_equality] >> SET_TAC[]
QED

Theorem ld_storage_read_effect:
  ld_vars P A f /\ fn_ptr_ok P f.lf_fn /\ fn_shape_ok f.lf_fn /\
  MEM inst (fn_insts f.lf_fn) /\ tn.t_var = f.lf_tv /\
  taint_ok f.lf_fn tn inst f.lf_src /\
  MEM inst.inst_opcode [SLOAD;TLOAD] /\ step_inst_base inst f.lf_tgt = OK ts /\
  ld_memory lo A tn f.lf_src f.lf_tgt /\ ld_nonghost tn f.lf_src f.lf_tgt ==>
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
  strip_tac >> drule_all ld_storage_read_vars >> strip_tac >>
  drule_all ld_storage_read_success >> strip_tac >>
  qpat_x_assum `step_inst_base inst f.lf_tgt = OK ts` mp_tac >>
  strip_tac >> drule_all ld_storage_read_success >> strip_tac >> gvs[] >>
  `step_taint inst f.lf_src (update_var out x f.lf_src) tn =
     tn with t_var := set_var_taint tn.t_var inst.inst_outputs
       (out_taint tn inst f.lf_src)` by
    (irule ld_storage_read_taint >> simp[]) >>
  (simp[] >>
   conj_tac >- (irule ld_memory_update_var >> simp[]) >>
   conj_tac >- (irule ld_nonghost_update_var >> simp[]) >>
   simp[ld_erase_set_prov, step_prov_def, out_prov_def])
QED
