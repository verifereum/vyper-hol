(* RETPC_PARAM values remain opaque under relocation. *)
Theory lowerDloadSafetyRetpcEffects
Ancestors
  lowerDloadSafetyKernel lowerDloadSafetyRelation lowerDloadSafetyUpdates
  lowerDloadSafetyValues ptrDiscipline venomState venomExecSemantics
  venomInst unitShapeDefs memLocDefs codegenRel contextCodegenRel finite_map list pred_set words

Theorem ld_retpc_taint[local]:
  inst.inst_opcode = RETPC_PARAM /\ inst.inst_operands = [Lit idx] ==>
  step_taint inst s (update_var v x s) tn =
    tn with t_var := set_var_taint tn.t_var inst.inst_outputs {}
Proof
  strip_tac >>
  simp[step_taint_def, out_taint_def, written_taint_def, mem_taint_def,
       update_var_def, new_site_bytes_def, step_writes_def, range_bytes_def,
       source_memory_write_ranges_def, store_taint_def, adopt_reset_def,
       imm_taint_def, eval_operand_def, FLOOKUP_DEF, taint_component_equality] >>
  SET_TAC[]
QED

Theorem ld_retpc_write[local]:
  ld_vars P A f /\ MEM inst (fn_insts f.lf_fn) /\
  inst.inst_opcode = RETPC_PARAM /\ inst.inst_outputs = [out] ==>
  ld_vars P A (f with <|
    lf_src := update_var out f.lf_src.vs_return_pc_token f.lf_src;
    lf_tgt := update_var out f.lf_tgt.vs_return_pc_token f.lf_tgt;
    lf_H := set_prov f.lf_H [out] NONE;
    lf_tv := set_var_taint f.lf_tv [out] {} |> )
Proof
  strip_tac >>
  `retpc_var f.lf_fn out` by
    (simp[retpc_var_def] >> irule copy_phi_var_seed >>
     qexists_tac `inst` >> simp[]) >>
  `MEM out (fn_ir_vars f.lf_fn)` by metis_tac[ld_inst_output_ir, MEM] >>
  pure_rewrite_tac[update_var_def] >> irule ld_vars_write >>
  simp[set_var_taint_def, FLOOKUP_UPDATE]
QED

Theorem ld_retpc_param_effect:
  ld_vars P A f /\ tn.t_var = f.lf_tv /\
  MEM inst (fn_insts f.lf_fn) /\ inst.inst_opcode = RETPC_PARAM /\
  step_inst_base inst f.lf_tgt = OK ts /\
  ld_memory lo A tn f.lf_src f.lf_tgt /\ ld_nonghost tn f.lf_src f.lf_tgt ==>
  ?ss. step_inst_base inst f.lf_src = OK ss /\
    ld_vars P A (f with <| lf_src := ss; lf_tgt := ts;
      lf_H := set_prov f.lf_H inst.inst_outputs NONE;
      lf_tv := (step_taint inst f.lf_src ss tn).t_var |> ) /\
    ld_memory lo A (step_taint inst f.lf_src ss tn) ss ts /\
    ld_nonghost (step_taint inst f.lf_src ss tn) ss ts /\
    ld_erase A o_f set_prov f.lf_H inst.inst_outputs NONE =
      step_prov (MAP (OPTION_MAP (ld_erase A)) f.lf_Q)
        (ld_erase A o_f f.lf_H) inst ss /\
    ss.vs_allocas = f.lf_src.vs_allocas /\
    ss.vs_alloca_next = f.lf_src.vs_alloca_next /\
    ss.vs_params = f.lf_src.vs_params /\
    ss.vs_current_bb = f.lf_src.vs_current_bb /\
    ss.vs_prev_bb = f.lf_src.vs_prev_bb /\
    ss.vs_inst_idx = f.lf_src.vs_inst_idx /\
    ss.vs_labels = f.lf_src.vs_labels /\
    ss.vs_return_pc_token = f.lf_src.vs_return_pc_token /\
    ts.vs_allocas = f.lf_tgt.vs_allocas /\
    ts.vs_alloca_next = f.lf_tgt.vs_alloca_next /\
    ts.vs_params = f.lf_tgt.vs_params /\
    ts.vs_current_bb = f.lf_tgt.vs_current_bb /\
    ts.vs_prev_bb = f.lf_tgt.vs_prev_bb /\
    ts.vs_inst_idx = f.lf_tgt.vs_inst_idx /\
    ts.vs_labels = f.lf_tgt.vs_labels /\
    ts.vs_return_pc_token = f.lf_tgt.vs_return_pc_token
Proof
  strip_tac >>
  qpat_x_assum `step_inst_base inst f.lf_tgt = OK ts` mp_tac >>
  pure_once_rewrite_tac[step_inst_base_def] >>
  asm_rewrite_tac[opcode_case_def] >>
  simp[AllCaseEqs()] >> rpt strip_tac >> gvs[] >>
  `step_taint inst f.lf_src
      (update_var out f.lf_src.vs_return_pc_token f.lf_src) tn =
    tn with t_var := set_var_taint tn.t_var [out] {}` by
    (drule_all ld_retpc_taint >> simp[]) >>
  simp[] >>
  conj_tac >- (irule ld_retpc_write >> simp[] >> qexists_tac `inst` >> simp[]) >>
  conj_tac >- (irule ld_memory_update_var >> simp[]) >>
  conj_tac >- (irule ld_nonghost_update_var >> simp[]) >>
  simp[ld_erase_set_prov, step_prov_def, out_prov_def, update_var_def]
QED
