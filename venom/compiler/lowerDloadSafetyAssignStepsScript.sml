(* ASSIGN copies selected identities, masked scalars and opaque tokens. *)
Theory lowerDloadSafetyAssignSteps
Ancestors
  lowerDloadSafetyUpdates lowerDloadSafetyValues lowerDloadSafetyRelation
  lowerDloadSafetyKernel ptrDiscipline unitShapeDefs venomState
  venomExecSemantics venomInst execEquivParamBase finite_map pred_set list
  lowerDloadPointerClosure pointerConfinedDefs irSupply unitLabelMapIdentity
  codegenRel

Theorem ld_assign_input_nonopaque[local]:
  MEM inst (fn_insts fn) /\ inst.inst_opcode = ASSIGN /\
  MEM out inst.inst_outputs /\ ~retpc_var fn out /\
  inst.inst_operands = [Var v] ==> ~retpc_var fn v
Proof
  simp[retpc_var_def] >> metis_tac[copy_phi_var_assign]
QED

Theorem ld_assign_selected_output[local]:
  ld_vars P A f /\ MEM inst (fn_insts f.lf_fn) /\
  inst.inst_opcode = ASSIGN /\ inst.inst_operands = [op] /\
  MEM out inst.inst_outputs /\ op_prov f.lf_H op = SOME a ==>
  out IN fn_pv P f.lf_fn
Proof
  Cases_on `op` >> simp[op_prov_def] >> strip_tac >>
  `s IN fn_pv P f.lf_fn` by
    (gvs[ld_vars_def, SUBSET_DEF, FLOOKUP_DEF] >> metis_tac[]) >>
  gvs[fn_pv_def] >> irule ld_pointer_preserving_output >>
  qexistsl_tac [`inst`, `s`] >> simp[is_pointer_preserving_op_def]
QED

Theorem ld_vars_assign[local]:
  ld_vars P A f /\ f.lf_src.vs_labels = f.lf_tgt.vs_labels /\
  tn.t_var = f.lf_tv /\ MEM inst (fn_insts f.lf_fn) /\
  inst.inst_opcode = ASSIGN /\ step_inst_base inst f.lf_tgt = OK ts ==>
  ?ss. step_inst_base inst f.lf_src = OK ss /\
    ld_vars P A (f with <| lf_src := ss; lf_tgt := ts;
      lf_H := set_prov f.lf_H inst.inst_outputs
        (first_prov f.lf_H inst.inst_operands);
      lf_tv := (step_taint inst f.lf_src ss tn).t_var |> )
Proof
  strip_tac >>
  qpat_x_assum `step_inst_base inst f.lf_tgt = OK ts` mp_tac >>
  simp[Once step_inst_base_def, AllCaseEqs()] >> strip_tac >> gvs[] >>
  rename1 `eval_operand op f.lf_tgt = SOME y` >>
  `IS_SOME (eval_operand op f.lf_src)` by
    (drule ld_vars_operand_defined >>
     disch_then (qspec_then `op` mp_tac) >> simp[] >>
     impl_tac >- metis_tac[ld_inst_input_ir, MEM] >> simp[]) >>
  Cases_on `eval_operand op f.lf_src` >> gvs[] >>
  rename1 `eval_operand op f.lf_src = SOME x` >>
  qexists_tac `update_var out x f.lf_src` >>
  simp[Once step_inst_base_def] >>
  simp[step_taint_def, out_taint_def, first_prov_def] >>
  simp[update_var_def] >> irule ld_vars_write >>
  simp[set_var_taint_def, FLOOKUP_UPDATE] >>
  conj_tac
  >- (Cases_on `op_prov f.lf_H op` >> simp[] >> rpt strip_tac >>
      irule ld_assign_selected_output >> metis_tac[MEM]) >>
  reverse conj_tac
  >- (irule ld_inst_output_ir >> metis_tac[MEM]) >>
  strip_tac >>
  `!v. op = Var v ==> ~retpc_var f.lf_fn v` by
    metis_tac[ld_assign_input_nonopaque, MEM] >>
  drule_all ld_vars_operand_agree >>
  Cases_on `op_prov f.lf_H op` >> simp[]
QED

Theorem ld_assign_success[local]:
  inst.inst_opcode = ASSIGN /\ step_inst_base inst s = OK s' ==>
  ?op out x. inst.inst_operands = [op] /\ inst.inst_outputs = [out] /\
    eval_operand op s = SOME x /\ s' = update_var out x s
Proof
  strip_tac >>
  qpat_x_assum `step_inst_base inst s = OK s'` mp_tac >>
  simp[Once step_inst_base_def, AllCaseEqs()] >> metis_tac[]
QED

Theorem ld_assign_effect:
  ld_vars P A f /\ f.lf_src.vs_labels = f.lf_tgt.vs_labels /\
  tn.t_var = f.lf_tv /\ MEM inst (fn_insts f.lf_fn) /\
  inst.inst_opcode = ASSIGN /\ step_inst_base inst f.lf_tgt = OK ts /\
  ld_memory lo A tn f.lf_src f.lf_tgt /\
  ld_nonghost tn f.lf_src f.lf_tgt ==>
  ?ss. step_inst_base inst f.lf_src = OK ss /\
    ld_vars P A (f with <| lf_src := ss; lf_tgt := ts;
      lf_H := set_prov f.lf_H inst.inst_outputs
        (first_prov f.lf_H inst.inst_operands);
      lf_tv := (step_taint inst f.lf_src ss tn).t_var |> ) /\
    ld_memory lo A (step_taint inst f.lf_src ss tn) ss ts /\
    ld_nonghost (step_taint inst f.lf_src ss tn) ss ts /\
    ld_erase A o_f set_prov f.lf_H inst.inst_outputs
      (first_prov f.lf_H inst.inst_operands) =
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
  strip_tac >> drule_all ld_vars_assign >> strip_tac >>
  drule_all ld_assign_success >> strip_tac >>
  qpat_x_assum `step_inst_base inst f.lf_tgt = OK ts` mp_tac >>
  strip_tac >> drule_all ld_assign_success >> strip_tac >> gvs[] >>
  gvs[ld_memory_def, ld_nonghost_def] >>
  simp[update_var_def, ld_memory_def, ld_nonghost_def,
       step_taint_def, mem_taint_def, imm_taint_def, adopt_reset_def,
       store_taint_def, ld_erase_set_prov, step_prov_def, out_prov_def,
       first_prov_def, ld_erase_op_prov, new_site_bytes_def,
       step_writes_def, source_memory_write_ranges_def, range_bytes_def,
       written_taint_def] >>
  conj_tac
  >- (rpt strip_tac >>
      qpat_x_assum `!k b c n j. _` irule >> metis_tac[]) >>
  Cases_on `op_prov f.lf_H op` >> simp[]
QED
