(* Parallel PHI effects preserve the original operand snapshot. *)
Theory lowerDloadSafetyPhiEffects
Ancestors
  lowerDloadSafetyUpdates lowerDloadSafetyValues lowerDloadSafetyRelation
  lowerDloadSafetyKernel ptrDiscipline venomState venomExecSemantics
  execEquivParamBase unitShapeDefs irSupply unitLabelMapIdentity finite_map pred_set list

Theorem ld_one_phi_source_success:
  ld_vars P A f /\ f.lf_src.vs_labels = f.lf_tgt.vs_labels /\
  f.lf_src.vs_prev_bb = f.lf_tgt.vs_prev_bb /\
  MEM inst (fn_insts f.lf_fn) /\
  eval_one_phi f.lf_tgt inst = SOME (out,y) ==>
  ?x. eval_one_phi f.lf_src inst = SOME (out,x)
Proof
  simp[eval_one_phi_def, AllCaseEqs()] >> strip_tac >> gvs[] >>
  rename1 `resolve_phi prev inst.inst_operands = SOME op` >>
  `IS_SOME (eval_operand op f.lf_src)` by
    (drule ld_vars_operand_defined >>
     disch_then (qspec_then `op` mp_tac) >>
     simp[] >>
     metis_tac[ld_inst_input_ir, resolve_phi_MEM]) >>
  Cases_on `eval_operand op f.lf_src` >> gvs[]
QED

Theorem ld_phis_source_success:
  !insts f ts.
  ld_vars P A f /\ f.lf_src.vs_labels = f.lf_tgt.vs_labels /\
  f.lf_src.vs_prev_bb = f.lf_tgt.vs_prev_bb /\
  EVERY (\i. MEM i (fn_insts f.lf_fn)) insts /\
  eval_phis f.lf_tgt insts = OK ts ==>
  ?ss. eval_phis f.lf_src insts = OK ss
Proof
  Induct_on `insts` >> rpt gen_tac >> simp[eval_phis_def] >>
  Cases_on `h.inst_opcode = PHI` >> simp[] >> strip_tac >>
  gvs[AllCaseEqs()] >>
  drule_all ld_one_phi_source_success >> strip_tac >>
  first_x_assum (drule_all_then strip_assume_tac) >>
  simp[]
QED

Theorem ld_phis_only_vars:
  !insts s ss. eval_phis s insts = OK ss ==>
  ss = s with vs_vars := ss.vs_vars
Proof
  Induct_on `insts` >> rpt gen_tac >> simp[eval_phis_def] >>
  Cases_on `h.inst_opcode = PHI` >> simp[] >> strip_tac >>
  gvs[AllCaseEqs()] >>
  first_x_assum drule >> strip_tac >>
  simp[update_var_def] >>
  pop_assum (fn th => once_rewrite_tac[th]) >> simp[]
QED

Theorem ld_phis_effect:
  ld_vars P A f /\ f.lf_src.vs_labels = f.lf_tgt.vs_labels /\
  f.lf_src.vs_prev_bb = f.lf_tgt.vs_prev_bb /\ tn.t_var = f.lf_tv /\
  EVERY (\i. MEM i (fn_insts f.lf_fn)) insts /\
  eval_phis f.lf_tgt insts = OK ts /\
  ld_memory lo A tn f.lf_src f.lf_tgt /\
  ld_nonghost tn f.lf_src f.lf_tgt ==>
  ?ss. eval_phis f.lf_src insts = OK ss /\
    ld_vars P A (f with <| lf_src := ss; lf_tgt := ts;
      lf_H := phis_prov f.lf_src.vs_prev_bb f.lf_H insts;
      lf_tv := phis_taint f.lf_src.vs_prev_bb tn insts |>) /\
    ld_memory lo A (tn with t_var := phis_taint f.lf_src.vs_prev_bb tn insts) ss ts /\
    ld_nonghost (tn with t_var := phis_taint f.lf_src.vs_prev_bb tn insts) ss ts /\
    ld_erase A o_f phis_prov f.lf_src.vs_prev_bb f.lf_H insts =
      phis_prov f.lf_src.vs_prev_bb (ld_erase A o_f f.lf_H) insts /\
    ss.vs_allocas = f.lf_src.vs_allocas /\
    ss.vs_alloca_next = f.lf_src.vs_alloca_next /\
    ss.vs_params = f.lf_src.vs_params /\
    ss.vs_current_bb = f.lf_src.vs_current_bb /\
    ss.vs_prev_bb = f.lf_src.vs_prev_bb /\
    ss.vs_inst_idx = f.lf_src.vs_inst_idx /\
    ss.vs_labels = f.lf_src.vs_labels /\
    ts.vs_allocas = f.lf_tgt.vs_allocas /\
    ts.vs_alloca_next = f.lf_tgt.vs_alloca_next /\
    ts.vs_params = f.lf_tgt.vs_params /\
    ts.vs_current_bb = f.lf_tgt.vs_current_bb /\
    ts.vs_prev_bb = f.lf_tgt.vs_prev_bb /\
    ts.vs_inst_idx = f.lf_tgt.vs_inst_idx /\
    ts.vs_labels = f.lf_tgt.vs_labels
Proof
  strip_tac >> drule_all ld_phis_source_success >> strip_tac >>
  drule_all_then assume_tac ld_vars_phis >>
  qexists_tac `ss` >> simp[ld_erase_phis_prov] >>
  `ss = f.lf_src with vs_vars := ss.vs_vars` by
    metis_tac[ld_phis_only_vars] >>
  `ts = f.lf_tgt with vs_vars := ts.vs_vars` by
    metis_tac[ld_phis_only_vars] >>
  qpat_x_assum `ss = _` (fn th => once_rewrite_tac[th]) >>
  qpat_x_assum `ts = _` (fn th => once_rewrite_tac[th]) >>
  gvs[ld_memory_def, ld_nonghost_def] >> metis_tac[]
QED
