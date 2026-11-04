(* Successful scalar computations, independent of location assembly. *)
Theory lowerDloadSafetyPureSteps
Ancestors
  lowerDloadSafetyUpdates lowerDloadSafetyValues venomExecSemantics venomState
  ptrDiscipline finite_map

Theorem ld_vars_exec_pure1:
  ld_vars P A f /\
  (!v. MEM v inst.inst_outputs ==> MEM v (fn_ir_vars f.lf_fn)) /\
  eval_operands inst.inst_operands f.lf_src =
    eval_operands inst.inst_operands f.lf_tgt /\
  exec_pure1 g inst f.lf_tgt = OK ts ==>
  ?ss. exec_pure1 g inst f.lf_src = OK ss /\
    ld_vars P A (f with <|
      lf_src := ss; lf_tgt := ts;
      lf_H := set_prov f.lf_H inst.inst_outputs NONE;
      lf_tv := set_var_taint f.lf_tv inst.inst_outputs {} |> )
Proof
  simp[exec_pure1_def, AllCaseEqs()] >> rpt strip_tac >>
  gvs[eval_operands_def, AllCaseEqs()] >>
  simp[update_var_def] >>
  irule ld_vars_write >> simp[set_var_taint_def, FLOOKUP_UPDATE, ld_word_agree_empty]
QED

Theorem ld_vars_exec_pure2:
  ld_vars P A f /\
  (!v. MEM v inst.inst_outputs ==> MEM v (fn_ir_vars f.lf_fn)) /\
  eval_operands inst.inst_operands f.lf_src =
    eval_operands inst.inst_operands f.lf_tgt /\
  exec_pure2 g inst f.lf_tgt = OK ts ==>
  ?ss. exec_pure2 g inst f.lf_src = OK ss /\
    ld_vars P A (f with <|
      lf_src := ss; lf_tgt := ts;
      lf_H := set_prov f.lf_H inst.inst_outputs NONE;
      lf_tv := set_var_taint f.lf_tv inst.inst_outputs {} |> )
Proof
  simp[exec_pure2_def, AllCaseEqs()] >> rpt strip_tac >>
  gvs[eval_operands_def, AllCaseEqs()] >>
  simp[update_var_def] >>
  irule ld_vars_write >>
  simp[set_var_taint_def, FLOOKUP_UPDATE, ld_word_agree_empty]
QED

Theorem ld_vars_exec_pure3:
  ld_vars P A f /\
  (!v. MEM v inst.inst_outputs ==> MEM v (fn_ir_vars f.lf_fn)) /\
  eval_operands inst.inst_operands f.lf_src =
    eval_operands inst.inst_operands f.lf_tgt /\
  exec_pure3 g inst f.lf_tgt = OK ts ==>
  ?ss. exec_pure3 g inst f.lf_src = OK ss /\
    ld_vars P A (f with <|
      lf_src := ss; lf_tgt := ts;
      lf_H := set_prov f.lf_H inst.inst_outputs NONE;
      lf_tv := set_var_taint f.lf_tv inst.inst_outputs {} |> )
Proof
  simp[exec_pure3_def, AllCaseEqs()] >> rpt strip_tac >>
  gvs[eval_operands_def, AllCaseEqs()] >>
  simp[update_var_def] >>
  irule ld_vars_write >>
  simp[set_var_taint_def, FLOOKUP_UPDATE, ld_word_agree_empty]
QED
