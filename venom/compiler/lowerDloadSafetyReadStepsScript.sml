(* Masked read observations consumed at the execution-combinator boundary. *)
Theory lowerDloadSafetyReadSteps
Ancestors
  lowerDloadSafetyUpdates lowerDloadSafetyValues venomExecSemantics venomState
  ptrDiscipline finite_map

Theorem ld_vars_exec_read0:
  ld_vars P A f /\
  (!v. MEM v inst.inst_outputs ==> MEM v (fn_ir_vars f.lf_fn)) /\
  word_agree_except m (g f.lf_src) (g f.lf_tgt) /\
  exec_read0 g inst f.lf_tgt = OK ts ==>
  ?ss. exec_read0 g inst f.lf_src = OK ss /\
    ld_vars P A (f with <|
      lf_src := ss; lf_tgt := ts;
      lf_H := set_prov f.lf_H inst.inst_outputs NONE;
      lf_tv := set_var_taint f.lf_tv inst.inst_outputs m |> )
Proof
  simp[exec_read0_def, AllCaseEqs()] >> rpt strip_tac >>
  gvs[] >> simp[update_var_def] >>
  irule ld_vars_write >> simp[set_var_taint_def, FLOOKUP_UPDATE]
QED

Theorem ld_vars_exec_read1:
  ld_vars P A f /\
  (!v. MEM v inst.inst_outputs ==> MEM v (fn_ir_vars f.lf_fn)) /\
  (!op y. MEM op inst.inst_operands /\
      eval_operand op f.lf_tgt = SOME y ==>
      ?x. eval_operand op f.lf_src = SOME x /\
          word_agree_except m (g x f.lf_src) (g y f.lf_tgt)) /\
  exec_read1 g inst f.lf_tgt = OK ts ==>
  ?ss. exec_read1 g inst f.lf_src = OK ss /\
    ld_vars P A (f with <|
      lf_src := ss; lf_tgt := ts;
      lf_H := set_prov f.lf_H inst.inst_outputs NONE;
      lf_tv := set_var_taint f.lf_tv inst.inst_outputs m |> )
Proof
  simp[exec_read1_def, AllCaseEqs()] >> rpt strip_tac >>
  gvs[] >> simp[update_var_def] >>
  irule ld_vars_write >> simp[set_var_taint_def, FLOOKUP_UPDATE]
QED
