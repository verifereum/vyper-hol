Theory frameRelocationGuardedSteps
Ancestors frameRelocationGuardedValues frameRelocationGhostCopy
  frameRelocationLocalSteps frameRelocationLocal frameOriginUpdates
  ptrDiscipline unitShapeDefs venomInst venomState finite_map

(* Opacity is forward closed by copy_phi_var, not by retpc_use_ok. *)
Theorem retpc_assign_classification:
  MEM inst (fn_insts fn) /\ inst.inst_opcode = ASSIGN /\
  inst.inst_operands = [Var w] /\ inst.inst_outputs = [v] ==>
  (~retpc_var fn v ==> ~retpc_var fn w)
Proof
  simp[retpc_var_def] >> rpt strip_tac >>
  qpat_x_assum `~copy_phi_var _ _ _` mp_tac >> simp[] >>
  irule (cj 2 copy_phi_var_rules) >>
  qexists_tac `inst` >> simp[]
QED

Theorem resolved_guarded_assign_step:
  local_rel (\u. F) (guarded_ptr Opaque L rv) (guarded_bytes Opaque rv tn) R Obs s t /\
  s.vs_labels = t.vs_labels /\ inst.inst_opcode = ASSIGN /\
  inst.inst_operands = [Var w] /\ inst.inst_outputs = [v] /\
  lookup_var w s = SOME x /\ (~Opaque v ==> ~Opaque w) /\
  (!a b x y. Obs a b ==> Obs (update_var v x a) (update_var v y b)) ==>
  ?y. eval_operand (Var w) t = SOME y /\
    step_inst_base inst s = OK (update_var v x s) /\
    step_inst_base inst t = OK (update_var v y t) /\
    local_rel (\u. F) (guarded_ptr Opaque L (origin_set rv [v] (FLOOKUP rv w)))
      (guarded_bytes Opaque (origin_set rv [v] (FLOOKUP rv w))
        (step_taint inst s (update_var v x s) tn)) R Obs
      (update_var v x s) (update_var v y t) /\
    step_prov PG (SND o_f rv) inst (update_var v x s) =
      SND o_f (origin_set rv [v] (FLOOKUP rv w))
Proof
  strip_tac >>
  `step_prov PG (SND o_f rv) inst (update_var v x s) =
     SND o_f (origin_set rv [v] (FLOOKUP rv w))` by
    (irule assign_prov_erasure >> simp[]) >>
  `step_taint inst s (update_var v x s) tn =
     tn with t_var := tn.t_var |+ (v,op_taint tn (Var w))` by
    (irule assign_taint_copy >> simp[]) >>
  simp[] >> irule local_rel_assign_copy >> simp[] >>
  qexistsl_tac [`guarded_bytes Opaque rv tn`, `\u. F`, `guarded_ptr Opaque L rv`] >>
  simp[guarded_ptr_other, guarded_bytes_other, guarded_ptr_output, guarded_bytes_output]
QED

Theorem retpc_guarded_assign_step:
  local_rel (\u. F) (guarded_ptr (retpc_var fn) L rv)
    (guarded_bytes (retpc_var fn) rv tn) R Obs s t /\
  MEM inst (fn_insts fn) /\ s.vs_labels = t.vs_labels /\
  inst.inst_opcode = ASSIGN /\ inst.inst_operands = [Var w] /\
  inst.inst_outputs = [v] /\ lookup_var w s = SOME x /\
  (!a b x y. Obs a b ==> Obs (update_var v x a) (update_var v y b)) ==>
  ?y. eval_operand (Var w) t = SOME y /\
    step_inst_base inst s = OK (update_var v x s) /\
    step_inst_base inst t = OK (update_var v y t) /\
    local_rel (\u. F)
      (guarded_ptr (retpc_var fn) L (origin_set rv [v] (FLOOKUP rv w)))
      (guarded_bytes (retpc_var fn) (origin_set rv [v] (FLOOKUP rv w))
        (step_taint inst s (update_var v x s) tn)) R Obs
      (update_var v x s) (update_var v y t) /\
    step_prov PG (SND o_f rv) inst (update_var v x s) =
      SND o_f (origin_set rv [v] (FLOOKUP rv w))
Proof
  strip_tac >> irule resolved_guarded_assign_step >> simp[] >>
  metis_tac[retpc_assign_classification]
QED
