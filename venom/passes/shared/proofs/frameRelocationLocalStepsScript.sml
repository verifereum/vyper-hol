Theory frameRelocationLocalSteps
Ancestors frameRelocationLocal frameRelocationOpaque frameRelocationValues
  venomExecSemantics venomState venomInst

(* This boundary constructs real ASSIGN steps. Its value obligations concern
   only the copied pair, not preservation of the entire post-state. *)
Theorem local_rel_assign:
  local_rel P ptr_rel B R Obs s t /\ s.vs_labels = t.vs_labels /\
  inst.inst_opcode = ASSIGN /\ inst.inst_operands = [op] /\
  inst.inst_outputs = [v] /\ eval_operand op s = SOME x /\
  (!u. u <> v ==> (P' u ==> P u) /\
    (!a b. ptr_rel u a b ==> ptr_rel' u a b) /\
    (!a b. B u a b ==> B' u a b)) /\
  (!y. eval_operand op t = SOME y ==>
    (P' v ==> x = y) /\ ptr_rel' v x y /\ B' v x y) /\
  (!a b x y. Obs a b ==> Obs (update_var v x a) (update_var v y b)) ==>
  ?y. eval_operand op t = SOME y /\
    step_inst_base inst s = OK (update_var v x s) /\
    step_inst_base inst t = OK (update_var v y t) /\
    local_rel P' ptr_rel' B' R Obs (update_var v x s) (update_var v y t)
Proof
  strip_tac >>
  `variable_domains s t` by metis_tac[local_rel_domains] >>
  drule_all opaque_assign_definedness >> strip_tac >>
  qexists_tac `y` >> simp[] >>
  irule local_rel_update_observation_invariant >> simp[] >>
  goal_assum (drule_at Any) >> simp[]
QED

Theorem local_rel_assign_scalar:
  local_rel P ptr_rel B R Obs s t /\ s.vs_labels = t.vs_labels /\
  inst.inst_opcode = ASSIGN /\ inst.inst_operands = [op] /\
  inst.inst_outputs = [v] /\ eval_operand op s = SOME x /\
  (!w. op = Var w ==> P w) /\
  (!u. u <> v ==> (P' u ==> P u) /\
    (!a b. ptr_rel u a b ==> ptr_rel' u a b) /\
    (!a b. B u a b ==> B' u a b)) /\
  ptr_rel' v x x /\ B' v x x /\
  (!a b x y. Obs a b ==> Obs (update_var v x a) (update_var v y b)) ==>
  ?y. eval_operand op t = SOME y /\
    step_inst_base inst s = OK (update_var v x s) /\
    step_inst_base inst t = OK (update_var v y t) /\
    local_rel P' ptr_rel' B' R Obs (update_var v x s) (update_var v y t)
Proof
  strip_tac >>
  `variables_agree_on P s t` by metis_tac[local_rel_scalars] >>
  `eval_operand op s = eval_operand op t` by
    (irule scalar_operand_agreement >> simp[] >> qexists_tac `P` >> simp[]) >>
  irule local_rel_assign >> gvs[] >>
  goal_assum (drule_at Any) >> simp[]
QED

(* Pointer and partial-byte copy use the source variable's independent
   predicates; equality of the copied machine words is not required. *)
Theorem local_rel_assign_copy:
  local_rel P ptr_rel B R Obs s t /\ s.vs_labels = t.vs_labels /\
  inst.inst_opcode = ASSIGN /\ inst.inst_operands = [Var w] /\
  inst.inst_outputs = [v] /\ lookup_var w s = SOME x /\
  (!u. u <> v ==> (P' u ==> P u) /\
    (!a b. ptr_rel u a b ==> ptr_rel' u a b) /\
    (!a b. B u a b ==> B' u a b)) /\
  (P' v ==> P w) /\
  (!a b. ptr_rel w a b ==> ptr_rel' v a b) /\
  (!a b. B w a b ==> B' v a b) /\
  (!a b x y. Obs a b ==> Obs (update_var v x a) (update_var v y b)) ==>
  ?y. eval_operand (Var w) t = SOME y /\
    step_inst_base inst s = OK (update_var v x s) /\
    step_inst_base inst t = OK (update_var v y t) /\
    local_rel P' ptr_rel' B' R Obs (update_var v x s) (update_var v y t)
Proof
  strip_tac >> irule local_rel_assign >> simp[eval_operand_def] >>
  conj_tac
  >- (rpt strip_tac
      >- (drule local_rel_scalars >> simp[variables_agree_on_def] >> strip_tac >>
          `P w` by metis_tac[] >>
          first_x_assum (qspec_then `w` mp_tac) >> simp[])
      >- metis_tac[local_rel_pointer]
      >> metis_tac[local_rel_bytes]) >>
  goal_assum (drule_at Any) >> simp[]
QED

(* Opaque copy imposes no equality obligation on the chosen operand. *)
Theorem local_rel_assign_opaque:
  local_rel P (\u a b. T) (\u a b. T) R Obs s t /\
  s.vs_labels = t.vs_labels /\ ~P v /\
  inst.inst_opcode = ASSIGN /\ inst.inst_operands = [op] /\
  inst.inst_outputs = [v] /\ eval_operand op s = SOME x /\
  (!a b x y. Obs a b ==> Obs (update_var v x a) (update_var v y b)) ==>
  ?y. eval_operand op t = SOME y /\
    step_inst_base inst s = OK (update_var v x s) /\
    step_inst_base inst t = OK (update_var v y t) /\
    local_rel P (\u a b. T) (\u a b. T) R Obs
      (update_var v x s) (update_var v y t)
Proof
  strip_tac >> irule local_rel_assign >> simp[] >>
  goal_assum (drule_at Any) >> simp[]
QED
