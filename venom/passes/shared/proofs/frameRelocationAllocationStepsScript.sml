Theory frameRelocationAllocationSteps
Ancestors frameRelocationLocal frameRelocationDemand frameRelocationValues
  frameRelocationOpaque venomState venomExecSemantics venomInst finite_map words

Theorem local_rel_field_frame:
  local_rel P ptr B R Obs s t /\
  s'.vs_vars = s.vs_vars /\ t'.vs_vars = t.vs_vars /\
  s'.vs_memory = s.vs_memory /\ t'.vs_memory = t.vs_memory /\
  (!a b. next a b ==> R a b) /\ Obs' s' t' ==>
  local_rel P ptr B next Obs' s' t'
Proof
  simp[local_rel_def, variable_domains_def, variables_agree_on_def,
       local_values_def, lookup_var_def, demand_agree_def] >> metis_tac[]
QED

Theorem local_rel_alloca_assign_step:
  inst.inst_opcode = ALLOCA /\ inst.inst_operands = [Lit sz] /\
  inst.inst_outputs = [v] /\
  target.inst_opcode = ASSIGN /\ target.inst_operands = [Lit addr] /\
  target.inst_outputs = [v] /\
  ((?oldsz. FLOOKUP s.vs_allocas inst.inst_id = SOME (b,oldsz) /\ s0 = s) \/
   (FLOOKUP s.vs_allocas inst.inst_id = NONE /\ b = s.vs_alloca_next /\
    s0 = s with <|vs_allocas := s.vs_allocas |+ (inst.inst_id,(b,w2n sz));
                 vs_alloca_next := b + w2n sz|>)) /\
  local_rel P ptr B R Obs s t /\
  (!a c. next a c ==> R a c) /\
  (!u. u <> v ==> (P' u ==> P u) /\
    (!x y. ptr u x y ==> ptr' u x y) /\
    (!x y. B u x y ==> B' u x y)) /\
  (P' v ==> n2w b = addr) /\ ptr' v (n2w b) addr /\ B' v (n2w b) addr /\
  Obs (update_var v (n2w b) s0) (update_var v addr t) ==>
  ?s' t'. step_inst_base inst s = OK s' /\ step_inst_base target t = OK t' /\
    local_rel P' ptr' B' next Obs s' t'
Proof
  rpt gen_tac >> disch_tac >>
  `s0.vs_vars = s.vs_vars /\ s0.vs_memory = s.vs_memory` by
    (fs[] >> gvs[]) >>
  `local_rel P ptr B R (\s t. T) s0 t` by
    (irule local_rel_field_frame >> simp[] >>
     qexistsl_tac [`Obs`, `R`, `s`, `t`] >> fs[]) >>
  `local_rel P' ptr' B' R (\s t. T)
     (update_var v (n2w b) s0) (update_var v addr t)` by
    (irule local_rel_update >> gns[] >>
     qexistsl_tac [`B`, `P`, `ptr`] >> gns[]) >>
  qexistsl_tac [`update_var v (n2w b) s0`, `update_var v addr t`] >>
  conj_tac >- (fs[] >> gvs[step_inst_base_def, exec_alloca_def]) >>
  conj_tac >- gns[step_inst_base_def, eval_operand_def] >>
  irule local_rel_field_frame >> simp[] >>
  goal_assum (drule_at Any) >> fs[]
QED
