(* Non-call transport.  Suspended frames retain their actual saved locals;
   all shared facts below are about the current memory, not saved memory. *)
Theory readonlyInvokeCopyFwdSteps
Ancestors
  readonlyInvokeCopyFwdValues readonlyInvokeCopyFwdMemory
  readonlyInvokeCopyFwdEffects readonlyInvokeCopyFwdRel
  taintAgree ptrDiscipline venomState venomExecSemantics
  finite_map words list pred_set

Theorem ricf_live_stack_update_var:
  ricf_live_stack_agree D ids tn maps stk targets s t ==>
  ricf_live_stack_agree D ids (tn with t_var := tv) maps stk targets
    (update_var out x s) (update_var out y t)
Proof
  simp[ricf_live_stack_agree_def, merge_callee_state_def, update_var_def]
QED

(* A local binding changes neither the current memory nor any suspended
   frame.  Its output provenance and taint are supplied by the opcode. *)
Theorem ricf_bind_live:
  ricf_frame_agree D X sites PG G tn s t /\
  ricf_live_stack_agree D ids tn maps stk targets s t /\
  ricf_value_agree sites p m x y ==>
  ricf_frame_agree D X sites PG (set_prov G [out] p)
    (tn with t_var := set_var_taint tn.t_var [out] m)
    (update_var out x s) (update_var out y t) /\
  ricf_live_stack_agree D ids
    (tn with t_var := set_var_taint tn.t_var [out] m) maps stk targets
    (update_var out x s) (update_var out y t)
Proof
  metis_tac[ricf_frame_agree_update_var, ricf_live_stack_update_var]
QED

Theorem ricf_assign_live:
  ricf_frame_agree D X sites PG G tn s t /\
  ricf_live_stack_agree D ids tn maps stk targets s t /\
  inst.inst_opcode = ASSIGN /\ inst.inst_operands = [op] /\
  inst.inst_outputs = [out] /\ eval_operand op s = SOME x ==>
  ?y. step_inst_base inst s = OK (update_var out x s) /\
      step_inst_base inst t = OK (update_var out y t) /\
      ricf_frame_agree D X sites PG (set_prov G [out] (op_prov G op))
        (tn with t_var := set_var_taint tn.t_var [out] (op_taint tn op))
        (update_var out x s) (update_var out y t) /\
      ricf_live_stack_agree D ids
        (tn with t_var := set_var_taint tn.t_var [out] (op_taint tn op))
        maps stk targets (update_var out x s) (update_var out y t)
Proof
  strip_tac >> drule_all ricf_frame_agree_operand >> strip_tac >>
  qexists_tac `y` >> simp[step_inst_base_opcode_eqs] >>
  irule ricf_bind_live >> metis_tac[]
QED

Theorem ricf_param_live:
  ricf_frame_agree D X sites PG G tn s t /\
  ricf_live_stack_agree D ids tn maps stk targets s t /\
  inst.inst_opcode = PARAM /\ inst.inst_operands = [Lit idx] /\
  inst.inst_outputs = [out] /\ w2n idx < LENGTH s.vs_params ==>
  step_inst_base inst s = OK (update_var out (EL (w2n idx) s.vs_params) s) /\
  step_inst_base inst t = OK (update_var out (EL (w2n idx) t.vs_params) t) /\
  ricf_frame_agree D X sites PG (set_prov G [out] (EL (w2n idx) PG))
    (tn with t_var := set_var_taint tn.t_var [out] {})
    (update_var out (EL (w2n idx) s.vs_params) s)
    (update_var out (EL (w2n idx) t.vs_params) t) /\
  ricf_live_stack_agree D ids
    (tn with t_var := set_var_taint tn.t_var [out] {}) maps stk targets
    (update_var out (EL (w2n idx) s.vs_params) s)
    (update_var out (EL (w2n idx) t.vs_params) t)
Proof
  strip_tac >>
  `LENGTH s.vs_params = LENGTH t.vs_params` by
    metis_tac[ricf_frame_agree_params, ricf_params_agree_def] >>
  simp[step_inst_base_opcode_eqs] >> irule ricf_bind_live >>
  metis_tac[ricf_frame_agree_param]
QED

(* Diagnostic boundary fact: activating a translation cannot describe a
   caller whose destination variable is still unchanged by MCOPY/NOP. *)
Theorem ricf_active_site_unchanged_var:
  ricf_frame_agree D X sites PG G tn s t /\
  FLOOKUP G v = SOME (db,sz) /\
  FLOOKUP sites (db,sz) = SOME (db,sb,sz) /\
  v IN FDOM s.vs_vars /\ t.vs_vars ' v = s.vs_vars ' v ==>
  (n2w sb : bytes32) = n2w db
Proof
  strip_tac >>
  `ricf_value_agree sites (SOME (db,sz)) (op_taint tn (Var v))
      (s.vs_vars ' v) (s.vs_vars ' v)` by
    metis_tac[ricf_frame_agree_def] >>
  `ricf_sites_ok sites` by metis_tac[ricf_frame_agree_sites] >>
  drule_all ricf_value_agree_relocated >>
  disch_then (fn th =>
    qpat_x_assum `ricf_value_agree _ _ _ _ _`
      (mp_tac o REWRITE_RULE [th])) >>
  simp_tac bool_ss [] >> strip_tac >>
  qpat_x_assum `_ = _ + _ - _` mp_tac >>
  POP_ASSUM_LIST (K ALL_TAC) >> simp[wordsTheory.WORD_EQ_SUB_LADD]
QED
