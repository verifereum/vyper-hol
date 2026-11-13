Theory concretizePtrDallocaRuntimeSteps
Ancestors
  concretizePtrDallocaAffine concretizePtrObservationInterface
  concretizePtrDallocaBoundaryProbes concretizePtrBPReverse
  concretizePtrDallocaGhostInterface concretizePtrPrefixLedger o1FrameLockstep
  concretizePtrDallocaProducer concretizePtrSourceOwnership
  frameRelocationTaintOrder venomExecSemantics
  ptrDiscipline venomState venomInst finite_map pred_set list

(* Only demanded arithmetic operands need scalar agreement.  In particular,
   this does not assert equality of all syntactically nonpointer variables. *)
Theorem ptr_dalloca_runtime_affine_values:
  fn_ptr_ok P fn /\ MEM inst (fn_insts fn) /\
  (inst.inst_opcode = ADD \/ inst.inst_opcode = SUB) /\
  inst.inst_operands = [a;b] /\ FDOM G SUBSET fn_pv P fn /\
  ptr_dalloca_ghost_vars G tn.t_var s Gt tnt.t_var t /\
  ptr_ledger_erases dyn births TG G /\
  ptr_mixed_vars births positions TG tn f g s t /\
  s.vs_labels = t.vs_labels /\
  (!op. MEM op [a;b] ==> ptr_nonopaque_operand f op /\ op_taint tn op = {}) /\
  out_prov PGt Gt inst t = SOME site ==>
  !op. MEM op [a;b] ==> eval_operand op s = eval_operand op t
Proof
  strip_tac >>
  `~(?v w. a = Var v /\ b = Var w /\
           v IN fn_pv P fn /\ w IN fn_pv P fn)` by
    metis_tac[ptr_reverse_affine] >>
  `!op. MEM op [a;b] /\ op_prov G op = NONE ==>
        eval_operand op s = eval_operand op t` by
    (rpt strip_tac >> irule ptr_mixed_scalar_eval >>
     goal_assum (drule_at Any) >> metis_tac[]) >>
  gvs[out_prov_def, ptr_dalloca_ghost_vars_def] >>
  Cases_on `a` >> Cases_on `b` >>
  gvs[first_prov_def, op_prov_def, AllCaseEqs()] >>
  rpt strip_tac >> gvs[eval_operand_def] >>
  fs[SUBSET_DEF, FLOOKUP_DEF] >> metis_tac[eval_operand_def]
QED

Theorem ptr_dalloca_runtime_affine_sites:
  fn_ptr_ok P fn /\ MEM inst (fn_insts fn) /\
  (inst.inst_opcode = ADD \/ inst.inst_opcode = SUB) /\
  inst.inst_operands = [a;b] /\ FDOM G SUBSET fn_pv P fn /\
  ptr_ledger_erases dyn births TG G /\
  (!v site. FLOOKUP Gt v = SOME site ==>
     FLOOKUP G v = SOME site /\ FLOOKUP TG v = NONE) /\
  (!v site. FLOOKUP TG v = NONE /\ FLOOKUP G v = SOME site ==>
     FLOOKUP Gt v = SOME site) ==>
  (!site. out_prov PGt Gt inst t = SOME site ==>
     out_prov PG G inst s = SOME site /\ out_prov PT TG inst s = NONE) /\
  (!site. out_prov PT TG inst s = NONE /\
     out_prov PG G inst s = SOME site ==>
     out_prov PGt Gt inst t = SOME site)
Proof
  strip_tac >>
  `~(?v w. a = Var v /\ b = Var w /\
           v IN fn_pv P fn /\ w IN fn_pv P fn)` by
    metis_tac[ptr_reverse_affine] >>
  `!v. FLOOKUP G v = NONE ==> FLOOKUP TG v = NONE` by
    (rpt strip_tac >>
     qpat_x_assum `ptr_ledger_erases _ _ _ _` mp_tac >>
     simp[ptr_ledger_erases_def] >> strip_tac >>
     qpat_x_assum `!v. ptr_owner_erases _ _ _ _`
       (qspec_then `v` mp_tac) >>
     Cases_on `FLOOKUP TG v` >> gvs[ptr_owner_erases_def, FLOOKUP_DEF] >>
     metis_tac[]) >>
  `!v. v NOTIN fn_pv P fn ==> FLOOKUP G v = NONE` by
    (fs[SUBSET_DEF, FLOOKUP_DEF] >> metis_tac[]) >>
  `!v. v NOTIN fn_pv P fn ==> FLOOKUP Gt v = NONE` by
    (rpt strip_tac >> Cases_on `FLOOKUP Gt v` >> gvs[] >>
     rename1 `FLOOKUP Gt v = SOME surviving` >>
     qpat_x_assum `!v site. FLOOKUP Gt v = SOME site ==> _`
       (qspecl_then [`v`,`surviving`] mp_tac) >> simp[]) >>
  qpat_x_assum `ptr_ledger_erases _ _ _ _` kall_tac >>
  qpat_x_assum `FDOM G SUBSET _` kall_tac >>
  gvs[out_prov_def] >> Cases_on `a` >> Cases_on `b` >>
  gvs[first_prov_def, op_prov_def, AllCaseEqs()] >>
  metis_tac[optionTheory.option_nchotomy]
QED

(* The update boundary is independent of the producer opcode.  Its site
   premises will be discharged from input operands, never from output maps. *)
Theorem ptr_dalloca_runtime_set_sites:
  (!v site. FLOOKUP Gt v = SOME site ==>
     FLOOKUP G v = SOME site /\ FLOOKUP TG v = NONE) /\
  (!v site. FLOOKUP TG v = NONE /\ FLOOKUP G v = SOME site ==>
     FLOOKUP Gt v = SOME site) /\
  (!site. pt = SOME site ==> p = SOME site /\ own = NONE) /\
  (!site. own = NONE /\ p = SOME site ==> pt = SOME site) ==>
  (!v site. FLOOKUP (set_prov Gt outs pt) v = SOME site ==>
     FLOOKUP (set_prov G outs p) v = SOME site /\
     FLOOKUP (set_prov TG outs own) v = NONE) /\
  (!v site. FLOOKUP (set_prov TG outs own) v = NONE /\
     FLOOKUP (set_prov G outs p) v = SOME site ==>
     FLOOKUP (set_prov Gt outs pt) v = SOME site)
Proof
  strip_tac >> simp[FLOOKUP_set_prov] >>
  rpt strip_tac >> Cases_on `MEM v outs` >> gvs[] >>
  Cases_on `outs = [v]` >> gvs[] >> metis_tac[]
QED

Theorem ptr_dalloca_runtime_set_vars:
  ptr_dalloca_ghost_vars G V s Gt Vt t /\
  (!site. pt = SOME site ==> p = SOME site) /\ mt SUBSET m /\
  (!v. ~MEM v outs ==>
     lookup_var v s' = lookup_var v s /\ lookup_var v t' = lookup_var v t) /\
  (!v site. outs = [v] /\ pt = SOME site ==>
     lookup_var v s' = lookup_var v t') ==>
  ptr_dalloca_ghost_vars (set_prov G outs p) (set_var_taint V outs m) s'
    (set_prov Gt outs pt) (set_var_taint Vt outs mt) t'
Proof
  simp[ptr_dalloca_ghost_vars_def, op_taint_def] >> strip_tac >>
  conj_tac
  >- (irule set_var_taint_subset >> simp[]) >>
  simp[FLOOKUP_set_prov] >> rpt strip_tac >>
  Cases_on `MEM v outs` >> gvs[] >>
  Cases_on `outs = [v]` >> gvs[] >> metis_tac[]
QED

Theorem ptr_dalloca_runtime_param_sites:
  inst.inst_opcode = PARAM /\
  LENGTH PT = LENGTH PG /\ LENGTH PG = LENGTH PGt /\
  (!k site. k < LENGTH PG /\ EL k PGt = SOME site ==>
     EL k PG = SOME site /\ EL k PT = NONE) /\
  (!k site. k < LENGTH PG /\ EL k PT = NONE /\ EL k PG = SOME site ==>
     EL k PGt = SOME site) ==>
  (!site. out_prov PGt Gt inst t = SOME site ==>
     out_prov PG G inst s = SOME site /\ out_prov PT TG inst s = NONE) /\
  (!site. out_prov PT TG inst s = NONE /\ out_prov PG G inst s = SOME site ==>
     out_prov PGt Gt inst t = SOME site)
Proof
  strip_tac >> gvs[out_prov_def] >>
  Cases_on `inst.inst_operands` >> gvs[] >>
  rename1 `op::ops` >> Cases_on `ops` >> gvs[] >>
  Cases_on `op` >> gvs[] >> rename1 `[Lit idx]` >>
  Cases_on `w2n idx < LENGTH PGt` >> gvs[] >> metis_tac[]
QED

Theorem ptr_dalloca_runtime_param_values:
  inst.inst_opcode = PARAM /\
  (!k site. k < LENGTH PGt /\ EL k PGt = SOME site ==>
     EL k s.vs_params = EL k t.vs_params) /\
  step_inst fuel C inst s = OK s' /\
  step_inst fuelt Ct inst t = OK t' /\
  out_prov PGt Gt inst t' = SOME site ==>
  !v. MEM v inst.inst_outputs ==> lookup_var v s' = lookup_var v t'
Proof
  strip_tac >>
  qpat_x_assum `step_inst fuel _ _ _ = _` mp_tac >>
  qpat_x_assum `step_inst fuelt _ _ _ = _` mp_tac >>
  simp[step_inst_non_invoke] >> pure_rewrite_tac[step_inst_base_def] >>
  asm_rewrite_tac[] >> simp[Once opcode_case_def] >>
  simp[AllCaseEqs()] >> rpt strip_tac >>
  gvs[out_prov_def, lookup_var_def, update_var_def, FLOOKUP_UPDATE]
QED

Theorem ptr_dalloca_runtime_dynamic_values:
  inst.inst_opcode = DALLOCA /\ s.vs_fmp = t.vs_fmp /\
  eval_operands inst.inst_operands s = eval_operands inst.inst_operands t /\
  step_inst fuel C inst s = OK s' /\
  step_inst fuelt Ct inst t = OK t' ==>
  s'.vs_fmp = t'.vs_fmp /\
  (!v. MEM v inst.inst_outputs ==> lookup_var v s' = lookup_var v t') /\
  out_prov PG G inst s' = out_prov PGt Gt inst t'
Proof
  strip_tac >> drule_all ptr_dalloca_execution >>
  disch_then (qspec_then `C` strip_assume_tac) >>
  `step_inst fuel C inst s = step_inst 0 C inst s` by
    gvs[step_inst_non_invoke] >>
  gvs[out_prov_def, lookup_var_def, update_var_def, FLOOKUP_UPDATE]
QED

Theorem ptr_dalloca_runtime_assign_sites:
  inst.inst_opcode = ASSIGN /\ inst.inst_operands = [op] /\
  (!v site. FLOOKUP Gt v = SOME site ==>
     FLOOKUP G v = SOME site /\ FLOOKUP TG v = NONE) /\
  (!v site. FLOOKUP TG v = NONE /\ FLOOKUP G v = SOME site ==>
     FLOOKUP Gt v = SOME site) ==>
  (!site. out_prov PGt Gt inst t = SOME site ==>
     out_prov PG G inst s = SOME site /\ out_prov PT TG inst s = NONE) /\
  (!site. out_prov PT TG inst s = NONE /\ out_prov PG G inst s = SOME site ==>
     out_prov PGt Gt inst t = SOME site)
Proof
  strip_tac >> Cases_on `op` >>
  gvs[out_prov_def, first_prov_def, op_prov_def] >>
  gvs[AllCaseEqs()] >> metis_tac[optionTheory.option_nchotomy]
QED

Theorem ptr_dalloca_runtime_copy_values:
  (inst.inst_opcode = ASSIGN \/ inst.inst_opcode = ADD \/ inst.inst_opcode = SUB) /\
  (!op. MEM op inst.inst_operands ==> eval_operand op s = eval_operand op t) /\
  step_inst fuel C inst s = OK s' /\
  step_inst fuelt Ct inst t = OK t' ==>
  !v. MEM v inst.inst_outputs ==> lookup_var v s' = lookup_var v t'
Proof
  strip_tac >>
  qpat_x_assum `step_inst fuel _ _ _ = _` mp_tac >>
  qpat_x_assum `step_inst fuelt _ _ _ = _` mp_tac >>
  simp[step_inst_non_invoke] >> pure_rewrite_tac[step_inst_base_def] >>
  asm_rewrite_tac[] >> pure_rewrite_tac[opcode_case_def] >>
  simp[exec_pure1_def, exec_pure2_def, AllCaseEqs()] >>
  rpt strip_tac >>
  gvs[lookup_var_def, update_var_def, FLOOKUP_UPDATE] >> metis_tac[]
QED
