Theory concretizePtrDallocaRuntimeSteps
Ancestors
  concretizePtrDallocaAffine concretizePtrObservationInterface
  concretizePtrDallocaBoundaryProbes concretizePtrBPReverse
  concretizePtrDallocaGhostInterface concretizePtrPrefixLedger o1FrameLockstep
  concretizePtrDallocaProducer concretizePtrSourceOwnership
  frameRelocationTaintOrder concretizeLayoutLocalShifts
  basePtrProofs blockPrefixEquiv venomExecSemantics
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

Theorem ptr_dalloca_runtime_next_sites:
  inst.inst_opcode <> ALLOCA /\
  fn_ptr_ok P fn /\ MEM inst (fn_insts fn) /\
  FDOM G SUBSET fn_pv P fn /\ ptr_ledger_erases dyn births TG G /\
  ((inst.inst_opcode = ADD \/ inst.inst_opcode = SUB) ==>
     ?a b. inst.inst_operands = [a;b]) /\
  (inst.inst_opcode = ASSIGN ==> ?op. inst.inst_operands = [op]) /\
  (!v site. FLOOKUP Gt v = SOME site ==>
     FLOOKUP G v = SOME site /\ FLOOKUP TG v = NONE) /\
  (!v site. FLOOKUP TG v = NONE /\ FLOOKUP G v = SOME site ==>
     FLOOKUP Gt v = SOME site) /\
  LENGTH PT = LENGTH PG /\ LENGTH PG = LENGTH PGt /\
  (!k site. k < LENGTH PG /\ EL k PGt = SOME site ==>
     EL k PG = SOME site /\ EL k PT = NONE) /\
  (!k site. k < LENGTH PG /\ EL k PT = NONE /\ EL k PG = SOME site ==>
     EL k PGt = SOME site) /\
  s.vs_fmp = t.vs_fmp /\
  (inst.inst_opcode = DALLOCA ==>
     eval_operands inst.inst_operands s = eval_operands inst.inst_operands t) /\
  step_inst fuel C inst s = OK s' /\ step_inst fuelt Ct inst t = OK t' ==>
  (!site. out_prov PGt Gt inst t' = SOME site ==>
     out_prov PG G inst s' = SOME site) /\
  (!v site. FLOOKUP (step_prov PGt Gt inst t') v = SOME site ==>
     FLOOKUP (step_prov PG G inst s') v = SOME site /\
     FLOOKUP (ptr_tagged_step token PT TG inst s') v = NONE) /\
  (!v site. FLOOKUP (ptr_tagged_step token PT TG inst s') v = NONE /\
     FLOOKUP (step_prov PG G inst s') v = SOME site ==>
     FLOOKUP (step_prov PGt Gt inst t') v = SOME site)
Proof
  strip_tac >>
  Cases_on `inst.inst_opcode = DALLOCA`
  >- (fs[] >> drule_all ptr_dalloca_runtime_dynamic_values >> strip_tac >>
      conj_tac >- metis_tac[] >>
      simp[step_prov_def, ptr_tagged_step_def] >>
      irule ptr_dalloca_runtime_set_sites >> simp[] >> metis_tac[]) >>
  `(!site. out_prov PGt Gt inst t' = SOME site ==>
       out_prov PG G inst s' = SOME site /\ out_prov PT TG inst s' = NONE) /\
   (!site. out_prov PT TG inst s' = NONE /\ out_prov PG G inst s' = SOME site ==>
       out_prov PGt Gt inst t' = SOME site)` by
    (Cases_on `inst.inst_opcode = PARAM`
     >- (irule ptr_dalloca_runtime_param_sites >> simp[]) >>
     Cases_on `inst.inst_opcode = ASSIGN`
     >- (irule ptr_dalloca_runtime_assign_sites >> metis_tac[]) >>
     Cases_on `inst.inst_opcode = ADD \/ inst.inst_opcode = SUB`
     >- (irule ptr_dalloca_runtime_affine_sites >> metis_tac[]) >>
     simp[out_prov_def]) >>
  conj_tac >- simp[] >>
  simp[step_prov_def, ptr_tagged_step_def] >>
  irule ptr_dalloca_runtime_set_sites >> simp[]
QED

Theorem ptr_dalloca_runtime_assign_values:
  inst.inst_opcode = ASSIGN /\ inst.inst_operands = [op] /\
  ptr_dalloca_ghost_vars G V s Gt Vt t /\
  step_inst fuel C inst s = OK s' /\ step_inst fuelt Ct inst t = OK t' /\
  out_prov PGt Gt inst t' = SOME site ==>
  !v. MEM v inst.inst_outputs ==> lookup_var v s' = lookup_var v t'
Proof
  rpt strip_tac >> irule ptr_dalloca_runtime_copy_values >>
  goal_assum (drule_at Any) >> goal_assum (drule_at Any) >> simp[] >>
  qpat_x_assum `out_prov _ _ _ _ = _` mp_tac >>
  Cases_on `op` >> gvs[out_prov_def, first_prov_def, op_prov_def,
    ptr_dalloca_ghost_vars_def, AllCaseEqs(), eval_operand_def] >> metis_tac[]
QED

Theorem ptr_dalloca_runtime_next_values:
  inst.inst_opcode <> ALLOCA /\
  fn_ptr_ok P fn /\ MEM inst (fn_insts fn) /\ FDOM G SUBSET fn_pv P fn /\
  ((inst.inst_opcode = ADD \/ inst.inst_opcode = SUB) ==>
     ?a b. inst.inst_operands = [a;b]) /\
  (inst.inst_opcode = ASSIGN ==> ?op. inst.inst_operands = [op]) /\
  ptr_dalloca_ghost_vars G tn.t_var s Gt tnt.t_var t /\
  ptr_ledger_erases dyn births TG G /\
  ptr_mixed_vars births positions TG tn f g s t /\ s.vs_labels = t.vs_labels /\
  ((inst.inst_opcode = ADD \/ inst.inst_opcode = SUB) ==>
     !op. MEM op inst.inst_operands ==>
       ptr_nonopaque_operand f op /\ op_taint tn op = {}) /\
  (!k site. k < LENGTH PGt /\ EL k PGt = SOME site ==>
     EL k s.vs_params = EL k t.vs_params) /\
  s.vs_fmp = t.vs_fmp /\
  (inst.inst_opcode = DALLOCA ==>
     eval_operands inst.inst_operands s = eval_operands inst.inst_operands t) /\
  step_inst fuel C inst s = OK s' /\ step_inst fuelt Ct inst t = OK t' /\
  out_prov PGt Gt inst t' = SOME site ==>
  !v. MEM v inst.inst_outputs ==> lookup_var v s' = lookup_var v t'
Proof
  rpt strip_tac >>
  Cases_on `inst.inst_opcode = DALLOCA`
  >- (fs[] >> drule_all ptr_dalloca_runtime_dynamic_values >> metis_tac[]) >>
  Cases_on `inst.inst_opcode = PARAM`
  >- (irule ptr_dalloca_runtime_param_values >> metis_tac[]) >>
  Cases_on `inst.inst_opcode = ASSIGN`
  >- (irule ptr_dalloca_runtime_assign_values >> metis_tac[]) >>
  `inst.inst_opcode = ADD \/ inst.inst_opcode = SUB` by
    (spose_not_then assume_tac >> gvs[out_prov_def]) >>
  `out_prov PGt Gt inst t = SOME site` by fs[out_prov_def] >>
  `!op. MEM op inst.inst_operands ==> eval_operand op s = eval_operand op t` by
    (fs[] >> drule ptr_dalloca_runtime_affine_values >>
     disch_then drule >> simp[] >> disch_then drule >> simp[] >>
     disch_then drule >> simp[] >> disch_then drule >> simp[] >>
     disch_then drule >> simp[] >> metis_tac[]) >>
  irule ptr_dalloca_runtime_copy_values >> metis_tac[]
QED

(* These are incoming selector and demanded read-mask conditions.  They do
   not assume anything about the successor variable-taint maps. *)
Theorem ptr_dalloca_runtime_output_mask:
  (!op. MEM op inst.inst_operands ==> op_taint tnt op SUBSET op_taint tn op) /\
  (!a wt. inst.inst_operands = [a] /\ eval_operand a t = SOME wt ==>
     ?w. eval_operand a s = SOME w /\
       ((inst.inst_opcode = MLOAD \/ inst.inst_opcode = ILOAD) ==>
         mem_word_taint tnt.t_mem (w2n wt) SUBSET mem_word_taint tn.t_mem (w2n w)) /\
       (inst.inst_opcode = SLOAD ==>
         key_taint tnt.t_stor wt SUBSET key_taint tn.t_stor w) /\
       (inst.inst_opcode = TLOAD ==>
         key_taint tnt.t_trans wt SUBSET key_taint tn.t_trans w)) /\
  (!a b. inst.inst_operands = [a;b] ==>
     (inst.inst_opcode = MUL ==>
       (eval_operand a s = SOME 1w <=> eval_operand a t = SOME 1w) /\
       (eval_operand b s = SOME 1w <=> eval_operand b t = SOME 1w)) /\
     ((inst.inst_opcode = SHL \/ inst.inst_opcode = SHR \/ inst.inst_opcode = SAR) ==>
       eval_operand a s = eval_operand a t)) ==>
  out_taint tnt inst t SUBSET out_taint tn inst s
Proof
  strip_tac >> Cases_on `inst.inst_operands` >> gvs[out_taint_def] >>
  rename1 `a::ops` >> Cases_on `ops`
  >- (gvs[] >> Cases_on `eval_operand a t` >> simp[] >>
      rename1 `eval_operand a t = SOME wt` >>
      qpat_x_assum `!wt'. _` (qspec_then `wt` mp_tac) >>
      simp[] >> strip_tac >> simp[] >>
      rpt IF_CASES_TAC >> gvs[]) >>
  rename1 `a::b::rest` >> Cases_on `rest` >> gvs[] >>
  Cases_on `inst.inst_opcode = MUL`
  >- (fs[] >> rpt IF_CASES_TAC >> gvs[] >> fs[SUBSET_DEF] >> metis_tac[]) >>
  Cases_on `inst.inst_opcode = SHL \/ inst.inst_opcode = SHR \/ inst.inst_opcode = SAR`
  >- (fs[] >> Cases_on `eval_operand a t` >> gvs[] >>
      irule shift_taint_mono >> simp[]) >>
  Cases_on `eval_operand a t` >> simp[]
QED

Theorem ptr_dalloca_runtime_static_next:
  inst.inst_opcode = ALLOCA /\ instt.inst_opcode = ASSIGN /\
  instt.inst_operands = [Lit pos] /\ instt.inst_outputs = inst.inst_outputs /\
  ptr_dalloca_ghost_vars G tn.t_var s Gt tnt.t_var t /\
  (!v site. FLOOKUP Gt v = SOME site ==> FLOOKUP TG v = NONE) /\
  (!v site. FLOOKUP TG v = NONE /\ FLOOKUP G v = SOME site ==>
     FLOOKUP Gt v = SOME site) /\
  step_inst fuel C inst s = OK s' /\ step_inst fuelt Ct instt t = OK t' ==>
  ptr_dalloca_ghost_vars (step_prov PG G inst s') (step_taint inst s s' tn).t_var
    (s' with vs_inst_idx := SUC s.vs_inst_idx)
    (step_prov PGt Gt instt t') (step_taint instt t t' tnt).t_var
    (t' with vs_inst_idx := SUC t.vs_inst_idx) /\
  (!v site. FLOOKUP (step_prov PGt Gt instt t') v = SOME site ==>
     FLOOKUP (ptr_tagged_step token PT TG inst s') v = NONE) /\
  (!v site. FLOOKUP (ptr_tagged_step token PT TG inst s') v = NONE /\
     FLOOKUP (step_prov PG G inst s') v = SOME site ==>
     FLOOKUP (step_prov PGt Gt instt t') v = SOME site)
Proof
  strip_tac >>
  `out_prov PGt Gt instt t' = NONE /\ out_taint tnt instt t = {}` by
    simp[out_prov_def, first_prov_def, op_prov_def, out_taint_def,
         eval_operand_def, op_taint_def] >>
  conj_tac
  >- (simp[step_prov_def, step_taint_def] >>
      irule ptr_dalloca_runtime_set_vars >> simp[] >>
      goal_assum (drule_at Any) >> simp[lookup_var_def] >>
      metis_tac[step_inst_preserves_lookup, lookup_var_def]) >>
  `!v site. FLOOKUP Gt v = SOME site ==>
     FLOOKUP G v = SOME site /\ FLOOKUP TG v = NONE` by
    (fs[ptr_dalloca_ghost_vars_def] >> metis_tac[]) >>
  simp[ptr_tagged_step_def, step_prov_def, out_prov_def] >>
  Cases_on `FLOOKUP s'.vs_allocas inst.inst_id` >>
  simp[FLOOKUP_set_prov] >> rpt strip_tac >>
  Cases_on `MEM v inst.inst_outputs` >> gvs[] >>
  Cases_on `inst.inst_outputs = [v]` >> gvs[] >> metis_tac[]
QED

Theorem ptr_dalloca_runtime_next:
  ((inst.inst_opcode = ALLOCA /\ instt.inst_opcode = ASSIGN /\
      (?pos. instt.inst_operands = [Lit pos]) /\
      instt.inst_outputs = inst.inst_outputs) \/
   (inst.inst_opcode <> ALLOCA /\ instt = inst)) /\
  fn_ptr_ok P fn /\ MEM inst (fn_insts fn) /\ FDOM G SUBSET fn_pv P fn /\
  ((inst.inst_opcode = ADD \/ inst.inst_opcode = SUB) ==>
     ?a b. inst.inst_operands = [a;b]) /\
  (inst.inst_opcode = ASSIGN ==> ?op. inst.inst_operands = [op]) /\
  ptr_dalloca_ghost_vars G tn.t_var s Gt tnt.t_var t /\
  (!v site. FLOOKUP Gt v = SOME site ==> FLOOKUP TG v = NONE) /\
  (!v site. FLOOKUP TG v = NONE /\ FLOOKUP G v = SOME site ==>
     FLOOKUP Gt v = SOME site) /\
  ptr_ledger_erases dyn births TG G /\
  ptr_mixed_vars births positions TG tn f g s t /\ s.vs_labels = t.vs_labels /\
  ((inst.inst_opcode = ADD \/ inst.inst_opcode = SUB) ==>
     !op. MEM op inst.inst_operands ==>
       ptr_nonopaque_operand f op /\ op_taint tn op = {}) /\
  LENGTH PT = LENGTH PG /\ LENGTH PG = LENGTH PGt /\
  (!k site. k < LENGTH PG /\ EL k PGt = SOME site ==>
     EL k PG = SOME site /\ EL k PT = NONE) /\
  (!k site. k < LENGTH PG /\ EL k PT = NONE /\ EL k PG = SOME site ==>
     EL k PGt = SOME site) /\
  (!k site. k < LENGTH PGt /\ EL k PGt = SOME site ==>
     EL k s.vs_params = EL k t.vs_params) /\
  s.vs_fmp = t.vs_fmp /\
  (inst.inst_opcode = DALLOCA ==>
     eval_operands inst.inst_operands s = eval_operands inst.inst_operands t) /\
  (!a wt. inst.inst_operands = [a] /\ eval_operand a t = SOME wt ==>
     ?w. eval_operand a s = SOME w /\
       ((inst.inst_opcode = MLOAD \/ inst.inst_opcode = ILOAD) ==>
         mem_word_taint tnt.t_mem (w2n wt) SUBSET mem_word_taint tn.t_mem (w2n w)) /\
       (inst.inst_opcode = SLOAD ==>
         key_taint tnt.t_stor wt SUBSET key_taint tn.t_stor w) /\
       (inst.inst_opcode = TLOAD ==>
         key_taint tnt.t_trans wt SUBSET key_taint tn.t_trans w)) /\
  (!a b. inst.inst_operands = [a;b] ==>
     (inst.inst_opcode = MUL ==>
       (eval_operand a s = SOME 1w <=> eval_operand a t = SOME 1w) /\
       (eval_operand b s = SOME 1w <=> eval_operand b t = SOME 1w)) /\
     ((inst.inst_opcode = SHL \/ inst.inst_opcode = SHR \/ inst.inst_opcode = SAR) ==>
       eval_operand a s = eval_operand a t)) /\
  step_inst fuel C inst s = OK s' /\ step_inst fuelt Ct instt t = OK t' ==>
  ptr_dalloca_ghost_vars (step_prov PG G inst s') (step_taint inst s s' tn).t_var
    (s' with vs_inst_idx := SUC s.vs_inst_idx)
    (step_prov PGt Gt instt t') (step_taint instt t t' tnt).t_var
    (t' with vs_inst_idx := SUC t.vs_inst_idx) /\
  (!v site. FLOOKUP (step_prov PGt Gt instt t') v = SOME site ==>
     FLOOKUP (ptr_tagged_step token PT TG inst s') v = NONE) /\
  (!v site. FLOOKUP (ptr_tagged_step token PT TG inst s') v = NONE /\
     FLOOKUP (step_prov PG G inst s') v = SOME site ==>
     FLOOKUP (step_prov PGt Gt instt t') v = SOME site)
Proof
  strip_tac
  >- (irule ptr_dalloca_runtime_static_next >> metis_tac[]) >>
  qpat_x_assum `instt = inst` SUBST_ALL_TAC >>
  `!v site. FLOOKUP Gt v = SOME site ==>
     FLOOKUP G v = SOME site /\ FLOOKUP TG v = NONE` by
    (fs[ptr_dalloca_ghost_vars_def] >> metis_tac[]) >>
  drule_all ptr_dalloca_runtime_next_sites >>
  disch_then (qspec_then `token` strip_assume_tac) >>
  reverse conj_tac >- metis_tac[] >>
  `!op. op_taint tnt op SUBSET op_taint tn op` by
    (Cases >> fs[ptr_dalloca_ghost_vars_def, op_taint_def]) >>
  `out_taint tnt inst t SUBSET out_taint tn inst s` by
    (irule ptr_dalloca_runtime_output_mask >> simp[] >> metis_tac[]) >>
  simp[step_prov_def, step_taint_def] >>
  irule ptr_dalloca_runtime_set_vars >>
  goal_assum (drule_at Any) >> simp[] >> conj_tac
  >- (rpt strip_tac >> simp[lookup_var_set_inst_idx] >>
      `MEM v inst.inst_outputs` by simp[] >>
      drule_all ptr_dalloca_runtime_next_values >> simp[]) >>
  simp[lookup_var_set_inst_idx] >> rpt strip_tac >>
  metis_tac[step_inst_preserves_lookup]
QED
