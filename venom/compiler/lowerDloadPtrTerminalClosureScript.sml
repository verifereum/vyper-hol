Theory lowerDloadPtrTerminalClosure
Ancestors
  lowerDloadPtrTerminal contextCodegenRel list lowerDloadPtrRawReachable venomInst
  ctxLookupAgree lowerDloadPtrAggregate lowerDloadPtrRel lowerDloadPtrCall ptrDiscipline venomState venomExecSemantics

(* In a program with DALLOCA, every target ALLOCA site of a boundary state
   lies below the initial free memory pointer: the target sites lie below
   the target frontier, which the memory match keeps below the floor, the
   source's initial free memory pointer. *)
Theorem dload_boundary_allocas_below_fmp:
  dload_boundary_core (dyn_floor C vs) lo fs V Ws PG PH G H tn un s t cs ds /\
  frame_reachable vs C cs PG G tn f i s /\ ptr_discipline lo C vs /\
  o1_ctx_shape C /\ ctx_has_dalloca C ==>
  allocas_below_fmp t
Proof
  strip_tac >>
  `allocas_below_fmp s` by
    (qpat_x_assum `ptr_discipline lo C vs` mp_tac >>
     simp[ptr_discipline_def] >> strip_tac >>
     first_x_assum (drule_at (Pat `frame_reachable`)) >> simp[]) >>
  `s.vs_initial_fmp = vs.vs_initial_fmp` by
    (`raw_reachable vs C f i s` by
       (irule lowerDloadPtrRawReachableTheory.frame_reachable_raw >>
        metis_tac[]) >>
     drule raw_reachable_initial_fmp >> simp[]) >>
  `t.vs_initial_fmp = s.vs_initial_fmp /\ t.vs_fmp = s.vs_fmp` by
    (drule dload_boundary_environment >>
     simp[dload_equal_environment_def, venom_state_component_equality]) >>
  `t.vs_alloca_next <= w2n t.vs_initial_fmp` by
    (`t.vs_alloca_next <= dyn_floor C vs` by
       (drule dload_boundary_memory >> simp[dload_memory_match_def]) >>
     gvs[dyn_floor_def]) >>
  `dload_live_layout lo s.vs_alloca_next t.vs_alloca_next fs` by
    (drule dload_boundary_layout >> simp[]) >>
  `dload_table_stack fs (s::MAP (\c. c.cf_state) cs)
     (t::MAP (\d. d.cf_state) ds)` by
    (drule dload_boundary_tables >> simp[]) >>
  `(EL 0 fs).dr_target = t.vs_allocas` by
    (fs[dload_table_stack_def] >>
     qpat_x_assum `!k. k < LENGTH fs ==> _` (qspec_then `0` mp_tac) >>
     simp[]) >>
  simp[allocas_below_fmp_def] >> conj_tac >- fs[allocas_below_fmp_def] >>
  rpt strip_tac >>
  qpat_x_assum `dload_live_layout _ _ _ _` mp_tac >>
  simp[dload_live_layout_def] >> strip_tac >>
  qpat_x_assum `!k id b n. k < LENGTH fs /\
      FLOOKUP (EL k fs).dr_target id = SOME (b,n) ==> _`
    (qspecl_then [`0`,`aid`,`b`,`sz`] mp_tac) >>
  `0 < LENGTH fs` by gvs[dload_table_stack_def] >>
  simp[] >> strip_tac >> gvs[] >> decide_tac
QED

(* The terminal slice's steps (the RETURNDATACOPY that enters it and its
   ASSIGNs) leave the ALLOCA sites and both free memory pointers alone. *)
Theorem dload_terminal_step_below_fmp[local]:
  (i.inst_opcode = ASSIGN \/ i.inst_opcode = RETURNDATACOPY) /\
  step_inst fuel C i t = OK t' /\ allocas_below_fmp t ==>
  allocas_below_fmp (t' with vs_inst_idx := n)
Proof
  strip_tac >>
  gvs[step_inst_non_invoke, step_inst_base_def, AllCaseEqs(),
      allocas_below_fmp_def, update_var_def, write_memory_with_expansion_def] >>
  metis_tac[]
QED

(* Canonical memory-free terminal disjunct. The indexed witness is kept here
   once so reachable-state consumers need not repeat its existential spine. *)
Definition dload_terminal_mode_def:
  dload_terminal_mode lo P vs C ds H un g j t <=>
  ?cs PG G tn f s fs bb tb bs bt mid a b k.
    frame_reachable vs C cs PG G tn f (EL k mid) s /\ j = EL k mid /\
    MEM bb f.fn_blocks /\
    lookup_block s.vs_current_bb f.fn_blocks = SOME bb /\
    lookup_block t.vs_current_bb g.fn_blocks = SOME tb /\
    s.vs_inst_idx = a+k /\ t.vs_inst_idx = b+k /\
    TAKE (LENGTH mid) (DROP a bb.bb_instructions) = mid /\
    TAKE (LENGTH mid) (DROP b tb.bb_instructions) = mid /\
    a+LENGTH mid <= LENGTH bb.bb_instructions /\
    b+LENGTH mid <= LENGTH tb.bb_instructions /\
    mid <> [] /\ EVERY (\i. i.inst_opcode = ASSIGN) (FRONT mid) /\
    (LAST mid).inst_opcode = REVERT /\ k < LENGTH mid /\
    lower_dload_block_supply bs bb = (tb,bt) /\
    set (fn_ir_vars f) SUBSET set bs.irs_used_vars /\
    (!i v. MEM i bb.bb_instructions /\ MEM (Var v) i.inst_operands ==>
       v IN set (fn_ir_vars f)) /\
    (!h. h <= LENGTH mid ==> ?pre u.
       lower_dload_insts_supply bs (TAKE (a+h) bb.bb_instructions) = (pre,u) /\
       LENGTH pre = b+h) /\
    FDOM G SUBSET fn_pv P f /\ s.vs_labels = t.vs_labels /\
    (!v. v IN set (fn_ir_vars f) ==>
       (lookup_var v s = NONE <=> lookup_var v t = NONE)) /\
    dload_vars_match (dyn_floor C vs) fs (set (fn_ir_vars f) DIFF {v | retpc_var f v})
       G H tn un s t /\
    dload_live_layout lo s.vs_alloca_next t.vs_alloca_next fs /\
    dload_table_stack fs (s::MAP (\c. c.cf_state) cs)
                        (t::MAP (\c. c.cf_state) ds) /\
    (ctx_has_dalloca C ==> allocas_below_fmp t)
End

Theorem dload_terminal_mode_safety:
  o1_ctx_shape C /\ ptr_discipline lo C vs /\
  EVERY (fn_ptr_ok P) C.ctx_functions /\
  dload_terminal_mode lo P vs C ds H un g j t ==>
  access_ok lo H g j t /\ taint_ok g un j t
Proof
  simp[dload_terminal_mode_def] >> rpt strip_tac >>
  drule_all dload_indexed_terminal_safety >> simp[]
QED

Theorem terminal_active_unique[local]:
  ALL_DISTINCT (fn_labels g) /\ active_inst g i t /\ active_inst g j t ==>
  i = j
Proof
  metis_tac[active_inst_block_lookup, optionTheory.SOME_11]
QED

Theorem dload_actual_copy_terminal_mode:
  o1_ctx_shape C /\ ptr_discipline lo C vs /\
  EVERY (fn_ptr_ok P) C.ctx_functions /\
  frame_reachable vs C cs PG G tn f i s /\
  dload_control_match q f g s t i [i] 0 /\ ir_supply_covers_fn q f /\
  ALL_DISTINCT (MAP (\bb. bb.bb_label) f.fn_blocks) /\
  ALL_DISTINCT (MAP (\bb. bb.bb_label) g.fn_blocks) /\
  i.inst_opcode = RETURNDATACOPY /\ i.inst_operands = [dst;off;sz] /\
  FDOM G SUBSET fn_pv P f /\
  dload_boundary_core (dyn_floor C vs) lo fs
    (set (fn_ir_vars f) DIFF {v | retpc_var f v}) Ws
    PG PH G H tn un s t cs ds /\
  (!v. v IN set (fn_ir_vars f) ==>
    (lookup_var v s = NONE <=> lookup_var v t = NONE)) /\
  (in_revert_forward g t \/ about_to_revert g i t) /\
  step_inst fuel Ct i t = OK t' ==>
  !jnext. active_inst g jnext (t' with vs_inst_idx := SUC t.vs_inst_idx) ==>
  dload_terminal_mode lo P vs C ds (step_prov PH H i t')
    (step_taint i t t' un) g jnext
    (t' with vs_inst_idx := SUC t.vs_inst_idx)
Proof
  disch_then (REPEAT_TCL CONJUNCTS_THEN assume_tac) >>
  `ctx_has_dalloca C ==>
   allocas_below_fmp (t' with vs_inst_idx := SUC t.vs_inst_idx)` by
    (strip_tac >> irule dload_terminal_step_below_fmp >>
     qexistsl [`Ct`,`fuel`,`i`,`t`] >> simp[] >>
     irule dload_boundary_allocas_below_fmp >> metis_tac[]) >>
  drule_all dload_actual_copy_terminal_entry >>
  disch_then (REPEAT_TCL CHOOSE_THEN (REPEAT_TCL CONJUNCTS_THEN assume_tac)) >>
  rpt strip_tac >>
  `jnext = HD mid` by
    (irule terminal_active_unique >>
     qexistsl [`g`,`t' with vs_inst_idx := SUC t.vs_inst_idx`] >>
     simp[fn_labels_def] >> metis_tac[]) >>
  qpat_x_assum `revert_forward_pair _ _ _ \/ _` kall_tac >>
  qpat_x_assum `in_revert_forward _ _ \/ _` kall_tac >>
  gvs[] >> rewrite_tac[dload_terminal_mode_def] >>
  qrefinel [`_`,`_`,`_`,`_`,`_`,`s' with vs_inst_idx := SUC s.vs_inst_idx`,
    `_`,`_`,`_`,`_`,`_`,`mid`,`_`,`_`,`0`] >>
  simp[EL] >>
  rpt (goal_assum (drule_at Any)) >> simp[] >>
  Cases_on `mid` >> gvs[]
QED

Theorem dload_terminal_mode_no_call:
  dload_terminal_mode lo P vs C ds H un g j t ==>
  j.inst_opcode <> INVOKE
Proof
  simp[dload_terminal_mode_def] >> rpt strip_tac >>
  drule_all dload_indexed_terminal_constructor_exclusions >> metis_tac[]
QED

Theorem dload_terminal_mode_no_return:
  dload_terminal_mode lo P vs C ds H un g j t ==>
  step_inst fuel Ct j t <> IntRet ret t'
Proof
  simp[dload_terminal_mode_def] >> rpt strip_tac >>
  drule_all dload_indexed_terminal_constructor_exclusions >> metis_tac[]
QED

Theorem dload_terminal_mode_no_block:
  dload_terminal_mode lo P vs C ds H un g j t /\
  is_terminator j.inst_opcode ==>
  step_inst fuel Ct j t <> OK t'
Proof
  simp[dload_terminal_mode_def] >> rpt strip_tac >>
  drule_all dload_indexed_terminal_constructor_exclusions >> strip_tac >>
  Cases_on `k+1 < LENGTH mid` >- metis_tac[] >>
  `k+1 = LENGTH mid` by decide_tac >> metis_tac[]
QED

Theorem dload_terminal_mode_next:
  ALL_DISTINCT (fn_labels g) /\ EVERY (fn_ptr_ok P) C.ctx_functions /\
  dload_terminal_mode lo P vs C ds H un g j t /\
  step_inst fuel Ct j t = OK t' /\
  active_inst g jnext (t' with vs_inst_idx := SUC t.vs_inst_idx) ==>
  dload_terminal_mode lo P vs C ds (step_prov PH H j t')
    (step_taint j t t' un) g jnext
    (t' with vs_inst_idx := SUC t.vs_inst_idx)
Proof
  simp[dload_terminal_mode_def] >> rpt strip_tac >>
  `k+1 < LENGTH mid` by
    (Cases_on `k+1 < LENGTH mid` >- simp[] >>
     `k+1 = LENGTH mid` by decide_tac >>
     drule_all dload_indexed_terminal_constructor_exclusions >> metis_tac[]) >>
  `ctx_has_dalloca C ==>
   allocas_below_fmp (t' with vs_inst_idx := SUC t.vs_inst_idx)` by
    (strip_tac >> irule dload_terminal_step_below_fmp >>
     qexistsl [`Ct`,`fuel`,`j`,`t`] >> gvs[] >>
     `(EL k mid).inst_opcode = ASSIGN` by
       (irule (cj 1 dload_terminal_slice_opcode) >> gvs[] >> decide_tac) >>
     simp[]) >>
  gvs[] >> drule_all dload_terminal_assign_next >>
  disch_then (qspec_then `PH` mp_tac) >>
  disch_then (REPEAT_TCL CHOOSE_THEN (REPEAT_TCL CONJUNCTS_THEN assume_tac)) >>
  `jnext = EL (k+1) mid` by
    (irule terminal_active_unique >>
     qexistsl [`g`,`t' with vs_inst_idx := SUC t.vs_inst_idx`] >>
     gvs[] >> metis_tac[]) >>
  gvs[] >>
  qrefinel [`_`,`_`,`_`,`_`,`_`,`s' with vs_inst_idx := SUC s.vs_inst_idx`,
    `_`,`_`,`_`,`_`,`mid`,`a`,`b`,`k+1`] >>
  simp[] >> rpt (goal_assum (drule_at Any)) >> simp[]
QED
