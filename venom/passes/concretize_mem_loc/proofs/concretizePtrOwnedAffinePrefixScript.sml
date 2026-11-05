Theory concretizePtrOwnedAffinePrefix
Ancestors concretizePtrOwnedAssignPrefix concretizePtrTaggedSupport
  concretizePtrSourceOwnership concretizePtrDeletedGapHistory
  concretizePtrChronologicalHistory concretizePtrParamSupport
  ptrDiscipline pointerConfinedDefs o1PassLift contextCodegenRel
  concretizePtrAffineTransport concretizePtrValueTransport concretizePtrLedgerProbe
  concretizePtrActivationChronology concretizePtrActivationBirths
  venomExecSemantics venomState venomInst finite_map list pred_set

Theorem ptr_tagged_affine_conditions[local]:
  affine_pointer_ops fn (ptr_roots P fn) /\
  MEM bb fn.fn_blocks /\ MEM inst bb.bb_instructions /\
  inst.inst_operands = [x;y] /\
  (inst.inst_opcode = ADD \/ inst.inst_opcode = SUB) /\
  (!v tag. FLOOKUP TG v = SOME tag ==> v IN fn_pv P fn) ==>
  (inst.inst_opcode = ADD ==> op_prov TG x = NONE \/ op_prov TG y = NONE) /\
  (inst.inst_opcode = SUB ==> op_prov TG y = NONE)
Proof
  strip_tac >>
  `~(?v1 v2. x = Var v1 /\ y = Var v2 /\
      v1 IN fn_pv P fn /\ v2 IN fn_pv P fn) /\
    (inst.inst_opcode = SUB ==> !v. y = Var v ==> v NOTIN fn_pv P fn)` by
    (gvs[affine_pointer_ops_def, fn_pv_def] >> metis_tac[]) >>
  Cases_on `x` >> Cases_on `y` >> simp[op_prov_def] >>
  Cases_on `FLOOKUP TG s` >> gvs[] >>
  Cases_on `FLOOKUP TG s'` >> gvs[] >> metis_tac[]
QED

Theorem ptr_owned_affine_conditions:
  ptr_source_ownership vs0 C h a tokens registry births PT TG saved /\
  EVERY (fn_ptr_ok P) C.ctx_functions /\
  EVERY (\fn. EVERY inst_wf (fn_insts fn)) C.ctx_functions /\
  ~ctx_has_dalloca C /\
  (!stk PG G tn fn inst s. frame_reachable vs0 C stk PG G tn fn inst s ==>
    taint_ok fn tn inst s) /\
  a.po_inst.inst_operands = [x;y] /\
  (a.po_inst.inst_opcode = ADD \/ a.po_inst.inst_opcode = SUB) ==>
  op_taint a.po_taint x = {} /\ op_taint a.po_taint y = {} /\
  (a.po_inst.inst_opcode = ADD ==> op_prov TG x = NONE \/ op_prov TG y = NONE) /\
  (a.po_inst.inst_opcode = SUB ==> op_prov TG y = NONE)
Proof
  strip_tac >>
  `frame_reachable vs0 C a.po_stack a.po_params a.po_prov a.po_taint
    a.po_fn a.po_inst a.po_state` by
    (drule ptr_gap_ownership_history >> strip_tac >>
     drule ptr_chrono_history_reachable >> simp[ptr_observation_reachable_def]) >>
  `taint_ok a.po_fn a.po_taint a.po_inst a.po_state` by metis_tac[] >>
  `op_taint a.po_taint x = {} /\ op_taint a.po_taint y = {}` by
    (gvs[taint_ok_def] >> metis_tac[]) >>

  `EVERY (\fn. EVERY (\i. i.inst_opcode <> DALLOCA) (fn_insts fn)) C.ctx_functions`
    by (qpat_x_assum `~ctx_has_dalloca C` mp_tac >>
        simp[ctx_has_dalloca_def, EXISTS_MEM, EVERY_MEM] >> metis_tac[]) >>
  `!v tag. FLOOKUP TG v = SOME tag ==> v IN fn_pv P a.po_fn` by
    (rpt strip_tac >> irule ptr_source_tagged_var_support >>
     rpt (goal_assum (drule_at Any))) >>
  drule_all ptr_frame_current_static >> strip_tac >>
  `fn_ptr_ok P a.po_fn` by gvs[EVERY_MEM] >>
  `!vs0 ctx stk PG G tn fn inst s.
    frame_reachable vs0 ctx stk PG G tn fn inst s ==> active_inst fn inst s` by
    (ho_match_mp_tac frame_reachable_ind >> simp[]) >>
  `active_inst a.po_fn a.po_inst a.po_state` by metis_tac[] >>
  gvs[active_inst_def] >>
  `MEM a.po_inst bb.bb_instructions` by metis_tac[EL_MEM] >>
  `affine_pointer_ops a.po_fn (ptr_roots P a.po_fn)` by gvs[fn_ptr_ok_def] >>
  metis_tac[ptr_tagged_affine_conditions]
QED

(* ptr_assign_target_segment is opcode-independent and is reused below. *)
Theorem ptr_affine_prefix_fields:
  (inst.inst_opcode = ASSIGN \/ inst.inst_opcode = ADD \/ inst.inst_opcode = SUB) /\
  step_inst fuel C inst s = OK post ==>
  post.vs_allocas = s.vs_allocas /\ post.vs_labels = s.vs_labels /\
  post.vs_current_bb = s.vs_current_bb /\ post.vs_inst_idx = s.vs_inst_idx
Proof
  strip_tac >> gvs[Once run_defs, step_inst_base_def, AllCaseEqs(), update_var_def] >>
  gvs[exec_pure2_def, AllCaseEqs(), update_var_def]
QED

Theorem ptr_affine_prefix_attach:
  ptr_source_ownership vs0 C h a tokens registry births PT TG saved /\
  active_inst a.po_fn a.po_inst a.po_state /\
  (a.po_inst.inst_opcode = ASSIGN \/ a.po_inst.inst_opcode = ADD \/
   a.po_inst.inst_opcode = SUB) /\
  step_inst 0 C a.po_inst a.po_state = OK post /\
  active_inst a.po_fn inst' (post with vs_inst_idx := SUC a.po_state.vs_inst_idx) ==>
  ptr_source_ownership vs0 C (h ++ [ptr_ledger_next a inst' post])
    (ptr_ledger_next a inst' post) tokens registry births PT
    (step_prov PT TG a.po_inst post) saved
Proof
  strip_tac >>
  `ptr_tagged_chrono_step C (HD tokens) a (ptr_ledger_next a inst' post)
     PT TG saved PT (step_prov PT TG a.po_inst post) saved` by
    (simp[ptr_ledger_next_def] >>
     `~is_terminator a.po_inst.inst_opcode /\ a.po_inst.inst_opcode <> INVOKE` by
       simp[is_terminator_def] >>
     `ptr_observe a.po_stack a.po_params a.po_prov a.po_taint
       a.po_fn a.po_inst a.po_state = a` by
       simp[NoAsms, ptr_observe_def, ptr_observation_component_equality] >>
     drule_all (cj 1 ptr_tagged_chrono_step_rules) >>
     simp[ptr_tagged_step_def] >> metis_tac[]) >>
  drule_all (cj 2 ptr_source_ownership_rules) >>
  drule ptr_ownership_overlay_fixed >>
  `post.vs_allocas = a.po_state.vs_allocas` by
    metis_tac[ptr_affine_prefix_fields] >>
  simp[ptr_activation_tokens_def, ptr_activation_registry_def,
    ptr_ledger_next_def, ptr_observe_def]
QED

Theorem ptr_arithmetic_prefix_back_next[local]:
  ptr_source_ownership vs0 C h a tokens registry births PT TG saved /\
  EVERY (fn_ptr_ok P) C.ctx_functions /\
  EVERY (\fn. EVERY inst_wf (fn_insts fn)) C.ctx_functions /\
  ~ctx_has_dalloca C /\
  (!stk PG G tn fn inst s. frame_reachable vs0 C stk PG G tn fn inst s ==>
    taint_ok fn tn inst s) /\
  MEM bb a.po_fn.fn_blocks /\ bb.bb_label = a.po_state.vs_current_bb /\
  a.po_inst = EL a.po_state.vs_inst_idx bb.bb_instructions /\
  SUC a.po_state.vs_inst_idx < LENGTH bb.bb_instructions /\
  ptr_vars_transport births positions TG a.po_taint a.po_state t /\
  a.po_state.vs_labels = t.vs_labels /\
  (a.po_inst.inst_opcode = ADD \/ a.po_inst.inst_opcode = SUB) /\
  a.po_inst.inst_operands = [x;y] /\ a.po_inst.inst_outputs = [out] /\
  step_inst 0 C' a.po_inst t = OK post ==>
  ?b TG'. ptr_source_ownership vs0 C (h ++ [b]) b tokens registry births PT TG' saved /\
    b.po_fn = a.po_fn /\ b.po_stack = a.po_stack /\ b.po_params = a.po_params /\
    b.po_inst = EL b.po_state.vs_inst_idx bb.bb_instructions /\
    b.po_state.vs_inst_idx = SUC a.po_state.vs_inst_idx /\
    b.po_state.vs_current_bb = a.po_state.vs_current_bb /\
    b.po_state.vs_labels = post.vs_labels /\
    ptr_vars_transport births positions TG' b.po_taint b.po_state
      (post with vs_inst_idx := SUC t.vs_inst_idx)
Proof
  strip_tac >>
  `active_inst a.po_fn a.po_inst a.po_state` by
    (simp[active_inst_def] >> qexists_tac `bb` >> simp[] >> decide_tac) >>
  `op_taint a.po_taint x = {} /\ op_taint a.po_taint y = {} /\
   (a.po_inst.inst_opcode = ADD ==> op_prov TG x = NONE \/ op_prov TG y = NONE) /\
   (a.po_inst.inst_opcode = SUB ==> op_prov TG y = NONE)` by
    metis_tac[ptr_owned_affine_conditions] >>
  `?s' t'. step_inst 0 C a.po_inst a.po_state = OK s' /\
    step_inst 0 C' a.po_inst t = OK t' /\
    ptr_vars_transport births positions (step_prov PT TG a.po_inst s')
      (step_taint a.po_inst a.po_state s' a.po_taint) s' t'` by
    (irule ptr_affine_transport_all >> rpt (goal_assum (drule_at Any)) >> metis_tac[]) >>
  gvs[] >>
  `s'.vs_allocas = a.po_state.vs_allocas /\
   s'.vs_labels = a.po_state.vs_labels /\
   s'.vs_current_bb = a.po_state.vs_current_bb /\
   s'.vs_inst_idx = a.po_state.vs_inst_idx` by
    (irule ptr_affine_prefix_fields >> rpt (goal_assum (drule_at Any)) >> simp[]) >>
  `post.vs_labels = t.vs_labels` by
    (irule (cj 2 ptr_affine_prefix_fields) >> rpt (goal_assum (drule_at Any)) >> simp[]) >>
  `active_inst a.po_fn (EL (SUC a.po_state.vs_inst_idx) bb.bb_instructions)
    (s' with vs_inst_idx := SUC a.po_state.vs_inst_idx)` by
    (simp[active_inst_def] >> qexists_tac `bb` >> simp[]) >>
  qexistsl_tac [`ptr_ledger_next a
    (EL (SUC a.po_state.vs_inst_idx) bb.bb_instructions) s'`,
    `step_prov PT TG a.po_inst s'`] >>
  (conj_tac
   >- (irule ptr_affine_prefix_attach >> rpt (goal_assum (drule_at Any)) >> simp[])) >>
  gvs[ptr_ledger_next_def, ptr_observe_def, ptr_vars_transport_def, lookup_var_def]
QED

Theorem ptr_affine_prefix_back_next:
  ptr_source_ownership vs0 C h a tokens registry births PT TG saved /\
  EVERY (fn_ptr_ok P) C.ctx_functions /\
  EVERY (\fn. EVERY inst_wf (fn_insts fn)) C.ctx_functions /\
  ~ctx_has_dalloca C /\
  (!stk PG G tn fn inst s. frame_reachable vs0 C stk PG G tn fn inst s ==>
    taint_ok fn tn inst s) /\
  MEM bb a.po_fn.fn_blocks /\ bb.bb_label = a.po_state.vs_current_bb /\
  a.po_inst = EL a.po_state.vs_inst_idx bb.bb_instructions /\
  SUC a.po_state.vs_inst_idx < LENGTH bb.bb_instructions /\
  ptr_vars_transport births positions TG a.po_taint a.po_state t /\
  a.po_state.vs_labels = t.vs_labels /\
  ((?op out. a.po_inst.inst_opcode = ASSIGN /\ a.po_inst.inst_operands = [op] /\
     a.po_inst.inst_outputs = [out]) \/
   (?x y out. (a.po_inst.inst_opcode = ADD \/ a.po_inst.inst_opcode = SUB) /\
     a.po_inst.inst_operands = [x;y] /\ a.po_inst.inst_outputs = [out])) /\
  step_inst 0 C' a.po_inst t = OK post ==>
  ?b TG'. ptr_source_ownership vs0 C (h ++ [b]) b tokens registry births PT TG' saved /\
    b.po_fn = a.po_fn /\ b.po_stack = a.po_stack /\ b.po_params = a.po_params /\
    b.po_inst = EL b.po_state.vs_inst_idx bb.bb_instructions /\
    b.po_state.vs_inst_idx = SUC a.po_state.vs_inst_idx /\
    b.po_state.vs_current_bb = a.po_state.vs_current_bb /\
    b.po_state.vs_labels = post.vs_labels /\
    ptr_vars_transport births positions TG' b.po_taint b.po_state
      (post with vs_inst_idx := SUC t.vs_inst_idx)
Proof
  strip_tac
  >- (drule_all ptr_assign_prefix_back_next >> simp[]) >>
  irule ptr_arithmetic_prefix_back_next >>
  rpt (goal_assum (drule_at Any)) >> metis_tac[]
QED
