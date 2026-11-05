Theory concretizePtrComparisonStep
Ancestors concretizePtrComparisonTransport concretizePtrValueTransport pair concretizePtrStageZero
  concretizePtrAffineTransport concretizePtrSourceOwnership
  concretizePtrStagePlacements concretizePtrAllocationOwnership
  concretizePtrActivationChronology concretizePtrActivationBirths
  concretizePtrChronologicalHistory concretizePtrPrefixLedger concretizePtrOwnerPath
  o1PassContract unitTransformDefs mem2varBlockSimHelpers ptrDiscipline venomExecSemantics venomState venomInst
  words arithmetic list rich_list finite_map pred_set

Theorem ptr_owner_view_state[local]:
  d <= LENGTH a.po_stack ==>
  (ptr_owner_view d a).cf_state =
    EL (LENGTH a.po_stack - d)
      (a.po_state :: MAP (\f. f.cf_state) a.po_stack)
Proof
  strip_tac >> Cases_on `d = LENGTH a.po_stack`
  >- simp[ptr_owner_view_def] >>
  Cases_on `LENGTH a.po_stack - d` >- gvs[] >>
  simp[ptr_owner_view_def, EL_MAP] >> AP_TERM_TAC >> decide_tac
QED

Theorem ptr_comparison_common_position[local]:
  ctx_pass_stage rpolicy (CFP_Simple VP_ConcretizeMemLoc)
    (o1_walk_view rpolicy 2) C C' /\
  EVERY (\f. f.fn_eom = NONE) C.ctx_functions /\ o1_ctx_shape C /\
  ctx_inst_ids_distinct C /\ callee_first names C.ctx_functions /\
  o1_run_state_ok vs /\ ~ctx_has_dalloca C /\ ptr_discipline lo C vs /\
  ptr_source_ownership vs C h a tokens registry births PT TG saved /\
  ptr_stage_placements C' positions /\
  FLOOKUP TG u = SOME (tu,iu) /\ FLOOKUP TG v = SOME (tv,iv) /\
  FLOOKUP a.po_prov u = SOME (b,sz) /\
  FLOOKUP a.po_prov v = SOME (b,sz) ==>
  ?p. FLOOKUP positions (Allocation iu) = SOME (p,sz) /\
      FLOOKUP positions (Allocation iv) = SOME (p,sz)
Proof
  strip_tac >> Cases_on `sz = 0`
  >- (gvs[] >> metis_tac[ptr_stage_live_zero_position]) >>
  `EVERY (\fn. EVERY (\i. i.inst_opcode <> DALLOCA) (fn_insts fn)) C.ctx_functions` by
    (gvs[ctx_has_dalloca_def, EVERY_MEM, EXISTS_MEM] >> metis_tac[]) >>
  `ptr_ledger_source_activations vs C h a tokens registry` by
    metis_tac[ptr_source_ownership_caches, ptr_source_birth_caches_activations] >>
  `frame_reachable vs C a.po_stack a.po_params a.po_prov a.po_taint
    a.po_fn a.po_inst a.po_state` by
    metis_tac[ptr_source_activations_sound, ptr_chrono_history_reachable,
      ptr_observation_reachable_def] >>
  `ptr_active_alloc_geometry (a.po_state :: MAP (\f. f.cf_state) a.po_stack)` by
    (drule ptr_frame_alloc_geometry >> fs[o1_run_state_ok_def, o1_initial_state_ok_def]) >>
  `?d p. d <= LENGTH a.po_stack /\
     FLOOKUP (ptr_owner_view d a).cf_state.vs_allocas iu = SOME (b,sz) /\
     FLOOKUP positions (Allocation iu) = SOME (p,sz)` by
    (qpat_x_assum `FLOOKUP TG v = _` kall_tac >>
     drule_all ptr_stage_placements_live_owner >> metis_tac[]) >>
  drule_all ptr_stage_placements_live_owner >> strip_tac >>
  `iu = iv` by
    (imp_res_tac ptr_owner_view_state >>
     `LENGTH a.po_stack - d < LENGTH (a.po_state :: MAP (\f. f.cf_state) a.po_stack)` by simp[] >>
     `LENGTH a.po_stack - d' < LENGTH (a.po_state :: MAP (\f. f.cf_state) a.po_stack)` by simp[] >>
     `b <= b /\ b < b + sz` by decide_tac >>
     metis_tac[ptr_active_alloc_unique_owner]) >>
  metis_tac[]
QED

Theorem ptr_comparison_values[local]:
  ctx_pass_stage rpolicy (CFP_Simple VP_ConcretizeMemLoc)
    (o1_walk_view rpolicy 2) C C' /\
  EVERY (\f. f.fn_eom = NONE) C.ctx_functions /\ o1_ctx_shape C /\
  ctx_inst_ids_distinct C /\ callee_first names C.ctx_functions /\
  o1_run_state_ok vs /\ ~ctx_has_dalloca C /\ ptr_discipline lo C vs /\
  ptr_source_ownership vs C h a tokens registry births PT TG saved /\
  ptr_stage_placements C' positions /\
  ptr_vars_transport births positions TG a.po_taint a.po_state t /\
  access_ok lo a.po_prov a.po_fn a.po_inst a.po_state /\
  a.po_inst.inst_operands = [Var u;Var v] /\
  (a.po_inst.inst_opcode = EQ \/ a.po_inst.inst_opcode = LT \/ a.po_inst.inst_opcode = GT) /\
  op_taint a.po_taint (Var u) = {} /\ op_taint a.po_taint (Var v) = {} /\
  (!aid p sz. FLOOKUP positions (Allocation aid) = SOME (p,sz) ==> p + sz < dimword(:256)) /\
  eval_operand (Var u) a.po_state = SOME x /\ eval_operand (Var v) a.po_state = SOME y /\
  eval_operand (Var u) t = SOME x' /\ eval_operand (Var v) t = SOME y' ==>
  (x' = y' <=> x = y) /\
  (w2n x' < w2n y' <=> w2n x < w2n y) /\
  (w2n x' > w2n y' <=> w2n x > w2n y)
Proof
  rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
  `ptr_value_transport births positions (FLOOKUP TG u) {} x x' /\
   ptr_value_transport births positions (FLOOKUP TG v) {} y y'` by
    (gnvs[ptr_vars_transport_def, eval_operand_def] >>
     conj_tac
     >- (qpat_x_assum `!v. ptr_lookup_transport _ _ _ _ _ _`
           (qspec_then `u` mp_tac) >> simp[ptr_lookup_transport_some]) >>
     qpat_x_assum `!v. ptr_lookup_transport _ _ _ _ _ _`
       (qspec_then `v` mp_tac) >> simp[ptr_lookup_transport_some]) >>
  `EVERY (\fn. EVERY (\i. i.inst_opcode <> DALLOCA) (fn_insts fn)) C.ctx_functions` by
    (gvs[ctx_has_dalloca_def, EVERY_MEM, EXISTS_MEM] >> metis_tac[]) >>
  drule_all ptr_source_ownership_prov_erases >> strip_tac >>
  Cases_on `u IN FDOM a.po_prov \/ v IN FDOM a.po_prov`
  >- (qsuff_tac `?b sz. FLOOKUP a.po_prov u = SOME (b,sz) /\
          FLOOKUP a.po_prov v = SOME (b,sz) /\
          b <= w2n x /\ w2n x <= b + sz /\ b <= w2n y /\ w2n y <= b + sz`
      >- (strip_tac >>
          `?tu iu tv iv. FLOOKUP TG u = SOME (tu,iu) /\ FLOOKUP TG v = SOME (tv,iv)` by
            (fs[ptr_ledger_erases_def, AllCaseEqs()] >> metis_tac[pair_CASES]) >>
          `?p. FLOOKUP positions (Allocation iu) = SOME (p,sz) /\
               FLOOKUP positions (Allocation iv) = SOME (p,sz)` by
            (irule ptr_comparison_common_position >>
             rpt (goal_assum (drule_at Any)) >> simp[]) >>
          gvs[ptr_value_transport_def, ptr_ledger_erases_def] >>
          metis_tac[ptr_comparison_eq_transport, ptr_comparison_lt_transport,
                    ptr_comparison_gt_transport]) >>
      fs[access_ok_def] >> first_x_assum (qspecl_then [`u`,`v`] mp_tac) >> simp[]) >>
  `FLOOKUP TG u = NONE /\ FLOOKUP TG v = NONE` by
    (fs[ptr_ledger_erases_def, FLOOKUP_DEF, AllCaseEqs()] >> metis_tac[]) >>
  gvs[ptr_value_transport_scalar_empty]
QED

Theorem ptr_comparison_step[local]:
  (inst.inst_opcode = EQ \/ inst.inst_opcode = LT \/ inst.inst_opcode = GT) ==>
  step_inst fuel C inst s =
    exec_pure2 (\x y. bool_to_word
      (if inst.inst_opcode = EQ then x = y
       else if inst.inst_opcode = LT then w2n x < w2n y
       else w2n x > w2n y)) inst s
Proof
  strip_tac >> simp[Once step_inst_def] >> simp[step_inst_base_def]
QED

Theorem ptr_comparison_transport:
  ctx_pass_stage rpolicy (CFP_Simple VP_ConcretizeMemLoc)
    (o1_walk_view rpolicy 2) C C' /\
  EVERY (\f. f.fn_eom = NONE) C.ctx_functions /\ o1_ctx_shape C /\
  ctx_inst_ids_distinct C /\ callee_first names C.ctx_functions /\
  o1_run_state_ok vs /\ ~ctx_has_dalloca C /\ ptr_discipline lo C vs /\
  ptr_source_ownership vs C h a tokens registry births PT TG saved /\
  ptr_stage_placements C' positions /\
  ptr_vars_transport births positions TG a.po_taint a.po_state t /\
  access_ok lo a.po_prov a.po_fn a.po_inst a.po_state /\
  a.po_inst.inst_operands = [Var u;Var v] /\ a.po_inst.inst_outputs = [out] /\
  (a.po_inst.inst_opcode = EQ \/ a.po_inst.inst_opcode = LT \/ a.po_inst.inst_opcode = GT) /\
  op_taint a.po_taint (Var u) = {} /\ op_taint a.po_taint (Var v) = {} /\
  (!aid p sz. FLOOKUP positions (Allocation aid) = SOME (p,sz) ==> p + sz < dimword(:256)) /\
  ((?s'. step_inst fuel C a.po_inst a.po_state = OK s') \/
   (?t'. step_inst fuel C' a.po_inst t = OK t')) ==>
  ?s' t'. step_inst fuel C a.po_inst a.po_state = OK s' /\
    step_inst fuel C' a.po_inst t = OK t' /\
    ptr_vars_transport births positions (step_prov PT TG a.po_inst s')
      (step_taint a.po_inst a.po_state s' a.po_taint) s' t' /\
    lookup_var out s' = lookup_var out t'
Proof
  rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
  `ptr_lookup_transport births positions (FLOOKUP TG u) {}
     (eval_operand (Var u) a.po_state) (eval_operand (Var u) t) /\
   ptr_lookup_transport births positions (FLOOKUP TG v) {}
     (eval_operand (Var v) a.po_state) (eval_operand (Var v) t)` by
    (gnvs[ptr_vars_transport_def, eval_operand_def] >> conj_tac
     >- (qpat_x_assum `!v. ptr_lookup_transport _ _ _ _ _ _`
          (qspec_then `u` mp_tac) >> simp[]) >>
     qpat_x_assum `!v. ptr_lookup_transport _ _ _ _ _ _`
       (qspec_then `v` mp_tac) >> simp[]) >>
  gs[ptr_comparison_step, exec_pure2_def, AllCaseEqs()] >>
  gs[ptr_lookup_transport_some, ptr_lookup_transport_some_right] >>

  rename1 `eval_operand (Var u) a.po_state = SOME sx` >>
  rename1 `eval_operand (Var v) a.po_state = SOME sy` >>
  rename1 `eval_operand (Var u) t = SOME tx` >>
  rename1 `eval_operand (Var v) t = SOME ty` >>
  `(tx = ty <=> sx = sy) /\
   (w2n tx < w2n ty <=> w2n sx < w2n sy) /\
   (w2n tx > w2n ty <=> w2n sx > w2n sy)` by
    (irule ptr_comparison_values >> rpt (goal_assum (drule_at Any)) >> simp[]) >>
  rpt (qpat_x_assum `update_var _ _ _ = _` (SUBST_ALL_TAC o SYM)) >>
  rpt (goal_assum (drule_at Any)) >>
  simp[step_prov_def, out_prov_def, lookup_var_update] >>
  irule ptr_vars_transport_update >>
  rpt (goal_assum (drule_at Any)) >> qexists_tac `{}` >>
  simp[ptr_value_transport_scalar_empty, step_taint_def, out_taint_def]
QED

(* Integration boundary:
   Stage assumptions supply coherent placements and, through source ownership,
   active allocation geometry. Positive-size comparisons share an allocation
   id; zero-size comparisons use stage-derived position zero, not owner equality.
   The paired-prefix construction must supply ownership and variable transport,
   plus the empty operand masks; source reachability and ptr_discipline supply
   access_ok. Successful execution on either side supplies defined operands.
   Literal/label comparisons and the syntactic classification remain outside
   this all-Var boundary.

   The strict placement-end premise is local, not a new frozen-task premise.
   complete_alloc_positions_with_imports_success proves this bound for each
   completed local allocation. Integrating it with ptr_stage_placements for
   arbitrary local/imported output metadata remains to be checked; this file
   does not infer the universal positions bound from a stage alone. *)
