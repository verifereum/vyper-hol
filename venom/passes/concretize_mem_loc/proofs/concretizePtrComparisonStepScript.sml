Theory concretizePtrComparisonStep
Ancestors concretizePtrComparisonTransport concretizePtrValueTransport pair concretizePtrStageZero
  concretizePtrOpaqueRetpc concretizePtrReturnTransport concretizePtrPlacementBounds
  pointerConfinedDefs memLocDefs
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

Theorem ptr_comparison_lookup_values[local]:
  ctx_pass_stage rpolicy (CFP_Simple VP_ConcretizeMemLoc)
    (o1_walk_view rpolicy 2) C C' /\
  EVERY (\f. f.fn_eom = NONE) C.ctx_functions /\ o1_ctx_shape C /\
  ctx_inst_ids_distinct C /\ callee_first names C.ctx_functions /\
  o1_run_state_ok vs /\ ~ctx_has_dalloca C /\ ptr_discipline lo C vs /\
  ptr_source_ownership vs C h a tokens registry births PT TG saved /\
  ptr_stage_placements C' positions /\
  ptr_value_transport births positions (FLOOKUP TG u) {} x x' /\
  ptr_value_transport births positions (FLOOKUP TG v) {} y y' /\
  access_ok lo a.po_prov a.po_fn a.po_inst a.po_state /\
  a.po_inst.inst_operands = [Var u;Var v] /\
  (a.po_inst.inst_opcode = EQ \/ a.po_inst.inst_opcode = LT \/ a.po_inst.inst_opcode = GT) /\
  (!aid p sz. FLOOKUP positions (Allocation aid) = SOME (p,sz) ==> p + sz < dimword(:256)) /\
  eval_operand (Var u) a.po_state = SOME x /\ eval_operand (Var v) a.po_state = SOME y ==>
  (x' = y' <=> x = y) /\
  (w2n x' < w2n y' <=> w2n x < w2n y) /\
  (w2n x' > w2n y' <=> w2n x > w2n y)
Proof
  rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
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
      fs[access_ok_def] >> metis_tac[]) >>
  `FLOOKUP TG u = NONE /\ FLOOKUP TG v = NONE` by
    (fs[ptr_ledger_erases_def, FLOOKUP_DEF, AllCaseEqs()] >> metis_tac[]) >>
  gvs[ptr_value_transport_scalar_empty]
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
  irule ptr_comparison_lookup_values >>
  rpt (goal_assum (drule_at Any)) >> simp[]
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

Theorem ptr_comparison_nonvar_scalar[local]:
  fn_ptr_ok P f /\ MEM inst (fn_insts f) /\
  (!v tag. FLOOKUP TG v = SOME tag ==> v IN fn_pv P f) /\
  MEM inst.inst_opcode [EQ; LT; GT] /\
  ~(?u v. inst.inst_operands = [Var u; Var v]) ==>
  EVERY (\op. op_prov TG op = NONE) inst.inst_operands
Proof
  strip_tac >>
  `!v. MEM (Var v) inst.inst_operands ==> v NOTIN fn_pv P f` by
    (qpat_x_assum `fn_ptr_ok P f` mp_tac >>
     simp[fn_ptr_ok_def] >> strip_tac >>
     qpat_x_assum `!inst. MEM inst (fn_insts f) ==> _`
       (qspec_then `inst` mp_tac) >> fs[MEM] >>
     simp[ptr_use_ok_def, is_pointer_preserving_op_def,
          mem_write_ops_def, mem_read_ops_def] >> metis_tac[]) >>
  simp[EVERY_MEM] >> rpt strip_tac >> Cases_on `op` >> simp[op_prov_def] >>
  Cases_on `FLOOKUP TG s` >> simp[] >> metis_tac[]
QED

Theorem ptr_mixed_comparison_values[local]:
  ctx_pass_stage rpolicy (CFP_Simple VP_ConcretizeMemLoc)
    (o1_walk_view rpolicy 2) C C' /\
  EVERY (\f. f.fn_eom = NONE) C.ctx_functions /\ o1_ctx_shape C /\
  ctx_inst_ids_distinct C /\ callee_first names C.ctx_functions /\
  o1_run_state_ok vs /\ ~ctx_has_dalloca C /\ ptr_discipline lo C vs /\
  ptr_source_ownership vs C h a tokens registry births PT TG saved /\
  ptr_stage_placements C' positions /\
  ptr_mixed_vars births positions TG a.po_taint a.po_fn g a.po_state t /\
  a.po_state.vs_labels = t.vs_labels /\
  fn_ptr_ok P a.po_fn /\ MEM a.po_inst (fn_insts a.po_fn) /\
  (!v tag. FLOOKUP TG v = SOME tag ==> v IN fn_pv P a.po_fn) /\
  EVERY (\op. ptr_nonopaque_operand a.po_fn op /\ op_taint a.po_taint op = {})
    a.po_inst.inst_operands /\
  access_ok lo a.po_prov a.po_fn a.po_inst a.po_state /\
  a.po_inst.inst_operands = [op1;op2] /\
  MEM a.po_inst.inst_opcode [EQ; LT; GT] /\
  eval_operand op1 a.po_state = SOME x /\ eval_operand op2 a.po_state = SOME y /\
  eval_operand op1 t = SOME x' /\ eval_operand op2 t = SOME y' ==>
  (x' = y' <=> x = y) /\
  (w2n x' < w2n y' <=> w2n x < w2n y) /\
  (w2n x' > w2n y' <=> w2n x > w2n y)
Proof
  strip_tac >>
  Cases_on `?u v. a.po_inst.inst_operands = [Var u; Var v]`
  >- (gvs[] >>
      `ptr_value_transport births positions (FLOOKUP TG u) {} x x' /\
       ptr_value_transport births positions (FLOOKUP TG v) {} y y'` by
        (fs[EVERY_DEF, ptr_nonopaque_operand_def, ptr_mixed_vars_def,
            eval_operand_def] >>
         conj_tac
         >- (qpat_x_assum `!x. _ ==> ptr_lookup_transport _ _ _ _ _ _`
               (qspec_then `u` mp_tac) >> simp[ptr_lookup_transport_some]) >>
         qpat_x_assum `!x. _ ==> ptr_lookup_transport _ _ _ _ _ _`
           (qspec_then `v` mp_tac) >> simp[ptr_lookup_transport_some]) >>
      `!aid p sz. FLOOKUP positions (Allocation aid) = SOME (p,sz) ==>
         p + sz < dimword(:256)` by
        (rpt strip_tac >> drule_all ptr_stage_placements_strict_bound >> simp[]) >>
      irule ptr_comparison_lookup_values >>
      rpt (goal_assum (drule_at Any)) >> fs[MEM]) >>
  `EVERY (\op. op_prov TG op = NONE) a.po_inst.inst_operands` by
    (irule ptr_comparison_nonvar_scalar >> rpt (goal_assum (drule_at Any))) >>
  `eval_operands a.po_inst.inst_operands a.po_state =
     eval_operands a.po_inst.inst_operands t` by
    (`EVERY (\op. ptr_nonopaque_operand a.po_fn op /\ op_prov TG op = NONE /\
          op_taint a.po_taint op = {}) a.po_inst.inst_operands` by
       (fs[EVERY_MEM] >> metis_tac[]) >>
     drule_all ptr_mixed_scalar_operands_equal >> simp[]) >>
  gvs[eval_operands_def]
QED

Theorem ptr_mixed_comparison_execution:
  ctx_pass_stage rpolicy (CFP_Simple VP_ConcretizeMemLoc)
    (o1_walk_view rpolicy 2) C C' /\
  EVERY (\f. f.fn_eom = NONE) C.ctx_functions /\ o1_ctx_shape C /\
  ctx_inst_ids_distinct C /\ callee_first names C.ctx_functions /\
  o1_run_state_ok vs /\ ~ctx_has_dalloca C /\ ptr_discipline lo C vs /\
  ptr_source_ownership vs C h a tokens registry births PT TG saved /\
  ptr_stage_placements C' positions /\
  ptr_mixed_vars births positions TG a.po_taint a.po_fn g a.po_state t /\
  a.po_state.vs_labels = t.vs_labels /\
  fn_ptr_ok P a.po_fn /\ MEM a.po_inst (fn_insts a.po_fn) /\
  (!v tag. FLOOKUP TG v = SOME tag ==> v IN fn_pv P a.po_fn) /\
  EVERY (\op. ptr_nonopaque_operand a.po_fn op /\ op_taint a.po_taint op = {})
    a.po_inst.inst_operands /\
  access_ok lo a.po_prov a.po_fn a.po_inst a.po_state /\
  a.po_inst.inst_outputs = [out] /\ ~retpc_var a.po_fn out /\
  MEM a.po_inst.inst_opcode [EQ; LT; GT] /\
  step_inst fuel Ct a.po_inst t = OK t' ==>
  ?v. step_inst 0 C a.po_inst a.po_state = OK (update_var out v a.po_state) /\
    t' = update_var out v t /\
    ptr_mixed_vars births positions
      (step_prov PT TG a.po_inst (update_var out v a.po_state))
      (step_taint a.po_inst a.po_state (update_var out v a.po_state) a.po_taint)
      a.po_fn g (update_var out v a.po_state) t'
Proof
  strip_tac >>
  `a.po_inst.inst_opcode = EQ \/ a.po_inst.inst_opcode = LT \/ a.po_inst.inst_opcode = GT` by
    fs[MEM] >>
  qpat_x_assum `step_inst _ _ _ _ = OK _` mp_tac >>
  simp[ptr_comparison_step, exec_pure2_def, AllCaseEqs()] >> strip_tac >>
  drule_all ptr_mixed_vars_eval_presence >> strip_tac >>
  `?sx sy. eval_operand op1 a.po_state = SOME sx /\
           eval_operand op2 a.po_state = SOME sy` by
    metis_tac[optionTheory.IS_SOME_EXISTS] >>
  `(x = y <=> sx = sy) /\
   (w2n x < w2n y <=> w2n sx < w2n sy) /\
   (w2n x > w2n y <=> w2n sx > w2n sy)` by
    (irule ptr_mixed_comparison_values >>
     rpt (goal_assum (drule_at Any)) >> simp[]) >>
  gvs[] >>
  qexists_tac `bool_to_word (if a.po_inst.inst_opcode = EQ then sx = sy
    else if a.po_inst.inst_opcode = LT then w2n sx < w2n sy else w2n sx > w2n sy)` >>
  simp[] >>
  drule ptr_mixed_vars_update >> disch_then irule >> simp[] >>
  simp[step_prov_def, out_prov_def, set_prov_def,
       step_taint_def, out_taint_def, set_var_taint_def,
       FLOOKUP_UPDATE, FLOOKUP_DRESTRICT, ptr_value_transport_refl] >>
  rpt strip_tac >> fs[ptr_mixed_vars_def, op_taint_def] >>
  gvs[FLOOKUP_UPDATE]
QED
