Theory gasFocusConcretizeCutComparison
Ancestors concretizePtrComparisonStep[qualified] marker[qualified,ignore_grammar]
  concretizePtrComparisonTransport concretizePtrValueTransport
  concretizePtrOrdinaryNext concretizePtrPairedPrefix concretizePtrPairedFields
  concretizePtrStructuralTranscript concretizePtrStructuralTrace
  concretizePtrDeletedGapHistory concretizePtrOperationalOpcodes concretizePtrLedgerProbe
  concretizePtrRequestHistory concretizePtrTaintContent concretizeStepStructure
  concretizeLayoutCutSafe[qualified] concretizePtrPlacementBounds[qualified]
  unitTransformDefs[qualified] o1ContractSimplifyCfgSrcFrame[qualified]
  o1PassContract o1ScheduleDecomp unitLabelMapIdentity contextCodegenRel
  codegenRel unitShapeDefs venomWf cfgWf frameViewFacts opcodeClass
  concretizePtrSourceOwnership concretizePtrActivationBirths
  concretizePtrActivationChronology concretizePtrPrefixLedger
  concretizePtrStagePlacements concretizePtrAllocationOwnership
  concretizePtrOwnerFloor concretizePtrOwnerPath concretizePtrChronologicalHistory
  frameAllocationOwnership ptrDiscipline
  gasFocusConcretizeEndpointCut gasFocusConcretizeTaggedSupport
  gasFocusChronologicalCut o1SafeUpto
  concretizePtrParamSupport concretizePtrOpaqueRetpc concretizePtrReturnTransport
  pointerConfinedDefs memLocDefs venomExecSemantics venomState venomInst
  arithmetic list rich_list finite_map pred_set words

Theorem ptr_comparison_birth_lookup[local]:
  ptr_ledger_erases floor births TG G /\ FLOOKUP TG v = SOME owner /\
  FLOOKUP G v = SOME site ==> FLOOKUP births owner = SOME site
Proof
  rw[ptr_ledger_erases_def] >>
  qpat_x_assum `!v. ptr_owner_erases _ _ _ _`
    (qspec_then `v` mp_tac) >> simp[ptr_owner_erases_def]
QED

Theorem ptr_comparison_owner_cache[local]:
  ptr_source_ownership vs C h a tokens registry births PT TG saved /\
  ptr_ledger_erases (dyn_floor C vs) births TG a.po_prov /\
  FLOOKUP TG v = SOME (token,aid) /\
  FLOOKUP a.po_prov v = SOME (b,sz) ==>
  ?d. d <= LENGTH a.po_stack /\
      EL (LENGTH a.po_stack - d) tokens = token /\
      FLOOKUP (ptr_owner_view d a).cf_state.vs_allocas aid = SOME (b,sz)
Proof
  strip_tac >>
  `MEM token tokens` by metis_tac[ptr_source_ownership_live_prov] >>
  `LENGTH tokens = SUC (LENGTH a.po_stack)` by
    metis_tac[ptr_source_ownership_caches, ptr_source_birth_caches_activations,
      ptr_source_activations_length] >>
  `FLOOKUP births (token,aid) = SOME (b,sz)` by
    metis_tac[ptr_comparison_birth_lookup] >>
  `ptr_birth_slices a tokens births` by
    metis_tac[ptr_source_ownership_caches, ptr_source_birth_caches_slices] >>
  gvs[MEM_EL] >> rename1 `n < SUC (LENGTH a.po_stack)` >>
  qexists_tac `LENGTH a.po_stack - n` >>
  `LENGTH a.po_stack - (LENGTH a.po_stack - n) = n` by decide_tac >>
  simp[] >> gvs[ptr_birth_slices_def] >>
  first_x_assum (qspecl_then [`LENGTH a.po_stack - n`,`aid`] mp_tac) >> simp[]
QED

Theorem ptr_comparison_owner_cut_floor[local]:
  ptr_chrono_history vs C h a /\ gas_cut n vs a.po_state /\
  ptr_discipline_upto lo n C vs /\ ctx_has_dalloca C /\
  d <= LENGTH a.po_stack /\
  FLOOKUP (ptr_owner_view d a).cf_state.vs_allocas aid = SOME (b,sz) ==>
  b + sz <= dyn_floor C vs
Proof
  strip_tac >>
  `ptr_observation_reachable vs C a` by metis_tac[ptr_chrono_history_reachable] >>
  drule_all ptr_reachable_owner_frame >> strip_tac >>
  `gas_cut n vs (ptr_owner_view d a).cf_state` by
    (Cases_on `d = LENGTH a.po_stack` >- simp[ptr_owner_view_def] >>
     drule_all ptr_chrono_saved_callers_cut >>
     simp[EVERY_MEM, ptr_owner_view_def] >> disch_then irule >>
     simp[MEM_EL] >> qexists_tac `LENGTH a.po_stack - (d + 1)` >>
     simp[]) >>
  `(ptr_owner_view d a).cf_state.vs_initial_fmp = vs.vs_initial_fmp` by
    metis_tac[ptrDisciplineEmptyTaintTheory.frame_reachable_initial_fmp] >>
  qpat_assum `frame_reachable _ _ _ _ _ _ _ _ (ptr_owner_view d a).cf_state`
    (mp_then Any mp_tac frame_reachable_caches_below_upto) >>
  disch_then (qspecl_then [`n`,`lo`] mp_tac) >>
  simp[] >>
  disch_then (qspecl_then [`0`,`aid`,`b`,`sz`] mp_tac) >> simp[dyn_floor_def]
QED

Theorem ptr_comparison_owner_id[local]:
  ptr_active_alloc_geometry (a.po_state :: MAP (\f. f.cf_state) a.po_stack) /\
  d <= LENGTH a.po_stack /\ e <= LENGTH a.po_stack /\
  FLOOKUP (ptr_owner_view d a).cf_state.vs_allocas aid = SOME (b,sz) /\
  FLOOKUP (ptr_owner_view e a).cf_state.vs_allocas aid' = SOME (b,sz) /\
  0 < sz ==> aid = aid'
Proof
  strip_tac >> imp_res_tac concretizePtrOwnerSeedsTheory.ptr_owner_view_index >>
  `LENGTH a.po_stack - d < LENGTH (a.po_state :: MAP (\f. f.cf_state) a.po_stack)` by simp[] >>
  `LENGTH a.po_stack - e < LENGTH (a.po_state :: MAP (\f. f.cf_state) a.po_stack)` by simp[] >>
  `b <= b /\ b < b + sz` by decide_tac >>
  metis_tac[ptr_active_alloc_unique_owner]
QED

Theorem ptr_comparison_untagged_floor[local]:
  ptr_ledger_erases floor births TG G /\ FLOOKUP TG w = NONE /\
  FLOOKUP G w = SOME (b,sz) ==> floor <= b
Proof
  rw[ptr_ledger_erases_def] >>
  qpat_x_assum `!v. ptr_owner_erases _ _ _ _`
    (qspec_then `w` mp_tac) >> simp[ptr_owner_erases_def] >>
  disch_then (qspec_then `(b,sz)` mp_tac) >> simp[]
QED

Theorem ptr_comparison_lookup_values_upto[local]:
  ptr_chrono_history vs C h a /\ gas_cut n vs a.po_state /\
  ptr_discipline_upto lo n C vs /\
  ptr_source_ownership vs C h a tokens registry births PT TG saved /\
  ptr_ledger_erases (dyn_floor C vs) births TG a.po_prov /\
  ptr_active_alloc_geometry (a.po_state :: MAP (\f. f.cf_state) a.po_stack) /\
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
  disch_then (map_every assume_tac o CONJUNCTS) >>
  Cases_on `u IN FDOM a.po_prov \/ v IN FDOM a.po_prov`
  >- (`?b sz. FLOOKUP a.po_prov u = SOME (b,sz) /\
          FLOOKUP a.po_prov v = SOME (b,sz) /\ 0 < sz /\
          b <= w2n x /\ w2n x <= b + sz /\ b <= w2n y /\ w2n y <= b + sz` by
        (fs[access_ok_def] >> metis_tac[]) >>
      `!w token aid. FLOOKUP TG w = SOME (token,aid) /\
          FLOOKUP a.po_prov w = SOME (b,sz) ==>
          ?d. d <= LENGTH a.po_stack /\
              FLOOKUP (ptr_owner_view d a).cf_state.vs_allocas aid = SOME (b,sz)` by
        (rpt strip_tac >> drule_all ptr_comparison_owner_cache >> metis_tac[]) >>
      `!w tag. FLOOKUP TG w = SOME tag /\ FLOOKUP a.po_prov w = SOME (b,sz) /\
         ctx_has_dalloca C ==> b + sz <= dyn_floor C vs` by
        (rpt strip_tac >> PairCases_on `tag` >> res_tac >>
         drule_all ptr_comparison_owner_cut_floor >> simp[]) >>
      `w2n x < dimword (:256)` by simp[w2n_lt] >>
      `!w. FLOOKUP TG w = NONE /\ FLOOKUP a.po_prov w = SOME (b,sz) ==>
         dyn_floor C vs <= b` by
        (rpt strip_tac >> drule_all ptr_comparison_untagged_floor >> simp[]) >>
      Cases_on `FLOOKUP TG u` >> Cases_on `FLOOKUP TG v`
      >- gvs[ptr_value_transport_scalar_empty]
      >- (`ctx_has_dalloca C ==> b + sz <= dyn_floor C vs` by metis_tac[] >>
          `dyn_floor C vs <= b` by metis_tac[] >>
          Cases_on `ctx_has_dalloca C` >> fs[dyn_floor_def])
      >- (`ctx_has_dalloca C ==> b + sz <= dyn_floor C vs` by metis_tac[] >>
          `dyn_floor C vs <= b` by metis_tac[] >>
          Cases_on `ctx_has_dalloca C` >> fs[dyn_floor_def]) >>
      rename1 `FLOOKUP TG u = SOME tu` >> rename1 `FLOOKUP TG v = SOME tv` >>
      PairCases_on `tu` >> PairCases_on `tv` >> res_tac >>
      `FLOOKUP births (tu0,tu1) = SOME (b,sz) /\
       FLOOKUP births (tv0,tv1) = SOME (b,sz)` by
        metis_tac[ptr_comparison_birth_lookup] >>
      `tu1 = tv1` by metis_tac[ptr_comparison_owner_id] >>
      `?p. FLOOKUP positions (Allocation tu1) = SOME (p,sz) /\
           x' = x - n2w b + n2w p /\ y' = y - n2w b + n2w p` by
        (gvs[ptr_value_transport_def, SF CONJ_ss]) >>
      `p + sz < dimword(:256)` by metis_tac[] >>
      conj_tac >- metis_tac[ptr_comparison_eq_transport] >>
      conj_tac >- metis_tac[ptr_comparison_lt_transport] >>
      metis_tac[ptr_comparison_gt_transport]) >>
  `!w. w NOTIN FDOM a.po_prov ==> FLOOKUP TG w = NONE` by
    (rpt strip_tac >>
     `FLOOKUP a.po_prov w = NONE` by fs[FLOOKUP_DEF] >>
     qpat_x_assum `ptr_ledger_erases _ _ _ _` mp_tac >>
     simp[ptr_ledger_erases_def] >> strip_tac >>
     Cases_on `FLOOKUP TG w` >> simp[] >>
     rename1 `FLOOKUP TG w = SOME owner` >>
     `owner IN FDOM births` by metis_tac[] >>
     qpat_x_assum `!v. ptr_owner_erases _ _ _ _` (qspec_then `w` mp_tac) >>
     simp[ptr_owner_erases_def] >> fs[FLOOKUP_DEF]) >>
  `FLOOKUP TG u = NONE /\ FLOOKUP TG v = NONE` by (fs[] >> metis_tac[]) >>
  gvs[ptr_value_transport_scalar_empty]
QED

Theorem ptr_comparison_nonvar_untagged[local]:
  fn_ptr_ok P f /\ MEM inst (fn_insts f) /\ ptr_static_support P f TG /\
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
  Cases_on `FLOOKUP TG s` >> simp[] >> fs[ptr_static_support_def] >> metis_tac[]
QED

Theorem ptr_comparison_mixed_values_upto[local]:
  ptr_chrono_history vs C h a /\ gas_cut n vs a.po_state /\
  ptr_discipline_upto lo n C vs /\
  ptr_source_ownership vs C h a tokens registry births PT TG saved /\
  ptr_ledger_erases (dyn_floor C vs) births TG a.po_prov /\
  ptr_active_alloc_geometry (a.po_state :: MAP (\f. f.cf_state) a.po_stack) /\
  ptr_mixed_vars births positions TG a.po_taint a.po_fn g a.po_state t /\
  a.po_state.vs_labels = t.vs_labels /\
  fn_ptr_ok P a.po_fn /\ MEM a.po_inst (fn_insts a.po_fn) /\
  ptr_static_support P a.po_fn TG /\
  EVERY (\op. ptr_nonopaque_operand a.po_fn op /\ op_taint a.po_taint op = {})
    a.po_inst.inst_operands /\
  access_ok lo a.po_prov a.po_fn a.po_inst a.po_state /\
  a.po_inst.inst_operands = [op1;op2] /\
  MEM a.po_inst.inst_opcode [EQ; LT; GT] /\
  (!aid p sz. FLOOKUP positions (Allocation aid) = SOME (p,sz) ==> p + sz < dimword(:256)) /\
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
      irule ptr_comparison_lookup_values_upto >>
      rpt (goal_assum (drule_at Any)) >> fs[MEM]) >>
  `EVERY (\op. op_prov TG op = NONE) a.po_inst.inst_operands` by
    (irule ptr_comparison_nonvar_untagged >> rpt (goal_assum (drule_at Any))) >>
  `eval_operands a.po_inst.inst_operands a.po_state =
     eval_operands a.po_inst.inst_operands t` by
    (`EVERY (\op. ptr_nonopaque_operand a.po_fn op /\ op_prov TG op = NONE /\
          op_taint a.po_taint op = {}) a.po_inst.inst_operands` by
       (fs[EVERY_MEM] >> metis_tac[]) >>
     drule_all ptr_mixed_scalar_operands_equal >> simp[]) >>
  gvs[eval_operands_def]
QED

Theorem ptr_comparison_execution_upto[local]:
  ptr_chrono_history vs C h a /\ gas_cut n vs a.po_state /\
  ptr_discipline_upto lo n C vs /\
  ptr_source_ownership vs C h a tokens registry births PT TG saved /\
  ptr_ledger_erases (dyn_floor C vs) births TG a.po_prov /\
  ptr_active_alloc_geometry (a.po_state :: MAP (\f. f.cf_state) a.po_stack) /\
  ptr_mixed_vars births positions TG a.po_taint a.po_fn g a.po_state t /\
  a.po_state.vs_labels = t.vs_labels /\
  fn_ptr_ok P a.po_fn /\ MEM a.po_inst (fn_insts a.po_fn) /\
  ptr_static_support P a.po_fn TG /\
  EVERY (\op. ptr_nonopaque_operand a.po_fn op /\ op_taint a.po_taint op = {})
    a.po_inst.inst_operands /\
  access_ok lo a.po_prov a.po_fn a.po_inst a.po_state /\
  (!aid p sz. FLOOKUP positions (Allocation aid) = SOME (p,sz) ==> p + sz < dimword(:256)) /\
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
  simp[concretizePtrComparisonStepTheory.ptr_comparison_step, exec_pure2_def, AllCaseEqs()] >> strip_tac >>
  drule_all ptr_mixed_vars_eval_presence >> strip_tac >>
  `?sx sy. eval_operand op1 a.po_state = SOME sx /\
           eval_operand op2 a.po_state = SOME sy` by
    metis_tac[optionTheory.IS_SOME_EXISTS] >>
  `(x = y <=> sx = sy) /\
   (w2n x < w2n y <=> w2n sx < w2n sy) /\
   (w2n x > w2n y <=> w2n sx > w2n sy)` by
    (irule ptr_comparison_mixed_values_upto >>
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

Theorem ptr_focus_comparison_step:
  ptr_paired_prefix R lp positions lo vs C C'
    h a ht at done tokens registry births PT TG saved entries H calls ws /\
  ctx_pass_stage rpolicy (CFP_Simple VP_ConcretizeMemLoc)
    (o1_walk_view rpolicy 2) C C' /\
  o1_ctx_shape C /\ EVERY (\f. f.fn_eom = NONE) C.ctx_functions /\
  EVERY ssa_form C.ctx_functions /\ callee_first names C.ctx_functions /\
  o1_initial_state_ok vs /\ ptr_discipline_upto lo n C vs /\
  gas_cut n vs at.po_state /\
  MEM a.po_inst.inst_opcode [EQ; LT; GT] /\
  at.po_inst = concretize_inst_with_positions (lp a.po_fn) a.po_inst /\
  ptr_chrono_step C' at zt ==>
  ?z TG'. TG' = step_prov PT TG a.po_inst z.po_state /\
    ptr_paired_prefix R lp positions lo vs C C'
      (h ++ [z]) z (ht ++ [zt]) zt (done ++ [LENGTH h - 1])
      tokens registry births PT TG' saved entries
      (H ++ [(tokens,registry,births,PT,TG',saved,entries)]) calls ws
Proof
  strip_tac >>
  drule_all ptr_paired_endpoint_cut_safety >> strip_tac >>
  drule ptr_paired_prefix_endpoint >> strip_tac >>
  drule ptr_paired_prefix_transcript >> strip_tac >>
  drule ptr_structural_transcript_erasure >> strip_tac >>
  drule ptr_structural_trace_ownership >> strip_tac >>
  drule ptr_gap_ownership_history >> strip_tac >>
  `MEM a.po_fn C.ctx_functions` by (drule ptr_frame_context_membership >> simp[]) >>
  `active_inst a.po_fn a.po_inst a.po_state` by
    (drule o1ContractSimplifyCfgSrcFrameTheory.scfg_frame_reachable_active >> simp[]) >>
  `MEM a.po_inst (fn_insts a.po_fn)` by
    (fs[active_inst_def, fn_insts_MEM] >> metis_tac[MEM_EL]) >>
  `EVERY (\f. EVERY inst_wf (fn_insts f)) C.ctx_functions` by
    (fs[o1_ctx_shape_def, o1_fn_shape_def, wf_function_def,
        EVERY_MEM, fn_inst_wf_def, fn_insts_MEM] >> metis_tac[]) >>
  `inst_wf a.po_inst` by
    (qpat_assum `EVERY (\f. EVERY inst_wf (fn_insts f)) C.ctx_functions`
       (mp_tac o REWRITE_RULE [EVERY_MEM]) >> metis_tac[]) >>
  `?out. a.po_inst.inst_outputs = [out]` by
    (fs[MEM] >> gvs[inst_wf_def, LENGTH_EQ_NUM_compute]) >>
  `~retpc_var a.po_fn out` by
    (irule noncopy_output_not_retpc >>
     conj_tac >- metis_tac[EVERY_MEM] >>
     qexists_tac `a.po_inst` >> fs[MEM]) >>
  `at.po_inst = a.po_inst` by (fs[MEM] >> gvs[concretize_positions_unchanged]) >>
  `~is_terminator a.po_inst.inst_opcode /\ a.po_inst.inst_opcode <> INVOKE /\
   a.po_inst.inst_opcode <> NOP /\ a.po_inst.inst_opcode <> ALLOCA` by
    (fs[MEM] >> simp[is_terminator_def]) >>
  `?P. EVERY (fn_ptr_ok P) C.ctx_functions` by
    (fs[ptr_discipline_upto_def, EVERY_MEM] >> metis_tac[]) >>
  `?P. fn_ptr_ok P a.po_fn /\ ptr_static_support P a.po_fn TG` by
    (drule_all ptr_focus_source_tagged_support >> fs[EVERY_MEM] >> metis_tac[]) >>
  suspend "execution"
QED

Resume ptr_focus_comparison_step[execution]:
  `EVERY (\obs. ctx_has_dalloca C ==> allocas_below_fmp obs.po_state) h` by
    (drule_all ptr_chrono_history_cut >> strip_tac >>
     drule ptr_chrono_history_reachable >>
     simp[EVERY_MEM, ptr_observation_reachable_def] >> strip_tac >>
     rpt strip_tac >>
     `gas_cut n vs obs.po_state` by
       (qpat_assum `EVERY (\b. gas_cut n vs b.po_state) h`
          (mp_tac o REWRITE_RULE [EVERY_MEM]) >>
        disch_then (qspec_then `obs` mp_tac) >> simp[]) >>
     `frame_reachable vs C obs.po_stack obs.po_params obs.po_prov obs.po_taint
        obs.po_fn obs.po_inst obs.po_state` by simp[] >>
     qpat_assum `frame_reachable _ _ obs.po_stack _ _ _ _ _ _`
       (mp_then Any mp_tac concretizeLayoutCutSafeTheory.ptr_discipline_upto_at) >>
     disch_then (qspecl_then [`n`,`lo`] mp_tac) >> simp[]) >>
  `ptr_ledger_erases (dyn_floor C vs) births TG a.po_prov` by
    (drule_all ptr_source_ownership_history_erases >> simp[]) >>
  `ptr_active_alloc_geometry (a.po_state :: MAP (\f. f.cf_state) a.po_stack)` by
    (`vs.vs_allocas = FEMPTY` by fs[unitTransformDefsTheory.o1_initial_state_ok_def] >>
     drule_all ptr_frame_alloc_geometry >> simp[]) >>
  `EVERY (\op. ptr_nonopaque_operand a.po_fn op /\ op_taint a.po_taint op = {})
     a.po_inst.inst_operands` by suspend "operands" >>
  `!aid p sz. FLOOKUP positions (Allocation aid) = SOME (p,sz) ==> p + sz < dimword(:256)` by
    (`ptr_stage_placements C' positions` by fs[ptr_paired_prefix_def] >>
     rpt strip_tac >> drule_all concretizePtrPlacementBoundsTheory.ptr_stage_placements_strict_bound >> simp[]) >>
  qpat_assum `ptr_chrono_step C' at zt` mp_tac >>
  once_rewrite_tac[ptr_chrono_step_cases] >>
  simp[ptr_observe_def, ptr_observation_component_equality] >>
  strip_tac >> gvs[Excl "MEM"] >>
  IF (qpat_assum `step_inst _ _ _ _ = OK _` (K all_tac)) all_tac
    (qpat_x_assum `step_inst _ _ _ _ = IntRet _ _` mp_tac >>
     simp[step_inst_non_invoke] >> strip_tac >>
     drule step_inst_base_intret_opcodes >> fs[MEM]) >>
  `?v. step_inst 0 C a.po_inst a.po_state = OK (update_var out v a.po_state) /\
     s' = update_var out v at.po_state /\
     ptr_mixed_vars births positions
       (step_prov PT TG a.po_inst (update_var out v a.po_state))
       (step_taint a.po_inst a.po_state (update_var out v a.po_state) a.po_taint)
       a.po_fn at.po_fn (update_var out v a.po_state) s'` by
    (fs[ptr_paired_sample_def] >>
     `a.po_state.vs_labels = at.po_state.vs_labels` by
       metis_tac[ptr_history_content_labels] >>
     `MEM a.po_inst.inst_opcode [EQ; LT; GT]` by simp[] >>
     drule_all ptr_comparison_execution_upto >> simp[]) >>
  suspend "attach"
QED

Resume ptr_focus_comparison_step[operands]:
  `EVERY (ptr_nonopaque_operand a.po_fn) a.po_inst.inst_operands` by
    (irule ptr_nonopaque_instruction_operands >>
     `opaque_use_ok a.po_fn` by
       (fs[o1_ctx_shape_def, o1_fn_shape_def, fn_shape_ok_def, EVERY_MEM] >> metis_tac[]) >>
     fs[MEM]) >>
  fs[MEM, taint_ok_def, EVERY_MEM] >> rpt strip_tac >>
  qpat_x_assum `!op. MEM op _ /\ _ ==> _` (qspec_then `op` mp_tac) >>
  simp[] >> metis_tac[]
QED

Resume ptr_focus_comparison_step[attach]:
  markerLib.RESUME_TAC >>
  `o1_fn_shape C a.po_fn` by
    (qpat_assum `o1_ctx_shape C` (mp_tac o REWRITE_RULE [o1_ctx_shape_def, EVERY_MEM]) >>
     simp[]) >>
  `EVERY bb_well_formed a.po_fn.fn_blocks /\ ALL_DISTINCT (fn_labels a.po_fn)` by
    (qpat_assum `o1_fn_shape C a.po_fn`
       (mp_tac o REWRITE_RULE [o1_fn_shape_def, wf_function_def, EVERY_MEM]) >>
     simp[EVERY_MEM]) >>
  `?i. active_inst a.po_fn i
     ((update_var out v a.po_state) with vs_inst_idx := SUC a.po_state.vs_inst_idx)` by
    (qpat_assum `active_inst a.po_fn a.po_inst a.po_state`
       (mp_then Any mp_tac ptr_ordinary_next_active) >>
     disch_then irule >> simp[update_var_def]) >>
  qabbrev_tac `z = ptr_ledger_next a i (update_var out v a.po_state)` >>
  `ALL_DISTINCT (fn_labels at.po_fn)` by
    (fs[ptr_paired_code_def] >> metis_tac[fn_labels_def, concretize_positions_labels]) >>
  drule ptr_paired_stage_local_allocas >>
  disch_then (qspecl_then [`o1_walk_view rpolicy 2`,`rpolicy`] mp_tac) >>
  simp[] >> strip_tac >>
  `ptr_paired_sample positions z zt
     (tokens,registry,births,PT,step_prov PT TG a.po_inst z.po_state,saved,entries)` by
    (simp[ptr_paired_sample_def, Abbr `z`, ptr_ledger_next_def, ptr_observe_def] >>
     (reverse conj_tac
      >- (fs[ptr_paired_sample_def] >>
          irule ptr_history_content_masks >> goal_assum (drule_at Any) >>
          fs[MEM] >>
          simp[step_taint_def, store_taint_def, adopt_reset_def, imm_taint_def]) >>
      gvs[step_prov_def, out_prov_def] >>
      irule ptr_mixed_vars_fields >> rpt (goal_assum (drule_at Any)) >>
      simp[update_var_def])) >>
  `ptr_paired_params positions z zt
     (tokens,registry,births,PT,step_prov PT TG a.po_inst z.po_state,saved,entries)` by
    fs[ptr_paired_params_def, Abbr `z`, ptr_ledger_next_def, ptr_observe_def, update_var_def] >>
  qexists_tac `z` >> simp[] >>
  drule ptr_paired_prefix_ordinary_nonwrite >> disch_then irule >>
  simp[Abbr `z`, ptr_ledger_next_def, ptr_observe_def, update_var_def,
       ptr_tagged_step_def] >>
  fs[MEM] >> simp[step_prov_def, out_prov_def, step_writes_def,
       source_memory_write_ranges_def, fixed_source_write_range_def, range_bytes_def] >>
  (reverse conj_tac >- fs[update_var_def] >>
   qexistsl_tac [`0`, `update_var out v a.po_state`] >> fs[update_var_def])
QED

Finalise ptr_focus_comparison_step
