(* The output's alloca frontier stays below the initial frame pointer on
   owned states, when the source has DALLOCA. *)
Theory lowerDloadTargetHeadroom
Ancestors
  lowerDloadCurrentSafety lowerDloadScratchSafety lowerDloadAllocationOrigins
  lowerDloadPublicTrace lowerDloadSafetyLocations lowerDloadSafetyKernel
  lowerDloadSafetyAmbient lowerDloadSafetyRelation lowerDloadSafetyBoundary
  lowerDloadScratchTransport ctxLookupAgreeHelpers lowerDloadDefs ptrDiscipline
  unitTransformDefs venomWf venomState list pred_set
Libs lowerDloadOwnedTransitionPackageLib

Theorem ld_prefix_initial_fmp[local]:
  !h t. ld_prefix C fn X p h t0 t ==> t.vs_initial_fmp = t0.vs_initial_fmp
Proof
  Induct >- simp[ld_prefix_zero] >>
  rpt strip_tac >> drule ld_prefix_predecessor >> strip_tac >>
  first_x_assum drule >> strip_tac >>
  drule step_inst_initial_fmp >> simp[]
QED

(* The frame's target frontier sits below the initial frame pointer, with
   room for one more scratch site when a private one is still fresh. *)
Theorem ld_sync_dalloca_frontier[local]:
  ld_sync lo P C vs0 stk PG G tn fn inst s t A (f::fs) N /\
  o1_ctx_shape C /\ mem_inv dload_headroom_ok C vs0 /\ ctx_has_dalloca C /\
  ALL_DISTINCT (MAP (\g. g.lf_fn) (f::fs)) ==>
  t.vs_alloca_next <= w2n t.vs_initial_fmp /\
  !d ai. ld_private f d ai /\ FLOOKUP t.vs_allocas ai = NONE ==>
    t.vs_alloca_next + 32 <= w2n t.vs_initial_fmp
Proof
  strip_tac >>
  `dload_headroom_ok C fn inst s` by
    (irule ld_sync_source_mem_inv >> metis_tac[]) >>
  `s.vs_alloca_next + 32 * ctx_dload_count C <= w2n s.vs_initial_fmp` by
    (qpat_x_assum `dload_headroom_ok _ _ _ _` mp_tac >>
     pure_rewrite_tac[dload_headroom_ok_def, GSYM ctx_has_dalloca_def] >>
     qpat_x_assum `ctx_has_dalloca C` (fn th => rewrite_tac[th]) >>
     strip_tac) >>
  `t.vs_initial_fmp = s.vs_initial_fmp` by
    (drule ld_sync_memory >> simp[ld_nonghost_def]) >>
  drule ld_sync_frontier >> strip_tac >>
  qpat_x_assum `t.vs_initial_fmp = _` (fn th => rewrite_tac[th]) >>
  qpat_x_assum `t.vs_alloca_next = _` (fn th => rewrite_tac[th]) >>
  conj_tac >- decide_tac >>
  rpt strip_tac >>
  drule ld_sync_active >> simp[] >> strip_tac >>
  `d NOTIN f.lf_E` by
    (spose_not_then assume_tac >>
     drule_all ld_maps_private >> simp[]) >>
  `set (MAP (\g. g.lf_fn) (f::fs)) SUBSET set C.ctx_functions` by
    (qpat_x_assum `ld_sync _ _ _ _ _ _ _ _ _ _ _ _ _ _ _` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >>
     simp[ld_sync_def, SUBSET_DEF, MEM_MAP, EVERY_MEM] >> rpt strip_tac >>
     metis_tac[]) >>
  `EVERY (ld_maps A) (f::fs)` by
    (qpat_x_assum `ld_sync _ _ _ _ _ _ _ _ _ _ _ _ _ _ _` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >> simp[ld_sync_def, EVERY_MEM] >>
     metis_tac[]) >>
  `ld_charge (f::fs) + 1 <= ctx_dload_count C` by
    (irule ld_configured_charge_fresh_bound >> metis_tac[]) >>
  decide_tac
QED

Theorem ld_owned_target_headroom:
  ^ld_owned lo P C C' vs0 Sigma names fn' ti t /\
  o1_ctx_shape C /\ o1_run_state_ok vs0 /\ mem_inv dload_headroom_ok C vs0 /\
  (!fn. MEM fn C.ctx_functions ==> ir_supply_covers_fn (Sigma fn.fn_name) fn) /\
  ctx_has_dalloca C ==>
  t.vs_alloca_next <= w2n t.vs_initial_fmp
Proof
  simp[] >> strip_tac >>
  `frames <> []` by
    (qpat_x_assum `ld_sync _ _ _ _ _ _ _ _ _ _ _ _ _ _ _` mp_tac >>
     pure_rewrite_tac[ld_sync_def] >> metis_tac[]) >>
  Cases_on `frames` >- gvs[] >> rename1 `ld_sync _ _ _ _ _ _ _ _ _ _ _ _ _ (f::fs) _` >>
  RULE_ASSUM_TAC (REWRITE_RULE [listTheory.HD]) >>
  `f.lf_fn = fn /\ MEM fn C.ctx_functions` by
    (qpat_x_assum `ld_sync _ _ _ _ _ _ _ _ _ _ _ _ _ _ _` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >> simp[ld_sync_def] >> metis_tac[]) >>
  `ALL_DISTINCT (MAP (\g. g.lf_fn) (f::fs))` by
    (qpat_x_assum `!j k. j < k /\ _ ==> _` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >>
     strip_tac >> simp[EL_ALL_DISTINCT_EL_EQ, EL_MAP] >> rpt strip_tac >>
     qmatch_goalsub_rename_tac `(EL j (f::fs)).lf_fn = (EL k (f::fs)).lf_fn` >>
     Cases_on `j = k` >- simp[] >>
     `j < k \/ k < j` by decide_tac >>
     fs[] >> metis_tac[list_precedes_distinct]) >>
  `ir_supply_covers_fn f.lf_supply fn` by
    (qpat_x_assum `EVERY (\f. f.lf_supply = _) _` mp_tac >>
     simp[] >> strip_tac >> metis_tac[]) >>
  `t.vs_initial_fmp = t0.vs_initial_fmp` by metis_tac[ld_prefix_initial_fmp] >>
  pop_assum (fn th => rewrite_tac[th]) >>
  drule ld_sync_source >> strip_tac >>
  drule_all ld_sync_fn_shape >> strip_tac >>
  drule o1_fn_shape_components >> strip_tac >>
  drule_all ld_sync_dalloca_frontier >> strip_tac >>
  `inst_wf inst` by
    (fs[fn_inst_wf_def, contextCodegenRelTheory.active_inst_def] >>
     metis_tac[MEM_EL]) >>
  Cases_on `inst.inst_opcode = DLOAD` >- suspend "dload" >>
  Cases_on `inst.inst_opcode = DLOADBYTES` >- suspend "dloadbytes" >>
  `X = [inst]` by (irule ld_envelope_ordinary >> metis_tac[]) >>
  `h = 0` by (drule ld_prefix_bound >> simp[]) >>
  gvs[ld_prefix_zero]
QED

Resume ld_owned_target_headroom[dload]:
  `?off out. inst.inst_operands = [off] /\ inst.inst_outputs = [out]` by
    fs[inst_wf_def, LENGTH_EQ_NUM_compute] >>
  drule ld_sync_active >> simp[] >> strip_tac >>
  drule_all ld_dload_envelope_temporary >> strip_tac >>
  `FLOOKUP s.vs_allocas ai = NONE` by
    (irule ld_sync_private_source_absent >>
     gvs[o1PassContractTheory.o1_run_state_ok_def, o1_initial_state_ok_def] >>
     metis_tac[]) >>
  `t0.vs_alloca_next < dimword(:256)` by metis_tac[ld_sync_ambient_headroom] >>
  `FLOOKUP t0.vs_allocas ai = NONE ==> t0.vs_alloca_next + 32 < dimword(:256)` by
    (strip_tac >> irule ld_sync_scratch_fresh_headroom >> metis_tac[]) >>
  `!b n. FLOOKUP t0.vs_allocas ai = SOME(b,n) ==>
     n = 32 /\ b + 32 <= t0.vs_alloca_next` by
    (rpt gen_tac >> disch_tac >> irule ld_sync_scratch_cached_bound >> metis_tac[]) >>
  drule_all lower_dload_prefix_scratch >> strip_tac >>
  qpat_x_assum `t.vs_alloca_next <= _ + _` mp_tac >>
  Cases_on `FLOOKUP t0.vs_allocas ai = NONE`
  >- (qpat_x_assum `!d ai. ld_private _ _ _ /\ _ ==> _`
        (qspecl_then [`inst.inst_id`, `ai`] mp_tac) >>
      impl_tac >- asm_rewrite_tac[] >>
      asm_rewrite_tac[] >> decide_tac) >>
  asm_rewrite_tac[] >> decide_tac
QED

Resume ld_owned_target_headroom[dloadbytes]:
  `?dest off len. inst.inst_operands = [dest;off;len]` by
    fs[inst_wf_def, LENGTH_EQ_NUM_compute] >>
  drule_all ld_dloadbytes_envelope_temporary >> strip_tac >>
  `h < 2` by (drule ld_prefix_bound >> simp[]) >>
  Cases_on `h = 0` >- gvs[ld_prefix_zero] >>
  `h = 1` by decide_tac >>
  qpat_x_assum `h = 1` SUBST_ALL_TAC >>
  drule_all ld_dloadbytes_prefix_observations >> strip_tac >>
  qpat_x_assum `t.vs_alloca_next = _` (fn th => rewrite_tac[th]) >>
  first_assum ACCEPT_TAC
QED
Finalise ld_owned_target_headroom
