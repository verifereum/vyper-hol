Theory lowerDloadCallMemory
Ancestors
  lowerDloadFrameRepresentation lowerDloadLifetime lowerDloadRelocation
  lowerDloadOwnership lowerDloadPairedBoundary o1LowerDloadJointRestore
  stepWriteFootprintBase venomExecSemantics venomState finite_map pred_set list

Theorem ld_call_entry_memory:
  setup_callee source xs s = SOME ss /\ setup_callee callee ys t = SOME cs /\
  enters_block source ss s1 /\ enters_block callee cs t1 /\
  f.lf_local = L /\ f.lf_params = AP /\ f.lf_prov = AG /\
  ld_byte_rel (\a b. (a=b /\ a<lo) \/
    ld_site_bytes E {owner | ?bs sz. ld_live astk L AP AG (owner,(bs,sz))} a b)
    Ts Tt (\a. read_memory a 1 s) (\b. read_memory b 1 t) ==>
  ld_byte_rel (\a b. (a=b /\ a<lo) \/
    ld_site_bytes E {owner | ?bs sz.
      ld_live (f::astk) FEMPTY (MAP (ld_op_prov AG) ops) FEMPTY (owner,(bs,sz))} a b)
    Ts Tt (\a. read_memory a 1 s1) (\b. read_memory b 1 t1)
Proof
  strip_tac >>
  `s1.vs_memory = ss.vs_memory /\ t1.vs_memory = cs.vs_memory` by
    metis_tac[enters_block_memory] >>
  `ss.vs_memory = s.vs_memory /\ cs.vs_memory = t.vs_memory` by
    gvs[setup_callee_def, AllCaseEqs()] >>
  drule_all ld_live_call_shape >> strip_tac >>
  fs[read_memory_def]
QED

Theorem ld_call_return_memory:
  ld_byte_rel (\a b. (a=b /\ a<lo) \/ ld_site_bytes E live a b)
    Ts Tt (\a. read_memory a 1 u) (\b. read_memory b 1 v) /\
  survivors SUBSET live /\
  bind_outputs outsS valsS (adopt_return_fmp irS (merge_callee_state s u)) = SOME s' /\
  bind_outputs outsT valsT (adopt_return_fmp irT (merge_callee_state t v)) = SOME t' ==>
  ld_byte_rel (\a b. (a=b /\ a<lo) \/
    ld_site_bytes (DRESTRICT E survivors) survivors a b)
    Ts Tt (\a. read_memory a 1 s') (\b. read_memory b 1 t')
Proof
  strip_tac >>
  qpat_x_assum `bind_outputs outsS _ _ = _` (mp_then Any SUBST1_TAC ld_bind_outputs_vars_only) >>
  qpat_x_assum `bind_outputs outsT _ _ = _` (mp_then Any SUBST1_TAC ld_bind_outputs_vars_only) >>
  fs[read_memory_def, adopt_return_fmp_def, merge_callee_state_def] >>
  irule ld_byte_rel_restrict >> goal_assum (drule_at Any) >>
  simp[ld_site_bytes_def, ld_site_entry_restrict] >> metis_tac[SUBSET_DEF]
QED
