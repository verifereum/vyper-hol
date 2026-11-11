(* Forwarding certificates from the same correlated owned-prefix witnesses. *)
Theory lowerDloadOwnedForwarding
Ancestors
  lowerDloadForwardingCoverage lowerDloadOwnedTransitionBoundary
  lowerDloadExpansionEndpoint lowerDloadSafetyKernel lowerDloadSafetyAmbient
  lowerDloadReturnAlignment lowerDloadSafetyLocations lowerDloadSafetyRelation
  contextCodegenRel venomExecSemantics venomInst ptrDiscipline o1PassContract
  list arithmetic venomWf
Libs lowerDloadForwardingPackageLib lowerDloadOwnedTransitionPackageLib
     lowerDloadReturnPackageLib

Theorem ld_selected_forwarding:
  ld_sync lo P C vs0 stk PG G tn fn inst s t0 A frames N /\
  fn' = ld_image (HD frames) /\
  ld_envelope (HD frames).lf_supply fn s s.vs_inst_idx X p /\
  ld_prefix C' fn' X p h t0 t /\ ti = EL h X /\
  EVERY inst_wf (fn_insts fn) /\
  ALL_DISTINCT (MAP (\b. b.bb_label) fn.fn_blocks) /\
  ir_supply_covers_fn (HD frames).lf_supply fn /\
  dload_headroom_ok C fn inst s /\ in_revert_forward fn s ==>
  ^ld_forward C' fn' ti t
Proof
  strip_tac >>
  Cases_on `frames` >- fs[ld_sync_def] >>
  rename1 `ld_sync _ _ _ _ _ _ _ _ _ _ _ _ _ (f::fs) _` >>
  RULE_ASSUM_TAC (PURE_REWRITE_RULE [HD]) >>
  `LENGTH X = 1` by metis_tac[ld_forward_envelope_singleton] >>
  `h = 0` by (drule ld_prefix_bound >> simp[] >> decide_tac) >>
  `t = t0` by fs[ld_prefix_zero] >>
  `t.vs_alloca_next < dimword (:256)` by metis_tac[ld_sync_target_headroom] >>
  `t.vs_current_bb = s.vs_current_bb` by metis_tac[ld_sync_control] >>
  `t.vs_inst_idx = p` by
    (drule_all ld_sync_envelope_position >> simp[]) >>
  `fn' = FST (lower_dload_function_supply f.lf_supply fn)` by
    (drule ld_sync_active >> fs[ld_image_def]) >>
  `in_revert_forward fn' t` by
    (Cases_on `lower_dload_function_supply f.lf_supply fn` >>
     gvs[] >> irule ld_envelope_revert_forward >>
     goal_assum (drule_at Any) >> simp[] >> metis_tac[]) >>
  `active_inst fn' ti t` by metis_tac[ld_prefix_active] >>
  `ALL_DISTINCT (MAP (\b. b.bb_label) fn'.fn_blocks)` by
    (Cases_on `lower_dload_function_supply f.lf_supply fn` >>
     gvs[] >> drule o1ContractLowerDloadTheory.lower_dload_function_supply_labels >>
     simp[fn_labels_def]) >>
  drule_all ld_active_lookup >> strip_tac >>
  gvs[in_revert_forward_def, revert_forward_at_def, get_instruction_def] >>
  goal_assum (drule_at Any) >> simp[] >>
  fs[revert_forward_pair_def] >> decide_tac
QED

Theorem ld_owned_forwarding:
  (?stk PG G tn fn inst s t0 A frames N X p h.
    ^ld_covered_ambient lo C C' vs0 Sigma names fn fn' /\
    ld_sync lo P C vs0 stk PG G tn fn inst s t0 A frames N /\
    ld_global lo A frames /\
    EVERY (\f. f.lf_supply = Sigma f.lf_fn.fn_name) frames /\
    (!j k. j < k /\ k < LENGTH frames ==>
      list_precedes (EL j frames).lf_fn.fn_name
                    (EL k frames).lf_fn.fn_name names) /\
    fn' = ld_image (HD frames) /\
    ld_envelope (HD frames).lf_supply fn s s.vs_inst_idx X p /\
    ld_prefix C' fn' X p h t0 t /\ ti = EL h X /\
    EVERY (\f. !j a. j < LENGTH f.lf_Q /\ EL j f.lf_Q = SOME a ==>
      j IN P f.lf_fn.fn_name) frames /\
    (!g. MEM g (TL frames) ==>
      FRANGE g.lf_H SUBSET ld_slots A (TL frames) /\
      (!a. MEM (SOME a) g.lf_Q ==> a IN ld_slots A (TL frames))) /\
    in_revert_forward fn s) ==>
  ^ld_forward C' fn' ti t
Proof
  strip_tac >> fs[] >>
  `ALL_DISTINCT (MAP (\b. b.bb_label) fn.fn_blocks) /\
   EVERY inst_wf (fn_insts fn)` by
    (drule_all ld_sync_fn_shape >> strip_tac >>
     drule o1_fn_shape_components >>
     simp[fn_inst_wf_def, EVERY_MEM, fn_insts_def, fn_insts_blocks_def,
          MEM_FLAT, MEM_MAP, PULL_EXISTS] >> metis_tac[fn_insts_blocks_MEM]) >>
  `dload_headroom_ok C fn inst s` by
    (drule_all ld_sync_source_mem_inv >> simp[]) >>
  `ir_supply_covers_fn (HD frames).lf_supply fn` by
    (Cases_on `frames` >- fs[ld_sync_def] >>
     drule_at (Pat `ld_sync _ _ _ _ _ _ _ _ _ _ _ _ _ _ _`)
       ld_sync_supply_covered >>
     disch_then (qspec_then `Sigma` mp_tac) >>
     (impl_tac >- fs[]) >> fs[]) >>
  drule_all (SRULE [] ld_selected_forwarding) >> gvs[]
QED
