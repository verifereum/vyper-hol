Theory assignEffectfulIndexEmpty
Ancestors
  assignPlaceEmptyStore stmtSimAugAssignPlaceMemory stmtSimDeclMem
  loweringPosts exprLoweringProps stmtLowering compileEnv exprOperandVar
  vyperState vyperPlaceFrames stmtSimAssignStorage
  gasOutcome gasSummary fragGasMode loweringStateRelDefs stmtSimDeclCompose
  vyperStorageFootprint vyperStoragePlaceObserved vyperFiniteStoragePreservation
  vyperPlaceTyping vyperTypeValues vyperStorageTrace vyperTypeDefaults tuplePlaceStep

Theorem assign_effectful_empty_target_store:
  (?H. valid_horizon cx st0 H mid.storage_trace) /\
  (!H. valid_horizon cx st0 H mid.storage_trace ==>
    target_post H ctx func cenv cx es sa st s0 mid (PlaceR p) (Type dty)
      (dst,SOME loc,SOME (ValPT dty)) s /\
    storage_place_observed H p /\ regions_consistent (FST H) /\
    storage_locks_separated (FST H) (SND H)) /\
  evaluate_type (get_tenv cx) dty = SOME dtv /\ has_length_word dty /\
  compile_store_at_loc cenv.ce_imm_alloca dst (Lit 0w) (SOME loc) st = ((),sb) /\
  write_place cx p (default_value dtv) mid = (INL (),ff) /\
  expr_sim_inv cenv cx env mid /\
  acyclic_struct_metadata cenv.ce_struct_fields /\
  local_ptrs_reserved cenv st /\
  (!id path entry t0.
    p = MemoryPlace id path /\ lookup_scopes id mid.scopes = SOME entry /\
    cenv.ce_var_type id = SOME t0 ==>
    evaluate_type (get_tenv cx) t0 = SOME entry.type) /\
  loc <> LocCode /\ loc <> LocCalldata /\
  fn_has_code st sb func /\ fn_inst_ids_distinct func /\
  ~s.vs_halted /\ s.vs_current_bb = st.cs_current_bb /\
  s.vs_inst_idx = LENGTH st.cs_current_insts /\
  alloca_frame cenv es sa s0 cenv mid s /\ ci_mono sa st /\
  ~block_is_terminated st ==>
  gas_outcome F (cx_tops cx) (ctx,func) cx st0 (write_place cx p (default_value dtv))
    (mid,s)
    (\H res ee u. !tail. stmt_post H ctx func cx lctx cenv cenv sa sb es s0
       res (ee with gas_obs := tail) u)
    (\H res ee r. !tail. stmt_exit (RetQ H) (ee with gas_obs := tail) res r)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  qpat_assum `?H. valid_horizon _ _ H _`
    (qx_choose_then `H0` assume_tac) >>
  `target_post H0 ctx func cenv cx es sa st s0 mid (PlaceR p) (Type dty)
     (dst,SOME loc,SOME (ValPT dty)) s` by metis_tac[] >>
  `?w. eval_operand dst s = SOME w /\
       place_ptr_rel cenv cx s (PlaceR p) w (SOME loc) (Type dty)` by
    gvs[target_post_def] >>
  `!x. dst = Var x ==> not_fresh_at st x` by gvs[target_post_def] >>
  `!H. valid_horizon cx st0 H mid.storage_trace ==>
    stmt_state_rel H ctx func cenv cx mid s` by
    (rpt strip_tac >> fs[target_post_def] >> metis_tac[]) >>
  drule_all assign_place_empty_store_framed >> strip_tac >>
  `!tail. write_place cx p (default_value dtv) (mid with gas_obs := tail) =
      (INL (),ff with gas_obs := tail)` by
    (Cases_on `p`
     >- (qpat_x_assum `write_place _ _ _ _ = _` mp_tac >>
         simp[write_place_def, write_storage_slot_gas_obs, AllCaseEqs()] >>
         rpt strip_tac >> gvs[])
     >- (drule aug_place_memory_write_gas_obs >> simp[]) >>
     fs[place_ptr_rel_def]) >>
  `!H. valid_horizon cx st0 H mid.storage_trace ==>
    storage_well_formed_on cx ff (FST H)` by suspend "storage_wf" >>
  `!H. valid_horizon cx st0 H mid.storage_trace ==>
    stmt_post H ctx func cx lctx cenv cenv sa sb es s0 (INL ()) ff t` by
    (rpt strip_tac >> irule aug_place_normal_post >> simp[] >>
     conj_tac
     >- (fs[target_post_def] >> metis_tac[compiler_ci_mono_not_fresh]) >>
     conj_tac >- (fs[target_post_def] >> metis_tac[]) >>
     Cases_on `loc` >> gvs[compile_store_at_loc_def] >>
     irule emit_void_nonterminator_open >> goal_assum (drule_at Any) >>
     simp[venomInstTheory.is_terminator_def]) >>
  `ff.storage_trace = mid.storage_trace` by
    metis_tac[write_place_storage_trace] >>
  simp[gas_outcome_def] >> qexists_tac `[]` >> disj2_tac >> disj1_tac >>
  simp[gas_summary_at_def, gas_marked_exec_def] >>
  qexistsl_tac [`INL ()`, `ff`, `OK t`] >> simp[stmt_post_end_gas_obs]
QED

Resume assign_effectful_empty_target_store[storage_wf]:
  rpt strip_tac >>
  qpat_assum `!H. valid_horizon _ _ H _ ==> _ /\ _`
    (qspec_then `H` (drule_then strip_assume_tac)) >>
  `storage_well_formed_on cx mid (FST H)` by fs[target_post_def] >>
  Cases_on `p`
  >- (rename1 `write_place cx (StoragePlace tr slot leaf) _ mid = _` >>
      `leaf = dtv` by fs[target_post_def, place_ptr_rel_def] >>
      qpat_x_assum `leaf = dtv` SUBST_ALL_TAC >>
      qpat_x_assum `storage_place_observed H _`
        (mp_tac o REWRITE_RULE [storage_place_observed_def]) >>
      disch_then (qx_choosel_then [`root`, `tv`, `path`, `delta`]
        strip_assume_tac) >>
      `storage_observations_ok cx H [StorageRoot tr (w2n root) tv]` by
        (simp[storage_observations_ok_def, storage_trace_regions_def,
           storage_trace_locks_def, storage_roots_fit_def,
           storage_trace_backends_well_formed_def] >>
         qpat_assum `regions_consistent (FST H)`
           (mp_tac o Q.SPECL [`tr`, `root`, `tv`] o CONJUNCT1 o
            REWRITE_RULE [regions_consistent_def]) >> simp[]) >>
      `well_formed_type_value dtv` by
        metis_tac[evaluate_type_well_formed_type_value] >>
      `value_has_type dtv (default_value dtv)` by
        metis_tac[default_value_has_type] >>
      `runtime_place_typed cx mid (StoragePlace tr slot dtv) dtv` by
        simp[runtime_place_typed_storage] >>
      mp_tac (Q.INST [`observations` |-> `[StorageRoot tr (w2n (root : bytes32)) tv]`,
        `p` |-> `StoragePlace tr slot dtv`, `st` |-> `mid`, `st'` |-> `ff`,
        `leaf_tv` |-> `dtv`, `v` |-> `default_value dtv`,
        `res` |-> `INL ()`] write_place_preserves_storage_well_formed_on) >>
      impl_tac >- (simp[] >> qexistsl_tac [`path`, `delta`] >> simp[]) >> simp[])
  >- (drule write_memory_place_frame >> strip_tac >>
      `ff.accounts = mid.accounts /\ ff.tStorage = mid.tStorage` by simp[] >>
      metis_tac[storage_well_formed_on_backends]) >>
  fs[target_post_def, place_ptr_rel_def]
QED
Finalise assign_effectful_empty_target_store
