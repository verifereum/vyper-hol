(* Full lower-bound ghost resources across the concrete reason head. *)
Theory bodyFullRaiseReasonHeadGhost
Ancestors
  bodyFullRaiseReasonHead stmtReasonMemory revertReasonPrefixPtr revertReasonLayout
  revertReasonPrefixFramePtr ptrSafetyTransport
  ghostObservationPtr valueEncodingProps abiEncoderZeroFrame
  loweringPosts exprLoweringProps bodyPtrDefs ptrDiscipline
  venomExecSemantics venomInst venomState finite_map words arithmetic pred_set

Theorem reason_head_allocas_from:
  run_inst_seq (reason_head id v M) s = OK t /\
  allocas_from lo s /\ lo <= s.vs_alloca_next ==>
  allocas_from lo t /\ lo <= t.vs_alloca_next
Proof
  simp[reason_head_def] >> strip_tac >>
  drule run_inst_seq_four_endpoint >> strip_tac >>
  `!id op args outs a b.
     op <> INVOKE /\ step_inst_base (mk_inst id op args outs) a = OK b /\
     allocas_from lo a /\ lo <= a.vs_alloca_next ==>
     allocas_from lo b /\ lo <= b.vs_alloca_next` by
    (rpt gen_tac >> strip_tac >> irule step_inst_allocas_from >>
     qexistsl_tac [`ARB`,`0`,`mk_inst id' op args outs`,`a`] >>
     simp[step_inst_non_invoke, mk_inst_def]) >>
  qpat_assum `!id op args outs a b. _` (fn th =>
    map_every (fn pat => qpat_assum pat (mp_then Any mp_tac th) >>
      simp[] >> strip_tac)
      [`step_inst_base _ s = _`, `step_inst_base _ s1 = _`,
       `step_inst_base _ s2 = _`]) >>
  qpat_assum `!id op args outs a b. _` (fn th =>
    qpat_assum `step_inst_base _ s3 = _` (mp_then Any mp_tac th)) >> simp[]
QED

Theorem reason_head_lo_frame:
  stmt_state_rel H ctx func cenv cx es s /\ fn_inst_ids_distinct func /\
  MEM (mk_inst id ALLOCA [Lit (n2w (64+M))]
    ["%" ++ toString v]) (fn_insts func) /\
  MEM (mk_inst (id+3) ALLOCA [Lit (n2w M)]
    ["%" ++ toString (v+2)]) (fn_insts func) /\
  (!k. k < 2 ==> not_local_ptr cenv es.scopes ("%" ++ toString (v+k))) /\
  64+M < dimword (:256) /\
  run_inst_seq (reason_head id v M) s = OK t /\
  inst_seq_ptr D lo ctx func PG G tn (reason_head id v M) s Gf tnf /\
  allocas_from lo s /\ lo <= s.vs_alloca_next ==>
  allocas_from lo t /\ lo <= t.vs_alloca_next /\
  mem_bytes_at 0 lo t.vs_memory = mem_bytes_at 0 lo s.vs_memory /\
  (!i. i < lo /\ i IN tnf.t_mem ==> i IN tn.t_mem)
Proof
  strip_tac >> drule_all reason_head_allocas_from >> strip_tac >>
  `reason_head id v M = revert_reason_prefix id v M` by
    simp[reason_head_def, revert_reason_prefix_def] >>
  fs[] >> drule_at (Pat `inst_seq_ptr _ _ _ _ _ _ _ _ _ _ _`)
    revert_reason_prefix_memory_effects >> disch_then drule >>
  disch_then (qspec_then `t` mp_tac) >> impl_tac >- simp[ADD_COMM] >> strip_tac >>
  `lo <= b /\ lo <= c` by
    (fs[allocas_from_def] >> metis_tac[]) >>
  simp[] >> irule abi_encoder_mem_bytes_singletons >> rpt strip_tac >>
  qpat_assum `!i. _ ==> mem_bytes_at i 1 _ = _` irule >>
  simp[] >> decide_tac
QED

Theorem reason_head_ghost_kept_at:
  stmt_state_rel H ctx func cenv cx es s /\ fn_inst_ids_distinct func /\
  MEM (mk_inst id ALLOCA [Lit (n2w (64+M))]
    ["%" ++ toString v]) (fn_insts func) /\
  MEM (mk_inst (id+3) ALLOCA [Lit (n2w M)]
    ["%" ++ toString (v+2)]) (fn_insts func) /\
  (!k. k < 3 ==> not_local_ptr cenv es.scopes ("%" ++ toString (v+k))) /\
  64+M < dimword (:256) /\ sa.cs_next_id <= id /\ sa.cs_next_var <= v /\
  local_ptrs_reserved cenv sa /\
  (!x w. not_fresh_at sa x /\ lookup_var x s0 = SOME w ==> lookup_var x s = SOME w) /\
  (!aid site. FLOOKUP s0.vs_allocas aid = SOME site ==> FLOOKUP s.vs_allocas aid = SOME site) /\
  ghost_kept_at lo cenv es sa Gi ti s0 G tn /\
  allocas_from lo s /\ lo <= s.vs_alloca_next /\
  run_inst_seq (reason_head id v M) s = OK t /\
  inst_seq_ptr D lo ctx func PG G tn (reason_head id v M) s Gf tnf ==>
  ghost_kept_at lo cenv es sa Gi ti s0 Gf tnf
Proof
  strip_tac >>
  `!k. k < 2 ==> not_local_ptr cenv es.scopes ("%" ++ toString (v+k))`
    by (rpt strip_tac >> first_x_assum irule >> decide_tac) >>
  drule_all reason_head_lo_frame >> strip_tac >>
  `ghost_kept cenv es sa Gi ti s0 G tn` by
    (fs[ghost_kept_zero, ghost_kept_at_def] >> metis_tac[]) >>
  `reason_head id v M = revert_reason_prefix id v M` by
    simp[reason_head_def, revert_reason_prefix_def] >> fs[] >>
  drule_at (Pat `inst_seq_ptr _ _ _ _ _ _ _ _ _ _ _`)
    revert_reason_prefix_ghost_kept >> disch_then drule >>
  disch_then (drule_at (Pat `ghost_kept _ _ _ _ _ _ _ _`)) >>
  disch_then (qspec_then `t` mp_tac) >>
  impl_tac >- simp[ADD_COMM] >>
  simp[ghost_kept_zero, ghost_kept_at_def] >>
  strip_tac >> simp[] >> rpt strip_tac >>
  qpat_x_assum `ghost_kept_at _ _ _ _ _ _ _ _ _` mp_tac >>
  simp[ghost_kept_at_def] >> metis_tac[]
QED

Theorem reason_head_ghost_inv_at:
  stmt_state_rel H ctx func cenv cx es s /\ fn_inst_ids_distinct func /\
  MEM (mk_inst id ALLOCA [Lit (n2w (64+M))]
    ["%" ++ toString v]) (fn_insts func) /\
  MEM (mk_inst (id+3) ALLOCA [Lit (n2w M)]
    ["%" ++ toString (v+2)]) (fn_insts func) /\
  (!k. k < 3 ==> not_local_ptr cenv es.scopes ("%" ++ toString (v+k))) /\
  (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) \/
     cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==>
     !k. k < 3 ==> x <> "%" ++ toString (v+k)) /\
  (!x. lo <> 0 /\ cenv.ce_imm_alloca = SOME (Var x) ==>
     !k. k < 3 ==> x <> "%" ++ toString (v+k)) /\
  64+M < dimword (:256) /\ ghost_inv_at D lo d cenv cx es G tn s /\
  run_inst_seq (reason_head id v M) s = OK t /\
  inst_seq_ptr D lo ctx func PG G tn (reason_head id v M) s Gf tnf ==>
  ghost_inv_at D lo d cenv cx es Gf tnf t
Proof
  strip_tac >>
  `!k. k < 2 ==> not_local_ptr cenv es.scopes ("%" ++ toString (v+k))`
    by (rpt strip_tac >> first_x_assum irule >> decide_tac) >>
  `allocas_from lo s /\ lo <= s.vs_alloca_next` by fs[ghost_inv_at_def] >>
  drule_all reason_head_lo_frame >> strip_tac >>
  `reason_head id v M = revert_reason_prefix id v M` by
    simp[reason_head_def, revert_reason_prefix_def] >> fs[] >>
  drule revert_reason_prefix_ghost_observations >> strip_tac >>
  drule revert_reason_prefix_data_frame >> strip_tac >>
  `t.vs_immutables = s.vs_immutables` by
    (qpat_assum `run_inst_seq _ s = OK t` mp_tac >>
     pure_rewrite_tac[revert_reason_prefix_def] >> strip_tac >>
     drule run_inst_seq_four_endpoint >>
     simp[step_alloca_eq, step_add_eq, step_mstore_eq, AllCaseEqs()] >>
     rpt strip_tac >> gvs[update_var_def, mstore_def]) >>
  drule_at (Pat `inst_seq_ptr _ _ _ _ _ _ _ _ _ _ _`)
    revert_reason_prefix_memory_effects >> disch_then drule >>
  disch_then (qspec_then `t` mp_tac) >> impl_tac >- simp[ADD_COMM] >> strip_tac >>
  qpat_x_assum `ghost_inv_at _ _ _ _ _ _ _ _ _` mp_tac >>
  rewrite_tac[ghost_inv_at_def] >> strip_tac >> rpt conj_tac
  >- suspend "locals"
  >- (Cases_on `d` >> simp[return_buf_ptr_def] >> PairCases_on `x` >>
      fs[return_buf_ptr_def] >> conj_tac
      >- (`lookup_var x t = lookup_var x s` by
            (irule revert_reason_prefix_lookup_frame >> metis_tac[ADD_COMM]) >> simp[]) >>
      irule revert_reason_prefix_old_ptr_covers >> metis_tac[ADD_COMM])
  >- metis_tac[ADD_COMM]
  >- fs[stor_taint_ok_at_def]
  >- (rpt strip_tac >> `i IN tn.t_mem` by metis_tac[] >> metis_tac[])
  >- metis_tac[ADD_COMM]
  >- simp[] >> simp[]
QED

Resume reason_head_ghost_inv_at[locals]:
  rpt gen_tac >> strip_tac >>
  `!k. k < 3 ==> p <> STRING #"%" (toString (v+k))` by
    (fs[loweringStateRelDefsTheory.not_local_ptr_def] >> metis_tac[]) >>
  `lookup_var p t = lookup_var p s` by
    (irule revert_reason_prefix_lookup_frame >>
     qexistsl_tac [`id`, `M`, `v`] >> simp[ADD_COMM]) >>
  `local_ptrs_rel func cenv es.scopes s` by
    fs[stmt_state_rel_def, loweringStateRelDefsTheory.state_rel_def] >>
  `?w. lookup_var p s = SOME w /\ type_memory_size entry.type <= sz /\
       val_wf entry.type entry.value` by
    (fs[loweringStateRelDefsTheory.local_ptrs_rel_def] >> metis_tac[]) >>
  conj_tac >-
    (irule revert_reason_prefix_old_ptr_covers >> metis_tac[]) >>
  rpt gen_tac >> strip_tac >>
  irule robust_val_in_memory_exterior_no_new_taint >>
  conj_tac >- simp[] >>
  qexistsl_tac [`{i | b <= i /\ i < b+(64+M)} UNION {i | c <= i /\ i < c+M}`,
    `s.vs_memory`, `t.vs_memory`, `tn.t_mem`, `tnf.t_mem`] >>
  `w' = w` by fs[] >> qpat_x_assum `w' = w` SUBST_ALL_TAC >>
  conj_tac >- metis_tac[] >>
  pure_asm_rewrite_tac[] >> rewrite_tac[] >> rpt strip_tac >>
  `val_footprint entry.type entry.value <= sz` by
    metis_tac[exprSimPropsTheory.val_footprint_le, LESS_EQ_TRANS] >>
  `local_region cenv es.scopes s name (w2n w) sz` by
    (simp[loweringStateRelDefsTheory.local_region_def] >> metis_tac[]) >>
  `i NOTIN ({i | b <= i /\ i < b+(64+M)} UNION {i | c <= i /\ i < c+M})` by
    (irule revert_reason_prefix_local_exterior >> simp[] >>
     goal_assum (drule_at (Pat `local_region _ _ _ _ _ _`)) >>
     simp[] >> goal_assum (drule_at (Pat `run_inst_seq _ _ = _`)) >>
     fs[ADD_COMM] >> metis_tac[]) >> fs[]
QED

Finalise reason_head_ghost_inv_at
