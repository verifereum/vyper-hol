(* Constructor immutable assignments at the selected qualified subpath. *)
Theory bodyQualifiedPlaceImmScalarMods
Ancestors
  bodyAssignQualifiedStageJoinMods bodyWriteImmWordMods bodyWriteImmCopyMods
  bodyFullPathHistory immutableAssignOpen immutableAssignEmpty
  immutableRegionFrameProps stateRelProj vyperTypeInitialState vyperPlaceFrames
  stmtSimProps bodyPtrDefs loweringStateRelDefs gasOutcomeFullPostMods
  stmtLowering context freshWrites ptrDiscipline words compileEnv exprLoweringProps
  bodyFullShadowBodyInv vyperStorageFootprint exprSimProps valueEncodingProps venomMemProps
  bodyFullImmutablePathStore vyperTypeEnv venomState stmtSimDefs bodyFullPredsMods
  exprSimHypsDefs bodyImmutableAugAssignExec vyperTypeDefaults
  bodyFullPostsMods bodyInvSplit bodySimFull loweringPosts immutableWritebackTransport

val location =
  ``cenv.ce_is_ctor /\
    ALOOKUP (ee : evaluation_state).immutables cx.txn.target = SOME imms /\
    FLOOKUP (get_source_immutables owner imms) id = SOME (itv,old) /\
    FLOOKUP cenv.ce_module_vars (owner,id) = SOME (ImmutableLoc off) /\
    mem_path_offset itv path = SOME (k,ptv) /\
    evaluate_type (get_tenv cx) dty = SOME ptv /\
    eval_operand dst s = SOME (n2w (off+k)) /\
    op_taint tn dst = {} /\ op_prov G dst = NONE``;

val entry =
  ``contract_inv mods exps ctx cenv cx /\ expr_sim_inv_mods mods cenv cx env ee /\
    local_ptrs_reserved cenv su /\
    (!x cap. cenv.ce_return_pc = SOME (PtrVar (Var x) cap) ==> not_fresh_at su x) /\
    fn_has_code su sb func /\ ~s.vs_halted /\ s.vs_current_bb = su.cs_current_bb /\
    s.vs_inst_idx = LENGTH su.cs_current_insts /\ alloca_history func s /\
    (ctx_has_dalloca ctx ==> allocas_below_fmp s) /\
    return_buf_frame d cenv su s /\ return_buf_sep d cenv ee s /\
    sa.cs_next_var <= su.cs_next_var /\
    s0.vs_alloca_next <= s.vs_alloca_next /\
    (!x w. not_fresh_at sa x /\ lookup_var x s0 = SOME w ==> lookup_var x s = SOME w) /\
    (!aid b. FLOOKUP s0.vs_allocas aid = SOME b ==> FLOOKUP s.vs_allocas aid = SOME b) /\
    alloca_frame cenv es sa s0 cenv ee s /\ ghost_kept_at lo cenv es sa G0 tn0 s0 G tn /\
    (!H. valid_horizon cx st0 H ee.storage_trace ==>
       dead_lo_ok_mods H (DF H) lo cenv cx /\ stmt_state_rel H ctx func cenv cx ee s /\
       immutable_frame_mods func cenv cx ee s /\ storage_well_formed_on cx ee (FST H) /\
       ghost_inv_at_mods (DF H) lo d cenv cx ee G tn s)``;

val outcome =
  ``gas_outcome_full_mods (DF,lo,explicit,ctx,func,PG) cenv.ce_modules cx st0
    (write_place cx (ImmutablePlace owner id path) v) (ee,s,G,tn)
    (\H res fin Gf tf q.
       res = INL () /\ stmt_lands lctx sb res q /\ ~q.vs_halted /\ ~block_is_terminated sb /\
       cenv_top_ext cenv cenv fin.scopes /\
       stmt_state_rel H ctx func cenv cx fin q /\ immutable_frame_mods func cenv cx fin q /\
       storage_well_formed_on cx fin (FST H) /\
       return_buf_frame d cenv sb q /\ return_buf_sep d cenv fin q /\
       alloca_history func q /\ (ctx_has_dalloca ctx ==> allocas_below_fmp q) /\
       s0.vs_alloca_next <= q.vs_alloca_next /\ ghost_inv_at_mods (DF H) lo d cenv cx fin Gf tf q /\
       (!x w. not_fresh_at sa x /\ lookup_var x s0 = SOME w ==> lookup_var x q = SOME w) /\
       (!aid b. FLOOKUP s0.vs_allocas aid = SOME b ==> FLOOKUP q.vs_allocas aid = SOME b) /\
       (!x. not_fresh_at sa x ==> FLOOKUP Gf x = FLOOKUP G0 x /\ op_taint tf (Var x) = op_taint tn0 (Var x)) /\
       alloca_frame cenv es sa s0 cenv fin q /\
       (!aid a n i. FLOOKUP s0.vs_allocas aid = SOME (a,n) /\ aid < sa.cs_next_id /\
        (!name b cap. local_region cenv es.scopes s0 name b cap ==> a+n <= b \/ b+cap <= a) /\
        a <= i /\ i < a+n /\ i IN tf.t_mem ==> i IN tn0.t_mem)) R``;

Theorem qualified_place_imm_word_mods:
  ^entry /\ ^location /\ ALOOKUP cenv.ce_modules owner = SOME tops /\
  is_word_type dty /\ value_has_type ptv v /\
  write_place cx (ImmutablePlace owner id path) v ee = (INL (),ef) /\
  compile_assign_value cenv dst LocCode op T loc dty sty bytes su = ((),sb) /\
  eval_operand op s = SOME (typed_val_to_w256 ptv v) /\ op_taint tn op = {} /\
  (!x. op = Var x ==> not_fresh_at su x) /\
  (!x cap. cenv.ce_return_buf = SOME (PtrVar (Var x) cap) ==> not_fresh_at su x) ==>
  ^outcome
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `compile_imm_store_word cenv.ce_imm_alloca dst op su = ((),sb)` by
    fs[compile_assign_value_def,comp_bind_def,comp_return_def] >>
  `su.cs_next_var <= sb.cs_next_var` by
    (mp_tac (Q.SPECL [`cenv.ce_imm_alloca`,`dst`,`op`,`su`] ci_mono_compile_imm_store_word) >>
     simp[ci_mono_def]) >>
  qpat_x_assum `ghost_kept_at _ _ _ _ _ _ _ _ _`
    (strip_assume_tac o REWRITE_RULE [ghost_kept_at_def]) >>
  irule immutable_word_writeback_mods >>
  qpat_assum `contract_inv _ _ _ _ _` (irule_at Any) >>
  qpat_assum `expr_sim_inv_mods _ _ _ _ _` (irule_at Any) >>
  qpat_assum `write_place _ _ _ _ = _` (irule_at Any) >>
  qpat_assum `compile_imm_store_word _ _ _ _ = _` (irule_at Any) >>
  qpat_assum `ALOOKUP cenv.ce_modules owner = SOME _` (irule_at Any) >>
  qpat_assum `ALOOKUP ee.immutables _ = SOME _` (irule_at Any) >>
  qpat_assum `FLOOKUP (get_source_immutables _ _) _ = SOME _` (irule_at Any) >>
  qpat_assum `FLOOKUP cenv.ce_module_vars _ = SOME _` (irule_at Any) >>
  qpat_assum `evaluate_type (get_tenv cx) dty = SOME _` (irule_at Any) >>
  qpat_assum `mem_path_offset _ _ = SOME _` (irule_at Any) >>
  qpat_assum `alloca_frame _ _ _ _ _ _ _` (irule_at Any) >>
  simp[] >>
  conj_tac >- (map_every qx_gen_tac [`aid`,`a`,`n`,`i`] >> disch_tac >>
               qpat_assum `!aid off sz i. FLOOKUP s0.vs_allocas aid = SOME (off,sz) /\ _ ==> i IN tn0.t_mem`
                 (qspecl_then [`aid`,`a`,`n`,`i`] mp_tac) >>
               impl_tac >- first_assum ACCEPT_TAC >> simp[]) >>
  rpt strip_tac >> qpat_assum `!H. valid_horizon _ _ H _ ==> _` (drule_then strip_assume_tac) >>
  first_assum ACCEPT_TAC
QED

Theorem imm_empty_base[local]:
  stmt_state_rel H ctx func cenv cx ee s /\ ghost_inv_at_mods D lo d cenv cx ee G tn s /\ 0 < lo ==>
  !base. cenv.ce_imm_alloca = SOME base ==>
    eval_operand base s = SOME 0w /\ op_taint tn base = {} /\ op_prov G base = NONE
Proof
  strip_tac >>
  drule_then (assume_tac o REWRITE_RULE [immutable_base_zero_def])
    stmt_state_rel_immutable_base_zero >>
  `!x. cenv.ce_imm_alloca = SOME (Var x) ==>
       FLOOKUP G x = NONE /\ op_taint tn (Var x) = {}` by fs[ghost_inv_at_mods_def] >>
  Cases >> simp[op_prov_def,op_taint_def]
QED

Theorem imm_empty_open[local]:
  compile_imm_store_word imm dst (Lit 0w) su = ((),sb) ==> ~block_is_terminated sb
Proof
  strip_tac >>
  `compile_assign_value (cenv with ce_imm_alloca := imm) dst LocCode
     (Lit 0w) T loc dty sty bytes su = ((),sb)` by
    simp[compile_assign_value_def,comp_bind_def,comp_return_def] >>
  drule_then ACCEPT_TAC immutable_assign_loccode_open
QED

Theorem imm_empty_seen_regions[local]:
  local_ptrs_reserved cenv su /\
  (!x. not_fresh_at su x ==> lookup_var x q = lookup_var x s) ==>
  !scopes name a n. local_region cenv scopes q name a n <=> local_region cenv scopes s name a n
Proof
  strip_tac >> rpt gen_tac >> irule local_region_lookup_cong >>
  rpt strip_tac >> first_x_assum irule >>
  qpat_assum `local_ptrs_reserved _ _`
    (strip_assume_tac o REWRITE_RULE [local_ptrs_reserved_def]) >>
  qpat_assum `!n1 n2 p sz1 sz2. FLOOKUP _ n1 = _ ==> _`
    (drule_then (qspecl_then [`name`,`sz`] strip_assume_tac)) >> first_assum ACCEPT_TAC
QED

Theorem imm_empty_gas_obs_frames[local]:
  (immutable_frame_mods func cenv cx (ef with gas_obs := gs) q <=>
   immutable_frame_mods func cenv cx ef q) /\
  (ghost_inv_at_mods D lo d cenv cx (ef with gas_obs := gs) Gf tf q <=>
   ghost_inv_at_mods D lo d cenv cx ef Gf tf q) /\
  (return_buf_sep d cenv (ef with gas_obs := gs) q <=> return_buf_sep d cenv ef q)
Proof
  conj_tac
  >- simp[immutable_frame_mods_def,immutables_rel_mods_def,immutable_alloca_sep_mods_def,
          immutable_alloca_sep_def,immutables_rel_def] >>
  conj_tac >- simp[ghost_inv_at_mods_def] >>
  Cases_on `d` >- simp[return_buf_sep_def] >>
  rename1 `return_buf_sep (SOME buf) _ _ _` >> Cases_on `buf` >> simp[return_buf_sep_def]
QED

Theorem qualified_place_imm_empty_mods:
  ^entry /\ ^location /\
  ALOOKUP cenv.ce_modules cenv.ce_module = SOME active_tops /\
  storage_trace_domain cx st0 ee.storage_trace /\ fn_inst_ids_distinct func /\
  has_length_word dty /\ v = default_value ptv /\
  write_place cx (ImmutablePlace owner id path) v ee = (INL (),ef) /\
  assign_place_store_code_mods cenv e NONE (dst,SOME LocCode,SOME (ValPT dty)) su = ((),sb) ==>
  ^outcome
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `compile_imm_store_word cenv.ce_imm_alloca dst (Lit 0w) su = ((),sb)` by
    fs[qualified_assign_store_code_mods,compile_store_at_loc_def] >>
  `su.cs_next_var <= sb.cs_next_var` by
    (mp_tac (Q.SPECL [`cenv.ce_imm_alloca`,`dst`,`Lit 0w`,`su`] ci_mono_compile_imm_store_word) >>
     simp[ci_mono_def]) >>
  `valid_horizon cx st0 (storage_trace_horizon ee.storage_trace) ee.storage_trace` by
    fs[storage_trace_domain_def] >>
  qpat_assum `!H. valid_horizon _ _ _ _ ==> _` (drule_then strip_assume_tac) >>
  drule_all_then strip_assume_tac immutable_region_value_layout_mods >>
  drule_then strip_assume_tac mem_path_offset_sound >>
  `32 <= type_memory_size ptv` by
    (`mem_word_at 0 (mstore 0 0w s).vs_memory = 0w` by
       simp[mem_word_at_eq_mload,mload_mstore_same] >>
     drule_all immutable_assign_empty_representation >> simp[]) >>
  `(off+k) + 32 <= lo /\ 0 < lo` by decide_tac >>
  `lo <= s.vs_alloca_next /\ allocas_from lo s` by fs[ghost_inv_at_mods_def] >>
  `lo < dimword (:256)` by
    (`s.vs_alloca_next < dimword (:256)` by
       (drule_then (ACCEPT_TAC o MATCH_MP alloca_room_next_lt) stmt_state_rel_alloca_room) >>
     decide_tac) >>
  `!base. cenv.ce_imm_alloca = SOME base ==>
      eval_operand base s = SOME 0w /\ op_taint tn base = {} /\ op_prov G base = NONE` by
    metis_tac[imm_empty_base] >>
  drule_all immutable_empty_path_store_mods >>
  disch_then (qspecl_then [`explicit`,`PG`]
    (qx_choose_then `q` (qx_choose_then `Gf` (qx_choose_then `tf` strip_assume_tac)))) >>
  qpat_x_assum `v = default_value _` SUBST_ALL_TAC >>
  `value_has_type ptv (default_value ptv)` by
    drule_then ACCEPT_TAC vyperTypeDefaultsTheory.default_value_has_type_thm >>
  `value_has_type itv old` by
    (`state_well_typed ee` by fs[expr_sim_inv_mods_def] >>
     drule_all_then assume_tac state_well_typed_immutables_ALOOKUP >>
     drule_all_then strip_assume_tac imms_well_typed_get_source_immutables >> simp[]) >>
  drule_then strip_assume_tac stmt_state_rel_local_ptrs_alloca >>
  drule_then assume_tac immutable_write_place_gas_obs >>
  drule_then (qx_choose_then `imms'` assume_tac) write_immutable_place_frame >>
  `ef.storage_trace = ee.storage_trace` by simp[] >>
  `~block_is_terminated sb` by drule_then ACCEPT_TAC imm_empty_open >>
  irule gas_outcome_full_mods_pure >> reverse conj_tac >- first_assum ACCEPT_TAC >>
  qexistsl_tac [`Gf`,`ef`,`INL ()`,`q`,`tf`] >>
  conj_tac >- first_assum ACCEPT_TAC >> qx_gen_tac `H` >> strip_tac >>
  `valid_horizon cx st0 H ee.storage_trace` by
    (qpat_assum `ef.storage_trace = ee.storage_trace` (fn th => pure_rewrite_tac[GSYM th]) >>
     first_assum ACCEPT_TAC) >>
  qpat_assum `!H. valid_horizon _ _ H _ ==> _`
    (qspec_then `H` (drule_then strip_assume_tac)) >>
  suspend "writeback"
QED

Resume qualified_place_imm_empty_mods[writeback]:
  drule_all_then (drule_all_then strip_assume_tac o MATCH_MP immutable_writeback_at_active_horizon)
    (Q.INST [`H` |-> `H`, `D` |-> `DF H`] immutable_copy_writeback_mods) >>
  qpat_assum `immutable_path_store_post _ _ _ _ _ _ _ _`
    (strip_assume_tac o REWRITE_RULE [immutable_path_store_post_def]) >>
  qpat_assum `!D. gas_origin_ptr_path _ _ _ _` (qspec_then `DF H` assume_tac) >>
  conj_tac >- first_assum ACCEPT_TAC >>
  CONV_TAC (TOP_DEPTH_CONV BETA_CONV) >>
  `storage_well_formed_on cx (ef with gas_obs := []) (FST H)` by
    (`storage_well_formed_on cx (ef with gas_obs := []) (FST H) <=>
      storage_well_formed_on cx ee (FST H)` by
       (irule storage_well_formed_on_backends >> simp[]) >>
     simp[]) >>
  `alloca_history func q` by drule_all_then ACCEPT_TAC body_full_path_alloca_history >>
  `ctx_has_dalloca ctx ==> allocas_below_fmp q` by
    (disch_tac >>
     qpat_assum `ctx_has_dalloca ctx ==> allocas_below_fmp s` (drule_then mp_tac) >>
     qpat_assum `q with <|vs_vars := _; vs_memory := _; vs_immutables := _;
       vs_prev_bb := _; vs_current_bb := _; vs_inst_idx := _|> = s`
       (strip_assume_tac o SIMP_RULE (srw_ss()) [venom_state_component_equality]) >>
     asm_rewrite_tac[allocas_below_fmp_def]) >>
  `!x. not_fresh_at su x ==> lookup_var x q = lookup_var x s` by
    (rpt strip_tac >> qpat_assum `!x. not_fresh_at su x ==> _ /\ _`
       (drule_then strip_assume_tac) >> first_assum ACCEPT_TAC) >>
  drule_all_then assume_tac imm_empty_seen_regions >>
  `!aid a n. FLOOKUP s0.vs_allocas aid = SOME (a,n) ==> lo <= a` by
    (rpt strip_tac >> qpat_assum `!aid b. FLOOKUP s0.vs_allocas aid = SOME b ==> _`
       (drule_then assume_tac) >> qpat_assum `allocas_from lo s`
       (drule_then ACCEPT_TAC o REWRITE_RULE [allocas_from_def])) >>
  suspend "allocation"
QED

Resume qualified_place_imm_empty_mods[allocation]:
  `alloca_frame cenv es sa s0 cenv (ef with gas_obs := []) q` by
    (rewrite_tac[alloca_frame_def] >> rpt gen_tac >> strip_tac >>
     qpat_assum `alloca_frame cenv es sa s0 cenv ee s`
       (drule_all_then strip_assume_tac o REWRITE_RULE [alloca_frame_def]) >>
     conj_tac
     >- (rename1 `mem_bytes_at a n q.vs_memory = _` >>
         `FLOOKUP s.vs_allocas aid = SOME (a,n)` by
           (qpat_assum `!aid b. FLOOKUP s0.vs_allocas aid = SOME b ==> _`
              (drule_then ACCEPT_TAC)) >>
         qpat_assum `!aid a n. FLOOKUP s.vs_allocas aid = SOME (a,n) ==> _`
           (drule_then (fn th => pure_rewrite_tac[th])) >> first_assum ACCEPT_TAC) >>
     simp[] >> rpt gen_tac >> disch_tac >>
     qpat_assum `!n b sz'. local_region cenv ee.scopes s n b sz' ==> _`
       (drule_then ACCEPT_TAC)) >>
  `!x. not_fresh_at sa x ==> not_fresh_at su x` by
    (rpt strip_tac >> drule_all_then ACCEPT_TAC not_fresh_at_mono) >>
  qpat_x_assum `ghost_kept_at _ _ _ _ _ _ _ _ _`
    (strip_assume_tac o REWRITE_RULE [ghost_kept_at_def]) >>
  simp[stmt_lands_def,cenv_top_ext_refl,stmt_state_rel_start_gas_obs,imm_empty_gas_obs_frames] >>
  rpt strip_tac >>
  rename1 `FLOOKUP s0.vs_allocas aid = SOME (a,n)` >>
  `lo <= a` by
    (qpat_assum `!aid a n. FLOOKUP s0.vs_allocas aid = SOME (a,n) ==> lo <= a`
       (drule_then ACCEPT_TAC)) >>
  rename1 `i IN tf.t_mem` >>
  `i IN tn.t_mem` by
    (qpat_assum `!i. ~(_ <= i /\ i < _) /\ i IN tf.t_mem ==> i IN tn.t_mem`
       (qspec_then `i` mp_tac) >>
     impl_tac >- (conj_tac >- decide_tac >> first_assum ACCEPT_TAC) >> simp[]) >>
  qpat_assum `!aid a n i. FLOOKUP s0.vs_allocas aid = SOME (a,n) /\ _ ==> i IN tn0.t_mem`
    (drule_all_then ACCEPT_TAC)
QED

Finalise qualified_place_imm_empty_mods
