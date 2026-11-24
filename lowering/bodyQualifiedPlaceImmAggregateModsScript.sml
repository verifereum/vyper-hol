(* Land the linked AssignImmCopy route using the supplied normalization and
   store endpoints; this adapter does not execute either compiler interval. *)
Theory bodyQualifiedPlaceImmAggregateMods
Ancestors
  bodyWriteImmCopyMods bodyFullPathHistory exprSimCopy gasOutcomeFullPostMods
  wordArgsPtr bodyFullUnwrapRun vyperStorageFootprint stmtSimProps stmtSimDefs
  fragGasOriginPtrLoop gasOutcomeFullZeroPrefixMods alist arithmetic
  bodyFullImmutablePathStore bodyPtrDefs gasOutcomeFullMods bodyFullPostsMods
  loweringPosts stateRelProj freshWrites ptrDiscipline bodyImmutableAugAssignExec
  vyperPlaceFrames venomState vyperState finite_map

Theorem imm_copy_alloca_frame[local]:
  alloca_frame cenv es0 sa0 s0 cenv es u /\
  (!aid ent. FLOOKUP s0.vs_allocas aid = SOME ent ==> FLOOKUP u.vs_allocas aid = SOME ent) /\
  (!aid b n. FLOOKUP u.vs_allocas aid = SOME (b,n) ==>
     mem_bytes_at b n q.vs_memory = mem_bytes_at b n u.vs_memory) /\
  (!name b n. local_region cenv ee.scopes q name b n ==>
     local_region cenv es.scopes u name b n) ==>
  alloca_frame cenv es0 sa0 s0 cenv ee q
Proof
  simp[alloca_frame_def] >> strip_tac >> rpt gen_tac >> strip_tac >>
  qpat_assum `!aid b n. FLOOKUP s0.vs_allocas aid = SOME (b,n) /\ _ ==> _`
    (drule_all_then strip_assume_tac) >>
  conj_tac
  >- (qpat_assum `!aid ent. FLOOKUP s0.vs_allocas aid = SOME ent ==> _`
        (drule_then assume_tac) >>
      qpat_assum `!aid b n. FLOOKUP u.vs_allocas aid = SOME (b,n) ==> _`
        (drule_then SUBST1_TAC) >> first_assum ACCEPT_TAC) >>
  rpt strip_tac >>
  qpat_assum `!name b n. local_region cenv ee.scopes q name b n ==> _`
    (drule_then (fn th => first_assum (fn f => ACCEPT_TAC (MATCH_MP f th))))
QED

Theorem qualified_place_imm_copy_landing_mods:
  contract_inv mods exps ctx cenv cx /\ expr_sim_inv_mods mods cenv cx env es /\
  cenv.ce_is_ctor /\ ALOOKUP cenv.ce_modules cenv.ce_module = SOME tops /\
  ALOOKUP es.immutables cx.txn.target = SOME imms /\
  FLOOKUP (get_source_immutables owner imms) id = SOME (itv,old) /\
  FLOOKUP cenv.ce_module_vars (owner,id) = SOME (ImmutableLoc off) /\
  value_has_type itv old /\ value_has_type ptv v /\
  mem_path_offset itv path = SOME (k,ptv) /\ off+k + type_memory_size ptv <= lo /\
  write_place cx (ImmutablePlace owner id path) v es = (INL (),fin) /\ es.gas_obs = [] /\
  ~s.vs_halted /\ ~block_is_terminated sb /\ fn_inst_ids_distinct func /\
  cenv_top_ext cenv0 cenv es.scopes /\
  immutable_path_store_post (lo,explicit,ctx,func,PG) (off+k) ptv v
    sm sb (u,Gu,tu) (q,Gf,tf) /\
  (!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn) [] (OK q,Gf,tf)) /\
  (!H. valid_horizon cx st0 H es.storage_trace ==>
    dead_lo_ok_mods H (DF H) lo cenv cx /\ stmt_state_rel H ctx func cenv cx es s /\
    immutable_frame_mods func cenv cx es s /\ storage_well_formed_on cx es (FST H) /\
    ghost_inv_at_mods (DF H) lo d cenv cx es G tn s) /\
  (!H : (bool # bytes32 # type_value) list # num list.
    stmt_state_rel H ctx func cenv cx es s ==> stmt_state_rel H ctx func cenv cx es u) /\
  (immutable_frame_mods func cenv cx es s ==> immutable_frame_mods func cenv cx es u) /\
  (!D d. ghost_inv_at_mods D lo d cenv cx es G tn s ==>
         ghost_inv_at_mods D lo d cenv cx es Gu tu u) /\
  return_buf_frame d cenv sm u /\ return_buf_sep d cenv es u /\
  local_ptrs_reserved cenv sm /\
  (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sm x) /\
  alloca_history func u /\ allocas_from lo u /\ (ctx_has_dalloca ctx ==> allocas_below_fmp u) /\
  sa0.cs_next_var <= sa.cs_next_var /\ sa0.cs_next_id <= sa.cs_next_id /\
  sa.cs_next_var <= sm.cs_next_var /\ sm.cs_next_var <= sb.cs_next_var /\
  s0.vs_alloca_next <= s.vs_alloca_next /\ s.vs_alloca_next <= u.vs_alloca_next /\
  (!x. not_fresh_at sa x ==> lookup_var x u = lookup_var x s) /\
  (!x w. not_fresh_at sa0 x /\ lookup_var x s0 = SOME w ==> lookup_var x s = SOME w) /\
  (!aid ent. FLOOKUP s0.vs_allocas aid = SOME ent ==> FLOOKUP s.vs_allocas aid = SOME ent) /\
  (!aid ent. FLOOKUP s.vs_allocas aid = SOME ent ==> FLOOKUP u.vs_allocas aid = SOME ent) /\
  alloca_frame cenv es0 sa0 s0 cenv es s /\ alloca_frame cenv es sa s cenv es u /\
  ghost_kept_at lo cenv es0 sa0 G0 tn0 s0 G tn /\ ghost_kept_at lo cenv es sa G tn s Gu tu /\
  (!name b n. local_region cenv es.scopes s name b n <=> local_region cenv es0.scopes s0 name b n) /\
  (!H. gas_origin_ptr_path (DF H,lo,explicit,ctx,func,PG) (z,Gz,tz) [] (OK s,G,tn)) ==>
  gas_outcome_full_mods (DF,lo,explicit,ctx,func,PG) cenv.ce_modules cx st0
    (write_place cx (ImmutablePlace owner id path) v) (es,z,Gz,tz)
    (\H res ee Gf tf q.
       res = INL () /\ stmt_lands lctx sb res q /\ ~q.vs_halted /\ ~block_is_terminated sb /\
       cenv_top_ext cenv0 cenv ee.scopes /\
       stmt_state_rel H ctx func cenv cx ee q /\ immutable_frame_mods func cenv cx ee q /\
       storage_well_formed_on cx ee (FST H) /\ return_buf_frame d cenv sb q /\
       alloca_history func q /\ return_buf_sep d cenv ee q /\
       (ctx_has_dalloca ctx ==> allocas_below_fmp q) /\ s0.vs_alloca_next <= q.vs_alloca_next /\
       ghost_inv_at_mods (DF H) lo d cenv cx ee Gf tf q /\
       (!x w. not_fresh_at sa0 x /\ lookup_var x s0 = SOME w ==> lookup_var x q = SOME w) /\
       (!aid ent. FLOOKUP s0.vs_allocas aid = SOME ent ==> FLOOKUP q.vs_allocas aid = SOME ent) /\
       (!x. not_fresh_at sa0 x ==>
         FLOOKUP Gf x = FLOOKUP G0 x /\ op_taint tf (Var x) = op_taint tn0 (Var x)) /\
       alloca_frame cenv es0 sa0 s0 cenv ee q /\
       (!aid b n i. FLOOKUP s0.vs_allocas aid = SOME (b,n) /\ aid < sa0.cs_next_id /\
          (!name a sz. local_region cenv es0.scopes s0 name a sz ==> b+n <= a \/ a+sz <= b) /\
          b <= i /\ i < b+n /\ i IN tf.t_mem ==> i IN tn0.t_mem)) R
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  irule gas_outcome_full_mods_zero_prefix >> qexistsl_tac [`G`,`s`,`tn`] >>
  conj_tac >- first_assum ACCEPT_TAC >>
  drule_then assume_tac immutable_write_place_gas_obs >>
  irule gas_outcome_full_mods_pure >> reverse conj_tac >- first_assum ACCEPT_TAC >>
  qexistsl_tac [`Gf`,`fin`,`INL ()`,`q`,`tf`] >>
  conj_tac >- first_assum ACCEPT_TAC >> qx_gen_tac `H` >> strip_tac >>
  conj_tac >- simp[] >>
  CONV_TAC (TOP_DEPTH_CONV BETA_CONV) >>
  drule_then (qx_choose_then `imms'` assume_tac) write_immutable_place_frame >>
  `fin with gas_obs := [] = fin /\ fin.storage_trace = es.storage_trace /\
   fin.scopes = es.scopes /\ fin.accounts = es.accounts /\ fin.tStorage = es.tStorage` by
    simp[evaluation_state_component_equality] >>
  qpat_assum `fin.storage_trace = es.storage_trace` (fn eq =>
    qpat_x_assum `valid_horizon _ _ _ fin.storage_trace`
      (assume_tac o PURE_REWRITE_RULE [eq])) >>
  qpat_assum `!H. valid_horizon _ _ _ _ ==> _` (drule_then strip_assume_tac) >>
  qpat_assum `!H. stmt_state_rel H _ _ _ _ _ s ==> _` (drule_then assume_tac) >>
  qpat_assum `immutable_frame_mods _ _ _ _ s ==> _` (drule_then assume_tac) >>
  qpat_assum `!D d. ghost_inv_at_mods D _ d _ _ _ _ _ s ==> _`
    (drule_then assume_tac) >>
  `local_ptrs_rel func cenv es.scopes u /\ alloca_inv u` by
    (qpat_assum `stmt_state_rel H ctx func cenv cx es u`
       (ACCEPT_TAC o MATCH_MP stmt_state_rel_local_ptrs_alloca)) >>
  drule_all_then strip_assume_tac
    (INST_TYPE [beta |-> ``:256``] immutable_copy_writeback_mods) >>
  `stmt_state_rel H ctx func cenv cx fin q` by
    (qpat_assum `!h ts. ALOOKUP cenv.ce_modules _ = SOME ts /\ _ ==> _` irule >>
     conj_tac >- (qexists_tac `tops` >> first_assum ACCEPT_TAC) >>
     first_assum ACCEPT_TAC) >>
  suspend "frames"
QED

Resume qualified_place_imm_copy_landing_mods[frames]:
  qpat_assum `immutable_path_store_post _ _ _ _ _ _ _ _`
    (strip_assume_tac o REWRITE_RULE [immutable_path_store_post_def]) >>
  `alloca_history func q` by
    (qpat_assum `!D. gas_origin_ptr_path _ (u,Gu,tu) [] (OK q,Gf,tf)`
       (qspec_then `DF H` (mp_then (Pat `gas_origin_ptr_path _ _ _ _`) irule
         body_full_path_alloca_history)) >> rpt conj_tac >> first_assum ACCEPT_TAC) >>
  `q.vs_fmp = u.vs_fmp /\ q.vs_initial_fmp = u.vs_initial_fmp` by
    (qpat_assum `q with <|vs_vars := _; vs_memory := _; vs_immutables := _;
                        vs_prev_bb := _; vs_current_bb := _; vs_inst_idx := _|> = u` mp_tac >>
     simp[venom_state_component_equality]) >>
  `ctx_has_dalloca ctx ==> allocas_below_fmp q` by
    (strip_tac >> qpat_assum `ctx_has_dalloca ctx ==> allocas_below_fmp u`
       (drule_then (assume_tac o REWRITE_RULE [allocas_below_fmp_def])) >>
     asm_rewrite_tac[allocas_below_fmp_def]) >>
  `storage_well_formed_on cx fin (FST H)` by
    (drule_all_then (fn th => simp[th]) storage_well_formed_on_backends) >>
  `!aid ent. FLOOKUP s0.vs_allocas aid = SOME ent ==> FLOOKUP u.vs_allocas aid = SOME ent` by
    (rpt strip_tac >> qpat_assum `!aid ent. FLOOKUP s.vs_allocas aid = SOME ent ==> _` irule >>
     qpat_assum `!aid ent. FLOOKUP s0.vs_allocas aid = SOME ent ==> _` irule >>
     first_assum ACCEPT_TAC) >>
  `alloca_frame cenv es0 sa0 s0 cenv es u` by
    (irule alloca_frame_trans >> qexistsl_tac [`cenv`,`es`,`s`,`sa`] >>
     rpt conj_tac >> first_assum ACCEPT_TAC) >>
  `alloca_frame cenv es0 sa0 s0 cenv fin q` by
    (irule imm_copy_alloca_frame >> qexistsl_tac [`es`,`u`] >>
     asm_rewrite_tac[] >> simp[] >> rpt strip_tac >>
     `local_region cenv es.scopes q name b n <=> local_region cenv es.scopes u name b n` by
       (irule copy_buffer_local_region_frame >> qexists_tac `sm` >>
        rpt strip_tac >>
        qpat_assum `!y. not_fresh_at sm y ==> lookup_var y q = lookup_var y u /\ _`
          (qspec_then `x` mp_tac) >> simp[]) >> gvs[]) >>
  suspend "ghost"
QED

Resume qualified_place_imm_copy_landing_mods[ghost]:
  `ghost_kept_at lo cenv es0 sa0 G0 tn0 s0 Gu tu` by
    (irule ghost_kept_at_trans >>
     rpt (first_assum (irule_at Any)) >> simp[]) >>
  `!x. not_fresh_at sa0 x ==> not_fresh_at sa x /\ not_fresh_at sm x` by
    (rpt strip_tac >- drule_all_then ACCEPT_TAC not_fresh_at_mono >>
     irule not_fresh_at_mono >> qexists_tac `sa0` >> simp[] >> decide_tac) >>
  `!x w. not_fresh_at sa0 x /\ lookup_var x s0 = SOME w ==> lookup_var x q = SOME w` by
    (rpt strip_tac >>
     qpat_assum `!x. not_fresh_at sa0 x ==> _ /\ _` (drule_then strip_assume_tac) >>
     qpat_assum `!x. not_fresh_at sm x ==> lookup_var x q = lookup_var x u /\
          FLOOKUP Gf x = FLOOKUP Gu x /\ op_taint tf (Var x) = op_taint tu (Var x)` (drule_then strip_assume_tac) >>
     qpat_assum `!x. not_fresh_at sa x ==> lookup_var x u = _` (drule_then assume_tac) >>
     qpat_assum `!x w. not_fresh_at sa0 x /\ _ ==> _` (drule_all_then assume_tac) >>
     asm_rewrite_tac[]) >>
  qpat_x_assum `ghost_kept_at _ _ _ _ _ _ _ Gu tu`
    (strip_assume_tac o REWRITE_RULE [ghost_kept_at_def]) >>
  `!x. not_fresh_at sa0 x ==> FLOOKUP Gf x = FLOOKUP G0 x /\
      op_taint tf (Var x) = op_taint tn0 (Var x)` by
    (rpt gen_tac >> strip_tac >>
     qpat_assum `!x. not_fresh_at sa0 x ==> not_fresh_at sa x /\ _`
       (drule_then strip_assume_tac) >>
     qpat_assum `!x. not_fresh_at sm x ==> lookup_var x q = lookup_var x u /\
          FLOOKUP Gf x = FLOOKUP Gu x /\ op_taint tf (Var x) = op_taint tu (Var x)` (drule_then strip_assume_tac) >>
     qpat_assum `!x. not_fresh_at sa0 x ==> FLOOKUP Gu x = _ /\ _`
       (drule_then strip_assume_tac) >> asm_rewrite_tac[]) >>
  `s0.vs_alloca_next <= q.vs_alloca_next` by decide_tac >>
  `!aid ent. FLOOKUP s0.vs_allocas aid = SOME ent ==> FLOOKUP q.vs_allocas aid = SOME ent` by
    (asm_rewrite_tac[] >> first_assum ACCEPT_TAC) >>
  qpat_assum `fin with gas_obs := [] = fin` (fn th => PURE_ONCE_REWRITE_TAC [th]) >>
  simp[stmt_lands_def] >> rpt strip_tac >>
  `FLOOKUP u.vs_allocas aid = SOME (b,n)` by
    (qpat_assum `!aid ent. FLOOKUP s0.vs_allocas aid = SOME ent ==> FLOOKUP u.vs_allocas aid = SOME ent`
       (drule_then ACCEPT_TAC)) >>
  `lo <= b` by
    (qpat_assum `allocas_from lo u`
       (drule_then ACCEPT_TAC o REWRITE_RULE [allocas_from_def])) >>
  `i IN tu.t_mem` by
    (qpat_assum `!i. ~(_ /\ _) /\ i IN tf.t_mem ==> i IN tu.t_mem` irule >>
     conj_tac >- decide_tac >> first_assum ACCEPT_TAC) >>
  qpat_assum `!aid b n i. FLOOKUP s0.vs_allocas aid = SOME (b,n) /\ _ ==> i IN tn0.t_mem`
    (drule_all_then ACCEPT_TAC)
QED

Finalise qualified_place_imm_copy_landing_mods
