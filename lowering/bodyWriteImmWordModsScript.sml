(* Word writeback at a previously selected constructor immutable place. *)
Theory bodyWriteImmWordMods
Ancestors
  bodyFullPostsMods bodyWrittenRegionFrameMods gasOutcomeFullPostMods
  immutableRegionFrameProps immutableDeployAssignMemoryFrame
  immutableDeployAssignBytes immutablePrefixDead augAssignFullImmutableDeadMask
  immutableWordStorePath bodyImmutableAugAssignExec bodyFullMemoryFrames
  bodyPtrBytestringBuiltinsWindowGhost bodyBinopFragMemory bodyMemoryDefs
  exprSimWordArgs exprSimProps stmtSimDeclStore stateRelProj exprLoweringProps
  placeMemoryPathRebuild vyperTypeEnv vyperPlaceFrames vyperTypeInitialState
  loweringPosts bodyPtrDefs immutableDeployAssignAdmissible venomState finite_map pred_set words
  fragExec rich_list compileEnv loweringStateRelDefs ptrDiscipline bodyFullShadowBodyInv
  bodyInvSplit bodyInvCodeProps fragGasOriginPtr vyperStorageFootprint vyperState
  exprSimHypsDefs valueEncodingProps valueEncodingDefs freshWrites stmtSimDefs bodySim list

Theorem immutable_word_path_encoding[local]:
  evaluate_type (get_tenv cx) ty = SOME ptv /\ is_word_type ty /\
  value_has_type ptv v /\ value_has_type itv old /\
  well_formed_type_value itv /\ mem_path_offset itv path = SOME (k,ptv) /\
  assign_subscripts itv old path (Replace v) = INL new /\
  off + type_memory_size itv <= lo /\
  (!mem. mem_agree_outside tn.t_mem s.vs_memory mem ==> val_in_memory itv old off mem) /\
  q.vs_memory = (mstore (off+k) (typed_val_to_w256 ptv v) s).vs_memory /\
  tf.t_mem = tn.t_mem DIFF {i | off+k <= i /\ i < off+k+32} ==>
  immutable_value_admissible itv new /\ val_in_memory itv new off q.vs_memory /\
  immutable_value_bytes_rel itv new (mem_bytes_at off (type_memory_size itv) q.vs_memory) /\
  (!j. off <= j /\ j < off + type_memory_size itv /\ j IN tf.t_mem ==>
       mem_dead_bytes (mem_bytes_at 0 lo q.vs_memory) off itv j)
Proof
  strip_tac >>
  drule_then strip_assume_tac mem_path_offset_sound >>
  drule_all_then assume_tac store_lays_out_typed >>
  `value_has_type itv new` by drule_all_then ACCEPT_TAC assign_subscripts_type_path_preserves_type >>
  `immutable_value_admissible itv new` by drule_all_then ACCEPT_TAC typed_immutable_admissible >>
  `!mem. mem_agree_outside tf.t_mem q.vs_memory mem ==> val_in_memory itv new off mem` by
    (mp_tac (Q.INST [`dirty` |-> `tn.t_mem`, `s` |-> `s`]
       augassign_immutable_path_robust_write) >>
     (impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)) >> simp[]) >>
  `val_in_memory itv new off q.vs_memory` by (first_assum irule >> simp[mem_agree_outside_def]) >>
  conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac >- (irule immutable_memory_bytes >> simp[]) >>
  rpt gen_tac >> strip_tac >>
  irule immutable_prefix_interior_dead >>
  rpt (conj_tac >- first_assum ACCEPT_TAC) >>
  qexistsl_tac [`tf.t_mem`, `new`] >> rpt conj_tac >> first_assum ACCEPT_TAC
QED

Theorem immutable_word_base_operand[local]:
  stmt_state_rel (H : (bool # bytes32 # type_value) list # num list) ctx func cenv cx es s /\
  ghost_inv_at_mods D lo d cenv cx es G tn s /\
  0 < lo ==>
  !base. cenv.ce_imm_alloca = SOME base ==> eval_operand base s = SOME 0w /\
    op_taint tn base = {} /\ op_prov G base = NONE
Proof
  strip_tac >>
  drule_then (assume_tac o REWRITE_RULE [immutable_base_zero_def])
    stmt_state_rel_immutable_base_zero >>
  `!x. cenv.ce_imm_alloca = SOME (Var x) ==>
       FLOOKUP G x = NONE /\ op_taint tn (Var x) = {}` by fs[ghost_inv_at_mods_def] >>
  Cases >> simp[op_prov_def,op_taint_def]
QED

Theorem immutable_word_history[local]:
  alloca_history func s /\ fn_has_code sa sb func /\
  s.vs_current_bb = sa.cs_current_bb /\ s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  sb.cs_current_bb = sa.cs_current_bb /\
  sb.cs_current_insts = sa.cs_current_insts ++ emitted_insts sa sb /\
  EVERY (\i. i.inst_opcode <> ALLOCA) (emitted_insts sa sb) /\
  u.vs_allocas = s.vs_allocas /\ u.vs_current_bb = s.vs_current_bb ==>
  alloca_history func (u with vs_inst_idx := LENGTH sb.cs_current_insts)
Proof
  strip_tac >>
  `?bb rest. lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
     DROP s.vs_inst_idx bb.bb_instructions = emitted_insts sa sb ++ rest` by
    (qpat_assum `fn_has_code _ _ _`
       (strip_assume_tac o CONJUNCT2 o REWRITE_RULE [fn_has_code_def]) >>
     qpat_assum `isPREFIX _ _` (strip_assume_tac o REWRITE_RULE [IS_PREFIX_APPEND]) >>
     qexistsl_tac [`bb`,`l`] >> simp[] >>
     qpat_assum `bb.bb_instructions = _` (fn eq => pure_rewrite_tac[eq]) >>
     qpat_assum `sb.cs_current_insts = _` (fn eq => pure_rewrite_tac[eq]) >>
     conj_tac >- (qpat_assum `sb.cs_current_bb = _` (fn eq => once_rewrite_tac[GSYM eq]) >> first_assum ACCEPT_TAC) >>
     once_rewrite_tac[GSYM APPEND_ASSOC] >>
     simp_tac std_ss [DROP_APPEND2,arithmeticTheory.LESS_EQ_REFL,
                      arithmeticTheory.SUB_EQUAL_0,DROP_0]) >>
  qpat_assum `sb.cs_current_insts = _` (fn th => once_rewrite_tac[th]) >>
  simp[LENGTH_APPEND] >>
  qpat_assum `s.vs_inst_idx = _` (fn eq => once_rewrite_tac[GSYM eq]) >>
  irule alloca_history_no_alloca_slice >>
  simp[] >> qexists_tac `rest` >>
  qpat_assum `s.vs_inst_idx = _` (fn eq => once_rewrite_tac[GSYM eq]) >>
  first_assum ACCEPT_TAC
QED

(* Use the unit frame at the active source.  Outside the module table
   there can be no constructor immutable with that owner. *)
Theorem immutable_word_active_frame[local]:
  contract_inv mods exps ctx cenv cx /\ cenv.ce_is_ctor /\
  immutable_frame_mods func cenv cx ee q ==>
  immutables_rel cenv cx.txn.target cenv.ce_module cenv.ce_is_ctor ee q /\
  immutable_alloca_sep func cenv cx ee q
Proof
  strip_tac >> Cases_on `ALOOKUP cenv.ce_modules cenv.ce_module`
  >- (`!id off. FLOOKUP cenv.ce_module_vars (cenv.ce_module,id) <> SOME (ImmutableLoc off)` by
       (rpt strip_tac >>
        drule_then (strip_assume_tac o REWRITE_RULE [immutable_section_layout_mods_def])
          contract_inv_immutable_section_layout >>
        qpat_assum `!src id off. FLOOKUP _ _ = _ <=> _`
          (drule_then strip_assume_tac o iffLR o SPEC_ALL) >>
        drule_then strip_assume_tac (iffLR immutable_region_mods_def) >>
        drule_then assume_tac contract_inv_cenv_modules >> fs[]) >>
      simp[immutables_rel_def, immutable_alloca_sep_def, immutable_decl_sep_alt]) >>
  qpat_assum `immutable_frame_mods _ _ _ _ _`
    (strip_assume_tac o REWRITE_RULE [immutable_frame_mods_def, immutables_rel_mods_def,
                                     immutable_alloca_sep_mods_def]) >>
  conj_tac
  >- (qpat_assum `!src tops. ALOOKUP _ src = SOME tops ==> immutables_rel _ _ _ _ _ _`
        (drule_then ACCEPT_TAC)) >>
  `cenv with ce_module := cenv.ce_module = cenv` by
    simp[compile_env_component_equality] >>
  qpat_assum `cenv with ce_module := cenv.ce_module = cenv` (fn eq =>
    qpat_assum `!src tops. ALOOKUP _ src = SOME tops ==> immutable_alloca_sep _ _ _ _ _`
       (drule_then (ACCEPT_TAC o PURE_REWRITE_RULE [eq])))
QED

Theorem immutable_word_writeback_mods:
  contract_inv mods exps ctx cenv cx /\ expr_sim_inv_mods mods cenv cx env es /\
  cenv.ce_is_ctor /\ ALOOKUP cenv.ce_modules owner = SOME tops /\
  ALOOKUP es.immutables cx.txn.target = SOME imms /\
  FLOOKUP (get_source_immutables owner imms) id = SOME (itv,old) /\
  FLOOKUP cenv.ce_module_vars (owner,id) = SOME (ImmutableLoc off) /\
  evaluate_type (get_tenv cx) ty = SOME ptv /\ is_word_type ty /\ value_has_type ptv v /\
  mem_path_offset itv path = SOME (k,ptv) /\
  write_place cx (ImmutablePlace owner id path) v es = (INL (),ef) /\
  compile_imm_store_word cenv.ce_imm_alloca dst op sa = ((),sb) /\
  eval_operand dst s = SOME (n2w (off+k)) /\ op_taint tn dst = {} /\ op_prov G dst = NONE /\
  eval_operand op s = SOME (typed_val_to_w256 ptv v) /\ op_taint tn op = {} /\
  (!x. op = Var x ==> not_fresh_at sa x) /\ local_ptrs_reserved cenv sa /\
  (!x cap. cenv.ce_return_buf = SOME (PtrVar (Var x) cap) ==> not_fresh_at sa x) /\
  (!x cap. cenv.ce_return_pc = SOME (PtrVar (Var x) cap) ==> not_fresh_at sa x) /\
  sa0.cs_next_var <= sa.cs_next_var /\ sa.cs_next_var <= sb.cs_next_var /\
  fn_has_code sa sb func /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\ s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  alloca_history func s /\ (ctx_has_dalloca ctx ==> allocas_below_fmp s) /\
  return_buf_frame d cenv sa s /\ return_buf_sep d cenv es s /\
  s0.vs_alloca_next <= s.vs_alloca_next /\
  (!x w. not_fresh_at sa0 x /\ lookup_var x s0 = SOME w ==> lookup_var x s = SOME w) /\
  (!aid b. FLOOKUP s0.vs_allocas aid = SOME b ==> FLOOKUP s.vs_allocas aid = SOME b) /\
  (!x. not_fresh_at sa0 x ==> FLOOKUP G x = FLOOKUP G0 x /\ op_taint tn (Var x) = op_taint tn0 (Var x)) /\
  alloca_frame c0 es0 sa0 s0 cenv es s /\
  (!aid a n i. FLOOKUP s0.vs_allocas aid = SOME (a,n) /\ aid < sa0.cs_next_id /\
    (!name b cap. local_region c0 es0.scopes s0 name b cap ==> a+n <= b \/ b+cap <= a) /\
    a <= i /\ i < a+n /\ i IN tn.t_mem ==> i IN tn0.t_mem) /\
  (!H. valid_horizon cx st0 H es.storage_trace ==>
    dead_lo_ok_mods H (DF H) lo cenv cx /\
    stmt_state_rel H ctx func cenv cx es s /\ immutable_frame_mods func cenv cx es s /\
    storage_well_formed_on cx es (FST H) /\ ghost_inv_at_mods (DF H) lo d cenv cx es G tn s) ==>
  gas_outcome_full_mods (DF,lo,explicit,ctx,func,PG) cenv.ce_modules cx st0
    (write_place cx (ImmutablePlace owner id path) v) (es,s,G,tn)
    (\H res ee Gf tf q.
       res = INL () /\ stmt_lands lctx sb res q /\ ~q.vs_halted /\ ~block_is_terminated sb /\
       cenv_top_ext cenv cenv ee.scopes /\
       stmt_state_rel H ctx func cenv cx ee q /\ immutable_frame_mods func cenv cx ee q /\
       storage_well_formed_on cx ee (FST H) /\
       return_buf_frame d cenv sb q /\ return_buf_sep d cenv ee q /\
       alloca_history func q /\ (ctx_has_dalloca ctx ==> allocas_below_fmp q) /\
       s0.vs_alloca_next <= q.vs_alloca_next /\ ghost_inv_at_mods (DF H) lo d cenv cx ee Gf tf q /\
       (!x w. not_fresh_at sa0 x /\ lookup_var x s0 = SOME w ==> lookup_var x q = SOME w) /\
       (!aid b. FLOOKUP s0.vs_allocas aid = SOME b ==> FLOOKUP q.vs_allocas aid = SOME b) /\
       (!x. not_fresh_at sa0 x ==> FLOOKUP Gf x = FLOOKUP G0 x /\ op_taint tf (Var x) = op_taint tn0 (Var x)) /\
       alloca_frame c0 es0 sa0 s0 cenv ee q /\
       (!aid a n i. FLOOKUP s0.vs_allocas aid = SOME (a,n) /\ aid < sa0.cs_next_id /\
        (!name b cap. local_region c0 es0.scopes s0 name b cap ==> a+n <= b \/ b+cap <= a) /\
        a <= i /\ i < a+n /\ i IN tf.t_mem ==> i IN tn0.t_mem)) R
Proof
  strip_tac >>
  drule_all_then strip_assume_tac immutable_path_write_source >>
  qpat_assum `write_place _ _ _ _ = _` (strip_assume_tac o MATCH_MP write_immutable_place_frame) >>
  `ef.storage_trace = es.storage_trace` by simp[] >>
  drule_then assume_tac immutable_write_place_gas_obs >>
  reverse (Cases_on `storage_trace_domain cx st0 es.storage_trace`)
  >- (irule gas_outcome_full_mods_bad_nil >> simp[]) >>
  `valid_horizon cx st0 (storage_trace_horizon es.storage_trace) es.storage_trace` by
    fs[storage_trace_domain_def] >>
  qpat_assum `!H. valid_horizon _ _ _ _ ==> _` (drule_then strip_assume_tac) >>
  drule_all_then strip_assume_tac immutable_region_value_layout_mods >>
  drule_then strip_assume_tac mem_path_offset_sound >>
  `type_memory_size ptv = 32` by drule_all_then ACCEPT_TAC word_tv_memory_size >>
  `w2n (n2w (off+k) : bytes32) = off+k` by
    (`s.vs_alloca_next < dimword (:256)` by
       (drule_then (ACCEPT_TAC o MATCH_MP alloca_room_next_lt) stmt_state_rel_alloca_room) >>
     `lo <= s.vs_alloca_next` by fs[ghost_inv_at_mods_def] >>
     simp[w2n_n2w] >> irule arithmeticTheory.LESS_MOD >> decide_tac) >>
  `w2n (n2w (off+k) : bytes32) + 32 <= lo /\ 0 < lo` by simp[] >>
  `allocas_from lo s /\ lo <= s.vs_alloca_next` by fs[ghost_inv_at_mods_def] >>
  `!base. cenv.ce_imm_alloca = SOME base ==> eval_operand base s = SOME 0w /\
    op_taint tn base = {} /\ op_prov G base = NONE` by
    (mp_tac (Q.INST [`H` |-> `storage_trace_horizon es.storage_trace`,
                    `D` |-> `DF (storage_trace_horizon es.storage_trace)`]
       immutable_word_base_operand) >> simp[]) >>
  suspend "execute"
QED

Resume immutable_word_writeback_mods[execute]:
  drule_all immutable_word_store_path_clean >>
  disch_then (qspecl_then [`explicit`,`PG`] strip_assume_tac) >>
  qabbrev_tac `q = u with vs_inst_idx := LENGTH sb.cs_current_insts` >>
  `q.vs_halted = s.vs_halted /\ q.vs_current_bb = s.vs_current_bb /\
   q.vs_allocas = s.vs_allocas /\ q.vs_alloca_next = s.vs_alloca_next /\
   q.vs_memory = (mstore (off+k) (typed_val_to_w256 ptv v) s).vs_memory /\
   q.vs_fmp = s.vs_fmp /\ q.vs_initial_fmp = s.vs_initial_fmp /\
   q.vs_call_ctx = s.vs_call_ctx /\ q.vs_tx_ctx = s.vs_tx_ctx /\
   q.vs_block_ctx = s.vs_block_ctx /\ q.vs_accounts = s.vs_accounts /\
   q.vs_transient = s.vs_transient /\ q.vs_logs = s.vs_logs /\
   q.vs_outcomes = s.vs_outcomes /\ q.vs_requests = s.vs_requests /\
   q.vs_pending_deletions = s.vs_pending_deletions /\ q.vs_labels = s.vs_labels /\
   q.vs_data_section = s.vs_data_section /\ q.vs_code = s.vs_code` by
    (qpat_assum `u with <|vs_vars := _; vs_memory := _; vs_immutables := _|> = s` mp_tac >>
     simp[Abbr `q`,venom_state_component_equality]) >>
  `!x. not_fresh_at sa x ==> lookup_var x q = lookup_var x s` by
    (unabbrev_all_tac >> pure_rewrite_tac[blockPrefixEquivTheory.lookup_var_set_inst_idx] >>
     first_assum ACCEPT_TAC) >>
  `alloca_history func q` by
    (qunabbrev_tac `q` >> irule immutable_word_history >>
     qexistsl_tac [`s`,`sa`] >>
     qpat_assum `u with <|vs_vars := _; vs_memory := _; vs_immutables := _|> = s` mp_tac >>
     simp[venom_state_component_equality]) >>
  `tf.t_mem = tn.t_mem DIFF {i | off+k <= i /\ i < off+k+32}` by simp[] >>
  `tf.t_mem SUBSET tn.t_mem` by simp[SUBSET_DEF,IN_DIFF] >>
  `mem_agree_outside {i | off+k <= i /\ i < off+k+32} s.vs_memory q.vs_memory` by
    (simp[mem_agree_outside_def] >> rpt strip_tac >> sym_tac >>
     irule mstore_mem_bytes_at_disjoint >> decide_tac) >>
  irule gas_outcome_full_mods_pure >> reverse conj_tac >- first_assum ACCEPT_TAC >>
  qexistsl_tac [`Gf`,`ef`,`INL ()`,`q`,`tf`] >>
  conj_tac >- first_assum ACCEPT_TAC >> qx_gen_tac `H` >> strip_tac >>
  conj_tac >- simp[Abbr `q`] >> suspend "frame"
QED

Resume immutable_word_writeback_mods[frame]:
  CONV_TAC (TOP_DEPTH_CONV BETA_CONV) >>
  qabbrev_tac `ee = ef with gas_obs := []` >>
  `ee.scopes = es.scopes /\ ee.accounts = es.accounts /\ ee.tStorage = es.tStorage /\
   ee.logs = es.logs /\ ee.outcomes = es.outcomes /\ ee.requests = es.requests /\
   ee.pending_deletions = es.pending_deletions /\
   ALOOKUP ee.immutables cx.txn.target = SOME (update_immutable owner id itv new imms)` by
    (qpat_assum `ef = es with immutables := (cx.txn.target,_)::_`
       (fn th => simp_tac (srw_ss()) [Abbr `ee`,th])) >>
  `valid_horizon cx st0 H es.storage_trace` by
    (qpat_assum `ef.storage_trace = es.storage_trace` (fn eq => pure_rewrite_tac[GSYM eq]) >>
     first_assum ACCEPT_TAC) >>
  qpat_assum `!H. valid_horizon _ _ _ _ ==> _`
    (qspec_then `H` (drule_then strip_assume_tac)) >>
  `value_has_type itv old` by
    (`state_well_typed es` by fs[expr_sim_inv_mods_def] >>
     drule_all_then assume_tac state_well_typed_immutables_ALOOKUP >>
     drule_all_then strip_assume_tac imms_well_typed_get_source_immutables >> simp[]) >>
  `!mem. mem_agree_outside tn.t_mem s.vs_memory mem ==> val_in_memory itv old off mem` by
    (`immutables_rel_mods cenv cx.txn.target cenv.ce_is_ctor es s` by fs[immutable_frame_mods_def] >>
     mp_tac (Q.INST [`entry` |-> `es`, `H` |-> `H`, `D` |-> `DF H`,
        `src` |-> `owner`, `rt` |-> `itv`, `v` |-> `old`]
        (INST_TYPE [alpha |-> ``:256``] qualified_immutable_ctor_frame_mods)) >>
     simp[]) >>
  mp_tac (Q.INST [`q` |-> `q`,`tf` |-> `tf`] immutable_word_path_encoding) >>
  (impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)) >> strip_tac >>
  `!name b n. local_region cenv ee.scopes q name b n <=> local_region cenv es.scopes s name b n` by
    (simp[] >> rpt gen_tac >> irule local_region_lookup_cong >> rpt strip_tac >>
     qpat_assum `!x. not_fresh_at sa x ==> lookup_var x q = _` irule >>
     qpat_assum `local_ptrs_reserved cenv sa`
       (strip_assume_tac o REWRITE_RULE [local_ptrs_reserved_def]) >>
     qpat_assum `!n1 n2 p sz1 sz2. FLOOKUP _ n1 = _ ==> _`
       (drule_then strip_assume_tac) >> simp[]) >>
  `!i. i < lo /\ i IN tn.t_mem ==> imm_section_dead_mods cenv (mem_bytes_at 0 lo s.vs_memory) i` by
    fs[ghost_inv_at_mods_def] >>
  mp_tac (Q.INST [`H` |-> `H`, `D` |-> `DF H`, `tv` |-> `itv`, `v` |-> `new`,
      `dest` |-> `off+k`, `bytes` |-> `32`, `t` |-> `q`, `M1` |-> `tn.t_mem`, `M2` |-> `tf.t_mem`]
      (INST_TYPE [alpha |-> ``:256``] written_region_frame_mods)) >>
  (impl_tac >- (simp[] >> rpt conj_tac >> rpt strip_tac >> fs[SUBSET_DEF] >> decide_tac)) >>
  strip_tac >>
  `!a n. 0 < n /\ lo <= a ==>
    mem_bytes_at a n q.vs_memory = mem_bytes_at a n s.vs_memory` by
    (rpt strip_tac >> simp[] >> irule mstore_mem_bytes_at_disjoint >> decide_tac) >>
  `!n a len. local_region cenv es.scopes s n a len ==>
    mem_bytes_at a len q.vs_memory = mem_bytes_at a len s.vs_memory` by
    (rpt strip_tac >> Cases_on `len = 0` >- simp[mem_bytes_at_def] >>
     first_assum irule >> conj_tac >- decide_tac >>
     `immutable_decl_sep_mods cenv cx es.scopes s.vs_vars s.vs_allocas s.vs_alloca_next` by
       (rewrite_tac[immutable_decl_sep_mods_def] >> rpt strip_tac >>
        qpat_assum `immutable_frame_mods func cenv cx es s`
          (strip_assume_tac o REWRITE_RULE [immutable_frame_mods_def,immutable_alloca_sep_mods_def]) >>
        qpat_assum `!src tops. ALOOKUP cenv.ce_modules src = SOME tops ==> immutable_alloca_sep _ _ _ _ _`
          (drule_then (strip_assume_tac o REWRITE_RULE [immutable_alloca_sep_def])) >>
        first_assum ACCEPT_TAC) >>
     irule (INST_TYPE [alpha |-> ``:256``] body_full_local_region_lower_bound_mods) >>
     rpt (first_assum (irule_at Any)) >> simp[] >> decide_tac) >>
  suspend "state"
QED

Resume immutable_word_writeback_mods[state]:
  `!name p sz. FLOOKUP cenv.ce_vars name = SOME (PtrVar (Var p) sz) ==>
    not_fresh_at sa p` by
    (rpt strip_tac >>
     qpat_assum `local_ptrs_reserved cenv sa`
       (strip_assume_tac o REWRITE_RULE [local_ptrs_reserved_def]) >>
     qpat_assum `!n1 n2 p sz1 sz2. FLOOKUP _ n1 = _ ==> _`
       (drule_then strip_assume_tac) >> simp[]) >>
  `local_ptrs_rel func cenv es.scopes s` by
    fs[stmt_state_rel_def,state_rel_def] >>
  `local_ptrs_rel func cenv ee.scopes q` by
    (qpat_assum `ee.scopes = _` (fn th => pure_rewrite_tac [th]) >>
     irule localPtrsPropsTheory.local_ptrs_rel_mem_agree >> qexists_tac `s` >>
     conj_tac
     >- (rpt strip_tac >> sym_tac >>
         qpat_assum `!n a len. local_region cenv es.scopes s n a len ==> _`
           (drule_then ACCEPT_TAC)) >>
     conj_tac
     >- (rpt strip_tac >>
         qpat_assum `!x. not_fresh_at sa x ==> lookup_var x q = _` irule >>
         qpat_assum `!name p sz. FLOOKUP cenv.ce_vars name = SOME (PtrVar (Var p) sz) ==> _`
           (drule_then ACCEPT_TAC)) >>
     conj_tac >- (simp[] >> rpt gen_tac >> Cases_on `FLOOKUP s.vs_allocas aid` >> simp[]) >>
     simp[] >> fs[stmt_state_rel_def,state_rel_def]) >>
  `LENGTH s.vs_memory <= LENGTH q.vs_memory` by
    simp[venomMemPropsTheory.mstore_memory_nondecreasing] >>
  `immutables_rel cenv cx.txn.target cenv.ce_module cenv.ce_is_ctor ee q /\
   immutable_alloca_sep func cenv cx ee q` by
    drule_all_then ACCEPT_TAC immutable_word_active_frame >>
  `immutable_base_zero cenv q` by
    (irule immutable_base_zero_frame >> qexists_tac `s` >>
     conj_tac
     >- (rpt strip_tac >>
         qpat_assum `!x. not_fresh_at sa x ==> lookup_var x q = _` irule >>
         qpat_assum `local_ptrs_reserved cenv sa`
           (strip_assume_tac o REWRITE_RULE [local_ptrs_reserved_def]) >>
         qpat_assum `!x. cenv.ce_imm_alloca = SOME (Var x) ==> _`
           (drule_then strip_assume_tac) >> simp[]) >>
     simp[] >> drule_then ACCEPT_TAC stmt_state_rel_immutable_base_zero) >>
  `state_rel H func cenv cx ee q` by
    (qpat_assum `stmt_state_rel H ctx func cenv cx es s`
       (strip_assume_tac o REWRITE_RULE [stmt_state_rel_def,state_rel_def]) >>
     simp[state_rel_def, storage_rel_def, transient_rel_def, accounts_rel_def,
          logs_rel_def, contract_storage_def, contract_transient_def] >>
     fs[storage_rel_def, transient_rel_def, accounts_rel_def,
        logs_rel_def, contract_storage_def, contract_transient_def]) >>
  `stmt_state_rel H ctx func cenv cx ee q` by
    (irule stmt_state_rel_allocas_frame >> simp[] >>
     qexistsl_tac [`es`,`s`] >> simp[venomMemPropsTheory.mstore_memory_nondecreasing]) >>
  suspend "ghost"
QED

Resume immutable_word_writeback_mods[ghost]:
  `stor_taint_ok_at (DF H) tf q` by
    (`!(im : num |-> bytes32). (DF H).d_imm im = UNIV` by fs[dead_lo_ok_mods_def] >>
     qpat_assum `ghost_inv_at_mods (DF H) lo d cenv cx es G tn s`
       (strip_assume_tac o REWRITE_RULE [ghost_inv_at_mods_def]) >>
     fs[stor_taint_ok_at_def]) >>
  `ghost_inv_at (DF H) 0 d cenv cx es G tn s` by
    (qpat_assum `ghost_inv_at_mods (DF H) lo d cenv cx es G tn s`
       (strip_assume_tac o REWRITE_RULE [ghost_inv_at_mods_def]) >>
     simp_tac (srw_ss()) [ghost_inv_at_def,allocas_from_def] >>
     rpt conj_tac >> first_assum ACCEPT_TAC) >>
  (* Reuse the local-window transport on the empty prefix; then restore the
     linked immutable deadness on the real prefix of length lo. *)
  `ghost_inv_at (DF H) 0 d cenv cx ee Gf tf q` by
    (irule ghost_inv_at_local_window_transport >>
     qpat_assum `ghost_inv_at (DF H) 0 d cenv cx es G tn s` (irule_at Any) >>
     qpat_assum `local_ptrs_reserved cenv sa` (irule_at Any) >>
     qpat_assum `local_ptrs_rel func cenv es.scopes s` (irule_at Any) >>
     `mem_bytes_at 0 0 q.vs_memory = mem_bytes_at 0 0 s.vs_memory` by simp[mem_bytes_at_def] >>
     qpat_x_assum `q.vs_memory = _` kall_tac >>
     simp[allocas_from_def] >>
     first_assum ACCEPT_TAC) >>
  `ghost_inv_at_mods (DF H) lo d cenv cx ee Gf tf q` by
    (qpat_assum `ghost_inv_at (DF H) 0 d cenv cx ee Gf tf q`
       (strip_assume_tac o REWRITE_RULE [ghost_inv_at_def]) >>
     `!x. lo <> 0 /\ cenv.ce_imm_alloca = SOME (Var x) ==>
         FLOOKUP Gf x = NONE /\ op_taint tf (Var x) = {}` by
       (rpt strip_tac >>
        `not_fresh_at sa x` by
          (qpat_assum `local_ptrs_reserved cenv sa`
             (strip_assume_tac o REWRITE_RULE [local_ptrs_reserved_def]) >>
           qpat_assum `!x. cenv.ce_imm_alloca = SOME (Var x) ==> _`
             (drule_then strip_assume_tac) >> simp[]) >>
        qpat_assum `ghost_inv_at_mods (DF H) lo d cenv cx es G tn s`
          (strip_assume_tac o REWRITE_RULE [ghost_inv_at_mods_def]) >>
        simp[]) >>
     `allocas_from lo q /\ lo <= q.vs_alloca_next` by
       (fs[allocas_from_def] >> first_assum ACCEPT_TAC) >>
     pure_rewrite_tac [ghost_inv_at_mods_def] >> rpt conj_tac >> first_assum ACCEPT_TAC) >>
  suspend "caller"
QED

Resume immutable_word_writeback_mods[caller]:
  `return_buf_frame d cenv sb q` by
    (irule return_buf_frame_frame >>
     qpat_assum `return_buf_frame d cenv sa s` (irule_at Any) >>
     simp[] >> rpt strip_tac >> simp[]) >>
  `return_buf_sep d cenv ee q` by
    (Cases_on `d` >- simp[bodySimFullTheory.return_buf_sep_def] >>
     rename1 `return_buf_sep (SOME ret) _ _ _` >> PairCases_on `ret` >>
     fs[bodySimFullTheory.return_buf_sep_def,allocas_from_def] >>
     rpt conj_tac >> first_assum ACCEPT_TAC) >>
  `alloca_frame c0 es0 sa0 s0 cenv ee q` by
    (simp_tac (srw_ss()) [alloca_frame_def] >> rpt gen_tac >> strip_tac >>
     qpat_assum `alloca_frame c0 es0 sa0 s0 cenv es s`
       (drule_all_then strip_assume_tac o REWRITE_RULE [alloca_frame_def]) >>
     conj_tac
     >- (`mem_bytes_at off' sz q.vs_memory = mem_bytes_at off' sz s.vs_memory` suffices_by fs[] >>
         Cases_on `sz = 0` >- simp[mem_bytes_at_def] >>
         qpat_assum `!a n. 0 < n /\ lo <= a ==> _` irule >>
         `FLOOKUP s.vs_allocas aid = SOME (off',sz)` by
           (qpat_assum `!aid b. FLOOKUP s0.vs_allocas aid = SOME b ==> _`
              (drule_then ACCEPT_TAC)) >>
         conj_tac >- decide_tac >>
         qpat_assum `allocas_from lo s`
           (drule_then ACCEPT_TAC o REWRITE_RULE [allocas_from_def])) >>
     rpt gen_tac >> disch_tac >>
     `local_region cenv es.scopes s n b sz'` by
       (qpat_assum `!name b n. local_region cenv ee.scopes q name b n <=> _`
          (fn th => pure_rewrite_tac [GSYM th]) >> first_assum ACCEPT_TAC) >>
     qpat_assum `!n b sz'. local_region cenv es.scopes s n b sz' ==> _`
       (drule_then ACCEPT_TAC)) >>
  `!x. not_fresh_at sa0 x ==> not_fresh_at sa x` by
    (rpt strip_tac >> drule_all_then ACCEPT_TAC freshWritesTheory.not_fresh_at_mono) >>
  `storage_well_formed_on cx ee (FST H)` by
    (`storage_well_formed_on cx ee (FST H) <=> storage_well_formed_on cx es (FST H)` by
       (irule storage_well_formed_on_backends >> simp[]) >> simp[]) >>
  `ctx_has_dalloca ctx ==> allocas_below_fmp q` by
    (strip_tac >> qpat_assum `ctx_has_dalloca ctx ==> allocas_below_fmp u`
      (drule_then mp_tac) >> simp_tac (srw_ss()) [allocas_below_fmp_def,Abbr `q`] >>
     strip_tac >> first_assum ACCEPT_TAC) >>
  `q.vs_inst_idx = LENGTH sb.cs_current_insts` by simp[Abbr `q`] >>
  simp[stmt_lands_def,stmtSimPropsTheory.cenv_top_ext_refl] >>
  rpt gen_tac >> strip_tac >>
  qpat_assum `!aid a n i. FLOOKUP s0.vs_allocas aid = SOME (a,n) /\ _ ==> i IN tn0.t_mem`
    (drule_all_then ACCEPT_TAC)
QED

Finalise immutable_word_writeback_mods
