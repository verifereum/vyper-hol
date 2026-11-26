(* Frame of the caller after the selected INVOKE's register-result stores. *)
Theory bodySelectedStoredCallerFrameMods
Ancestors
  bodyIfExpTypedImmFrameMods bodyFullPostsMods bodyFullShadowBodyInv bodyInvSplit
  bodyPtrMakeArrayMemoryFrame intCallResult allocaHistoryFragment allocaHistory
  stateRelProj exprSimProps exprLoweringProps loweringStateRelDefs
  typedMemoryCopy loweringPosts bodyPtrDefs ptrDiscipline freshWrites
  compileEnv venomState venomMemDefs vyperState finite_map list

Theorem stored_covers[local]:
  ptr_covers J N p a sz /\ lookup_var p stored = lookup_var p a /\
  FLOOKUP Gs p = FLOOKUP J p /\ op_taint ts (Var p) = op_taint N (Var p) ==>
  ptr_covers Gs ts p stored sz
Proof
  simp[ptr_covers_def] >> rpt strip_tac >> simp[] >> metis_tac[]
QED

Theorem stored_local_value[local]:
  local_ptrs_rel func ce ee.scopes a /\
  lookup_scopes name ee.scopes = SOME entry /\
  FLOOKUP ce.ce_vars name = SOME (PtrVar (Var p) sz) /\
  (!w mem. lookup_var p a = SOME w /\ mem_agree_outside N.t_mem a.vs_memory mem ==>
    val_in_memory entry.type entry.value (w2n w) mem) /\
  lookup_var p stored = lookup_var p a /\
  (!n b cap. local_region ce ee.scopes a n b cap ==>
    mem_bytes_at b cap stored.vs_memory = mem_bytes_at b cap a.vs_memory) /\
  ts.t_mem SUBSET N.t_mem ==>
  !w mem. lookup_var p stored = SOME w /\ mem_agree_outside ts.t_mem stored.vs_memory mem ==>
    val_in_memory entry.type entry.value (w2n w) mem
Proof
  strip_tac >> rpt gen_tac >> strip_tac >>
  `lookup_var p a = SOME w` by fs[] >>
  `local_region ce ee.scopes a name (w2n w) sz` by simp[local_region_def] >>
  `val_wf entry.type entry.value /\ type_memory_size entry.type <= sz` by
    (fs[local_ptrs_rel_def] >> qpat_x_assum `!n e p sz. _ ==> ?w. _` drule_all >>
     strip_tac >> gvs[]) >>
  `val_footprint entry.type entry.value <= sz` by
    (drule exprSimPropsTheory.val_footprint_le >> simp[]) >>
  irule robust_val_in_memory_shrinking_frame >> simp[] >>
  qexistsl_tac [`N.t_mem`,`ts.t_mem`,`a.vs_memory`,`stored.vs_memory`,`sz`] >>
  fs[pred_setTheory.SUBSET_DEF] >> metis_tac[]
QED

Theorem stored_ghost[local]:
  ghost_inv_at_mods D lo d ce cx ee J N a /\ local_ptrs_rel func ce ee.scopes a /\
  local_ptrs_reserved ce k /\
  (!x sz. ce.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at k x) /\
  (!x sz. ce.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at k x) /\
  (!x. not_fresh_at k x ==> lookup_var x stored = lookup_var x a /\
    FLOOKUP Gs x = FLOOKUP J x /\ op_taint ts (Var x) = op_taint N (Var x)) /\
  (!n b cap. local_region ce ee.scopes a n b cap ==>
    mem_bytes_at b cap stored.vs_memory = mem_bytes_at b cap a.vs_memory) /\
  mem_bytes_at 0 lo stored.vs_memory = mem_bytes_at 0 lo a.vs_memory /\
  ts.t_mem SUBSET N.t_mem /\ ts.t_stor = N.t_stor /\ ts.t_trans = N.t_trans /\ ts.t_imm = N.t_imm /\
  (stored with <|vs_vars := a.vs_vars; vs_memory := a.vs_memory|>) = a ==>
  ghost_inv_at_mods D lo d ce cx ee Gs ts stored
Proof
  simp[ghost_inv_at_mods_def] >> strip_tac >>
  conj_tac >- suspend "locals" >>
  conj_tac >- suspend "buffer" >>
  conj_tac >- suspend "storage" >>
  conj_tac >- (fs[pred_setTheory.SUBSET_DEF] >> metis_tac[]) >>
  conj_tac >- (rpt strip_tac >> `not_fresh_at k x` by metis_tac[local_ptrs_reserved_def] >> metis_tac[]) >>
  qpat_assum `stored with <|vs_memory := _; vs_vars := _|> = _`
    (mp_tac o Q.AP_TERM `\s:venom_state. (s.vs_allocas,s.vs_alloca_next)`) >>
  simp[] >> strip_tac >> fs[allocas_from_def] >> first_assum ACCEPT_TAC
QED
Resume stored_ghost[locals]:
  rpt gen_tac >> strip_tac >>
  `not_fresh_at k p` by metis_tac[local_ptrs_reserved_def] >>
  qpat_assum `!x. not_fresh_at k x ==> _` drule >> strip_tac >>
  qpat_assum `!name entry p sz. _ ==> ptr_covers _ _ _ _ _ /\ _` drule_all >> strip_tac >>
  conj_tac >- (irule stored_covers >> simp[] >> metis_tac[]) >>
  match_mp_tac stored_local_value >>
  goal_assum (drule_at (Pat `local_ptrs_rel _ _ _ _`)) >>
  simp[] >> first_assum ACCEPT_TAC
QED
Resume stored_ghost[buffer]:
  Cases_on `d` >- simp[return_buf_ptr_def] >> PairCases_on `x` >>
  fs[return_buf_ptr_def] >>
  `not_fresh_at k x` by metis_tac[] >>
  qpat_assum `!x. not_fresh_at k x ==> _` drule >> strip_tac >>
  drule_all stored_covers >> simp[]
QED
Resume stored_ghost[storage]:
  qpat_assum `stored with <|vs_memory := _; vs_vars := _|> = _`
    (mp_tac o Q.AP_TERM `\s:venom_state. (s.vs_accounts,s.vs_transient,s.vs_immutables,s.vs_call_ctx)`) >>
  simp[] >> strip_tac >> fs[stor_taint_ok_at_def]
QED
Finalise stored_ghost[local]

(* The input a is the advanced caller cursor (the raw merge with only its
   instruction index changed).  No premise describes a returned word. *)
Theorem selected_stored_caller_frame_mods:
  stmt_state_rel H ctx func ce cx ee a /\ immutable_frame_mods func ce cx ee a /\
  storage_well_formed_on cx ee (FST H) /\ ALOOKUP ce.ce_modules ce.ce_module = SOME tops /\
  ghost_inv_at_mods (DF H) lo d ce cx ee J N a /\
  ghost_kept_at lo ce es0 sa G0 tn0 s0 J N /\ locals_kept ce es0 ee s0 a /\
  (!x w. not_fresh_at sa x /\ lookup_var x s0 = SOME w ==> lookup_var x a = SOME w) /\
  (!aid b. FLOOKUP s0.vs_allocas aid = SOME b ==> FLOOKUP a.vs_allocas aid = SOME b) /\
  (!aid b sz. FLOOKUP s0.vs_allocas aid = SOME (b,sz) /\ aid < sa.cs_next_id /\
    (!n lb lsz. local_region ce es0.scopes s0 n lb lsz ==> b + sz <= lb \/ lb + lsz <= b) ==>
    mem_bytes_at b sz a.vs_memory = mem_bytes_at b sz s0.vs_memory) /\
  local_ptrs_reserved ce sa /\ sa.cs_next_var <= st4.cs_next_var /\
  (!x sz. ce.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!x sz. ce.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  MEM ai (fn_insts func) /\ ai.inst_opcode = ALLOCA /\ ai.inst_id = sa.cs_next_id /\
  FLOOKUP a.vs_allocas sa.cs_next_id = SOME (off,cap:num) /\ lo <= off /\
  (!n b sz. local_region ce ee.scopes a n b sz ==> b + sz <= off \/ off + cap <= b) /\
  alloca_history func a /\ fn_inst_ids_distinct func /\
  (ctx_has_dalloca ctx ==> allocas_below_fmp a) /\ s0.vs_alloca_next <= a.vs_alloca_next /\
  a.vs_current_bb = st4.cs_current_bb /\ a.vs_inst_idx = LENGTH st4.cs_current_insts /\
  fn_has_code st4 sm func /\ store_multi_results buf ops k st4 = ((),sm) /\
  run_inst_seq (emitted_insts st4 sm) a = OK stored /\
  (stored with <|vs_vars := a.vs_vars; vs_memory := a.vs_memory|>) = a /\
  (!x. not_fresh_at st4 x ==> lookup_var x stored = lookup_var x a /\
    FLOOKUP Gs x = FLOOKUP J x /\ op_taint ts (Var x) = op_taint N (Var x)) /\
  ts.t_mem = N.t_mem DIFF {i | off <= i /\ i < off + cap} /\
  ts.t_stor = N.t_stor /\ ts.t_trans = N.t_trans /\ ts.t_imm = N.t_imm /\
  (!b sz. b + sz <= off \/ off + cap <= b ==>
    mem_bytes_at b sz stored.vs_memory = mem_bytes_at b sz a.vs_memory) ==>
  let z = stored with vs_inst_idx := LENGTH sm.cs_current_insts in
  stmt_state_rel H ctx func ce cx ee z /\ immutable_frame_mods func ce cx ee z /\
  storage_well_formed_on cx ee (FST H) /\ ghost_inv_at_mods (DF H) lo d ce cx ee Gs ts z /\
  ghost_kept_at lo ce es0 sa G0 tn0 s0 Gs ts /\ locals_kept ce es0 ee s0 z /\
  (!x w. not_fresh_at sa x /\ lookup_var x s0 = SOME w ==> lookup_var x z = SOME w) /\
  (!aid b. FLOOKUP s0.vs_allocas aid = SOME b ==> FLOOKUP z.vs_allocas aid = SOME b) /\
  (!aid b sz. FLOOKUP s0.vs_allocas aid = SOME (b,sz) /\ aid < sa.cs_next_id /\
    (!n lb lsz. local_region ce es0.scopes s0 n lb lsz ==> b + sz <= lb \/ lb + lsz <= b) ==>
    mem_bytes_at b sz z.vs_memory = mem_bytes_at b sz s0.vs_memory) /\
  z.vs_current_bb = sm.cs_current_bb /\ z.vs_inst_idx = LENGTH sm.cs_current_insts /\
  alloca_history func z /\ (ctx_has_dalloca ctx ==> allocas_below_fmp z) /\
  s0.vs_alloca_next <= z.vs_alloca_next
Proof
  strip_tac >> simp[stmt_state_rel_inst_idx, lookup_var_def] >>
  drule stmt_state_rel_local_ptrs_alloca >> strip_tac >>
  drule run_inst_seq_memory_length >> strip_tac >>
  drule store_multi_results_shape >> strip_tac >>
  `sm.cs_current_bb = st4.cs_current_bb` by fs[same_blocks_def] >>
  `stored.vs_allocas = a.vs_allocas /\ stored.vs_alloca_next = a.vs_alloca_next /\
   stored.vs_initial_fmp = a.vs_initial_fmp /\ stored.vs_fmp = a.vs_fmp /\
   stored.vs_current_bb = a.vs_current_bb` by
    (qpat_assum `stored with <|vs_vars := _; vs_memory := _|> = _` mp_tac >>
     simp[venom_state_component_equality]) >>
  `!x. not_fresh_at sa x ==> lookup_var x stored = lookup_var x a /\
    FLOOKUP Gs x = FLOOKUP J x /\ op_taint ts (Var x) = op_taint N (Var x)` by
    (rpt strip_tac >> `not_fresh_at st4 x` by metis_tac[freshWritesTheory.not_fresh_at_mono] >> fs[]) >>
  `!n b sz. local_region ce ee.scopes a n b sz ==>
    mem_bytes_at b sz stored.vs_memory = mem_bytes_at b sz a.vs_memory` by
    (rpt gen_tac >> strip_tac >> first_x_assum irule >> metis_tac[]) >>
  `immutable_frame_mods func ce cx ee stored` by suspend "immutable" >>
  `ghost_inv_at_mods (DF H) lo d ce cx ee Gs ts stored` by suspend "ghost" >>
  conj_tac >- suspend "physical" >>
  conj_tac >- suspend "immutable_cursor" >>
  simp[] >> conj_tac >- suspend "ghost_cursor" >>
  conj_tac >- suspend "kept" >>
  conj_tac >- suspend "locals" >>
  conj_tac >- (simp[GSYM lookup_var_def] >> rpt strip_tac >> metis_tac[]) >>
  conj_tac >- suspend "old_bytes" >>
  conj_tac >- suspend "history" >>
  fs[allocas_below_fmp_def] >> metis_tac[]
QED
Resume selected_stored_caller_frame_mods[immutable]:
  irule ifexp_typed_immutable_frame_mods >>
  goal_assum (drule_at (Pat `immutable_frame_mods _ _ _ _ _`)) >>
  qexistsl_tac [`off`,`ai`,`sa`,`cap`] >>
  simp[typed_copy_state_frame_def, typed_copy_frame_def] >>
  qpat_assum `stored with <|vs_vars := _; vs_memory := _|> = _`
    mp_tac >> simp[venom_state_component_equality] >> strip_tac >> simp[] >>
  rpt gen_tac >> strip_tac >>
  qpat_assum `!b sz. _ ==> mem_bytes_at _ _ stored.vs_memory = _` irule >>
  simp[arithmeticTheory.ADD_COMM]
QED
Resume selected_stored_caller_frame_mods[ghost]:
  irule stored_ghost >>
  goal_assum (drule_at (Pat `ghost_inv_at_mods _ _ _ _ _ _ _ _ _`)) >>
  goal_assum (drule_at (Pat `local_ptrs_reserved _ _`)) >>
  simp[pred_setTheory.DIFF_SUBSET] >>
  qpat_assum `!b sz. _ ==> mem_bytes_at _ _ _ = _` (qspecl_then [`0`,`lo`] mp_tac) >> simp[] >>
  qexists_tac `func` >> simp[] >> first_assum ACCEPT_TAC
QED
Resume selected_stored_caller_frame_mods[physical]:
  irule result_state_memory_frame >>
  conj_tac
  >- (qpat_assum `immutable_frame_mods _ _ _ _ stored` mp_tac >>
      pure_rewrite_tac[immutable_frame_mods_def, immutables_rel_mods_def] >>
      strip_tac >> qpat_assum `!src tops. _ ==> immutables_rel _ _ _ _ _ _` irule >>
      goal_assum (drule_at Any)) >>
  qexists_tac `a` >> simp[] >>
  conj_tac >- first_assum ACCEPT_TAC >>
  fs[local_ptrs_reserved_def] >> metis_tac[]
QED
Resume selected_stored_caller_frame_mods[immutable_cursor]:
  qpat_x_assum `immutable_frame_mods _ _ _ _ stored` mp_tac >>
  simp[immutable_frame_mods_def, immutables_rel_mods_def, immutable_alloca_sep_mods_def,
       immutables_rel_def, immutable_alloca_sep_def, immutable_decl_sep_def,
       local_region_def, lookup_var_def]
QED
Resume selected_stored_caller_frame_mods[ghost_cursor]:
  qpat_x_assum `ghost_inv_at_mods _ _ _ _ _ _ _ _ stored` mp_tac >>
  Cases_on `d`
  >- (simp_tac (srw_ss()) [ghost_inv_at_mods_def, allocas_from_def, stor_taint_ok_at_def,
                           return_buf_ptr_def, ptr_covers_def, lookup_var_def] >>
      strip_tac >> rpt conj_tac >> first_assum ACCEPT_TAC) >>
  rename1 `ghost_inv_at_mods _ _ (SOME p) _ _ _ _ _ _` >> PairCases_on `p` >>
  simp_tac (srw_ss()) [ghost_inv_at_mods_def, allocas_from_def, stor_taint_ok_at_def,
                       return_buf_ptr_def, ptr_covers_def, lookup_var_def] >>
  strip_tac >> rpt conj_tac >> first_assum ACCEPT_TAC
QED
Resume selected_stored_caller_frame_mods[kept]:
  fs[ghost_kept_at_def, pred_setTheory.IN_DIFF] >> conj_tac
  >- (rpt strip_tac >> rename1 `FLOOKUP s0.vs_allocas aid = SOME (b,n)` >>
      qpat_assum `!aid b n i. FLOOKUP s0.vs_allocas aid = _ /\ _ ==> _`
        (qspecl_then [`aid`,`b`,`n`,`i`] mp_tac) >> simp[] >>
      disch_then irule >> first_assum ACCEPT_TAC) >>
  rpt strip_tac >>
  qpat_assum `!n b sz i. local_region _ _ s0 n b sz /\ _ ==> _` drule_all >> simp[]
QED
Resume selected_stored_caller_frame_mods[locals]:
  irule locals_kept_regions_tail >>
  goal_assum (drule_at (Pat `locals_kept _ _ _ _ _`)) >>
  simp[] >> rpt gen_tac >> strip_tac >>
  `local_region ce ee.scopes a n b sz` by
    (irule local_region_frame_fwd >> goal_assum (drule_at (Pat `local_region _ _ _ _ _ _`)) >>
     qexists_tac `sa` >> fs[locals_kept_def]) >>
  qpat_assum `!n b sz. local_region _ _ _ _ _ _ ==> mem_bytes_at _ _ stored.vs_memory = _` drule >> simp[]
QED
Resume selected_stored_caller_frame_mods[old_bytes]:
  rpt gen_tac >> strip_tac >>
  `FLOOKUP a.vs_allocas aid = SOME (b,sz)` by
    (qpat_assum `!aid b. FLOOKUP s0.vs_allocas aid = SOME b ==> _` drule >> simp[]) >>
  `aid <> sa.cs_next_id` by decide_tac >>
  `b + sz <= off \/ off + cap <= b` by
    (fs[alloca_inv_def, allocas_non_overlapping_def] >>
     qpat_assum `!a1 a2 b1 sz1 b2 sz2. _ ==> _ \/ _` drule_all >>
     simp[arithmeticTheory.ADD_COMM]) >>
  `mem_bytes_at b sz stored.vs_memory = mem_bytes_at b sz a.vs_memory` by
    (qpat_assum `!b sz. _ ==> mem_bytes_at _ _ stored.vs_memory = _` irule >>
     simp[arithmeticTheory.ADD_COMM]) >>
  simp[] >>
  qpat_assum `!aid b sz. _ ==> mem_bytes_at _ _ a.vs_memory = _`
    (qspecl_then [`aid`,`b`,`sz`] mp_tac) >> simp[] >>
  disch_then irule >> first_assum ACCEPT_TAC
QED
Resume selected_stored_caller_frame_mods[history]:
  drule_all stmtReasonLitFragMemoryTheory.fn_has_code_code >> strip_tac >>
  fs[rich_listTheory.IS_PREFIX_APPEND] >>
  qpat_assum `a.vs_inst_idx = LENGTH st4.cs_current_insts` (SUBST1_TAC o SYM) >>
  irule alloca_history_run_inst_seq >>
  goal_assum (drule_at (Pat `run_inst_seq _ _ = OK _`)) >>
  fs[EVERY_MEM]
QED
Finalise selected_stored_caller_frame_mods
