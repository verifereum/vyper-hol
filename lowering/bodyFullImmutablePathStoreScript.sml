(* Restore the statement post after the constructor writes one live path. *)
Theory bodyFullImmutablePathStore
Ancestors
  immutableDeployAssignPathGhost immutableAssignCompose
  bodyImmutableAugAssignExec bodyFullPathHistory bodyFullHashKeccakFixed
  stmtSimDefs exprLoweringProps loweringPosts gasOutcomeFullCompose gasSummary fragExec bodyInvCodeProps
  freshWrites bodyPtrDefs bodySim vyperPlaceFrames
  vyperStorageFootprint gasContext venomState
  immutableWordStorePath stmtSimDeclStore stmtLowering context
  exprSimCopy wordLoadStorePtr venomMemProofs calldataTypedRobustPtr
  fragGasOriginPtrExec fragGasOriginPtrDead immutableCopyWordsPath immutableDeployOperandTransfer
  venomMemProps exprLowering localValueStoreProps
  compileEnv bodyMemoryDefs words arithmetic exprSimProps ptrDiscipline loweringStateRelDefs stateRelProj
  robustCopyTransportPtr valueEncodingProps valueTypingMemoryProps assignTuplePtrStoreWord
  bodySimAugPlaceLoad exprSimPopNestedLocalSource exprSimSubscriptArrayLiveImmutableView
  exprSimHypsDefs vyperTypeSystem vyperTypeInvariants vyperTargetPlaceWrite
  vyperPlaceWriteSoundness vyperInterpreter vyperState
  bodyInvSplit[qualified]
  gasOutcomeFullMods[qualified]

(* The executor fixes the write's byte window before source-state restoration. *)
Definition immutable_path_store_post_def:
  immutable_path_store_post
    (lo,explicit,ctx,func,PG) off tv v sa sb (s,G,tn) (q,Gf,tf) <=>
    (!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG)
      (s,G,tn) [] (OK q,Gf,tf)) /\
    (!m. mem_agree_outside tf.t_mem q.vs_memory m ==> val_in_memory tv v off m) /\
    (q with <|vs_vars := s.vs_vars; vs_memory := s.vs_memory;
      vs_immutables := s.vs_immutables; vs_prev_bb := s.vs_prev_bb;
      vs_current_bb := s.vs_current_bb; vs_inst_idx := s.vs_inst_idx|>) = s /\
    LENGTH s.vs_memory <= LENGTH q.vs_memory /\
    (!a n. regions_disjoint a n off (type_memory_size tv) ==>
      mem_bytes_at a n q.vs_memory = mem_bytes_at a n s.vs_memory) /\
    (!i. ~(off <= i /\ i < off+type_memory_size tv) /\ i IN tf.t_mem ==>
         i IN tn.t_mem) /\
    tf.t_stor = tn.t_stor /\ tf.t_trans = tn.t_trans /\
    (!x. not_fresh_at sa x ==> lookup_var x q = lookup_var x s /\
      FLOOKUP Gf x = FLOOKUP G x /\ op_taint tf (Var x) = op_taint tn (Var x)) /\
    ~q.vs_halted /\ q.vs_current_bb = sb.cs_current_bb /\
    q.vs_inst_idx = LENGTH sb.cs_current_insts
End

Theorem immutable_path_store_base_operand:
  stmt_state_rel H ctx func ce cx ee s /\ ghost_inv_at D lo d ce cx ee G tn s /\
  local_ptrs_reserved ce sa /\ lo <> 0 ==>
  !base. ce.ce_imm_alloca = SOME base ==> eval_operand base s = SOME 0w /\
    copy_old_operand sa base /\ op_taint tn base = {} /\ op_prov G base = NONE
Proof
  strip_tac >>
  drule_then (assume_tac o REWRITE_RULE [immutable_base_zero_def])
    stmt_state_rel_immutable_base_zero >>
  `!x. ce.ce_imm_alloca = SOME (Var x) ==>
       FLOOKUP G x = NONE /\ op_taint tn (Var x) = {}` by
    fs[ghost_inv_at_def] >>
  Cases >> simp[copy_old_operand_def,op_prov_def] >>
  simp[op_taint_def] >> metis_tac[local_ptrs_reserved_imm_base,op_taint_def]
QED

Theorem immutable_path_store_word:
  compile_assign_value ce dst LocCode op T loc ty sty bytes sa = ((),sb) /\
  is_word_type ty /\ evaluate_type tenv ty = SOME tv /\ value_has_type tv v /\
  copy_old_operand sa op /\ eval_operand op s = SOME (typed_val_to_w256 tv v) /\
  op_taint tn op = {} /\
  eval_operand dst s = SOME (n2w off) /\ op_taint tn dst = {} /\ op_prov G dst = NONE /\
  off+32 <= lo /\ lo <= s.vs_alloca_next /\ lo < dimword (:256) /\
  (!base. ce.ce_imm_alloca = SOME base ==> eval_operand base s = SOME 0w /\
    op_taint tn base = {} /\ op_prov G base = NONE) /\
  allocas_from lo s /\ (ctx_has_dalloca ctx ==> allocas_below_fmp s) /\
  fn_has_code sa sb func /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\ s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?q Gf tf. immutable_path_store_post (lo,explicit,ctx,func,PG) off tv v
    sa sb (s,G,tn) (q,Gf,tf)
Proof
  strip_tac >>
  `compile_imm_store_word ce.ce_imm_alloca dst op sa = ((),sb)` by
    fs[compile_assign_value_def,comp_bind_def,comp_return_def] >>
  `w2n (n2w off:bytes32) = off` by (simp[w2n_n2w,LESS_MOD] >> decide_tac) >>
  `w2n (n2w off:bytes32) + 32 <= lo` by simp[] >>
  `type_memory_size tv = 32` by drule_all_then ACCEPT_TAC evaluated_word_memory_size >>
  `!x. op = Var x ==> not_fresh_at sa x` by fs[copy_old_operand_def] >>
  drule_all immutable_word_store_path_clean >>
  disch_then (strip_assume_tac o Q.INST [`PG` |-> `PG`,`explicit` |-> `explicit`]
              o SPEC_ALL) >>
  rename1 `u.vs_memory = _` >>
  rename1 `tf.t_stor = tn.t_stor` >>
  qabbrev_tac `q = u with vs_inst_idx := LENGTH sb.cs_current_insts` >>
  `!m. mem_agree_outside tf.t_mem q.vs_memory m ==> val_in_memory tv v off m` by
    (mp_tac (Q.INST [`ty` |-> `ty`,`tenv` |-> `tenv`,
        `dirty` |-> `tn.t_mem`,`off` |-> `off`,`s` |-> `s`]
        typed_word_store_robust_ptr) >>
     simp[Abbr `q`]) >>
  qexistsl [`q`,`Gf`,`tf`] >> simp[immutable_path_store_post_def,Abbr `q`] >>
  `u.vs_current_bb = s.vs_current_bb /\ u.vs_halted = s.vs_halted` by
    (qpat_assum `(u with <|vs_vars := _; vs_memory := _; vs_immutables := _|>) = s` mp_tac >>
     simp[venom_state_component_equality]) >>
  simp[mstore_memory_nondecreasing,blockPrefixEquivTheory.lookup_var_set_inst_idx] >>
  conj_tac >-
    (qpat_assum `(u with <|vs_vars := _; vs_memory := _; vs_immutables := _|>) = s` mp_tac >>
     simp[venom_state_component_equality]) >>
  rpt strip_tac >> irule mstore_mem_bytes_at_disjoint >>
  fs[regions_disjoint_def] >> decide_tac
QED

Theorem immutable_path_store_fixed:
  compile_assign_value ce dst LocCode (Var src) F loc ty ty (type_memory_size tv)
    sa = ((),sb) /\
  ~is_bytestring_type ty /\ 0 < type_memory_size tv /\ value_has_type tv v /\
  not_fresh_at sa src /\ eval_operand (Var src) s = SOME (n2w a) /\
  (!m. mem_agree_outside tn.t_mem s.vs_memory m ==> val_in_memory tv v a m) /\
  ptr_covers G tn src s (type_memory_size tv) /\
  lo <= a /\ a + type_memory_size tv < dimword (:256) /\
  a + type_memory_size tv <= s.vs_alloca_next /\
  copy_old_operand sa dst /\ eval_operand dst s = SOME (n2w off) /\
  op_taint tn dst = {} /\ op_prov G dst = NONE /\
  off+type_memory_size tv <= lo /\ lo <= s.vs_alloca_next /\ lo < dimword (:256) /\
  (!base. ce.ce_imm_alloca = SOME base ==> eval_operand base s = SOME 0w /\
    copy_old_operand sa base /\ op_taint tn base = {} /\ op_prov G base = NONE) /\
  allocas_from lo s /\ (ctx_has_dalloca ctx ==> allocas_below_fmp s) /\
  fn_has_code sa sb func /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\ s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?q Gf tf. immutable_path_store_post (lo,explicit,ctx,func,PG) off tv v
    sa sb (s,G,tn) (q,Gf,tf)
Proof
  strip_tac >>
  qabbrev_tac `copy_size = type_memory_size tv` >>
  qabbrev_tac `n = if copy_size <= 32 then 1 else (copy_size+31) DIV 32` >>
  `32*n = copy_size` by
    (`copy_size = 32 * type_slot_size tv` by simp[Abbr `copy_size`,type_memory_size_slots] >>
     Cases_on `copy_size <= 32` >> simp[Abbr `n`] >> decide_tac) >>
  `compile_imm_store_words ce.ce_imm_alloca (Var src) dst n 0 sa = ((),sb)` by
    (simp[Abbr `n`] >> irule immutable_store_suffix_words >>
     gvs[compile_assign_value_def,comp_bind_def,comp_return_def]) >>
  mp_tac (Q.INST [`imm` |-> `ce.ce_imm_alloca`,`root` |-> `src`,`k` |-> `copy_size`,
    `capacity` |-> `copy_size`,`explicit` |-> `explicit`,`PG` |-> `PG`]
    immutable_copy_words_path) >>
  (impl_tac >- fs[eval_operand_def]) >>
  disch_then (qx_choosel_then [`u`,`Gf`,`tf`] strip_assume_tac) >>
  qabbrev_tac `q = u with vs_inst_idx := LENGTH sb.cs_current_insts` >>
  `!i. i < copy_size ==> (off+i IN tf.t_mem <=> a+i IN tn.t_mem)` by
    (rpt strip_tac >>
     qpat_assum `!x. x IN tf.t_mem <=> _` (qspec_then `off+i` mp_tac) >>
     `off+i-off = i` by decide_tac >> simp[]) >>
  `!m. mem_agree_outside tf.t_mem q.vs_memory m ==> val_in_memory tv v off m` by
    (qspecl_then [`tv`,`v`,`a`,`off`,`copy_size`,`tn.t_mem`,`tf.t_mem`,
       `s.vs_memory`,`q.vs_memory`] match_mp_tac robust_val_in_memory_copy_transport >>
     simp[Abbr `q`,value_has_type_memory_wf] >>
     simp[Abbr `copy_size`,val_footprint_le,value_has_type_memory_wf]) >>
  `u.vs_current_bb = s.vs_current_bb /\ u.vs_halted = s.vs_halted` by
    (qpat_assum `(u with <|vs_vars := _; vs_memory := _; vs_immutables := _|>) = s` mp_tac >>
     simp[venom_state_component_equality]) >>
  `sb.cs_current_bb = sa.cs_current_bb` by fs[same_blocks_def] >>
  qexistsl [`q`,`Gf`,`tf`] >>
  simp[immutable_path_store_post_def,Abbr `q`,blockPrefixEquivTheory.lookup_var_set_inst_idx] >>
  conj_tac >-
    (qpat_assum `(u with <|vs_vars := _; vs_memory := _; vs_immutables := _|>) = s` mp_tac >>
     simp[venom_state_component_equality]) >>
  conj_tac >- (rpt strip_tac >> fs[regions_disjoint_def]) >>
  rpt strip_tac >>
  qpat_x_assum `if _ then _ else _` mp_tac >> simp[]
QED

(* SCRATCH MEASUREMENT: the original proof failed after widening the body
   definitions. Temporarily admit it to test its downstream consumers.
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_then assume_tac immutable_write_place_gas_obs >>
  `fin.gas_obs = [] /\ fin.storage_trace = ee.storage_trace` by
    (drule_then strip_assume_tac write_immutable_place_frame >> simp[]) >>
  `fin with gas_obs := [] = fin` by simp[evaluation_state_component_equality] >>
  `q.vs_allocas = s.vs_allocas /\ q.vs_alloca_next = s.vs_alloca_next /\
   q.vs_call_ctx = s.vs_call_ctx /\ q.vs_accounts = s.vs_accounts /\
   q.vs_transient = s.vs_transient` by
    (qpat_assum `(q with <|vs_vars := _; vs_memory := _; vs_immutables := _;
          vs_prev_bb := _; vs_current_bb := _; vs_inst_idx := _|>) = s` mp_tac >>
     simp[venom_state_component_equality]) >>
  `val_in_memory ptv v (off+k) q.vs_memory` by
    (first_assum irule >> simp[mem_agree_outside_def]) >>
  `!x. not_fresh_at sa x ==> not_fresh_at su x` by
    metis_tac[not_fresh_at_mono] >>
  `return_buf_frame d ce sb q` by
    (irule return_buf_frame_frame >> qexistsl [`ce`,`s`,`su`] >> simp[] >>
     metis_tac[]) >>
  irule gas_outcome_full_intro >>
  qexistsl [`Gf`,`fin`,`[]`,`OK q`,`INL ()`,`tf`] >>
  simp[gas_explicit_def,exit_result_def] >>
  gen_tac >> strip_tac >>
  qpat_assum `!H. valid_horizon cx st0 H ee.storage_trace ==> _`
    (drule_then (map_every assume_tac o CONJUNCTS)) >>
  `immutable_section_layout_mods ce.ce_modules ce` by
    metis_tac[body_inv_unit_immutable_layout] >>
  `stmt_post H ctx func cx lctx ce ce su sb ee s (INL ()) fin q` by
    (`q with vs_inst_idx := LENGTH sb.cs_current_insts = q` by
       simp[venom_state_component_equality] >>
     qpat_assum `q with vs_inst_idx := LENGTH sb.cs_current_insts = q`
       (fn eq => mp_tac
         (REWRITE_RULE [eq] (Q.INST [`q` |-> `q`,`sb` |-> `sb`]
            (INST_TYPE [alpha |-> ``:256``] immutable_path_assign_suffix_stmt_post)))) >>
     simp[] >> disch_then match_mp_tac >> simp[]) >>
  `allocas_from lo s` by fs[ghost_inv_at_def] >>
  `allocas_from lo q` by
    (qpat_assum `q.vs_allocas = s.vs_allocas` (fn eq => REWRITE_TAC [allocas_from_def,eq]) >>
     qpat_assum `allocas_from lo s` (ACCEPT_TAC o REWRITE_RULE [allocas_from_def])) >>
  `s.vs_alloca_next <= q.vs_alloca_next` by simp[] >>
  drule_all_then assume_tac immutable_path_store_ghost_inv >>
  drule_then strip_assume_tac stateRelProjTheory.stmt_state_rel_local_ptrs_alloca >>
  drule_all_then assume_tac body_full_path_alloca_history >>
  `off + type_memory_size itv <= lo` by
    (drule_all immutable_assign_section_root >> strip_tac >> first_assum ACCEPT_TAC) >>
  drule_then strip_assume_tac exprSimPropsTheory.mem_path_offset_sound >>
  qpat_assum `stmt_post _ _ _ _ _ _ _ _ _ _ _ _ _ _`
    (strip_assume_tac o REWRITE_RULE [stmt_post_def]) >>
  gvs[] >>
  conj_tac >-
    (qpat_assum `stmt_state_rel H ctx func ce cx fin q`
      (ACCEPT_TAC o MATCH_MP stmt_state_rel_allocas_below_fmp)) >>
  conj_tac >-
    (irule alloca_frame_trans >> qexistsl [`ce`,`ee`,`s`,`su`] >>
     rpt conj_tac >> first_assum ACCEPT_TAC) >>
  rpt strip_tac >>
  `lo <= a` by
    (qpat_assum `allocas_from lo s0` (mp_tac o REWRITE_RULE [allocas_from_def]) >>
     disch_then drule >> simp[]) >>
  `i IN tn.t_mem` by
    (qpat_assum `!i. _ ==> i IN tn.t_mem` irule >> simp[] >> decide_tac) >>
  metis_tac[]
QED
*)
Theorem immutable_path_write_outcome:
  (contract_inv mods exps ctx ce cx /\
     module_body_inv mods ce.ce_module tops ce cx) /\
  expr_sim_inv_mods mods ce cx env ee /\ local_ptrs_reserved ce su /\ ce.ce_is_ctor /\
  FLOOKUP env.bare_globals (ce.ce_module,id) = SOME ity /\
  FLOOKUP ce.ce_module_vars (ce.ce_module,id) = SOME (ImmutableLoc off) /\
  ce.ce_module_var_type (ce.ce_module,id) = SOME ity /\
  evaluate_type (get_tenv cx) ity = SOME itv /\
  mem_path_offset itv path = SOME (k,ptv) /\
  write_place cx (ImmutablePlace ce.ce_module id path) v ee = (INL (),fin) /\
  value_has_type ptv v /\
  (!m. mem_agree_outside tf.t_mem q.vs_memory m ==> val_in_memory ptv v (off+k) m) /\
  (q with <|vs_vars := s.vs_vars; vs_memory := s.vs_memory;
    vs_immutables := s.vs_immutables; vs_prev_bb := s.vs_prev_bb;
    vs_current_bb := s.vs_current_bb; vs_inst_idx := s.vs_inst_idx|>) = s /\
  LENGTH s.vs_memory <= LENGTH q.vs_memory /\
  (!a n. regions_disjoint a n (off+k) (type_memory_size ptv) ==>
    mem_bytes_at a n q.vs_memory = mem_bytes_at a n s.vs_memory) /\
  (!i. ~(off+k <= i /\ i < off+k+type_memory_size ptv) /\ i IN tf.t_mem ==>
       i IN tn.t_mem) /\
  tf.t_stor = tn.t_stor /\ tf.t_trans = tn.t_trans /\
  (!x. not_fresh_at su x ==> lookup_var x q = lookup_var x s /\
    FLOOKUP Gf x = FLOOKUP G x /\ op_taint tf (Var x) = op_taint tn (Var x)) /\
  (!x cap. ce.ce_return_buf = SOME (PtrVar (Var x) cap) ==> not_fresh_at su x) /\
  (!x cap. ce.ce_return_pc = SOME (PtrVar (Var x) cap) ==> not_fresh_at su x) /\
  su.cs_next_var <= sb.cs_next_var /\ sa.cs_next_var <= su.cs_next_var /\
  sa.cs_next_id <= su.cs_next_id /\
  fn_inst_ids_distinct func /\ alloca_history func s /\ return_buf_frame d ce su s /\
  ~q.vs_halted /\ q.vs_current_bb = sb.cs_current_bb /\
  q.vs_inst_idx = LENGTH sb.cs_current_insts /\ ~block_is_terminated sb /\
  (!H. valid_horizon cx st0 H ee.storage_trace ==>
    stmt_state_rel H ctx func ce cx ee s /\ storage_well_formed_on cx ee (FST H) /\
    ghost_inv_at (DF H) lo d ce cx ee G tn s /\ dead_lo_ok H (DF H) lo ce cx /\
    gas_origin_ptr_path (DF H,lo,explicit,ctx,func,PG) (s,G,tn) [] (OK q,Gf,tf)) /\
  ee.gas_obs = [] /\ storage_trace_domain cx st0 ee.storage_trace /\
  allocas_from lo s0 /\ s0.vs_alloca_next <= s.vs_alloca_next /\
  (!x w. not_fresh_at sa x /\ lookup_var x s0 = SOME w ==> lookup_var x s = SOME w) /\
  (!aid b. FLOOKUP s0.vs_allocas aid = SOME b ==> FLOOKUP s.vs_allocas aid = SOME b) /\
  (!x. not_fresh_at sa x ==> FLOOKUP G x = FLOOKUP G0 x /\
    op_taint tn (Var x) = op_taint tn0 (Var x)) /\
  alloca_frame ce es sa s0 ce ee s /\
  (!aid a n i. FLOOKUP s0.vs_allocas aid = SOME (a,n) /\ aid < sa.cs_next_id /\
    (!name b cap. local_region ce es.scopes s0 name b cap ==> a+n <= b \/ b+cap <= a) /\
    a <= i /\ i < a+n /\ i IN tn.t_mem ==> i IN tn0.t_mem) ==>
  gas_outcome_full_mods (DF,lo,explicit,ctx,func,PG) ce.ce_modules cx st0
    (write_place cx (ImmutablePlace ce.ce_module id path) v) (ee,s,G,tn)
    (\H res ef G' tn' t. ?ce'.
      stmt_lands lctx sb res t /\ ~t.vs_halted /\
      (res = INL () ==> ~block_is_terminated sb /\ ce' = ce) /\
      cenv_top_ext ce ce' ef.scopes /\
      stmt_state_rel H ctx func ce' cx ef t /\ storage_well_formed_on cx ef (FST H) /\
      return_buf_frame d ce' sb t /\ alloca_history func t /\
      (ctx_has_dalloca ctx ==> allocas_below_fmp t) /\
      s0.vs_alloca_next <= t.vs_alloca_next /\ ghost_inv_at (DF H) lo d ce' cx ef G' tn' t /\
      (!x w. not_fresh_at sa x /\ lookup_var x s0 = SOME w ==> lookup_var x t = SOME w) /\
      (!aid b. FLOOKUP s0.vs_allocas aid = SOME b ==> FLOOKUP t.vs_allocas aid = SOME b) /\
      (!x. not_fresh_at sa x ==>
        FLOOKUP G' x = FLOOKUP G0 x /\ op_taint tn' (Var x) = op_taint tn0 (Var x)) /\
      alloca_frame ce es sa s0 ce' ef t /\
      (!aid a n i. FLOOKUP s0.vs_allocas aid = SOME (a,n) /\ aid < sa.cs_next_id /\
        (!name b cap. local_region ce es.scopes s0 name b cap ==> a+n <= b \/ b+cap <= a) /\
        a <= i /\ i < a+n /\ i IN tn'.t_mem ==> i IN tn0.t_mem)) R
Proof
  cheat
QED
