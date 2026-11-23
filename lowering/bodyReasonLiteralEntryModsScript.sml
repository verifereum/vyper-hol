(* The reason shortcut allocates at the annotation's capacity, while its
   compiled value uses the payload length as tag. *)
Theory bodyReasonLiteralEntryMods
Ancestors
  bodyFullRaiseReasonLiteralEntry bodyFullShadowBodyInv stateRelProj
  reasonLiteralBufferPtr stmtReasonLitMemory exprSimPtrLiteralBuffer
  bodyFullUnwrapSlotPost bodyPtrMakeArrayAllocBuffer instSeqPtrLo
  gasOriginPtrLabels allocationPtr fragGasSeqPtr allocaHistoryFragment
  exprSimUnwrapProps exprSimMemDefs loweringPosts localPtrsProps
  exprLoweringProps exprLowering exprSimHypsDefs stmtLowering context
  ptrDiscipline bodyPtrDefs loweringStateRelDefs compileEnv vyperTypeSystem vyperAST
  vyperValue vyperStorageFootprint venomState venomInst venomExecSemantics venomExecProofs list words

Theorem reason_capacity_run_mem[local]:
  compile_bytelike_literal bs ml sa = (buf,sb) /\ LENGTH bs <= ml /\
  fn_has_code sa sb func /\ stmt_state_rel H ctx func cenv cx es s /\
  32+32*word_size ml < dimword (:256) /\
  run_inst_seq (emitted_insts sa sb) s = OK t ==>
  EVERY (\i. i.inst_opcode = ALLOCA \/ i.inst_opcode = ADD \/
             i.inst_opcode = MSTORE) (emitted_insts sa sb) /\
  run_inst_seq_mem_ok (emitted_insts sa sb) s /\
  s.vs_alloca_next <= t.vs_alloca_next /\
  t.vs_halted = s.vs_halted /\ t.vs_current_bb = s.vs_current_bb
Proof
  strip_tac >> drule reason_literal_compiler_shape >> strip_tac >>
  `MEM (mk_inst sa.cs_next_id ALLOCA
      [Lit (n2w (32+32*word_size ml))] [STRING #"%" (toString sa.cs_next_var)])
      (fn_insts func)` by
    (irule compileAllocaProvenanceTheory.fn_has_code_current_member >>
     goal_assum (drule_at Any) >> gvs[]) >>
  drule_then assume_tac stmt_state_rel_alloca_room >>
  drule_then strip_assume_tac stmt_state_rel_local_ptrs_alloca >>
  `alloca_next_valid s` by fs[venomMemDefsTheory.alloca_inv_def] >>
  `!x. FLOOKUP s.vs_allocas sa.cs_next_id = SOME x ==>
       SND x = 32+32*word_size ml` by
    (PairCases >> strip_tac >>
     drule_all allocationPtrTheory.stmt_state_rel_alloca_site_bound >> simp[]) >>
  drule bytelike_literal_run_mem >>
  disch_then (qspecl_then [`ctx`,`func`,`s`] mp_tac) >>
  (impl_tac >-
    (`32+(ml+31) DIV 32*32 = 32+32*word_size ml` by
       simp_tac std_ss [vfmConstantsTheory.word_size_def, arithmeticTheory.MULT_COMM] >>
     asm_rewrite_tac[])) >>
  strip_tac >> gvs[]
QED

Theorem reason_literal_static_step[local]:
  (i.inst_opcode = ALLOCA \/ i.inst_opcode = ADD \/ i.inst_opcode = MSTORE) /\
  step_inst_base i s = OK t ==>
  t.vs_call_ctx = s.vs_call_ctx /\ t.vs_accounts = s.vs_accounts /\
  t.vs_transient = s.vs_transient /\ t.vs_immutables = s.vs_immutables
Proof
  strip_tac >> qpat_x_assum `step_inst_base i s = OK t` mp_tac
  >- (simp[step_inst_base_opcode_eqs, exec_alloca_def, AllCaseEqs(),
           update_var_def, mstore_def] >> strip_tac >> gvs[])
  >- (simp[step_inst_base_opcode_eqs, exec_pure2_def, AllCaseEqs(),
           update_var_def] >> strip_tac >> gvs[]) >>
  simp[step_inst_base_opcode_eqs, exec_write2_def, AllCaseEqs(),
       update_var_def, mstore_def] >> strip_tac >> gvs[]
QED

Theorem reason_literal_static_run[local]:
  !code s t.
    EVERY (\i. i.inst_opcode = ALLOCA \/ i.inst_opcode = ADD \/ i.inst_opcode = MSTORE) code /\
    run_inst_seq code s = OK t ==>
    t.vs_call_ctx = s.vs_call_ctx /\ t.vs_accounts = s.vs_accounts /\
    t.vs_transient = s.vs_transient /\ t.vs_immutables = s.vs_immutables
Proof
  Induct >> simp[run_inst_seq_def] >> rpt gen_tac >> strip_tac >>
  `~is_terminator h.inst_opcode` by gvs[is_terminator_def] >>
  gvs[AllCaseEqs()] >>
  drule_at Any reason_literal_static_step >> simp[] >> strip_tac >>
  first_x_assum drule_all >> simp[]
QED

(* Apply the physical copy-frame rule with no low-section obligation. The
   actual linked section and its allocation floor are transported separately. *)
Theorem reason_copy_ghost_mods[local]:
  ghost_inv_at_mods D lo d cenv cx es G tn s /\ local_ptrs_reserved cenv sa /\
  (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  local_ptrs_rel func cenv es.scopes s /\
  (!name b len. local_region cenv es.scopes s name b len ==>
    start+nb <= b \/ b+len <= start) /\
  (!x. not_fresh_at sa x ==> lookup_var x z = lookup_var x s /\
    FLOOKUP Gf x = FLOOKUP G x /\ op_taint tf (Var x) = op_taint tn (Var x)) /\
  (!a k. a+k <= start \/ start+nb <= a ==>
    mem_bytes_at a k z.vs_memory = mem_bytes_at a k s.vs_memory) /\
  (!j. j < start \/ start+nb <= j ==> (j IN tf.t_mem <=> j IN tn.t_mem)) /\
  lo <= start /\ stor_taint_ok_at D tf z /\ allocas_from lo z /\ lo <= z.vs_alloca_next ==>
  ghost_inv_at_mods D lo d cenv cx es Gf tf z
Proof
  strip_tac >>
  `ghost_inv_at D 0 d cenv cx es G tn s` by
    (qpat_assum `ghost_inv_at_mods _ _ _ _ _ _ _ _ _` mp_tac >>
     pure_rewrite_tac[ghost_inv_at_mods_def, ghost_inv_at_def, ptrDisciplineTheory.allocas_from_def] >>
     simp[NoAsms] >> strip_tac >> rpt conj_tac >> first_assum ACCEPT_TAC) >>
  `ghost_inv_at D 0 d cenv cx es Gf tf z` by
    (irule unwrap_slot_copy_ghost_inv_at >>
     simp[ptrDisciplineTheory.allocas_from_def] >>
     map_every (fn pat => qpat_assum pat (irule_at Any))
       [`ghost_inv_at _ _ _ _ _ _ _ _ s`, `local_ptrs_reserved _ _`,
        `local_ptrs_rel _ _ _ _`] >>
     qexistsl_tac [`start`,`nb`] >>
     `nb + start = start + nb` by decide_tac >>
     asm_rewrite_tac[]) >>
  `mem_bytes_at 0 lo z.vs_memory = mem_bytes_at 0 lo s.vs_memory` by simp[] >>
  fs[ghost_inv_at_mods_def, ghost_inv_at_def] >> rpt conj_tac
  >- first_assum ACCEPT_TAC
  >- (qx_gen_tac `i` >> strip_tac >> `i < start` by decide_tac >> metis_tac[]) >>
  rpt strip_tac >> fs[local_ptrs_reserved_def] >> metis_tac[]
QED

Theorem reason_literal_pointer[local]:
  LENGTH str <= n /\ word_size (LENGTH str) <= word_size ml /\
  b < dimword (:256) /\ mem_word_at b s.vs_memory = n2w (LENGTH str) /\
  mem_bytes_at (b+32) (LENGTH str) s.vs_memory = MAP (n2w o ORD) str /\
  tf.t_mem = (tn.t_mem UNION dirty) DIFF
     {i | b <= i /\ i < b+32+32*word_size (LENGTH str)} /\
  FLOOKUP G p = SOME (b,32+32*word_size ml) /\
  lookup_var p s = SOME (n2w b) /\ op_taint tf (Var p) = {} ==>
  ptr_val_ok cx (BaseT (StringT n)) (StringV str) (Var p) G tf s
Proof
  strip_tac >>
  `val_wf (BaseTV (StringT n)) (StringV str) /\
   val_in_memory (BaseTV (StringT n)) (StringV str) b s.vs_memory /\
   (!i. b <= i /\ i < b+val_footprint (BaseTV (StringT n)) (StringV str) ==>
      i NOTIN tf.t_mem) /\
   val_store_size (BaseTV (StringT n)) (StringV str) = 32+32*word_size (LENGTH str)` by
    (drule_all (SRULE [] (Q.INST [`tn` |-> `tn with t_mem := tn.t_mem UNION dirty`]
      (SPEC_ALL literal_ptr_string_representation))) >> simp[]) >>
  simp[ptr_val_ok_def, is_word_type_def] >>
  irule literal_clean_ptr_mem_ok >> qexistsl_tac [`b`,`32+32*word_size ml`,`n2w b`] >>
  simp[evaluate_type_def, w2n_n2w]
QED

Theorem reason_literal_message_entry_mods:
  compile_bytelike_literal (MAP (n2w o ORD) str) ml sa = (buf,sb) /\
  LENGTH str <= ml /\
  fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
  local_ptrs_reserved cenv sa /\
  32+32*word_size ml < dimword (:256) /\
  storage_trace_domain cx st0 es.storage_trace /\
  (!H. valid_horizon cx st0 H es.storage_trace ==>
    stmt_state_rel H ctx func cenv cx es s /\
    storage_well_formed_on cx es (FST H) /\
    ghost_inv_at_mods (DF H) lo d cenv cx es G tn s) /\
  alloca_history func s /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) ==>
  ?t p Gf tnf.
    compile_reason_message cenv (Literal (BaseT (StringT ml)) (StringL str)) sa =
      (LocatedValue (BaseT (StringT (LENGTH str))) (base_ptr buf),sb) /\
    buf.buf_operand = Var p /\
    vv_operand (LocatedValue (BaseT (StringT (LENGTH str))) (base_ptr buf)) = Var p /\
    vv_location (LocatedValue (BaseT (StringT (LENGTH str))) (base_ptr buf)) = SOME LocMemory /\
    not_fresh_at sb p /\
    alloca_history func t /\ s.vs_alloca_next <= t.vs_alloca_next /\
    ~t.vs_halted /\ t.vs_current_bb = sb.cs_current_bb /\
    t.vs_inst_idx = LENGTH sb.cs_current_insts /\
    ghost_kept_at lo cenv es sa G tn s Gf tnf /\
    expr_store_bound cx (BaseT (StringT (LENGTH str))) (StringV str) (Var p) t /\
    ptr_val_ok cx (BaseT (StringT (LENGTH str))) (StringV str) (Var p) Gf tnf t /\
    ptr_val_ok cx (BaseT (StringT ml)) (StringV str) (Var p) Gf tnf t /\
    ptr_buf_ok cenv (Literal (BaseT (StringT ml)) (StringL str)) (Var p) Gf t /\
    (!H. valid_horizon cx st0 H es.storage_trace ==>
      gas_origin_ptr_path (DF H,lo,explicit,ctx,func,PG) (s,G,tn) [] (OK t,Gf,tnf) /\
      expr_post H ctx func cenv cx (Literal (BaseT (StringT ml)) (StringL str))
        es sa sb s es (StringV str) (Var p) t /\
      ghost_inv_at_mods (DF H) lo d cenv cx es Gf tnf t)
Proof
  strip_tac >>
  `LENGTH (MAP (n2w o ORD) str : word8 list) <= ml` by simp[] >>
  `valid_horizon cx st0 (storage_trace_horizon es.storage_trace)
     es.storage_trace` by fs[storage_trace_domain_def] >>
  qpat_assum `!H. valid_horizon _ _ H _ ==> _`
    (drule_then strip_assume_tac) >>
  drule_all reason_literal_buffer_ptr_run >>
  disch_then (qspecl_then [`tn`,`func`,`PG`,`G`,`DF (storage_trace_horizon es.storage_trace)`]
    (strip_assume_tac o REWRITE_RULE [LENGTH_MAP])) >>
  drule_all reason_capacity_run_mem >> strip_tac >>
  drule reason_literal_compiler_shape >> strip_tac >>
  `sb.cs_current_bb = sa.cs_current_bb` by fs[same_blocks_def] >>
  drule_all stmtReasonLitFragMemoryTheory.fn_has_code_code >> strip_tac >>
  `lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
   isPREFIX (emitted_insts sa sb) (DROP s.vs_inst_idx bb.bb_instructions)` by gvs[] >>
  `(ctx_has_dalloca ctx ==>
     !pre i post u. emitted_insts sa sb = pre ++ i::post /\
       run_inst_seq pre s = OK u ==> unitTransformDefs$dalloca_no_wrap i u)` by
    (rpt strip_tac >> irule memSafeRunTheory.dalloca_no_wrap_non_dalloca >>
     `MEM i (emitted_insts sa sb)` by simp[MEM_APPEND] >>
     qpat_assum `EVERY (\i. i.inst_opcode = ALLOCA \/ _) _`
       (mp_tac o REWRITE_RULE [EVERY_MEM]) >>
     disch_then (drule_then (strip_assume_tac o BETA_RULE)) >> simp[]) >>
  qabbrev_tac `z = t with vs_inst_idx := LENGTH sb.cs_current_insts` >>
  `!H. valid_horizon cx st0 H es.storage_trace ==>
       gas_origin_ptr_path (DF H,lo,explicit,ctx,func,PG) (s,G,tn) [] (OK z,G',tn')` by
    (gen_tac >> strip_tac >>
     qpat_assum `!H. valid_horizon _ _ H _ ==> stmt_state_rel _ _ _ _ _ _ _ /\ _`
       (drule_then strip_assume_tac) >>
     drule_all reason_literal_buffer_ptr_run >>
     disch_then (qspecl_then [`tn`,`func`,`PG`,`G`,`DF H`]
       (strip_assume_tac o REWRITE_RULE [LENGTH_MAP])) >>
     `G'' = G' /\ tn'' = tn'` by
       (irule inst_seq_ptr_ghost_unique >>
        goal_assum (drule_at Any) >> goal_assum (drule_at Any)) >>
     qpat_x_assum `G'' = G'` SUBST_ALL_TAC >>
     qpat_x_assum `tn'' = tn'` SUBST_ALL_TAC >>
     `inst_seq_ptr (DF H) lo ctx func PG G tn (emitted_insts sa sb) s G' tn'` by
       (irule inst_seq_ptr_zero_to_lo >>
        qpat_assum `ghost_inv_at_mods (DF H) _ _ _ _ _ _ _ _`
          (strip_assume_tac o REWRITE_RULE [ghost_inv_at_mods_def]) >>
        qpat_assum `inst_seq_ptr (DF H) 0 _ _ _ _ _ _ _ _ _` (irule_at Any) >>
        simp[]) >>
     `t' = t` by metis_tac[pairTheory.PAIR_EQ, venomExecSemanticsTheory.exec_result_11] >>
     qpat_x_assum `t' = t` SUBST_ALL_TAC >>
     drule_all run_inst_seq_gas_origin_ptr_path >>
     disch_then (qspec_then `explicit` mp_tac) >> simp[Abbr `z`]) >>
  `allocas_from lo z /\ lo <= z.vs_alloca_next` by
    (qpat_assum `!H. valid_horizon _ _ H _ ==> gas_origin_ptr_path _ _ _ _`
       (drule_then assume_tac) >>
     qpat_assum `ghost_inv_at_mods _ _ _ _ _ _ _ _ s`
       (strip_assume_tac o REWRITE_RULE [ghost_inv_at_mods_def]) >>
     drule gasOriginPtrLabelsTheory.member_origin_allocas_from >>
     disch_then (qspec_then `lo` mp_tac) >> simp[]) >>
  `lo <= b` by
    (`z.vs_allocas = u.vs_allocas` by
       (qpat_assum `t with <|vs_vars := _; vs_memory := _|> = u` mp_tac >>
        simp[Abbr `z`, Once venom_state_component_equality]) >>
     fs[ptrDisciplineTheory.allocas_from_def] >> first_assum drule >> simp[]) >>
  `word_size (LENGTH str) <= word_size ml` by
    metis_tac[exprSimPropsTheory.word_size_monotone] >>
  `b < dimword (:256)` by decide_tac >>
  `!a len. a+len <= b \/ b+32+32*word_size ml <= a ==>
    mem_bytes_at a len t.vs_memory = mem_bytes_at a len s.vs_memory` by
    (rpt strip_tac >>
     qpat_assum `!a len. _ ==> mem_bytes_at a len t.vs_memory = _`
       (qspecl_then [`a`,`len`] mp_tac) >>
     (impl_tac >- decide_tac) >> simp[]) >>
  `!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s /\
       FLOOKUP G' x = FLOOKUP G x /\ op_taint tn' (Var x) = op_taint tn (Var x)` by
    (rpt strip_tac >> fs[op_taint_def] >> metis_tac[]) >>
  `!name a len. local_region cenv es.scopes s name a len ==>
      regions_disjoint b (32+32*word_size ml) a len` by
    (drule_all literal_ptr_local_region_frame >> metis_tac[]) >>
  `!i. i < b \/ b+32+32*word_size ml <= i ==> (i IN tn'.t_mem <=> i IN tn.t_mem)` by
    (rpt strip_tac >> simp[] >>
     `i NOTIN dirty` by
       (qpat_assum `dirty SUBSET _` (mp_tac o REWRITE_RULE [pred_setTheory.SUBSET_DEF]) >>
        disch_then (qspec_then `i` mp_tac) >> simp[] >> decide_tac) >>
     gvs[] >> decide_tac) >>
  qexistsl_tac [`z`,`p`,`G'`,`tn'`] >>
  conj_tac >- simp[compile_reason_message_def, comp_bind_def, comp_return_def] >>
  conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac >- (pure_rewrite_tac[vv_operand_def, base_ptr_def] >>
               simp_tac (srw_ss()) [] >> first_assum ACCEPT_TAC) >>
  conj_tac >- simp[vv_location_def, base_ptr_def] >>
  conj_tac >- suspend "fresh" >>
  conj_tac >- suspend "history" >>
  ntac 4 (conj_tac >- simp[Abbr `z`]) >>
  conj_tac >- suspend "kept" >>
  conj_tac >- suspend "store" >>
  conj_tac >- suspend "actual_ptr" >>
  conj_tac >- suspend "capacity_ptr" >>
  conj_tac >- suspend "buf" >>
  gen_tac >> strip_tac >>
  conj_tac >-
    (qpat_assum `!H. valid_horizon _ _ H _ ==> gas_origin_ptr_path _ _ _ _`
      (drule_then ACCEPT_TAC)) >>
  conj_tac >- suspend "source" >>
  suspend "linked_ghost"
QED

Resume reason_literal_message_entry_mods[fresh]:
  `p' = p` by fs[] >>
  `sh'.cs_next_var <= sb.cs_next_var` by
    (qspecl_then [`Var p'`,`MAP (n2w o ORD) str`,`32`,`sh'`] mp_tac
       ci_mono_compile_store_byte_chunks >> simp[ci_mono_def]) >>
  irule freshWritesTheory.not_fresh_at_mono >> qexists_tac `sh'` >> gvs[]
QED

Resume reason_literal_message_entry_mods[history]:
  simp_tac bool_ss [Abbr `z`] >>
  `LENGTH sb.cs_current_insts = s.vs_inst_idx + LENGTH (emitted_insts sa sb)` by simp[] >>
  pop_assum SUBST1_TAC >> irule alloca_history_run_inst_seq >>
  goal_assum (drule_at (Pat `run_inst_seq _ _ = _`)) >>
  `EVERY (\i. ~is_terminator i.inst_opcode) (emitted_insts sa sb)` by
    (qpat_assum `EVERY (\i. i.inst_opcode <> INVOKE /\ _) _` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >> simp[EVERY_MEM]) >>
  simp[] >> fs[stmt_state_rel_def, rich_listTheory.IS_PREFIX_APPEND, is_terminator_def]
QED

Resume reason_literal_message_entry_mods[kept]:
  `ghost_kept cenv es sa G tn s G' tn'` by
    (irule exprSimPtrLiteralBufferTheory.ghost_kept_disjoint_taint_frame >>
     conj_tac >- simp[] >> qexistsl_tac [`b`,`32+32*word_size ml`] >>
     rpt conj_tac >> TRY (first_assum ACCEPT_TAC)
     >- (rpt strip_tac >> qpat_assum `!aid a len. aid < _ /\ _ ==> _`
         (drule_all_then ACCEPT_TAC)) >>
     simp[pred_setTheory.SUBSET_DEF] >> qx_gen_tac `i` >> strip_tac >>
     qpat_assum `dirty SUBSET _`
       (mp_tac o Q.SPEC `i` o REWRITE_RULE [pred_setTheory.SUBSET_DEF]) >>
     fs[] >> decide_tac) >>
  qpat_x_assum `ghost_kept _ _ _ _ _ _ _ _` mp_tac >>
  pure_rewrite_tac[ghost_kept_at_def, ghost_kept_def] >>
  strip_tac >> rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
  qx_gen_tac `i` >> strip_tac >> `i < b` by decide_tac >> fs[]
QED

Resume reason_literal_message_entry_mods[store]:
  `b+32+32*word_size ml <= t.vs_alloca_next` by
    (`u.vs_alloca_next = t.vs_alloca_next` by
       (qpat_assum `t with <|vs_vars := _; vs_memory := _|> = u` mp_tac >>
        simp[Once venom_state_component_equality]) >>
     qpat_assum `stmt_state_rel _ _ _ _ _ _ u`
       (strip_assume_tac o MATCH_MP stmt_state_rel_local_ptrs_alloca) >>
     fs[venomMemDefsTheory.alloca_inv_def, venomMemDefsTheory.alloca_next_valid_def] >>
     qpat_assum `!aid base sz. FLOOKUP u.vs_allocas aid = SOME (base,sz) ==> _`
       (drule_then assume_tac) >> decide_tac) >>
  qpat_assum `lookup_var p t = _`
    (assume_tac o REWRITE_RULE [lookup_var_def]) >>
  simp[expr_store_bound_def, evaluate_type_def, is_word_type_def,
       eval_operand_def, lookup_var_def, exprSimPropsTheory.val_store_size_def, w2n_n2w,
       Abbr `z`] >>
  decide_tac
QED

Resume reason_literal_message_entry_mods[actual_ptr]:
  irule reason_literal_pointer >> simp[] >>
  qexistsl_tac [`dirty`,`ml`,`tn`] >> simp[Abbr `z`] >>
  fs[lookup_var_def]
QED

Resume reason_literal_message_entry_mods[capacity_ptr]:
  irule reason_literal_pointer >> simp[] >>
  qexistsl_tac [`dirty`,`ml`,`tn`] >> simp[Abbr `z`] >>
  fs[lookup_var_def]
QED

Resume reason_literal_message_entry_mods[buf]:
  irule literal_site_ptr_buf_ok >>
  qexistsl_tac [`b`,`32+32*word_size ml`,`n2w b`] >>
  simp[lookup_var_def, w2n_n2w, lowered_value_type_def, expr_type_def,
       type_memory_bytes_def, type_slot_size_def] >>
  fs[vfmConstantsTheory.word_size_def, Abbr `z`, lookup_var_def]
QED

Resume reason_literal_message_entry_mods[source]:
  qpat_assum `!H. valid_horizon _ _ H _ ==> stmt_state_rel _ _ _ _ _ _ _ /\ _`
    (drule_then strip_assume_tac) >>
  drule_all reason_literal_buffer_ptr_run >>
  disch_then (qspecl_then [`tn`,`func`,`PG`,`G`,`DF H`]
    (strip_assume_tac o REWRITE_RULE [LENGTH_MAP])) >>
  `t' = t` by metis_tac[venomExecSemanticsTheory.exec_result_11] >>
  qpat_x_assum `t' = t` SUBST_ALL_TAC >>
  `p'' = p` by metis_tac[operand_11] >>
  qpat_x_assum `p'' = p` SUBST_ALL_TAC >>
  `b' < dimword (:256)` by decide_tac >>
  `b' = b` by
    (qpat_assum `lookup_var p t = SOME (n2w b')` mp_tac >>
     qpat_assum `lookup_var p t = SOME (n2w b)` (fn th => pure_rewrite_tac[th]) >>
     simp[w2n_n2w, n2w_11]) >>
  qpat_x_assum `b' = b` SUBST_ALL_TAC >>
  `val_wf (BaseTV (StringT ml)) (StringV str) /\
   val_in_memory (BaseTV (StringT ml)) (StringV str) b t.vs_memory /\
   val_footprint (BaseTV (StringT ml)) (StringV str) <= 32+32*word_size (LENGTH str)` by
    (drule_all (SRULE [] (Q.INST [`tn` |-> `tn with t_mem := tn.t_mem UNION dirty`]
      (SPEC_ALL literal_ptr_string_representation))) >> simp[]) >>
  `vv_post H ctx func cenv cx (Literal (BaseT (StringT ml)) (StringL str))
    es sa sb s es (Value (StringV str))
    (LocatedValue (expr_type (Literal (BaseT (StringT ml)) (StringL str)))
       (base_ptr buf)) z` by
    (simp_tac bool_ss [Abbr `z`] >> irule literal_ptr_memory_vv_frame_post >>
     simp[expr_type_def, evaluate_type_def, post_value_type_def, is_word_type_def] >>
     qexistsl_tac [`32+32*word_size ml`, `p'`, `sh''`, `u'`, `n2w b`] >>
     gvs[w2n_n2w, eval_operand_def] >>
     rpt conj_tac
     >- first_assum ACCEPT_TAC
     >- first_assum ACCEPT_TAC
     >- (rpt strip_tac >>
         qpat_assum `!a len. _ ==> mem_bytes_at a len t.vs_memory = mem_bytes_at a len s.vs_memory` irule >>
         decide_tac)
     >- (qspec_then `ml` mp_tac exprSimPropsTheory.le_word_size_mul >> decide_tac)
     >- (simp[type_slot_size_def] >> decide_tac) >>
     first_assum irule >> simp[]) >>
  drule expr_post_of_vv_post_memory >> simp[base_ptr_def, expr_type_def, is_word_type_def]
QED

Resume reason_literal_message_entry_mods[linked_ghost]:
  qpat_assum `!H. valid_horizon _ _ H _ ==> stmt_state_rel _ _ _ _ _ _ _ /\ _`
    (drule_then strip_assume_tac) >>
  drule_all reason_literal_static_run >> strip_tac >>
  `stor_taint_ok_at (DF H) tn' z` by
    (qpat_assum `ghost_inv_at_mods (DF H) _ _ _ _ _ _ _ _`
       (strip_assume_tac o REWRITE_RULE [ghost_inv_at_mods_def]) >>
     qpat_assum `stor_taint_ok_at (DF H) tn s`
       (strip_assume_tac o REWRITE_RULE [stor_taint_ok_at_def]) >>
     simp[stor_taint_ok_at_def, Abbr `z`]) >>
  drule_then strip_assume_tac stmt_state_rel_local_ptrs_alloca >>
  irule reason_copy_ghost_mods >>
  qpat_assum `ghost_inv_at_mods (DF H) _ _ _ _ _ _ _ _` (irule_at Any) >>
  qexistsl_tac [`b`,`sa`,`32+32*word_size ml`,`func`] >>
  simp[] >> fs[Abbr `z`, regions_disjoint_def, lookup_var_def] >>
  conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac >- first_assum ACCEPT_TAC >>
  qx_gen_tac `j` >> disch_tac >>
  qpat_assum `!i. _ ==> (i IN tn'.t_mem <=> i IN tn.t_mem)`
    (qspec_then `j` mp_tac) >>
  impl_tac >- first_assum ACCEPT_TAC >>
  simp[] >> `j < b \/ b + (32 * word_size (LENGTH str) + 32) <= j` by decide_tac >>
  gvs[]
QED

Finalise reason_literal_message_entry_mods
