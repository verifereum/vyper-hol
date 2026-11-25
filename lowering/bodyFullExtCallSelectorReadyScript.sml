Theory bodyFullExtCallSelectorReady
Ancestors
  bodyFullExtCallBufferSetup bodyFullExtCallPacking calldataOverwritePtr
  typedCopyOriginPtrFields typedMemoryCopy exprSimAlloc emitHelperProps
  exprLoweringProps fragGasOriginPtrLoop fragGasOriginPtrDead bodyPtrDefs
  ptrDiscipline ptrSafeRun venomState memoryReadProps words pred_set
  decoderGhostFramePtr stateRelProj bodyPtrMakeArrayCopyStateFrame
  bodyPtrSignedConvertSourceFrame bodyFullPathHistory valueEncodingProps
  loweringShapeRules venomMemDefs finite_map exprSimExtCallCase exprSafeOperand
  bodyPtrBytestringBuiltinsWindowGhost exprSimProps loweringPosts bodyFullAllocaFresh
  fragExec venomExecSemantics bodyFullHashKeccakFixed[qualified,ignore_grammar]

Definition extcall_pack_raw_def:
  extcall_pack_raw a b s t <=>
    ?r. run_inst_seq (emitted_insts a b) s = OK r /\
        t = (r with vs_inst_idx := LENGTH b.cs_current_insts)
End

(* Retain the write's exact memory and ghost frame at the PC after MSTORE.
   The short selector-tail post forgets these once it has read the four bytes. *)
Theorem selector_write_frame[local]:
  emit_void MSTORE [Var root; Lit (calldata_method_id bs)] sa = ((),sm) /\
  fn_has_code sa sm func /\ fn_inst_ids_distinct func /\
  lookup_var root s = SOME w /\ ptr_covers G tn root s capacity /\
  32 <= capacity /\ w2n w + capacity <= s.vs_alloca_next /\
  allocas_from lo s /\ (ctx_has_dalloca ctx ==> allocas_below_fmp s) /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?m Gm tm.
    (!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG)
      (s,G,tn) [] (OK m,Gm,tm)) /\
    m = (mstore (w2n w) (calldata_method_id bs) s with
          vs_inst_idx := LENGTH sm.cs_current_insts) /\
    extcall_pack_raw sa sm s m /\
    ~m.vs_halted /\ m.vs_current_bb = sm.cs_current_bb /\
    m.vs_inst_idx = LENGTH sm.cs_current_insts /\
    m.vs_allocas = s.vs_allocas /\ m.vs_alloca_next = s.vs_alloca_next /\
    allocas_from lo m /\ ptr_covers Gm tm root m capacity /\
    (!x. lookup_var x m = lookup_var x s /\ FLOOKUP Gm x = FLOOKUP G x /\
      op_taint tm (Var x) = op_taint tn (Var x)) /\
    (!i. w2n w <= i /\ i < w2n w + 32 ==> i NOTIN tm.t_mem) /\
    tm.t_mem SUBSET tn.t_mem /\ tm.t_stor = tn.t_stor /\
    tm.t_trans = tn.t_trans /\ tm.t_imm = tn.t_imm
Proof
  strip_tac >>
  `ptr_covers G tn root s 32` by
    (gvs[ptr_covers_def] >> decide_tac) >>
  `eval_operand (Var root) s = SOME w /\
   eval_operand (Lit (calldata_method_id bs)) s = SOME (calldata_method_id bs) /\
   op_taint tn (Lit (calldata_method_id bs)) = {}` by
    simp[eval_operand_def, op_taint_def] >>
  drule_all clean_mstore_overwrite_prefix_uniform_origin_joint >>
  disch_then (qspec_then `PG` (qx_choose_then `m` (qx_choose_then `Gm`
    (qx_choose_then `tm` strip_assume_tac)))) >>
  `step_inst_base (mk_inst sa.cs_next_id MSTORE
    [Var root;Lit (calldata_method_id bs)] []) s =
    OK (mstore (w2n w) (calldata_method_id bs) s)` by (irule step_MSTORE >> simp[]) >>
  `m with vs_inst_idx := s.vs_inst_idx = mstore (w2n w) (calldata_method_id bs) s` by
    (drule emitted_insts_emit_void >> strip_tac >> fs[run_inst_seq_def]) >>
  `m = (mstore (w2n w) (calldata_method_id bs) s with
          vs_inst_idx := LENGTH sm.cs_current_insts)` by
    (qpat_assum `m with vs_inst_idx := _ = _`
       (mp_tac o AP_TERM ``\t:venom_state. t with vs_inst_idx := LENGTH sm.cs_current_insts``) >>
     simp[venom_state_component_equality]) >>
  `!x. lookup_var x m = lookup_var x s` by simp[lookup_var_def,mstore_def] >>
  `ptr_covers Gm tm root m capacity` by
    (irule ptr_covers_frame >> metis_tac[]) >>
  `allocas_from lo m` by (gvs[allocas_from_def] >> metis_tac[]) >>
  `w2n w + 32 <= s.vs_alloca_next` by decide_tac >>
  `extcall_pack_raw sa sm s m` by
    (simp[extcall_pack_raw_def] >> qexists_tac `mstore (w2n w) (calldata_method_id bs) s` >>
     drule emitted_insts_emit_void >> simp[run_inst_seq_def]) >>
  qexistsl [`m`,`Gm`,`tm`] >> simp[] >> metis_tac[]
QED

(* The ADD leaves the just-written memory unchanged. Keep its record frame
   relative to the actual store state, not a separately chosen endpoint. *)
Theorem selector_suffix_frame[local]:
  emit_void MSTORE [Var root;Lit (calldata_method_id bs)] sa = ((),sm) /\
  emit_op ADD [Var root;Lit 28w] sm = (off,sb) /\
  fn_has_code sa sm func /\ fn_has_code sm sb func /\ fn_inst_ids_distinct func /\
  LENGTH bs = 4 /\ lookup_var root s = SOME w /\
  not_fresh_at sm root /\ ptr_covers G tn root s capacity /\ 32 <= capacity /\
  w2n w + capacity < dimword (:256) /\ w2n w + capacity <= s.vs_alloca_next /\
  allocas_from lo s /\ lo <= s.vs_alloca_next /\ (ctx_has_dalloca ctx ==> allocas_below_fmp s) /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?p t Gf tf m.
    off = Var p /\ not_fresh_at sb p /\ ptr_covers Gf tf p t 4 /\
    lookup_var p t = SOME (n2w (w2n w + 28)) /\
    ptr_covers Gf tf root t capacity /\ lookup_var root t = SOME w /\
    (!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG)
      (s,G,tn) [] (OK t,Gf,tf)) /\
    m = (mstore (w2n w) (calldata_method_id bs) s with
          vs_inst_idx := LENGTH sm.cs_current_insts) /\
    extcall_pack_raw sa sm s m /\ extcall_pack_raw sm sb m t /\
    typed_copy_state_frame sm 0 0 m t /\
    t.vs_memory = m.vs_memory /\
    venomState$read_memory (w2n w + 28) 4 t = bs /\
    (!i. w2n w + 28 <= i /\ i < w2n w + 32 ==> i NOTIN tf.t_mem) /\
    tf.t_mem SUBSET tn.t_mem /\ tf.t_stor = tn.t_stor /\
    tf.t_trans = tn.t_trans /\ tf.t_imm = tn.t_imm /\
    t.vs_allocas = s.vs_allocas /\ t.vs_alloca_next = s.vs_alloca_next /\
    ~t.vs_halted /\ t.vs_current_bb = sb.cs_current_bb /\
    t.vs_inst_idx = LENGTH sb.cs_current_insts /\
    (!x. not_fresh_at sm x ==>
      lookup_var x t = lookup_var x s /\ FLOOKUP Gf x = FLOOKUP G x /\
      op_taint tf (Var x) = op_taint tn (Var x))
Proof
  strip_tac >> drule_all selector_write_frame >>
  disch_then (qspecl_then [`explicit`,`PG`]
    (qx_choose_then `m` (qx_choose_then `Gm` (qx_choose_then `tm` strip_assume_tac)))) >>
  `lookup_var root m = SOME w` by metis_tac[] >>
  `lo <= m.vs_alloca_next /\ w2n w + 28 < dimword (:256) /\
   28 + 4 <= capacity` by decide_tac >>
  `ctx_has_dalloca ctx ==> allocas_below_fmp m` by
    (qpat_assum `m = _` SUBST1_TAC >>
     qpat_assum `ctx_has_dalloca ctx ==> allocas_below_fmp s` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >>
     simp[allocas_below_fmp_def, mstore_def] >> metis_tac[]) >>
  `emit_op ADD [Var root;Lit (n2w 28)] sm = (off,sb)` by simp[] >>
  drule_all (Q.SPECL [`root`,`28`,`4`,`capacity`]
    typed_copy_origin_ptr_add_path_with_raw_endpoint) >>
  disch_then (qspecl_then [`explicit`,`PG`,`0`,`0`] strip_assume_tac) >>
  `extcall_pack_raw sm sb m t` by (simp[extcall_pack_raw_def] >> metis_tac[]) >>
  `!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG)
      (s,G,tn) [] (OK t,Gf,tnf)` by
    (gen_tac >> irule gas_origin_ptr_path_trans >> qexistsl [`Gm`,`m`,`tm`] >>
     conj_tac >- simp[] >>
     irule gas_origin_ptr_path_from_no_dead >> simp[]) >>
  `lookup_var root t = SOME w /\ FLOOKUP Gf root = FLOOKUP Gm root /\
   op_taint tnf (Var root) = op_taint tm (Var root)` by metis_tac[] >>
  `ptr_covers Gf tnf root t capacity` by
    (irule ptr_covers_frame >> metis_tac[]) >>
  `t.vs_allocas = s.vs_allocas` by
    (qpat_assum `typed_copy_state_frame _ _ _ _ _`
       (strip_assume_tac o REWRITE_RULE [typed_copy_state_frame_def]) >>
     qpat_assum `t with <|vs_vars := _; vs_memory := _; vs_prev_bb := _;
                          vs_current_bb := _; vs_inst_idx := _|> = m`
       (mp_tac o AP_TERM ``venom_state_vs_allocas``) >> simp[]) >>
  `venomState$read_memory (w2n w + 28) 4 t = bs` by
    simp[read_memory_eq_mem_bytes_at,
      GSYM (REWRITE_RULE [read_memory_eq_mem_bytes_at] extcall_selector_store_read)] >>
  qexistsl [`p`,`t`,`Gf`,`tnf`,`m`] >> simp[] >> metis_tac[]
QED

(* The physical write is confined to the registered, nonlocal buffer. The
   successor of the ADD then differs only in variables and its cursor. *)
Theorem selector_suffix_stmt_rel[local]:
  stmt_state_rel H ctx func cenv cx es u /\
  compile_alloc_buffer n sa = (ba,sb) /\ fn_has_code sa sb func /\
  FLOOKUP u.vs_allocas sa.cs_next_id = SOME (a,n) /\ 32 <= n /\
  (!name b k. local_region cenv es.scopes u name b k ==>
    loweringStateRelDefs$regions_disjoint a n b k) /\
  local_ptrs_reserved cenv sm /\
  m = (mstore a (calldata_method_id bs) u with vs_inst_idx := idx) /\
  typed_copy_state_frame sm 0 0 m t /\ t.vs_memory = m.vs_memory ==>
  stmt_state_rel H ctx func cenv cx es t
Proof
  strip_tac >>
  `stmt_state_rel H ctx func cenv cx es (mstore a (calldata_method_id bs) u)` by
    (drule_all buffer_alloc_code >> strip_tac >>
     irule literal_mstore_state_rel >> reverse conj_tac >- simp[] >>
     qexistsl [`a`, `mk_inst sa.cs_next_id ALLOCA [Lit (n2w n)]
                                  [STRING #"%" (toString sa.cs_next_var)]`, `n`] >>
     simp[venomInstTheory.mk_inst_def] >>
     qpat_assum `!name b k. local_region _ _ _ _ _ _ ==> _`
       (ACCEPT_TAC o REWRITE_RULE [loweringStateRelDefsTheory.regions_disjoint_def])) >>
  `stmt_state_rel H ctx func cenv cx es m` by
    (qpat_assum `m = _` SUBST1_TAC >> simp[stmt_state_rel_inst_idx]) >>
  qpat_assum `typed_copy_state_frame _ _ _ _ _`
    (strip_assume_tac o REWRITE_RULE [typed_copy_state_frame_def]) >>
  qabbrev_tac `u' = t with <|vs_prev_bb := m.vs_prev_bb;
                            vs_current_bb := m.vs_current_bb;
                            vs_inst_idx := m.vs_inst_idx|>` >>
  `u' = m with vs_vars := t.vs_vars` by
    (qpat_assum `u' with <|vs_vars := _; vs_memory := _|> = m`
       (mp_tac o AP_TERM ``\s:venom_state. s with vs_vars := t.vs_vars``) >>
     simp[Abbr `u'`, venom_state_component_equality]) >>
  `stmt_state_rel H ctx func cenv cx es u'` by
    (irule stmt_state_rel_readonly_vars_pc >> qexistsl [`m`,`sm`] >>
     simp[] >> simp[lookup_var_def] >>
     fs[lookup_var_def]) >>
  fs[Abbr `u'`, literal_stmt_state_rel_cursor]
QED

Theorem selector_packing_run[local]:
  compile_alloc_buffer n sa = (ba,sb) /\
  emit_void MSTORE [ba.buf_operand; Lit (calldata_method_id bs)] sb = ((),sm) /\
  emit_op ADD [ba.buf_operand; Lit 28w] sm = (off,sp) /\
  fn_has_code sa sb func /\ fn_has_code sb sm func /\ fn_has_code sm sp func /\
  fn_inst_ids_distinct func /\ LENGTH bs = 4 /\ 32 <= n /\ n < dimword (:256) /\
  stmt_state_rel (H0 : (bool # bytes32 # type_value) list # num list)
    ctx func cenv cx ee s /\ local_ptrs_reserved cenv sa /\
  alloca_history func s /\ allocas_from lo s /\ lo <= s.vs_alloca_next /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?q p w t Gf tf.
    ba.buf_operand = Var q /\ off = Var p /\ not_fresh_at sp q /\ not_fresh_at sp p /\
    lookup_var q t = SOME w /\ lookup_var p t = SOME (n2w (w2n w + 28)) /\
    ptr_covers Gf tf q t n /\ ptr_covers Gf tf p t 4 /\
    FLOOKUP t.vs_allocas sa.cs_next_id = SOME (w2n w,n) /\
    lo <= w2n w /\ w2n w + n < dimword (:256) /\ w2n w + n <= t.vs_alloca_next /\
    venomState$read_memory (w2n w + 28) 4 t = bs /\
    (!i. w2n w + 28 <= i /\ i < w2n w + 32 ==> i NOTIN tf.t_mem) /\
    (!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG)
         (s,G,tn) [] (OK t,Gf,tf)) /\
    (!H : (bool # bytes32 # type_value) list # num list.
       stmt_state_rel H ctx func cenv cx ee s ==> stmt_state_rel H ctx func cenv cx ee t) /\
    ~t.vs_halted /\ t.vs_current_bb = sp.cs_current_bb /\
    t.vs_inst_idx = LENGTH sp.cs_current_insts /\
    alloca_history func t /\ allocas_from lo t /\ s.vs_alloca_next <= t.vs_alloca_next /\
    sa.cs_next_var <= sp.cs_next_var /\ sa.cs_next_id < sp.cs_next_id /\
    (!aid ent. FLOOKUP s.vs_allocas aid = SOME ent ==> FLOOKUP t.vs_allocas aid = SOME ent) /\
    (!aid b k. aid < sa.cs_next_id /\ FLOOKUP t.vs_allocas aid = SOME (b,k) ==>
       loweringStateRelDefs$regions_disjoint (w2n w) n b k) /\
    (!name b k. local_region cenv ee.scopes s name b k ==>
       loweringStateRelDefs$regions_disjoint (w2n w) n b k) /\
    (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s /\
         FLOOKUP Gf x = FLOOKUP G x /\ op_taint tf (Var x) = op_taint tn (Var x)) /\
    (!a k. a+k <= w2n w \/ w2n w + 32 <= a ==>
       mem_bytes_at a k t.vs_memory = mem_bytes_at a k s.vs_memory) /\
    (!i. i < s.vs_alloca_next /\ i IN tf.t_mem ==> i IN tn.t_mem) /\
    tf.t_stor = tn.t_stor /\ tf.t_trans = tn.t_trans /\ tf.t_imm = tn.t_imm /\
    t.vs_accounts = s.vs_accounts /\ t.vs_transient = s.vs_transient /\
    t.vs_call_ctx = s.vs_call_ctx /\ t.vs_immutables = s.vs_immutables /\
    t.vs_code = s.vs_code /\ t.vs_labels = s.vs_labels /\ t.vs_requests = s.vs_requests /\
    (?u m. extcall_pack_raw sa sb s u /\ extcall_pack_raw sb sm u m /\
           extcall_pack_raw sm sp m t)
Proof
  strip_tac >>
  `ctx_has_dalloca ctx ==> allocas_below_fmp s` by
    (qpat_assum `stmt_state_rel H0 ctx func cenv cx ee s`
       (ACCEPT_TAC o MATCH_MP bodyFullHashKeccakFixedTheory.stmt_state_rel_allocas_below_fmp)) >>
  `ctx_has_dalloca ctx ==> allocas_below_fmp s /\
    s.vs_alloca_next + pending_alloca_size func s <= w2n s.vs_initial_fmp` by
    (qpat_assum `stmt_state_rel H0 ctx func cenv cx ee s`
       (mp_tac o MATCH_MP stmt_state_rel_fmp_room) >>
     simp[fmp_room_def] >> rpt strip_tac >> res_tac >> decide_tac) >>
  drule_all (INST_TYPE [``:'b`` |-> ``:256``]
     (SPEC_ALL alloc_buffer_origin_ptr_path_with_raw_endpoint)) >>
  disch_then (qspecl_then [`tn`,`explicit`,`PG`,`G`] (qx_choosel_then
    [`q`,`w`,`u`,`Gu`,`tu`,`raw`] strip_assume_tac)) >>
  `extcall_pack_raw sa sb s u` by (simp[extcall_pack_raw_def] >> metis_tac[]) >>
  qpat_x_assum `u = raw with vs_inst_idx := _` kall_tac >>
  qpat_x_assum `Gu = step_prov _ _ _ raw` kall_tac >>
  qpat_x_assum `tu = step_taint _ _ raw _` kall_tac >>
  `u.vs_memory = s.vs_memory /\ u.vs_halted = s.vs_halted /\
   u.vs_accounts = s.vs_accounts /\ u.vs_transient = s.vs_transient /\
   u.vs_call_ctx = s.vs_call_ctx /\ u.vs_immutables = s.vs_immutables /\
   u.vs_code = s.vs_code /\ u.vs_labels = s.vs_labels /\ u.vs_requests = s.vs_requests` by
    (qpat_assum `u with <|vs_vars := _; vs_allocas := _;
         vs_alloca_next := _; vs_inst_idx := _|> = s` (SUBST1_TAC o SYM) >> simp[]) >>
  `!i. i < s.vs_alloca_next /\ i IN tu.t_mem ==> i IN tn.t_mem` by
    (rpt strip_tac >> metis_tac[arithmeticTheory.NOT_LESS]) >>
  `lo <= w2n w` by metis_tac[allocas_from_def] >>
  `sa.cs_next_var <= sb.cs_next_var /\ sa.cs_next_id <= sb.cs_next_id` by
    (drule abiBuiltinAllocationTheory.abi_builtin_alloc_buffer_shape >> strip_tac >>
     drule emitted_insts_emit_op >> simp[]) >>
  `sb.cs_next_var = sm.cs_next_var /\ sb.cs_next_id < sm.cs_next_id /\
   sm.cs_next_var <= sp.cs_next_var /\ sm.cs_next_id < sp.cs_next_id` by
    (qpat_assum `emit_void _ _ _ = _` (mp_tac o REWRITE_RULE [emit_void_eq]) >>
     qpat_assum `emit_op _ _ _ = _` (mp_tac o REWRITE_RULE [emit_op_eq]) >>
     simp[] >> rpt strip_tac >> gvs[]) >>
  `not_fresh_at sm q /\ lo <= u.vs_alloca_next` by
    (conj_tac >- (irule freshWritesTheory.not_fresh_at_mono >> qexists `sb` >> simp[]) >>
     decide_tac) >>
  `emit_void MSTORE [Var q; Lit (calldata_method_id bs)] sb = ((),sm) /\
   emit_op ADD [Var q;Lit 28w] sm = (off,sp)` by metis_tac[] >>
  `stmt_state_rel H0 ctx func cenv cx ee u` by
    (qpat_assum `!H. stmt_state_rel H ctx func cenv cx ee s ==> stmt_state_rel H ctx func cenv cx ee u`
       (qspec_then `H0` (drule_then ACCEPT_TAC))) >>
  `ctx_has_dalloca ctx ==> allocas_below_fmp u` by
    (qpat_assum `stmt_state_rel H0 ctx func cenv cx ee u`
       (ACCEPT_TAC o MATCH_MP bodyFullHashKeccakFixedTheory.stmt_state_rel_allocas_below_fmp)) >>
  `~u.vs_halted` by simp[] >>
  drule_all selector_suffix_frame >>
  disch_then (qspecl_then [`explicit`,`PG`] (qx_choose_then `p` (qx_choose_then `t`
    (qx_choose_then `Gf` (qx_choose_then `tf` (qx_choose_then `m` strip_assume_tac)))))) >>
  `!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn) [] (OK t,Gf,tf)` by
    (gen_tac >> irule gas_origin_ptr_path_trans >> qexistsl [`Gu`,`u`,`tu`] >> simp[]) >>
  `alloca_history func t` by
    (irule body_full_path_alloca_history >>
     drule stmt_state_rel_local_ptrs_alloca >> metis_tac[]) >>
  `!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s /\
     FLOOKUP Gf x = FLOOKUP G x /\ op_taint tf (Var x) = op_taint tn (Var x)` by
    (rpt strip_tac >> `not_fresh_at sm x` by
      (irule freshWritesTheory.not_fresh_at_mono >> qexists `sa` >> simp[]) >> metis_tac[]) >>
  `!name b k. local_region cenv ee.scopes s name b k ==>
    loweringStateRelDefs$regions_disjoint (w2n w) n b k` by
    metis_tac[exprSimCopyTheory.copy_buffer_local_region_frame] >>
  `local_ptrs_reserved cenv sm` by (irule local_ptrs_reserved_next_var >> qexists `sa` >> simp[]) >>
  `!H : (bool # bytes32 # type_value) list # num list.
     stmt_state_rel H ctx func cenv cx ee s ==> stmt_state_rel H ctx func cenv cx ee t` by
    (qx_gen_tac `h` >> disch_tac >> `stmt_state_rel h ctx func cenv cx ee u` by
       (qpat_assum `!H. stmt_state_rel H ctx func cenv cx ee s ==> stmt_state_rel H ctx func cenv cx ee u`
          (qspec_then `h` mp_tac) >> simp[]) >>
     irule selector_suffix_stmt_rel >>
     qexistsl [`w2n w`,`ba`,`bs`,`LENGTH sm.cs_current_insts`,`m`,`n`,`sa`,`sb`,`sm`,`u`] >>
     simp[] >> rpt conj_tac >> first_assum ACCEPT_TAC) >>
  `FLOOKUP t.vs_allocas sa.cs_next_id = SOME (w2n w,n)` by simp[] >>
  `stmt_state_rel H0 ctx func cenv cx ee t` by
    (qpat_assum `!H. stmt_state_rel H ctx func cenv cx ee s ==> stmt_state_rel H ctx func cenv cx ee t`
       (qspec_then `H0` mp_tac) >> simp[]) >>
  `!aid b k. aid < sa.cs_next_id /\ FLOOKUP t.vs_allocas aid = SOME (b,k) ==>
       loweringStateRelDefs$regions_disjoint (w2n w) n b k` by
    (rpt strip_tac >> `sa.cs_next_id <> aid` by decide_tac >>
     qpat_assum `FLOOKUP t.vs_allocas aid = SOME (b,k)` mp_tac >>
     qpat_assum `FLOOKUP t.vs_allocas sa.cs_next_id = SOME _` mp_tac >>
     qpat_assum `sa.cs_next_id <> aid` mp_tac >>
     qpat_assum `stmt_state_rel H0 _ _ _ _ _ t`
       (mp_tac o CONJUNCT2 o MATCH_MP stmt_state_rel_local_ptrs_alloca) >>
     POP_ASSUM_LIST (K ALL_TAC) >>
     rewrite_tac[alloca_inv_def, allocas_non_overlapping_def,
                 loweringStateRelDefsTheory.regions_disjoint_def] >> metis_tac[]) >>
  `!a k. a+k <= w2n w \/ w2n w + 32 <= a ==>
       mem_bytes_at a k t.vs_memory = mem_bytes_at a k s.vs_memory` by
    (rpt gen_tac >> disch_tac >>
     qpat_assum `t.vs_memory = m.vs_memory` SUBST1_TAC >>
     qpat_assum `m = _` SUBST1_TAC >>
     qpat_assum `u.vs_memory = s.vs_memory` (SUBST1_TAC o SYM) >>
     simp[NoAsms] >> irule mstore_mem_bytes_at_disjoint >> first_assum ACCEPT_TAC) >>
  `!i. i < s.vs_alloca_next /\ i IN tf.t_mem ==> i IN tn.t_mem` by
    (rpt strip_tac >>
     `i IN tu.t_mem` by
       (qpat_assum `tf.t_mem SUBSET tu.t_mem`
          (qspec_then `i` mp_tac o REWRITE_RULE [SUBSET_DEF]) >> simp[]) >>
     qpat_assum `!j. j < s.vs_alloca_next /\ j IN tu.t_mem ==> j IN tn.t_mem`
       (qspec_then `i` mp_tac) >> simp[]) >>
  `t.vs_accounts = u.vs_accounts /\ t.vs_transient = u.vs_transient /\
   t.vs_call_ctx = u.vs_call_ctx /\ t.vs_immutables = u.vs_immutables /\
   t.vs_code = u.vs_code /\ t.vs_labels = u.vs_labels /\ t.vs_requests = u.vs_requests` by
    (qpat_assum `typed_copy_state_frame _ _ _ _ _`
       (strip_assume_tac o REWRITE_RULE [typed_copy_state_frame_def]) >>
     qpat_assum `t with <|vs_vars := _; vs_memory := _; vs_prev_bb := _;
                         vs_current_bb := _; vs_inst_idx := _|> = m`
       (mp_tac o AP_TERM ``\v:venom_state.
         (v.vs_accounts,v.vs_transient,v.vs_call_ctx,v.vs_immutables,
          v.vs_code,v.vs_labels,v.vs_requests)``) >> simp[mstore_def]) >>
  `not_fresh_at sp q` by
    (irule freshWritesTheory.not_fresh_at_mono >> qexists `sm` >> simp[]) >>
  `allocas_from lo t` by
    (qpat_assum `allocas_from lo u` mp_tac >>
     qpat_assum `t.vs_allocas = u.vs_allocas` (fn th =>
       rewrite_tac[allocas_from_def,th])) >>
  qexistsl [`q`,`p`,`w`,`t`,`Gf`,`tf`] >> rpt conj_tac >>
  FIRST [first_assum ACCEPT_TAC, (simp[] >> NO_TAC),
         (qexistsl [`u`,`m`] >> simp[] >> NO_TAC), decide_tac]
QED

(* Keep the selected default, including the provenance and robustness of
   a non-word default, at the physical packing successor. *)
Theorem selector_default_frame[local]:
  extcall_default_ready cx rt hasdef def dt dopt s /\
  eval_operand def t = eval_operand def s /\
  s.vs_alloca_next <= t.vs_alloca_next /\
  (!x. def = Var x ==> lookup_var x t = lookup_var x s /\
    FLOOKUP Gf x = FLOOKUP G x /\ op_taint tf (Var x) = op_taint tn (Var x)) /\
  (!dv. dopt = SOME dv /\ ~is_word_type dt ==>
    ptr_mem_ok cx dt dv def G tn s /\
    (type_memory_bytes cenv dt <> 0 ==>
      (?p. def = Var p /\ ptr_covers G tn p s (type_memory_bytes cenv dt)) /\
      (!w. eval_operand def s = SOME w ==>
            w2n w + type_memory_bytes cenv dt <= s.vs_alloca_next)) /\
    (?w tv. eval_operand def s = SOME w /\
      evaluate_type (get_tenv cx) dt = SOME tv /\ val_wf tv dv /\
      mem_bytes_at (w2n w) (type_memory_size tv) t.vs_memory =
        mem_bytes_at (w2n w) (type_memory_size tv) s.vs_memory /\
      (!i. w2n w <= i /\ i < w2n w + type_memory_size tv /\ i IN tf.t_mem ==>
        i IN tn.t_mem))) ==>
  extcall_default_ready cx rt hasdef def dt dopt t /\
  (!dv. dopt = SOME dv /\ ~is_word_type dt ==>
    ptr_mem_ok cx dt dv def Gf tf t /\
    (type_memory_bytes cenv dt <> 0 ==>
      (?p. def = Var p /\ ptr_covers Gf tf p t (type_memory_bytes cenv dt)) /\
      (!w. eval_operand def t = SOME w ==>
            w2n w + type_memory_bytes cenv dt <= t.vs_alloca_next)))
Proof
  strip_tac >> conj_tac
  >- (fs[extcall_default_ready_def] >> rpt strip_tac >>
      qpat_assum `!d. dopt = SOME d ==> _` drule >> strip_tac >> simp[] >>
      `expr_val_rel cx dt d def t` by
        (Cases_on `is_word_type dt` >- fs[expr_val_rel_def] >>
         irule expr_val_rel_mem_agree >> metis_tac[]) >>
      gvs[] >> rpt strip_tac >> res_tac >> decide_tac) >>
  rpt gen_tac >> strip_tac >>
  qpat_assum `!dv. dopt = SOME dv /\ ~is_word_type dt ==> _`
    (drule_all_then strip_assume_tac) >> conj_tac
  >- (simp[ptr_mem_ok_def] >> rpt gen_tac >> strip_tac >>
      qpat_assum `ptr_mem_ok _ _ _ _ _ _ _` (mp_tac o REWRITE_RULE [ptr_mem_ok_def]) >>
      disch_then (drule_all_then strip_assume_tac)
      >- (rpt strip_tac >> irule robust_val_in_memory_window_transport >>
          conj_tac >- first_assum ACCEPT_TAC >>
          qexistsl [`tn.t_mem`,`tf.t_mem`,`type_memory_size tv`,
                    `s.vs_memory`,`t.vs_memory`] >> simp[val_footprint_le]) >>
      metis_tac[]) >>
  strip_tac >>
  qpat_assum `type_memory_bytes cenv dt <> 0 ==> _` drule >> strip_tac >>
  conj_tac >- (qexists `p` >> simp[] >> irule ptr_covers_frame >> metis_tac[]) >>
  rpt strip_tac >> gvs[] >> first_x_assum drule >> decide_tac
QED

(* The selector-only branch of extcall_request_buffer_layout.  The three
   compiler equations select the allocation, store and final offset cuts;
   the positional list is empty, independently of the evaluated keywords. *)
Theorem extcall_selector_packing_ready_with_raw_endpoints:
  vals = [] /\ LENGTH vals = LENGTH argvs /\ LENGTH argvs = LENGTH arg_types /\
  mid = w2n (calldata_method_id
    (function_selector fname (vyper_to_abi_types (get_tenv cx) arg_types))) /\
  compile_alloc_buffer ((if abi > cap then abi else cap) + 32) se = (ba,sb) /\
  emit_void MSTORE [ba.buf_operand;Lit (n2w mid)] sb = ((),sm) /\
  emit_op ADD [ba.buf_operand;Lit 28w] sm = (off,sp) /\
  fn_has_code se sb func /\ fn_has_code sb sm func /\ fn_has_code sm sp func /\
  fn_inst_ids_distinct func /\
  (if abi > cap then abi else cap) + 32 < dimword (:256) /\
  (?H. valid_horizon cx st0 H ee.storage_trace) /\
  (!H. valid_horizon cx st0 H ee.storage_trace ==>
       stmt_state_rel H ctx func cenv cx ee s /\ storage_well_formed_on cx ee (FST H) /\
       ghost_inv_at (DF H) lo d cenv cx ee G tn s) /\
  stmt_state_rel H0 ctx func cenv cx es s0 /\
  wb_frame cenv es ee sa s0 s /\ MAP FDOM es.scopes = MAP FDOM ee.scopes /\
  local_ptrs_reserved cenv sa /\ sa.cs_next_var <= se.cs_next_var /\
  sa.cs_next_id <= se.cs_next_id /\
  ~s.vs_halted /\ s.vs_current_bb = se.cs_current_bb /\
  s.vs_inst_idx = LENGTH se.cs_current_insts /\ ee.gas_obs = [] /\
  outcomes_accounts_typed ee.outcomes /\ accounts_runtime_well_typed ee.accounts /\
  alloca_history func s /\ allocas_from lo s /\ lo <= s.vs_alloca_next /\
  s0.vs_alloca_next <= s.vs_alloca_next /\ ghost_kept_at lo cenv es sa G0 tn0 s0 G tn /\
  (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  EVERY (safe_operand se) [addr;value;gas;def] /\
  EVERY (\p. op_taint tn p = {}) [addr;value;gas;def] /\
  (?aw. eval_operand addr s = SOME aw /\ w2w aw = target) /\
  (stat <=> value_opt = NONE) /\
  (?vw. eval_operand value s = SOME vw /\
        w2n vw = (case value_opt of NONE => 0 | SOME k => k)) /\
  eval_operand gas s = SOME gw /\
  (!g. OPTION_BIND source_gas dest_NumV = SOME g ==> g = w2n gw) /\
  extcall_default_ready cx rt hasdef def dt dopt s /\
  (!dv. dopt = SOME dv /\ ~is_word_type dt ==>
    ptr_mem_ok cx dt dv def G tn s /\
    (type_memory_bytes cenv dt <> 0 ==>
      (?p. def = Var p /\ ptr_covers G tn p s (type_memory_bytes cenv dt)) /\
      (!w. eval_operand def s = SOME w ==>
           w2n w + type_memory_bytes cenv dt <= s.vs_alloca_next)) /\
    (?w aid tv. eval_operand def s = SOME w /\
      evaluate_type (get_tenv cx) dt = SOME tv /\ val_wf tv dv /\
      FLOOKUP s.vs_allocas aid = SOME (w2n w,type_memory_size tv) /\
      aid < se.cs_next_id)) ==>
  ?calldata t Gf tf.
    (?u m. extcall_pack_raw se sb s u /\ extcall_pack_raw sb sm u m /\
           extcall_pack_raw sm sp m t) /\
    build_ext_calldata (get_tenv cx) fname arg_types argvs = SOME calldata /\
    extcall_request_ready st0 ctx func cenv cx rt es sa s0 sp stat
      addr value gas ba.buf_operand off (Lit 4w) cap target value_opt calldata
      hasdef def dt dopt ee t /\
    (IS_SOME dopt /\ ~is_word_type dt ==>
      ?w aid tv. eval_operand def t = SOME w /\
        evaluate_type (get_tenv cx) dt = SOME tv /\
        FLOOKUP t.vs_allocas aid = SOME (w2n w,type_memory_size tv) /\
        aid < sp.cs_next_id) /\
    (!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG)
      (s,G,tn) [] (OK t,Gf,tf)) /\
    alloca_history func t /\ allocas_from lo t /\
    lo <= t.vs_alloca_next /\ s0.vs_alloca_next <= t.vs_alloca_next /\
    (!H. valid_horizon cx st0 H ee.storage_trace ==>
         ghost_inv_at (DF H) lo d cenv cx ee Gf tf t) /\
    ghost_kept_at lo cenv es sa G0 tn0 s0 Gf tf /\
    eval_operand gas t = SOME gw /\
    (!g. OPTION_BIND source_gas dest_NumV = SOME g ==> g = w2n gw) /\
    EVERY (\p. op_taint tf p = {}) [addr;value;gas;ba.buf_operand;off;Lit 4w;def] /\
    (!ao az. eval_operand off t = SOME ao /\ eval_operand (Lit 4w) t = SOME az ==>
      (az <> 0w ==> (?p. off = Var p /\ ptr_covers Gf tf p t (w2n az)) /\
                    w2n ao + w2n az <= t.vs_alloca_next) /\
      (!j. w2n ao <= j /\ j < w2n ao + w2n az ==> j NOTIN tf.t_mem)) /\
    (cap <> 0 ==> ?p. ba.buf_operand = Var p /\ ptr_covers Gf tf p t cap) /\
    (!dv. dopt = SOME dv /\ ~is_word_type dt ==>
      ptr_mem_ok cx dt dv def Gf tf t /\
      (type_memory_bytes cenv dt <> 0 ==>
        (?p. def = Var p /\ ptr_covers Gf tf p t (type_memory_bytes cenv dt)) /\
        (!w. eval_operand def t = SOME w ==>
             w2n w + type_memory_bytes cenv dt <= t.vs_alloca_next)))
Proof
  strip_tac >>
  `argvs = [] /\ arg_types = []` by (Cases_on `arg_types` >> Cases_on `argvs` >> gvs[]) >>
  qabbrev_tac `bs = function_selector fname []` >>
  qabbrev_tac `n = (if abi > cap then abi else cap) + 32` >>
  `build_ext_calldata (get_tenv cx) fname arg_types argvs = SOME bs /\
   LENGTH bs = 4 /\ n2w mid = calldata_method_id bs` by
    (simp[Abbr `bs`, vyperABITheory.build_ext_calldata_def, vyperABITheory.vyper_to_abi_type_def,
          vyperABITheory.vyper_to_abi_def, contractABITheory.enc_def, listTheory.REV_DEF,
          entryDispatchPropsTheory.function_selector_length]) >>
  `32 <= n /\ cap <= n` by (simp[Abbr `n`] >> IF_CASES_TAC >> decide_tac) >>
  `local_ptrs_reserved cenv se` by
    (irule local_ptrs_reserved_next_var >> qexists `sa` >> simp[]) >>
  qpat_assum `!H. valid_horizon _ _ H _ ==> _` (drule_then strip_assume_tac) >>
  `emit_void MSTORE [ba.buf_operand;Lit (calldata_method_id bs)] sb = ((),sm)` by metis_tac[] >>
  drule_all selector_packing_run >>
  disch_then (qspecl_then [`tn`,`explicit`,`PG`,`G`]
    (qx_choose_then `q` (qx_choose_then `p` (qx_choose_then `w`
      (qx_choose_then `t` (qx_choose_then `Gf` (qx_choose_then `tf` strip_assume_tac))))))) >>
  `local_ptrs_rel func cenv ee.scopes s /\ alloca_inv s` by
    (qpat_assum `stmt_state_rel H _ _ _ _ ee s`
       (mp_tac o MATCH_MP stmt_state_rel_local_ptrs_alloca) >> simp[]) >>
  `!b k. b+k <= s.vs_alloca_next /\
          loweringStateRelDefs$regions_disjoint (w2n w) n b k ==>
    mem_bytes_at b k t.vs_memory = mem_bytes_at b k s.vs_memory /\
    (!i. b <= i /\ i < b+k /\ i IN tf.t_mem ==> i IN tn.t_mem)` by
    (rpt gen_tac >> rewrite_tac[loweringStateRelDefsTheory.regions_disjoint_def] >>
     strip_tac >>
     (conj_tac
      >- (qpat_assum `!a k. a+k <= w2n w \/ _ ==> _` irule >> decide_tac)
      >> rpt strip_tac >> `i < s.vs_alloca_next` by decide_tac >> simp[])) >>
  `!name b k. local_region cenv ee.scopes s name b k ==>
    mem_bytes_at b k t.vs_memory = mem_bytes_at b k s.vs_memory /\
    (!i. b <= i /\ i < b+k /\ i IN tf.t_mem ==> i IN tn.t_mem)` by
    (rpt gen_tac >> disch_tac >>
     `b+k <= s.vs_alloca_next` by (drule_all bodyMemoryDefsTheory.body_local_region_frontier >> simp[]) >>
     qpat_assum `!name b k. local_region cenv ee.scopes s name b k ==> _`
       (drule_then assume_tac) >>
     qpat_assum `!b k. b+k <= s.vs_alloca_next /\ _ ==> _`
       (drule_all_then strip_assume_tac) >> simp[]) >>
  `!aid b k. aid < se.cs_next_id /\ FLOOKUP s.vs_allocas aid = SOME (b,k) ==>
    loweringStateRelDefs$regions_disjoint (w2n w) n b k /\
    mem_bytes_at b k t.vs_memory = mem_bytes_at b k s.vs_memory /\
    (!i. b <= i /\ i < b+k /\ i IN tf.t_mem ==> i IN tn.t_mem)` by
    (rpt gen_tac >> strip_tac >>
     `FLOOKUP t.vs_allocas aid = SOME (b,k)` by simp[] >>
     `b+k <= s.vs_alloca_next` by
       (qpat_assum `alloca_inv s` (mp_tac o CONJUNCT2 o REWRITE_RULE [alloca_inv_def]) >>
        rewrite_tac[alloca_next_valid_def] >> disch_then (drule_then ACCEPT_TAC)) >>
     `loweringStateRelDefs$regions_disjoint (w2n w) n b k` by
       (qpat_assum `!aid b k. aid < se.cs_next_id /\ FLOOKUP t.vs_allocas aid = SOME (b,k) ==> _`
          (drule_all_then ACCEPT_TAC)) >>
     qpat_assum `!b k. b+k <= s.vs_alloca_next /\ _ ==> _`
       (drule_all_then strip_assume_tac) >> simp[]) >>
  `mem_bytes_at 0 lo t.vs_memory = mem_bytes_at 0 lo s.vs_memory` by
    (qpat_assum `!a k. a+k <= w2n w \/ _ ==> _` irule >> simp[]) >>
  `wb_frame cenv es ee sa s0 t` by
    (drule_at (Pat `wb_frame _ _ _ _ _ _`) exprSimHashTheory.wb_frame_allocating_tail >>
     disch_then irule >> simp[] >> conj_tac
     >- (qexists `se` >> simp[] >> (metis_tac[]))
     >> qexists `ee.scopes` >> simp[] >> rpt strip_tac >>
     qpat_assum `!name b k. local_region cenv ee.scopes s name b k ==> _ /\ _`
       (drule_then strip_assume_tac) >> simp[]) >>
  `!op. safe_operand se op ==> eval_operand op t = eval_operand op s /\
      op_taint tf op = op_taint tn op /\ safe_operand sp op` by
    (Cases >> simp[eval_operand_def,op_taint_def,safe_operand_def] >>
     metis_tac[freshWritesTheory.not_fresh_at_mono]) >>
  `!dv. dopt = SOME dv /\ ~is_word_type dt ==>
    ?dw aid tv. eval_operand def s = SOME dw /\
      evaluate_type (get_tenv cx) dt = SOME tv /\ val_wf tv dv /\
      loweringStateRelDefs$regions_disjoint (w2n w) n (w2n dw) (type_memory_size tv) /\
      mem_bytes_at (w2n dw) (type_memory_size tv) t.vs_memory =
        mem_bytes_at (w2n dw) (type_memory_size tv) s.vs_memory /\
      (!i. w2n dw <= i /\ i < w2n dw + type_memory_size tv /\ i IN tf.t_mem ==>
           i IN tn.t_mem)` by
    (rpt strip_tac >> qpat_assum `!dv. dopt = SOME dv /\ ~is_word_type dt ==> _`
       (drule_all_then strip_assume_tac) >>
     qpat_assum `!aid b k. aid < se.cs_next_id /\ FLOOKUP s.vs_allocas aid = SOME (b,k) ==> _`
       (drule_all_then strip_assume_tac) >> metis_tac[]) >>
  `extcall_default_ready cx rt hasdef def dt dopt t /\
   (!dv. dopt = SOME dv /\ ~is_word_type dt ==>
      ptr_mem_ok cx dt dv def Gf tf t /\
      (type_memory_bytes cenv dt <> 0 ==>
        (?p. def = Var p /\ ptr_covers Gf tf p t (type_memory_bytes cenv dt)) /\
        (!w. eval_operand def t = SOME w ==>
             w2n w + type_memory_bytes cenv dt <= t.vs_alloca_next)))` by
    (irule selector_default_frame >> qexistsl [`G`,`s`,`tn`] >>
     qpat_assum `EVERY (safe_operand se) _`
       (strip_assume_tac o REWRITE_RULE [listTheory.EVERY_DEF]) >>
     qpat_assum `!op. safe_operand se op ==> _` (drule_all_then strip_assume_tac) >>
     simp[] >> conj_tac
     >- (rpt gen_tac >> disch_tac >>
         `not_fresh_at se x` by
           (qpat_assum `safe_operand se def`
              (mp_tac o Q.SPEC `x` o CONJUNCT1 o REWRITE_RULE [safe_operand_def]) >> simp[]) >>
         qpat_assum `!x. not_fresh_at se x ==> _` (drule_then strip_assume_tac) >> simp[])
     >> rpt gen_tac >> strip_tac >>
     qpat_assum `!dv. _ ==> ?dw aid tv. _` (drule_all_then strip_assume_tac) >>
     qpat_assum `!dv. _ ==> ptr_mem_ok _ _ dv _ _ _ _ /\ _`
       (drule_all_then (STRIP_ASSUME_TAC o cj 1)) >>
     qpat_assum `!dv. _ ==> ptr_mem_ok _ _ dv _ _ _ _ /\ _`
       (drule_all_then (STRIP_ASSUME_TAC o cj 2)) >> simp[]) >>
  `!H. valid_horizon cx st0 H ee.storage_trace ==>
       stmt_state_rel H ctx func cenv cx ee t /\ storage_well_formed_on cx ee (FST H)` by
    (rpt gen_tac >> disch_tac >>
     qpat_assum `!H. valid_horizon _ _ H _ ==> _` (drule_then strip_assume_tac) >> simp[]) >>
  `!x. not_fresh_at sa x ==>
       lookup_var x t = lookup_var x s /\ FLOOKUP Gf x = FLOOKUP G x /\
       op_taint tf (Var x) = op_taint tn (Var x)` by
    (rpt gen_tac >> disch_tac >>
     `not_fresh_at se x` by (irule freshWritesTheory.not_fresh_at_mono >> qexists `sa` >> simp[]) >>
     qpat_assum `!x. not_fresh_at se x ==> _` (drule_then ACCEPT_TAC)) >>
  `!i. i < lo /\ i IN tf.t_mem ==> i IN tn.t_mem` by
    (rpt strip_tac >> `i < s.vs_alloca_next` by decide_tac >> simp[]) >>
  `!H. valid_horizon cx st0 H ee.storage_trace ==> ghost_inv_at (DF H) lo d cenv cx ee Gf tf t` by
    (rpt gen_tac >> disch_tac >>
     qpat_assum `!H. valid_horizon _ _ H _ ==> _ /\ _ /\ ghost_inv_at _ _ _ _ _ _ _ _ _`
       (drule_then strip_assume_tac) >>
     rename1 `ghost_inv_at (DF J) lo d cenv cx ee G tn s` >>
     `stor_taint_ok_at (DF J) tf t` by
       (qpat_assum `ghost_inv_at (DF J) _ _ _ _ _ _ _ _`
          (mp_tac o cj 4 o REWRITE_RULE [ghost_inv_at_def]) >> simp[stor_taint_ok_at_def]) >>
     irule ghost_inv_at_local_window_transport >>
     `lo <= t.vs_alloca_next` by decide_tac >> simp[] >>
     qexistsl [`G`,`ee`,`func`,`s`,`sa`,`tn`] >> simp[] >> rpt conj_tac >>
     rpt strip_tac >>
     qpat_assum `!name b k. local_region cenv ee.scopes s name b k ==> _ /\ _`
       (drule_then strip_assume_tac) >> simp[arithmeticTheory.ADD_COMM]) >>
  `ghost_kept_at lo cenv es sa G0 tn0 s0 Gf tf` by
    (qpat_assum `ghost_kept_at lo cenv es sa G0 tn0 s0 G tn`
       (strip_assume_tac o REWRITE_RULE [ghost_kept_at_def]) >>
     `alloca_inv s0` by
       (qpat_assum `stmt_state_rel H0 ctx func cenv cx es s0`
          (mp_then Any mp_tac stmt_state_rel_local_ptrs_alloca) >> simp[]) >>
     simp[ghost_kept_at_def] >> rpt conj_tac
     >- (rpt gen_tac >> strip_tac >>
         rename1 `FLOOKUP s0.vs_allocas aid = SOME (b,k)` >>
         `b+k <= s0.vs_alloca_next` by
           (qpat_assum `alloca_inv s0` (mp_tac o CONJUNCT2 o REWRITE_RULE [alloca_inv_def]) >>
            rewrite_tac[alloca_next_valid_def] >> disch_then (drule_then ACCEPT_TAC)) >>
         `i < s.vs_alloca_next` by decide_tac >> `i IN tn.t_mem` by simp[] >>
         qpat_assum `!aid off sz i. FLOOKUP s0.vs_allocas aid = _ /\ _ ==> _`
           (qspecl_then [`aid`,`b`,`k`,`i`] mp_tac) >> simp[] >> (impl_tac >- first_assum ACCEPT_TAC) >> simp[])
     >- (rpt gen_tac >> strip_tac >>
         rename1 `local_region cenv es.scopes s0 name b k` >>
         `b+k <= s0.vs_alloca_next` by (drule_all bodyMemoryDefsTheory.body_local_region_frontier >> simp[]) >>
         `i < s.vs_alloca_next` by decide_tac >> `i IN tn.t_mem` by simp[] >>
         first_x_assum match_mp_tac >> metis_tac[])
     >> rpt strip_tac >> `i < s.vs_alloca_next` by decide_tac >> `i IN tn.t_mem` by simp[] >> simp[]) >>
  `local_ptrs_reserved cenv sp` by
    (irule local_ptrs_reserved_next_var >> qexists `se` >> simp[]) >>
  `eval_operand addr t = SOME aw /\ eval_operand value t = SOME vw /\
   eval_operand gas t = SOME gw /\ eval_operand def t = eval_operand def s /\
   EVERY (safe_operand sp) [addr;value;gas;def] /\
   EVERY (\p. op_taint tf p = {}) [addr;value;gas;def]` by
    (qpat_assum `EVERY (safe_operand se) _` (strip_assume_tac o REWRITE_RULE [listTheory.EVERY_DEF]) >>
     qpat_assum `EVERY (\p. op_taint tn p = {}) _` (strip_assume_tac o BETA_RULE o REWRITE_RULE [listTheory.EVERY_DEF]) >>
     simp[]) >>
  `w2n (n2w (w2n w + 28) : bytes32) = w2n w + 28` by
    (`w2n w + 28 < dimword(:256)` by decide_tac >> simp[wordsTheory.w2n_n2w]) >>
  `op_taint tf (Var q) = {} /\ op_taint tf (Var p) = {}` by
    (fs[ptr_covers_def]) >>
  `ptr_covers Gf tf q t cap` by
    (irule reasonCopySourcePtrTheory.ptr_covers_mono >> qexists `n` >> simp[]) >>
  `s0.vs_alloca_next <= t.vs_alloca_next /\ lo <= t.vs_alloca_next /\
   sa.cs_next_var <= sp.cs_next_var /\ sa.cs_next_id <= sp.cs_next_id` by decide_tac >>
  qpat_assum `EVERY (\p. op_taint tf p = {}) [addr;value;gas;def]`
    (strip_assume_tac o BETA_RULE o REWRITE_RULE [listTheory.EVERY_DEF]) >>
  qpat_assum `EVERY (safe_operand sp) [addr;value;gas;def]`
    (strip_assume_tac o REWRITE_RULE [listTheory.EVERY_DEF]) >>
  `op_taint tf (Lit 4w) = {}` by simp[op_taint_def] >>
  `IS_SOME dopt /\ ~is_word_type dt ==>
    ?dw aid tv. eval_operand def t = SOME dw /\
      evaluate_type (get_tenv cx) dt = SOME tv /\
      FLOOKUP t.vs_allocas aid = SOME (w2n dw,type_memory_size tv) /\
      aid < sp.cs_next_id` by
    (strip_tac >>
     `?dv. dopt = SOME dv` by metis_tac[optionTheory.IS_SOME_EXISTS] >>
     qpat_assum `!dv. dopt = SOME dv /\ ~is_word_type dt ==> _ /\ _ /\
       (?w aid tv. _ /\ _ /\ _ /\ FLOOKUP s.vs_allocas aid = SOME _ /\ _)`
       (drule_all_then (qx_choosel_then [`dw`,`aid`,`tv`] strip_assume_tac o cj 3)) >>
     qexistsl_tac [`dw`,`aid`,`tv`] >> simp[] >> decide_tac) >>
  `!name b k. local_region cenv ee.scopes t name b k ==>
    loweringStateRelDefs$regions_disjoint (w2n w) cap b k` by
    (rpt gen_tac >> disch_tac >>
     `local_region cenv ee.scopes s name b k` by
       (irule (iffLR exprSimCopyTheory.copy_buffer_local_region_frame) >>
        qexistsl [`se`,`t`] >> simp[]) >>
     qpat_assum `!name b k. local_region cenv ee.scopes s name b k ==> regions_disjoint _ _ _ _`
       (drule_then mp_tac) >>
     simp[loweringStateRelDefsTheory.regions_disjoint_def] >> decide_tac) >>
  `!name b k. local_region cenv es.scopes s0 name b k ==>
    loweringStateRelDefs$regions_disjoint (w2n w) cap b k` by
    (rpt gen_tac >> disch_tac >>
     drule_all wordArgsPtrTheory.wb_frame_local_regions >>
     disch_then (qspecl_then [`name`,`b`,`k`] assume_tac) >>
     first_x_assum match_mp_tac >> metis_tac[]) >>
  `!aid b k. aid < sa.cs_next_id /\ FLOOKUP t.vs_allocas aid = SOME (b,k) ==>
    loweringStateRelDefs$regions_disjoint (w2n w) cap b k` by
    (rpt gen_tac >> strip_tac >> `aid < se.cs_next_id` by decide_tac >>
     qpat_assum `!aid b k. aid < se.cs_next_id /\ FLOOKUP t.vs_allocas aid = SOME (b,k) ==> _`
       (drule_all_then mp_tac) >>
     simp[loweringStateRelDefsTheory.regions_disjoint_def] >> decide_tac) >>
  qexistsl [`bs`,`t`,`Gf`,`tf`] >>
  conj_tac >- (qexistsl_tac [`u`,`m`] >> simp[]) >>
  simp[extcall_request_ready_def,eval_operand_def,safe_operand_def] >>
  conj_tac >- (qexists `H` >> simp[]) >>
  conj_tac >- (qexistsl [`se.cs_next_id`,`n`] >> simp[]) >>
  conj_tac >- (first_assum ACCEPT_TAC) >>
  conj_tac >- (first_assum ACCEPT_TAC) >>
  conj_tac >- (first_assum ACCEPT_TAC) >>
  conj_tac
  >- (strip_tac >> rpt gen_tac >> strip_tac >>
      `stmt_state_rel H ctx func cenv cx ee t` by simp[] >>
      qpat_assum `stmt_state_rel H _ _ _ _ ee t`
        (assume_tac o MATCH_MP (cj 5 (iffLR stmt_state_rel_def))) >>
      `?inst. MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\
              inst.inst_id = se.cs_next_id` by
        (drule_all exprSimAllocTheory.buffer_alloc_code >> strip_tac >>
         goal_assum (drule_at Any) >> simp[venomInstTheory.mk_inst_def]) >>
      qpat_assum `immutable_alloca_sep func cenv cx ee t`
        (mp_tac o CONJUNCT2 o REWRITE_RULE [immutable_alloca_sep_def]) >>
      simp[] >> disch_then (qspecl_then [`name`,`tv`,`v`,`off'`] mp_tac) >>
      simp[] >> strip_tac >>
      `regions_disjoint off' (type_memory_size tv) (w2n w) n` by
        (qpat_assum `!i b sz. MEM i (fn_insts func) /\ _ ==> regions_disjoint _ _ _ _`
           (qspecl_then [`inst`,`w2n w`,`n`] mp_tac) >> simp[]) >>
      fs[loweringStateRelDefsTheory.regions_disjoint_def] >> decide_tac) >>
  rpt gen_tac >> strip_tac >>
  qpat_assum `!dv. _ ==> ?dw aid tv. _` (drule_all_then strip_assume_tac) >>
  `tv' = tv /\ dw = w'` by
    (qpat_x_assum `evaluate_type _ dt = SOME tv'` mp_tac >>
     qpat_x_assum `eval_operand def s = SOME dw` mp_tac >> simp[]) >>
  qpat_x_assum `tv' = tv` SUBST_ALL_TAC >>
  qpat_x_assum `dw = w'` SUBST_ALL_TAC >>
  drule_then assume_tac exprSimPropsTheory.val_footprint_le >>
  qpat_assum `regions_disjoint (w2n w) n _ _` mp_tac >>
  rewrite_tac[loweringStateRelDefsTheory.regions_disjoint_def] >> decide_tac
QED

(* The original ready interface forgets only the three exact runs. *)
Theorem extcall_selector_packing_ready:
  vals = [] /\ LENGTH vals = LENGTH argvs /\ LENGTH argvs = LENGTH arg_types /\
  mid = w2n (calldata_method_id
    (function_selector fname (vyper_to_abi_types (get_tenv cx) arg_types))) /\
  compile_alloc_buffer ((if abi > cap then abi else cap) + 32) se = (ba,sb) /\
  emit_void MSTORE [ba.buf_operand;Lit (n2w mid)] sb = ((),sm) /\
  emit_op ADD [ba.buf_operand;Lit 28w] sm = (off,sp) /\
  fn_has_code se sb func /\ fn_has_code sb sm func /\ fn_has_code sm sp func /\
  fn_inst_ids_distinct func /\
  (if abi > cap then abi else cap) + 32 < dimword (:256) /\
  (?H. valid_horizon cx st0 H ee.storage_trace) /\
  (!H. valid_horizon cx st0 H ee.storage_trace ==>
       stmt_state_rel H ctx func cenv cx ee s /\ storage_well_formed_on cx ee (FST H) /\
       ghost_inv_at (DF H) lo d cenv cx ee G tn s) /\
  stmt_state_rel H0 ctx func cenv cx es s0 /\
  wb_frame cenv es ee sa s0 s /\ MAP FDOM es.scopes = MAP FDOM ee.scopes /\
  local_ptrs_reserved cenv sa /\ sa.cs_next_var <= se.cs_next_var /\
  sa.cs_next_id <= se.cs_next_id /\
  ~s.vs_halted /\ s.vs_current_bb = se.cs_current_bb /\
  s.vs_inst_idx = LENGTH se.cs_current_insts /\ ee.gas_obs = [] /\
  outcomes_accounts_typed ee.outcomes /\ accounts_runtime_well_typed ee.accounts /\
  alloca_history func s /\ allocas_from lo s /\ lo <= s.vs_alloca_next /\
  s0.vs_alloca_next <= s.vs_alloca_next /\ ghost_kept_at lo cenv es sa G0 tn0 s0 G tn /\
  (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  EVERY (safe_operand se) [addr;value;gas;def] /\
  EVERY (\p. op_taint tn p = {}) [addr;value;gas;def] /\
  (?aw. eval_operand addr s = SOME aw /\ w2w aw = target) /\
  (stat <=> value_opt = NONE) /\
  (?vw. eval_operand value s = SOME vw /\
        w2n vw = (case value_opt of NONE => 0 | SOME k => k)) /\
  eval_operand gas s = SOME gw /\
  (!g. OPTION_BIND source_gas dest_NumV = SOME g ==> g = w2n gw) /\
  extcall_default_ready cx rt hasdef def dt dopt s /\
  (!dv. dopt = SOME dv /\ ~is_word_type dt ==>
    ptr_mem_ok cx dt dv def G tn s /\
    (type_memory_bytes cenv dt <> 0 ==>
      (?p. def = Var p /\ ptr_covers G tn p s (type_memory_bytes cenv dt)) /\
    (!w. eval_operand def s = SOME w ==>
           w2n w + type_memory_bytes cenv dt <= s.vs_alloca_next)) /\
    (?w aid tv. eval_operand def s = SOME w /\
      evaluate_type (get_tenv cx) dt = SOME tv /\ val_wf tv dv /\
      FLOOKUP s.vs_allocas aid = SOME (w2n w,type_memory_size tv) /\
      aid < se.cs_next_id)) ==>
  ?calldata t Gf tf.
    build_ext_calldata (get_tenv cx) fname arg_types argvs = SOME calldata /\
    extcall_request_ready st0 ctx func cenv cx rt es sa s0 sp stat
      addr value gas ba.buf_operand off (Lit 4w) cap target value_opt calldata
      hasdef def dt dopt ee t /\
    (IS_SOME dopt /\ ~is_word_type dt ==>
      ?w aid tv. eval_operand def t = SOME w /\
        evaluate_type (get_tenv cx) dt = SOME tv /\
        FLOOKUP t.vs_allocas aid = SOME (w2n w,type_memory_size tv) /\
        aid < sp.cs_next_id) /\
    (!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG)
      (s,G,tn) [] (OK t,Gf,tf)) /\
    alloca_history func t /\ allocas_from lo t /\
    lo <= t.vs_alloca_next /\ s0.vs_alloca_next <= t.vs_alloca_next /\
    (!H. valid_horizon cx st0 H ee.storage_trace ==>
         ghost_inv_at (DF H) lo d cenv cx ee Gf tf t) /\
    ghost_kept_at lo cenv es sa G0 tn0 s0 Gf tf /\
    eval_operand gas t = SOME gw /\
    (!g. OPTION_BIND source_gas dest_NumV = SOME g ==> g = w2n gw) /\
    EVERY (\p. op_taint tf p = {}) [addr;value;gas;ba.buf_operand;off;Lit 4w;def] /\
    (!ao az. eval_operand off t = SOME ao /\ eval_operand (Lit 4w) t = SOME az ==>
      (az <> 0w ==> (?p. off = Var p /\ ptr_covers Gf tf p t (w2n az)) /\
                    w2n ao + w2n az <= t.vs_alloca_next) /\
      (!j. w2n ao <= j /\ j < w2n ao + w2n az ==> j NOTIN tf.t_mem)) /\
    (cap <> 0 ==> ?p. ba.buf_operand = Var p /\ ptr_covers Gf tf p t cap) /\
    (!dv. dopt = SOME dv /\ ~is_word_type dt ==>
      ptr_mem_ok cx dt dv def Gf tf t /\
      (type_memory_bytes cenv dt <> 0 ==>
        (?p. def = Var p /\ ptr_covers Gf tf p t (type_memory_bytes cenv dt)) /\
        (!w. eval_operand def t = SOME w ==>
             w2n w + type_memory_bytes cenv dt <= t.vs_alloca_next)))
Proof
  disch_then (fn th =>
    mp_tac (MATCH_MP extcall_selector_packing_ready_with_raw_endpoints th)) >>
  disch_then (qx_choosel_then [`calldata`,`t`,`Gf`,`tf`]
    (CONJUNCTS_THEN2 (K all_tac) assume_tac)) >>
  qexistsl_tac [`calldata`,`t`,`Gf`,`tf`] >> first_assum ACCEPT_TAC
QED
