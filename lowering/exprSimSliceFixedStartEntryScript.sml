(* The ALLOCA/MSTORE capture before the first Slice bound. *)
Theory exprSimSliceFixedStartEntry
Ancestors
  bodyFullBuiltinSliceFixedCapture exprSimHash exprSimWordArgs exprSimAlloc
  bodyPtrBytestringBuiltinsWindowGhost bodyMemoryDefs exprSimProps
  bodyFullIfExpReach bodyFullHashKeccakFixed[qualified,ignore_grammar]
  stateRelProj vyperStorageFootprint loweringHalt exprLoweringProps
  loweringPosts ptrDiscipline valueEncodingProps venomMemDefs bodyPtrDefs
  compileEnv fragExec freshWrites venomState venomInst

(* The run premise is specialized to this compiler cut. The same capture
   witnesses are used for the path, the next-child entry and the byte view. *)
Theorem slice_fixed_capture_start_entry:
  (!(H:(bool # bytes32 # type_value) list # num list) (w:bytes32).
    stmt_state_rel H ctx func cenv cx mid t /\
    eval_operand src_op t = SOME w /\ op_taint tn1 src_op = {} /\
    allocas_from lo t /\ lo <= t.vs_alloca_next /\
    (ctx_has_dalloca ctx ==> allocas_below_fmp t /\
      t.vs_alloca_next + pending_alloca_size func t <= w2n t.vs_initial_fmp) ==>
    ?root p allocated captured G tn.
      buf.buf_operand = Var root /\ not_fresh_at sc root /\
      (!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (t,G1,tn1) []
        (OK captured,G,tn)) /\
      captured = mstore (w2n p) w allocated with vs_inst_idx := LENGTH sc.cs_current_insts /\
      captured.vs_current_bb = sc.cs_current_bb /\
      captured.vs_inst_idx = LENGTH sc.cs_current_insts /\ ~captured.vs_halted /\
      lookup_var root captured = SOME p /\ ptr_covers G tn root captured 32 /\
      mem_word_at (w2n p) captured.vs_memory = w /\
      mem_bytes_at (w2n p) 32 captured.vs_memory = word_to_bytes w T /\
      (!i. w2n p <= i /\ i < w2n p+32 ==> i NOTIN tn.t_mem) /\
      alloca_history func captured /\ allocas_from lo captured /\
      t.vs_alloca_next <= captured.vs_alloca_next /\
      FLOOKUP captured.vs_allocas st1.cs_next_id = SOME (w2n p,32) /\
      w2n p+32 < dimword (:256) /\ w2n p+32 <= captured.vs_alloca_next /\
      (!x. not_fresh_at st1 x ==>
        lookup_var x captured = lookup_var x t /\ FLOOKUP G x = FLOOKUP G1 x /\
        op_taint tn (Var x) = op_taint tn1 (Var x)) /\
      allocated with <|vs_vars := t.vs_vars;vs_allocas := t.vs_allocas;
        vs_alloca_next := t.vs_alloca_next;vs_inst_idx := t.vs_inst_idx|> = t /\
      (!H':(bool # bytes32 # type_value) list # num list.
        stmt_state_rel H' ctx func cenv cx mid t ==>
        stmt_state_rel H' ctx func cenv cx mid allocated) /\
      (!aid entry. FLOOKUP t.vs_allocas aid = SOME entry ==>
        FLOOKUP captured.vs_allocas aid = SOME entry) /\
      (!aid b len. aid < st1.cs_next_id /\ FLOOKUP t.vs_allocas aid = SOME (b,len) ==>
        regions_disjoint (w2n p) 32 b len) /\
      (!name b len. local_region cenv mid.scopes allocated name b len ==>
        regions_disjoint (w2n p) 32 b len) /\
      tn.t_stor = tn1.t_stor /\ tn.t_trans = tn1.t_trans /\ tn.t_imm = tn1.t_imm /\
      (!j. j < t.vs_alloca_next /\ j IN tn.t_mem ==> j IN tn1.t_mem)) /\
  expr_type src = BaseT (BytesT (Fixed m)) /\ m <= 32 /\
  value_has_type (BaseTV (BytesT (Fixed m))) (BytesV bs) /\
  storage_trace_domain cx st0 mid.storage_trace /\
  (!H. valid_horizon cx st0 H mid.storage_trace ==>
    expr_post H ctx func cenv cx src es sa st1 s0 mid (BytesV bs) src_op t /\
    ghost_inv_at (DF H) lo d cenv cx mid G1 tn1 t) /\
  ptr_val_ok cx (post_value_type cenv src) (BytesV bs) src_op G1 tn1 t /\
  compile_alloc_buffer 32 st1 = (buf,sm) /\
  emit_void MSTORE [buf.buf_operand;src_op] sm = ((),sc) /\
  fn_has_code st1 sc func /\ local_ptrs_reserved cenv st1 /\
  return_buf_frame d cenv st1 t /\
  (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at st1 x) /\
  (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at st1 x) /\
  (!bb. MEM bb func.fn_blocks ==> phi_prefix_length bb.bb_instructions = 0) /\
  (!fn inst u. frag_reachable ctx func t fn inst u ==> dalloca_fmp_headroom inst u) ==>
  ?root p w captured G tn.
    buf.buf_operand = Var root /\ not_fresh_at sc root /\
    (!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (t,G1,tn1) []
      (OK captured,G,tn)) /\
    (!H. valid_horizon cx st0 H mid.storage_trace ==>
      stmt_state_rel H ctx func cenv cx mid captured /\
      storage_well_formed_on cx mid (FST H) /\
      ghost_inv_at (DF H) lo d cenv cx mid G tn captured) /\
    captured.vs_current_bb = sc.cs_current_bb /\
    captured.vs_inst_idx = LENGTH sc.cs_current_insts /\ ~captured.vs_halted /\
    alloca_history func captured /\ allocas_from lo captured /\
    lo <= captured.vs_alloca_next /\ t.vs_alloca_next <= captured.vs_alloca_next /\
    (ctx_has_dalloca ctx ==> allocas_below_fmp captured) /\
    (!fn inst u. frag_reachable ctx func captured fn inst u ==> dalloca_fmp_headroom inst u) /\
    local_ptrs_reserved cenv sc /\ return_buf_frame d cenv sc captured /\
    (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sc x) /\
    (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sc x) /\
    LENGTH bs = m /\ TAKE (LENGTH bs) (word_to_bytes_be w) = bs /\
    mem_bytes_at (w2n p) (LENGTH bs) captured.vs_memory = bs /\
    MEM (mk_inst st1.cs_next_id ALLOCA [Lit 32w]
      [STRING #"%" (toString st1.cs_next_var)]) (fn_insts func) /\
    (!name b len. local_region cenv mid.scopes captured name b len ==>
      regions_disjoint (w2n p) 32 b len) /\
    lookup_var root captured = SOME p /\ ptr_covers G tn root captured 32 /\
    mem_word_at (w2n p) captured.vs_memory = w /\
    mem_bytes_at (w2n p) 32 captured.vs_memory = word_to_bytes w T /\
    (!i. w2n p <= i /\ i < w2n p+32 ==> i NOTIN tn.t_mem) /\
    FLOOKUP captured.vs_allocas st1.cs_next_id = SOME (w2n p,32) /\
    w2n p+32 < dimword (:256) /\ w2n p+32 <= captured.vs_alloca_next /\
    (!x. not_fresh_at st1 x ==>
      lookup_var x captured = lookup_var x t /\ FLOOKUP G x = FLOOKUP G1 x /\
      op_taint tn (Var x) = op_taint tn1 (Var x)) /\
    (!aid entry. FLOOKUP t.vs_allocas aid = SOME entry ==>
      FLOOKUP captured.vs_allocas aid = SOME entry) /\
    (!aid b len. aid < st1.cs_next_id /\ FLOOKUP t.vs_allocas aid = SOME (b,len) ==>
      regions_disjoint (w2n p) 32 b len) /\
    (!name b len. local_region cenv mid.scopes t name b len ==>
      regions_disjoint (w2n p) 32 b len) /\
    (!off sz. regions_disjoint (w2n p) 32 off sz ==>
      mem_bytes_at off sz captured.vs_memory = mem_bytes_at off sz t.vs_memory) /\
    tn.t_stor = tn1.t_stor /\ tn.t_trans = tn1.t_trans /\ tn.t_imm = tn1.t_imm /\
    (!j. j < t.vs_alloca_next /\ j IN tn.t_mem ==> j IN tn1.t_mem)
Proof
  disch_then (CONJUNCTS_THEN2 (mk_asm "fixed_run") strip_assume_tac) >>
  `valid_horizon cx st0 (storage_trace_horizon mid.storage_trace)
     mid.storage_trace` by fs[storage_trace_domain_def] >>
  qpat_assum `!H. valid_horizon _ _ H _ ==> expr_post H _ _ _ _ _ _ _ _ _ _ _ _ _ /\ _`
    (qspec_then `storage_trace_horizon mid.storage_trace` (drule_then strip_assume_tac)) >>
  drule_all hash_fixed_post_view >> disch_then (qx_choose_then `w` strip_assume_tac) >>
  `post_value_type cenv src = BaseT (BytesT (Fixed m))` by
    simp[post_value_type_word, is_word_type_def] >>
  `op_taint tn1 src_op = {}` by fs[ptr_val_ok_def] >>
  `stmt_state_rel (storage_trace_horizon mid.storage_trace) ctx func cenv cx mid t` by
    (drule expr_post_state >> simp[]) >>
  `allocas_from lo t /\ lo <= t.vs_alloca_next` by fs[ghost_inv_at_def] >>
  `ctx_has_dalloca ctx ==> allocas_below_fmp t /\
     t.vs_alloca_next + pending_alloca_size func t <= w2n t.vs_initial_fmp` by
    (qpat_assum `stmt_state_rel _ ctx func cenv cx mid t`
      (fn th =>
        mp_tac (MATCH_MP bodyFullHashKeccakFixedTheory.stmt_state_rel_allocas_below_fmp th) >>
        mp_tac (MATCH_MP stmt_state_rel_fmp_room th)) >>
     POP_ASSUM_LIST (K ALL_TAC) >> simp[fmp_room_def] >> decide_tac) >>
  asm_x "fixed_run" (qspecl_then [`storage_trace_horizon mid.storage_trace`,`w:bytes32`] mp_tac) >>
  (impl_tac >- simp[]) >>
  disch_then (qx_choosel_then [`root`,`p`,`allocated`,`captured`,`G`,`tn`]
    strip_assume_tac) >>
  `ci_mono st1 sm` by
    (qspecl_then [`32`,`st1`] mp_tac ci_mono_compile_alloc_buffer >> simp[]) >>
  `ci_mono sm sc` by
    (qspecl_then [`MSTORE`,`[buf.buf_operand;src_op]`,`sm`] mp_tac ci_mono_emit_void >> simp[]) >>
  `ci_mono st1 sc` by (irule ci_mono_trans >> qexists_tac `sm` >> simp[]) >>
  `MEM (mk_inst st1.cs_next_id ALLOCA [Lit 32w]
     [STRING #"%" (toString st1.cs_next_var)]) (fn_insts func)` by
    (irule buffer_alloc_code >> qexistsl_tac [`buf`,`sm`] >> simp[] >>
     irule (cj 1 fn_has_code_split) >> conj_tac >- fs[ci_mono_def] >>
     qexists_tac `sc` >> fs[ci_mono_def]) >>
  `allocated.vs_memory = t.vs_memory /\ captured.vs_vars = allocated.vs_vars /\
   captured.vs_allocas = allocated.vs_allocas /\ captured.vs_call_ctx = t.vs_call_ctx /\
   captured.vs_accounts = t.vs_accounts /\ captured.vs_transient = t.vs_transient /\
   captured.vs_immutables = t.vs_immutables` by
    (qpat_assum `allocated with <|vs_vars := _;vs_allocas := _;
       vs_alloca_next := _;vs_inst_idx := _|> = t` mp_tac >>
     qpat_assum `captured = mstore _ _ _ with vs_inst_idx := _` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >> rpt strip_tac >>
     gvs[mstore_def,write_memory_with_expansion_def,venom_state_component_equality]) >>
  `!H. valid_horizon cx st0 H mid.storage_trace ==>
     stmt_state_rel H ctx func cenv cx mid captured /\
     storage_well_formed_on cx mid (FST H)` by
    (gen_tac >> disch_tac >>
     qpat_assum `!H. valid_horizon _ _ H _ ==> expr_post H _ _ _ _ _ _ _ _ _ _ _ _ _ /\ _`
       (qspec_then `H` (drule_then strip_assume_tac)) >>
     `stmt_state_rel H ctx func cenv cx mid allocated` by
       (qpat_assum `!H'. stmt_state_rel H' _ _ _ _ _ t ==> stmt_state_rel H' _ _ _ _ _ allocated`
          (qspec_then `H` irule) >>
        qpat_assum `expr_post H _ _ _ _ _ _ _ _ _ _ _ _ _`
          (ACCEPT_TAC o MATCH_MP expr_post_state)) >>
     reverse conj_tac >- fs[expr_post_def] >>
     qpat_assum `captured = mstore _ _ _ with vs_inst_idx := _` SUBST1_TAC >>
     simp[stmt_state_rel_inst_idx] >>
     irule literal_mstore_state_rel >>
     reverse conj_tac >- first_assum ACCEPT_TAC >>
     qexistsl_tac [`w2n p`,
       `mk_inst st1.cs_next_id ALLOCA [Lit 32w]
         [STRING #"%" (toString st1.cs_next_var)]`,`32`] >>
     fs[mk_inst_def] >> rpt strip_tac >>
     qpat_assum `!name b len. local_region cenv mid.scopes allocated name b len ==> _`
       (qspecl_then [`name`,`lb`,`lsz`] mp_tac) >>
     simp[loweringStateRelDefsTheory.regions_disjoint_def]) >>
  `!off sz. regions_disjoint (w2n p) 32 off sz ==>
     mem_bytes_at off sz captured.vs_memory = mem_bytes_at off sz t.vs_memory` by
    (rpt strip_tac >>
     qpat_assum `captured = mstore _ _ _ with vs_inst_idx := _` SUBST1_TAC >>
     simp[] >> irule EQ_TRANS >>
     qexists_tac `mem_bytes_at off sz allocated.vs_memory` >>
     reverse conj_tac >- simp[] >>
     irule mstore_mem_bytes_at_disjoint >>
     fs[loweringStateRelDefsTheory.regions_disjoint_def]) >>
  `!x. not_fresh_at st1 x ==> lookup_var x allocated = lookup_var x t` by
    (qpat_assum `!x. not_fresh_at st1 x ==> lookup_var x captured = _ /\ _` mp_tac >>
     qpat_assum `captured.vs_vars = allocated.vs_vars` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >> simp[lookup_var_def]) >>
  `!name b sz. local_region cenv mid.scopes t name b sz ==>
     regions_disjoint (w2n p) 32 b sz` by
    (rpt strip_tac >>
     qpat_assum `!name b len. local_region cenv mid.scopes allocated name b len ==> _` irule >>
     qexists_tac `name` >> irule local_region_frame_fwd >>
     qexistsl_tac [`t`,`st1`,`mid.scopes`] >> simp[]) >>
  `lo <= w2n p` by
    (qpat_assum `allocas_from lo captured` mp_tac >>
     qpat_assum `FLOOKUP captured.vs_allocas st1.cs_next_id = SOME (w2n p,32)` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >> simp[allocas_from_def] >> metis_tac[]) >>
  `lo <= captured.vs_alloca_next` by decide_tac >>
  `!name b sz. local_region cenv mid.scopes t name b sz ==>
     mem_bytes_at b sz captured.vs_memory = mem_bytes_at b sz t.vs_memory /\
     (!j. b <= j /\ j < b+sz /\ j IN tn.t_mem ==> j IN tn1.t_mem)` by
    (rpt gen_tac >> disch_tac >> conj_tac
     >- (qpat_assum `!off sz. regions_disjoint _ _ _ _ ==> _` irule >>
         qpat_assum `!name b len. local_region cenv mid.scopes t name b len ==> _`
           (qspecl_then [`name`,`b`,`sz`] match_mp_tac) >> simp[]) >>
     rpt strip_tac >>
     `b+sz <= t.vs_alloca_next` by (drule_all body_local_region_frontier >> simp[]) >>
     qpat_assum `!j. j < t.vs_alloca_next /\ j IN tn.t_mem ==> _` irule >>
     simp[] >> decide_tac) >>
  `mem_bytes_at 0 lo captured.vs_memory = mem_bytes_at 0 lo t.vs_memory /\
   (!j. j < lo /\ j IN tn.t_mem ==> j IN tn1.t_mem)` by
    (conj_tac
     >- (qpat_assum `!off sz. regions_disjoint _ _ _ _ ==> _` irule >>
         simp[loweringStateRelDefsTheory.regions_disjoint_def]) >>
     rpt strip_tac >>
     qpat_assum `!j. j < t.vs_alloca_next /\ j IN tn.t_mem ==> _` irule >>
     simp[] >> decide_tac) >>
  `!x w. not_fresh_at st1 x /\ lookup_var x t = SOME w ==>
     lookup_var x captured = SOME w` by
    (qpat_assum `!x. not_fresh_at st1 x ==> lookup_var x captured = _ /\ _` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >> simp[]) >>
  `!x. not_fresh_at st1 x ==>
     FLOOKUP G x = FLOOKUP G1 x /\ op_taint tn (Var x) = op_taint tn1 (Var x)` by
    (qpat_assum `!x. not_fresh_at st1 x ==> lookup_var x captured = _ /\ _` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >> simp[]) >>
  `!H. valid_horizon cx st0 H mid.storage_trace ==>
     ghost_inv_at (DF H) lo d cenv cx mid G tn captured` by
    (gen_tac >> disch_tac >>
     qpat_assum `!H. valid_horizon _ _ H _ ==> expr_post H _ _ _ _ _ _ _ _ _ _ _ _ _ /\ _`
       (qspec_then `H` (drule_then strip_assume_tac)) >>
     `local_ptrs_rel func cenv mid.scopes t` by
       (qpat_assum `expr_post H _ _ _ _ _ _ _ _ _ _ _ _ _`
         (ACCEPT_TAC o MATCH_MP (cj 1 stmt_state_rel_local_ptrs_alloca) o
          MATCH_MP expr_post_state)) >>
     `stor_taint_ok_at (DF H) tn captured` by
       (qpat_assum `ghost_inv_at (DF H) lo d cenv cx mid G1 tn1 t` mp_tac >>
        qpat_assum `tn.t_stor = tn1.t_stor` mp_tac >>
        qpat_assum `tn.t_trans = tn1.t_trans` mp_tac >>
        qpat_assum `tn.t_imm = tn1.t_imm` mp_tac >>
        qpat_assum `captured.vs_call_ctx = t.vs_call_ctx` mp_tac >>
        qpat_assum `captured.vs_accounts = t.vs_accounts` mp_tac >>
        qpat_assum `captured.vs_transient = t.vs_transient` mp_tac >>
        qpat_assum `captured.vs_immutables = t.vs_immutables` mp_tac >>
        POP_ASSUM_LIST (K ALL_TAC) >> simp[ghost_inv_at_def,stor_taint_ok_at_def]) >>
     irule ghost_inv_at_local_window_transport >>
     qpat_assum `ghost_inv_at (DF H) lo d cenv cx mid G1 tn1 t` (irule_at Any) >>
     qexistsl_tac [`st1`,`func`] >> simp[NoAsms] >>
     rpt conj_tac >> first_assum MATCH_ACCEPT_TAC) >>
  `ctx_has_dalloca ctx ==> allocas_below_fmp captured` by
    (qpat_assum `!H. valid_horizon _ _ H _ ==> stmt_state_rel H _ _ _ _ _ captured /\ _`
      (qspec_then `storage_trace_horizon mid.storage_trace` (drule_then strip_assume_tac)) >>
     qpat_assum `stmt_state_rel _ _ _ _ _ _ captured`
       (ACCEPT_TAC o MATCH_MP bodyFullHashKeccakFixedTheory.stmt_state_rel_allocas_below_fmp)) >>
  `!fn inst u. frag_reachable ctx func captured fn inst u ==> dalloca_fmp_headroom inst u` by
    (qpat_assum `!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) _ [] _`
       (qspec_then `DF (storage_trace_horizon mid.storage_trace)` assume_tac) >>
     qpat_assum `gas_origin_ptr_path _ (t,G1,tn1) [] (OK captured,G,tn)` (fn path =>
       qpat_assum `!bb. MEM bb func.fn_blocks ==> phi_prefix_length _ = 0` (fn no_phi =>
         qpat_assum `!fn inst u. frag_reachable ctx func t fn inst u ==> _`
           (ACCEPT_TAC o MATCH_MP gas_origin_ptr_path_dalloca_fmp_headroom o
            CONJ path o CONJ no_phi)))) >>
  `local_ptrs_reserved cenv sc` by
    (irule local_ptrs_reserved_next_var >> qexists_tac `st1` >> fs[ci_mono_def]) >>
  `return_buf_frame d cenv sc captured` by
    (irule return_buf_frame_frame >> qexistsl_tac [`cenv`,`t`,`st1`] >> fs[ci_mono_def]) >>
  `(!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sc x) /\
   (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sc x)` by
    (conj_tac >> rpt strip_tac >> irule not_fresh_at_mono >>
     qexists_tac `st1` >> fs[ci_mono_def]) >>
  `mem_bytes_at (w2n p) (LENGTH bs) captured.vs_memory = bs` by
    (qpat_assum `captured = mstore _ _ _ with vs_inst_idx := _` SUBST1_TAC >>
     simp[NoAsms] >> irule hash_mstore_prefix >> simp[]) >>
  `!name b len. local_region cenv mid.scopes captured name b len ==>
     regions_disjoint (w2n p) 32 b len` by
    (qpat_assum `captured.vs_vars = allocated.vs_vars` mp_tac >>
     qpat_assum `!name b len. local_region cenv mid.scopes allocated name b len ==> _`
       mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >> simp[loweringStateRelDefsTheory.local_region_def,lookup_var_def] >>
     metis_tac[]) >>
  qpat_x_assum `captured = mstore _ _ _ with vs_inst_idx := _` kall_tac >>
  qexistsl_tac [`root`,`p`,`w`,`captured`,`G`,`tn`] >> simp[] >>
  rpt conj_tac >> first_assum MATCH_ACCEPT_TAC
QED
