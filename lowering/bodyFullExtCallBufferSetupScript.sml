Theory bodyFullExtCallBufferSetup
Ancestors
  bodyFullExtCallPacking bodyFullAllocaFresh calldataOverwritePtr exprSimAlloc
  decoderGhostFramePtr emitHelperProps exprLoweringProps fragExec
  ghostPcTransportPtr wordLoadStorePtr allocaHistory memoryReadProps
  loweringStateRelDefs stateRelProj ptrDiscipline venomState venomExecSemantics
  venomInst words pred_set finite_map ptrSafeRun arithmetic fragGasOriginPtr
  selectorDispatch bodyPtrDefs bodyFullUnwrapRun abiBuiltinAllocation compileEnv
  fragGasSeqPtr fragGasOriginPtrLoop venomMemDefs loweringShapeDefs valueEncodingProps
  bodyMemoryDefs bodyPtrBytestringBuiltinsWindowGhost abiCallerAllocation loweringPosts

(* Close the exact selector write at the new PC. Unlike the selector-only
   tail, this does not compute the calldata operand yet. *)
Theorem extcall_selector_setup_store[local]:
  emit_void MSTORE [Var q; Lit (calldata_method_id bs)] sa = ((),sb) /\
  fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
  LENGTH bs = 4 /\ lookup_var q s = SOME w /\
  32 <= n /\ ptr_covers G tn q s n /\ w2n w + n <= s.vs_alloca_next /\
  allocas_from lo s /\ alloca_history func s /\ alloca_inv s /\
  ~ctx_has_dalloca ctx /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?u Gu tu.
    (!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG)
         (s,G,tn) [] (OK u,Gu,tu)) /\
    u = (mstore (w2n w) (calldata_method_id bs) s with
           vs_inst_idx := LENGTH sb.cs_current_insts) /\
    ~u.vs_halted /\ u.vs_current_bb = sb.cs_current_bb /\
    u.vs_inst_idx = LENGTH sb.cs_current_insts /\
    u.vs_allocas = s.vs_allocas /\ u.vs_alloca_next = s.vs_alloca_next /\
    alloca_history func u /\ allocas_from lo u /\
    (!x. lookup_var x u = lookup_var x s /\ FLOOKUP Gu x = FLOOKUP G x /\
         op_taint tu (Var x) = op_taint tn (Var x)) /\
    ptr_covers Gu tu q u n /\
    venomState$read_memory (w2n w + 28) 4 u = bs /\
    (!i. w2n w + 28 <= i /\ i < w2n w + 32 ==> i NOTIN tu.t_mem) /\
    tu.t_mem SUBSET tn.t_mem /\ tu.t_stor = tn.t_stor /\
    tu.t_trans = tn.t_trans /\ tu.t_imm = tn.t_imm
Proof
  strip_tac >>
  `ptr_covers G tn q s 32` by
    (gvs[ptr_covers_def] >> metis_tac[arithmeticTheory.LESS_EQ_TRANS,
                                      arithmeticTheory.LESS_EQ_MONO_ADD_EQ]) >>
  `eval_operand (Var q) s = SOME w /\
   eval_operand (Lit (calldata_method_id bs)) s = SOME (calldata_method_id bs) /\
   op_taint tn (Lit (calldata_method_id bs)) = {}` by
    simp[eval_operand_def, op_taint_def] >>
  `ctx_has_dalloca ctx ==> allocas_below_fmp s` by simp[] >>
  drule_all clean_mstore_overwrite_prefix_uniform_origin_joint >>
  disch_then (qspec_then `PG` (qx_choose_then `u` (qx_choose_then `Gu`
     (qx_choose_then `tu` strip_assume_tac)))) >>
  `u with vs_inst_idx := s.vs_inst_idx = mstore (w2n w) (calldata_method_id bs) s` by
    (`step_inst_base (mk_inst sa.cs_next_id MSTORE
         [Var q;Lit (calldata_method_id bs)] []) s =
         OK (mstore (w2n w) (calldata_method_id bs) s)` by
       (irule step_MSTORE >> simp[]) >>
     drule emitted_insts_emit_void >> strip_tac >> fs[run_inst_seq_def]) >>
  `u = (mstore (w2n w) (calldata_method_id bs) s with
           vs_inst_idx := LENGTH sb.cs_current_insts)` by
    (qpat_assum `u with vs_inst_idx := _ = _`
       (mp_tac o AP_TERM ``\t:venom_state. t with vs_inst_idx := LENGTH sb.cs_current_insts``) >>
     simp[venom_state_component_equality]) >>
  `!x. lookup_var x u = lookup_var x s` by simp[lookup_var_def, mstore_def] >>
  `ptr_covers Gu tu q u n` by (irule ptr_covers_frame >> metis_tac[]) >>
  `venomState$read_memory (w2n w + 28) 4 u = bs` by
    simp[read_memory_eq_mem_bytes_at,
         GSYM (REWRITE_RULE [read_memory_eq_mem_bytes_at] extcall_selector_store_read)] >>
  `w2n w + 32 <= s.vs_alloca_next` by decide_tac >>
  `allocas_from lo u` by
    (qpat_assum `u.vs_allocas = s.vs_allocas` (fn th => simp[allocas_from_def,th]) >>
     qpat_assum `allocas_from lo s` (ACCEPT_TAC o REWRITE_RULE [allocas_from_def])) >>
  `alloca_history func u` by
    (qpat_assum `u = (mstore _ _ _ with vs_inst_idx := _)` SUBST1_TAC >>
     qspecl_then [`emitted_insts sa sb`,`sa`,`sb`,`s`,
       `mstore (w2n w) (calldata_method_id bs) s`] mp_tac emitted_alloca_history >>
     drule emitted_insts_emit_void >> strip_tac >>
     drule emit_void_same_blocks >> simp[same_blocks_def] >> strip_tac >>
     fs[is_terminator_def, mk_inst_def, mstore_def, run_inst_seq_def]) >>
  qexistsl [`u`,`Gu`,`tu`] >> simp[] >> metis_tac[arithmeticTheory.LESS_EQ_TRANS]
QED

(* Old sites, active locals, and the immutable prefix all end below the
   entry frontier. The selector write also misses each of these windows. *)
Theorem extcall_setup_protected_window[local]:
  stmt_state_rel (H : (bool # bytes32 # type_value) list # num list) ctx func cenv cx es s /\
  32 <= n /\ lo <= start /\ lo <= s.vs_alloca_next /\
  (!aid b k. aid < sa.cs_next_id /\ FLOOKUP s.vs_allocas aid = SOME (b,k) ==>
     loweringStateRelDefs$regions_disjoint start n b k) /\
  (!name b k. local_region cenv es.scopes s name b k ==>
     loweringStateRelDefs$regions_disjoint start n b k) /\
  (!a k. a+k <= start \/ start + 32 <= a ==>
     mem_bytes_at a k t.vs_memory = mem_bytes_at a k s.vs_memory) /\
  (!i. i < s.vs_alloca_next /\ i IN tt.t_mem ==> i IN tn.t_mem) ==>
  !a k. (a+k <= lo \/
         (?name b len. local_region cenv es.scopes s name b len /\
                       b <= a /\ a+k <= b+len) \/
         (?aid b len. aid < sa.cs_next_id /\ FLOOKUP s.vs_allocas aid = SOME (b,len) /\
                      b <= a /\ a+k <= b+len)) ==>
    mem_bytes_at a k t.vs_memory = mem_bytes_at a k s.vs_memory /\
    (!i. a <= i /\ i < a+k /\ i IN tt.t_mem ==> i IN tn.t_mem)
Proof
  strip_tac >> rpt gen_tac >>
  `((a+k <= lo) \/
     (?name b len. local_region cenv es.scopes s name b len /\
                   b <= a /\ a+k <= b+len) \/
     (?aid b len. aid < sa.cs_next_id /\ FLOOKUP s.vs_allocas aid = SOME (b,len) /\
                  b <= a /\ a+k <= b+len)) ==>
     (a+k <= start \/ start+32 <= a) /\ a+k <= s.vs_alloca_next` by
    (strip_tac >- decide_tac
     >- (`b + len <= s.vs_alloca_next` by
           (drule_all body_local_region_frontier >> simp[]) >>
         `loweringStateRelDefs$regions_disjoint start n b len` by metis_tac[] >>
         pop_assum (mp_tac o REWRITE_RULE [loweringStateRelDefsTheory.regions_disjoint_def]) >>
         decide_tac) >>
     `b + len <= s.vs_alloca_next` by
       (drule stmt_state_rel_local_ptrs_alloca >> simp[alloca_inv_def, alloca_next_valid_def] >>
        metis_tac[]) >>
     `loweringStateRelDefs$regions_disjoint start n b len` by metis_tac[] >>
     pop_assum (mp_tac o REWRITE_RULE [loweringStateRelDefsTheory.regions_disjoint_def]) >>
     decide_tac) >>
  disch_tac >>
  `a + k <= start \/ start + 32 <= a` by metis_tac[] >>
  `a + k <= s.vs_alloca_next` by metis_tac[] >>
  simp[] >> rpt strip_tac >>
  `i < s.vs_alloca_next` by decide_tac >> metis_tac[]
QED

(* The compiler's setup cuts, before either the selector-only tail or the
   first delayed argument store. Old operand registers are retained even if
   they were absent at entry. Memory is framed outside the selector word. *)
Theorem extcall_request_buffer_setup:
  compile_alloc_buffer n sa = (shared,sb) /\
  emit_void MSTORE [shared.buf_operand; Lit (calldata_method_id bs)] sb = ((),sc) /\
  (has_args ==> compile_alloc_buffer mem sc = (tuple,sd)) /\
  fn_has_code sa sb func /\ fn_has_code sb sc func /\
  (has_args ==> fn_has_code sc sd func) /\ fn_inst_ids_distinct func /\
  LENGTH bs = 4 /\ 32 <= n /\ n < dimword (:256) /\
  (has_args ==> mem < dimword (:256)) /\
  stmt_state_rel (H0 : (bool # bytes32 # type_value) list # num list)
    ctx func cenv cx es s /\ local_ptrs_reserved cenv sa /\
  alloca_history func s /\ allocas_from lo s /\ lo <= s.vs_alloca_next /\
  ~ctx_has_dalloca ctx /\ ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?q w t Gt tt.
    shared.buf_operand = Var q /\
    not_fresh_at (if has_args then sd else sb) q /\
    lookup_var q t = SOME w /\ ptr_covers Gt tt q t n /\
    FLOOKUP t.vs_allocas sa.cs_next_id = SOME (w2n w,n) /\
    FLOOKUP Gt q = SOME (w2n w,n) /\
    lo <= w2n w /\ w2n w + n < dimword (:256) /\ w2n w + n <= t.vs_alloca_next /\
    (!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG)
         (s,G,tn) [] (OK t,Gt,tt)) /\
    (!H : (bool # bytes32 # type_value) list # num list.
       stmt_state_rel H ctx func cenv cx es s ==> stmt_state_rel H ctx func cenv cx es t) /\
    ~t.vs_halted /\ alloca_history func t /\ allocas_from lo t /\
    t.vs_current_bb = (if has_args then sd else sb).cs_current_bb /\
    t.vs_inst_idx = LENGTH (if has_args then sd else sb).cs_current_insts /\
    s.vs_alloca_next <= t.vs_alloca_next /\
    (!aid ent. FLOOKUP s.vs_allocas aid = SOME ent ==> FLOOKUP t.vs_allocas aid = SOME ent) /\
    (!aid b k. aid < sa.cs_next_id /\ FLOOKUP s.vs_allocas aid = SOME (b,k) ==>
       loweringStateRelDefs$regions_disjoint (w2n w) n b k) /\
    (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s /\
         FLOOKUP Gt x = FLOOKUP G x /\ op_taint tt (Var x) = op_taint tn (Var x)) /\
    (!a k. a+k <= w2n w \/ w2n w + 32 <= a ==>
       mem_bytes_at a k t.vs_memory = mem_bytes_at a k s.vs_memory) /\
    (!i. i < s.vs_alloca_next /\ i IN tt.t_mem ==> i IN tn.t_mem) /\
    tt.t_stor = tn.t_stor /\ tt.t_trans = tn.t_trans /\ tt.t_imm = tn.t_imm /\
    (if has_args then
       ?p z. tuple.buf_operand = Var p /\ not_fresh_at sd p /\
         lookup_var p t = SOME z /\ ptr_covers Gt tt p t mem /\
         FLOOKUP t.vs_allocas sc.cs_next_id = SOME (w2n z,mem) /\
         FLOOKUP Gt p = SOME (w2n z,mem) /\
         w2n z + mem < dimword (:256) /\ w2n z + mem <= t.vs_alloca_next /\
         loweringStateRelDefs$regions_disjoint (w2n z) mem (w2n w) n /\
         (!aid b k. aid < sa.cs_next_id /\ FLOOKUP s.vs_allocas aid = SOME (b,k) ==>
            loweringStateRelDefs$regions_disjoint (w2n z) mem b k) /\
         (!name b k. local_region cenv es.scopes t name b k ==>
            loweringStateRelDefs$regions_disjoint (w2n z) mem b k) /\
         venomState$read_memory (w2n w + 28) 4 t = bs /\
         (!i. w2n w + 28 <= i /\ i < w2n w + 32 ==> i NOTIN tt.t_mem)
     else t.vs_memory = s.vs_memory) /\
    sa.cs_next_var <= (if has_args then sd else sb).cs_next_var /\
    t.vs_accounts = s.vs_accounts /\ t.vs_transient = s.vs_transient /\
    t.vs_call_ctx = s.vs_call_ctx /\ t.vs_immutables = s.vs_immutables /\
    t.vs_code = s.vs_code /\
    (!name b k. local_region cenv es.scopes s name b k ==>
       loweringStateRelDefs$regions_disjoint (w2n w) n b k) /\
    (!a k. (a+k <= lo \/
           (?name b len. local_region cenv es.scopes s name b len /\
                         b <= a /\ a+k <= b+len) \/
           (?aid b len. aid < sa.cs_next_id /\ FLOOKUP s.vs_allocas aid = SOME (b,len) /\
                        b <= a /\ a+k <= b+len)) ==>
      mem_bytes_at a k t.vs_memory = mem_bytes_at a k s.vs_memory /\
      (!i. a <= i /\ i < a+k /\ i IN tt.t_mem ==> i IN tn.t_mem)) /\
    sa.cs_next_id <= (if has_args then sd else sb).cs_next_id /\
    t.vs_labels = s.vs_labels /\ t.vs_requests = s.vs_requests /\
    pure_frame cenv func es sa s t
Proof
  strip_tac >>
  `ctx_has_dalloca ctx ==> allocas_below_fmp s` by simp[] >>
  drule_all (INST_TYPE [``:'b`` |-> ``:256``] (SPEC_ALL alloc_buffer_origin_ptr_path_exact)) >>
  disch_then (qspecl_then [`tn`, `explicit`, `PG`, `G`]
    (qx_choose_then `q` (qx_choose_then `w` (qx_choose_then `u`
      (qx_choose_then `Gu` (qx_choose_then `tu` strip_assume_tac)))))) >>
  `u.vs_memory = s.vs_memory /\ u.vs_halted = s.vs_halted /\
   u.vs_accounts = s.vs_accounts /\ u.vs_transient = s.vs_transient /\
   u.vs_call_ctx = s.vs_call_ctx /\ u.vs_immutables = s.vs_immutables /\
   u.vs_code = s.vs_code /\ u.vs_labels = s.vs_labels /\
   u.vs_requests = s.vs_requests` by
    (qpat_assum `u with <|vs_vars := _; vs_allocas := _;
         vs_alloca_next := _; vs_inst_idx := _|> = s` (SUBST1_TAC o SYM) >> simp[]) >>
  `sa.cs_next_var <= sb.cs_next_var /\ sa.cs_next_id <= sb.cs_next_id` by
    (drule abi_builtin_alloc_buffer_shape >> strip_tac >>
     drule emitted_insts_emit_op >> strip_tac >> decide_tac) >>
  `!name b k. local_region cenv es.scopes s name b k ==>
       loweringStateRelDefs$regions_disjoint (w2n w) n b k` by
    (`!name b k. local_region cenv es.scopes u name b k <=>
                  local_region cenv es.scopes s name b k` by
       (rpt gen_tac >> irule local_region_lookup_cong >> rpt strip_tac >>
        `not_fresh_at sa p` by metis_tac[local_ptrs_reserved_def] >> metis_tac[]) >>
     metis_tac[]) >>
  `lo <= w2n w` by metis_tac[allocas_from_def] >>
  Cases_on `has_args`
  >- suspend "tuple" >>
  `!i. i < s.vs_alloca_next /\ i IN tu.t_mem ==> i IN tn.t_mem` by
    (rpt strip_tac >> metis_tac[arithmeticTheory.NOT_LESS]) >>
  `!a k. a+k <= w2n w \/ w2n w + 32 <= a ==>
     mem_bytes_at a k u.vs_memory = mem_bytes_at a k s.vs_memory` by simp[] >>
  mp_tac (Q.INST [`start` |-> `w2n (w:bytes32)`, `H` |-> `H0`,
      `t` |-> `u`, `tt` |-> `tu`] extcall_setup_protected_window) >>
  impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC) >> strip_tac >>
  `pure_frame cenv func es sa s u` by simp[pure_frame_def] >>
  qexistsl [`q`,`w`,`u`,`Gu`,`tu`] >>
  simp[NoAsms] >> rpt conj_tac >>> NTH_GOAL (simp[]) 8 >>> NTH_GOAL (simp[]) 8 >>> NTH_GOAL (simp[]) 10 >> first_assum ACCEPT_TAC
QED

Resume extcall_request_buffer_setup[tuple]:
  gvs[] >>
  `stmt_state_rel H0 ctx func cenv cx es u` by
    (qpat_assum `!H. stmt_state_rel H ctx func cenv cx es s ==> stmt_state_rel H ctx func cenv cx es u`
       (qspec_then `H0` mp_tac) >> simp[]) >>
  `alloca_inv u` by
    (qpat_assum `stmt_state_rel _ _ _ _ _ _ u`
       (mp_tac o MATCH_MP stmt_state_rel_local_ptrs_alloca) >> simp[]) >>
  `w2n w + n <= u.vs_alloca_next` by decide_tac >>
  drule_all extcall_selector_setup_store >>
  disch_then (qspecl_then [`explicit`,`PG`]
    (qx_choose_then `v` (qx_choose_then `Gv` (qx_choose_then `tv` strip_assume_tac)))) >>
  `!H : (bool # bytes32 # type_value) list # num list.
      stmt_state_rel H ctx func cenv cx es s ==> stmt_state_rel H ctx func cenv cx es v` by
    (qx_gen_tac `H` >> strip_tac >>
     qspecl_then [`n`,`sa`,`sb`,`shared`,`func`] mp_tac buffer_alloc_code >>
     simp[] >> strip_tac >>
     qpat_assum `v = (mstore _ _ _ with vs_inst_idx := _)` SUBST1_TAC >>
     simp[stmt_state_rel_inst_idx] >> irule literal_mstore_state_rel >>
     reverse conj_tac
     >- (qpat_assum `!H. stmt_state_rel H ctx func cenv cx es s ==> stmt_state_rel H ctx func cenv cx es u`
          (qspec_then `H` mp_tac) >> simp[]) >>
     qexistsl [`w2n w`,`mk_inst sa.cs_next_id ALLOCA [Lit (n2w n)] [STRING #"%" (toString sa.cs_next_var)]`,`n`] >>
     simp[mk_inst_def] >>
     rpt strip_tac >>
     qpat_assum `!name b len. local_region cenv es.scopes u name b len ==> _`
       (drule_then mp_tac) >> simp[loweringStateRelDefsTheory.regions_disjoint_def]) >>
  every_drule abi_builtin_alloc_buffer_shape >> rpt strip_tac >>
  every_drule emitted_insts_emit_op >> rpt strip_tac >>
  drule emitted_insts_emit_void >> strip_tac >>
  `sa.cs_next_id < sc.cs_next_id /\ sa.cs_next_var <= sc.cs_next_var /\
   sb.cs_next_var <= sc.cs_next_var /\ sb.cs_next_var <= sd.cs_next_var` by decide_tac >>
  `local_ptrs_reserved cenv sc` by (irule local_ptrs_reserved_next_var >> qexists `sa` >> simp[]) >>
  `stmt_state_rel H0 ctx func cenv cx es v` by
    (qpat_assum `!H. stmt_state_rel H ctx func cenv cx es s ==> stmt_state_rel H ctx func cenv cx es v`
       (qspec_then `H0` mp_tac) >> simp[]) >>
  `lo <= v.vs_alloca_next` by decide_tac >>
  `ctx_has_dalloca ctx ==> allocas_below_fmp v` by simp[] >>
  drule_all (Q.INST [`sa` |-> `sc`, `sb` |-> `sd`, `s` |-> `v`]
    (INST_TYPE [``:'b`` |-> ``:256``] (SPEC_ALL alloc_buffer_origin_ptr_path_exact))) >>
  disch_then (qspecl_then [`tv`, `explicit`, `PG`, `Gv`] strip_assume_tac) >>
  rename1 `lookup_var p tf = SOME z` >>
  `tf.vs_memory = v.vs_memory /\ tf.vs_halted = v.vs_halted /\
   tf.vs_accounts = v.vs_accounts /\ tf.vs_transient = v.vs_transient /\
   tf.vs_call_ctx = v.vs_call_ctx /\ tf.vs_immutables = v.vs_immutables /\
   tf.vs_code = v.vs_code /\ tf.vs_labels = v.vs_labels /\
   tf.vs_requests = v.vs_requests` by
    (qpat_assum `tf with <|vs_vars := _; vs_allocas := _;
         vs_alloca_next := _; vs_inst_idx := _|> = v` (SUBST1_TAC o SYM) >> simp[]) >>
  `v.vs_accounts = s.vs_accounts /\ v.vs_transient = s.vs_transient /\
   v.vs_call_ctx = s.vs_call_ctx /\ v.vs_immutables = s.vs_immutables /\
   v.vs_code = s.vs_code /\ v.vs_labels = s.vs_labels /\
   v.vs_requests = s.vs_requests` by simp[mstore_def] >>
  `sa.cs_next_var <= sd.cs_next_var /\ sa.cs_next_id <= sd.cs_next_id` by decide_tac >>
  `not_fresh_at sc q /\ not_fresh_at sd q` by
    metis_tac[loweringShapeDefsTheory.not_fresh_at_mono] >>
  `lookup_var q tf = lookup_var q v /\ FLOOKUP G' q = FLOOKUP Gv q /\
   op_taint tn' (Var q) = op_taint tv (Var q)` by
    (qpat_assum `!x. not_fresh_at sc x ==> lookup_var x tf = _ /\ _`
       (qspec_then `q` mp_tac) >> simp[]) >>
  `ptr_covers G' tn' q tf n` by (irule ptr_covers_frame >> metis_tac[]) >>
  `!a k. a+k <= w2n w \/ w2n w + 32 <= a ==>
       mem_bytes_at a k tf.vs_memory = mem_bytes_at a k s.vs_memory` by
    (rpt gen_tac >> disch_tac >> simp[] >>
     qpat_assum `u.vs_memory = s.vs_memory` (SUBST1_TAC o SYM) >>
     irule mstore_mem_bytes_at_disjoint >> first_assum ACCEPT_TAC) >>
  `!i. i < s.vs_alloca_next /\ i IN tn'.t_mem ==> i IN tn.t_mem` by
    (rpt strip_tac >> gvs[SUBSET_DEF] >>
     metis_tac[arithmeticTheory.NOT_LESS, arithmeticTheory.LESS_LESS_EQ_TRANS]) >>
  mp_tac (Q.INST [`start` |-> `w2n (w:bytes32)`, `H` |-> `H0`,
      `t` |-> `tf`, `tt` |-> `tn'`] extcall_setup_protected_window) >>
  impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC) >>
  disch_then (mk_asm "protected") >>
  `pure_frame cenv func es sa s tf` by
    (simp[NoAsms,pure_frame_def] >> conj_tac
     >- (rpt strip_tac >> asm "protected" (qspecl_then [`b`,`sz`] mp_tac) >>
         impl_tac >- metis_tac[arithmeticTheory.LESS_EQ_REFL] >> simp[]) >>
     rpt strip_tac >>
     qpat_assum `!a k. a+k <= w2n w \/ w2n w + 32 <= a ==> _` irule >>
     `MEM (mk_inst sa.cs_next_id ALLOCA [Lit (n2w n)]
        [STRING #"%" (toString sa.cs_next_var)]) (fn_insts func)` by
       (irule buffer_alloc_code >> qexistsl [`shared`,`sb`] >> simp[]) >>
     qpat_assum `!inst b sz. _ ==> loweringStateRelDefs$regions_disjoint _ _ _ _`
       (qspecl_then [`mk_inst sa.cs_next_id ALLOCA [Lit (n2w n)]
         [STRING #"%" (toString sa.cs_next_var)]`,`w2n w`,`n`] mp_tac) >>
     simp[mk_inst_def,loweringStateRelDefsTheory.regions_disjoint_def] >> decide_tac) >>
  qexistsl [`w`,`tf`,`G'`,`tn'`] >> simp[] >>
  conj_tac
  >- (gen_tac >> irule gas_origin_ptr_path_trans >> qexistsl [`Gv`,`v`,`tv`] >>
      reverse conj_tac >- simp[] >>
      irule gas_origin_ptr_path_trans >> qexistsl [`Gu`,`u`,`tu`] >> simp[]) >>
  conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac
  >- (gen_tac >> strip_tac >>
      `not_fresh_at sc x` by metis_tac[loweringShapeDefsTheory.not_fresh_at_mono] >>
      qpat_assum `!x. not_fresh_at sc x ==> lookup_var x tf = _ /\ _`
        (qspec_then `x` mp_tac) >> simp[]) >>
  conj_tac
  >- (qpat_assum `!a k. a+k <= w2n w \/ w2n w + 32 <= a ==> _`
        mp_tac >> simp[]) >>
  conj_tac
  >- (qpat_assum `!i. i < s.vs_alloca_next /\ i IN tn'.t_mem ==> i IN tn.t_mem`
        mp_tac >> simp[]) >>
  reverse conj_tac
  >- (conj_tac >- first_assum ACCEPT_TAC >> asm "protected" mp_tac >> simp[]) >>
  conj_tac
  >- (qpat_assum `!aid b len. aid < sc.cs_next_id /\ FLOOKUP v.vs_allocas aid = _ ==> _`
        (qspecl_then [`sa.cs_next_id`,`w2n w`,`n`] mp_tac) >> simp[]) >>
  conj_tac
  >- (rpt strip_tac >>
      qpat_assum `!aid b len. aid < sc.cs_next_id /\ FLOOKUP v.vs_allocas aid = _ ==> _`
        (qspecl_then [`aid`,`b`,`k`] mp_tac) >>
      simp[] >> metis_tac[arithmeticTheory.LESS_TRANS]) >>
  conj_tac >- first_assum ACCEPT_TAC >>
  qpat_assum `tf.vs_memory = v.vs_memory` (fn th =>
    simp[read_memory_eq_mem_bytes_at, th, IgnAsm `v = (_ with vs_inst_idx := _)`] >>
    qpat_assum `venomState$read_memory (w2n w + 28) 4 v = bs`
      (ACCEPT_TAC o REWRITE_RULE [read_memory_eq_mem_bytes_at]))
QED

Finalise extcall_request_buffer_setup
