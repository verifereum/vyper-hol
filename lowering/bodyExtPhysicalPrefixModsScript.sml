Theory bodyExtPhysicalPrefixMods
Ancestors
  bodyFullExtCallBufferSetup bodyFullAbiEncodeAllocOrigin
  bodyExtPackingFrameMods bodyFullPathHistory bodyFullHashKeccakFixed
  venomMemProps venomState ptrDiscipline calldataOverwritePtr venomExecSemantics
  emitHelperProps fragExec abiEncoderWindowContract abiBuiltinAllocation
  finite_map pred_set exprLoweringProps exprSimAlloc exprSimProps decoderGhostFramePtr
  loweringPosts loweringStateRelDefs ghostPcTransportPtr fragGasOriginPtrLoop
  bodyFullExtCallPacking stateRelProj valueEncodingProps bodyMemoryDefs bodyPtrDefs
  venomMemDefs compileEnv venomInst bodyFullShadowBodyInv arithmetic
  reasonCopySourcePtr memoryReadProps

(* The uniform overwrite rule gives the ghost effects of the actual store.
   Expose its memory update as well, for the linked immutable frame. *)
Theorem selector_endpoint[local]:
  emit_void MSTORE [Var q; Lit (calldata_method_id bs)] sb = ((),sc) /\
  fn_has_code sb sc func /\ fn_inst_ids_distinct func /\
  lookup_var q u = SOME w /\ ptr_covers Gu tu q u 32 /\
  w2n w + 32 <= u.vs_alloca_next /\ allocas_from lo u /\
  (ctx_has_dalloca ctx ==> allocas_below_fmp u) /\
  ~u.vs_halted /\ u.vs_current_bb = sb.cs_current_bb /\
  u.vs_inst_idx = LENGTH sb.cs_current_insts ==>
  ?t Gt tt.
    t = (mstore (w2n w) (calldata_method_id bs) u with
           vs_inst_idx := LENGTH sc.cs_current_insts) /\
    (!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG)
         (u,Gu,tu) [] (OK t,Gt,tt)) /\
    ~t.vs_halted /\ t.vs_current_bb = sc.cs_current_bb /\
    (!x. FLOOKUP Gt x = FLOOKUP Gu x /\
         op_taint tt (Var x) = op_taint tu (Var x)) /\
    (!i. w2n w <= i /\ i < w2n w + 32 ==> i NOTIN tt.t_mem) /\
    tt.t_mem SUBSET tu.t_mem /\ tt.t_stor = tu.t_stor /\
    tt.t_trans = tu.t_trans /\ tt.t_imm = tu.t_imm
Proof
  strip_tac >>
  `eval_operand (Var q) u = SOME w /\
   eval_operand (Lit (calldata_method_id bs)) u = SOME (calldata_method_id bs) /\
   op_taint tu (Lit (calldata_method_id bs)) = {}` by
    simp[eval_operand_def, op_taint_def] >>
  drule_all clean_mstore_overwrite_prefix_uniform_origin_joint >>
  disch_then (qspec_then `PG` mp_tac) >>
  disch_then (qx_choose_then `uout` (qx_choose_then `gout`
    (qx_choose_then `tout` strip_assume_tac))) >>
  `step_inst_base (mk_inst sb.cs_next_id MSTORE
       [Var q;Lit (calldata_method_id bs)] []) u =
       OK (mstore (w2n w) (calldata_method_id bs) u)` by
    (irule step_MSTORE >> simp[]) >>
  `uout with vs_inst_idx := u.vs_inst_idx = mstore (w2n w) (calldata_method_id bs) u` by
    (drule emitted_insts_emit_void >> strip_tac >> fs[run_inst_seq_def]) >>
  `uout = (mstore (w2n w) (calldata_method_id bs) u with
          vs_inst_idx := LENGTH sc.cs_current_insts)` by
    (qpat_assum `uout with vs_inst_idx := _ = _`
       (mp_tac o AP_TERM ``\s:venom_state. s with vs_inst_idx := LENGTH sc.cs_current_insts``) >>
     simp[venom_state_component_equality]) >>
  `!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG)
     (u,Gu,tu) [] (OK uout,gout,tout)` by
    (qpat_assum `w2n w + 32 <= u.vs_alloca_next ==> _` mp_tac >> simp[]) >>
  qexistsl [`uout`,`gout`,`tout`] >> rpt conj_tac >> first_assum ACCEPT_TAC
QED

Theorem prefix_alloca_growth[local]:
  s.vs_alloca_next <= t.vs_alloca_next /\
  t.vs_allocas = (abi_builtin_allocate_state id n s).vs_allocas ==>
  window_alloca_growth s t
Proof
  simp[window_alloca_growth_def] >> rpt strip_tac >>
  Cases_on `FLOOKUP s.vs_allocas id = NONE` >>
  gvs[abi_builtin_allocate_state_def,FLOOKUP_UPDATE,AllCaseEqs()]
QED

(* A prefix write cannot touch a subrange of a protected old interval. *)
Theorem prefix_protected_subranges[local]:
  stmt_state_rel (H:(bool # bytes32 # type_value) list # num list) ctx func ce cx es s ==>
  lo <= start /\ lo <= s.vs_alloca_next /\ 32 <= n /\
  (!name b len. local_region ce es.scopes s name b len ==> regions_disjoint start n b len) /\
  (!aid b len. aid < cut.cs_next_id /\ FLOOKUP s.vs_allocas aid = SOME (b,len) ==>
               regions_disjoint start n b len) ==>
  !a k. (a+k <= lo \/
         (?name b len. local_region ce es.scopes s name b len /\ b <= a /\ a+k <= b+len) \/
         (?aid b len. aid < cut.cs_next_id /\ FLOOKUP s.vs_allocas aid = SOME (b,len) /\
                      b <= a /\ a+k <= b+len)) ==>
        (a+k <= start \/ start+32 <= a) /\ a+k <= s.vs_alloca_next
Proof
  strip_tac >> strip_tac >> rpt gen_tac >> strip_tac >- decide_tac
  >- (drule_all body_local_region_frontier >> strip_tac >>
      qpat_assum `!name b len. local_region _ _ _ name b len ==> _`
        (drule_then mp_tac) >>
      simp[loweringStateRelDefsTheory.regions_disjoint_def] >> decide_tac) >>
  `alloca_next_valid s` by
    (drule stmt_state_rel_local_ptrs_alloca >> simp[alloca_inv_def]) >>
  qpat_assum `alloca_next_valid s`
    (drule_then assume_tac o REWRITE_RULE [alloca_next_valid_def]) >>
  qpat_assum `!aid b len. aid < _ /\ FLOOKUP _ aid = SOME (b,len) ==> _`
    (drule_all_then mp_tac) >>
  simp[loweringStateRelDefsTheory.regions_disjoint_def] >> decide_tac
QED

Theorem ext_physical_prefix_mods:
  compile_alloc_buffer n sa = (shared,sb) /\
  emit_void MSTORE [shared.buf_operand;Lit (calldata_method_id bs)] sb = ((),sc) /\
  fn_has_code sa sb func /\ fn_has_code sb sc func /\ fn_inst_ids_distinct func /\
  LENGTH bs = 4 /\ 32 <= n /\ n < dimword (:256) /\
  stmt_state_rel (H0:(bool # bytes32 # type_value) list # num list)
    ctx func cenv cx es s /\ local_ptrs_reserved cenv sa /\
  (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  alloca_history func s /\ allocas_from lo s /\ lo <= s.vs_alloca_next /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?q w t Gt tt.
    shared.buf_operand = Var q /\ not_fresh_at sc q /\
    lookup_var q t = SOME w /\ ptr_covers Gt tt q t n /\
    MEM (mk_inst sa.cs_next_id ALLOCA [Lit (n2w n)] [q]) (fn_insts func) /\
    FLOOKUP t.vs_allocas sa.cs_next_id = SOME (w2n w,n) /\
    FLOOKUP Gt q = SOME (w2n w,n) /\
    lo <= w2n w /\ w2n w + n < dimword (:256) /\ w2n w + n <= t.vs_alloca_next /\
    venomState$read_memory (w2n w + 28) 4 t = bs /\
    (!i. w2n w <= i /\ i < w2n w + 32 ==> i NOTIN tt.t_mem) /\
    (!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn) [] (OK t,Gt,tt)) /\
    (!H : (bool # bytes32 # type_value) list # num list.
       stmt_state_rel H ctx func cenv cx es s ==> stmt_state_rel H ctx func cenv cx es t) /\
    (!D. ghost_inv_at_mods D lo d cenv cx es G tn s /\ immutable_frame_mods func cenv cx es s ==>
         ghost_inv_at_mods D lo d cenv cx es Gt tt t /\ immutable_frame_mods func cenv cx es t) /\
    pure_frame cenv func es sa s t /\ wb_frame cenv es es sa s t /\
    ghost_kept_at lo cenv es sa G tn s Gt tt /\
    ~t.vs_halted /\ alloca_history func t /\ allocas_from lo t /\
    t.vs_current_bb = sc.cs_current_bb /\ t.vs_inst_idx = LENGTH sc.cs_current_insts /\
    ci_mono sa sb /\ ci_mono sb sc /\ ci_mono sa sc /\
    local_ptrs_reserved cenv sc /\ window_alloca_growth s t /\
    (!aid row. FLOOKUP s.vs_allocas aid = SOME row ==> FLOOKUP t.vs_allocas aid = SOME row) /\
    (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s /\
      FLOOKUP Gt x = FLOOKUP G x /\ op_taint tt (Var x) = op_taint tn (Var x)) /\
    (!i. i < s.vs_alloca_next /\ i IN tt.t_mem ==> i IN tn.t_mem) /\
    tt.t_stor = tn.t_stor /\ tt.t_trans = tn.t_trans /\ tt.t_imm = tn.t_imm /\
    t.vs_accounts = s.vs_accounts /\ t.vs_transient = s.vs_transient /\
    t.vs_call_ctx = s.vs_call_ctx /\ t.vs_immutables = s.vs_immutables /\
    t.vs_data_section = s.vs_data_section /\ LENGTH s.vs_memory <= LENGTH t.vs_memory /\
    (!a k. a+k <= w2n w \/ w2n w + 32 <= a ==>
       mem_bytes_at a k t.vs_memory = mem_bytes_at a k s.vs_memory) /\
    (!a k. (a+k <= lo \/
            (?name b len. local_region cenv es.scopes s name b len /\ b <= a /\ a+k <= b+len) \/
            (?aid b len. aid < sa.cs_next_id /\ FLOOKUP s.vs_allocas aid = SOME (b,len) /\
                         b <= a /\ a+k <= b+len)) ==>
       mem_bytes_at a k t.vs_memory = mem_bytes_at a k s.vs_memory /\
       (!i. a <= i /\ i < a+k /\ i IN tt.t_mem ==> i IN tn.t_mem))
Proof
  strip_tac >>
  drule_all (INST_TYPE [Type.beta |-> ``:256``] abi_encode_alloc_origin_exact) >>
  disch_then (qspecl_then [`tn`,`explicit`,`PG`,`G`] mp_tac) >>
  disch_then (qx_choose_then `root` (qx_choose_then `bw`
    (qx_choose_then `u` (qx_choose_then `Gu` (qx_choose_then `tu` strip_assume_tac))))) >>
  qpat_assum `u with <|vs_vars := _; vs_allocas := _; vs_alloca_next := _; vs_inst_idx := _|> = s`
    mp_tac >> simp[venom_state_component_equality] >> strip_tac >>
  `stmt_state_rel H0 ctx func cenv cx es u` by simp[] >>
  `ctx_has_dalloca ctx ==> allocas_below_fmp u` by
    (qpat_assum `stmt_state_rel _ _ _ _ _ _ u`
      (mp_tac o MATCH_MP bodyFullHashKeccakFixedTheory.stmt_state_rel_allocas_below_fmp) >> simp[]) >>
  `emit_void MSTORE [Var root;Lit (calldata_method_id bs)] sb = ((),sc)` by
    (qpat_assum `shared.buf_operand = Var root` (SUBST1_TAC o SYM) >>
     first_assum ACCEPT_TAC) >>
  `ptr_covers Gu tu root u 32` by (irule ptr_covers_mono >> metis_tac[]) >>
  `w2n bw + 32 <= u.vs_alloca_next` by decide_tac >>
  drule_all selector_endpoint >>
  disch_then (qspecl_then [`explicit`,`PG`] mp_tac) >>
  disch_then (qx_choose_then `v` (qx_choose_then `Gv` (qx_choose_then `tv` strip_assume_tac))) >>
  `v.vs_allocas = u.vs_allocas /\ v.vs_alloca_next = u.vs_alloca_next /\
   v.vs_inst_idx = LENGTH sc.cs_current_insts /\
   (!x. lookup_var x v = lookup_var x u) /\
   v.vs_accounts = s.vs_accounts /\ v.vs_transient = s.vs_transient /\
   v.vs_call_ctx = s.vs_call_ctx /\ v.vs_immutables = s.vs_immutables /\
   v.vs_data_section = s.vs_data_section` by
    (qpat_assum `v = _` SUBST1_TAC >> simp[mstore_def, lookup_var_def]) >>
  `LENGTH s.vs_memory <= LENGTH v.vs_memory` by
    (qpat_assum `v = _` SUBST1_TAC >>
     simp[] >>
     qpat_assum `u.vs_memory = s.vs_memory` (PURE_ONCE_REWRITE_TAC o single o SYM) >>
     irule mstore_memory_nondecreasing) >>
  `venomState$read_memory (w2n bw + 28) 4 v = bs` by
    (qpat_assum `v = _` SUBST1_TAC >>
     simp[read_memory_eq_mem_bytes_at,
          GSYM (REWRITE_RULE [read_memory_eq_mem_bytes_at] extcall_selector_store_read)]) >>
  `!a k. a+k <= w2n bw \/ w2n bw + 32 <= a ==>
         mem_bytes_at a k v.vs_memory = mem_bytes_at a k s.vs_memory` by
    (qpat_assum `v = _` SUBST1_TAC >>
     simp[] >>
     qpat_assum `u.vs_memory = s.vs_memory` (PURE_ONCE_REWRITE_TAC o single o SYM) >>
     rpt strip_tac >> irule mstore_mem_bytes_at_disjoint >> simp[]) >>
  `window_alloca_growth s v` by
    (irule prefix_alloca_growth >> simp[] >> metis_tac[]) >>
  `!i. i < s.vs_alloca_next /\ i IN tv.t_mem ==> i IN tn.t_mem` by
    (rpt strip_tac >>
     `i IN tu.t_mem` by
       (qpat_assum `tv.t_mem SUBSET tu.t_mem`
          (qspec_then `i` mp_tac o REWRITE_RULE [SUBSET_DEF]) >> simp[]) >>
     `~(s.vs_alloca_next <= i)` by decide_tac >>
     qpat_assum `!i. i IN tu.t_mem <=> _` (qspec_then `i` mp_tac) >> simp[]) >>
  `!x. not_fresh_at sa x ==> lookup_var x v = lookup_var x s /\
     FLOOKUP Gv x = FLOOKUP G x /\ op_taint tv (Var x) = op_taint tn (Var x)` by
    simp[] >>
  `!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn) [] (OK v,Gv,tv)` by
    (gen_tac >> irule gas_origin_ptr_path_trans >> qexistsl [`Gu`,`u`,`tu`] >> simp[]) >>
  `lo <= w2n bw` by
    (qpat_assum `allocas_from lo u`
      (drule_then ACCEPT_TAC o REWRITE_RULE [allocas_from_def])) >>
  `!name b k. local_region cenv es.scopes u name b k <=> local_region cenv es.scopes s name b k` by
    (rpt gen_tac >> irule local_region_lookup_cong >> rpt strip_tac >>
     `not_fresh_at sa p` by
       (qpat_assum `local_ptrs_reserved cenv sa`
         (strip_assume_tac o REWRITE_RULE [local_ptrs_reserved_def]) >>
        qpat_assum `!n1 n2 p sz1 sz2. FLOOKUP _ n1 = SOME (PtrVar (Var p) sz1) ==> _`
          (drule_then mp_tac) >> simp[]) >> simp[]) >>
  `!name b k. local_region cenv es.scopes s name b k ==> regions_disjoint (w2n bw) n b k` by
    (qpat_assum `!name b k. local_region cenv es.scopes u name b k ==> _` mp_tac >> simp[]) >>
  `MEM (mk_inst sa.cs_next_id ALLOCA [Lit (n2w n)] [root]) (fn_insts func)` by
    (drule abi_builtin_alloc_buffer_shape >> strip_tac >>
     drule emitted_insts_emit_op >> strip_tac >>
     drule_all buffer_alloc_code >>
     `root = STRING #"%" (toString sa.cs_next_var)` by
       (qpat_assum `shared.buf_operand = Var root` mp_tac >>
        qpat_assum `shared.buf_operand = Var (STRING _ _)` (PURE_ONCE_REWRITE_TAC o single) >> simp[]) >>
     simp[]) >>
  `!H:(bool # bytes32 # type_value) list # num list.
     stmt_state_rel H ctx func cenv cx es s ==> stmt_state_rel H ctx func cenv cx es v` by
    (gen_tac >> strip_tac >> qpat_assum `v = _` SUBST1_TAC >>
     simp[stmt_state_rel_inst_idx] >> irule literal_mstore_state_rel >>
     reverse conj_tac >- simp[] >>
     qexistsl [`w2n bw`,`mk_inst sa.cs_next_id ALLOCA [Lit (n2w n)] [root]`,`n`] >>
     simp[mk_inst_def] >> conj_tac
     >- (rpt strip_tac >>
         qpat_assum `!name b k. local_region _ _ s name b k ==> _`
           (qspecl_then [`name`,`lb`,`lsz`] mp_tac) >>
         simp[loweringStateRelDefsTheory.regions_disjoint_def] >> decide_tac) >>
     qpat_assum `u.vs_allocas = (abi_builtin_allocate_state _ _ _).vs_allocas`
       (PURE_ONCE_REWRITE_TAC o single o SYM) >> first_assum ACCEPT_TAC) >>
  `pure_frame cenv func es sa s v` by
    (irule pure_frame_fresh_alloca >> conj_tac
     >- (rpt strip_tac >>
         qpat_assum `!a k. _ \/ _ ==> mem_bytes_at a k v.vs_memory = _` irule >>
         qpat_assum `!name b k. local_region _ _ s name b k ==> _` (drule_then mp_tac) >>
         simp[loweringStateRelDefsTheory.regions_disjoint_def] >> decide_tac) >>
     qexistsl [`w2n bw`,`sa.cs_next_id`,`[Lit (n2w n)]`,`[root]`,`n`] >>
     `FLOOKUP v.vs_allocas sa.cs_next_id = SOME (w2n bw,n)` by
       (qpat_assum `v.vs_allocas = u.vs_allocas` SUBST1_TAC >> first_assum ACCEPT_TAC) >>
     rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >> TRY (PURE_REWRITE_TAC [LESS_EQ_REFL] >> ACCEPT_TAC TRUTH) >>
     rpt strip_tac >>
     qpat_assum `!a k. _ \/ _ ==> mem_bytes_at a k v.vs_memory = _` irule >>
     fs[loweringStateRelDefsTheory.regions_disjoint_def] >> decide_tac) >>
  `!aid row. FLOOKUP s.vs_allocas aid = SOME row ==> FLOOKUP v.vs_allocas aid = SOME row` by
    (qpat_assum `v.vs_allocas = u.vs_allocas` SUBST1_TAC >> first_assum ACCEPT_TAC) >>
  `tv.t_stor = tn.t_stor /\ tv.t_trans = tn.t_trans /\ tv.t_imm = tn.t_imm` by simp[] >>
  `!D. ghost_inv_at_mods D lo d cenv cx es G tn s /\ immutable_frame_mods func cenv cx es s ==>
       ghost_inv_at_mods D lo d cenv cx es Gv tv v /\ immutable_frame_mods func cenv cx es v` by
    (gen_tac >> strip_tac >>
     irule (INST_TYPE [Type.alpha |-> ``:256``] ext_packing_frame_mods) >>
     qexistsl [`G`,`H0`,`ctx`,`sa`,`tn`,`s`] >> rpt conj_tac >> first_assum ACCEPT_TAC) >>
  `alloca_inv u` by (drule stmt_state_rel_local_ptrs_alloca >> simp[]) >>
  `alloca_history func v` by
    (qpat_assum `!D. gas_origin_ptr_path _ (u,Gu,tu) [] (OK v,Gv,tv)`
       (qspec_then `ARB` mp_tac) >> disch_tac >>
     drule_all_then ACCEPT_TAC body_full_path_alloca_history) >>
  `allocas_from lo v` by
    (qpat_assum `v.vs_allocas = u.vs_allocas` (fn th => pure_rewrite_tac[allocas_from_def,th]) >>
     qpat_assum `allocas_from lo u` (ACCEPT_TAC o REWRITE_RULE [allocas_from_def])) >>
  `ci_mono sa sb` by metis_tac[ci_mono_compile_alloc_buffer,pairTheory.SND] >>
  `ci_mono sb sc` by metis_tac[ci_mono_emit_void,pairTheory.SND] >>
  `ci_mono sa sc` by (irule ci_mono_trans >> qexists `sb` >> simp[]) >>
  `local_ptrs_reserved cenv sc` by
    (irule local_ptrs_reserved_next_var >> qexists `sa` >> fs[ci_mono_def]) >>
  `not_fresh_at sc root` by
    (irule loweringShapeDefsTheory.not_fresh_at_mono >> qexists `sb` >> fs[ci_mono_def]) >>
  `ptr_covers Gv tv root v n` by
    (irule ptr_covers_frame >> qexistsl [`Gu`,`u`,`tu`] >> simp[]) >>
  `FLOOKUP v.vs_allocas sa.cs_next_id = SOME (w2n bw,n)` by
    (qpat_assum `v.vs_allocas = u.vs_allocas` SUBST1_TAC >> first_assum ACCEPT_TAC) >>
  qpat_assum `stmt_state_rel H0 _ _ _ _ _ s`
    (mp_tac o MATCH_MP (Q.INST [`start` |-> `w2n (bw:bytes32)`, `cut` |-> `sa`]
                        prefix_protected_subranges)) >>
  impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC) >> strip_tac >>
  `!a k. (a+k <= lo \/
          (?name b len. local_region cenv es.scopes s name b len /\ b <= a /\ a+k <= b+len) \/
          (?aid b len. aid < sa.cs_next_id /\ FLOOKUP s.vs_allocas aid = SOME (b,len) /\
                       b <= a /\ a+k <= b+len)) ==>
     mem_bytes_at a k v.vs_memory = mem_bytes_at a k s.vs_memory /\
     (!i. a <= i /\ i < a+k /\ i IN tv.t_mem ==> i IN tn.t_mem)` by
    (rpt gen_tac >> disch_tac >>
     qpat_assum `!a k. _ ==> (_ \/ _) /\ a+k <= s.vs_alloca_next`
       (qspecl_then [`a`,`k`] mp_tac) >>
     impl_tac >- first_assum ACCEPT_TAC >> disch_then (CONJUNCTS_THEN assume_tac) >>
     conj_tac >- (qpat_assum `!a k. _ \/ _ ==> mem_bytes_at a k v.vs_memory = _` irule >> simp[]) >>
     rpt strip_tac >> `i < s.vs_alloca_next` by decide_tac >> simp[]) >>
  `!name b len. local_region cenv es.scopes s name b len ==>
       mem_bytes_at b len v.vs_memory = mem_bytes_at b len s.vs_memory /\
       (!i. b <= i /\ i < b+len /\ i IN tv.t_mem ==> i IN tn.t_mem)` by
    (rpt gen_tac >> strip_tac >>
     qpat_assum `!a k. _ \/ _ \/ _ ==> mem_bytes_at a k v.vs_memory = _ /\ _`
       (qspecl_then [`b`,`len`] mp_tac) >> metis_tac[LESS_EQ_REFL]) >>
  `!aid b len. aid < sa.cs_next_id /\ FLOOKUP s.vs_allocas aid = SOME (b,len) ==>
       mem_bytes_at b len v.vs_memory = mem_bytes_at b len s.vs_memory /\
       (!i. b <= i /\ i < b+len /\ i IN tv.t_mem ==> i IN tn.t_mem)` by
    (rpt gen_tac >> strip_tac >>
     qpat_assum `!a k. _ \/ _ \/ _ ==> mem_bytes_at a k v.vs_memory = _ /\ _`
       (qspecl_then [`b`,`len`] mp_tac) >> metis_tac[LESS_EQ_REFL]) >>
  `wb_frame cenv es es sa s v` by
    (pure_rewrite_tac[wb_frame_def] >> rpt conj_tac
     >- (rpt strip_tac >> simp[])
     >- first_assum ACCEPT_TAC
     >- (rpt strip_tac >>
         qpat_assum `!aid b len. aid < sa.cs_next_id /\ FLOOKUP _ aid = SOME (b,len) ==> _ /\ _`
           (drule_all_then (ACCEPT_TAC o CONJUNCT1))) >>
     irule locals_kept_regions >> rpt strip_tac >>
     qpat_assum `!name b len. local_region _ _ s name b len ==> _ /\ _`
       (drule_then (ACCEPT_TAC o CONJUNCT1))) >>
  `ghost_kept_at lo cenv es sa G tn s Gv tv` by
    (pure_rewrite_tac[ghost_kept_at_def] >> rpt conj_tac
     >- (rpt strip_tac >> simp[])
     >- (rpt strip_tac >>
         qpat_assum `!aid b len. aid < sa.cs_next_id /\ FLOOKUP _ aid = SOME (b,len) ==> _ /\ _`
           (drule_all_then (strip_assume_tac o CONJUNCT2)) >> simp[]) >>
     rpt strip_tac >>
     qpat_assum `!name b len. local_region _ _ s name b len ==> _ /\ _`
       (drule_then (strip_assume_tac o CONJUNCT2)) >> simp[]) >>
  qexistsl [`bw`,`v`,`Gv`,`tv`] >>
  rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
  simp[AC ADD_ASSOC ADD_COMM]
QED
