(* One successful calldata suffix, with its physical and ghost endpoint shared. *)
Theory bodyFullBuiltinBytestringCalldataRun
Ancestors
  bodyFullBuiltinBytestringCalldataPrefix bodyFullBuiltinBytestringOutBuffer
  bodyFullBuiltinBytestringCopy bodyPtrBytestringBuiltinsCalldataFrame
  bodyPtrBytestringBuiltinsExternalSlice
  bodyPtrBytestringBuiltinsBuffer bodyPtrBytestringBuiltinsBounds
  exprSimCalldataSlice exprSimProps exprLoweringProps bodyPtrDefs
  fragGasOriginPtr fragExec emitHelper emitHelperProps freshWrites
  compileEnv loweringStateRelDefs localPtrsProps ptrDiscipline allocaHistory
  venomExecSemantics venomState venomInst context words list finite_map
  loweringPosts valueEncodingProofs instMemFrontier pred_set vyperTypeInvariants instIdxIndep
  bodyMemoryDefs
  codegenRel bodyPtrBytestringBuiltinsSliceEndpoint exprSimAlloc

(* Instantiate the closed provider before its existential witnesses enter scope. *)
fun calldata_horizons initial target provider =
  let
    val post = fst (dest_forall (find_term (fn tm => is_forall tm andalso
      fst (dest_var (fst (dest_forall tm))) = "H'") (concl provider)))
    val formal = first (fn v => fst (dest_var v) = "H") (free_vars (concl provider))
    val tys = match_type (type_of (pairSyntax.mk_pair (formal,post)))
      (type_of (pairSyntax.mk_pair (initial,target)))
  in INST [inst tys formal |-> initial] (INST_TYPE tys provider) end;

Theorem bytestring_calldata_full_run:
  compile_slice_calldata start (Lit (n2w n)) N sa = (out,sb) /\
  fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
  local_ptrs_reserved cenv sa /\
  stmt_state_rel H0 ctx func cenv cx es s /\ context_well_typed cx /\
  0 < n /\ n < dimword (:256) /\ a < dimword (:256) /\
  32+n <= N /\ N < dimword (:256) /\
  eval_operand start s = SOME (n2w a) /\
  op_prov G start = NONE /\ op_taint tn start = {} /\
  (!x. start = Var x ==> not_fresh_at sa x) /\
  a+n < dimword (:256) /\ a+n <= LENGTH cx.txn.calldata /\
  alloca_history func s /\ allocas_from lo s /\ lo <= s.vs_alloca_next /\
  ~ctx_has_dalloca ctx /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?p w t HG tm.
    out = Var p /\ not_fresh_at sb p /\
    (!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG)
      (s,G,tn) [] (OK t,HG,tm)) /\
    t.vs_current_bb = sb.cs_current_bb /\
    t.vs_inst_idx = LENGTH sb.cs_current_insts /\ ~t.vs_halted /\
    lookup_var p t = SOME w /\ ptr_covers HG tm p t N /\
    FLOOKUP t.vs_allocas (sa.cs_next_id+7) = SOME (w2n w,N) /\
    w2n w+N < dimword (:256) /\ w2n w+N <= t.vs_alloca_next /\
    val_in_memory (BaseTV (BytesT (Dynamic n)))
      (BytesV (TAKE n (DROP a cx.txn.calldata))) (w2n w) t.vs_memory /\
    (!i. w2n w <= i /\ i < w2n w+32+n ==> i NOTIN tm.t_mem) /\
    (!H'. stmt_state_rel H' ctx func cenv cx es s ==>
       stmt_state_rel H' ctx func cenv cx es t) /\
    alloca_history func t /\ allocas_from lo t /\ lo <= t.vs_alloca_next /\
    (!x. not_fresh_at sa x ==>
      lookup_var x t = lookup_var x s /\ FLOOKUP HG x = FLOOKUP G x /\
      op_taint tm (Var x) = op_taint tn (Var x)) /\
    (!aid e. FLOOKUP s.vs_allocas aid = SOME e ==>
      FLOOKUP t.vs_allocas aid = SOME e) /\
    (!aid b len. FLOOKUP s.vs_allocas aid = SOME (b,len) /\
      aid < sa.cs_next_id ==>
      mem_bytes_at b len t.vs_memory = mem_bytes_at b len s.vs_memory) /\
    (!name b len. local_region cenv es.scopes s name b len ==>
      mem_bytes_at b len t.vs_memory = mem_bytes_at b len s.vs_memory /\
      (!i. b <= i /\ i < b+len /\ i IN tm.t_mem ==> i IN tn.t_mem)) /\
    mem_bytes_at 0 lo t.vs_memory = mem_bytes_at 0 lo s.vs_memory /\
    tm.t_stor = tn.t_stor /\ tm.t_trans = tn.t_trans /\ tm.t_imm = tn.t_imm /\
    ghost_kept_at lo cenv es sa G tn s HG tm /\
    locals_kept cenv es es s t /\ pure_frame cenv func es sa s t
Proof
  strip_tac >> drule compile_slice_calldata_stages >> strip_tac >>
  `fn_has_code sa s2 func /\ fn_has_code s2 s3 func /\
   fn_has_code s3 s4 func /\ fn_has_code s4 sb func` by
    metis_tac[fn_has_code_split, cs_extends_trans] >>
  `s.vs_call_ctx.cc_calldata = cx.txn.calldata` by
    fs[stmt_state_rel_def, state_rel_def, call_ctx_rel_def] >>
  `LENGTH s.vs_call_ctx.cc_calldata < dimword (:256)` by
    fs[context_well_typed_def, dimword_def] >>
  (fn (asl,w) => qpat_assum `stmt_state_rel H0 ctx func cenv cx es s`
    (fn th => mp_tac (Q.INST [`sb` |-> `s2`,`sm` |-> `s1`]
      (calldata_horizons (hd (snd (strip_comb (concl th))))
        (hd (snd (strip_comb (concl th)))) bytestring_calldata_prefix_full_run))) (asl,w)) >>
  impl_tac >- simp[] >>
  disch_then (qx_choose_then `u` (qx_choose_then `G1`
    (qx_choose_then `tn1` strip_assume_tac))) >>
  `stmt_state_rel H0 ctx func cenv cx es u` by
    (qpat_assum `!H'. _ ==> stmt_state_rel _ _ _ _ _ _ u`
      (qspec_then `H0` match_mp_tac) >> simp[]) >>
  `allocas_from lo u /\ lo <= u.vs_alloca_next` by
    (qpat_assum `u = s with <|vs_vars := _; vs_inst_idx := _|>` SUBST1_TAC >>
     simp[allocas_from_def] >> qpat_assum `allocas_from lo s`
       (ACCEPT_TAC o REWRITE_RULE[allocas_from_def])) >>
  `sa.cs_next_var <= s2.cs_next_var /\ sa.cs_next_id <= s2.cs_next_id /\
   s2.cs_next_id = sa.cs_next_id+7` by
    (qpat_assum `emit_op CALLDATASIZE [] sa = _`
       (mp_then Any strip_assume_tac emitted_insts_emit_op) >>
     drule compile_assert_slice_bounds_layout >> simp[]) >>
  `local_ptrs_reserved cenv s2` by
    (fs[local_ptrs_reserved_def] >> rpt strip_tac >>
     metis_tac[freshWritesTheory.not_fresh_at_mono]) >>
  `u.vs_labels = s.vs_labels` by
    (qpat_assum `u = s with <|vs_vars := _; vs_inst_idx := _|>`
      (mp_tac o Q.AP_TERM `\st. st.vs_labels`) >> simp[]) >>
  qpat_assum `u = s with <|vs_vars := _; vs_inst_idx := _|>`
    (assume_tac o SIMP_RULE (srw_ss()) [] o
      Q.AP_TERM `\st. st.vs_call_ctx.cc_calldata`) >>
  `eval_operand start u = SOME (n2w a) /\
   op_prov G1 start = NONE /\ op_taint tn1 start = {}` by
    (Cases_on `start` >> gvs[eval_operand_def, op_prov_def, op_taint_def] >>
     metis_tac[]) >>
  `32 <= N` by decide_tac >>
  (fn (asl,w) =>
    let val post = fst (dest_forall (find_term (fn tm => is_forall tm andalso
      fst (dest_var (fst (dest_forall tm))) = "H'") w))
    in qpat_assum `stmt_state_rel H0 ctx func cenv cx es u` (fn th =>
      mp_tac (Q.INST [`sa` |-> `s2`,`sb` |-> `s3`, `s` |-> `u`,
        `G` |-> `G1`,`tn` |-> `tn1`, `root` |-> `out`, `n` |-> `N`]
        (calldata_horizons (hd (snd (strip_comb (concl th)))) post
          bytestring_out_buffer_full_run))) (asl,w) end) >>
  impl_tac >- simp[] >>
  disch_then (qx_choose_then `root` (qx_choose_then `dst`
    (qx_choose_then `w` (qx_choose_then `v` (qx_choose_then `G2`
      (qx_choose_then `tn2` strip_assume_tac)))))) >>
  qpat_assum `out = Var root` SUBST_ALL_TAC >>
  qpat_assum `data = Var dst` SUBST_ALL_TAC >>
  qpat_assum `v with <|vs_vars := _; vs_allocas := _;
      vs_alloca_next := _; vs_inst_idx := _|> = u`
    (assume_tac o SIMP_RULE (srw_ss()) [] o
      Q.AP_TERM `\st. st.vs_call_ctx.cc_calldata`) >>
  `v.vs_call_ctx.cc_calldata = cx.txn.calldata` by metis_tac[] >>
  `v.vs_labels = u.vs_labels` by
    (qpat_assum `v with <|vs_vars := _; vs_allocas := _;
      vs_alloca_next := _; vs_inst_idx := _|> = u`
       (mp_tac o Q.AP_TERM `\st. st.vs_labels`) >> simp[]) >>
  `eval_operand start v = SOME (n2w a) /\ op_taint tn2 start = {}` by
    (Cases_on `start` >> gvs[eval_operand_def, op_taint_def] >>
     metis_tac[freshWritesTheory.not_fresh_at_mono]) >>
  `w2n (w+32w) = w2n w+32` by
    (`w2n w+32 < dimword (:256)` by decide_tac >>
     simp[w2n_add_2, w2n_n2w]) >>
  `ptr_covers G2 tn2 dst v n` by
    (fs[ptr_covers_def] >> metis_tac[arithmeticTheory.LESS_EQ_TRANS]) >>
  qabbrev_tac `bytes = TAKE n (DROP a cx.txn.calldata)` >>
  `LENGTH bytes = n` by simp[Abbr `bytes`, LENGTH_TAKE_EQ] >>
  `step_inst_base (mk_inst s3.cs_next_id CALLDATACOPY
       [Var dst;start;Lit (n2w n)] []) v =
     OK (write_memory_with_expansion (w2n (w+32w)) bytes v)` by
    (qspecl_then [`Var dst`,`start`,`Lit (n2w n)`,`v`,`w+32w`,
       `n2w a`,`n2w n`,`s3.cs_next_id`] mp_tac calldata_copy_step >>
     simp[eval_operand_def, Abbr `bytes`, w2n_n2w]) >>
  mp_tac (bytestring_external_copy_length_full_run |> Q.INST
    [`sa` |-> `s3`,`sm` |-> `s4`,`s` |-> `v`, `G` |-> `G2`,
     `tn` |-> `tn2`, `opc` |-> `CALLDATACOPY`,
     `ops` |-> `[Var dst;start;Lit (n2w n)]`, `cnt` |-> `Lit (n2w n)`,
     `wd` |-> `w+32w`, `wa` |-> `n2w a`, `wn` |-> `n2w n`, `b` |-> `w`]) >>
  impl_tac >- simp[eval_operand_def, op_taint_def, w2n_n2w] >>
  disch_then (qx_choose_then `vc` (qx_choose_then `t`
    (qx_choose_then `tm` strip_assume_tac))) >>
  `t = mstore (w2n w) (n2w n)
      (write_memory_with_expansion (w2n w+32) bytes v)
        with vs_inst_idx := LENGTH sb.cs_current_insts` by
    (qpat_assum `t = _` mp_tac >> qpat_assum `vc = _` mp_tac >>
     qpat_assum `t.vs_inst_idx = LENGTH sb.cs_current_insts` mp_tac >>
     qpat_assum `w2n (w+32w) = w2n w+32` mp_tac >>
     rpt (pop_assum kall_tac) >> rpt strip_tac >>
     gvs[mstore_idx]) >>
  `!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG)
      (s,G,tn) [] (OK t,G2,tm)` by
    (gen_tac >>
     qpat_assum `!D. gas_origin_ptr_path _ (s,G,tn) _ _`
       (qspec_then `D` mp_tac) >>
     qpat_assum `!D. gas_origin_ptr_path _ (u,G1,tn1) _ _`
       (qspec_then `D` mp_tac) >>
     qpat_assum `!D. gas_origin_ptr_path _ (v,G2,tn2) _ _`
       (qspec_then `D` mp_tac) >>
     rpt (pop_assum kall_tac) >> metis_tac[gas_origin_ptr_path_append, APPEND_NIL]) >>
  `t.vs_vars = v.vs_vars /\ t.vs_allocas = v.vs_allocas /\
   t.vs_alloca_next = v.vs_alloca_next` by
    (qpat_assum `vc = _`
       (strip_assume_tac o SIMP_RULE (srw_ss()) [write_memory_with_expansion_def, LET_THM] o
         Q.AP_TERM `\st. (st.vs_vars,st.vs_allocas,st.vs_alloca_next)`) >>
     qpat_assum `t = _`
       (strip_assume_tac o SIMP_RULE (srw_ss()) [mstore_def, write_memory_with_expansion_def, LET_THM] o
         Q.AP_TERM `\st. (st.vs_vars,st.vs_allocas,st.vs_alloca_next)`) >>
     rpt conj_tac >> first_assum ACCEPT_TAC) >>
  `u.vs_allocas = s.vs_allocas /\ u.vs_alloca_next = s.vs_alloca_next /\
   u.vs_memory = s.vs_memory` by
    (qpat_assum `u = s with <|vs_vars := _; vs_inst_idx := _|>`
      (ACCEPT_TAC o SIMP_RULE (srw_ss()) [] o
        Q.AP_TERM `\st. (st.vs_allocas,st.vs_alloca_next,st.vs_memory)`)) >>
  `v.vs_memory = s.vs_memory` by
    (qpat_assum `v with <|vs_vars := _; vs_allocas := _;
        vs_alloca_next := _; vs_inst_idx := _|> = u`
      (assume_tac o SIMP_RULE (srw_ss()) [] o Q.AP_TERM `\st. st.vs_memory`) >>
     metis_tac[]) >>
  `lookup_var root t = SOME w` by fs[lookup_var_def] >>
  `FLOOKUP v.vs_allocas (sa.cs_next_id+7) = SOME (w2n w,N)` by
    (qpat_assum `s2.cs_next_id = sa.cs_next_id+7` (fn id =>
      qpat_assum `FLOOKUP v.vs_allocas s2.cs_next_id = SOME (w2n w,N)`
        (ACCEPT_TAC o REWRITE_RULE[id]))) >>
  `FLOOKUP t.vs_allocas (sa.cs_next_id+7) = SOME (w2n w,N)` by
    (simp[] >> qpat_assum `s2.cs_next_id = sa.cs_next_id+7` (fn id =>
      qpat_assum `FLOOKUP v.vs_allocas s2.cs_next_id = SOME (w2n w,N)`
        (ACCEPT_TAC o REWRITE_RULE[id]))) >>
  `lo <= t.vs_alloca_next` by decide_tac >>
  `allocas_from lo t` by
    (qpat_assum `allocas_from lo v` mp_tac >>
     simp[NoAsms, allocas_from_def] >> simp[]) >>
  `!aid e. FLOOKUP s.vs_allocas aid = SOME e ==>
     FLOOKUP t.vs_allocas aid = SOME e` by
    (rpt strip_tac >> simp[] >>
     qpat_assum `!aid e. FLOOKUP u.vs_allocas aid = SOME e ==> _` irule >> simp[]) >>
  `!x. not_fresh_at sa x ==>
     lookup_var x t = lookup_var x s /\ FLOOKUP G2 x = FLOOKUP G x /\
     op_taint tm (Var x) = op_taint tn (Var x)` by
    (rpt strip_tac >>
     `not_fresh_at s2 x` by
       (irule freshWritesTheory.not_fresh_at_mono >> qexists_tac `sa` >> simp[]) >>
     qpat_assum `!x. not_fresh_at sa x ==> lookup_var x u = _ /\ _` mp_tac >>
     qpat_assum `!x. not_fresh_at s2 x ==> lookup_var x v = _ /\ _` mp_tac >>
     qpat_assum `t.vs_vars = v.vs_vars` mp_tac >>
     qpat_assum `tm.t_var = tn2.t_var` mp_tac >>
     qpat_assum `not_fresh_at sa x` mp_tac >>
     qpat_assum `not_fresh_at s2 x` mp_tac >>
     rpt (pop_assum kall_tac) >> rpt strip_tac >>
     fs[lookup_var_def, op_taint_def] >> metis_tac[]) >>
  `tm.t_mem = (tn2.t_mem DIFF
      {i | w2n (w+32w) <= i /\ i < w2n (w+32w)+n})
      DIFF {i | w2n w <= i /\ i < w2n w+32}` by
    (qpat_assum `tm.t_mem = _` mp_tac >>
     simp[source_memory_write_ranges_def, sized_source_write_range_def,
       range_bytes_def, mk_inst_def, eval_operand_def, w2n_n2w, EXTENSION]) >>
  `!i. w2n w <= i /\ i < w2n w+32+n ==> i NOTIN tm.t_mem` by
    (mp_tac (INST_TYPE [alpha |-> ``:256``] external_slice_written_taint |> Q.INST
       [`a` |-> `w`,`wn` |-> `(n2w n:bytes32)`,`dirty` |-> `tn2.t_mem`]) >>
     simp[w2n_n2w]) >>
  `?inst. MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\
     inst.inst_id = s2.cs_next_id` by
    (drule compile_slice_out_buf_compiler_parts >> strip_tac >>
     rename1 `compile_alloc_buffer _ _ = (abuf,asc)` >>
     qspecl_then [`s2`,`asc`,`s3`,`func`] mp_tac fn_has_code_split >>
     simp[] >> strip_tac >>
     qspecl_then [`N`,`s2`,`asc`,`abuf`,`func`] mp_tac buffer_alloc_code >>
     simp[] >> strip_tac >>
     qexists_tac `mk_inst s2.cs_next_id ALLOCA [Lit (n2w N)]
       [STRING #"%" (toString s2.cs_next_var)]` >> simp[mk_inst_def] >>
     qpat_assum `MEM (mk_inst _ ALLOCA _ _) (fn_insts func)`
       (ACCEPT_TAC o REWRITE_RULE[mk_inst_def])) >>
  rename1 `MEM allocinst (fn_insts func)` >>
  `tm.t_mem SUBSET tn2.t_mem` by
    (qpat_assum `tm.t_mem = (tn2.t_mem DIFF
       {i | w2n (w+32w) <= i /\ i < w2n (w+32w)+n}) DIFF _` SUBST1_TAC >>
     simp[SUBSET_DEF]) >>
  `!i. i < s.vs_alloca_next /\ i IN tm.t_mem ==> i IN tn.t_mem` by
    (rpt strip_tac >>
     `i IN tn2.t_mem` by
       (qpat_assum `tm.t_mem SUBSET tn2.t_mem`
         (qspec_then `i` mp_tac o REWRITE_RULE[SUBSET_DEF]) >> simp[]) >>
     qpat_assum `!i. i IN tn2.t_mem <=> _` (qspec_then `i` mp_tac) >>
     simp[] >> decide_tac) >>
  `!name b len. local_region cenv es.scopes s name b len ==>
      local_region cenv es.scopes v name b len` by
    (rpt strip_tac >> irule local_region_frame_fwd >>
     qexistsl_tac [`s`,`sa`,`es.scopes`] >> simp[] >>
     rpt strip_tac >>
     qpat_assum `!x. not_fresh_at sa x ==> lookup_var x t = _ /\ _`
       mp_tac >>
     qpat_assum `t.vs_vars = v.vs_vars` mp_tac >>
     qpat_assum `not_fresh_at sa x` mp_tac >>
     qpat_assum `lookup_var x s = SOME _` mp_tac >>
     rpt (pop_assum kall_tac) >> rpt strip_tac >>
     fs[lookup_var_def] >> metis_tac[]) >>
  qpat_assum `t = _`
    (assume_tac o SIMP_RULE (srw_ss()) [] o Q.AP_TERM `\st. st.vs_memory`) >>
  `!off len. regions_disjoint off len (w2n w) N ==>
     mem_bytes_at off len t.vs_memory = mem_bytes_at off len s.vs_memory` by
    (rpt strip_tac >>
     qpat_assum `t.vs_memory = _` (fn th => once_rewrite_tac[th]) >>
     qpat_assum `v.vs_memory = s.vs_memory`
       (fn th => pure_once_rewrite_tac[GSYM th]) >>
     `n2w n = (n2w (LENGTH bytes):bytes32)` by simp[] >>
     pop_assum SUBST1_TAC >> irule bytes_buffer_write_frame >>
     fs[regions_disjoint_def] >> decide_tac) >>
  `!name b len. local_region cenv es.scopes s name b len ==>
     mem_bytes_at b len t.vs_memory = mem_bytes_at b len s.vs_memory` by
    (rpt strip_tac >>
     qpat_assum `!off len. regions_disjoint _ _ _ _ ==> _` irule >>
     qpat_assum `!name b len. local_region _ _ v _ _ _ ==> _`
       (qspecl_then [`name`,`b`,`len`] mp_tac) >>
     impl_tac
     >- (qpat_assum `!name b len. local_region _ _ s _ _ _ ==> _`
           (qspecl_then [`name`,`b`,`len`] match_mp_tac) >> simp[]) >>
     simp[regions_disjoint_def] >> decide_tac) >>
  `!aid b sz. FLOOKUP s.vs_allocas aid = SOME (b,sz) ==>
     b+sz <= s.vs_alloca_next` by
    (qpat_assum `stmt_state_rel H0 ctx func cenv cx es s`
      (mp_tac o CONJUNCT1 o CONJUNCT2 o REWRITE_RULE[stmt_state_rel_def]) >>
     rpt (pop_assum kall_tac) >>
     simp[venomMemDefsTheory.alloca_inv_def,
       venomMemDefsTheory.alloca_next_valid_def] >>
     strip_tac >> first_assum ACCEPT_TAC) >>
  `!name b len. local_region cenv es.scopes s name b len ==>
     mem_bytes_at b len t.vs_memory = mem_bytes_at b len s.vs_memory /\
     (!i. b <= i /\ i < b+len /\ i IN tm.t_mem ==> i IN tn.t_mem)` by
    (rpt gen_tac >> disch_tac >> conj_tac
     >- (qpat_assum `!name b len. local_region _ _ s _ _ _ ==>
           mem_bytes_at _ _ _ = _`
           (qspecl_then [`name`,`b`,`len`] match_mp_tac) >> simp[]) >>
     rpt strip_tac >>
     qpat_assum `!i. i < s.vs_alloca_next /\ _ ==> _` irule >> simp[] >>
     `b+len <= s.vs_alloca_next` by
       (drule_all body_local_region_frontier >> simp[]) >> decide_tac) >>
  `ghost_kept_at lo cenv es sa G tn s G2 tm` by
    (rewrite_tac[ghost_kept_at_def] >> rpt conj_tac
     >- (rpt strip_tac >>
         qpat_assum `!x. not_fresh_at sa x ==> lookup_var x t = _ /\ _`
           (qspec_then `x` mp_tac) >> simp[])
     >- (rpt strip_tac >>
         qpat_assum `!i. i < s.vs_alloca_next /\ _ ==> _` irule >> simp[] >>
         `off+sz <= s.vs_alloca_next` by
           (qpat_assum `!aid b sz. FLOOKUP s.vs_allocas aid = SOME (b,sz) ==> _`
             (qspecl_then [`aid`,`off`,`sz`] match_mp_tac) >> simp[]) >>
         decide_tac)
     >- (rpt strip_tac >>
         qpat_assum `!i. i < s.vs_alloca_next /\ _ ==> _` irule >> simp[] >>
         `b+sz <= s.vs_alloca_next` by
           (drule_all body_local_region_frontier >> simp[]) >> decide_tac) >>
     rpt strip_tac >>
     qpat_assum `!i. i < s.vs_alloca_next /\ _ ==> _` irule >> simp[] >>
     decide_tac) >>
  `locals_kept cenv es es s t` by
    (irule locals_kept_regions >> first_assum ACCEPT_TAC) >>
  `!aid b len. FLOOKUP s.vs_allocas aid = SOME (b,len) /\ aid < sa.cs_next_id ==>
     mem_bytes_at b len t.vs_memory = mem_bytes_at b len s.vs_memory` by
    (rpt strip_tac >>
     qpat_assum `!off len. regions_disjoint _ _ _ _ ==> _` irule >>
     qpat_assum `!aid b len. _ /\ _ ==> regions_disjoint _ _ _ _`
       (qspecl_then [`aid`,`b`,`len`] mp_tac) >>
     impl_tac >- (simp[] >> decide_tac) >>
     simp[regions_disjoint_def] >> decide_tac) >>
  `lo <= w2n w` by
    (qpat_assum `allocas_from lo t`
      (qspecl_then [`sa.cs_next_id+7`,`w2n w`,`N`] match_mp_tac o
        REWRITE_RULE[allocas_from_def]) >> first_assum ACCEPT_TAC) >>
  `mem_bytes_at 0 lo t.vs_memory = mem_bytes_at 0 lo s.vs_memory` by
    (qpat_assum `!off len. regions_disjoint _ _ _ _ ==> _`
      (qspecl_then [`0`,`lo`] match_mp_tac) >> simp[regions_disjoint_def]) >>
  `pure_frame cenv func es sa s t` by
    (rewrite_tac[pure_frame_def] >> conj_tac
     >- first_assum ACCEPT_TAC >>
     rpt strip_tac >>
     qpat_assum `!off len. regions_disjoint _ _ _ _ ==> _` irule >>
     qpat_assum `!inst b sz. _ ==> regions_disjoint off len b sz`
       (qspecl_then [`allocinst`,`w2n w`,`N`] match_mp_tac) >> simp[]) >>
  `alloca_history func t` by
    (qpat_assum `emit_void CALLDATACOPY _ _ = _`
       (mp_then Any strip_assume_tac emitted_insts_emit_void) >>
     qpat_assum `emit_void MSTORE _ _ = _`
       (mp_then Any strip_assume_tac emitted_insts_emit_void) >>
     qpat_assum `emit_void CALLDATACOPY _ _ = _`
       (mp_then Any mp_tac emit_void_extends) >>
     simp[same_blocks_def] >> strip_tac >>
     qpat_assum `emit_void MSTORE _ _ = _`
       (mp_then Any mp_tac emit_void_extends) >>
     simp[same_blocks_def] >> strip_tac >>
     qpat_assum `vc = _`
       (strip_assume_tac o SIMP_RULE (srw_ss())
         [write_memory_with_expansion_def, LET_THM] o
         Q.AP_TERM `\st. (st.vs_allocas,st.vs_current_bb,st.vs_inst_idx)`) >>
     `vc.vs_current_bb = s4.cs_current_bb /\
      vc.vs_inst_idx = LENGTH s4.cs_current_insts` by simp[] >>
     qspecl_then [`s3`,`s4`,`func`,
       `[mk_inst s3.cs_next_id CALLDATACOPY [Var dst;start;Lit (n2w n)] []]`]
       mp_tac fn_has_code_same_block >> simp[] >>
     disch_then (qx_choose_then `copybb` strip_assume_tac) >>
     `get_instruction copybb v.vs_inst_idx =
       SOME (mk_inst s3.cs_next_id CALLDATACOPY [Var dst;start;Lit (n2w n)] [])` by
       simp[] >>
     `alloca_history func (v with vs_inst_idx := SUC v.vs_inst_idx)` by
       (irule history_nonalloca_advance >> conj_tac
        >- (qexistsl_tac [`copybb`,
          `mk_inst s3.cs_next_id CALLDATACOPY [Var dst;start;Lit (n2w n)] []`] >>
            simp[mk_inst_def]) >> first_assum ACCEPT_TAC) >>
     `alloca_history func vc` by
       (irule alloca_history_frame >>
        qexists_tac `v with vs_inst_idx := SUC v.vs_inst_idx` >> simp[]) >>
     qspecl_then [`s4`,`sb`,`func`,
       `[mk_inst s4.cs_next_id MSTORE [Var root;Lit (n2w n)] []]`]
       mp_tac fn_has_code_same_block >> simp[] >>
     strip_tac >>
     `get_instruction copybb vc.vs_inst_idx =
       SOME (mk_inst s4.cs_next_id MSTORE [Var root;Lit (n2w n)] [])` by
       simp[] >>
     `alloca_history func (vc with vs_inst_idx := SUC vc.vs_inst_idx)` by
       (irule history_nonalloca_advance >> conj_tac
        >- (qexistsl_tac [`copybb`,`mk_inst s4.cs_next_id MSTORE [Var root;Lit (n2w n)] []`] >>
            simp[mk_inst_def]) >> first_assum ACCEPT_TAC) >>
     irule alloca_history_frame >>
     qexists_tac `vc with vs_inst_idx := SUC vc.vs_inst_idx` >>
     simp[] >> simp[NoAsms, mstore_def, write_memory_with_expansion_def, LET_THM] >>
     simp[]) >>
  qexistsl_tac [`root`,`w`,`t`,`G2`,`tm`] >>
  asm_simp_tac bool_ss [] >> rpt conj_tac >>
  TRY (first_assum ACCEPT_TAC)
  >- (irule freshWritesTheory.not_fresh_at_mono >> qexists_tac `s3` >>
      simp[] >> qpat_assum `emit_void CALLDATACOPY _ _ = _`
        (mp_then Any strip_assume_tac emitted_insts_emit_void) >>
      qpat_assum `emit_void MSTORE _ _ = _`
        (mp_then Any strip_assume_tac emitted_insts_emit_void) >> simp[]) >>
  TRY (first_assum ACCEPT_TAC)
  >- (qpat_assum `t = _` SUBST1_TAC >>
      qspecl_then [`a`,`n`,`cx.txn.calldata`,`w2n w`,`n`,`v`]
        mp_tac calldata_slice_write_encoding >>
      simp[Abbr `bytes`]) >>
  TRY (first_assum ACCEPT_TAC)
  >- (rpt strip_tac >>
      `stmt_state_rel H' ctx func cenv cx es u` by
        (qpat_assum `stmt_state_rel H' ctx func cenv cx es s` mp_tac >>
         qpat_assum `!x. not_fresh_at sa x ==> lookup_var x u = _ /\ _` mp_tac >>
         qpat_assum `u = s with <|vs_vars := _; vs_inst_idx := _|>` mp_tac >>
         qpat_assum `local_ptrs_reserved cenv sa` mp_tac >>
         rpt (pop_assum kall_tac) >> rpt strip_tac >>
         qpat_assum `u = _` SUBST1_TAC >>
         simp[stmt_state_rel_inst_idx] >> irule stmt_state_rel_vars_frame >>
         fs[local_ptrs_reserved_def, lookup_var_def, stmt_state_rel_inst_idx] >>
         metis_tac[]) >>
      `stmt_state_rel H' ctx func cenv cx es v` by
        ((fn (asl,w) =>
          qpat_assum `!h. _ ==> stmt_state_rel _ _ _ _ _ _ v`
            (match_mp_tac o ISPEC (hd (snd (strip_comb w)))) (asl,w)) >> simp[]) >>
      qpat_assum `t = _` SUBST1_TAC >>
      simp[NoAsms, stmt_state_rel_inst_idx] >>
      irule allocated_bytes_write_state_rel >>
      conj_tac >- first_assum ACCEPT_TAC >> conj_tac
      >- (qexistsl_tac [`N`,`allocinst`] >> rpt conj_tac >>
          TRY (first_assum ACCEPT_TAC) >> metis_tac[]) >>
      first_assum ACCEPT_TAC) >>
  metis_tac[]
QED
