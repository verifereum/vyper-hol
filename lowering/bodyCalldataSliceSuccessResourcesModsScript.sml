(* The successful calldata slice uses one buffer cut and one pair of writes. *)
Theory bodyCalldataSliceSuccessResourcesMods
Ancestors
  bodyCalldataSliceBufferDeltaMods bodyCalldataSliceWritesFrameMods
  bodyFullBuiltinBytestringCalldataPrefix bodyFullBuiltinBytestringCopy
  bodyPtrBytestringBuiltinsExternalSlice bodyPtrBytestringBuiltinsCalldataFrame
  bodyPtrBytestringBuiltinsBounds bodyPtrBytestringBuiltinsBuffer
  bodyFullPathHistory bodyFullHashKeccakFixed[qualified]
  decoderOriginAllocationFrame[qualified] bodyMemAggregatePath[qualified]
  fragGasOrigin[qualified] fragGasMode[qualified] fragGasOriginPtr
  exprSimCalldataSlice exprSimAlloc exprSimProps exprLoweringProps
  fragExec emitHelper emitHelperProps freshWrites allocaHistory compileEnv
  loweringStateRelDefs bodyMemoryDefs loweringPosts bodyPtrDefs ptrDiscipline
  venomExecSemantics venomMemDefs venomState venomInst context
  list words finite_map pred_set vyperTypeInvariants

Triviality slice_prefix_state_rel:
  stmt_state_rel H ctx func cenv cx es s /\ local_ptrs_reserved cenv sa /\
  u = s with <|vs_vars := u.vs_vars; vs_inst_idx := idx|> /\
  (!x. not_fresh_at sa x ==> lookup_var x u = lookup_var x s) ==>
  stmt_state_rel H ctx func cenv cx es u
Proof
  strip_tac >>
  `!x. not_fresh_at sa x ==> lookup_var x (s with vs_vars := u.vs_vars) =
                            lookup_var x s` by
    (qpat_assum `!x. _ ==> lookup_var x u = _` mp_tac >>
     qpat_assum `u = _` (fn th => CONV_TAC (LAND_CONV (ONCE_REWRITE_CONV [th]))) >>
     simp[lookup_var_def]) >>
  qpat_assum `u = _` (fn th => once_rewrite_tac[th]) >>
  simp[stmt_state_rel_inst_idx] >> irule stmt_state_rel_vars_frame >>
  fs[local_ptrs_reserved_def, lookup_var_def, stmt_state_rel_inst_idx] >> metis_tac[]
QED

Triviality slice_empty_path_join:
  (!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn) [] (OK u,G1,tn1)) /\
  (!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (u,G1,tn1) [] (OK v,G2,tn2)) ==>
  !D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn) [] (OK v,G2,tn2)
Proof
  strip_tac >> gen_tac >>
  first_x_assum (qspec_then `D` assume_tac) >>
  first_x_assum (qspec_then `D` assume_tac) >>
  metis_tac[gas_origin_ptr_path_append, APPEND_NIL]
QED

Triviality slice_buffer_below_fmp:
  gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (u,G1,tn1) [] (OK v,G2,tn2) /\
  stmt_state_rel H ctx func cenv cx es u /\ fn_inst_ids_distinct func /\
  v.vs_fmp = u.vs_fmp /\
  (ctx_has_dalloca ctx ==>
     u.vs_alloca_next + pending_alloca_size func u <= w2n u.vs_initial_fmp) ==>
  ctx_has_dalloca ctx ==> allocas_below_fmp v
Proof
  strip_tac >> strip_tac >>
  `allocas_below_fmp u` by
    (drule bodyFullHashKeccakFixedTheory.stmt_state_rel_allocas_below_fmp >> simp[]) >>
  `alloca_inv u` by fs[stmt_state_rel_def] >>
  `gas_path_mem ctx func u 0 (OK v)` by
    (drule gas_origin_ptr_path_projections >>
     disch_then (mp_tac o MATCH_MP fragGasOriginTheory.gas_origin_path_erase o CONJUNCT1) >>
     simp[fragGasModeTheory.gas_marked_path_def]) >>
  `alloca_inv v` by
    (drule_all bodyMemAggregatePathTheory.aggregate_mem_path_alloca_inv >> simp[]) >>
  qpat_assum `gas_origin_ptr_path _ _ _ _`
    (mp_then Any mp_tac decoderOriginAllocationFrameTheory.decoder_origin_path_allocas_below_fmp) >>
  simp[]
QED

Theorem calldata_slice_success_resources_mods:
  compile_slice_calldata start (Lit (n2w n)) N sa = (out,sb) /\
  fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
  local_ptrs_reserved cenv sa /\
  stmt_state_rel (H0:(bool # 'a word # type_value) list # num list) ctx func cenv cx es s /\
  context_well_typed cx /\
  0 < n /\ n < dimword (:256) /\ a < dimword (:256) /\
  32+n <= N /\ N < dimword (:256) /\
  eval_operand start s = SOME (n2w a) /\
  op_prov G start = NONE /\ op_taint tn start = {} /\
  (!x. start = Var x ==> not_fresh_at sa x) /\
  a+n < dimword (:256) /\ a+n <= LENGTH cx.txn.calldata /\
  alloca_history func s /\ allocas_from lo s /\ lo <= s.vs_alloca_next /\
  (ctx_has_dalloca ctx ==>
     s.vs_alloca_next + pending_alloca_size func s <= w2n s.vs_initial_fmp) /\
  ~s.vs_halted /\
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
    (!(H':(bool # 'b word # type_value) list # num list).
       stmt_state_rel H' ctx func cenv cx es s ==> stmt_state_rel H' ctx func cenv cx es t) /\
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
    (!i. i < lo /\ i IN tm.t_mem ==> i IN tn.t_mem) /\
    tm.t_stor = tn.t_stor /\ tm.t_trans = tn.t_trans /\ tm.t_imm = tn.t_imm /\
    ghost_kept_at lo cenv es sa G tn s HG tm /\
    locals_kept cenv es es s t /\ pure_frame cenv func es sa s t /\
    t.vs_accounts = s.vs_accounts /\ t.vs_transient = s.vs_transient /\
    t.vs_call_ctx = s.vs_call_ctx /\ t.vs_immutables = s.vs_immutables /\
    s.vs_alloca_next <= t.vs_alloca_next /\
    (!off len. off+len <= w2n w \/ w2n w+N <= off ==>
       mem_bytes_at off len t.vs_memory = mem_bytes_at off len s.vs_memory) /\
    t.vs_data_section = s.vs_data_section /\ LENGTH s.vs_memory <= LENGTH t.vs_memory /\
    (!aid b len. FLOOKUP t.vs_allocas aid = SOME (b,len) ==>
       FLOOKUP s.vs_allocas aid = SOME (b,len) \/ s.vs_alloca_next <= b) /\
    (!i. i < s.vs_alloca_next /\ i IN tm.t_mem ==> i IN tn.t_mem) /\
    (?inst. MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\
       inst.inst_id = sa.cs_next_id+7)
Proof
  strip_tac >> drule compile_slice_calldata_stages >> strip_tac >>
  `fn_has_code sa s2 func /\ fn_has_code s2 sb func` by
    (irule fn_has_code_split >> simp[] >> metis_tac[cs_extends_trans]) >>
  `fn_has_code s2 s3 func /\ fn_has_code s3 sb func` by
    (irule fn_has_code_split >> simp[] >> metis_tac[cs_extends_trans]) >>
  `fn_has_code s3 s4 func /\ fn_has_code s4 sb func` by
    (irule fn_has_code_split >> simp[]) >>
  `s.vs_call_ctx.cc_calldata = cx.txn.calldata` by
    fs[stmt_state_rel_def, state_rel_def, call_ctx_rel_def] >>
  `LENGTH s.vs_call_ctx.cc_calldata < dimword (:256)` by
    fs[context_well_typed_def, dimword_def] >>
  `a+n <= LENGTH s.vs_call_ctx.cc_calldata` by simp[] >>
  drule_all bytestring_calldata_prefix_full_run >>
  disch_then (qspecl_then [`explicit`,`PG`] strip_assume_tac) >>
  rename1 `u = s with <|vs_vars := _;vs_inst_idx := _|>` >>
  `!H. stmt_state_rel H ctx func cenv cx es s ==>
       stmt_state_rel H ctx func cenv cx es u` by
    (rpt strip_tac >> irule slice_prefix_state_rel >>
     qexistsl [`LENGTH s2.cs_current_insts`,`s`,`sa`] >> simp[]) >>
  `stmt_state_rel H0 ctx func cenv cx es u` by
    (irule slice_prefix_state_rel >> qexistsl [`LENGTH s2.cs_current_insts`,`s`,`sa`] >> simp[]) >>
  `u.vs_allocas = s.vs_allocas /\ u.vs_alloca_next = s.vs_alloca_next /\
   u.vs_fmp = s.vs_fmp /\ u.vs_initial_fmp = s.vs_initial_fmp /\
   u.vs_memory = s.vs_memory /\ u.vs_call_ctx = s.vs_call_ctx /\
   u.vs_accounts = s.vs_accounts /\ u.vs_transient = s.vs_transient /\
   u.vs_immutables = s.vs_immutables /\ u.vs_data_section = s.vs_data_section /\
   u.vs_labels = s.vs_labels` by
    (qpat_assum `u = _` (fn th => once_rewrite_tac[th]) >> simp[]) >>
  `ctx_has_dalloca ctx ==>
   u.vs_alloca_next + pending_alloca_size func u <= w2n u.vs_initial_fmp` by
    (`pending_alloca_size func u = pending_alloca_size func s` by
       simp[pending_alloca_size_def] >>
     asm_simp_tac bool_ss []) >>
  `allocas_from lo u /\ lo <= u.vs_alloca_next` by
    (conj_tac
     >- (pure_rewrite_tac[allocas_from_def] >> asm_rewrite_tac[] >>
         qpat_assum `allocas_from lo s` (ACCEPT_TAC o REWRITE_RULE[allocas_from_def])) >>
     asm_rewrite_tac[]) >>
  `sa.cs_next_var <= s2.cs_next_var /\ s2.cs_next_id = sa.cs_next_id+7` by
    (drule emitted_insts_emit_op >> strip_tac >>
     drule compile_assert_slice_bounds_layout >> simp[]) >>
  `local_ptrs_reserved cenv s2` by
    (irule local_ptrs_reserved_next_var >> qexists `sa` >> simp[]) >>
  `!x. not_fresh_at sa x ==> not_fresh_at s2 x` by
    (rpt strip_tac >> irule freshWritesTheory.not_fresh_at_mono >>
     qexists `sa` >> simp[]) >>
  `32 <= N` by decide_tac >>
  suspend "buffer_and_copy"
QED

Resume calldata_slice_success_resources_mods[buffer_and_copy]:
  qmatch_asmsub_rename_tac `gas_origin_ptr_path _ (s,G,tn) [] (OK u,G1,tn1)` >>
  drule_all calldata_slice_buffer_delta_mods >>
  disch_then (qspecl_then [`tn1`,`explicit`,`PG`,`G1`]
    (qx_choosel_then [`root`,`dst`,`w`,`v`,`G2`,`tn2`] strip_assume_tac)) >>
  qpat_x_assum `out = Var root` SUBST_ALL_TAC >>
  qpat_x_assum `data = Var dst` SUBST_ALL_TAC >>
  `v.vs_memory = s.vs_memory /\ v.vs_call_ctx = s.vs_call_ctx /\
   v.vs_fmp = u.vs_fmp /\ v.vs_accounts = s.vs_accounts /\
   v.vs_transient = s.vs_transient /\ v.vs_immutables = s.vs_immutables /\
   v.vs_data_section = s.vs_data_section /\ v.vs_labels = s.vs_labels` by
    (qpat_assum `v with <|vs_vars := _; vs_allocas := _;
        vs_alloca_next := _; vs_inst_idx := _|> = u` mp_tac >>
     simp[venom_state_component_equality]) >>
  `ctx_has_dalloca ctx ==> allocas_below_fmp v` by
    (qpat_assum `!D. gas_origin_ptr_path _ (u,G1,tn1) [] (OK v,G2,tn2)`
       (mp_then Any mp_tac slice_buffer_below_fmp o SPEC_ALL) >>
     disch_then (qspecl_then [`es`,`cx`,`cenv`,`H0`] mp_tac) >>
     asm_simp_tac bool_ss []) >>
  `eval_operand start v = SOME (n2w a) /\ op_taint tn2 start = {}` by
    (Cases_on `start` >> gvs[eval_operand_def, op_taint_def] >> metis_tac[]) >>
  `w2n (w + 32w) = w2n w + 32` by
    (`w2n w+32 < dimword (:256)` by decide_tac >> simp[w2n_add_2,w2n_n2w]) >>
  `ptr_covers G2 tn2 dst v n` by
    (irule reasonCopySourcePtrTheory.ptr_covers_mono >>
     qexists `N-32` >> simp[] >> decide_tac) >>
  qabbrev_tac `bytes = TAKE n (DROP a cx.txn.calldata)` >>
  `LENGTH bytes = n` by simp[Abbr `bytes`, LENGTH_TAKE_EQ] >>
  `step_inst_base (mk_inst s3.cs_next_id CALLDATACOPY
      [Var dst;start;Lit (n2w n)] []) v =
    OK (write_memory_with_expansion (w2n (w+32w)) bytes v)` by
    (`TAKE (w2n (n2w n:bytes32)) (DROP (w2n (n2w a:bytes32))
        v.vs_call_ctx.cc_calldata) = bytes` by simp[Abbr `bytes`,w2n_n2w] >>
     pop_assum (fn th => pure_once_rewrite_tac[GSYM th]) >>
     irule calldata_copy_step >> simp[eval_operand_def,w2n_n2w]) >>
  mp_tac (bytestring_external_copy_length_full_run |> Q.INST
    [`sa` |-> `s3`,`sm` |-> `s4`,`s` |-> `v`,`G` |-> `G2`,`tn` |-> `tn2`,
     `opc` |-> `CALLDATACOPY`,`ops` |-> `[Var dst;start;Lit (n2w n)]`,
     `cnt` |-> `Lit (n2w n)`,`wa` |-> `(n2w a:bytes32)`,
     `wn` |-> `(n2w n:bytes32)`,`wd` |-> `w+32w`,`b` |-> `w`]) >>
  impl_tac >- (simp[eval_operand_def,op_taint_def,w2n_n2w] >> decide_tac) >>
  disch_then (qx_choosel_then [`vc`,`t`,`tm`] strip_assume_tac) >>
  suspend "write_endpoint"
QED

Resume calldata_slice_success_resources_mods[write_endpoint]:
  `eval_operand (Var dst) v = SOME (w+32w)` by simp[eval_operand_def] >>
  `eval_operand (Lit (n2w n)) v = SOME (n2w n)` by simp[eval_operand_def] >>
  `w2n (n2w n:bytes32) = n` by simp[w2n_n2w] >>
  drule_all calldata_slice_writes_frame_mods >> strip_tac >>
  `t = (mstore (w2n w) (n2w n)
           (write_memory_with_expansion (w2n w+32) bytes v))
         with vs_inst_idx := SUC (SUC v.vs_inst_idx)` by
    (qpat_assum `t = (mstore _ _ _) with vs_inst_idx := _`
       (fn th => once_rewrite_tac[th]) >>
     qpat_assum `vc = _` (fn th => once_rewrite_tac[th]) >>
     simp[instIdxIndepTheory.mstore_idx]) >>
  `t.vs_vars = v.vs_vars /\ t.vs_accounts = s.vs_accounts /\
   t.vs_transient = s.vs_transient /\ t.vs_call_ctx = s.vs_call_ctx /\
   t.vs_immutables = s.vs_immutables` by
    (qpat_assum `t = (mstore _ _ (write_memory_with_expansion _ _ _)) with vs_inst_idx := _`
       (fn th => once_rewrite_tac[th]) >>
     simp_tac pure_ss [mstore_def,write_memory_with_expansion_def,LET_THM,
                       venom_state_accfupds] >>
     asm_rewrite_tac[]) >>
  `!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn) [] (OK v,G2,tn2)` by
    (qpat_assum `!D. gas_origin_ptr_path _ (s,G,tn) [] (OK u,G1,tn1)` mp_tac >>
     qpat_assum `!D. gas_origin_ptr_path _ (u,G1,tn1) [] (OK v,G2,tn2)` mp_tac >>
     rpt (pop_assum kall_tac) >> metis_tac[slice_empty_path_join]) >>
  `!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn) [] (OK t,G2,tm)` by
    (qpat_assum `!D. gas_origin_ptr_path _ (s,G,tn) [] (OK v,G2,tn2)` mp_tac >>
     qpat_assum `!D. gas_origin_ptr_path _ (v,G2,tn2) [] (OK t,G2,tm)` mp_tac >>
     rpt (pop_assum kall_tac) >> metis_tac[slice_empty_path_join]) >>
  `alloca_inv s` by
    (qpat_assum `stmt_state_rel H0 ctx func cenv cx es s`
       (strip_assume_tac o REWRITE_RULE[stmt_state_rel_def]) >> first_assum ACCEPT_TAC) >>
  `alloca_history func t` by
    (qpat_assum `!D. gas_origin_ptr_path _ (s,G,tn) [] (OK t,G2,tm)`
       (assume_tac o SPEC_ALL) >>
     drule_all body_full_path_alloca_history >> simp[]) >>
  `?inst. MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\
          inst.inst_id = s2.cs_next_id` by
    (drule compile_slice_out_buf_compiler_parts >> strip_tac >>
     rename1 `compile_alloc_buffer _ _ = (abuf,asc)` >>
     `fn_has_code s2 asc func` by
       (qspecl_then [`s2`,`asc`,`s3`,`func`] mp_tac fn_has_code_split >> simp[]) >>
     drule_all buffer_alloc_code >> strip_tac >>
     qexists `mk_inst s2.cs_next_id ALLOCA [Lit (n2w N)]
       [STRING #"%" (toString s2.cs_next_var)]` >> simp[mk_inst_def]) >>
  rename1 `allocinst.inst_id = s2.cs_next_id` >>
  suspend "frames"
QED

Resume calldata_slice_success_resources_mods[frames]:
  `!x. not_fresh_at sa x ==>
      lookup_var x t = lookup_var x s /\ FLOOKUP G2 x = FLOOKUP G x /\
      op_taint tm (Var x) = op_taint tn (Var x)` by
    (gen_tac >> strip_tac >>
     `not_fresh_at s2 x` by simp[] >>
     qpat_assum `!x. not_fresh_at sa x ==> lookup_var x u = _ /\ _`
       (qspec_then `x` mp_tac) >>
     qpat_assum `!x. not_fresh_at s2 x ==> lookup_var x v = _ /\ _`
       (qspec_then `x` mp_tac) >>
     qpat_assum `not_fresh_at sa x` (fn th =>
       qpat_assum `not_fresh_at s2 x` (fn th' => pure_rewrite_tac[th,th'])) >>
     qpat_assum `t.vs_vars = v.vs_vars` (fn th => pure_rewrite_tac[lookup_var_def,th]) >>
     qpat_assum `tm.t_var = tn2.t_var` (fn th => pure_rewrite_tac[op_taint_def,th]) >>
     rpt (pop_assum kall_tac) >> metis_tac[]) >>
  `!name b len. local_region cenv es.scopes s name b len ==>
      local_region cenv es.scopes v name b len` by
    (rpt strip_tac >> irule local_region_frame_fwd >>
     qexistsl [`s`,`sa`,`es.scopes`] >>
     asm_simp_tac bool_ss [] >> rpt strip_tac >>
     qpat_assum `!x. not_fresh_at sa x ==> lookup_var x t = _ /\ _`
       (qspec_then `x` mp_tac) >>
     qpat_assum `t.vs_vars = v.vs_vars` (fn th =>
       pure_rewrite_tac[lookup_var_def,th]) >>
     asm_simp_tac bool_ss [lookup_var_def]) >>
  `!off len. off+len <= w2n w \/ w2n w+N <= off ==>
      mem_bytes_at off len t.vs_memory = mem_bytes_at off len s.vs_memory` by
    (qpat_assum `!off len. _ \/ _ ==>
        mem_bytes_at off len t.vs_memory = mem_bytes_at off len v.vs_memory` mp_tac >>
     asm_simp_tac bool_ss []) >>
  `!i. i < s.vs_alloca_next /\ i IN tm.t_mem ==> i IN tn.t_mem` by
    (rpt strip_tac >>
     `i IN tn2.t_mem` by
       (qpat_assum `tm.t_mem SUBSET tn2.t_mem`
          (qspec_then `i` mp_tac o REWRITE_RULE[SUBSET_DEF]) >>
        asm_simp_tac bool_ss []) >>
     qpat_assum `!i. i IN tn2.t_mem <=> _` (qspec_then `i` mp_tac) >>
     asm_simp_tac bool_ss [] >> decide_tac) >>
  `!name b len. local_region cenv es.scopes s name b len ==>
      mem_bytes_at b len t.vs_memory = mem_bytes_at b len s.vs_memory /\
      (!i. b <= i /\ i < b+len /\ i IN tm.t_mem ==> i IN tn.t_mem)` by
    (rpt gen_tac >> strip_tac >> conj_tac
     >- (qpat_assum `!off len. _ \/ _ ==> mem_bytes_at off len t.vs_memory = _` irule >>
         `local_region cenv es.scopes v name b len` by simp[] >>
         qpat_assum `!name b len. local_region _ _ v _ _ _ ==> _`
           (qspecl_then [`name`,`b`,`len`] mp_tac) >>
         asm_simp_tac bool_ss [loweringStateRelDefsTheory.regions_disjoint_def, DISJ_COMM]) >>
     rpt strip_tac >>
     `b+len <= s.vs_alloca_next` by (drule_all body_local_region_frontier >> simp[]) >>
     qpat_assum `!i. i < s.vs_alloca_next /\ _ ==> _` irule >> simp[] >> decide_tac) >>
  `ghost_kept_at lo cenv es sa G tn s G2 tm` by
    (rewrite_tac[ghost_kept_at_def] >> rpt conj_tac
     >- (rpt strip_tac >>
         qpat_assum `!x. not_fresh_at sa x ==> lookup_var x t = _ /\ _`
           (qspec_then `x` mp_tac) >> simp[])
     >- (rpt strip_tac >>
         `off+sz <= s.vs_alloca_next` by
           (qpat_assum `alloca_inv s`
              (strip_assume_tac o REWRITE_RULE[alloca_inv_def,alloca_next_valid_def]) >>
            qpat_assum `!aid b sz. FLOOKUP s.vs_allocas aid = _ ==> _ <= s.vs_alloca_next`
              (qspecl_then [`aid`,`off`,`sz`] mp_tac) >> asm_simp_tac bool_ss []) >>
         qpat_assum `!i. i < s.vs_alloca_next /\ _ ==> _` irule >> simp[] >> decide_tac) >>
     qx_genl_tac [`nm`,`b`,`sz`,`i`] >> strip_tac >>
     qpat_x_assum `tm.t_mem = _` kall_tac >>
     qpat_assum `!name b len. local_region _ _ s _ _ _ ==> _ /\ _`
       (qspecl_then [`nm`,`b`,`sz`] mp_tac) >> asm_simp_tac bool_ss [] >>
     disch_then (qspec_then `i` mp_tac o CONJUNCT2) >> asm_simp_tac bool_ss []) >>
  suspend "package"
QED

Resume calldata_slice_success_resources_mods[package]:
  `not_fresh_at sb root` by
    (irule freshWritesTheory.not_fresh_at_mono >> qexists `s3` >>
     qpat_assum `emit_void CALLDATACOPY _ _ = _` (mp_then Any strip_assume_tac emitted_insts_emit_void) >>
     qpat_assum `emit_void MSTORE _ _ = _` (mp_then Any strip_assume_tac emitted_insts_emit_void) >>
     asm_simp_tac bool_ss [arithmeticTheory.LESS_EQ_REFL]) >>
  `lookup_var root t = SOME w` by
    (qpat_assum `lookup_var root v = _` (mp_tac o REWRITE_RULE[lookup_var_def]) >>
     qpat_assum `t.vs_vars = v.vs_vars` (fn th => pure_rewrite_tac[lookup_var_def,th]) >>
     simp_tac bool_ss []) >>
  `FLOOKUP t.vs_allocas (sa.cs_next_id+7) = SOME (w2n w,N)` by
    (qpat_assum `s2.cs_next_id = _` (fn th => once_rewrite_tac[GSYM th]) >>
     qpat_assum `t.vs_allocas = v.vs_allocas` (fn th => pure_rewrite_tac[th]) >>
     first_assum ACCEPT_TAC) >>
  `val_in_memory (BaseTV (BytesT (Dynamic n))) (BytesV bytes) (w2n w) t.vs_memory` by
    (qpat_assum `t = (mstore _ _ (write_memory_with_expansion _ _ _)) with vs_inst_idx := _`
       (fn th => once_rewrite_tac[th]) >> simp_tac pure_ss [venom_state_accfupds] >>
     qspecl_then [`w2n w`,`bytes`,`n`,`v`] mp_tac bytes_buffer_write_encoding >>
     qpat_assum `LENGTH bytes = n` (fn th => pure_rewrite_tac[th]) >> simp_tac bool_ss []) >>
  `!(H':(bool # 'b word # type_value) list # num list).
     stmt_state_rel H' ctx func cenv cx es s ==> stmt_state_rel H' ctx func cenv cx es t` by
    (qx_gen_tac `H'` >> strip_tac >>
     `stmt_state_rel H' ctx func cenv cx es u` by
       (irule slice_prefix_state_rel >> qexistsl [`LENGTH s2.cs_current_insts`,`s`,`sa`] >>
        qpat_assum `!x. not_fresh_at sa x ==> lookup_var x u = _ /\ _` mp_tac >>
        asm_simp_tac bool_ss []) >>
     `stmt_state_rel H' ctx func cenv cx es v` by
       (qpat_assum `!H'. stmt_state_rel H' ctx func cenv cx es u ==> _`
          (qspec_then `H'` mp_tac) >> asm_simp_tac bool_ss []) >>
     qpat_assum `t = (mstore _ _ (write_memory_with_expansion _ _ _)) with vs_inst_idx := _`
       (fn th => once_rewrite_tac[th]) >> simp_tac pure_ss [stmt_state_rel_inst_idx] >>
     irule allocated_bytes_write_state_rel >> asm_simp_tac bool_ss [] >>
     qexistsl [`N`,`allocinst`] >> rpt conj_tac >>
     (first_assum ACCEPT_TAC ORELSE
      (qpat_assum `allocinst.inst_id = s2.cs_next_id` (fn th => pure_rewrite_tac[th]) >>
       first_assum ACCEPT_TAC))) >>
  suspend "finish"
QED

Resume calldata_slice_success_resources_mods[finish]:
  `allocas_from lo t` by
    (pure_rewrite_tac[allocas_from_def] >>
     qpat_assum `t.vs_allocas = v.vs_allocas` (fn th => pure_rewrite_tac[th]) >>
     qpat_assum `allocas_from lo v` (ACCEPT_TAC o REWRITE_RULE[allocas_from_def])) >>
  `lo <= w2n w` by
    (qpat_assum `allocas_from lo v`
       (qspecl_then [`s2.cs_next_id`,`w2n w`,`N`] mp_tac o REWRITE_RULE[allocas_from_def]) >>
     disch_then (fn th => qpat_assum `FLOOKUP v.vs_allocas s2.cs_next_id = _`
       (ACCEPT_TAC o MATCH_MP th))) >>
  `s.vs_alloca_next <= t.vs_alloca_next` by
    (qpat_assum `u.vs_alloca_next = s.vs_alloca_next` (fn th => once_rewrite_tac[GSYM th]) >>
     qpat_assum `t.vs_alloca_next = v.vs_alloca_next` (fn th => pure_rewrite_tac[th]) >>
     first_assum ACCEPT_TAC) >>
  `lo <= t.vs_alloca_next` by
    (irule arithmeticTheory.LESS_EQ_TRANS >> qexists `s.vs_alloca_next` >> asm_simp_tac bool_ss []) >>
  `!aid e. FLOOKUP s.vs_allocas aid = SOME e ==> FLOOKUP t.vs_allocas aid = SOME e` by
    (qpat_assum `!aid e. FLOOKUP u.vs_allocas aid = SOME e ==> _` mp_tac >>
     qpat_assum `u.vs_allocas = s.vs_allocas` (fn th => pure_rewrite_tac[th]) >>
     qpat_assum `t.vs_allocas = v.vs_allocas` (fn th => pure_rewrite_tac[th]) >> simp_tac bool_ss []) >>
  `!aid b len. FLOOKUP t.vs_allocas aid = SOME (b,len) ==>
      FLOOKUP s.vs_allocas aid = SOME (b,len) \/ s.vs_alloca_next <= b` by
    (qpat_assum `!aid b len. FLOOKUP v.vs_allocas aid = SOME (b,len) ==> _ \/ _` mp_tac >>
     qpat_assum `u.vs_allocas = s.vs_allocas` (fn th => pure_rewrite_tac[th]) >>
     qpat_assum `u.vs_alloca_next = s.vs_alloca_next` (fn th => pure_rewrite_tac[th]) >>
     qpat_assum `t.vs_allocas = v.vs_allocas` (fn th => pure_rewrite_tac[th]) >> simp_tac bool_ss []) >>
  `!aid b len. FLOOKUP s.vs_allocas aid = SOME (b,len) /\ aid < sa.cs_next_id ==>
      mem_bytes_at b len t.vs_memory = mem_bytes_at b len s.vs_memory` by
    (rpt strip_tac >>
     qpat_assum `!off len. _ \/ _ ==> mem_bytes_at off len t.vs_memory = mem_bytes_at off len s.vs_memory` irule >>
     `aid < s2.cs_next_id` by (qpat_assum `s2.cs_next_id = _` (fn th => pure_rewrite_tac[th]) >> decide_tac) >>
     qpat_assum `!aid b len. aid < s2.cs_next_id /\ _ ==> _`
       (qspecl_then [`aid`,`b`,`len`] mp_tac) >>
     qpat_assum `u.vs_allocas = s.vs_allocas` (fn th => pure_rewrite_tac[th]) >>
     asm_simp_tac bool_ss [loweringStateRelDefsTheory.regions_disjoint_def,DISJ_COMM]) >>
  `mem_bytes_at 0 lo t.vs_memory = mem_bytes_at 0 lo s.vs_memory` by
    (qpat_assum `!off len. _ \/ _ ==> mem_bytes_at off len t.vs_memory = mem_bytes_at off len s.vs_memory` irule >>
     disj1_tac >> asm_simp_tac bool_ss [arithmeticTheory.ADD_CLAUSES]) >>
  `!i. i < lo /\ i IN tm.t_mem ==> i IN tn.t_mem` by
    (rpt strip_tac >> qpat_assum `!i. i < s.vs_alloca_next /\ _ ==> _` irule >>
     conj_tac >- decide_tac >> first_assum ACCEPT_TAC) >>
  suspend "close"
QED

Resume calldata_slice_success_resources_mods[close]:
  `!nm b len. local_region cenv es.scopes s nm b len ==>
      mem_bytes_at b len t.vs_memory = mem_bytes_at b len s.vs_memory` by
    (rpt strip_tac >>
     qpat_assum `!name b len. local_region _ _ s _ _ _ ==> _ /\ _`
       (qspecl_then [`nm`,`b`,`len`] mp_tac) >>
     asm_simp_tac bool_ss []) >>
  `locals_kept cenv es es s t` by (irule locals_kept_regions >> first_assum ACCEPT_TAC) >>
  `allocinst.inst_id = sa.cs_next_id + 7` by
    (qpat_assum `allocinst.inst_id = _` (fn th => pure_rewrite_tac[th]) >> first_assum ACCEPT_TAC) >>
  `pure_frame cenv func es sa s t` by
    (pure_rewrite_tac[pure_frame_def] >> conj_tac >- first_assum ACCEPT_TAC >>
     rpt strip_tac >>
     qpat_assum `!off len. _ \/ _ ==> mem_bytes_at off len t.vs_memory = mem_bytes_at off len s.vs_memory` irule >>
     qpat_assum `!inst b sz. MEM inst _ /\ _ ==> _`
       (qspecl_then [`allocinst`,`w2n w`,`N`] mp_tac) >>
     `sa.cs_next_id <= allocinst.inst_id` by
       (qpat_assum `allocinst.inst_id = sa.cs_next_id + 7` (fn th => pure_rewrite_tac[th]) >> decide_tac) >>
     impl_tac
     >- (rpt conj_tac >>
         (first_assum ACCEPT_TAC ORELSE
          (qpat_assum `allocinst.inst_id = sa.cs_next_id + 7` (fn th => pure_rewrite_tac[th]) >>
           first_assum ACCEPT_TAC))) >>
     simp_tac bool_ss [loweringStateRelDefsTheory.regions_disjoint_def]) >>
  `LENGTH s.vs_memory <= LENGTH t.vs_memory` by
    (qpat_assum `v.vs_memory = s.vs_memory` (fn th => once_rewrite_tac[GSYM th]) >>
     first_assum ACCEPT_TAC) >>
  `w2n w + N <= t.vs_alloca_next` by
    (qpat_assum `t.vs_alloca_next = v.vs_alloca_next` (fn th => pure_rewrite_tac[th]) >>
     first_assum ACCEPT_TAC) >>
  qexistsl [`root`,`w`,`t`,`G2`,`tm`] >> rpt conj_tac >>
  (first_assum ACCEPT_TAC ORELSE asm_simp_tac bool_ss []) >>
  qexists `allocinst` >> rpt conj_tac >> first_assum ACCEPT_TAC
QED

Finalise calldata_slice_success_resources_mods
