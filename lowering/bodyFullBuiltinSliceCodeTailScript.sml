(* One joint pure code suffix for self and external Slice sources. *)
Theory bodyFullBuiltinSliceCodeTail
Ancestors
  bodyFullPreds bodySimFull bodyFullOfVV gasOutcomeFullCompose
  bodyFullUnwrapRun exprSimProps exprSimWordArgs exprSimHash
  exprSimSliceExtcodeEntry
  bodyFullBuiltinBytestringQuery bodyFullBuiltinBytestringBuffer
  bodyFullBuiltinBytestringBounds bodyFullBuiltinBytestringCopy
  bodyFullBuiltinBytestringAbort
  bodyPtrBytestringBuiltinsWindowGhost wordArgsPtr
  exprSimSliceSource exprSimSliceOrdinaryFrame exprSimHypsDefs
  exprLowering vyperInterpreter vyperAST list
  fragExec emitHelperProps bodyPtrBytestringBuiltinsSlice
  bodyPtrBytestringBuiltinsBuffer loweringPosts loweringStateRelDefs
  reasonCodeResourcesPtr bodyPtrAttributeFields
Libs
  horizonTypeLib

Theorem slice_code_output_resources_at_horizon:
  stmt_state_rel (storage_trace_horizon es.storage_trace) ctx func cenv cx es s ==>
  compile_slice_out_buf N sa = ((out,data),sc) /\
  emit_void opc ops sc = ((),sd) /\
  emit_void MSTORE [out;cnt] sd = ((),sb) /\
  fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
  local_ptrs_reserved cenv sa /\
  0 < n /\ n < dimword (:256) /\ 32+n <= N /\ N < dimword (:256) /\
  LENGTH bytes = n /\
  eval_operand start s = SOME wa /\ eval_operand cnt s = SOME (n2w n) /\
  op_taint tn start = {} /\ op_taint tn cnt = {} /\
  (!x. (start = Var x \/ cnt = Var x) ==> not_fresh_at sa x) /\
  (((opc = CALLDATACOPY \/ opc = CODECOPY) /\ ops = [data;start;cnt]) \/
   (opc = EXTCODECOPY /\ ops = [addr;data;start;cnt] /\
    (?aw. eval_operand addr s = SOME aw) /\ op_taint tn addr = {} /\
    (!x. addr = Var x ==> not_fresh_at sa x))) /\
  (!v wd. v.vs_accounts = s.vs_accounts /\ v.vs_call_ctx = s.vs_call_ctx /\
    v.vs_code = s.vs_code /\
    eval_operand data v = SOME wd /\ eval_operand start v = SOME wa /\
    eval_operand cnt v = SOME (n2w n) /\
    (opc = EXTCODECOPY ==> eval_operand addr v = eval_operand addr s) ==>
    step_inst_base (mk_inst sc.cs_next_id opc ops []) v =
      OK (write_memory_with_expansion (w2n wd) bytes v)) /\
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
    FLOOKUP t.vs_allocas sa.cs_next_id = SOME (w2n w,N) /\
    w2n w+N < dimword (:256) /\ w2n w+N <= t.vs_alloca_next /\
    val_in_memory (BaseTV (BytesT (Dynamic bound))) (BytesV bytes)
      (w2n w) t.vs_memory /\
    (!i. w2n w <= i /\ i < w2n w+32+n ==> i NOTIN tm.t_mem) /\
    (!H':(bool # bytes32 # type_value) list # num list.
      stmt_state_rel H' ctx func cenv cx es s ==>
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
    locals_kept cenv es es s t /\ pure_frame cenv func es sa s t /\
    t.vs_accounts = s.vs_accounts /\ t.vs_transient = s.vs_transient /\
    t.vs_call_ctx = s.vs_call_ctx /\ t.vs_immutables = s.vs_immutables /\
    s.vs_alloca_next <= t.vs_alloca_next
Proof
  strip_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
  irule (bytestring_external_output_full_resources
    |> horizonTypeLib.at_horizon_named "H0" |> horizonTypeLib.at_horizon) >>
  simp[] >> conj_tac >- (qexistsl_tac [`addr`,`cnt`,`opc`,`ops`,`sd`,`start`,`wa`] >> simp[] >> first_assum ACCEPT_TAC) >>
  qexists_tac `storage_trace_horizon es.storage_trace` >> simp[]
QED

Theorem slice_code_tail_full:
  emit_op query_op query_ops sa = (limit,sc) /\
  compile_assert_slice_bounds start cnt limit sc = ((),sd) /\
  compile_slice_out_buf N sd = ((out,data),se) /\
  emit_void copy_op copy_ops se = ((),sf) /\
  emit_void MSTORE [out;cnt] sf = ((),sb) /\
  fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
  local_ptrs_reserved cenv sa /\ ~ctx_has_dalloca ctx /\
  MEM query_op [CODESIZE;EXTCODESIZE] /\ LENGTH query_ops <= 1 /\
  (!arg. MEM arg query_ops ==> op_taint tn arg = {}) /\
  step_inst_base
    (mk_inst sa.cs_next_id query_op query_ops
      [STRING #"%" (toString sa.cs_next_var)]) s =
    OK (update_var (STRING #"%" (toString sa.cs_next_var))
      (n2w (LENGTH code)) s) /\
  eval_operand start s = SOME (n2w i) /\
  eval_operand cnt s = SOME (n2w k) /\
  op_prov G start = NONE /\ op_taint tn start = {} /\
  op_prov G cnt = NONE /\ op_taint tn cnt = {} /\
  (!x. (start = Var x \/ cnt = Var x) ==> not_fresh_at sa x) /\
  (!l. start <> Label l /\ cnt <> Label l) /\
  ((copy_op = CODECOPY /\ copy_ops = [data;start;cnt]) \/
   (copy_op = EXTCODECOPY /\ copy_ops = [addr;data;start;cnt] /\
    (?aw. eval_operand addr s = SOME aw) /\
    op_taint tn addr = {} /\
    (!x. addr = Var x ==> not_fresh_at sa x) /\ (!l. addr <> Label l))) /\
  (!v wd. i+k <= LENGTH code /\
    v.vs_accounts = s.vs_accounts /\ v.vs_call_ctx = s.vs_call_ctx /\
    v.vs_code = s.vs_code /\
    eval_operand data v = SOME wd /\
    eval_operand start v = SOME (n2w i) /\
    eval_operand cnt v = SOME (n2w k) /\
    (copy_op = EXTCODECOPY ==> eval_operand addr v = eval_operand addr s) ==>
    step_inst_base (mk_inst se.cs_next_id copy_op copy_ops []) v =
      OK (write_memory_with_expansion (w2n wd) (TAKE k (DROP i code)) v)) /\
  i < dimword (:256) /\ 0 < k /\ k < dimword (:256) /\ k <= n /\
  LENGTH code < dimword (:256) /\
  e = Builtin (BaseT (BytesT (Dynamic n))) (Slice n) args /\
  N = type_memory_bytes cenv (BaseT (BytesT (Dynamic n))) /\
  32+n <= N /\ N < dimword (:256) /\
  storage_trace_domain cx st0 es.storage_trace /\
  (!H. valid_horizon cx st0 H es.storage_trace ==>
    stmt_state_rel H ctx func cenv cx es s /\
    storage_well_formed_on cx es (FST H) /\
    ghost_inv_at (DF H) lo d cenv cx es G tn s) /\
  es.gas_obs = [] /\ alloca_history func s /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==>
    not_fresh_at sa x) /\
  (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==>
    not_fresh_at sa x) /\
  (!tail. source (es with gas_obs := tail) =
    ((case evaluate_slice (BytesV code) (IntV (&i)) (IntV (&k)) n of
        INL v => INL (Value v) | INR err => INR (Error err)),
     es with gas_obs := tail)) ==>
  gas_outcome_full (DF,lo,explicit,ctx,func,PG) tops cx st0 source
    (es,s,G,tn)
    (\H res ee HG tm t.
      res = INL (Value (BytesV (TAKE k (DROP i code)))) /\
      vv_post H ctx func cenv cx e es sa sb s ee
        (Value (BytesV (TAKE k (DROP i code))))
        (LocatedValue (BaseT (BytesT (Dynamic n))) (mk_ptr out LocMemory)) t /\
      vv_store_bound cx (BaseT (BytesT (Dynamic n))) (BaseT (BytesT (Dynamic n)))
        ee (Value (BytesV (TAKE k (DROP i code))))
        (LocatedValue (BaseT (BytesT (Dynamic n))) (mk_ptr out LocMemory)) t /\
      t.vs_current_bb = sb.cs_current_bb /\ t.vs_inst_idx = LENGTH sb.cs_current_insts /\
      alloca_history func t /\ s.vs_alloca_next <= t.vs_alloca_next /\
      ghost_inv_at (DF H) lo d cenv cx ee HG tm t /\
      ptr_vv_ok cx (BaseT (BytesT (Dynamic n)))
        (Value (BytesV (TAKE k (DROP i code))))
        (LocatedValue (BaseT (BytesT (Dynamic n))) (mk_ptr out LocMemory)) ee HG tm t /\
      ptr_buf_ok cenv e out HG t /\
      ghost_kept_at lo cenv es sa G tn s HG tm)
    (\H res ee gt r. expr_exit res r /\ halt_exit H cx ee res r)
Proof
  rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
  qpat_assum `e = _` SUBST_ALL_TAC >>
  qpat_assum `N = _` SUBST_ALL_TAC >>
  `es with gas_obs := [] = es` by
    (qpat_assum `es.gas_obs = []` (SUBST1_TAC o SYM) >> simp[]) >>
  qabbrev_tac `copy_shape =
    ((copy_op = CODECOPY /\ copy_ops = [data;start;cnt]) \/
     (copy_op = EXTCODECOPY /\ copy_ops = [addr;data;start;cnt] /\
      (?aw. eval_operand addr s = SOME aw) /\ op_taint tn addr = {} /\
      (!x. addr = Var x ==> not_fresh_at sa x) /\ (!l. addr <> Label l)))` >>
  `valid_horizon cx st0 (storage_trace_horizon es.storage_trace) es.storage_trace` by
    fs[vyperStorageFootprintTheory.storage_trace_domain_def] >>
  `stmt_state_rel (storage_trace_horizon es.storage_trace)
      ctx func cenv cx es s /\
   ghost_inv_at (DF (storage_trace_horizon es.storage_trace))
      lo d cenv cx es G tn s` by
    (qpat_assum `!H. valid_horizon _ _ H es.storage_trace ==> _`
       (qspec_then `storage_trace_horizon es.storage_trace` mp_tac) >> simp[]) >>
  `alloca_inv s /\ allocas_from lo s /\ lo <= s.vs_alloca_next` by
    fs[exprLoweringPropsTheory.stmt_state_rel_def,bodyPtrDefsTheory.ghost_inv_at_def] >>
  `cs_extends sa sc /\ cs_extends sc sd /\ cs_extends sd se /\
   cs_extends se sf /\ cs_extends sf sb` by
    (rpt conj_tac
     >- metis_tac[fragExecTheory.cs_appends_emit_helpers,fragExecTheory.cs_appends_def]
     >- metis_tac[bodyPtrBytestringBuiltinsSliceTheory.slice_bounds_extends]
     >- metis_tac[bodyPtrBytestringBuiltinsBufferTheory.compile_slice_out_buf_compiler_parts,
                  compileEnvTheory.cs_extends_trans] >>
     metis_tac[fragExecTheory.cs_appends_emit_helpers,fragExecTheory.cs_appends_def]) >>
  `fn_has_code sa sc func /\ fn_has_code sc sd func /\ fn_has_code sd sb func` by
    (qpat_assum `fn_has_code sa sb func` mp_tac >>
     qpat_assum `cs_extends sa sc` mp_tac >> qpat_assum `cs_extends sc sd` mp_tac >>
     qpat_assum `cs_extends sd se` mp_tac >> qpat_assum `cs_extends se sf` mp_tac >>
     qpat_assum `cs_extends sf sb` mp_tac >> rpt (pop_assum kall_tac) >>
     metis_tac[fragExecTheory.fn_has_code_split,compileEnvTheory.cs_extends_trans]) >>
  `MEM query_op [CALLDATASIZE;CODESIZE;EXTCODESIZE]` by fs[MEM] >>
  mp_tac (bodyFullBuiltinBytestringQueryTheory.bytestring_source_size_full_run |> Q.INST
    [`sa` |-> `sa`,`sb` |-> `sc`,`s` |-> `s`,`G` |-> `G`,`tn` |-> `tn`,
     `limit` |-> `limit`,`opc` |-> `query_op`,`ops` |-> `query_ops`,
     `wl` |-> `n2w (LENGTH (code:word8 list))`, `explicit` |-> `explicit`]) >>
  (impl_tac >- simp[]) >>
  disch_then (qx_choose_then `size_var` (qx_choose_then `zq`
    (qx_choose_then `G4` (qx_choose_then `tn4` strip_assume_tac)))) >>
  `!x. start = Var x ==> not_fresh_at sa x` by simp[] >>
  `!x. cnt = Var x ==> not_fresh_at sa x` by simp[] >>
  `zq.vs_labels = s.vs_labels` by simp[venomStateTheory.update_var_def] >>
  mp_tac (bodyPtrBytestringBuiltinsExternalSliceTheory.reserved_operand_ghost_frame |> Q.INST
    [`sa` |-> `sa`,`s` |-> `s`,`t` |-> `zq`,`G` |-> `G`,`HG` |-> `G4`,
     `tn` |-> `tn`,`tm` |-> `tn4`]) >>
  (impl_tac >- simp[]) >> strip_tac >>
  `eval_operand start zq = SOME (n2w i) /\
   op_prov G4 start = NONE /\ op_taint tn4 start = {} /\
   eval_operand cnt zq = SOME (n2w k) /\
   op_prov G4 cnt = NONE /\ op_taint tn4 cnt = {}` by
    (qpat_assum `!op. (!s. op = Var s ==> not_fresh_at sa s) ==> _`
       (fn th => map_every mp_tac (map (fn operand => Q.SPEC operand th)
         [`start`,`cnt`])) >> simp[]) >>
  `!x. not_fresh_at sa x ==> not_fresh_at sc x` by
    (rpt strip_tac >> irule freshWritesTheory.not_fresh_at_mono >>
     qexists_tac `sa` >> simp[] >>
     qpat_assum `emit_op query_op _ _ = _`
       (mp_then Any strip_assume_tac emitHelperPropsTheory.emitted_insts_emit_op) >> simp[]) >>
  `!op. MEM op [start;cnt;limit] ==>
     op_prov G4 op = NONE /\ op_taint tn4 op = {} /\
     (!x. op = Var x ==> not_fresh_at sc x)` by
    (qpat_assum `!x. not_fresh_at sa x ==> not_fresh_at sc x` mp_tac >>
     qpat_assum `!x. start = Var x ==> not_fresh_at sa x` mp_tac >>
     qpat_assum `!x. cnt = Var x ==> not_fresh_at sa x` mp_tac >>
     qpat_assum `limit = Var size_var` mp_tac >>
     qpat_assum `not_fresh_at sc size_var` mp_tac >>
     qpat_assum `op_prov G4 start = NONE` mp_tac >>
     qpat_assum `op_prov G4 cnt = NONE` mp_tac >>
     qpat_assum `op_prov G4 limit = NONE` mp_tac >>
     qpat_assum `op_taint tn4 start = {}` mp_tac >>
     qpat_assum `op_taint tn4 cnt = {}` mp_tac >>
     qpat_assum `op_taint tn4 limit = {}` mp_tac >>
     rpt (pop_assum kall_tac) >> simp[MEM] >> rpt strip_tac >> gvs[] >> metis_tac[]) >>
  `allocas_from lo zq /\ lo <= zq.vs_alloca_next` by
    (qpat_assum `zq = _` SUBST1_TAC >>
     simp[ptrDisciplineTheory.allocas_from_def,venomStateTheory.update_var_def] >>
     qpat_assum `allocas_from lo s`
       (ACCEPT_TAC o REWRITE_RULE[ptrDisciplineTheory.allocas_from_def])) >>
  mp_tac (bodyPtrBytestringBuiltinsBoundsTheory.slice_bounds_reserved_natural_runtime |> Q.INST
    [`sa` |-> `sc`,`sb` |-> `sd`,`s` |-> `zq`,`start` |-> `start`,
     `len` |-> `cnt`,`limit` |-> `limit`,`a` |-> `i`,`n` |-> `k`,
     `cap` |-> `LENGTH (code:word8 list)`]) >>
  (impl_tac >-
    (simp[venomStateTheory.eval_operand_def,venomStateTheory.lookup_var_def,
          venomStateTheory.update_var_def,finite_mapTheory.FLOOKUP_UPDATE] >>
     qpat_assum `!op. MEM op [start;cnt;limit] ==> _` mp_tac >>
     rpt (pop_assum kall_tac) >> simp[MEM] >> metis_tac[])) >>
  disch_then (qx_choose_then `bound_state` strip_assume_tac) >>
  reverse (Cases_on `i+k <= LENGTH code`)
  >- suspend "bounds_abort" >>
  `i+k < dimword (:256)` by decide_tac >>
  `run_inst_seq (emitted_insts sc sd) zq = OK bound_state` by simp[] >>
  mp_tac (bodyFullBuiltinBytestringBoundsTheory.bytestring_slice_bounds_full_run |> Q.INST
    [`sa` |-> `sc`,`sb` |-> `sd`,`s` |-> `zq`,`u` |-> `bound_state`,
     `start` |-> `start`,`len` |-> `cnt`,`limit` |-> `limit`,
     `G` |-> `G4`,`tn` |-> `tn4`,`wa` |-> `n2w i`,`wn` |-> `n2w k`,
     `wl` |-> `n2w (LENGTH (code:word8 list))`, `explicit` |-> `explicit`]) >>
  (impl_tac >-
    (simp[venomStateTheory.eval_operand_def,venomStateTheory.lookup_var_def,
          venomStateTheory.update_var_def,finite_mapTheory.FLOOKUP_UPDATE] >>
     qpat_assum `!op. MEM op [start;cnt;limit] ==> _` mp_tac >>
     qpat_assum `limit = Var size_var` mp_tac >>
     rpt (pop_assum kall_tac) >> simp[MEM] >> rpt strip_tac >> gvs[] >> metis_tac[])) >>
  disch_then (qx_choose_then `G5` (qx_choose_then `tn5` strip_assume_tac)) >>
  qabbrev_tac `zb = bound_state with vs_inst_idx := LENGTH sd.cs_current_insts` >>
  `!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG)
      (s,G,tn) [] (OK zb,G5,tn5)` by
    (gen_tac >> qunabbrev_tac `zb` >>
     qpat_assum `!D. gas_origin_ptr_path _ (s,G,tn) _ _` (qspec_then `D` mp_tac) >>
     qpat_assum `!D. gas_origin_ptr_path _ (zq,G4,tn4) _ _` (qspec_then `D` mp_tac) >>
     rpt (pop_assum kall_tac) >>
     metis_tac[fragGasOriginPtrTheory.gas_origin_ptr_path_append,listTheory.APPEND_NIL]) >>
  `zb = s with <|vs_vars := zb.vs_vars;
      vs_inst_idx := LENGTH sd.cs_current_insts|>` by
    (qpat_assum `bound_state = zq with vs_vars := bound_state.vs_vars`
       (mp_tac o Q.AP_TERM `\st. st with vs_inst_idx := LENGTH sd.cs_current_insts`) >>
     simp[Abbr `zb`,venomStateTheory.update_var_def]) >>
  `!x. not_fresh_at sa x ==>
     lookup_var x zb = lookup_var x s /\ FLOOKUP G5 x = FLOOKUP G x /\
     op_taint tn5 (Var x) = op_taint tn (Var x)` by
    (simp[Abbr `zb`] >>
     qpat_assum `!x. not_fresh_at sa x ==> lookup_var x zq = _ /\ _` mp_tac >>
     qpat_assum `!x. not_fresh_at sc x ==> lookup_var x bound_state = _ /\ _` mp_tac >>
     qpat_assum `!x. not_fresh_at sa x ==> not_fresh_at sc x` mp_tac >>
     rpt (pop_assum kall_tac) >> rpt strip_tac >>
     fs[venomStateTheory.lookup_var_def] >> metis_tac[]) >>
  `alloca_inv zq` by
    (irule localPtrsPropsTheory.alloca_inv_fields >> qexists_tac `s` >>
     simp[venomStateTheory.update_var_def]) >>
  `alloca_history func zb` by
    (simp[Abbr `zb`] >>
     qspecl_then [`emitted_insts sc sd`,`sc`,`sd`,`zq`,`bound_state`]
       mp_tac bodyFullUnwrapRunTheory.emitted_alloca_history >>
     (impl_tac >-
       (qpat_assum `compile_assert_slice_bounds _ _ _ sc = _`
          (mp_then Any strip_assume_tac
            bodyPtrBytestringBuiltinsBoundsTheory.compile_assert_slice_bounds_layout) >>
        qpat_assum `same_blocks sc sd`
          (strip_assume_tac o REWRITE_RULE[exprLoweringPropsTheory.same_blocks_def]) >>
        simp[venomInstTheory.mk_inst_def,venomInstTheory.is_terminator_def])) >> simp[]) >>
  `zb.vs_memory = s.vs_memory /\ zb.vs_allocas = s.vs_allocas /\
   zb.vs_alloca_next = s.vs_alloca_next /\ zb.vs_labels = s.vs_labels /\
   zb.vs_code = s.vs_code /\ zb.vs_accounts = s.vs_accounts /\
   zb.vs_call_ctx = s.vs_call_ctx /\ zb.vs_transient = s.vs_transient /\
   zb.vs_immutables = s.vs_immutables /\ zb.vs_halted = s.vs_halted` by
    (qpat_assum `zb = s with <|vs_vars := _;vs_inst_idx := _|>`
      (mp_tac o Q.AP_TERM `\st. (st.vs_memory,st.vs_allocas,st.vs_alloca_next,
        st.vs_labels,st.vs_code,st.vs_accounts,st.vs_call_ctx,st.vs_transient,
        st.vs_immutables,st.vs_halted)`) >>
     rpt (pop_assum kall_tac) >> simp[]) >>
  `!op. (!x. op = Var x ==> not_fresh_at sa x) ==>
     eval_operand op zb = eval_operand op s /\ op_prov G5 op = op_prov G op /\
     op_taint tn5 op = op_taint tn op` by
    (mp_tac (bodyPtrBytestringBuiltinsExternalSliceTheory.reserved_operand_ghost_frame |> Q.INST
       [`sa` |-> `sa`,`s` |-> `s`,`t` |-> `zb`,
        `G` |-> `G`,`HG` |-> `G5`,`tn` |-> `tn`,`tm` |-> `tn5`]) >>
     (impl_tac >- simp[]) >> disch_then ACCEPT_TAC) >>
  `eval_operand start zb = SOME (n2w i) /\ op_taint tn5 start = {} /\
   eval_operand cnt zb = SOME (n2w k) /\ op_taint tn5 cnt = {}` by
    (qpat_assum `!op. (!x. op = Var x ==> not_fresh_at sa x) ==>
      eval_operand op zb = _ /\ _`
       (fn th => map_every mp_tac (map (fn operand => Q.SPEC operand th)
         [`start`,`cnt`])) >> simp[]) >>
  `sa.cs_next_var <= sd.cs_next_var /\ sa.cs_next_id <= sd.cs_next_id` by
    (qpat_assum `emit_op query_op _ _ = _`
       (mp_then Any strip_assume_tac emitHelperPropsTheory.emitted_insts_emit_op) >>
     qpat_assum `compile_assert_slice_bounds _ _ _ sc = _`
       (mp_then Any strip_assume_tac
         bodyPtrBytestringBuiltinsBoundsTheory.compile_assert_slice_bounds_layout) >> simp[]) >>
  `!x. not_fresh_at sa x ==> not_fresh_at sd x` by
    (rpt strip_tac >> irule freshWritesTheory.not_fresh_at_mono >>
     qexists_tac `sa` >> simp[]) >>
  `local_ptrs_reserved cenv sd` by
    (irule exprLoweringPropsTheory.local_ptrs_reserved_next_var >>
     qexists_tac `sa` >> simp[]) >>
  `!H:(bool # bytes32 # type_value) list # num list.
    stmt_state_rel H ctx func cenv cx es s ==>
    stmt_state_rel H ctx func cenv cx es zb` by
    (rpt strip_tac >>
     qpat_assum `stmt_state_rel H ctx func cenv cx es s` mp_tac >>
     qpat_assum `!x. not_fresh_at sa x ==> lookup_var x zb = _ /\ _` mp_tac >>
     qpat_assum `local_ptrs_reserved cenv sa` mp_tac >>
     qpat_assum `zb = s with <|vs_vars := _;vs_inst_idx := _|>` mp_tac >>
     rpt (pop_assum kall_tac) >> rpt strip_tac >>
     qpat_assum `zb = s with <|vs_vars := _;vs_inst_idx := _|>` SUBST1_TAC >>
     simp[exprLoweringPropsTheory.stmt_state_rel_inst_idx] >>
     irule exprSimPropsTheory.stmt_state_rel_vars_frame >>
     fs[loweringStateRelDefsTheory.local_ptrs_reserved_def,venomStateTheory.lookup_var_def,
        exprLoweringPropsTheory.stmt_state_rel_inst_idx] >> metis_tac[]) >>
  `stmt_state_rel (storage_trace_horizon es.storage_trace) ctx func cenv cx es zb` by
    (qpat_assum `!H. stmt_state_rel H ctx func cenv cx es s ==> _`
       (qspec_then `storage_trace_horizon es.storage_trace` match_mp_tac) >>
     first_assum ACCEPT_TAC) >>
  `allocas_from lo zb /\ lo <= zb.vs_alloca_next` by
    (simp[ptrDisciplineTheory.allocas_from_def] >>
     qpat_assum `allocas_from lo s`
       (ACCEPT_TAC o REWRITE_RULE[ptrDisciplineTheory.allocas_from_def])) >>
  qabbrev_tac `copied = TAKE k (DROP i code)` >>
  `LENGTH copied = k` by
    (simp[Abbr `copied`,listTheory.LENGTH_TAKE,listTheory.LENGTH_DROP] >> decide_tac) >>
  `copy_op = EXTCODECOPY ==>
    eval_operand addr zb = eval_operand addr s /\
    (?aw. eval_operand addr zb = SOME aw) /\ op_taint tn5 addr = {} /\
    (!x. addr = Var x ==> not_fresh_at sd x)` by
    (strip_tac >> qunabbrev_tac `copy_shape` >>
     qpat_assum `(_ /\ _) \/ (_ /\ _)` mp_tac >>
     disch_then (DISJ_CASES_THEN STRIP_ASSUME_TAC) >> fs[] >>
     qpat_assum `!op. (!x. op = Var x ==> not_fresh_at sa x) ==>
       eval_operand op zb = _ /\ _` (qspec_then `addr` mp_tac) >> simp[]) >>
  `!v wd. v.vs_accounts = zb.vs_accounts /\
    v.vs_call_ctx = zb.vs_call_ctx /\ v.vs_code = zb.vs_code /\
    eval_operand data v = SOME wd /\ eval_operand start v = SOME (n2w i) /\
    eval_operand cnt v = SOME (n2w k) /\
    (copy_op = EXTCODECOPY ==> eval_operand addr v = eval_operand addr zb) ==>
    step_inst_base (mk_inst se.cs_next_id copy_op copy_ops []) v =
      OK (write_memory_with_expansion (w2n wd) copied v)` by
    (rpt strip_tac >> simp[Abbr `copied`] >>
     qpat_assum `!v wd. _ ==> step_inst_base _ v = _` irule >> simp[] >> metis_tac[]) >>
  `32+k <= type_memory_bytes cenv (BaseT (BytesT (Dynamic n)))` by decide_tac >>
  `zb.vs_current_bb = sd.cs_current_bb /\
   zb.vs_inst_idx = LENGTH sd.cs_current_insts` by simp[Abbr `zb`] >>
  `~zb.vs_halted` by simp[] >>
  `!x. (start = Var x \/ cnt = Var x) ==> not_fresh_at sd x` by
    (qpat_assum `!x. start = Var x \/ cnt = Var x ==> _` mp_tac >>
     qpat_assum `!x. not_fresh_at sa x ==> not_fresh_at sd x` mp_tac >>
     rpt (pop_assum kall_tac) >> metis_tac[]) >>
  suspend "copy_and_post"
QED

Resume slice_code_tail_full[copy_and_post]:
  drule slice_code_output_resources_at_horizon >>
  disch_then (drule_at (Pat `compile_slice_out_buf _ _ = _`)) >>
  disch_then (drule_at (Pat `emit_void _ _ _ = _`)) >>
  disch_then (drule_at (Pat `emit_void _ _ _ = _`)) >>
  disch_then (drule_at (Pat `eval_operand cnt _ = SOME (n2w _)`)) >>
  disch_then (drule_at (Pat `op_taint _ start = {}`)) >>
  disch_then (drule_at (Pat `allocas_from _ _`)) >>
  disch_then (qspec_then `explicit` mp_tac) >>
  disch_then (qspec_then `n` mp_tac) >>
  disch_then (qspec_then `PG` mp_tac) >>
  disch_then (qspec_then `G5` mp_tac) >>
  (impl_tac >- (simp[] >> conj_tac
     >- first_assum ACCEPT_TAC >>
     qpat_assum `copy_shape` mp_tac >>
     simp[Abbr `copy_shape`] >> metis_tac[])) >>
  disch_then (qx_choose_then `result_var` (qx_choose_then `result_word`
    (qx_choose_then `target` (qx_choose_then `HG`
      (qx_choose_then `tm` strip_assume_tac))))) >>
  suspend "post"
QED

Resume slice_code_tail_full[post]:
  `!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG)
      (s,G,tn) [] (OK target,HG,tm)` by
    (gen_tac >>
     qpat_assum `!D. gas_origin_ptr_path _ (s,G,tn) _ _`
       (qspec_then `D` mp_tac) >>
     qpat_assum `!D. gas_origin_ptr_path _ (zb,G5,tn5) _ _`
       (qspec_then `D` mp_tac) >>
     rpt (pop_assum kall_tac) >>
     metis_tac[fragGasOriginPtrTheory.gas_origin_ptr_path_append,listTheory.APPEND_NIL]) >>
  `tn5.t_mem = tn.t_mem /\ tn5.t_stor = tn.t_stor /\
   tn5.t_trans = tn.t_trans /\ tn5.t_imm = tn.t_imm` by simp[] >>
  `!x. not_fresh_at sa x ==>
     lookup_var x target = lookup_var x s /\ FLOOKUP HG x = FLOOKUP G x /\
     op_taint tm (Var x) = op_taint tn (Var x)` by
    (qpat_assum `!x. not_fresh_at sa x ==> lookup_var x zb = _ /\ _` mp_tac >>
     qpat_assum `!x. not_fresh_at sd x ==> lookup_var x target = _ /\ _` mp_tac >>
     qpat_assum `!x. not_fresh_at sa x ==> not_fresh_at sd x` mp_tac >>
     rpt (pop_assum kall_tac) >> metis_tac[]) >>
  `!name b len. local_region cenv es.scopes s name b len ==>
     local_region cenv es.scopes zb name b len` by
    (rpt strip_tac >> irule exprSimPropsTheory.local_region_frame_fwd >>
     qexistsl_tac [`s`,`sa`,`es.scopes`] >> simp[]) >>
  `!name b len. local_region cenv es.scopes s name b len ==>
     mem_bytes_at b len target.vs_memory = mem_bytes_at b len s.vs_memory /\
     (!j. b <= j /\ j < b+len /\ j IN tm.t_mem ==> j IN tn.t_mem)` by
    (qpat_assum `!name b len. local_region cenv es.scopes zb name b len ==> _` mp_tac >>
     qpat_assum `!name b len. local_region cenv es.scopes s name b len ==> _` mp_tac >>
     qpat_assum `zb.vs_memory = s.vs_memory` mp_tac >>
     qpat_assum `tn5.t_mem = tn.t_mem` mp_tac >>
     rpt (pop_assum kall_tac) >> metis_tac[]) >>
  `mem_bytes_at 0 lo target.vs_memory = mem_bytes_at 0 lo s.vs_memory /\
   (!j. j < lo /\ j IN tm.t_mem ==> j IN tn.t_mem)` by
    (qpat_assum `ghost_kept_at lo cenv es sd G5 tn5 zb HG tm`
       (mp_tac o last o CONJUNCTS o REWRITE_RULE[bodyPtrDefsTheory.ghost_kept_at_def]) >>
     simp[]) >>
  suspend "horizon_post"
QED

Resume slice_code_tail_full[horizon_post]:
  `!H. valid_horizon cx st0 H es.storage_trace ==>
     stmt_state_rel H ctx func cenv cx es target /\
     storage_well_formed_on cx es (FST H) /\
     ghost_inv_at (DF H) lo d cenv cx es HG tm target` by
    (rpt strip_tac >>
     qpat_assum `!H. valid_horizon _ _ H es.storage_trace ==>
        stmt_state_rel H ctx func cenv cx es s /\ _`
       (qspec_then `H` mp_tac) >>
     (impl_tac >- first_assum ACCEPT_TAC) >> strip_tac >>
     `local_ptrs_rel func cenv es.scopes s` by
       (qpat_assum `stmt_state_rel H ctx func cenv cx es s` mp_tac >>
        rpt (pop_assum kall_tac) >> rpt strip_tac >>
        fs[exprLoweringPropsTheory.stmt_state_rel_def,
           loweringStateRelDefsTheory.state_rel_def]) >>
     `stmt_state_rel H ctx func cenv cx es zb` by
       (qpat_assum `!H. stmt_state_rel H ctx func cenv cx es s ==> _`
          (qspec_then `H` match_mp_tac) >> first_assum ACCEPT_TAC) >>
     `stmt_state_rel H ctx func cenv cx es target` by
       (qpat_assum `!H'. stmt_state_rel H' ctx func cenv cx es zb ==> _`
          (qspec_then `H` match_mp_tac) >> first_assum ACCEPT_TAC) >>
     simp[] >>
     `stor_taint_ok_at (DF H) tm target` by
       (qpat_assum `ghost_inv_at (DF H) lo d cenv cx es G tn s`
          (mp_tac o el 4 o CONJUNCTS o REWRITE_RULE[bodyPtrDefsTheory.ghost_inv_at_def]) >>
        simp[bodyPtrDefsTheory.stor_taint_ok_at_def]) >>
     irule ghost_inv_at_local_window_transport >>
     simp[] >> qexistsl_tac [`G`,`es`,`func`,`s`,`sa`,`tn`] >>
     simp[] >> metis_tac[]) >>
  suspend "frames_post"
QED

Resume slice_code_tail_full[frames_post]:
  `wb_frame cenv es es sa s zb` by
    simp[loweringPostsTheory.wb_frame_def,exprSimPropsTheory.locals_kept_mem] >>
  `wb_frame cenv es es sd zb target` by
    (qpat_assum `locals_kept cenv es es zb target` mp_tac >>
     qpat_assum `!x. not_fresh_at sd x ==> lookup_var x target = _ /\ _` mp_tac >>
     qpat_assum `!aid e. FLOOKUP zb.vs_allocas aid = SOME e ==> _` mp_tac >>
     qpat_assum `!aid b len. FLOOKUP zb.vs_allocas aid = SOME (b,len) /\ aid < sd.cs_next_id ==> _` mp_tac >>
     rpt (pop_assum kall_tac) >> rpt strip_tac >>
     simp[loweringPostsTheory.wb_frame_def] >> metis_tac[]) >>
  `wb_frame cenv es es sa s target` by
    (qpat_assum `stmt_state_rel (storage_trace_horizon es.storage_trace) ctx func cenv cx es s`
      (mp_then Any mp_tac (exprSimWordArgsTheory.wb_frame_trans |> horizonTypeLib.at_horizon_named "H")) >>
     disch_then (drule_at (Pat `wb_frame _ _ _ _ _ _`)) >>
     disch_then (drule_at (Pat `wb_frame _ _ _ _ _ _`)) >>
     simp[]) >>
  `pure_frame cenv func es sa s target` by
    (irule exprSimPropsTheory.pure_frame_trans >> simp[] >>
     qexistsl_tac [`es`,`sd`,`zb`] >> simp[] >> metis_tac[]) >>
  `ghost_kept_at lo cenv es sa G tn s G5 tn5` by
    (qpat_assum `!x. not_fresh_at sa x ==> lookup_var x zb = _ /\ _` mp_tac >>
     qpat_assum `tn5.t_mem = tn.t_mem` mp_tac >>
     rpt (pop_assum kall_tac) >> simp[bodyPtrDefsTheory.ghost_kept_at_def] >> metis_tac[]) >>
  `ghost_kept_at lo cenv es sa G tn s HG tm` by
    (irule (wordArgsPtrTheory.ghost_kept_at_wb_trans |> horizonTypeLib.at_horizon_named "H") >>
     simp[] >> conj_tac >- metis_tac[] >>
     qexistsl_tac [`G5`,`es`,`es`,`zb`,`sd`,`tn5`] >> simp[]) >>
  suspend "representation_post"
QED

Resume slice_code_tail_full[representation_post]:
  `type_memory_bytes cenv (BaseT (BytesT (Dynamic n))) =
      32+32*word_size n` by
    (rpt (pop_assum kall_tac) >>
     simp[compileEnvTheory.type_memory_bytes_def,vfmConstantsTheory.word_size_def] >>
     decide_tac) >>
  `n < dimword (:256)` by decide_tac >>
  `evaluate_type (get_tenv cx) (BaseT (BytesT (Dynamic n))) =
      SOME (BaseTV (BytesT (Dynamic n)))` by
    (qpat_assum `type_memory_bytes cenv (BaseT (BytesT (Dynamic n))) < _` mp_tac >>
     qpat_assum `type_memory_bytes cenv (BaseT (BytesT (Dynamic n))) = _` mp_tac >>
     qpat_assum `n < dimword (:256)` mp_tac >> rpt (pop_assum kall_tac) >>
     simp[vyperValueTheory.evaluate_type_def,vyperValueTheory.type_slot_size_def,
          wordsTheory.dimword_def] >> decide_tac) >>
  `val_wf (BaseTV (BytesT (Dynamic n))) (BytesV copied)` by
    (simp[valueEncodingDefsTheory.val_wf_def,valueEncodingTheory.type_memory_size_def] >> decide_tac) >>
  `val_store_size (BaseTV (BytesT (Dynamic n))) (BytesV copied) <=
      type_memory_bytes cenv (BaseT (BytesT (Dynamic n)))` by
    (qspec_then `k` (qspec_then `n` mp_tac) exprSimPropsTheory.word_size_monotone >>
     simp[exprSimPropsTheory.val_store_size_def] >> decide_tac) >>
  qpat_assum `out = Var result_var` SUBST_ALL_TAC >>
  `ptr_mem_ok cx (BaseT (BytesT (Dynamic n))) (BytesV copied)
      (Var result_var) HG tm target` by
    (irule reasonCodeResourcesPtrTheory.clean_memory_representation_ptr >>
     simp[] >> qexists_tac `type_memory_bytes cenv (BaseT (BytesT (Dynamic n)))` >>
     simp[loweringPostsTheory.val_footprint_def] >> rpt strip_tac >>
     qpat_assum `!i. w2n result_word <= i /\ i < w2n result_word+32+k ==> _`
       irule >> simp[]) >>
  suspend "pointer_post"
QED

Resume slice_code_tail_full[pointer_post]:
  `op_taint tm (Var result_var) = {}` by
    (qpat_assum `ptr_covers HG tm result_var target _`
       (ACCEPT_TAC o CONJUNCT1 o REWRITE_RULE[bodyPtrDefsTheory.ptr_covers_def])) >>
  `ptr_vv_ok cx (BaseT (BytesT (Dynamic n))) (Value (BytesV copied))
      (LocatedValue (BaseT (BytesT (Dynamic n))) (mk_ptr (Var result_var) LocMemory))
      es HG tm target` by
    (irule bodyPtrAttributeFieldsTheory.ptr_vv_ok_memory >>
     simp[contextTheory.mk_ptr_def,vyperStateTheory.read_result_def,
          vyperStateTheory.return_def]) >>
  `ptr_buf_ok cenv
      (Builtin (BaseT (BytesT (Dynamic n))) (Slice n) args)
      (Var result_var) HG target` by
    (qpat_assum `ptr_covers HG tm result_var target _` mp_tac >>
     qpat_assum `type_memory_bytes cenv (BaseT (BytesT (Dynamic n))) = _` mp_tac >>
     rpt (pop_assum kall_tac) >>
     rw[bodyPtrDefsTheory.ptr_covers_def,bodyPtrDefsTheory.ptr_buf_ok_def,
        venomStateTheory.eval_operand_def,exprLoweringTheory.lowered_value_type_def,
        vyperASTTheory.expr_type_def] >> gvs[] >>
     qexistsl_tac [`b`,`sz'`] >> simp[] >> decide_tac) >>
  `vv_store_bound cx (BaseT (BytesT (Dynamic n))) (BaseT (BytesT (Dynamic n)))
      es (Value (BytesV copied))
      (LocatedValue (BaseT (BytesT (Dynamic n))) (mk_ptr (Var result_var) LocMemory))
      target` by
    (qpat_assum `evaluate_type (get_tenv cx) (BaseT (BytesT (Dynamic n))) = _` mp_tac >>
     qpat_assum `w2n result_word+type_memory_bytes cenv (BaseT (BytesT (Dynamic n))) <= _` mp_tac >>
     qpat_assum `val_store_size (BaseTV (BytesT (Dynamic n))) (BytesV copied) <= _` mp_tac >>
     qpat_assum `lookup_var result_var target = SOME result_word` mp_tac >>
     qpat_assum `type_memory_bytes cenv (BaseT (BytesT (Dynamic n))) = _` mp_tac >>
     rpt (pop_assum kall_tac) >>
     rw[exprSimMemDefsTheory.vv_store_bound_def,contextTheory.mk_ptr_def,
        vyperStateTheory.read_result_def,vyperStateTheory.return_def,
        venomStateTheory.eval_operand_def,valueEncodingTheory.type_memory_size_def] >>
     gvs[] >> decide_tac) >>
  suspend "allocation_post"
QED

Resume slice_code_tail_full[allocation_post]:
  `fn_has_code sd se func` by
    (qpat_assum `fn_has_code sd sb func` mp_tac >>
     qpat_assum `cs_extends sd se` mp_tac >>
     qpat_assum `cs_extends se sf` mp_tac >> qpat_assum `cs_extends sf sb` mp_tac >>
     rpt (pop_assum kall_tac) >>
     metis_tac[fragExecTheory.fn_has_code_split,compileEnvTheory.cs_extends_trans]) >>
  `MEM (mk_inst sd.cs_next_id ALLOCA
      [Lit (n2w (type_memory_bytes cenv (BaseT (BytesT (Dynamic n)))))]
      [STRING #"%" (toString sd.cs_next_var)]) (fn_insts func)` by
    (qpat_assum `compile_slice_out_buf _ sd = _`
       (mp_then Any mp_tac exprSimSliceExtcodeEntryTheory.slice_extcode_out_owner_inst) >>
     simp[]) >>
  `ci_mono sd se` by
    (qspecl_then [`type_memory_bytes cenv (BaseT (BytesT (Dynamic n)))`,`sd`]
       mp_tac exprLoweringPropsTheory.ci_mono_compile_slice_out_buf >> simp[]) >>
  `sd.cs_next_id < sb.cs_next_id` by
    (qpat_assum `emit_void copy_op _ se = _`
       (mp_then Any strip_assume_tac emitHelperPropsTheory.emitted_insts_emit_void) >>
     qpat_assum `emit_void MSTORE _ sf = _`
       (mp_then Any strip_assume_tac emitHelperPropsTheory.emitted_insts_emit_void) >>
     fs[exprLoweringPropsTheory.ci_mono_def] >> decide_tac) >>
  `!name b sz. local_region cenv es.scopes target name b sz ==>
      regions_disjoint (w2n result_word)
        (type_memory_bytes cenv (BaseT (BytesT (Dynamic n)))) b sz` by
    (rpt strip_tac >>
     `alloca_inv target /\ local_ptrs_rel func cenv es.scopes target` by
       (qpat_assum `!H. valid_horizon _ _ H es.storage_trace ==>
          stmt_state_rel H ctx func cenv cx es target /\ _`
          (qspec_then `storage_trace_horizon es.storage_trace` mp_tac) >>
        (impl_tac >- first_assum ACCEPT_TAC) >>
        rpt (pop_assum kall_tac) >> rpt strip_tac >>
        fs[exprLoweringPropsTheory.stmt_state_rel_def,
           loweringStateRelDefsTheory.state_rel_def]) >>
     irule localPtrsPropsTheory.local_ptrs_rel_alloca_disjoint >>
     simp[] >>
     qexistsl_tac [`cenv`,`func`,
       `mk_inst sd.cs_next_id ALLOCA
         [Lit (n2w (type_memory_bytes cenv (BaseT (BytesT (Dynamic n)))))]
         [STRING #"%" (toString sd.cs_next_var)]`,
       `name`,`STRING #"%" (toString sd.cs_next_var)`,`es.scopes`,`target`] >>
     simp[venomInstTheory.mk_inst_def] >>
     irule exprLoweringPropsTheory.local_ptrs_reserved_fresh >>
     qexists_tac `sd` >> simp[]) >>
  suspend "vv_post"
QED

Resume slice_code_tail_full[vv_post]:
  `!H. valid_horizon cx st0 H es.storage_trace ==>
      vv_post H ctx func cenv cx
        (Builtin (BaseT (BytesT (Dynamic n))) (Slice n) args)
        es sa sb s es (Value (BytesV copied))
        (LocatedValue (BaseT (BytesT (Dynamic n)))
          (mk_ptr (Var result_var) LocMemory)) target` by
    (rpt strip_tac >>
     qpat_assum `!H. valid_horizon _ _ H es.storage_trace ==>
       stmt_state_rel H ctx func cenv cx es target /\ _`
       (qspec_then `H` mp_tac) >>
     (impl_tac >- first_assum ACCEPT_TAC) >> strip_tac >>
     irule (exprSimHashTheory.vv_post_allocated_memory_intro |>
       Q.INST [`e` |-> `Builtin (BaseT (BytesT (Dynamic n))) (Slice n) args`] |>
       SRULE [vyperASTTheory.expr_type_def]) >>
     simp[vyperASTTheory.expr_type_def,loweringPostsTheory.post_value_type_def,
       compileEnvTheory.is_word_type_def,contextTheory.mk_ptr_def,
       venomStateTheory.eval_operand_def,loweringPostsTheory.val_footprint_def] >>
     qexistsl_tac [`sd.cs_next_id`,`w2n result_word`,
       `type_memory_bytes cenv (BaseT (BytesT (Dynamic n)))`] >>
     simp[] >>
     qx_genl_tac [`name`,`lb`,`lsz`] >> strip_tac >>
     qpat_assum `!name b sz. local_region cenv es.scopes target name b sz ==> _`
       (qspecl_then [`name`,`lb`,`lsz`] mp_tac) >>
     simp[loweringStateRelDefsTheory.regions_disjoint_def]) >>
  suspend "normal_outcome"
QED

Resume slice_code_tail_full[normal_outcome]:
  rpt (qpat_x_assum `gas_outcome_full _ _ _ _ _ _ _ _` kall_tac) >>
  irule gas_outcome_full_pure >> reverse conj_tac >- simp[] >>
  qexistsl_tac [`HG`,`es`,`INL (Value (BytesV copied))`,`target`,`tm`] >>
  conj_tac >-
    (qpat_assum `!tail. source _ = _` mp_tac >>
     simp[exprSimSliceSourceTheory.slice_bytes_nat,Abbr `copied`]) >>
  simp[]
QED

Resume slice_code_tail_full[bounds_abort]:
  qabbrev_tac `aborted = revert_state (set_returndata [] bound_state)` >>
  `run_inst_seq (emitted_insts sc sd) zq = Abort Revert_abort aborted` by
    (simp[Abbr `aborted`] >> Cases_on `i+k < dimword (:256)` >> simp[]) >>
  mp_tac (Q.INST [`sa` |-> `sc`,`sb` |-> `sd`,`s` |-> `zq`,
     `a` |-> `start`,`n` |-> `cnt`,`limit` |-> `limit`,
     `wa` |-> `n2w i`,`wn` |-> `n2w k`,
     `wl` |-> `n2w (LENGTH (code:word8 list))`,
     `G` |-> `G4`,`tn` |-> `tn4`,`u` |-> `aborted`,`ab` |-> `Revert_abort`,
     `explicit` |-> `explicit`]
     bodyFullBuiltinBytestringAbortTheory.bytestring_slice_bounds_full_abort) >>
  (impl_tac >-
    (simp[venomStateTheory.eval_operand_def,venomStateTheory.lookup_var_def,
          venomStateTheory.update_var_def,finite_mapTheory.FLOOKUP_UPDATE] >>
     qpat_assum `!op. MEM op [start;cnt;limit] ==> _` mp_tac >>
     qpat_assum `limit = Var size_var` mp_tac >>
     rpt (pop_assum kall_tac) >> simp[MEM] >> rpt strip_tac >> gvs[] >> metis_tac[])) >>
  disch_then (qx_choose_then `G6` (qx_choose_then `tn6` strip_assume_tac) o CONJUNCT2) >>
  qabbrev_tac `abort_target = aborted with vs_inst_idx := zq.vs_inst_idx+5` >>
  `!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG)
      (s,G,tn) [] (Abort Revert_abort abort_target,G6,tn6)` by
    (gen_tac >> qunabbrev_tac `abort_target` >>
     qpat_assum `!D. gas_origin_ptr_path _ (s,G,tn) _ _` (qspec_then `D` mp_tac) >>
     qpat_assum `!D. gas_origin_ptr_path _ (zq,G4,tn4) _ _` (qspec_then `D` mp_tac) >>
     rpt (pop_assum kall_tac) >>
     metis_tac[fragGasOriginPtrTheory.gas_origin_ptr_path_append,listTheory.APPEND_NIL]) >>
  irule gas_outcome_full_exit >> reverse conj_tac >- simp[] >>
  qexistsl_tac [`G6`,`es`,`Abort Revert_abort abort_target`,
    `INR (Error (RuntimeError "evaluate_slice range"))`,`tn6`] >>
  qpat_assum `!tail. source _ = _` mp_tac >>
  simp[exprSimSliceSourceTheory.slice_bytes_nat,
       fragExecTheory.exit_result_def,exprSimDefsTheory.expr_exit_def,
       exprSimDefsTheory.halt_exit_def]
QED

Finalise slice_code_tail_full
