(* Joint memory suffix for ordinary bytes and string Slice sources. *)
Theory bodyFullBuiltinSliceMemoryTail
Ancestors
  bodyFullPreds bodySimFull bodyFullOfVV gasOutcomeFullCompose
  bodyFullUnwrapRun exprSimProps exprSimWordArgs exprSimHash
  exprSimSliceExtcodeEntry exprSimSliceData exprSimSliceTerminal
  assignTuplePtrBytesCopy assignTuplePtrStageFrame assignTuplePtrLocalFixedCopy
  bodyPtrBytestringBuiltinsAllocation
  bodyFullBuiltinBytestringQuery bodyFullBuiltinBytestringBuffer
  bodyFullBuiltinBytestringBounds bodyFullBuiltinBytestringCopy
  bodyFullBuiltinBytestringAbort
  bodyPtrBytestringBuiltinsWindowGhost wordArgsPtr
  exprSimSliceSource exprSimSliceOrdinaryFrame exprSimHypsDefs
  exprLowering vyperInterpreter vyperAST list
  fragExec emitHelperProps bodyPtrBytestringBuiltinsSlice
  bodyPtrBytestringBuiltinsBuffer loweringPosts loweringStateRelDefs
  reasonCodeResourcesPtr bodyPtrAttributeFields

Theorem slice_memory_tail_full:
  compile_slice_data limit (Var src) start cnt N sa = (out,sb) /\
  fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
  local_ptrs_reserved cenv sa /\ ~ctx_has_dalloca ctx /\
  eval_operand limit s = SOME (n2w (LENGTH bs)) /\
  lookup_var src s = SOME p /\ ptr_covers G tn src s (LENGTH bs) /\
  op_prov G limit = NONE /\ op_taint tn limit = {} /\
  eval_operand start s = SOME (n2w i) /\
  eval_operand cnt s = SOME (n2w k) /\
  op_prov G start = NONE /\ op_taint tn start = {} /\
  op_prov G cnt = NONE /\ op_taint tn cnt = {} /\
  (!op x. MEM op [limit;Var src;start;cnt] /\ op = Var x ==>
    not_fresh_at sa x) /\
  (!l. limit <> Label l /\ start <> Label l /\ cnt <> Label l) /\
  mem_bytes_at (w2n p) (LENGTH bs) s.vs_memory = bs /\
  (!j. w2n p <= j /\ j < w2n p + LENGTH bs ==> j NOTIN tn.t_mem) /\
  w2n p + LENGTH bs < dimword (:256) /\
  w2n p + LENGTH bs <= s.vs_alloca_next /\
  i < dimword (:256) /\ k < dimword (:256) /\
  (i+k <= LENGTH bs ==> k <= n) /\
  ((a = BaseT (BytesT (Dynamic n)) /\
      result = BytesV (TAKE k (DROP i bs))) \/
   (?str. a = BaseT (StringT n) /\ bs = MAP (n2w o ORD) str /\
      result = StringV (TAKE k (DROP i str)))) /\
  e = Builtin a (Slice n) args /\
  N = type_memory_bytes cenv a /\ 32+n <= N /\ N < dimword (:256) /\
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
    ((if i+k <= LENGTH bs then INL (Value result)
      else INR (Error (RuntimeError "evaluate_slice range"))),
     es with gas_obs := tail)) ==>
  gas_outcome_full (DF,lo,explicit,ctx,func,PG) tops cx st0 source
    (es,s,G,tn)
    (\H res ee HG tm t.
      res = INL (Value result) /\
      vv_post H ctx func cenv cx e es sa sb s ee (Value result)
        (LocatedValue a (mk_ptr out LocMemory)) t /\
      vv_store_bound cx a a ee (Value result)
        (LocatedValue a (mk_ptr out LocMemory)) t /\
      t.vs_current_bb = sb.cs_current_bb /\ t.vs_inst_idx = LENGTH sb.cs_current_insts /\
      alloca_history func t /\ s.vs_alloca_next <= t.vs_alloca_next /\
      ghost_inv_at (DF H) lo d cenv cx ee HG tm t /\
      ptr_vv_ok cx a (Value result) (LocatedValue a (mk_ptr out LocMemory)) ee HG tm t /\
      ptr_buf_ok cenv e out HG t /\ ghost_kept_at lo cenv es sa G tn s HG tm)
    (\H res ee gt r. expr_exit res r)
Proof
  rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
  qpat_assum `e = _` SUBST_ALL_TAC >>
  qabbrev_tac `result_shape =
    ((a = BaseT (BytesT (Dynamic n)) /\
       result = BytesV (TAKE k (DROP i bs))) \/
     (?str. a = BaseT (StringT n) /\ bs = MAP (n2w o ORD) str /\
       result = StringV (TAKE k (DROP i str))))` >>
  `es with gas_obs := [] = es` by
    (qpat_assum `es.gas_obs = []` (SUBST1_TAC o SYM) >> simp[]) >>
  `valid_horizon cx st0 (storage_trace_horizon es.storage_trace) es.storage_trace` by
    fs[vyperStorageFootprintTheory.storage_trace_domain_def] >>
  `stmt_state_rel (storage_trace_horizon es.storage_trace)
      ctx func cenv cx es s /\
   ghost_inv_at (DF (storage_trace_horizon es.storage_trace))
      lo d cenv cx es G tn s` by
    (qpat_assum `!H. valid_horizon _ _ H es.storage_trace ==> _`
       (qspec_then `storage_trace_horizon es.storage_trace` mp_tac) >>
     (impl_tac >- simp[]) >> strip_tac >> simp[]) >>
  `alloca_inv s /\ allocas_from lo s /\ lo <= s.vs_alloca_next` by
    fs[exprLoweringPropsTheory.stmt_state_rel_def,bodyPtrDefsTheory.ghost_inv_at_def] >>
  drule exprSimSliceDataTheory.slice_data_decompose >> strip_tac >>
  `cs_extends sa sc /\ cs_extends sc sd /\ cs_extends sd se /\
   cs_extends se sf /\ cs_extends sf sb` by
    (rpt conj_tac
     >- metis_tac[bodyPtrBytestringBuiltinsSliceTheory.slice_bounds_extends]
     >- metis_tac[bodyPtrBytestringBuiltinsBufferTheory.compile_slice_out_buf_compiler_parts,
                  compileEnvTheory.cs_extends_trans] >>
     metis_tac[fragExecTheory.cs_appends_emit_helpers,fragExecTheory.cs_appends_def]) >>
  `fn_has_code sa sc func /\ fn_has_code sc sd func /\ fn_has_code sc sb func /\
   fn_has_code sd se func /\ fn_has_code se sf func /\ fn_has_code sf sb func` by
    (qpat_assum `fn_has_code sa sb func` mp_tac >>
     qpat_assum `cs_extends sa sc` mp_tac >> qpat_assum `cs_extends sc sd` mp_tac >>
     qpat_assum `cs_extends sd se` mp_tac >> qpat_assum `cs_extends se sf` mp_tac >>
     qpat_assum `cs_extends sf sb` mp_tac >> rpt (pop_assum kall_tac) >>
     metis_tac[fragExecTheory.fn_has_code_split,compileEnvTheory.cs_extends_trans]) >>
  `!op. MEM op [start;cnt;limit] ==>
     op_prov G op = NONE /\ op_taint tn op = {} /\
     (!x. op = Var x ==> not_fresh_at sa x)` by
    (simp[MEM] >> rpt strip_tac >> gvs[] >> metis_tac[MEM]) >>
  mp_tac (bodyPtrBytestringBuiltinsBoundsTheory.slice_bounds_reserved_natural_runtime |> Q.INST
    [`sa` |-> `sa`,`sb` |-> `sc`,`s` |-> `s`,`start` |-> `start`,
     `len` |-> `cnt`,`limit` |-> `limit`,`a` |-> `i`,`n` |-> `k`,
     `cap` |-> `LENGTH (bs:word8 list)`]) >>
  (impl_tac >-
    (simp[] >>
     qpat_assum `!op. MEM op [start;cnt;limit] ==> _` mp_tac >>
     rpt (pop_assum kall_tac) >> simp[MEM] >> metis_tac[])) >>
  disch_then (qx_choose_then `bound_state` strip_assume_tac) >>
  reverse (Cases_on `i+k <= LENGTH bs`)
  >- suspend "bounds_abort" >>
  `k <= n /\ i+k < dimword (:256)` by (simp[] >> decide_tac) >>
  `run_inst_seq (emitted_insts sa sc) s = OK bound_state` by simp[] >>
  mp_tac (bodyFullBuiltinBytestringBoundsTheory.bytestring_slice_bounds_full_run |> Q.INST
    [`sa` |-> `sa`,`sb` |-> `sc`,`s` |-> `s`,`u` |-> `bound_state`,
     `start` |-> `start`,`len` |-> `cnt`,`limit` |-> `limit`,
     `G` |-> `G`,`tn` |-> `tn`,`wa` |-> `n2w i`,`wn` |-> `n2w k`,
     `wl` |-> `n2w (LENGTH (bs:word8 list))`,`explicit` |-> `explicit`]) >>
  (impl_tac >-
    (simp[] >> qpat_assum `!op. MEM op [start;cnt;limit] ==> _` mp_tac >>
     rpt (pop_assum kall_tac) >> simp[MEM] >> metis_tac[])) >>
  disch_then (qx_choose_then `G1` (qx_choose_then `tn1` strip_assume_tac)) >>
  qabbrev_tac `zb = bound_state with vs_inst_idx := LENGTH sc.cs_current_insts` >>
  FAIL_TAC "memory Slice bounds success prefix"
QED

Resume slice_memory_tail_full[bounds_abort]:
  FAIL_TAC "memory Slice bounds abort prefix"
QED

Finalise slice_memory_tail_full
