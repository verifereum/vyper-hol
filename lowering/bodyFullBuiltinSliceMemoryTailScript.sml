(* Joint memory suffix for ordinary bytes and string Slice sources. *)
Theory bodyFullBuiltinSliceMemoryTail
Ancestors
  bodyFullPreds bodySimFull bodyFullOfVV gasOutcomeFullCompose
  bodyFullUnwrapRun exprSimProps exprSimWordArgs exprSimHash
  exprSimSliceExtcodeEntry exprSimSliceData exprSimSliceTerminal
  assignTuplePtrBytesCopy assignTuplePtrStageFrame assignTuplePtrLocalFixedCopy
  bodyPtrBytestringBuiltinsAllocation decoderGhostFramePtr reasonCopySourcePtr
  bodyFullBuiltinBytestringQuery bodyFullBuiltinBytestringBuffer
  bodyFullBuiltinBytestringBounds bodyFullBuiltinBytestringCopy
  bodyFullBuiltinBytestringAbort bodyFullBuiltinBytestringOutBuffer
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
    (\H res ee gt r. expr_exit res r /\ halt_exit H cx ee res r)
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
  `zb = s with <|vs_vars := zb.vs_vars;
      vs_inst_idx := LENGTH sc.cs_current_insts|>` by
    (qpat_assum `bound_state = s with vs_vars := bound_state.vs_vars`
       (mp_tac o Q.AP_TERM `\st. st with vs_inst_idx := LENGTH sc.cs_current_insts`) >>
     simp[Abbr `zb`]) >>
  `!x. not_fresh_at sa x ==>
     lookup_var x zb = lookup_var x s /\ FLOOKUP G1 x = FLOOKUP G x /\
     op_taint tn1 (Var x) = op_taint tn (Var x)` by
    (simp[Abbr `zb`,venomStateTheory.lookup_var_def,NoAsms] >>
     qpat_assum `!x. not_fresh_at sa x ==> lookup_var x bound_state = _ /\ _`
       (ACCEPT_TAC o REWRITE_RULE[venomStateTheory.lookup_var_def])) >>
  `alloca_history func zb` by
    (simp[Abbr `zb`] >>
     qspecl_then [`emitted_insts sa sc`,`sa`,`sc`,`s`,`bound_state`]
       mp_tac bodyFullUnwrapRunTheory.emitted_alloca_history >>
     (impl_tac >-
       (qpat_assum `compile_assert_slice_bounds _ _ _ sa = _`
          (mp_then Any strip_assume_tac
            bodyPtrBytestringBuiltinsBoundsTheory.compile_assert_slice_bounds_layout) >>
        qpat_assum `same_blocks sa sc`
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
     eval_operand op zb = eval_operand op s /\
     op_prov G1 op = op_prov G op /\ op_taint tn1 op = op_taint tn op` by
    (mp_tac (bodyPtrBytestringBuiltinsExternalSliceTheory.reserved_operand_ghost_frame |> Q.INST
       [`sa` |-> `sa`,`s` |-> `s`,`t` |-> `zb`,
        `G` |-> `G`,`HG` |-> `G1`,`tn` |-> `tn`,`tm` |-> `tn1`]) >>
     (impl_tac >- simp[]) >> disch_then ACCEPT_TAC) >>
  `!x. (start = Var x \/ cnt = Var x \/ limit = Var x \/ Var src = Var x) ==>
      not_fresh_at sa x` by metis_tac[MEM] >>
  `eval_operand start zb = SOME (n2w i) /\ op_taint tn1 start = {} /\
   eval_operand cnt zb = SOME (n2w k) /\ op_taint tn1 cnt = {}` by
    (qpat_assum `!op. (!x. op = Var x ==> not_fresh_at sa x) ==>
      eval_operand op zb = _ /\ _`
       (fn th => map_every mp_tac (map (fn operand => Q.SPEC operand th)
         [`start`,`cnt`])) >> simp[]) >>
  `not_fresh_at sa src` by metis_tac[] >>
  `lookup_var src zb = SOME p /\ ptr_covers G1 tn1 src zb (LENGTH bs)` by
    (qpat_assum `!x. not_fresh_at sa x ==> lookup_var x zb = _ /\ _`
       (qspec_then `src` mp_tac) >>
     qpat_assum `ptr_covers G tn src s (LENGTH bs)`
       (mp_tac o REWRITE_RULE[bodyPtrDefsTheory.ptr_covers_def]) >>
     qpat_assum `lookup_var src s = SOME p` mp_tac >>
     qpat_assum `not_fresh_at sa src` mp_tac >>
     rpt (pop_assum kall_tac) >> simp[bodyPtrDefsTheory.ptr_covers_def] >>
     metis_tac[]) >>
  `sa.cs_next_var <= sc.cs_next_var /\ sa.cs_next_id <= sc.cs_next_id` by
    (qpat_assum `compile_assert_slice_bounds _ _ _ sa = _`
       (mp_then Any strip_assume_tac
         bodyPtrBytestringBuiltinsBoundsTheory.compile_assert_slice_bounds_layout) >> simp[]) >>
  `!x. not_fresh_at sa x ==> not_fresh_at sc x` by
    (rpt strip_tac >> irule freshWritesTheory.not_fresh_at_mono >>
     qexists_tac `sa` >> simp[]) >>
  `local_ptrs_reserved cenv sc` by
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
  `zb.vs_current_bb = sc.cs_current_bb /\
   zb.vs_inst_idx = LENGTH sc.cs_current_insts /\ ~zb.vs_halted` by simp[Abbr `zb`] >>
  drule_at (Pat `stmt_state_rel _ _ _ _ _ _ _`)
    (Q.INST [`sa` |-> `sc`,`sb` |-> `sd`,`s` |-> `zb`,
      `root` |-> `out`,`data` |-> `out_data`,`n` |-> `N`,
      `G` |-> `G1`,`tn` |-> `tn1`,`explicit` |-> `explicit`,`PG` |-> `PG`]
      bytestring_out_buffer_full_run) >>
  disch_then (mp_tac o SPEC_ALL) >>
  (impl_tac >- (simp[] >> decide_tac)) >>
  disch_then (qx_choose_then `root` (qx_choose_then `dst`
    (qx_choose_then `w` (qx_choose_then `v` (qx_choose_then `G2`
      (qx_choose_then `tn2` strip_assume_tac)))))) >>
  suspend "success_output"
QED

Resume slice_memory_tail_full[bounds_abort]:
  qabbrev_tac `aborted = revert_state (set_returndata [] bound_state)` >>
  `run_inst_seq (emitted_insts sa sc) s = Abort Revert_abort aborted` by
    (simp[Abbr `aborted`] >> Cases_on `i+k < dimword (:256)` >> simp[]) >>
  mp_tac (Q.INST [`sa` |-> `sa`,`sb` |-> `sc`,`s` |-> `s`,
     `a` |-> `start`,`n` |-> `cnt`,`limit` |-> `limit`,
     `wa` |-> `n2w i`,`wn` |-> `n2w k`,
     `wl` |-> `n2w (LENGTH (bs:word8 list))`,
     `G` |-> `G`,`tn` |-> `tn`,`u` |-> `aborted`,`ab` |-> `Revert_abort`,
     `explicit` |-> `explicit`]
     bodyFullBuiltinBytestringAbortTheory.bytestring_slice_bounds_full_abort) >>
  (impl_tac >-
    (simp[] >> qpat_assum `!op. MEM op [start;cnt;limit] ==> _` mp_tac >>
     rpt (pop_assum kall_tac) >> simp[MEM] >> rpt strip_tac >> gvs[] >> metis_tac[])) >>
  disch_then (qx_choose_then `G6` (qx_choose_then `tn6` strip_assume_tac) o CONJUNCT2) >>
  irule gas_outcome_full_exit >> reverse conj_tac >- simp[] >>
  qexistsl_tac [`G6`,`es`,
    `Abort Revert_abort (aborted with vs_inst_idx := s.vs_inst_idx+5)`,
    `INR (Error (RuntimeError "evaluate_slice range"))`,`tn6`] >>
  qpat_assum `!tail. source _ = _` mp_tac >>
  simp[fragExecTheory.exit_result_def,exprSimDefsTheory.expr_exit_def,
    exprSimDefsTheory.halt_exit_def]
QED

Resume slice_memory_tail_full[success_output]:
  cheat
QED

Finalise slice_memory_tail_full
