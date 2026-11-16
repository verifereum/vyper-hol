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
      (INST_TYPE [alpha |-> ``:256``, beta |-> ``:256``]
        bytestring_out_buffer_full_run)) >>
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
  `!x. not_fresh_at sa x ==>
     lookup_var x v = lookup_var x s /\ FLOOKUP G2 x = FLOOKUP G x /\
     op_taint tn2 (Var x) = op_taint tn (Var x)` by
    (qpat_assum `!x. not_fresh_at sc x ==> lookup_var x v = _ /\ _` mp_tac >>
     qpat_assum `!x. not_fresh_at sa x ==> lookup_var x zb = _ /\ _` mp_tac >>
     qpat_assum `!x. not_fresh_at sa x ==> not_fresh_at sc x` mp_tac >>
     rpt (pop_assum kall_tac) >> metis_tac[]) >>
  `v.vs_memory = s.vs_memory /\ v.vs_labels = s.vs_labels /\
   v.vs_accounts = s.vs_accounts /\ v.vs_call_ctx = s.vs_call_ctx /\
   v.vs_code = s.vs_code /\ v.vs_transient = s.vs_transient /\
   v.vs_immutables = s.vs_immutables` by
    (qpat_assum `v with <|vs_vars := _;vs_allocas := _;
       vs_alloca_next := _;vs_inst_idx := _|> = zb` mp_tac >>
     simp[venomStateTheory.venom_state_component_equality]) >>
  `!op. (!x. op = Var x ==> not_fresh_at sa x) ==>
     eval_operand op v = eval_operand op s /\
     op_prov G2 op = op_prov G op /\ op_taint tn2 op = op_taint tn op` by
    (mp_tac (bodyPtrBytestringBuiltinsExternalSliceTheory.reserved_operand_ghost_frame |> Q.INST
       [`sa` |-> `sa`,`s` |-> `s`,`t` |-> `v`,
        `G` |-> `G`,`HG` |-> `G2`,`tn` |-> `tn`,`tm` |-> `tn2`]) >>
     (impl_tac >- simp[]) >> disch_then ACCEPT_TAC) >>
  `eval_operand start v = SOME (n2w i) /\ op_taint tn2 start = {} /\
   eval_operand cnt v = SOME (n2w k) /\ op_taint tn2 cnt = {}` by
    (qpat_assum `!op. (!x. op = Var x ==> not_fresh_at sa x) ==>
      eval_operand op v = _ /\ _`
       (fn th => map_every mp_tac (map (fn operand => Q.SPEC operand th)
         [`start`,`cnt`])) >> simp[]) >>
  `lookup_var src v = SOME p /\ ptr_covers G2 tn2 src v (LENGTH bs)` by
    (qpat_assum `!x. not_fresh_at sa x ==> lookup_var x v = _ /\ _`
       (qspec_then `src` mp_tac) >>
     qpat_assum `ptr_covers G tn src s (LENGTH bs)`
       (mp_tac o REWRITE_RULE[bodyPtrDefsTheory.ptr_covers_def]) >>
     qpat_assum `lookup_var src s = SOME p` mp_tac >>
     qpat_assum `not_fresh_at sa src` mp_tac >>
     rpt (pop_assum kall_tac) >> simp[bodyPtrDefsTheory.ptr_covers_def] >> metis_tac[]) >>
  `sa.cs_next_var <= sd.cs_next_var` by
    (qspecl_then [`N`,`sc`] mp_tac
       exprLoweringPropsTheory.ci_mono_compile_slice_out_buf >>
     simp[exprLoweringPropsTheory.ci_mono_def] >> decide_tac) >>
  `!x. not_fresh_at sa x ==> not_fresh_at sd x` by
    (rpt strip_tac >> irule freshWritesTheory.not_fresh_at_mono >>
     qexists_tac `sa` >> simp[]) >>
  qabbrev_tac `copy_var = STRING #"%" (toString sd.cs_next_var)` >>
  `copy_src = Var copy_var /\
   se.cs_current_bb = sd.cs_current_bb /\
   se.cs_current_insts = sd.cs_current_insts ++
     [mk_inst sd.cs_next_id ADD [Var src;start] [copy_var]] /\
   (!x. not_fresh_at sd x ==> x <> copy_var)` by
    (simp[Abbr `copy_var`,NoAsms] >>
     qpat_assum `emit_op ADD [Var src;start] sd = _` mp_tac >>
     rpt (pop_assum kall_tac) >>
     simp[emitHelperTheory.emit_op_def,compileEnvTheory.comp_bind_def,
       compileEnvTheory.comp_ignore_bind_def,compileEnvTheory.comp_return_def,
       compileEnvTheory.fresh_id_def,compileEnvTheory.fresh_var_def,
       compileEnvTheory.emit_def,loweringStateRelDefsTheory.not_fresh_at_def] >>
     rpt strip_tac >> gvs[]) >>
  qabbrev_tac `offset_inst = mk_inst sd.cs_next_id ADD [Var src;start] [copy_var]` >>
  qabbrev_tac `za = update_var copy_var (p+n2w i) v` >>
  qabbrev_tac `G3 = step_prov PG G2 offset_inst za` >>
  qabbrev_tac `tn3 = step_taint offset_inst v za tn2` >>
  `step_inst_base offset_inst v = OK za` by
    simp[Abbr `offset_inst`,Abbr `za`,venomExecSemanticsTheory.step_inst_base_opcode_eqs,
      venomInstTheory.mk_inst_def,venomExecSemanticsTheory.exec_pure2_def,
      venomStateTheory.eval_operand_def] >>
  `ptr_covers G3 tn3 copy_var za k` by
    (mp_tac (Q.SPECL [`PG`,`G2`,`tn2`,`v`,`sd.cs_next_id`,`src`,`copy_var`,
       `p`,`i`,`LENGTH (bs:word8 list)`,`k`,`start`]
       bodyPtrBytestringBuiltinsAllocationTheory.pointer_offset_covers) >>
     (impl_tac >- (simp[] >> decide_tac)) >>
     simp[Abbr `G3`,Abbr `tn3`,Abbr `offset_inst`,Abbr `za`,
       bodyPtrDefsTheory.ptr_covers_def,venomStateTheory.lookup_var_def]) >>
  suspend "source_offset"
QED

Resume slice_memory_tail_full[source_offset]:
  `op_taint tn3 (Var copy_var) = {} /\
   tn3.t_mem = tn2.t_mem /\ tn3.t_stor = tn2.t_stor /\
   tn3.t_trans = tn2.t_trans /\
   (!x. x <> copy_var ==> FLOOKUP G3 x = FLOOKUP G2 x /\
     op_taint tn3 (Var x) = op_taint tn2 (Var x))` by
    simp[Abbr `G3`,Abbr `tn3`,Abbr `offset_inst`,Abbr `za`,
      typedCopyPtrTheory.copy_len_binop_ghost_frame] >>
  `tn3.t_imm = tn2.t_imm` by
    simp[Abbr `tn3`,Abbr `offset_inst`,ptrDisciplineTheory.step_taint_def,
      ptrDisciplineTheory.imm_taint_def,venomInstTheory.mk_inst_def] >>
  `!x. not_fresh_at sd x ==>
     lookup_var x za = lookup_var x v /\ FLOOKUP G3 x = FLOOKUP G2 x /\
     op_taint tn3 (Var x) = op_taint tn2 (Var x)` by
    (rpt strip_tac >>
     qpat_assum `!x. not_fresh_at sd x ==> x <> copy_var` (qspec_then `x` assume_tac) >>
     simp[Abbr `za`,emitHelperPropsTheory.lookup_var_update_var]) >>
  `!op. (!x. op = Var x ==> not_fresh_at sd x) ==>
     eval_operand op za = eval_operand op v /\
     op_prov G3 op = op_prov G2 op /\ op_taint tn3 op = op_taint tn2 op` by
    (mp_tac (bodyPtrBytestringBuiltinsExternalSliceTheory.reserved_operand_ghost_frame |> Q.INST
       [`sa` |-> `sd`,`s` |-> `v`,`t` |-> `za`,
        `G` |-> `G2`,`HG` |-> `G3`,`tn` |-> `tn2`,`tm` |-> `tn3`]) >>
     (impl_tac >- simp[Abbr `za`,venomStateTheory.update_var_def]) >> disch_then ACCEPT_TAC) >>
  `eval_operand cnt za = SOME (n2w k) /\ op_taint tn3 cnt = {}` by
    (qpat_assum `!op. (!x. op = Var x ==> not_fresh_at sd x) ==>
      eval_operand op za = _ /\ _` (qspec_then `cnt` mp_tac) >> simp[] >> metis_tac[]) >>
  `lookup_var copy_var za = SOME (p+n2w i) /\
   lookup_var root za = SOME w /\
   lookup_var dst za = SOME (w+32w)` by
    (simp[Abbr `za`,emitHelperPropsTheory.lookup_var_update_var] >> metis_tac[]) >>
  `ptr_covers G3 tn3 root za N /\ ptr_covers G3 tn3 dst za (N-32)` by
    (conj_tac >> irule decoderGhostFramePtrTheory.ptr_covers_frame >>
     qexistsl_tac [`G2`,`v`,`tn2`] >> simp[] >> metis_tac[]) >>
  `ptr_covers G3 tn3 dst za k` by
    (irule reasonCopySourcePtrTheory.ptr_covers_mono >>
     qexists_tac `N-32` >> simp[] >> decide_tac) >>
  `w2n (w+32w) = w2n w+32 /\
   w2n (p+n2w i) = w2n p+i` by
    (simp[wordsTheory.w2n_add_2,wordsTheory.w2n_n2w] >>
     conj_tac >> irule arithmeticTheory.LESS_MOD >> decide_tac) >>
  qabbrev_tac `copy_inst = mk_inst se.cs_next_id MCOPY [Var dst;Var copy_var;cnt] []` >>
  qabbrev_tac `zc = mcopy (w2n w+32) (w2n p+i) k za` >>
  qabbrev_tac `tn4 = step_taint copy_inst za zc tn3` >>
  `!D. inst_seq_ptr D 0 ctx func PG G3 tn3 [copy_inst] za G3 tn4 /\
    run_inst_seq [copy_inst] za = OK zc` by
    (gen_tac >>
     mp_tac (Q.SPECL [`D`,`ctx`,`func`,`PG`,`G3`,`tn3`,`za`,`se.cs_next_id`,
       `dst`,`copy_var`,`cnt`,`p+n2w i`,`w+32w`,`n2w k`]
       assignTuplePtrLocalFixedCopyTheory.mcopy_operand_seq_ptr) >>
     simp[Abbr `copy_inst`,Abbr `zc`,Abbr `tn4`]) >>
  `step_inst_base copy_inst za = OK zc` by
    simp[Abbr `copy_inst`,Abbr `zc`,
       venomExecSemanticsTheory.step_inst_base_opcode_eqs,
       venomInstTheory.mk_inst_def,venomStateTheory.eval_operand_def] >>
  `step_prov PG G3 copy_inst zc = G3 /\
   tn4.t_var = tn3.t_var /\ tn4.t_stor = tn3.t_stor /\
   tn4.t_trans = tn3.t_trans /\ tn4.t_imm = tn3.t_imm` by
    (mp_tac (Q.SPECL [`PG`,`G3`,`tn3`,`za`,`se.cs_next_id`,`Var dst`,
       `Var copy_var`,`cnt`,`p+n2w i`,`w+32w`,`n2w k`]
       fragExecPtrTheory.mcopy_operand_ghost_frame) >>
     (impl_tac >- simp[venomStateTheory.eval_operand_def]) >>
     simp[wordsTheory.w2n_n2w] >> strip_tac >>
     mp_tac (Q.SPECL [`tn3`,`za`,`se.cs_next_id`,`Var dst`,
       `Var copy_var`,`cnt`,`p+n2w i`,`w+32w`,`n2w k`,`k`,
       `step_taint (mk_inst se.cs_next_id MCOPY [Var dst;Var copy_var;cnt] []) za
         (mcopy (w2n (w:bytes32)+32) (w2n (p:bytes32)+i) k za) tn3`]
       assignTuplePtrLocalFixedCopyTheory.mcopy_operand_taint_frames_ptr) >>
     (impl_tac >- simp[venomStateTheory.eval_operand_def,wordsTheory.w2n_n2w,
       Abbr `copy_inst`,Abbr `zc`,Abbr `tn4`]) >> strip_tac >>
     simp[Abbr `copy_inst`,Abbr `zc`,Abbr `tn4`,wordsTheory.w2n_n2w]) >>
  suspend "mcopy_checked"
QED

Resume slice_memory_tail_full[mcopy_checked]:
  `step_prov PG G2 offset_inst za = G3 /\ step_taint offset_inst v za tn2 = tn3` by
    simp[Abbr `G3`,Abbr `tn3`] >>
  `lookup_var root zc = SOME w /\ eval_operand cnt zc = SOME (n2w k) /\
   op_taint tn4 cnt = {}` by
    (simp[Abbr `zc`,NoAsms] >>
     qpat_assum `lookup_var root za = SOME w` mp_tac >>
     qpat_assum `eval_operand cnt za = SOME (n2w k)` mp_tac >>
     qpat_assum `op_taint tn3 cnt = {}` mp_tac >>
     qpat_assum `tn4.t_var = tn3.t_var` mp_tac >>
     rpt (pop_assum kall_tac) >> Cases_on `cnt` >>
     simp[venomExecSemanticsTheory.mcopy_def,
       venomStateTheory.write_memory_with_expansion_def,venomStateTheory.eval_operand_def,
       ptrDisciplineTheory.op_taint_def,venomStateTheory.lookup_var_def]) >>
  `!op. op_taint tn4 op = op_taint tn3 op` by
    (qpat_assum `tn4.t_var = tn3.t_var` mp_tac >>
     rpt (pop_assum kall_tac) >> disch_tac >> Cases_on `op` >>
     simp[ptrDisciplineTheory.op_taint_def]) >>
  `ptr_covers G3 tn4 root zc N` by
    (irule decoderGhostFramePtrTheory.ptr_covers_frame >>
     qexistsl_tac [`G3`,`za`,`tn3`] >>
     simp[Abbr `zc`,venomExecSemanticsTheory.mcopy_def,
       venomStateTheory.write_memory_with_expansion_def,
       venomStateTheory.lookup_var_def]) >>
  `ptr_covers G3 tn4 root zc 32` by
    (irule reasonCopySourcePtrTheory.ptr_covers_mono >>
     qexists_tac `N` >> simp[] >> decide_tac) >>
  qabbrev_tac `store_inst = mk_inst sf.cs_next_id MSTORE [Var root;cnt] []` >>
  qabbrev_tac `zt = mstore (w2n w) (n2w k) zc` >>
  qabbrev_tac `tm = step_taint store_inst zc zt tn4` >>
  `step_inst_base store_inst zc = OK zt` by
    simp[Abbr `store_inst`,Abbr `zt`,
       venomExecSemanticsTheory.step_inst_base_opcode_eqs,
       venomInstTheory.mk_inst_def,venomExecSemanticsTheory.exec_write2_def,
       venomStateTheory.eval_operand_def] >>
  `step_prov PG G3 store_inst zt = G3 /\
   tm.t_var = tn4.t_var /\ tm.t_stor = tn4.t_stor /\
   tm.t_trans = tn4.t_trans /\ tm.t_imm = tn4.t_imm` by
    simp[Abbr `store_inst`,Abbr `zt`,Abbr `tm`,
       wordLoadStorePtrTheory.ifexp_materialize_mstore_ghost] >>
  `!op. op_taint tm op = op_taint tn4 op` by
    (qpat_assum `tm.t_var = tn4.t_var` mp_tac >>
     rpt (pop_assum kall_tac) >> disch_tac >> Cases_on `op` >>
     simp[ptrDisciplineTheory.op_taint_def]) >>
  `~is_terminator copy_inst.inst_opcode /\ ~is_terminator store_inst.inst_opcode` by
    simp[Abbr `copy_inst`,Abbr `store_inst`,venomInstTheory.mk_inst_def,
      venomInstTheory.is_terminator_def] >>
  `op_taint tn2 (Var src) = {}` by
    (qpat_assum `ptr_covers G2 tn2 src v (LENGTH bs)`
       (ACCEPT_TAC o CONJUNCT1 o REWRITE_RULE[bodyPtrDefsTheory.ptr_covers_def])) >>
  `!D. inst_seq_ptr D 0 ctx func PG G2 tn2
      [offset_inst;copy_inst;store_inst] v G3 tm` by
    (gen_tac >> simp[fragGasSeqPtrTheory.inst_seq_ptr_def,
       instIdxIndepTheory.step_inst_inst_idx_indep,
       instIdxIndepTheory.exec_result_map_def] >>
     conj_tac >-
       (simp[Abbr `offset_inst`] >> irule typedCopyPtrTheory.ptr_inst_ok_copy_len_binop >>
        simp[]) >>
     conj_tac >-
       (simp[Abbr `copy_inst`] >> irule fragExecPtrTheory.ptr_inst_ok_mcopy_operand >>
        simp[]) >>
     simp[Abbr `store_inst`] >> irule fragExecPtrTheory.ptr_inst_ok_mstore >> simp[]) >>
  `lo <= v.vs_alloca_next` by decide_tac >>
  `!D. inst_seq_ptr D lo ctx func PG G2 tn2
      [offset_inst;copy_inst;store_inst] v G3 tm` by
    (gen_tac >> irule instSeqPtrLoTheory.inst_seq_ptr_zero_to_lo >> simp[] >>
     qexists_tac `D` >> simp[]) >>
  `run_inst_seq [offset_inst;copy_inst;store_inst] v = OK zt` by
    simp[exprLoweringPropsTheory.run_inst_seq_def] >>
  `inst_mem_below_frontier offset_inst v /\
   inst_mem_below_frontier copy_inst za /\ inst_mem_below_frontier store_inst zc` by
    (rpt conj_tac
     >- (irule instMemFrontierTheory.below_frontier_no_ranges >>
         simp[Abbr `offset_inst`,venomInstTheory.mk_inst_def])
     >- (simp[Abbr `copy_inst`,instMemFrontierTheory.below_frontier_MCOPY,
           venomStateTheory.eval_operand_def,Abbr `za`,venomStateTheory.update_var_def] >>
         decide_tac) >>
     simp[Abbr `store_inst`,instMemFrontierTheory.below_frontier_MSTORE,
       venomStateTheory.eval_operand_def,Abbr `zc`,Abbr `za`,
       venomExecSemanticsTheory.mcopy_def,venomStateTheory.write_memory_with_expansion_def,
       venomStateTheory.update_var_def] >> decide_tac) >>
  `!st. inst_dload_in_section offset_inst st /\
      inst_dload_in_section copy_inst st /\ inst_dload_in_section store_inst st` by
    simp[memSafeRunTheory.inst_dload_in_section_def,
      Abbr `offset_inst`,Abbr `copy_inst`,Abbr `store_inst`,venomInstTheory.mk_inst_def] >>
  `run_inst_seq_mem_ok [offset_inst;copy_inst;store_inst] v` by
    simp[fragExecMemTheory.run_inst_seq_mem_ok_cons,
      fragExecMemTheory.run_inst_seq_mem_ok_last] >>
  `sb.cs_current_bb = sd.cs_current_bb /\
   sb.cs_current_insts = sd.cs_current_insts ++ [offset_inst;copy_inst;store_inst]` by
    (qpat_assum `emit_void MCOPY _ se = _`
       (mp_then Any strip_assume_tac emitHelperPropsTheory.emitted_insts_emit_void) >>
     qpat_assum `emit_void MSTORE _ sf = _`
       (mp_then Any strip_assume_tac emitHelperPropsTheory.emitted_insts_emit_void) >>
     qpat_assum `emit_void MCOPY _ se = _`
       (mp_then Any strip_assume_tac exprLoweringPropsTheory.emit_void_same_blocks) >>
     qpat_assum `emit_void MSTORE _ sf = _`
       (mp_then Any strip_assume_tac exprLoweringPropsTheory.emit_void_same_blocks) >>
     qpat_assum `sf.cs_current_insts = _` mp_tac >>
     qpat_assum `sb.cs_current_insts = _` mp_tac >>
     qpat_assum `same_blocks se sf` mp_tac >>
     qpat_assum `same_blocks sf sb` mp_tac >>
     qpat_assum `se.cs_current_bb = sd.cs_current_bb` mp_tac >>
     qpat_assum `se.cs_current_insts = _` mp_tac >>
     qpat_assum `out = Var root` mp_tac >>
     qpat_assum `out_data = Var dst` mp_tac >>
     qpat_assum `copy_src = Var copy_var` mp_tac >>
     simp[Abbr `offset_inst`,Abbr `copy_inst`,Abbr `store_inst`,NoAsms] >>
     rpt (pop_assum kall_tac) >> rpt strip_tac >>
     gvs[exprLoweringPropsTheory.same_blocks_def,listTheory.APPEND_ASSOC]) >>
  `fn_has_code sd sb func` by
    metis_tac[fragExecTheory.fn_has_code_split,compileEnvTheory.cs_extends_trans] >>
  qabbrev_tac `target = zt with vs_inst_idx := LENGTH sb.cs_current_insts` >>
  `!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (v,G2,tn2) []
      (OK target,G3,tm)` by
    (gen_tac >> simp[Abbr `target`,NoAsms] >>
     irule bodyFullUnwrapRunTheory.emitted_origin_ptr_path >>
     conj_tac >- simp[] >>
     qexistsl_tac [`[offset_inst;copy_inst;store_inst]`,`sd`] >>
     simp[] >>
     simp[Abbr `offset_inst`,Abbr `copy_inst`,Abbr `store_inst`,
       venomInstTheory.mk_inst_def,venomInstTheory.is_terminator_def]) >>
  `!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn) []
      (OK target,G3,tm)` by
    (gen_tac >>
     qpat_assum `!D. gas_origin_ptr_path _ (s,G,tn) _ _` (qspec_then `D` mp_tac) >>
     qpat_assum `!D. gas_origin_ptr_path _ (zb,G1,tn1) _ _` (qspec_then `D` mp_tac) >>
     qpat_assum `!D. gas_origin_ptr_path _ (v,G2,tn2) _ _` (qspec_then `D` mp_tac) >>
     rpt (pop_assum kall_tac) >>
     metis_tac[fragGasOriginPtrTheory.gas_origin_ptr_path_append,listTheory.APPEND_NIL]) >>
  suspend "joint_path"
QED

Resume slice_memory_tail_full[joint_path]:
  qabbrev_tac `copied = TAKE k (DROP i bs)` >>
  `LENGTH copied = k` by
    (simp[Abbr `copied`,listTheory.LENGTH_TAKE,listTheory.LENGTH_DROP] >> decide_tac) >>
  `mcopy (w2n w+32) (w2n p+i) k za =
      write_memory_with_expansion (w2n w+32) copied za` by
    (mp_tac (Q.INST [`src` |-> `w2n (p:bytes32)`,`start` |-> `i`,`len` |-> `k`,
       `dst` |-> `w2n (w:bytes32)+32`,`s` |-> `za`]
       exprSimSliceDataTheory.slice_mcopy_payload) >>
     simp[Abbr `za`,Abbr `copied`,venomStateTheory.update_var_def]) >>
  `target = mstore (w2n w) (n2w k)
      (write_memory_with_expansion (w2n w+32) copied za)
        with vs_inst_idx := LENGTH sb.cs_current_insts` by
    simp[Abbr `target`,Abbr `zt`,Abbr `zc`] >>
  `target.vs_vars = za.vs_vars /\ target.vs_allocas = v.vs_allocas /\
   target.vs_alloca_next = v.vs_alloca_next /\
   target.vs_current_bb = v.vs_current_bb /\ ~target.vs_halted /\
   target.vs_accounts = s.vs_accounts /\ target.vs_transient = s.vs_transient /\
   target.vs_call_ctx = s.vs_call_ctx /\ target.vs_immutables = s.vs_immutables` by
    (qpat_assum `target = mstore _ _ _ with vs_inst_idx := _` mp_tac >>
     qpat_assum `Abbrev (za = _)` (mp_tac o REWRITE_RULE [markerTheory.Abbrev_def]) >>
     qpat_assum `~v.vs_halted` mp_tac >>
     qpat_assum `v.vs_accounts = s.vs_accounts` mp_tac >>
     qpat_assum `v.vs_transient = s.vs_transient` mp_tac >>
     qpat_assum `v.vs_call_ctx = s.vs_call_ctx` mp_tac >>
     qpat_assum `v.vs_immutables = s.vs_immutables` mp_tac >>
     rpt (pop_assum kall_tac) >> rpt disch_tac >>
     qpat_assum `target = _` SUBST1_TAC >>
     pure_rewrite_tac[venomStateTheory.mstore_def,
       venomStateTheory.write_memory_with_expansion_def,LET_THM] >>
     BETA_TAC >> pure_rewrite_tac[venomStateTheory.venom_state_accfupds] >>
     simp[venomStateTheory.update_var_def]) >>
  `!x. not_fresh_at sa x ==>
     lookup_var x target = lookup_var x s /\ FLOOKUP G3 x = FLOOKUP G x /\
     op_taint tm (Var x) = op_taint tn (Var x)` by
    (qpat_assum `!x. not_fresh_at sd x ==> lookup_var x za = _ /\ _` mp_tac >>
     qpat_assum `!x. not_fresh_at sa x ==> lookup_var x v = _ /\ _` mp_tac >>
     qpat_assum `!x. not_fresh_at sa x ==> not_fresh_at sd x` mp_tac >>
     qpat_assum `target.vs_vars = za.vs_vars` mp_tac >>
     qpat_assum `tm.t_var = tn4.t_var` mp_tac >>
     qpat_assum `tn4.t_var = tn3.t_var` mp_tac >>
     rpt (pop_assum kall_tac) >>
     simp[venomStateTheory.lookup_var_def,ptrDisciplineTheory.op_taint_def] >> metis_tac[]) >>
  `FLOOKUP target.vs_allocas sc.cs_next_id = SOME (w2n w,N) /\
   lookup_var root target = SOME w` by
    (qpat_assum `lookup_var root za = SOME w` mp_tac >>
     qpat_assum `FLOOKUP v.vs_allocas sc.cs_next_id = SOME (w2n w,N)` mp_tac >>
     qpat_assum `target.vs_vars = za.vs_vars` mp_tac >>
     qpat_assum `target.vs_allocas = v.vs_allocas` mp_tac >>
     rpt (pop_assum kall_tac) >> simp[venomStateTheory.lookup_var_def]) >>
  `ptr_covers G3 tm root target N` by
    (irule decoderGhostFramePtrTheory.ptr_covers_frame >>
     qexistsl_tac [`G3`,`za`,`tn3`] >>
     simp[venomStateTheory.lookup_var_def]) >>
  `allocas_from lo target` by
    (qpat_assum `allocas_from lo v` mp_tac >>
     qpat_assum `target.vs_allocas = v.vs_allocas` mp_tac >>
     rpt (pop_assum kall_tac) >> simp[ptrDisciplineTheory.allocas_from_def]) >>
  `lo <= target.vs_alloca_next /\ w2n w+N <= target.vs_alloca_next /\
   s.vs_alloca_next <= target.vs_alloca_next` by decide_tac >>
  `!j. j<k ==> w2n p+i+j NOTIN tn3.t_mem` by
    (qpat_assum `!j. w2n p<=j /\ j<w2n p+LENGTH bs ==> _` mp_tac >>
     qpat_assum `!j. j IN tn2.t_mem <=> _` mp_tac >>
     qpat_assum `tn3.t_mem = tn2.t_mem` mp_tac >>
     qpat_assum `tn1.t_mem = tn.t_mem` mp_tac >>
     qpat_assum `zb.vs_alloca_next = s.vs_alloca_next` mp_tac >>
     qpat_assum `w2n p+LENGTH bs <= s.vs_alloca_next` mp_tac >>
     qpat_assum `i+k<=LENGTH bs` mp_tac >>
     rpt (pop_assum kall_tac) >> rpt strip_tac >>
     `w2n p<=w2n p+i+j /\ w2n p+i+j<w2n p+LENGTH bs /\
       w2n p+i+j<s.vs_alloca_next` by decide_tac >>
     `~(s.vs_alloca_next <= w2n p+i+j)` by decide_tac >> metis_tac[]) >>
  `tn4.t_mem = tn2.t_mem DIFF
      {j | w2n w+32<=j /\ j<w2n w+32+k}` by
    (mp_tac (Q.SPECL [`PG`,`G3`,`tn3`,`za`,`se.cs_next_id`,`Var dst`,
       `Var copy_var`,`cnt`,`p+n2w i`,`w+32w`,`n2w k`]
       fragExecPtrTheory.mcopy_operand_ghost_frame) >>
     (impl_tac >- simp[venomStateTheory.eval_operand_def]) >>
     disch_then (mp_tac o last o CONJUNCTS) >>
     qpat_assum `!j. j<k ==> w2n p+i+j NOTIN tn3.t_mem` mp_tac >>
     qpat_assum `tn3.t_mem = tn2.t_mem` mp_tac >>
     qpat_assum `k < dimword (:256)` mp_tac >>
     qpat_assum `w2n (w+32w) = w2n w+32` mp_tac >>
     qpat_assum `w2n (p+n2w i) = w2n p+i` mp_tac >>
     qpat_assum `Abbrev (tn4 = _)` (mp_tac o REWRITE_RULE [markerTheory.Abbrev_def]) >>
     qpat_assum `Abbrev (copy_inst = _)` (mp_tac o REWRITE_RULE [markerTheory.Abbrev_def]) >>
     qpat_assum `Abbrev (zc = _)` (mp_tac o REWRITE_RULE [markerTheory.Abbrev_def]) >>
     rpt (pop_assum kall_tac) >> rpt disch_tac >>
     gvs[wordsTheory.w2n_n2w,arithmeticTheory.LESS_MOD] >>
     fs[pred_setTheory.EXTENSION] >>
     metis_tac[arithmeticTheory.ADD_ASSOC,arithmeticTheory.ADD_COMM]) >>
  `tm.t_mem = tn4.t_mem DIFF {j | w2n w<=j /\ j<w2n w+32}` by
    (mp_tac (Q.INST [`addr` |-> `Var root`,`value` |-> `cnt`,`s` |-> `zc`,
       `a` |-> `w`,`w` |-> `(n2w k:bytes32)`,`tn` |-> `tn4`,`id` |-> `sf.cs_next_id`]
       wordLoadStorePtrTheory.ifexp_materialize_mstore_taint) >>
     simp[venomStateTheory.eval_operand_def,Abbr `store_inst`,Abbr `tm`,Abbr `zt`]) >>
  `tm.t_mem SUBSET tn2.t_mem /\ tm.t_stor = tn.t_stor /\
   tm.t_trans = tn.t_trans /\ tm.t_imm = tn.t_imm` by
    simp[pred_setTheory.SUBSET_DEF] >>
  `!j. w2n w<=j /\ j<w2n w+32+k ==> j NOTIN tm.t_mem` by
    (qpat_assum `tm.t_mem = _` (fn th => rewrite_tac[th]) >>
     qpat_assum `tn4.t_mem = _` (fn th => rewrite_tac[th]) >>
     simp[] >> rpt strip_tac >> decide_tac) >>
  suspend "memory_frames"
QED

Resume slice_memory_tail_full[memory_frames]:
  `local_ptrs_reserved cenv sd` by
    (irule exprLoweringPropsTheory.local_ptrs_reserved_next_var >>
     qexists_tac `sa` >> simp[]) >>
  `not_local_ptr cenv es.scopes copy_var` by
    (simp[Abbr `copy_var`] >> irule exprLoweringPropsTheory.local_ptrs_reserved_fresh >>
     qexists_tac `sd` >> simp[]) >>
  `!H:(bool # bytes32 # type_value) list # num list.
     stmt_state_rel H ctx func cenv cx es s ==>
     stmt_state_rel H ctx func cenv cx es za` by
    (rpt strip_tac >> simp[Abbr `za`] >>
     irule exprLoweringPropsTheory.stmt_state_rel_update_var >> simp[] >>
     qpat_assum `!H'. stmt_state_rel H' ctx func cenv cx es zb ==> _`
       (qspec_then `H` match_mp_tac) >>
     qpat_assum `!H. stmt_state_rel H ctx func cenv cx es s ==> _`
       (qspec_then `H` match_mp_tac) >> first_assum ACCEPT_TAC) >>
  `stmt_state_rel (storage_trace_horizon es.storage_trace) ctx func cenv cx es v` by
    (qpat_assum `!H'. stmt_state_rel H' ctx func cenv cx es zb ==> _`
       (qspec_then `storage_trace_horizon es.storage_trace` match_mp_tac) >>
     first_assum ACCEPT_TAC) >>
  `local_ptrs_rel func cenv es.scopes v /\ alloca_inv v` by
    (qpat_assum `stmt_state_rel (storage_trace_horizon es.storage_trace)
       ctx func cenv cx es v` mp_tac >> rpt (pop_assum kall_tac) >>
     simp[exprLoweringPropsTheory.stmt_state_rel_def,loweringStateRelDefsTheory.state_rel_def]) >>
  `!name b len. local_region cenv es.scopes za name b len ==>
      regions_disjoint (w2n w) N b len` by
    (rpt strip_tac >>
     qpat_assum `!name b len. local_region cenv es.scopes v name b len ==> _`
       (qspecl_then [`name`,`b`,`len`] match_mp_tac) >>
     qspecl_then [`func`,`cenv`,`es.scopes`,`v`,`sd`,`es.scopes`,`za`,
       `name`,`b`,`len`] match_mp_tac exprSimPropsTheory.local_region_frame >>
     simp[] >> metis_tac[]) >>
  `MEM (mk_inst sc.cs_next_id ALLOCA [Lit (n2w N)]
      [STRING #"%" (toString sc.cs_next_var)]) (fn_insts func)` by
    (qpat_assum `compile_slice_out_buf N sc = _`
       (mp_then Any mp_tac exprSimSliceExtcodeEntryTheory.slice_extcode_out_owner_inst) >> simp[]) >>
  qabbrev_tac `alloc_inst = mk_inst sc.cs_next_id ALLOCA [Lit (n2w N)]
      [STRING #"%" (toString sc.cs_next_var)]` >>
  `!H. valid_horizon cx st0 H es.storage_trace ==>
     stmt_state_rel H ctx func cenv cx es target /\
     storage_well_formed_on cx es (FST H)` by
    (rpt strip_tac >>
     qpat_assum `!H. valid_horizon _ _ H es.storage_trace ==> _`
       (qspec_then `H` mp_tac) >> (impl_tac >- simp[]) >> strip_tac >>
     simp[] >>
     qpat_assum `target = mstore _ _ _ with vs_inst_idx := _` SUBST1_TAC >>
     simp[exprLoweringPropsTheory.stmt_state_rel_inst_idx] >>
     irule bodyPtrBytestringBuiltinsCalldataFrameTheory.allocated_bytes_write_state_rel >>
     simp[] >> qexistsl_tac [`N`,`alloc_inst`] >>
     qpat_assum `!name b len. local_region cenv es.scopes za name b len ==> _` mp_tac >>
     simp[Abbr `alloc_inst`,venomInstTheory.mk_inst_def,Abbr `za`,venomStateTheory.update_var_def]) >>
  `alloca_history func target` by
    (simp[Abbr `target`,NoAsms] >>
     qspecl_then [`[offset_inst;copy_inst;store_inst]`,`sd`,`sb`,`v`,`zt`]
       match_mp_tac bodyFullUnwrapRunTheory.emitted_alloca_history >>
     simp[Abbr `offset_inst`,Abbr `copy_inst`,Abbr `store_inst`,
       venomInstTheory.mk_inst_def,venomInstTheory.is_terminator_def]) >>
  `!name b len. local_region cenv es.scopes s name b len ==>
     local_region cenv es.scopes v name b len` by
    (rpt strip_tac >> irule exprSimPropsTheory.local_region_frame_fwd >>
     qexistsl_tac [`s`,`sa`,`es.scopes`] >> simp[] >> metis_tac[]) >>
  `target.vs_memory = (mstore (w2n w) (n2w k)
      (write_memory_with_expansion (w2n w+32) copied s)).vs_memory` by
    (qpat_assum `target = mstore _ _ _ with vs_inst_idx := _` mp_tac >>
     qpat_assum `Abbrev (za = _)` (mp_tac o REWRITE_RULE [markerTheory.Abbrev_def]) >>
     qpat_assum `v.vs_memory = s.vs_memory` mp_tac >>
     rpt (pop_assum kall_tac) >> rpt disch_tac >>
     qpat_assum `target = _` SUBST1_TAC >>
     pure_rewrite_tac[venomStateTheory.mstore_def,
       venomStateTheory.write_memory_with_expansion_def,LET_THM] >>
     BETA_TAC >> pure_rewrite_tac[venomStateTheory.venom_state_accfupds] >>
     simp[venomStateTheory.update_var_def]) >>
  `!off len. regions_disjoint off len (w2n w) N ==>
     mem_bytes_at off len target.vs_memory = mem_bytes_at off len s.vs_memory` by
    (rpt strip_tac >>
     qpat_assum `target.vs_memory = _` (fn th => once_rewrite_tac[th]) >>
     `n2w k = (n2w (LENGTH copied):bytes32)` by simp[] >>
     pop_assum SUBST1_TAC >> irule exprSimCalldataSliceTheory.bytes_buffer_write_frame >>
     fs[loweringStateRelDefsTheory.regions_disjoint_def] >> decide_tac) >>
  `!name b len. local_region cenv es.scopes s name b len ==>
     mem_bytes_at b len target.vs_memory = mem_bytes_at b len s.vs_memory` by
    (rpt strip_tac >>
     qpat_assum `!off len. regions_disjoint _ _ _ _ ==> _` irule >>
     qpat_assum `!name b len. local_region cenv es.scopes v name b len ==> _`
       (qspecl_then [`name`,`b`,`len`] mp_tac) >>
     (impl_tac >- metis_tac[]) >>
     simp[loweringStateRelDefsTheory.regions_disjoint_def] >> decide_tac) >>
  `!j. j<s.vs_alloca_next /\ j IN tm.t_mem ==> j IN tn.t_mem` by
    (qpat_assum `tm.t_mem SUBSET tn2.t_mem` mp_tac >>
     qpat_assum `!j. j IN tn2.t_mem <=> _` mp_tac >>
     qpat_assum `tn1.t_mem = tn.t_mem` mp_tac >>
     qpat_assum `zb.vs_alloca_next = s.vs_alloca_next` mp_tac >>
     rpt (pop_assum kall_tac) >> simp[pred_setTheory.SUBSET_DEF] >>
     rpt strip_tac >> `~(s.vs_alloca_next <= j)` by decide_tac >> metis_tac[]) >>
  `!name b len. local_region cenv es.scopes s name b len ==>
     mem_bytes_at b len target.vs_memory = mem_bytes_at b len s.vs_memory /\
     (!j. b<=j /\ j<b+len /\ j IN tm.t_mem ==> j IN tn.t_mem)` by
    (rpt gen_tac >> disch_tac >> conj_tac >- metis_tac[] >> rpt strip_tac >>
     qpat_assum `!j. j<s.vs_alloca_next /\ _ ==> _` irule >> simp[] >>
     `b+len<=s.vs_alloca_next` by
       (drule_all bodyMemoryDefsTheory.body_local_region_frontier >> simp[]) >> decide_tac) >>
  suspend "semantic_frames"
QED

Resume slice_memory_tail_full[semantic_frames]:
  `!aid entry. FLOOKUP s.vs_allocas aid = SOME entry ==>
      FLOOKUP target.vs_allocas aid = SOME entry` by
    (qpat_assum `!aid e. FLOOKUP zb.vs_allocas aid = SOME e ==> _` mp_tac >>
     qpat_assum `zb.vs_allocas = s.vs_allocas` mp_tac >>
     qpat_assum `target.vs_allocas = v.vs_allocas` mp_tac >>
     rpt (pop_assum kall_tac) >> metis_tac[]) >>
  `!aid b len. aid < sa.cs_next_id /\ FLOOKUP s.vs_allocas aid = SOME (b,len) ==>
      regions_disjoint (w2n w) N b len` by
    (rpt strip_tac >>
     qpat_assum `!aid b len. aid < sc.cs_next_id /\ _ ==> _`
       (qspecl_then [`aid`,`b`,`len`] match_mp_tac) >> simp[] >> decide_tac) >>
  `locals_kept cenv es es s target` by
    (irule exprSimPropsTheory.locals_kept_regions >> first_assum ACCEPT_TAC) >>
  `wb_frame cenv es es sa s target` by
    (pure_rewrite_tac[loweringPostsTheory.wb_frame_def] >> rpt conj_tac
     >- (rpt strip_tac >>
         qpat_assum `!x. not_fresh_at sa x ==> lookup_var x target = _ /\ _`
           (qspec_then `x` mp_tac) >> simp[])
     >- first_assum ACCEPT_TAC
     >- (rpt strip_tac >>
         qpat_assum `!off len. regions_disjoint _ _ _ _ ==> _` irule >>
         qpat_assum `!aid b len. aid < sa.cs_next_id /\ _ ==> _`
           (qspecl_then [`aid`,`off`,`sz`] mp_tac) >>
         simp[loweringStateRelDefsTheory.regions_disjoint_def] >> decide_tac) >>
     first_assum ACCEPT_TAC) >>
  `!name off len. local_region cenv es.scopes s name off len ==>
     regions_disjoint (w2n w) N off len` by
    (rpt strip_tac >>
     qpat_assum `!name b len. local_region cenv es.scopes v name b len ==> _`
       (qspecl_then [`name`,`off`,`len`] match_mp_tac) >>
     qpat_assum `!name b len. local_region cenv es.scopes s name b len ==>
       local_region cenv es.scopes v name b len` irule >> simp[]) >>
  `sa.cs_next_id <= sc.cs_next_id` by
    (qpat_assum `cs_extends sa sc` mp_tac >>
     simp[compileEnvTheory.cs_extends_def]) >>
  `pure_frame cenv func es sa s target` by
    (`32 + LENGTH copied <= N` by (simp[] >> decide_tac) >>
     qpat_assum `!aid entry. FLOOKUP s.vs_allocas aid = SOME entry ==> _` mp_tac >>
     qpat_assum `MEM alloc_inst (fn_insts func)` mp_tac >>
     qpat_assum `Abbrev (alloc_inst = _)` (mp_tac o REWRITE_RULE [markerTheory.Abbrev_def]) >>
     qpat_assum `FLOOKUP target.vs_allocas sc.cs_next_id = SOME (w2n w,N)` mp_tac >>
     qpat_assum `sa.cs_next_id <= sc.cs_next_id` mp_tac >>
     qpat_assum `!name off len. local_region cenv es.scopes s name off len ==>
       regions_disjoint (w2n w) N off len` mp_tac >>
     qpat_assum `target.vs_memory = _` mp_tac >>
     qpat_assum `LENGTH copied = k` mp_tac >>
     qpat_assum `32 + LENGTH copied <= N` mp_tac >>
     rpt (pop_assum kall_tac) >> rpt disch_tac >>
     irule exprSimSliceDataTheory.slice_allocated_bytes_pure_frame >>
     conj_tac >- first_assum ACCEPT_TAC >>
     qexistsl_tac [`copied`,`alloc_inst`,`w2n (w:bytes32)`,`N`] >>
     fs[venomInstTheory.mk_inst_def] >> first_assum ACCEPT_TAC) >>
  `lo <= w2n w` by
    (qpat_assum `allocas_from lo target` mp_tac >>
     qpat_assum `FLOOKUP target.vs_allocas sc.cs_next_id = SOME (w2n w,N)` mp_tac >>
     rpt (pop_assum kall_tac) >>
     simp[ptrDisciplineTheory.allocas_from_def] >> metis_tac[]) >>
  `mem_bytes_at 0 lo target.vs_memory = mem_bytes_at 0 lo s.vs_memory /\
   (!j. j<lo /\ j IN tm.t_mem ==> j IN tn.t_mem)` by
    (conj_tac >-
       (qpat_assum `!off len. regions_disjoint _ _ _ _ ==> _` irule >>
        simp[loweringStateRelDefsTheory.regions_disjoint_def]) >>
     rpt strip_tac >> qpat_assum `!j. j<s.vs_alloca_next /\ _ ==> _` irule >>
     simp[] >> decide_tac) >>
  `!aid off sz. FLOOKUP s.vs_allocas aid = SOME (off,sz) ==>
     off+sz <= s.vs_alloca_next` by
    (qpat_assum `alloca_inv s` mp_tac >> rpt (pop_assum kall_tac) >>
     simp[venomMemDefsTheory.alloca_inv_def,venomMemDefsTheory.alloca_next_valid_def] >>
     strip_tac >> first_assum ACCEPT_TAC) >>
  `ghost_kept_at lo cenv es sa G tn s G3 tm` by
    (qpat_assum `!x. not_fresh_at sa x ==> lookup_var x target = _ /\ _` mp_tac >>
     qpat_assum `!j. j<s.vs_alloca_next /\ _ ==> _` mp_tac >>
     qpat_assum `!name b len. local_region cenv es.scopes s name b len ==>
       mem_bytes_at b len target.vs_memory = _ /\ _` mp_tac >>
     qpat_assum `!j. j<lo /\ _ ==> _` mp_tac >>
     qpat_assum `!aid off sz. FLOOKUP s.vs_allocas aid = SOME (off,sz) ==> _` mp_tac >>
     rpt (pop_assum kall_tac) >> rpt disch_tac >>
     pure_rewrite_tac[bodyPtrDefsTheory.ghost_kept_at_def] >> rpt conj_tac
     >- metis_tac[]
     >- (rpt strip_tac >>
         qpat_assum `!j. j<s.vs_alloca_next /\ _ ==> _` irule >> simp[] >>
         `off+sz<=s.vs_alloca_next` by metis_tac[] >> decide_tac)
     >- metis_tac[] >> first_assum ACCEPT_TAC) >>
  `!H. valid_horizon cx st0 H es.storage_trace ==>
     ghost_inv_at (DF H) lo d cenv cx es G3 tm target` by
    (rpt strip_tac >>
     qpat_assum `!H. valid_horizon _ _ H es.storage_trace ==>
       stmt_state_rel H ctx func cenv cx es s /\ _`
       (qspec_then `H` mp_tac) >> (impl_tac >- simp[]) >> strip_tac >>
     `local_ptrs_rel func cenv es.scopes s` by
       (qpat_assum `stmt_state_rel H ctx func cenv cx es s` mp_tac >>
        rpt (pop_assum kall_tac) >> rpt strip_tac >>
        fs[exprLoweringPropsTheory.stmt_state_rel_def,loweringStateRelDefsTheory.state_rel_def]) >>
     `stor_taint_ok_at (DF H) tm target` by
       (qpat_assum `ghost_inv_at (DF H) lo d cenv cx es G tn s`
         (mp_tac o el 4 o CONJUNCTS o REWRITE_RULE[bodyPtrDefsTheory.ghost_inv_at_def]) >>
        simp[bodyPtrDefsTheory.stor_taint_ok_at_def]) >>
     drule_at (Pat `ghost_inv_at _ _ _ _ _ _ _ _ _`)
       (Q.INST [`fn` |-> `func`,`sa` |-> `sa`,`s'` |-> `target`,
         `es'` |-> `es`,`HG` |-> `G3`,`tm` |-> `tm`]
         bodyPtrBytestringBuiltinsWindowGhostTheory.ghost_inv_at_local_window_transport) >>
     disch_then (mp_tac o SPEC_ALL) >>
     (impl_tac >-
       (rpt conj_tac
        >- first_assum ACCEPT_TAC
        >- first_assum ACCEPT_TAC
        >- first_assum ACCEPT_TAC
        >- first_assum ACCEPT_TAC
        >- (qpat_assum `!x. not_fresh_at sa x ==> lookup_var x target = _ /\ _` mp_tac >>
            rpt (pop_assum kall_tac) >> metis_tac[])
        >- (qpat_assum `!x. not_fresh_at sa x ==> lookup_var x target = _ /\ _` mp_tac >>
            rpt (pop_assum kall_tac) >> metis_tac[])
        >- first_assum ACCEPT_TAC
        >- REFL_TAC
        >- first_assum ACCEPT_TAC
        >- first_assum ACCEPT_TAC
        >- first_assum ACCEPT_TAC
        >- first_assum ACCEPT_TAC
        >> first_assum ACCEPT_TAC)) >>
     disch_then ACCEPT_TAC) >>
  suspend "typed_output"
QED

Resume slice_memory_tail_full[typed_output]:
  `N = 32+32*word_size n /\ n < dimword (:256) /\ ~is_word_type a` by
    (qpat_assum `result_shape` mp_tac >>
     qpat_assum `N = type_memory_bytes cenv a` mp_tac >>
     qpat_assum `32+n<=N` mp_tac >> qpat_assum `N<dimword (:256)` mp_tac >>
     qunabbrev_tac `result_shape` >> rpt (pop_assum kall_tac) >>
     rw[] >> simp[compileEnvTheory.type_memory_bytes_def,compileEnvTheory.is_word_type_def,
       vfmConstantsTheory.word_size_def] >> decide_tac) >>
  `mem_bytes_at (w2n p) (LENGTH bs) za.vs_memory = bs` by
    simp[Abbr `za`,venomStateTheory.update_var_def] >>
  `?vt. evaluate_type (get_tenv cx) a = SOME vt /\
     type_memory_size vt = N /\ val_wf vt result /\
     val_footprint vt result = 32+k /\ val_store_size vt result <= N /\
     val_in_memory vt result (w2n w) target.vs_memory` by
    (qpat_assum `result_shape` mp_tac >> qunabbrev_tac `result_shape` >>
     disch_then (DISJ_CASES_THEN STRIP_ASSUME_TAC)
     >- (qexists_tac `BaseTV (BytesT (Dynamic n))` >>
         `val_in_memory (BaseTV (BytesT (Dynamic n)))
            (BytesV (TAKE k (DROP i bs))) (w2n w) target.vs_memory` by
           (simp[Abbr `target`,Abbr `zt`,Abbr `zc`,NoAsms] >>
            match_mp_tac (SIMP_RULE (srw_ss()) [arithmeticTheory.ADD_COMM]
              (Q.INST [`src` |-> `w2n (p:bytes32)`,`start` |-> `i`,
                 `len` |-> `k`,`bs` |-> `bs`,`output_base` |-> `w2n (w:bytes32)`,
                 `s` |-> `za`,`bound` |-> `n`]
                (Q.INST [`p` |-> `output_base`]
                  exprSimSliceDataTheory.slice_copy_store_encoding))) >> simp[]) >>
         qpat_x_assum `val_in_memory (BaseTV (BytesT (Dynamic n))) _ _ target.vs_memory` mp_tac >>
         qspec_then `k` (qspec_then `n` mp_tac) exprSimPropsTheory.word_size_monotone >>
         simp[vyperValueTheory.evaluate_type_def,vyperValueTheory.type_slot_size_def,
           valueEncodingTheory.type_memory_size_def,valueEncodingDefsTheory.val_wf_def,
           loweringPostsTheory.val_footprint_def,exprSimPropsTheory.val_store_size_def,
           listTheory.LENGTH_TAKE,listTheory.LENGTH_DROP] >> decide_tac) >>
     qexists_tac `BaseTV (StringT n)` >>
     `LENGTH (TAKE k (DROP i str)) = k` by
       (irule listTheory.LENGTH_TAKE >> simp[listTheory.LENGTH_DROP] >>
        qpat_assum `i+k <= LENGTH bs` mp_tac >>
        qpat_assum `bs = MAP _ str` mp_tac >>
        rpt (pop_assum kall_tac) >> simp[] >> decide_tac) >>
     `val_in_memory (BaseTV (StringT n))
        (StringV (TAKE k (DROP i str))) (w2n w) target.vs_memory` by
       (simp[Abbr `target`,Abbr `zt`,Abbr `zc`,NoAsms] >>
        match_mp_tac (SIMP_RULE (srw_ss()) [arithmeticTheory.ADD_COMM]
          (Q.INST [`src` |-> `w2n (p:bytes32)`,`start` |-> `i`,
             `len` |-> `k`,`text` |-> `str`,`output_base` |-> `w2n (w:bytes32)`,
             `s` |-> `za`,`bound` |-> `n`]
            (Q.INST [`p` |-> `output_base`]
              exprSimSliceDataTheory.slice_copy_store_string_encoding))) >>
        qpat_assum `mem_bytes_at (w2n p) (LENGTH bs) za.vs_memory = bs` mp_tac >>
        qpat_assum `i+k <= LENGTH bs` mp_tac >>
        qpat_assum `bs = MAP _ str` mp_tac >>
        rpt (pop_assum kall_tac) >> simp[]) >>
     qpat_x_assum `val_in_memory (BaseTV (StringT n)) _ _ target.vs_memory` mp_tac >>
     qspec_then `k` (qspec_then `n` mp_tac) exprSimPropsTheory.word_size_monotone >>
     simp[vyperValueTheory.evaluate_type_def,vyperValueTheory.type_slot_size_def,
       valueEncodingTheory.type_memory_size_def,valueEncodingDefsTheory.val_wf_def,
       loweringPostsTheory.val_footprint_def,exprSimPropsTheory.val_store_size_def] >> decide_tac) >>
  suspend "typed_pointer"
QED

Resume slice_memory_tail_full[typed_pointer]:
  `ptr_mem_ok cx a result (Var root) G3 tm target` by
    (mp_tac (Q.INST [`ty` |-> `a`,`vt` |-> `vt`,`v` |-> `result`,
       `b` |-> `(w:bytes32)`,`root` |-> `root`,`s` |-> `target`,
       `G` |-> `G3`,`tn` |-> `tm`,`capacity` |-> `N`]
       reasonCodeResourcesPtrTheory.clean_memory_representation_ptr) >>
     (impl_tac >- (simp[] >> rpt strip_tac >>
       qpat_assum `!j. w2n w<=j /\ j<w2n w+32+k ==> _` irule >> simp[])) >>
     disch_then ACCEPT_TAC) >>
  `ptr_vv_ok cx a (Value result)
      (LocatedValue a (mk_ptr (Var root) LocMemory)) es G3 tm target` by
    (qpat_assum `ptr_mem_ok cx a result (Var root) G3 tm target` mp_tac >>
     qpat_assum `ptr_covers G3 tm root target N` mp_tac >>
     rpt (pop_assum kall_tac) >> rpt disch_tac >>
     qspecl_then [`cx`,`a`,`Value result`,`a`,`mk_ptr (Var root) LocMemory`,
       `es`,`G3`,`tm`,`target`,`result`] match_mp_tac
       bodyPtrAttributeFieldsTheory.ptr_vv_ok_memory >>
     fs[bodyPtrDefsTheory.ptr_covers_def,contextTheory.mk_ptr_def,
       vyperStateTheory.read_result_def,vyperStateTheory.return_def]) >>
  `ptr_buf_ok cenv (Builtin a (Slice n) args) (Var root) G3 target` by
    (qpat_assum `ptr_covers G3 tm root target N` mp_tac >>
     qpat_assum `N = type_memory_bytes cenv a` mp_tac >>
     rpt (pop_assum kall_tac) >>
     rw[bodyPtrDefsTheory.ptr_covers_def,bodyPtrDefsTheory.ptr_buf_ok_def,
       venomStateTheory.eval_operand_def,exprLoweringTheory.lowered_value_type_def,
       vyperASTTheory.expr_type_def] >> gvs[] >>
     qexistsl_tac [`b`,`sz'`] >> simp[]) >>
  `vv_store_bound cx a a es (Value result)
      (LocatedValue a (mk_ptr (Var root) LocMemory)) target` by
    (qpat_assum `evaluate_type (get_tenv cx) a = SOME vt` mp_tac >>
     qpat_assum `type_memory_size vt = N` mp_tac >>
     qpat_assum `w2n w+N <= target.vs_alloca_next` mp_tac >>
     qpat_assum `val_store_size vt result <= N` mp_tac >>
     qpat_assum `lookup_var root target = SOME w` mp_tac >>
     rpt (pop_assum kall_tac) >>
     rw[exprSimMemDefsTheory.vv_store_bound_def,contextTheory.mk_ptr_def,
       vyperStateTheory.read_result_def,vyperStateTheory.return_def,
       venomStateTheory.eval_operand_def] >> gvs[] >> decide_tac) >>
  `sc.cs_next_id < sb.cs_next_id` by
    (qpat_assum `compile_slice_out_buf N sc = _` mp_tac >>
     qpat_assum `emit_op ADD _ sd = _` mp_tac >>
     qpat_assum `emit_void MCOPY _ se = _` mp_tac >>
     qpat_assum `emit_void MSTORE _ sf = _` mp_tac >>
     rpt (pop_assum kall_tac) >> rpt disch_tac >>
     qpat_assum `emit_op ADD _ sd = _`
       (mp_then Any strip_assume_tac emitHelperPropsTheory.emitted_insts_emit_op) >>
     qpat_assum `emit_void MCOPY _ se = _`
       (mp_then Any strip_assume_tac emitHelperPropsTheory.emitted_insts_emit_void) >>
     qpat_assum `emit_void MSTORE _ sf = _`
       (mp_then Any strip_assume_tac emitHelperPropsTheory.emitted_insts_emit_void) >>
     qspecl_then [`N`,`sc`] mp_tac
       exprLoweringPropsTheory.ci_mono_compile_slice_out_buf >>
     simp[exprLoweringPropsTheory.ci_mono_def]) >>
  `!name b len. local_region cenv es.scopes target name b len ==>
     regions_disjoint (w2n w) N b len` by
    (rpt strip_tac >>
     qpat_assum `!name b len. local_region cenv es.scopes za name b len ==> _`
       (qspecl_then [`name`,`b`,`len`] match_mp_tac) >>
     qspecl_then [`func`,`cenv`,`es.scopes`,`za`,`sd`,`es.scopes`,`target`,
       `name`,`b`,`len`] match_mp_tac exprSimPropsTheory.local_region_frame >>
     simp[venomStateTheory.lookup_var_def] >>
     `local_ptrs_rel func cenv es.scopes za` by
       (`stmt_state_rel (storage_trace_horizon es.storage_trace)
           ctx func cenv cx es za` by
          (qpat_assum `!H. stmt_state_rel H ctx func cenv cx es s ==> _`
             (qspec_then `storage_trace_horizon es.storage_trace` match_mp_tac) >>
           first_assum ACCEPT_TAC) >>
        qpat_assum `stmt_state_rel (storage_trace_horizon es.storage_trace)
           ctx func cenv cx es za` mp_tac >>
        rpt (pop_assum kall_tac) >>
        simp[exprLoweringPropsTheory.stmt_state_rel_def,loweringStateRelDefsTheory.state_rel_def]) >>
     simp[]) >>
  suspend "normal_post"
QED

Resume slice_memory_tail_full[normal_post]:
  `!H. valid_horizon cx st0 H es.storage_trace ==>
     vv_post H ctx func cenv cx (Builtin a (Slice n) args)
       es sa sb s es (Value result)
       (LocatedValue a (mk_ptr (Var root) LocMemory)) target` by
    (rpt strip_tac >>
     qpat_assum `!H. valid_horizon _ _ H es.storage_trace ==>
       stmt_state_rel H ctx func cenv cx es target /\ _`
       (qspec_then `H` mp_tac) >>
     (impl_tac >- first_assum ACCEPT_TAC) >> strip_tac >>
     `32+k <= N` by decide_tac >>
     qpat_assum `~is_word_type a` mp_tac >>
     qpat_assum `evaluate_type (get_tenv cx) a = SOME vt` mp_tac >>
     qpat_assum `val_wf vt result` mp_tac >>
     qpat_assum `val_in_memory vt result (w2n w) target.vs_memory` mp_tac >>
     qpat_assum `stmt_state_rel H ctx func cenv cx es target` mp_tac >>
     qpat_assum `storage_well_formed_on cx es (FST H)` mp_tac >>
     qpat_assum `lookup_var root target = SOME w` mp_tac >>
     qpat_assum `FLOOKUP target.vs_allocas sc.cs_next_id = SOME (w2n w,N)` mp_tac >>
     qpat_assum `sa.cs_next_id <= sc.cs_next_id` mp_tac >>
     qpat_assum `sc.cs_next_id < sb.cs_next_id` mp_tac >>
     qpat_assum `val_footprint vt result = 32+k` mp_tac >>
     qpat_assum `32+k <= N` mp_tac >>
     qpat_assum `!name b len. local_region cenv es.scopes target name b len ==> _` mp_tac >>
     qpat_assum `wb_frame cenv es es sa s target` mp_tac >>
     qpat_assum `pure_frame cenv func es sa s target` mp_tac >>
     rpt (pop_assum kall_tac) >> rpt disch_tac >>
     irule (SIMP_RULE (srw_ss()) [vyperASTTheory.expr_type_def]
       (Q.INST [`e` |-> `Builtin a (Slice n) args`,`aid` |-> `sc.cs_next_id`,
        `b` |-> `w2n (w:bytes32)`,`sz` |-> `N`,`w` |-> `(w:bytes32)`,`tv` |-> `vt`]
       exprSimHashTheory.vv_post_allocated_memory_intro)) >>
     simp[vyperASTTheory.expr_type_def,loweringPostsTheory.post_value_type_def,
       contextTheory.mk_ptr_def,venomStateTheory.eval_operand_def] >>
     qexistsl_tac [`N`,`sc`] >> simp[] >>
     qx_genl_tac [`name`,`lb`,`lsz`] >> strip_tac >>
     qpat_assum `!name b len. local_region cenv es.scopes target name b len ==> _`
       (qspecl_then [`name`,`lb`,`lsz`] mp_tac) >>
     simp[loweringStateRelDefsTheory.regions_disjoint_def]) >>
  `target.vs_inst_idx = LENGTH sb.cs_current_insts` by
    simp[Abbr `target`,NoAsms] >>
  `target.vs_current_bb = sb.cs_current_bb` by
    (qpat_assum `target.vs_current_bb = v.vs_current_bb` mp_tac >>
     qpat_assum `v.vs_current_bb = sd.cs_current_bb` mp_tac >>
     qpat_assum `sb.cs_current_bb = sd.cs_current_bb` mp_tac >>
     rpt (pop_assum kall_tac) >> simp[]) >>
  qpat_assum `~s.vs_halted` mp_tac >>
  qpat_assum `!tail. source _ = _` mp_tac >>
  qpat_assum `i+k <= LENGTH bs` mp_tac >>
  qpat_assum `es with gas_obs := [] = es` mp_tac >>
  qpat_assum `!D. gas_origin_ptr_path _ (s,G,tn) [] (OK target,G3,tm)` mp_tac >>
  qpat_assum `!H. valid_horizon _ _ H es.storage_trace ==> vv_post H _ _ _ _ _ _ _ _ _ _ _ _ _` mp_tac >>
  qpat_assum `vv_store_bound cx a a es (Value result) (LocatedValue a (mk_ptr (Var root) LocMemory)) target` mp_tac >>
  qpat_assum `target.vs_current_bb = sb.cs_current_bb` mp_tac >>
  qpat_assum `target.vs_inst_idx = LENGTH sb.cs_current_insts` mp_tac >>
  qpat_assum `alloca_history func target` mp_tac >>
  qpat_assum `s.vs_alloca_next <= target.vs_alloca_next` mp_tac >>
  qpat_assum `!H. valid_horizon _ _ H es.storage_trace ==> ghost_inv_at _ _ _ _ _ _ _ _ target` mp_tac >>
  qpat_assum `ptr_vv_ok cx a (Value result) (LocatedValue a (mk_ptr (Var root) LocMemory)) es G3 tm target` mp_tac >>
  qpat_assum `ptr_buf_ok cenv (Builtin a (Slice n) args) (Var root) G3 target` mp_tac >>
  qpat_assum `ghost_kept_at lo cenv es sa G tn s G3 tm` mp_tac >>
  qpat_assum `out = Var root` mp_tac >>
  rpt (pop_assum kall_tac) >> rpt disch_tac >>
  irule gas_outcome_full_pure >> reverse conj_tac >- simp[] >>
  qexistsl_tac [`G3`,`es`,`INL (Value result)`,`target`,`tm`] >>
  conj_tac >- (qpat_assum `!tail. source _ = _` mp_tac >> simp[]) >> simp[]
QED

Finalise slice_memory_tail_full
