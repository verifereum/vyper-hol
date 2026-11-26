(* Ordinary linked Slice after the source and both scalar operands have landed. *)
Theory bodySliceWindowMods
Ancestors
  bodySliceBoundsExitMods bodySliceBoundsLandingMods bodySliceOutputLandingMods
  bodySliceSourceOffsetMods bodySliceCopyStoreMods bodySliceWritePathMods
  bodySliceWindowPhysicalMods bodySliceWindowGhostMods bodySliceWindowValueMods
  bodyFullPredsMods gasOutcomeFullPostMods exprSimSliceData
  bodyPtrBytestringBuiltinsSlice bodyPtrBytestringBuiltinsBuffer
  bodyFullHashKeccakFixed stateRelProj freshWrites localPtrsProps fragExecMem
  instMemFrontier memSafeRun loweringStateRelDefs compileAllocaProvenance
  bodyFullShadowBodyInv compileEnv fragExec
Libs horizonTypeLib

Theorem slice_window_suffix_mods:
  compile_slice_data limit (Var src) start cnt N sa = (out,sb) /\
  fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
  local_ptrs_reserved cenv sa /\
  (ctx_has_dalloca ctx ==> allocas_below_fmp s /\
    s.vs_alloca_next + pending_alloca_size func s <= w2n s.vs_initial_fmp) /\
  eval_operand limit s = SOME (n2w (LENGTH bs)) /\
  lookup_var src s = SOME p /\ ptr_covers G tn src s (LENGTH bs) /\
  op_prov G limit = NONE /\ op_taint tn limit = {} /\
  eval_operand start s = SOME (n2w i) /\ eval_operand cnt s = SOME (n2w k) /\
  op_prov G start = NONE /\ op_taint tn start = {} /\
  op_prov G cnt = NONE /\ op_taint tn cnt = {} /\
  (!op x. MEM op [limit;Var src;start;cnt] /\ op = Var x ==>
     not_fresh_at sa x) /\
  (!l. limit <> Label l /\ start <> Label l /\ cnt <> Label l) /\
  mem_bytes_at (w2n p) (LENGTH bs) s.vs_memory = bs /\
  (!j. w2n p <= j /\ j < w2n p + LENGTH bs ==> j NOTIN tn.t_mem) /\
  w2n p + LENGTH bs < dimword (:256) /\ w2n p + LENGTH bs <= s.vs_alloca_next /\
  i < dimword (:256) /\ k < dimword (:256) /\ (i+k <= LENGTH bs ==> k <= n) /\
  ((a = BaseT (BytesT (Dynamic n)) /\ result = BytesV (TAKE k (DROP i bs))) \/
   (?str. a = BaseT (StringT n) /\ bs = MAP (n2w o ORD) str /\
      result = StringV (TAKE k (DROP i str)))) /\
  e = Builtin a (Slice n) args /\
  N = type_memory_bytes cenv a /\ 32+n <= N /\ N < dimword (:256) /\
  storage_trace_domain cx st0 es.storage_trace /\
  (!H. valid_horizon cx st0 H es.storage_trace ==>
    stmt_state_rel H ctx func cenv cx es s /\
    immutable_frame_mods func cenv cx es s /\
    storage_well_formed_on cx es (FST H) /\
    ghost_inv_at_mods (DF H) lo d cenv cx es G tn s) /\
  es.gas_obs = [] /\ alloca_history func s /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\ s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!tail. source (es with gas_obs := tail) =
    ((if i+k <= LENGTH bs then INL (Value result)
      else INR (Error (RuntimeError "evaluate_slice range"))), es with gas_obs := tail)) ==>
  gas_outcome_full_mods (DF,lo,explicit,ctx,func,PG) mods cx st0 source (es,s,G,tn)
    (\H res ee HG tm t.
      res = INL (Value result) /\
      vv_post_mods H ctx func cenv cx e es sa sb s ee (Value result)
        (LocatedValue a (mk_ptr out LocMemory)) t /\
      vv_store_bound cx a a ee (Value result) (LocatedValue a (mk_ptr out LocMemory)) t /\
      t.vs_current_bb = sb.cs_current_bb /\ t.vs_inst_idx = LENGTH sb.cs_current_insts /\
      alloca_history func t /\ s.vs_alloca_next <= t.vs_alloca_next /\
      ghost_inv_at_mods (DF H) lo d cenv cx ee HG tm t /\
      ptr_vv_ok cx a (Value result) (LocatedValue a (mk_ptr out LocMemory)) ee HG tm t /\
      ptr_buf_ok cenv e out HG t /\ ghost_kept_at lo cenv es sa G tn s HG tm /\
      (ctx_has_dalloca ctx ==> allocas_below_fmp t))
    (\H res ee gt r. expr_exit res r /\ halt_exit H cx ee res r /\
      (ctx_has_dalloca ctx ==> !u. r = Halt u ==> allocas_below_fmp u))
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `valid_horizon cx st0 (storage_trace_horizon es.storage_trace) es.storage_trace` by
    fs[vyperStorageFootprintTheory.storage_trace_domain_def] >>
  qpat_assum `!H. valid_horizon _ _ H _ ==> _` (drule_then strip_assume_tac) >>
  drule_then strip_assume_tac stmt_state_rel_local_ptrs_alloca >>
  `allocas_from lo s /\ lo <= s.vs_alloca_next` by
    (qpat_assum `ghost_inv_at_mods _ _ _ _ _ _ _ _ _` mp_tac >>
     simp_tac bool_ss [ghost_inv_at_mods_def] >>
     disch_then (map_every assume_tac o CONJUNCTS) >> simp[]) >>
  `ctx_has_dalloca ctx ==> allocas_below_fmp s` by
    (drule_then ACCEPT_TAC stmt_state_rel_allocas_below_fmp) >>
  `LENGTH bs < dimword (:256)` by decide_tac >>
  drule slice_data_decompose >>
  disch_then (qx_choosel_then [`sc`,`sd`,`se`,`sf`,`data`,`copy_src`] strip_assume_tac) >>
  `cs_extends sa sc` by (drule slice_bounds_extends >> simp[]) >>
  `cs_extends sc sd` by
    (drule compile_slice_out_buf_compiler_parts >> metis_tac[cs_extends_trans]) >>
  `cs_extends sd se /\ cs_extends se sf /\ cs_extends sf sb` by
    (qpat_assum `emit_op ADD _ sd = _` mp_tac >>
     qpat_assum `emit_void MCOPY _ se = _` mp_tac >>
     qpat_assum `emit_void MSTORE _ sf = _` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >> metis_tac[cs_appends_emit_helpers,cs_appends_def]) >>
  `cs_extends sd sb` by metis_tac[cs_extends_trans] >>
  `fn_has_code sa sc func /\ fn_has_code sc sd func /\ fn_has_code sd sb func` by
    (qpat_assum `fn_has_code sa sb func` mp_tac >>
     qpat_assum `cs_extends sa sc` mp_tac >> qpat_assum `cs_extends sc sd` mp_tac >>
     qpat_assum `cs_extends sd sb` mp_tac >> POP_ASSUM_LIST (K ALL_TAC) >>
     metis_tac[fn_has_code_split,cs_extends_trans]) >>
  `!op. MEM op [start;cnt;limit] ==> op_prov G op = NONE /\ op_taint tn op = {} /\
     (!x. op = Var x ==> not_fresh_at sa x)` by
    (map_every (fn pat => qpat_assum pat mp_tac)
       [`op_prov G start = _`,`op_prov G cnt = _`,`op_prov G limit = _`,
        `op_taint tn start = _`,`op_taint tn cnt = _`,`op_taint tn limit = _`,
        `!op x. MEM op _ /\ _ ==> _`] >>
     POP_ASSUM_LIST (K ALL_TAC) >> simp_tac bool_ss [listTheory.MEM] >> metis_tac[]) >>
  `not_fresh_at sa src` by
    (qpat_assum `!op x. MEM op _ /\ _ ==> _` irule >> simp[]) >>
  reverse (Cases_on `i+k <= LENGTH bs`) >- suspend "abort" >>
  suspend "land"
QED

Resume slice_window_suffix_mods[abort]:
  irule slice_bounds_exit_mods >> reverse conj_tac
  >- (simp[] >> qexistsl_tac [`LENGTH bs`,`cnt`,`i`,`k`,`limit`,`sa`,`sc`,`start`] >>
      qpat_assum `!op. MEM op [start;cnt;limit] ==> _` mp_tac >> simp[] >>
      POP_ASSUM_LIST (K ALL_TAC) >> metis_tac[]) >>
  qpat_assum `!tail. source _ = _` mp_tac >> simp[]
QED

Resume slice_window_suffix_mods[land]:
  mp_tac (horizonTypeLib.at_horizon_named "H" slice_bounds_landing_mods |>
    INST_TYPE [Type.alpha |-> ``:word8``]) >>
  (impl_tac >- (rpt conj_tac >> (first_assum ACCEPT_TAC ORELSE simp[]))) >>
  disch_then (qx_choosel_then [`zb`,`G1`,`tn1`] strip_assume_tac) >>
  `stmt_state_rel (storage_trace_horizon es.storage_trace) ctx func cenv cx es zb` by
    (qpat_assum `!es H. stmt_state_rel H _ _ _ _ es s ==> _` (drule_then ACCEPT_TAC)) >>
  mp_tac (horizonTypeLib.at_horizon_named "H" slice_output_landing_mods |> Q.INST
    [`G` |-> `G1`, `tn` |-> `tn1`, `H` |-> `storage_trace_horizon es.storage_trace`]) >>
  (impl_tac >- (rpt conj_tac >> (first_assum ACCEPT_TAC ORELSE decide_tac))) >>
  disch_then (qx_choosel_then [`root`,`dst`,`w`,`v`,`G2`,`tn2`] strip_assume_tac) >>
  suspend "offset"
QED

Resume slice_window_suffix_mods[offset]:
  `sa.cs_next_var <= sd.cs_next_var /\ sc.cs_next_id < sb.cs_next_id` by
    (qspecl_then [`N`,`sc`] mp_tac exprLoweringPropsTheory.ci_mono_compile_slice_out_buf >>
     qpat_assum `emit_void MSTORE _ sf = _` (mp_tac o MATCH_MP emitHelperPropsTheory.emitted_insts_emit_void) >>
     qpat_assum `emit_void MCOPY _ se = _` (mp_tac o MATCH_MP emitHelperPropsTheory.emitted_insts_emit_void) >>
     qpat_assum `emit_op ADD _ sd = _` (mp_tac o MATCH_MP emitHelperPropsTheory.emitted_insts_emit_op) >>
     simp[exprLoweringPropsTheory.ci_mono_def] >> decide_tac) >>
  `!x. not_fresh_at sa x ==> not_fresh_at sd x` by
    (rpt strip_tac >> irule not_fresh_at_mono >> qexists_tac `sa` >> simp[]) >>
  `!x. not_fresh_at sa x ==> lookup_var x v = lookup_var x s /\
    FLOOKUP G2 x = FLOOKUP G x /\ op_taint tn2 (Var x) = op_taint tn (Var x)` by
    (qpat_assum `!x. not_fresh_at sc x ==> lookup_var x v = _ /\ _` mp_tac >>
     qpat_assum `!x. not_fresh_at sa x ==> lookup_var x zb = _ /\ _` mp_tac >>
     qpat_assum `!x. not_fresh_at sa x ==> not_fresh_at sc x` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >> metis_tac[]) >>
  `v.vs_memory = s.vs_memory /\ v.vs_labels = s.vs_labels /\
   v.vs_call_ctx = s.vs_call_ctx /\ v.vs_accounts = s.vs_accounts /\
   v.vs_transient = s.vs_transient /\ v.vs_immutables = s.vs_immutables /\
   v.vs_data_section = s.vs_data_section` by
    (qpat_assum `v with <|vs_vars := _;vs_allocas := _;
       vs_alloca_next := _;vs_inst_idx := _|> = zb` mp_tac >>
     qpat_assum `zb = _` (pure_once_rewrite_tac o single) >>
     simp[venomStateTheory.venom_state_component_equality]) >>
  `!x. (start = Var x \/ cnt = Var x) ==> not_fresh_at sa x` by
    (rpt strip_tac >> qpat_assum `!op x. MEM op _ /\ _ ==> _` irule >> simp[] >>
     metis_tac[]) >>
  `eval_operand start v = SOME (n2w i) /\ op_taint tn2 start = {} /\
   eval_operand cnt v = SOME (n2w k) /\ op_taint tn2 cnt = {}` by
    (qpat_assum `!x. not_fresh_at sa x ==> lookup_var x v = _ /\ _`
       (mp_then Any (fn th => map_every (fn opnd => qspec_then opnd mp_tac th) [`start`,`cnt`])
         bodyPtrBytestringBuiltinsExternalSliceTheory.reserved_operand_ghost_frame) >>
     `!x. start = Var x ==> not_fresh_at sa x` by metis_tac[] >>
     `!x. cnt = Var x ==> not_fresh_at sa x` by metis_tac[] >> simp[]) >>
  `lookup_var src v = SOME p /\ ptr_covers G2 tn2 src v (LENGTH bs)` by
    (qpat_assum `!x. not_fresh_at sa x ==> lookup_var x v = _ /\ _`
       (qspec_then `src` strip_assume_tac) >>
     simp[] >> irule decoderGhostFramePtrTheory.ptr_covers_frame >>
     qexistsl_tac [`G`,`s`,`tn`] >> simp[]) >>
  `!x. cnt = Var x ==> not_fresh_at sd x` by
    (rpt strip_tac >> qpat_assum `!x. not_fresh_at sa x ==> not_fresh_at sd x` irule >>
     qpat_assum `!op x. MEM op _ /\ _ ==> _` irule >> simp[]) >>
  `32+k <= N /\ 32 <= N /\ lo <= v.vs_alloca_next` by decide_tac >>
  mp_tac (INST_TYPE [Type.alpha |-> ``:word8``] slice_source_offset_mods) >>
  (impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)) >>
  disch_then (qx_choosel_then [`copy_var`,`offset_inst`,`za`,`G3`,`tn3`] strip_assume_tac) >>
  suspend "writes"
QED

Resume slice_window_suffix_mods[writes]:
  qpat_assum `out = Var root` SUBST_ALL_TAC >>
  qpat_assum `data = Var dst` SUBST_ALL_TAC >>
  qpat_assum `copy_src = Var copy_var` SUBST_ALL_TAC >>
  `za.vs_memory = s.vs_memory /\ za.vs_alloca_next = v.vs_alloca_next` by
    (qpat_assum `za = _` SUBST1_TAC >> simp[venomStateTheory.update_var_def]) >>
  `mem_bytes_at (w2n p) (LENGTH bs) za.vs_memory = bs /\
   w2n p+i+k <= za.vs_alloca_next /\ w2n w+N <= za.vs_alloca_next` by
    (conj_tac
     >- (qpat_assum `za.vs_memory = _` (pure_once_rewrite_tac o single) >> first_assum ACCEPT_TAC) >>
     decide_tac) >>
  `!j. j < k ==> w2n p+i+j NOTIN tn3.t_mem` by
    (gen_tac >> disch_tac >>
     `w2n p <= w2n p+i+j /\ w2n p+i+j < w2n p + LENGTH bs /\
      w2n p+i+j < zb.vs_alloca_next` by decide_tac >>
     simp[arithmeticTheory.NOT_LESS_EQUAL]) >>
  mp_tac slice_copy_store_mods >>
  (impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)) >>
  simp_tac bool_ss [LET_THM] >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  qabbrev_tac `copy_inst = mk_inst se.cs_next_id MCOPY [Var dst;Var copy_var;cnt] []` >>
  qabbrev_tac `store_inst = mk_inst sf.cs_next_id MSTORE [Var root;cnt] []` >>
  qabbrev_tac `zc = mcopy (w2n w+32) (w2n p+i) k za` >>
  qabbrev_tac `zt = mstore (w2n w) (n2w k) zc` >>
  qabbrev_tac `tn4 = step_taint copy_inst za zc tn3` >>
  qabbrev_tac `tm = step_taint store_inst zc zt tn4` >>
  qabbrev_tac `target = zt with vs_inst_idx := LENGTH sb.cs_current_insts` >>
  suspend "path"
QED

Resume slice_window_suffix_mods[path]:
  `stmt_state_rel (storage_trace_horizon es.storage_trace) ctx func cenv cx es v` by
    (qpat_assum `!H. stmt_state_rel H _ _ _ _ _ zb ==> _` (drule_then ACCEPT_TAC)) >>
  `alloca_inv v` by
    (qpat_assum `stmt_state_rel _ _ _ _ _ _ v`
       (mp_then Any strip_assume_tac stmt_state_rel_local_ptrs_alloca) >> simp[]) >>
  `zt.vs_current_bb = sd.cs_current_bb` by
    (qpat_assum `zt = mstore _ _ (write_memory_with_expansion _ _ za)` SUBST1_TAC >>
     qpat_assum `za = _` SUBST1_TAC >>
     pure_rewrite_tac[venomStateTheory.mstore_def,venomStateTheory.write_memory_with_expansion_def,
       venomStateTheory.update_var_def,LET_THM] >> BETA_TAC >>
     pure_rewrite_tac[venomStateTheory.venom_state_accfupds] >> first_assum ACCEPT_TAC) >>
  `sb.cs_current_bb = sd.cs_current_bb /\
   sb.cs_current_insts = sd.cs_current_insts ++ [offset_inst;copy_inst;store_inst]` by
    (qpat_assum `emit_void MCOPY _ se = _`
       (mp_then Any strip_assume_tac exprLoweringPropsTheory.emit_void_same_blocks) >>
     qpat_assum `emit_void MSTORE _ sf = _`
       (mp_then Any strip_assume_tac exprLoweringPropsTheory.emit_void_same_blocks) >>
     fs[exprLoweringPropsTheory.same_blocks_def,listTheory.APPEND_ASSOC]) >>
  `inst_mem_below_frontier offset_inst v /\ !st. inst_dload_in_section offset_inst st` by
    (qpat_assum `offset_inst = _` SUBST1_TAC >>
     simp[venomInstTheory.mk_inst_def,memSafeRunTheory.inst_dload_in_section_def] >>
     irule instMemFrontierTheory.below_frontier_no_ranges >> simp[venomInstTheory.mk_inst_def]) >>
  `run_inst_seq_mem_ok [offset_inst;copy_inst;store_inst] v` by
    (map_every (fn pat => qpat_assum pat mp_tac)
       [`step_inst_base offset_inst v = OK za`,`step_inst_base copy_inst za = OK zc`,
        `inst_mem_below_frontier offset_inst v`,`inst_mem_below_frontier copy_inst za`,
        `inst_mem_below_frontier store_inst zc`,
        `!st. inst_dload_in_section offset_inst st`,
        `!st. inst_dload_in_section copy_inst st /\ inst_dload_in_section store_inst st`] >>
     POP_ASSUM_LIST (K ALL_TAC) >>
     disch_then (fn th => map_every (fn st => qspec_then st strip_assume_tac th) [`za`,`zc`]) >>
     disch_then (qspec_then `v` assume_tac) >> rpt disch_tac >>
     simp[run_inst_seq_mem_ok_cons,run_inst_seq_mem_ok_last]) >>
  `!pre j post u. [offset_inst;copy_inst;store_inst] = pre ++ j::post /\
      run_inst_seq pre v = OK u ==> dalloca_no_wrap j u` by
    (rpt strip_tac >> irule dalloca_no_wrap_non_dalloca >>
     qpat_assum `[offset_inst;copy_inst;store_inst] = pre ++ j::post`
       (mp_tac o Q.AP_TERM `MEM j`) >>
     simp_tac bool_ss [listTheory.MEM_APPEND,listTheory.MEM] >>
     disch_then (REPEAT_TCL DISJ_CASES_THEN SUBST1_TAC) >>
     simp[Abbr `copy_inst`,Abbr `store_inst`,venomInstTheory.mk_inst_def]) >>
  mp_tac (INST_TYPE [Type.alpha |-> ``:256``] slice_write_path_mods) >>
  qpat_assum `copy_var = _` (fn def =>
    qpat_assum `offset_inst = _` (pure_rewrite_tac o single o SYM o REWRITE_RULE[def])) >>
  qpat_assum `Abbrev (copy_inst = _)` (pure_rewrite_tac o single o SYM o REWRITE_RULE[markerTheory.Abbrev_def]) >>
  qpat_assum `Abbrev (store_inst = _)` (pure_rewrite_tac o single o SYM o REWRITE_RULE[markerTheory.Abbrev_def]) >>
  (impl_tac >- (rpt conj_tac >> (first_assum ACCEPT_TAC ORELSE
     simp[Abbr `target`,Abbr `tn4`,Abbr `tm`,venomInstTheory.is_terminator_def]))) >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  suspend "physical"
QED

Resume slice_window_suffix_mods[physical]:
  `!H:(bool # bytes32 # type_value) list # num list.
      stmt_state_rel H ctx func cenv cx es s ==> stmt_state_rel H ctx func cenv cx es v` by
    (gen_tac >> disch_tac >>
     qpat_assum `!es H. stmt_state_rel H _ _ _ _ es s ==> _` (drule_then assume_tac) >>
     qpat_assum `!H. stmt_state_rel H _ _ _ _ _ zb ==> _` (drule_then ACCEPT_TAC)) >>
  `!j. j < s.vs_alloca_next /\ j IN tm.t_mem ==> j IN tn.t_mem` by
    (gen_tac >> strip_tac >>
     `~(zb.vs_alloca_next <= j)` by decide_tac >>
     qpat_x_assum `j IN tm.t_mem` mp_tac >>
     qpat_assum `tm.t_mem = _` (once_rewrite_tac o single) >>
     qpat_assum `tn3.t_mem = _` (once_rewrite_tac o single) >>
     simp[pred_setTheory.IN_DIFF]) >>
  qabbrev_tac `bytes = TAKE k (DROP i bs)` >>
  `LENGTH bytes = k` by
    (simp[Abbr `bytes`,listTheory.LENGTH_TAKE_EQ,listTheory.LENGTH_DROP] >> decide_tac) >>
  `target = mstore (w2n w) (n2w k) (write_memory_with_expansion (w2n w+32) bytes za)
      with vs_inst_idx := LENGTH sb.cs_current_insts` by
    (qpat_assum `zt = mstore _ _ (write_memory_with_expansion _ _ _)`
       (fn th => simp_tac bool_ss [Abbr `target`, th])) >>
  qabbrev_tac `inst = mk_inst sc.cs_next_id ALLOCA [Lit (n2w N)]
      [STRING #"%" (toString sc.cs_next_var)]` >>
  `MEM inst (fn_insts func)` by
    (drule compile_slice_out_buf_compiler_parts >> strip_tac >>
     `fn_has_code sc sm func` by (drule_all fn_has_code_split >> simp[]) >>
     irule fn_has_code_current_member >> qexistsl_tac [`sc`,`sm`] >>
     simp[] >> drule loweringHaltTheory.compile_alloc_buffer_insts >>
     simp[Abbr `inst`,listTheory.MEM_APPEND]) >>
  `inst.inst_opcode = ALLOCA /\ inst.inst_id = sc.cs_next_id` by
    simp[Abbr `inst`,venomInstTheory.mk_inst_def] >>
  `!x. not_fresh_at sa x ==> lookup_var x v = lookup_var x s` by
    (gen_tac >> disch_tac >>
     qpat_assum `!x. not_fresh_at sa x ==> lookup_var x v = _ /\ _`
       (drule_then strip_assume_tac) >> first_assum ACCEPT_TAC) >>
  mp_tac (horizonTypeLib.at_horizon_named "H0" slice_window_physical_frame_mods |> Q.INST
    [`p` |-> `w2n (w:bytes32)`, `H0` |-> `storage_trace_horizon es.storage_trace`,
     `j` |-> `LENGTH sb.cs_current_insts`] |>
    Q.INST [`value` |-> `(p:bytes32) + n2w i`]) >>
  (impl_tac >-
    (rpt conj_tac >> (first_assum ACCEPT_TAC ORELSE
      (qpat_assum `copy_var = _` (pure_once_rewrite_tac o single o SYM) >> first_assum ACCEPT_TAC)
       ORELSE
      (map_every (fn pat => qpat_assum pat (pure_once_rewrite_tac o single))
        [`inst.inst_id = _`, `s.vs_allocas = _`, `s.vs_alloca_next = zb.vs_alloca_next`, `LENGTH bytes = _`] >>
       (first_assum ACCEPT_TAC ORELSE decide_tac))))) >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  suspend "post"
QED

Resume slice_window_suffix_mods[post]:
  `target.vs_vars = za.vs_vars /\ target.vs_call_ctx = s.vs_call_ctx /\
    target.vs_accounts = s.vs_accounts /\ target.vs_transient = s.vs_transient /\
    target.vs_immutables = s.vs_immutables /\
    target.vs_memory = (mstore (w2n w) (n2w k)
      (write_memory_with_expansion (w2n w+32) bytes za)).vs_memory` by
    (qpat_assum `target = mstore _ _ _ with vs_inst_idx := _` SUBST1_TAC >>
     qpat_assum `za = _` SUBST1_TAC >>
     simp_tac bool_ss [venomStateTheory.mstore_def,venomStateTheory.write_memory_with_expansion_def,
       venomStateTheory.update_var_def,LET_THM,venomStateTheory.venom_state_accfupds] >>
     rpt conj_tac >> first_assum ACCEPT_TAC) >>
  `!x. not_fresh_at sa x ==> lookup_var x target = lookup_var x s /\
       FLOOKUP G3 x = FLOOKUP G x /\ op_taint tm (Var x) = op_taint tn (Var x)` by
    (gen_tac >> disch_tac >>
     qpat_assum `!x. not_fresh_at sa x ==> not_fresh_at sd x` (drule_then assume_tac) >>
     qpat_assum `!x. not_fresh_at sd x ==> lookup_var x za = _ /\ _` (drule_then strip_assume_tac) >>
     qpat_assum `!x. not_fresh_at sa x ==> lookup_var x v = _ /\ _` (drule_then strip_assume_tac) >>
     map_every (fn pat => qpat_assum pat mp_tac)
       [`lookup_var x za = _`,`lookup_var x v = _`,`target.vs_vars = _`,
        `FLOOKUP G3 x = _`,`FLOOKUP G2 x = _`,
        `op_taint tn3 (Var x) = _`,`op_taint tn2 (Var x) = _`,
        `tm.t_var = _`,`tn4.t_var = _`] >>
     POP_ASSUM_LIST (K ALL_TAC) >>
     simp[venomStateTheory.lookup_var_def,ptrDisciplineTheory.op_taint_def]) >>
  `lookup_var root target = SOME w /\ ptr_covers G3 tm root target N` by
    (conj_tac
     >- (qpat_assum `target.vs_vars = _` mp_tac >> qpat_assum `lookup_var root za = _` mp_tac >>
         simp_tac bool_ss [venomStateTheory.lookup_var_def] >> rw[]) >>
     irule decoderGhostFramePtrTheory.ptr_covers_frame >> qexistsl_tac [`G3`,`zt`,`tm`] >>
     simp_tac bool_ss [Abbr `target`,venomStateTheory.lookup_var_def,venomStateTheory.venom_state_accfupds] >>
     first_assum ACCEPT_TAC) >>
  `!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn) [] (OK target,G3,tm)` by
    (gen_tac >> map_every (fn pat => qpat_assum pat (qspec_then `D` mp_tac))
      [`!D. gas_origin_ptr_path _ (s,G,tn) _ (OK zb,G1,tn1)`,
       `!D. gas_origin_ptr_path _ (zb,G1,tn1) _ (OK v,G2,tn2)`,
       `!D. gas_origin_ptr_path _ (v,G2,tn2) _ (OK target,G3,tm)`] >>
     POP_ASSUM_LIST (K ALL_TAC) >>
     metis_tac[fragGasOriginPtrTheory.gas_origin_ptr_path_append,listTheory.APPEND_NIL]) >>
  irule gas_outcome_full_mods_pure >> reverse conj_tac >- first_assum ACCEPT_TAC >>
  qexistsl_tac [`G3`,`es`,`INL (Value result)`,`target`,`tm`] >>
  conj_tac >- (qpat_assum `!tail. source _ = _` mp_tac >> simp[]) >>
  `es with gas_obs := [] = es` by
    (qpat_assum `es.gas_obs = []` (SUBST1_TAC o SYM) >> simp[]) >>
  qpat_assum `es with gas_obs := [] = es` (pure_once_rewrite_tac o single) >>
  BETA_TAC >> gen_tac >> disch_tac >> suspend "horizon"
QED

Resume slice_window_suffix_mods[horizon]:
  qpat_assum `!H. valid_horizon _ _ H _ ==> _` (drule_then strip_assume_tac) >>
  qpat_assum `!H. stmt_state_rel H _ _ _ _ _ s ==> stmt_state_rel H _ _ _ _ _ target`
    (drule_then assume_tac) >>
  mp_tac (slice_window_ghost_frame_mods |> Q.INST [`D` |-> `DF (H:(bool # bytes32 # type_value) list # num list)`]) >>
  (impl_tac >- (rpt conj_tac >> (first_assum ACCEPT_TAC ORELSE simp[]))) >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  mp_tac (horizonTypeLib.at_horizon_named "H" slice_window_value_mods |>
    INST_TYPE [Type.alpha |-> ``:256``] |>
    Q.INST [`out` |-> `Var root`, `aid` |-> `sc.cs_next_id`]) >>
  qpat_assum `Abbrev (bytes = _)`
    (pure_rewrite_tac o single o SYM o REWRITE_RULE[markerTheory.Abbrev_def]) >>
  (impl_tac >- (rpt conj_tac >> (first_assum ACCEPT_TAC ORELSE simp[]))) >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `ctx_has_dalloca ctx ==> allocas_below_fmp target` by
    (qpat_assum `stmt_state_rel H _ _ _ _ _ target`
       (mp_then Any ACCEPT_TAC stmt_state_rel_allocas_below_fmp)) >>
  simp[]
QED

Finalise slice_window_suffix_mods
