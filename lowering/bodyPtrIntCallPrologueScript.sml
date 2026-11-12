Theory bodyPtrIntCallPrologue
Ancestors
  bodyPtrIntCallCapture bodyPtrIntCallMaterialize bodyPtrIntCallScratch
  intCallCallee bodyPtrIntCallEntryContracts exprSimProps finite_map list
  compileEnv loweringPosts valueEncodingDefs venomExecSemantics venomState
  loweringStateRelDefs fragExec exprLoweringProps ptrDiscipline context
  bodyPtrDefs dftGasInvOracleFrame bodyPtrPrecompileBuiltinsAllocationFrame
  venomInst entrySinkExtraction

Theorem internal_args_rel_footprints[local]:
  internal_args_rel ce params env argbase args frontier mem ==>
  !name entry off sz.
    FLOOKUP env name = SOME entry /\
    FLOOKUP ce.ce_vars name = SOME (MemLoc off sz) ==>
    val_footprint entry.type entry.value <= sz
Proof
  simp[internal_args_rel_def] >> rpt strip_tac >>
  `MEM name (MAP FST params)` by metis_tac[flookup_thm] >>
  gvs[MEM_MAP, MEM_EL] >>
  qpat_x_assum `!i. i < LENGTH params ==> _` drule >> strip_tac >>
  gvs[] >> drule val_footprint_le >> decide_tac
QED

Theorem prologue_prefix_alloca_room[local]:
  compile_internal_prologue cenv params has_rb ret_type st0 =
    ((cenv2,return_pc),st1) /\
  fn_has_code st0 st1 func /\ st0.cs_current_insts = [] /\
  isPREFIX stop.cs_current_insts st1.cs_current_insts /\
  run_inst_seq (emitted_insts start stop) s = OK t /\
  alloca_room ctx func s ==>
  alloca_room ctx func t
Proof
  strip_tac >> irule run_inst_seq_alloca_room >>
  goal_assum (drule_at Any) >> simp[] >>
  qexists_tac `emitted_insts start stop` >> simp[] >>
  drule compile_internal_prologue_shape >> strip_tac >>
  qpat_x_assum `fn_has_code _ _ _` mp_tac >>
  qpat_x_assum `isPREFIX _ _` mp_tac >>
  qpat_x_assum `EVERY (\i. i.inst_opcode <> INVOKE /\ _) _` mp_tac >>
  qpat_x_assum `st1.cs_current_insts = st0.cs_current_insts ++ _` mp_tac >>
  qpat_x_assum `st0.cs_current_insts = []` mp_tac >>
  POP_ASSUM_LIST (K all_tac) >>
  simp[fn_has_code_def, rich_listTheory.IS_PREFIX_APPEND, EVERY_MEM,
    emitted_insts_def] >> rpt strip_tac >>
  `MEM i stop.cs_current_insts` by
    metis_tac[rich_listTheory.MEM_DROP_IMP]
  >- (irule lookup_block_fn_insts >> goal_assum (drule_at Any) >>
      simp[] >> metis_tac[MEM_APPEND]) >>
  metis_tac[MEM_APPEND]
QED

Theorem prologue_scratch_prepare[local]:
  (case ret_type of NONE => comp_return ()
   | SOME ty => if cenv.ce_returns_count > 0 then
       do compile_alloc_buffer (type_memory_bytes cenv ty); comp_return () od
     else comp_return ()) sm = ((),st1) /\
  fn_has_code st0 st1 func /\
  isPREFIX sm.cs_current_insts st1.cs_current_insts /\
  alloca_room ctx func s /\
  (!aid. aid IN FDOM s.vs_allocas ==> aid < sm.cs_next_id) ==>
  ?enabled n buf.
    (if enabled then compile_alloc_buffer n sm else (buf,sm)) = (buf,st1) /\
    (enabled ==> s.vs_alloca_next + w2n (n2w n : 256 word) < dimword (:256))
Proof
  strip_tac >> Cases_on `ret_type` >-
    (qexistsl_tac [`F`,`0`,`ARB`] >> fs[comp_return_def]) >>
  Cases_on `cenv.ce_returns_count > 0` >-
    (qpat_x_assum `_ sm = ((),st1)` mp_tac >>
     simp[comp_bind_def, comp_return_def, comp_ignore_bind_def] >>
     pairarg_tac >> strip_tac >>
     qpat_x_assum `_ (compile_alloc_buffer _ sm) = ((),st1)` mp_tac >>
     simp[] >> disch_then SUBST_ALL_TAC >>
     rename1 `compile_alloc_buffer n sm = (scratchbuf,st1)` >>
     qexistsl_tac [`T`,`n`,`scratchbuf`] >> simp[] >>
     drule emitted_allocation_singleton >> strip_tac >>
     `MEM (mk_inst sm.cs_next_id ALLOCA [Lit (n2w n)]
       [STRING #"%" (toString sm.cs_next_var)]) (fn_insts func)` by
       (qpat_assum `fn_has_code _ _ _` mp_tac >>
        qpat_assum `emitted_insts sm st1 = _` mp_tac >>
        qpat_assum `isPREFIX _ _` mp_tac >>
        POP_ASSUM_LIST (K all_tac) >>
        gvs[fn_has_code_def, rich_listTheory.IS_PREFIX_APPEND,
          emitted_insts_def, rich_listTheory.DROP_LENGTH_APPEND] >>
        rpt strip_tac >> gvs[rich_listTheory.DROP_LENGTH_APPEND] >>
        metis_tac[lookup_block_fn_insts, MEM_APPEND, MEM]) >>
     `sm.cs_next_id NOTIN FDOM s.vs_allocas` by
       metis_tac[prim_recTheory.LESS_REFL] >>
     drule_at (Pos (el 2)) alloca_room_fresh >>
     simp[mk_inst_def] >> disch_then (qspecl_then [`s`,`ctx`] mp_tac) >> simp[]) >>
  qexistsl_tac [`F`,`0`,`ARB`] >> fs[comp_return_def]
QED

Theorem intcall_suffix_path[local]:
  run_inst_seq code s = OK t /\
  (!k. inst_seq_ptr D lo ctx func PG G tn code
    (s with vs_inst_idx := k) G' tn') /\
  ~s.vs_halted /\ lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
  isPREFIX code (DROP k bb.bb_instructions) /\
  EVERY (\i. i.inst_opcode <> INVOKE /\
    ~is_terminator i.inst_opcode /\ i.inst_opcode <> GAS) code ==>
  gas_path_ptr D lo ctx func PG G tn (s with vs_inst_idx := k) 0 G' tn'
    (OK (t with vs_inst_idx := k + LENGTH code))
Proof
  strip_tac >>
  `EVERY (\i. ~is_terminator i.inst_opcode) code /\
   EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode) code /\
   FILTER (\i. i.inst_opcode = GAS) code = []` by
    (fs[EVERY_MEM, FILTER_EQ_NIL] >> metis_tac[]) >>
  mp_tac (Q.INST [`fn` |-> `func`, `s` |-> `s with vs_inst_idx := k`,
    `t` |-> `t with vs_inst_idx := k`] (SPEC_ALL
      fragGasSeqPtrTheory.run_inst_seq_gas_path_ptr)) >>
  simp[run_inst_seq_inst_idx, instIdxIndepTheory.exec_result_map_def]
QED

Theorem intcall_path_suffix_join[local]:
  gas_path_ptr D lo ctx func PG G0 tn0 s0 0 G tn
    (OK (s with vs_inst_idx := LENGTH prefix)) /\
  run_inst_seq code s = OK t /\
  (!k. inst_seq_ptr D lo ctx func PG G tn code
    (s with vs_inst_idx := k) G' tn') /\
  ~s.vs_halted /\ lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
  isPREFIX (prefix ++ code) bb.bb_instructions /\
  EVERY (\i. i.inst_opcode <> INVOKE /\
    ~is_terminator i.inst_opcode /\ i.inst_opcode <> GAS) code ==>
  gas_path_ptr D lo ctx func PG G0 tn0 s0 0 G' tn'
    (OK (t with vs_inst_idx := LENGTH (prefix ++ code)))
Proof
  strip_tac >>
  `isPREFIX code (DROP (LENGTH prefix) bb.bb_instructions)` by
    (qpat_x_assum `isPREFIX _ _` mp_tac >>
     simp[rich_listTheory.IS_PREFIX_APPEND] >> strip_tac >>
     metis_tac[GSYM APPEND_ASSOC, rich_listTheory.DROP_LENGTH_APPEND]) >>
  drule_all intcall_suffix_path >>
  simp[] >> strip_tac >>
  `0 + 0 = (0:num)` by simp[] >>
  metis_tac[fragGasPathPtrTheory.gas_path_ptr_then]
QED

Theorem compile_internal_prologue_entry_ptr:
  !cenv params has_rb ret_type st0 cenv2 return_pc st1 func ctx args caller
   s0 f cx vs env PG tn d.
    compile_internal_prologue cenv params has_rb ret_type st0 =
      ((cenv2,return_pc),st1) /\
    fn_has_code st0 st1 func /\ fn_inst_ids_distinct func /\
    st0.cs_current_insts = [] /\
    st0.cs_current_bb = (HD func.fn_blocks).bb_label /\
    setup_callee func args caller = SOME s0 /\ ~cenv.ce_is_ctor /\
    state_rel f cenv cx (vs with scopes := []) caller /\
    internal_immutable_regions cenv cx vs caller.vs_alloca_next /\
    internal_args_rel cenv params env (if has_rb then 1 else 0) args
      caller.vs_alloca_next caller.vs_memory /\
    caller.vs_alloca_next + internal_stack_size cenv params < dimword (:256) /\
    alloca_room ctx func s0 /\ fmp_room ctx func s0 /\
    cenv.ce_imm_alloca = NONE /\ ~ctx_has_dalloca ctx /\
    LENGTH PG = LENGTH s0.vs_params /\
    intcall_entry_memory cenv params env (if has_rb then 1 else 0)
      PG (tn with t_var := FEMPTY) s0 /\
    intcall_entry_return cenv has_rb d PG s0 /\ stor_taint_ok cx tn s0 ==>
    ?s1 G1 tn1.
      ~s1.vs_halted /\ s1.vs_current_bb = st1.cs_current_bb /\
      s1.vs_inst_idx = LENGTH st1.cs_current_insts /\
      stmt_state_rel ctx func (cenv2 with ce_alloca_locals := T) cx
        (vs with scopes := [env]) s1 /\
      fresh_vars_wrt st1 s1 /\
      (?x. return_pc = Var x /\ not_fresh_at st1 x /\
           lookup_var x s1 = SOME s0.vs_return_pc_token) /\
      (has_rb ==> ?rb. not_fresh_at st1 rb /\ lookup_var rb s1 = SOME (HD args) /\
        !off sz. cenv.ce_return_buf = SOME (MemLoc off sz) ==>
          cenv2.ce_return_buf = SOME (PtrVar (Var rb) sz)) /\
      (!fuel r. run_from fuel ctx func s1 = r /\ (!e. r <> Error e) ==>
        ?fuel'. run_from fuel' ctx func s0 = r) /\
      ghost_inv d (cenv2 with ce_alloca_locals := T) cx
        (vs with scopes := [env]) G1 tn1 s1 /\
      gas_path_ptr (cx_dead cx) 0 ctx func PG FEMPTY (tn with t_var := FEMPTY)
        s0 0 G1 tn1 (OK s1)
Proof
  rpt gen_tac >> strip_tac >>
  drule internal_prologue_stages >> strip_tac >>
  drule_all internal_prologue_stage_shapes >> strip_tac >>
  `?rbop. (has_rb ==> emit_op PARAM [Lit 0w] st0 = (rbop,stb) /\ rb = SOME rbop) /\
     (~has_rb ==> stb = st0)` by
    (qpat_x_assum `(if has_rb then _ else _) st0 = _` mp_tac >>
     Cases_on `has_rb` >> simp[comp_bind_def, comp_return_def] >>
     pairarg_tac >> simp[] >> metis_tac[]) >>
  `s0.vs_allocas = FEMPTY /\ s0.vs_vars = FEMPTY /\ s0.vs_params = args /\
   s0.vs_memory = caller.vs_memory /\ s0.vs_alloca_next = caller.vs_alloca_next /\
   ~s0.vs_halted /\ s0.vs_inst_idx = 0 /\
   s0.vs_current_bb = st0.cs_current_bb` by
    (qpat_x_assum `setup_callee _ _ _ = _` mp_tac >>
     simp[setup_callee_def, AllCaseEqs()] >> strip_tac >> gvs[]) >>
  `fresh_vars_wrt st0 s0 /\ allocas_from 0 s0` by
    simp[fresh_vars_wrt_def, allocas_from_def] >>
  `?bb. lookup_block s0.vs_current_bb func.fn_blocks = SOME bb /\
     isPREFIX (emitted_insts st0 sc) (DROP s0.vs_inst_idx bb.bb_instructions)` by
    (fs[fn_has_code_def, emitted_insts_def] >>
     metis_tac[rich_listTheory.IS_PREFIX_TRANS]) >>
  `((if has_rb then 1 else 0) + LENGTH params <= LENGTH s0.vs_params) /\
     LENGTH s0.vs_params < dimword (:256)` by fs[internal_args_rel_def] >>
  `has_rb ==> emit_op PARAM [Lit 0w] st0 = (rbop,stb)` by metis_tac[] >>
  drule_all (SRULE [] (Q.INST [`idx` |-> `if has_rb then 1 else 0`]
    intcall_capture_path_ptr)) >>
  disch_then (qspecl_then [`tn with t_var := FEMPTY`,`FEMPTY`,`cx_dead cx`] mp_tac) >>
  strip_tac >>
  `ce.ce_vars = cenv.ce_vars /\ t.vs_alloca_next = s0.vs_alloca_next /\
   t.vs_memory = s0.vs_memory /\ un.t_mem = tn.t_mem` by
    (conj_tac >- (qpat_assum `ce = _` (fn th => rewrite_tac[th]) >> simp[]) >>
     conj_tac >- (qpat_assum `t = _` (fn th => once_rewrite_tac[th]) >> simp[]) >>
     conj_tac >- (qpat_assum `t = _` (fn th => once_rewrite_tac[th]) >> simp[]) >>
     qpat_assum `un = _` (fn th => once_rewrite_tac[th]) >> simp[]) >>
  `intcall_pending env ce caps H un t` by
    (`internal_args_rel cenv params env (if has_rb then 1 else 0)
        s0.vs_params s0.vs_alloca_next s0.vs_memory` by metis_tac[] >>
     drule internal_args_rel_footprints >> strip_tac >>
     irule intcall_entry_captured_pending >>
     goal_assum (drule_at Any) >> simp[] >>
     goal_assum (drule_at Any) >> simp[] >>
     goal_assum (drule_at Any) >> simp[] >> rpt strip_tac >>
     qpat_x_assum `!i. i < LENGTH params ==> ?p. _` drule >>
     simp[arithmeticTheory.ADD_COMM]) >>
  `return_buf_ptr d ce H un t` by
    (irule intcall_entry_captured_return >>
     goal_assum (drule_at Any) >> simp[] >>
     strip_tac >>
     qpat_x_assum `intcall_entry_return _ _ _ _ _` mp_tac >>
     simp[intcall_entry_return_def] >> rpt strip_tac >>
     qpat_x_assum `t = _` kall_tac >> qpat_x_assum `un = _` kall_tac >>
     qpat_assum `ce = _` (fn th => rewrite_tac[th]) >>
     simp[] >> metis_tac[]) >>
  `ALL_DISTINCT (MAP FST caps)` by fs[internal_args_rel_def] >>
  `EVERY (\c. ?p. SND (SND c) = Var p /\ not_fresh_at sc p) caps` by
    (simp[EVERY_EL] >> rpt strip_tac >>
     qpat_x_assum `!i. i < LENGTH params ==> ?p. _`
       (qspec_then `n` mp_tac) >>
     `n < LENGTH params` by metis_tac[] >> simp[] >>
     strip_tac >> rename1 `EL n caps = (FST (EL n params),SND (EL n params),Var captured_var)` >>
     qexists_tac `captured_var` >> simp[] >>
     `captured_var IN FDOM t.vs_vars` by
       (qpat_x_assum `lookup_var captured_var t = SOME _` mp_tac >>
        simp[lookup_var_def, flookup_thm]) >>
     simp[not_fresh_at_def] >> rpt strip_tac >>
     qpat_x_assum `fresh_vars_wrt sc t` mp_tac >>
     simp[fresh_vars_wrt_def] >>
     qexists_tac `n'` >> simp[] >>
     qpat_x_assum `captured_var = _` (fn th => rewrite_tac[GSYM th]) >> simp[]) >>
  `!ps. internal_stack_size ce ps = internal_stack_size cenv ps` by
    (Induct >- simp[internal_stack_size_def] >>
     PairCases >> simp[internal_stack_size_def]) >>
  `!aid. aid IN FDOM t.vs_allocas ==> aid < sc.cs_next_id` by
    (qpat_assum `t = _` (fn th => once_rewrite_tac[th]) >> simp[]) >>
  `intcall_completed FEMPTY ce H un t` by simp[intcall_completed_def] >>
  `t.vs_alloca_next + internal_stack_size ce
     (MAP (\c. (FST c,FST (SND c))) caps) < dimword (:256)` by metis_tac[] >>
  drule_all (SRULE [] (Q.INST [`done` |-> `FEMPTY`]
    (SPEC_ALL intcall_materialize_path_ptr))) >>
  disch_then (qspecl_then [`func`,`PG`,`cx_dead cx`] strip_assume_tac) >>
  `!x w. lookup_var x t = SOME w ==> not_fresh_at sc x` by
    (rpt strip_tac >> simp[not_fresh_at_def] >> rpt strip_tac >>
     qpat_x_assum `fresh_vars_wrt sc t` mp_tac >>
     simp[fresh_vars_wrt_def] >> qexists_tac `n` >> simp[] >>
     qpat_x_assum `lookup_var x t = SOME w` mp_tac >>
     qpat_x_assum `x = _` (fn th => rewrite_tac[GSYM th]) >>
     simp[lookup_var_def, flookup_thm]) >>
  `(!p sz. ce.ce_return_pc = SOME (PtrVar (Var p) sz) ==>
      not_fresh_at sc p /\ op_taint un (Var p) = {}) /\
   (!p sz. ce.ce_return_buf = SOME (PtrVar (Var p) sz) ==> not_fresh_at sc p)` by
    (qpat_assum `ce = _` (fn th => rewrite_tac[th]) >> simp[] >>
     Cases_on `has_rb` >-
       (qpat_x_assum `intcall_entry_return _ _ _ _ _` mp_tac >>
        simp[intcall_entry_return_def] >> strip_tac >>
        qpat_x_assum `has_rb ==> _ /\ rb = SOME _` mp_tac >>
        simp[] >> strip_tac >> simp[] >>
        qpat_x_assum `has_rb ==> ?p. _` mp_tac >> simp[] >>
        strip_tac >> simp[] >> metis_tac[]) >>
     qpat_x_assum `intcall_entry_return _ _ _ _ _` mp_tac >>
     simp[intcall_entry_return_def] >> strip_tac >> simp[] >>
     Cases_on `rb` >> simp[]) >>
  drule_all intcall_materialize_return_frame >> strip_tac >>
  `FDOM env = set (MAP FST caps)` by fs[internal_args_rel_def] >>
  `DRESTRICT env (set (MAP FST caps)) = env` by metis_tac[DRESTRICT_FDOM] >>
  `intcall_completed env cenv2 H' un' t'` by metis_tac[] >>
  `t'.vs_call_ctx = t.vs_call_ctx` by
    (irule run_inst_seq_preserves_field >>
     goal_assum (drule_at Any) >> metis_tac[inv_base_call_ctx]) >>
  `t.vs_accounts = s0.vs_accounts /\ t.vs_transient = s0.vs_transient /\
   t.vs_call_ctx = s0.vs_call_ctx /\ un.t_stor = tn.t_stor /\
   un.t_trans = tn.t_trans /\ un.t_imm = tn.t_imm` by
    (rpt conj_tac >>
     qpat_assum `t = _` (fn th => once_rewrite_tac[th]) >>
     qpat_assum `un = _` (fn th => once_rewrite_tac[th]) >> simp[]) >>
  `stor_taint_ok cx un' t'` by
    (qpat_x_assum `stor_taint_ok cx tn s0` mp_tac >>
     qpat_assum `t = _` (fn th => once_rewrite_tac[th]) >>
     qpat_assum `un = _` (fn th => once_rewrite_tac[th]) >>
     simp[stor_taint_ok_def]) >>
  drule_all internal_capture_materialization_entry >>
  disch_then (qx_choose_then `tc` strip_assume_tac) >>
  `tc = t` by
    (qpat_x_assum `run_inst_seq (emitted_insts st0 sc) s0 = OK tc` mp_tac >>
     simp[]) >> qpat_x_assum `tc = t` SUBST_ALL_TAC >>
  `!i. MEM i (DROP (LENGTH sc.cs_current_insts) sm.cs_current_insts) ==>
       MEM i (fn_insts func)` by
    (qpat_assum `fn_has_code _ _ _` mp_tac >>
     qpat_assum `isPREFIX sm.cs_current_insts st1.cs_current_insts` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >>
     simp[fn_has_code_def, rich_listTheory.IS_PREFIX_APPEND] >>
     rpt strip_tac >> irule lookup_block_fn_insts >>
     goal_assum (drule_at Any) >> simp[] >>
     metis_tac[rich_listTheory.MEM_DROP_IMP]) >>
  drule_all materialize_run_compact >>
  disch_then (qx_choose_then `tm` strip_assume_tac) >>
  `tm = t'` by
    (qpat_x_assum `run_inst_seq _ t = OK tm` mp_tac >> simp[]) >> qpat_x_assum `tm = t'` SUBST_ALL_TAC >>
  `fresh_vars_wrt sm t' /\
   (!aid. aid IN FDOM t'.vs_allocas ==> aid < sm.cs_next_id)` by
    fs[mat_inv_def] >>
  `!p w. lookup_var p t' = SOME w ==> not_fresh_at sm p` by
    (rpt strip_tac >> simp[not_fresh_at_def] >> rpt strip_tac >>
     qpat_x_assum `fresh_vars_wrt sm t'` mp_tac >>
     simp[fresh_vars_wrt_def] >> qexists_tac `n` >> simp[] >>
     qpat_x_assum `lookup_var p' t' = SOME w` mp_tac >>
     qpat_x_assum `p' = _` (fn th => rewrite_tac[GSYM th]) >>
     simp[lookup_var_def, flookup_thm]) >>
  `!p sz name entry. FLOOKUP env name = SOME entry /\
    FLOOKUP cenv2.ce_vars name = SOME (PtrVar (Var p) sz) ==>
    not_fresh_at sm p` by
    (rpt strip_tac >>
     qpat_x_assum `intcall_completed env cenv2 H' un' t'` mp_tac >>
     simp[intcall_completed_def] >> disch_then drule >> strip_tac >>
     qpat_assum `!p w. lookup_var p t' = SOME w ==> _` mp_tac >>
     qpat_assum `FLOOKUP cenv2.ce_vars name = SOME _` mp_tac >>
     qpat_x_assum `FLOOKUP cenv2.ce_vars name = SOME _` kall_tac >>
     qpat_assum `intcall_local_value _ _ _ _ _ _` mp_tac >>
     qpat_assum `FLOOKUP cenv2.ce_vars name = SOME _` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >>
     simp[intcall_local_value_def, ptr_covers_def] >> metis_tac[]) >>
  `cenv2.ce_return_pc = ce.ce_return_pc /\
   cenv2.ce_return_buf = ce.ce_return_buf` by
    (drule materialize_internal_params_shape >> simp[] >>
     strip_tac >> simp[]) >>
  `(!p sz. cenv2.ce_return_buf = SOME (PtrVar (Var p) sz) ==>
      not_fresh_at sm p) /\
   (!p sz. cenv2.ce_return_pc = SOME (PtrVar (Var p) sz) ==>
      not_fresh_at sm p /\ op_taint un' (Var p) = {})` by
    (simp[] >> rpt strip_tac >>
     `not_fresh_at sc p` by metis_tac[] >>
     fs[not_fresh_at_def] >> metis_tac[arithmeticTheory.LESS_EQ_TRANS]) >>
  `alloca_room ctx func t` by
    (qpat_assum `compile_internal_prologue _ _ _ _ _ = _` mp_tac >>
     qpat_assum `fn_has_code _ _ _` mp_tac >>
     qpat_assum `st0.cs_current_insts = []` mp_tac >>
     qpat_assum `isPREFIX sc.cs_current_insts sm.cs_current_insts` mp_tac >>
     qpat_assum `isPREFIX sm.cs_current_insts st1.cs_current_insts` mp_tac >>
     qpat_assum `run_inst_seq (emitted_insts st0 sc) s0 = OK t` mp_tac >>
     qpat_assum `alloca_room ctx func s0` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >> rpt strip_tac >>
     metis_tac[prologue_prefix_alloca_room, rich_listTheory.IS_PREFIX_TRANS]) >>
  `alloca_room ctx func t'` by
    (qpat_assum `compile_internal_prologue _ _ _ _ _ = _` mp_tac >>
     qpat_assum `fn_has_code _ _ _` mp_tac >>
     qpat_assum `st0.cs_current_insts = []` mp_tac >>
     qpat_assum `isPREFIX sm.cs_current_insts st1.cs_current_insts` mp_tac >>
     qpat_assum `run_inst_seq (DROP (LENGTH sc.cs_current_insts) sm.cs_current_insts) t = OK t'` mp_tac >>
     qpat_assum `alloca_room ctx func t` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >> rpt strip_tac >>
     metis_tac[prologue_prefix_alloca_room, emitted_insts_def]) >>
  drule_all prologue_scratch_prepare >> strip_tac >>
  drule_all intcall_scratch_path_word_env_ptr >>
  disch_then (qspecl_then [`func`,`PG`,`cx_dead cx`] strip_assume_tac) >>
  `sm.cs_current_insts = sc.cs_current_insts ++ emitted_insts sc sm /\
   st1.cs_current_insts = sm.cs_current_insts ++ emitted_insts sm st1` by
    (qpat_assum `isPREFIX sc.cs_current_insts sm.cs_current_insts` mp_tac >>
     qpat_assum `isPREFIX sm.cs_current_insts st1.cs_current_insts` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >>
     simp[rich_listTheory.IS_PREFIX_APPEND, emitted_insts_def] >>
     rpt strip_tac >>
     metis_tac[rich_listTheory.DROP_LENGTH_APPEND]) >>
  `EVERY (\i. i.inst_opcode <> INVOKE /\
       ~is_terminator i.inst_opcode /\ i.inst_opcode <> GAS)
       (emitted_insts sc sm)` by
    (qpat_assum `materialize_internal_params ce caps sc = _` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >> strip_tac >>
     drule intCallCalleeTheory.materialize_internal_params_shape >>
     simp[emitted_insts_def] >> rpt strip_tac >>
     gvs[rich_listTheory.DROP_LENGTH_APPEND, EVERY_MEM] >>
     rpt strip_tac >> res_tac >> gvs[is_terminator_def]) >>
  `EVERY (\i. i.inst_opcode <> INVOKE /\
       ~is_terminator i.inst_opcode /\ i.inst_opcode <> GAS)
       (emitted_insts sm st1)` by
    (qpat_assum `(if enabled then _ else _) = _` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >> Cases_on `enabled` >> simp[] >-
       (strip_tac >> drule emitted_allocation_singleton >>
        simp[mk_inst_def, is_terminator_def]) >>
     strip_tac >> gvs[emitted_insts_def]) >>
  `~t.vs_halted /\ t.vs_current_bb = s0.vs_current_bb` by
    (qpat_assum `t = _` (fn th => once_rewrite_tac[th]) >> simp[]) >>
  `~t'.vs_halted /\ t'.vs_current_bb = t.vs_current_bb` by
    (qpat_assum `run_inst_seq _ t = OK t'` mp_tac >>
     qpat_assum `EVERY _ (emitted_insts sc sm)` mp_tac >>
     qpat_assum `~t.vs_halted` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >> rpt strip_tac >>
     `EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
        (DROP (LENGTH sc.cs_current_insts) sm.cs_current_insts)` by
       (fs[EVERY_MEM, emitted_insts_def] >> metis_tac[]) >>
     drule_all run_inst_seq_preserves_entry_control >> simp[]) >>
  `isPREFIX sm.cs_current_insts bb.bb_instructions /\
   isPREFIX st1.cs_current_insts bb.bb_instructions` by
    (qpat_assum `fn_has_code _ _ _` mp_tac >>
     qpat_assum `lookup_block s0.vs_current_bb _ = _` mp_tac >>
     qpat_assum `s0.vs_current_bb = _` mp_tac >>
     qpat_assum `st1.cs_current_bb = st0.cs_current_bb` mp_tac >>
     qpat_assum `isPREFIX sm.cs_current_insts st1.cs_current_insts` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >> simp[fn_has_code_def] >>
     rpt strip_tac >> gvs[] >> metis_tac[rich_listTheory.IS_PREFIX_TRANS]) >>
  `gas_path_ptr (cx_dead cx) 0 ctx func PG FEMPTY (tn with t_var := FEMPTY)
     s0 0 H un (OK (t with vs_inst_idx := LENGTH sc.cs_current_insts))` by
    (qpat_assum `gas_path_ptr _ _ _ _ _ _ _ _ _ H un _` mp_tac >>
     qpat_assum `s0.vs_inst_idx = 0` mp_tac >>
     qpat_assum `st0.cs_current_insts = []` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >> simp[emitted_insts_def]) >>
  `gas_path_ptr (cx_dead cx) 0 ctx func PG FEMPTY (tn with t_var := FEMPTY)
     s0 0 H' un' (OK (t' with vs_inst_idx := LENGTH sm.cs_current_insts))` by
    (mp_tac (GEN_ALL (Q.INST [`prefix` |-> `sc.cs_current_insts`,
       `code` |-> `emitted_insts sc sm`] intcall_path_suffix_join)) >>
     simp[] >> disch_then irule >>
     conj_tac >- simp[] >>
     qexistsl_tac [`H`,`bb`,`t`,`un`] >>
     qpat_assum `sm.cs_current_insts = sc.cs_current_insts ++ _`
       (fn th => once_rewrite_tac[GSYM th]) >>
     metis_tac[GSYM emitted_insts_def]) >>
  `gas_path_ptr (cx_dead cx) 0 ctx func PG FEMPTY (tn with t_var := FEMPTY)
     s0 0 H'' un'' (OK (t'' with vs_inst_idx := LENGTH st1.cs_current_insts))` by
    (qpat_assum `st1.cs_current_insts = sm.cs_current_insts ++ _`
       (fn th => once_rewrite_tac[th]) >>
     irule intcall_path_suffix_join >>
     conj_tac >- simp[] >>
     qexistsl_tac [`H'`,`bb`,`t'`,`un'`] >>
     qpat_assum `st1.cs_current_insts = sm.cs_current_insts ++ _`
       (fn th => once_rewrite_tac[GSYM th]) >>
     metis_tac[GSYM emitted_insts_def]) >>
  `emitted_insts st0 st1 = emitted_insts st0 sc ++
     emitted_insts sc sm ++ emitted_insts sm st1` by
    (qpat_assum `st0.cs_current_insts = []` mp_tac >>
     qpat_assum `sm.cs_current_insts = sc.cs_current_insts ++ _` mp_tac >>
     qpat_assum `st1.cs_current_insts = sm.cs_current_insts ++ _` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >> rpt strip_tac >>
     simp[Once emitted_insts_def] >>
     simp[emitted_insts_def, APPEND_ASSOC]) >>
  `run_inst_seq (emitted_insts st0 st1) s0 = OK t''` by
    (qpat_assum `emitted_insts st0 st1 = _` (fn th => rewrite_tac[th]) >>
     qpat_assum `run_inst_seq (emitted_insts st0 sc) s0 = OK t` mp_tac >>
     qpat_assum `run_inst_seq (DROP (LENGTH sc.cs_current_insts) sm.cs_current_insts) t = OK t'` mp_tac >>
     qpat_assum `run_inst_seq (emitted_insts sm st1) t' = OK t''` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >> rpt strip_tac >>
     fs[GSYM emitted_insts_def] >> metis_tac[run_inst_seq_append]) >>
  drule internal_prologue_run >>
  simp[] >>
  disch_then drule_all >> strip_tac >>
  rename1 `mat_frame st0 s0 sem` >>
  `sem = t''` by
    (qpat_assum `run_inst_seq (emitted_insts st0 st1) s0 = OK t''` mp_tac >>
     qpat_assum `run_inst_seq (_ ++ _ ++ _) s0 = OK sem` mp_tac >>
     qpat_assum `emitted_insts st0 st1 = _` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >> simp[]) >>
  qpat_x_assum `sem = t''` SUBST_ALL_TAC >>
  drule compile_internal_prologue_shape >> strip_tac >>
  `frag_exec ctx st0 st1 (\s. s = s0)
     (\s. s = (t'' with vs_inst_idx := LENGTH st1.cs_current_insts))
     (\r. F)` by
    (qpat_assum `run_inst_seq (emitted_insts st0 st1) s0 = OK t''` mp_tac >>
     qpat_assum `st1.cs_current_insts = st0.cs_current_insts ++ _` mp_tac >>
     qpat_assum `EVERY _ new` mp_tac >>
     qpat_assum `st1.cs_blocks = st0.cs_blocks` mp_tac >>
     qpat_assum `st1.cs_current_bb = st0.cs_current_bb` mp_tac >>
     qpat_assum `st0.cs_current_insts = []` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >> rpt strip_tac >>
     irule frag_exec_run_inst_seq >>
     simp[rich_listTheory.IS_PREFIX_APPEND, emitted_insts_def] >>
     qexists_tac `t''` >> gvs[emitted_insts_def, rich_listTheory.DROP_LENGTH_APPEND]) >>
  qpat_x_assum `frag_exec _ _ _ _ _ _` mp_tac >>
  simp[frag_exec_def] >>
  disch_then (qspec_then `func` mp_tac) >>
  simp[] >> strip_tac >>
  `EVERY (\i. MEM i (fn_insts func) /\ i.inst_opcode <> INVOKE)
     (emitted_insts st0 st1)` by
    (qpat_assum `fn_has_code st0 st1 func` mp_tac >>
     qpat_assum `st1.cs_current_insts = st0.cs_current_insts ++ new` mp_tac >>
     qpat_assum `EVERY _ new` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >>
     simp[fn_has_code_def, emitted_insts_def] >> rpt strip_tac >>
     fs[rich_listTheory.DROP_LENGTH_APPEND, EVERY_MEM] >>
     rpt strip_tac >> res_tac >> simp[] >>
     irule lookup_block_fn_insts >>
     qexistsl_tac [`bb`,`st1.cs_current_bb`] >>
     fs[rich_listTheory.IS_PREFIX_APPEND] >> gvs[]) >>
  `cenv2.ce_imm_alloca = NONE /\ ~cenv2.ce_is_ctor` by
    (qpat_assum `materialize_internal_params ce caps sc = _` mp_tac >>
     qpat_assum `ce = _` mp_tac >>
     qpat_assum `cenv.ce_imm_alloca = NONE` mp_tac >>
     qpat_assum `~cenv.ce_is_ctor` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >> rpt strip_tac >>
     drule materialize_internal_params_shape >> strip_tac >> gvs[]) >>
  `alloca_room ctx func t''` by
    (irule run_inst_seq_alloca_room >>
     qexistsl_tac [`emitted_insts st0 st1`,`s0`] >> simp[]) >>
  `fmp_room ctx func t''` by
    (irule intCallCalleeTheory.run_inst_seq_fmp_room >>
     qexistsl_tac [`emitted_insts st0 st1`,`s0`] >>
     fs[mat_frame_def] >>
     qpat_x_assum `t'' = _` (fn th => ONCE_REWRITE_TAC [th]) >> simp[]) >>
  `ghost_inv d (cenv2 with ce_alloca_locals := T) cx
     (vs with scopes := [env]) H'' un'' t''` by
    (irule intcall_completed_ghost_inv >>
     simp[vyperStateTheory.lookup_scopes_def, AllCaseEqs()] >>
     conj_tac
     >- (qexists_tac `env` >>
         qpat_assum `intcall_completed env cenv2 H'' un'' t''` mp_tac >>
         POP_ASSUM_LIST (K all_tac) >>
         simp[intcall_completed_def] >> strip_tac >>
         gen_tac >> Cases_on `FLOOKUP env name` >> simp[]) >>
     qpat_assum `return_buf_ptr d cenv2 H'' un'' t''` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >>
     Cases_on `d` >> simp[return_buf_ptr_def] >>
     rename1 `return_buf_ptr (SOME pair) _ _ _ _ ==> _` >>
     PairCases_on `pair` >> simp[return_buf_ptr_def]) >>
  `ghost_inv d (cenv2 with ce_alloca_locals := T) cx
     (vs with scopes := [env]) H'' un''
     (t'' with vs_inst_idx := LENGTH st1.cs_current_insts)` by
    (qpat_assum `ghost_inv _ _ _ _ _ _ t''` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >>
     Cases_on `d`
     >- (simp[ghost_inv_def, return_buf_ptr_def, ptr_covers_def,
              lookup_var_def, stor_taint_ok_def] >> metis_tac[]) >>
     rename1 `ghost_inv (SOME pair) _ _ _ _ _ _ ==> _` >>
     PairCases_on `pair` >>
     simp[ghost_inv_def, return_buf_ptr_def, ptr_covers_def,
          lookup_var_def, stor_taint_ok_def] >> metis_tac[]) >>
  `LENGTH st1.cs_current_insts = LENGTH new` by
    (qpat_assum `st1.cs_current_insts = st0.cs_current_insts ++ new` mp_tac >>
     simp[]) >>
  qexistsl_tac [`t'' with vs_inst_idx := LENGTH st1.cs_current_insts`,
                `H''`,`un''`] >>
  simp[stmt_state_rel_inst_idx] >>
  conj_tac
  >- (qpat_assum `sm.cs_current_insts = sc.cs_current_insts ++ _` mp_tac >>
      qpat_assum `st1.cs_current_insts = sm.cs_current_insts ++ _` mp_tac >>
      qpat_assum `LENGTH st1.cs_current_insts = LENGTH new` mp_tac >>
      POP_ASSUM_LIST (K all_tac) >> rpt strip_tac >> fs[] >> decide_tac) >>
  simp[fresh_vars_wrt_def, lookup_var_def] >>
  qpat_assum `state_rel func _ _ _ t''` mp_tac >>
  qpat_assum `immutable_alloca_sep func _ _ _ t''` mp_tac >>
  qpat_assum `alloca_inv t''` mp_tac >>
  qpat_assum `alloca_room ctx func t''` mp_tac >>
  qpat_assum `fmp_room ctx func t''` mp_tac >>
  qpat_assum `fresh_vars_wrt st1 t''` mp_tac >>
  qpat_assum `lookup_var x t'' = _` mp_tac >>
  qpat_assum `has_rb ==> _` mp_tac >>
  qpat_assum `cenv2.ce_imm_alloca = NONE` mp_tac >>
  qpat_assum `~cenv2.ce_is_ctor` mp_tac >>
  qpat_assum `!inst n base sz. _` mp_tac >>
  POP_ASSUM_LIST (K all_tac) >>
  simp[stmt_state_rel_def, fresh_vars_wrt_def, lookup_var_def,
       immutable_base_zero_def] >> rpt strip_tac >> metis_tac[]
QED
