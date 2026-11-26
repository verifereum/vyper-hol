(* Post-operand validation and materialization for blueprint creation. *)
Theory s1PrefixBlueprintFinish
Ancestors
  s1PrefixCompose s1PrefixFrame bodyFullCreateHeld
  bodySim bodyPtrDefs builtinCreate contextRawReachable exprSimHypsDefs
  context compileEnv list
  vyperStorageTrace vyperStorageFootprint vyperCreate vyperInterpreter
  vyperState vyperAST vyperValue venomState venomInst venomMemDefs
  fragGasOriginPtr fragExec loweringStateRelDefs ptrDiscipline contextCodegenRel
  stateRelProj accountsRelProps exprLoweringProps loweringShapeDefs
  codegenRel emitHelperProps exprSimAccounts stmtSimAugAssignPlace
  stmtReasonLitFragMemory dallocaCreateGeometry externalEntryShape
  exprSimSliceExtcode bodyFullDynamicBuffer memoryReadProps
  bodyPtrBytestringBuiltinsExternalSlice
Libs
  pairLib

Theorem blueprint_finish_prefix_from_dispatch:
  (!codep len amount sop rof sm result sb func s ctx cx st0 ee cenv DF lo d G tn
      pv sz initcode aw sw source explicit PG.
    compile_create_dispatch codep len amount sop rof sm = (result,sb) /\
    fn_has_code sm sb func /\
    ~s.vs_halted /\ s.vs_current_bb = sm.cs_current_bb /\
    s.vs_inst_idx = LENGTH sm.cs_current_insts /\
    (ctx_has_dalloca ctx ==> allocas_below_fmp s) /\
    storage_trace_domain cx st0 ee.storage_trace /\
    (!H. valid_horizon cx st0 H ee.storage_trace ==>
      stmt_state_rel H ctx func cenv cx ee s /\ storage_well_formed_on cx ee (FST H) /\
      ghost_inv_at (DF H) lo d cenv cx ee G tn s) /\
    outcomes_accounts_typed ee.outcomes /\
    eval_operand codep s = SOME pv /\ eval_operand len s = SOME sz /\
    (sz <> 0w ==> ?p. codep = Var p /\ ptr_covers G tn p s (w2n sz)) /\
    (sz <> 0w ==> w2n pv + w2n sz <= s.vs_alloca_next \/
      (ctx_has_dalloca ctx /\ w2n s.vs_initial_fmp <= w2n pv /\
       w2n pv + w2n sz <= w2n s.vs_fmp)) /\
    read_memory (w2n pv) (w2n sz) s = initcode /\
    (!i. w2n pv <= i /\ i < w2n pv + w2n sz ==> i NOTIN tn.t_mem) /\
    op_taint tn codep = {} /\ op_taint tn len = {} /\
    eval_operand amount s = SOME aw /\ op_taint tn amount = {} /\
    (case sop of NONE => sw = NONE | SOME op =>
       ?w. sw = SOME w /\ eval_operand op s = SOME w /\ op_taint tn op = {}) /\
    (!tail. source (ee with gas_obs := tail) =
      if w2n sz > 2 * max_code_size then
        (INR (Error (RuntimeError "create initcode too large")),ee with gas_obs := tail)
      else
        bind (ignore_bind (check_not_static cx)
          (create_oracle_result sw (w2n aw) initcode rof))
          (read_result cx) (ee with gas_obs := tail)) ==>
    gas_prefix_full (DF,lo,explicit,ctx,func,PG) cx st0 source (ee,s,G,tn)) ==>
  compile_create_blueprint_check lit target off sm = (codep,sn) /\
  compile_create_blueprint_append target amount sop off codep args_ptr cnt rof sn = (result,sb) /\
  fn_has_code sm sb func /\ body_inv tops ctx cenv cx /\ MEM func ctx.ctx_functions /\
  (!fn i z. frag_reachable ctx func s fn i z ==> dalloca_fmp_headroom i z) /\
  storage_trace_domain cx st0 ee.storage_trace /\
  stmt_state_rel (storage_trace_horizon ee.storage_trace) ctx func cenv cx es s0 /\
  (!H. valid_horizon cx st0 H ee.storage_trace ==>
    stmt_state_rel H ctx func cenv cx ee s /\ storage_well_formed_on cx ee (FST H) /\
    ghost_inv_at (DF H) lo d cenv cx ee G tn s) /\
  wb_frame cenv es ee sa s0 s /\ ghost_kept_at lo cenv es sa G0 tn0 s0 G tn /\
  s0.vs_alloca_next <= s.vs_alloca_next /\
  local_ptrs_reserved cenv sm /\ sa.cs_next_var <= sm.cs_next_var /\
  (!x k. cenv.ce_return_buf = SOME (PtrVar (Var x) k) ==> not_fresh_at sm x) /\
  (!x k. cenv.ce_return_pc = SOME (PtrVar (Var x) k) ==> not_fresh_at sm x) /\
  return_buf_frame d cenv sm s /\
  ~s.vs_halted /\ s.vs_current_bb = sm.cs_current_bb /\ s.vs_inst_idx = LENGTH sm.cs_current_insts /\
  accounts_well_typed ee.accounts /\ LENGTH bs = 20 /\ outcomes_accounts_typed ee.outcomes /\
  eval_operand target s = SOME (typed_val_to_w256 (BaseTV AddressT) (BytesV bs)) /\
  op_taint tn target = {} /\ eval_operand amount s = SOME aw /\ op_taint tn amount = {} /\
  OPTREL (\op w. eval_operand op s = SOME w /\ op_taint tn op = {}) sop sw /\
  eval_operand off s = SOME ow /\ op_taint tn off = {} /\ op_prov G off = NONE /\
  eval_operand cnt s = SOME (n2w (LENGTH args)) /\ op_taint tn cnt = {} /\ op_prov G cnt = NONE /\
  LENGTH args < 2 ** 64 /\
  (!x. MEM (Var x) [target;off;args_ptr;cnt;amount] \/ sop = SOME (Var x) ==> not_fresh_at sm x) /\
  (cnt <> Lit 0w ==> ?q a. args_ptr = Var q /\ lookup_var q s = SOME a /\
    ptr_covers G tn q s (LENGTH args) /\ (args = [] \/ w2n a + LENGTH args <= s.vs_alloca_next) /\
    (!i. w2n a <= i /\ i < w2n a + LENGTH args ==> i NOTIN tn.t_mem) /\
    read_memory (w2n a) (LENGTH args) s = args) /\
  code = (lookup_account (word_of_bytes_be bs) ee.accounts).code /\
  storage_trace_frame source /\
  (!tail. source (ee with gas_obs := tail) =
    if ~(if lit then blueprint_size_ok (blueprint_copy_size (w2n ow) code) else w2n ow < LENGTH code) then
      (INR (Error (RuntimeError "create source has no deployable code")),ee with gas_obs := tail)
    else if blueprint_copy_size (w2n ow) code + LENGTH args > 2 * max_code_size then
      (INR (Error (RuntimeError "create initcode too large")),ee with gas_obs := tail)
    else bind (ignore_bind (check_not_static cx)
      (create_oracle_result sw (w2n aw) (blueprint_initcode (blueprint_copy_size (w2n ow) code) (w2n ow) code args) rof))
      (read_result cx) (ee with gas_obs := tail)) ==>
  gas_prefix_full (DF,lo,explicit,ctx,func,PG) cx st0 source (ee,s,G,tn)
Proof
  disch_then (mk_asm "dispatch") >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  qabbrev_tac `n = blueprint_copy_size (w2n ow) code` >>
  Cases_on `if lit then blueprint_size_ok n else w2n ow < LENGTH code`
  >- suspend "prepare" >>
  irule gas_prefix_full_no_outcome >> simp[] >>
  rpt gen_tac >>
  qpat_assum `!tail. source _ = _` (qspec_then `gobs` mp_tac) >>
  gvs[Abbr `n`]
QED

Resume blueprint_finish_prefix_from_dispatch[prepare]:
  `ctx_has_dalloca ctx` by suspend "dalloca" >>
  `valid_horizon cx st0 (storage_trace_horizon ee.storage_trace) ee.storage_trace` by
    fs[storage_trace_domain_def] >>
  qpat_assum `!H. _ ==> stmt_state_rel H ctx func cenv cx ee s /\ _`
    (drule_then strip_assume_tac) >>
  qpat_assum `stmt_state_rel _ ctx func cenv cx ee s`
    (mp_then Any (mp_then Any strip_assume_tac accountsRelPropsTheory.state_rel_accounts)
       stateRelProjTheory.stmt_state_rel_state_rel) >>
  `LENGTH code <= 24576 /\
   (lookup_account (w2w (typed_val_to_w256 (BaseTV AddressT) (BytesV bs))) s.vs_accounts).code = code` by
    (drule_all_then strip_assume_tac exprSimSliceExtcodeTheory.slice_extcode_account >> simp[]) >>
  `allocas_from lo s` by fs[ghost_inv_at_def] >>
  `allocas_below_fmp s /\ s.vs_alloca_next <= w2n s.vs_fmp` by suspend "frontier" >>
  `gas_origin_ptr_path (DF (storage_trace_horizon ee.storage_trace),lo,explicit,ctx,func,PG)
     (s,G,tn) [] (OK s,G,tn)` by simp[cj 1 gas_origin_ptr_path_rules] >>
  qpat_assum `(lookup_account _ s.vs_accounts).code = code` (assume_tac o SYM) >>
  drule_all create_blueprint_prepared_path >>
  qpat_x_assum `code = (lookup_account _ s.vs_accounts).code` kall_tac >>
  qpat_x_assum `(lookup_account _ s.vs_accounts).code = code` kall_tac >>
  qpat_x_assum `code = (lookup_account _ ee.accounts).code` kall_tac >>
  qpat_assum `Abbrev (n = _)`
    (fn th => pure_rewrite_tac [GSYM (REWRITE_RULE [markerTheory.Abbrev_def] th)]) >>
  qpat_assum `if lit then _ else _`
    (fn th => pure_rewrite_tac [EQT_INTRO th,COND_CLAUSES]) >>
  disch_then (qx_choosel_then [`sc`,`p`,`lenop`,`t`,`Gmat`,`tt`] (map_every assume_tac o CONJUNCTS)) >>
  irule gas_prefix_full_zero_prefix_guarded >> simp[] >>
  qexistsl [`Gmat`,`t`,`tt`] >> simp[] >>
  suspend "materialized"
QED

Resume blueprint_finish_prefix_from_dispatch[dalloca]:
  drule dallocaCreateGeometryTheory.create_blueprint_create_prefix >>
  disch_then (qx_choosel_then [`len`,`u`,`buf`,`v`,`w`,`r`,`created`,`r'`]
    (map_every assume_tac o CONJUNCTS)) >>
  qpat_x_assum `compile_alloc_dynamic _ _ = _`
    (assume_tac o REWRITE_RULE [compile_alloc_dynamic_def]) >>
  `cs_extends sm sn` by
    metis_tac[externalEntryShapeTheory.compile_create_blueprint_check_labels,pairTheory.SND] >>
  `cs_extends sn u` by
    (qpat_assum `emit_op ADD _ sn = (len,u)`
       (mp_then Any (ACCEPT_TAC o CONJUNCT1) exprSimAccountsTheory.emit_op_extends_next_var)) >>
  `cs_extends sm u` by (irule cs_extends_trans >> qexists `sn` >> simp[]) >>
  `cs_extends u v` by
    (qpat_assum `emit_op DALLOCA _ u = (buf,v)`
       (mp_then Any (ACCEPT_TAC o CONJUNCT1) exprSimAccountsTheory.emit_op_extends_next_var)) >>
  `cs_extends v w` by
    (qpat_assum `emit_void EXTCODECOPY _ v = ((),w)`
       (mp_then Any ACCEPT_TAC stmtSimAugAssignPlaceTheory.aug_place_emit_void_grows)) >>
  `cs_extends w r` by
    (qpat_x_assum `if cnt = Lit 0w then _ else _` mp_tac >>
     Cases_on `cnt = Lit 0w`
     >- (simp[] >> strip_tac >> simp[cs_extends_refl]) >>
     simp[compile_copy_memory_dynamic_def] >>
     disch_then (qx_choosel_then [`dst`,`sc`] strip_assume_tac) >>
     irule cs_extends_trans >> qexists `sc` >>
     conj_tac
     >- (qpat_assum `emit_op ADD _ w = _`
           (mp_then Any (ACCEPT_TAC o CONJUNCT1) exprSimAccountsTheory.emit_op_extends_next_var)) >>
     qpat_assum `emit_void MCOPY _ sc = _`
       (mp_then Any ACCEPT_TAC stmtSimAugAssignPlaceTheory.aug_place_emit_void_grows)) >>
  `cs_extends r r'` by
    (qpat_x_assum `(case sop of NONE => _ | SOME _ => _) r = _` mp_tac >>
     Cases_on `sop` >> simp[] >>
     disch_then (mp_then Any (ACCEPT_TAC o CONJUNCT1) exprSimAccountsTheory.emit_op_extends_next_var)) >>
  `cs_extends r' sb` by
    metis_tac[externalEntryShapeTheory.compile_check_create_result_labels,pairTheory.SND] >>
  `fn_has_code u v func` by
    (irule fragExecTheory.fn_has_code_mid >>
     qpat_assum `fn_has_code sm sb func` (irule_at Any) >>
     simp[] >> metis_tac[cs_extends_trans]) >>
  qpat_assum `emit_op DALLOCA _ _ = _`
    (mp_then Any strip_assume_tac exprLoweringPropsTheory.emit_op_extends) >>
  qpat_assum `emit_op DALLOCA _ _ = _`
    (mp_then Any strip_assume_tac emitHelperPropsTheory.emitted_insts_emit_op) >>
  qpat_assum `same_blocks u v` (strip_assume_tac o REWRITE_RULE [same_blocks_def]) >>
  qpat_assum `fn_has_code u v func` (mp_then Any mp_tac stmtReasonLitFragMemoryTheory.fn_has_code_code) >>
  disch_then (qspec_then `emitted_insts u v` mp_tac) >> simp[] >> strip_tac >>
  simp[ctx_has_dalloca_def,EXISTS_MEM] >> qexists `func` >> simp[] >>
  qexists `mk_inst u.cs_next_id DALLOCA [len] [STRING #"%" (toString u.cs_next_var)]` >>
  reverse conj_tac >- simp[mk_inst_def] >> first_x_assum irule >> simp[]
QED

Resume blueprint_finish_prefix_from_dispatch[frontier]:
  `s.vs_alloca_next <= w2n s.vs_initial_fmp /\ w2n s.vs_initial_fmp <= w2n s.vs_fmp` by
    (qpat_assum `stmt_state_rel _ ctx func cenv cx ee s`
       (mp_then Any mp_tac stateRelProjTheory.stmt_state_rel_fmp_room) >>
     simp[fmp_room_def] >> rpt strip_tac >> decide_tac) >>
  `s.vs_alloca_next <= w2n s.vs_fmp` by decide_tac >>
  simp[allocas_below_fmp_def] >>
  qpat_assum `stmt_state_rel _ ctx func cenv cx ee s`
    (mp_then Any strip_assume_tac stateRelProjTheory.stmt_state_rel_local_ptrs_alloca) >>
  fs[alloca_inv_def,alloca_next_valid_def] >> rpt strip_tac >> first_x_assum drule >> decide_tac
QED

Resume blueprint_finish_prefix_from_dispatch[materialized]:
  `!H. valid_horizon cx st0 H ee.storage_trace ==>
    stmt_state_rel H ctx func cenv cx ee t /\ storage_well_formed_on cx ee (FST H) /\
    ghost_inv_at (DF H) lo d cenv cx ee Gmat tt t` by
    (gen_tac >> disch_tac >>
     qpat_assum `!H. _ ==> stmt_state_rel H ctx func cenv cx ee s /\ _`
       (drule_then (map_every assume_tac o CONJUNCTS)) >>
     qpat_assum `!b k. _ ==> read_memory b k t = _`
       (assume_tac o REWRITE_RULE [memoryReadPropsTheory.read_memory_eq_mem_bytes_at]) >>
     `w2n s.vs_fmp = w2n s.vs_fmp` by simp[] >>
     drule_all_then (map_every assume_tac o CONJUNCTS) bodyFullDynamicBufferTheory.dynamic_buffer_materialized_frame >>
     simp[]) >>
  `t.vs_labels = s.vs_labels` by
    (qpat_assum `_ with <|vs_vars := _; vs_inst_idx := _; vs_memory := _; vs_fmp := _|> = _`
       (mp_tac o AP_TERM ``\u:venom_state. u.vs_labels``) >> simp[]) >>
  `!op. (!x. op = Var x ==> not_fresh_at sm x) ==>
      eval_operand op t = eval_operand op s /\ op_prov Gmat op = op_prov G op /\
      op_taint tt op = op_taint tn op` by
    (match_mp_tac bodyPtrBytestringBuiltinsExternalSliceTheory.reserved_operand_ghost_frame >> simp[]) >>
  `!x. amount = Var x \/ sop = SOME (Var x) ==> not_fresh_at sm x` by
    (rpt strip_tac >> qpat_assum `!x. MEM (Var x) _ \/ _ ==> _` irule >> simp[MEM]) >>
  `eval_operand amount t = SOME aw /\ op_taint tt amount = {}` by metis_tac[] >>
  `(case sop of NONE => sw = NONE | SOME op =>
      ?w. sw = SOME w /\ eval_operand op t = SOME w /\ op_taint tt op = {})` by
    (Cases_on `sop` >> Cases_on `sw` >> gvs[optionTheory.OPTREL_def] >> metis_tac[]) >>
  suspend "dispatch"
QED

Resume blueprint_finish_prefix_from_dispatch[dispatch]:
  qabbrev_tac `N = n + LENGTH args` >>
  `w2n (n2w N:bytes32) = N` by simp[wordsTheory.w2n_n2w] >>
  `!tail. source (ee with gas_obs := tail) =
    if N > 2 * max_code_size then
      (INR (Error (RuntimeError "create initcode too large")),ee with gas_obs := tail)
    else bind (ignore_bind (check_not_static cx)
      (create_oracle_result sw (w2n aw) (blueprint_initcode n (w2n ow) code args) rof))
      (read_result cx) (ee with gas_obs := tail)` by
    (qpat_assum `!tail. source (ee with gas_obs := tail) = _`
       (fn th => simp[Once th,Abbr `N`])) >>
  asm "dispatch" irule >>
  qpat_assum `compile_create_dispatch (Var p) lenop _ _ _ _ = _` (irule_at Any) >>
  qpat_assum `eval_operand (Var p) t = SOME _` (irule_at Any) >>
  qpat_assum `eval_operand lenop t = SOME _` (irule_at Any) >>
  qpat_assum `eval_operand amount t = SOME _` (irule_at Any) >>
  qexistsl [`sw`,`blueprint_initcode n (w2n ow) code args`,`d`,`cenv`] >>
  simp[]
QED

Finalise blueprint_finish_prefix_from_dispatch
