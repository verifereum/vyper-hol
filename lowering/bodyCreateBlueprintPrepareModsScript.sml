(* Prepare the linked blueprint window at the actual dispatch boundary. *)
Theory bodyCreateBlueprintPrepareMods
Ancestors
  bodyCreateBlueprintGuardMods bodyCreateBlueprintMaterializeMods
  bodyCreateMaterializedWindowMods bodyFullPostsMods bodyFullShadowBodyInv
  bodyFullIfExpReach[qualified] bodyFullHashKeccakFixed[qualified]
  bodyFullPathHistory[qualified] bodyPtrBytestringBuiltinsExternalSlice[qualified]
  accountsRelProps[qualified] exprSimSliceExtcode[qualified] stateRelProj[qualified]
  dallocaCreateGeometry externalEntryShape stmtReasonLitFragMemory[qualified]
  gasOutcomeFullPostMods gasOutcomeFullZeroPrefixMods
  builtinCreate fragExec fragGasOriginPtr loweringShapeDefs exprLoweringProps
  exprSimDefs loweringPosts ptrDiscipline compileEnv vyperCreate vyperStorageFootprint
  venomState venomInst venomLayout list rich_list words finite_map option

Theorem blueprint_append_has_dalloca[local]:
  compile_create_blueprint_check lit target off sm = (code,sn) /\
  compile_create_blueprint_append target amount sop off code args_ptr cnt rof sn = (result,sb) /\
  fn_has_code sm sb func /\ MEM func ctx.ctx_functions ==>
  ctx_has_dalloca ctx
Proof
  strip_tac >> drule_then strip_assume_tac compile_create_blueprint_dalloca_chunk >>
  `cs_extends sm sn` by
    (qspecl_then [`lit`,`target`,`off`,`sm`] mp_tac compile_create_blueprint_check_labels >> simp[]) >>
  `cs_extends sn sd` by
    (simp[cs_extends_def] >> qexists `[]` >> simp[]) >>
  `cs_extends sd sb` by
    (qspecl_then [`created`,`rof`,`sd`] mp_tac compile_check_create_result_labels >> simp[]) >>
  `fn_has_code sn sd func` by
    (irule fn_has_code_mid >> conj_tac >- first_assum ACCEPT_TAC >>
     qexistsl [`sb`,`sm`] >> asm_rewrite_tac[]) >>
  qpat_assum `fn_has_code sn sd func`
    (mp_then Any mp_tac stmtReasonLitFragMemoryTheory.fn_has_code_code) >>
  disch_then (qspec_then `chunk` mp_tac) >> simp[] >> strip_tac >>
  drule_then strip_assume_tac create_blueprint_dalloca_chunk_parts >>
  simp[ctx_has_dalloca_def,EXISTS_MEM] >> qexists `func` >> simp[] >>
  qexists `alloc` >> simp[] >> first_x_assum irule >> simp[]
QED

Theorem blueprint_prepared_mods:
  compile_create_blueprint_check lit target off sm = (codep,sn) /\
  compile_create_blueprint_append target amount sop off codep args_ptr cnt rof sn = (result,sb) /\
  fn_has_code sm sb func /\ contract_inv mods exps ctx cenv cx /\ MEM func ctx.ctx_functions /\
  (!fn i z. contextRawReachable$frag_reachable ctx func s fn i z ==> dalloca_fmp_headroom i z) /\
  storage_trace_domain cx st0 ee.storage_trace /\
  stmt_state_rel H0 ctx func cenv cx es s0 /\
  (!H. valid_horizon cx st0 H ee.storage_trace ==>
    stmt_state_rel H ctx func cenv cx ee s /\ immutable_frame_mods func cenv cx ee s /\
    storage_well_formed_on cx ee (FST H) /\ ghost_inv_at_mods (DF H) lo d cenv cx ee G tn s) /\
  wb_frame cenv es ee sa s0 s /\ ghost_kept_at lo cenv es sa G0 tn0 s0 G tn /\
  alloca_history func s /\ s0.vs_alloca_next <= s.vs_alloca_next /\
  local_ptrs_reserved cenv sm /\ sa.cs_next_var <= sm.cs_next_var /\
  (!x k. cenv.ce_return_buf = SOME (PtrVar (Var x) k) ==> not_fresh_at sm x) /\
  (!x k. cenv.ce_return_pc = SOME (PtrVar (Var x) k) ==> not_fresh_at sm x) /\
  return_buf_frame d cenv sm s /\ fn_inst_ids_distinct func /\
  ~s.vs_halted /\ s.vs_current_bb = sm.cs_current_bb /\ s.vs_inst_idx = LENGTH sm.cs_current_insts /\
  accounts_well_typed ee.accounts /\ LENGTH bs = 20 /\
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
  n = blueprint_copy_size (w2n ow) code /\
  (!tail. source (ee with gas_obs := tail) =
    if ~(if lit then blueprint_size_ok n else w2n ow < LENGTH code) then
      (INR (Error (RuntimeError "create source has no deployable code")),ee with gas_obs := tail)
    else if n + LENGTH args > 2 * max_code_size then
      (INR (Error (RuntimeError "create initcode too large")),ee with gas_obs := tail)
    else bind (ignore_bind (check_not_static cx)
      (create_oracle_result sw (w2n aw) (blueprint_initcode n (w2n ow) code args) rof))
      (read_result cx) (ee with gas_obs := tail)) /\
  (!sc p len t Gmat tt pv sz.
    compile_create_dispatch (Var p) len amount sop rof sc = (result,sb) /\
    fn_has_code sc sb func /\ cs_extends sm sc /\ local_ptrs_reserved cenv sc /\
    sa.cs_next_var <= sc.cs_next_var /\
    (!x k. cenv.ce_return_buf = SOME (PtrVar (Var x) k) ==> not_fresh_at sc x) /\
    (!x k. cenv.ce_return_pc = SOME (PtrVar (Var x) k) ==> not_fresh_at sc x) /\
    ~t.vs_halted /\ t.vs_current_bb = sc.cs_current_bb /\ t.vs_inst_idx = LENGTH sc.cs_current_insts /\
    alloca_history func t /\ allocas_below_fmp t /\ s0.vs_alloca_next <= t.vs_alloca_next /\
    (!H. valid_horizon cx st0 H ee.storage_trace ==>
      stmt_state_rel H ctx func cenv cx ee t /\ immutable_frame_mods func cenv cx ee t /\
      storage_well_formed_on cx ee (FST H) /\ ghost_inv_at_mods (DF H) lo d cenv cx ee Gmat tt t) /\
    wb_frame cenv es ee sa s0 t /\ ghost_kept_at lo cenv es sa G0 tn0 s0 Gmat tt /\
    return_buf_frame d cenv sc t /\
    eval_operand (Var p) t = SOME pv /\ eval_operand len t = SOME sz /\
    w2n sz = n + LENGTH args /\ ptr_covers Gmat tt p t (w2n sz) /\
    ctx_has_dalloca ctx /\ w2n t.vs_initial_fmp <= w2n pv /\ w2n pv + w2n sz <= w2n t.vs_fmp /\
    read_memory (w2n pv) (w2n sz) t = blueprint_initcode n (w2n ow) code args /\
    (!i. w2n pv <= i /\ i < w2n pv + w2n sz ==> i NOTIN tt.t_mem) /\
    op_taint tt (Var p) = {} /\ op_taint tt len = {} /\
    eval_operand amount t = SOME aw /\ op_taint tt amount = {} /\
    OPTREL (\op w. eval_operand op t = SOME w /\ op_taint tt op = {}) sop sw /\
    (!tail. source (ee with gas_obs := tail) =
      if w2n sz > 2 * max_code_size then
        (INR (Error (RuntimeError "create initcode too large")),ee with gas_obs := tail)
      else bind (ignore_bind (check_not_static cx)
        (create_oracle_result sw (w2n aw) (blueprint_initcode n (w2n ow) code args) rof))
        (read_result cx) (ee with gas_obs := tail)) ==>
    gas_outcome_full_mods (DF,lo,explicit,ctx,func,PG) cenv.ce_modules cx st0 source (ee,t,Gmat,tt) Q
      (\H res ee' gt r. expr_exit res r /\ halt_exit H cx ee' res r /\
        (ctx_has_dalloca ctx ==> !z. r = Halt z ==> allocas_below_fmp z))) ==>
  gas_outcome_full_mods (DF,lo,explicit,ctx,func,PG) cenv.ce_modules cx st0 source (ee,s,G,tn) Q
    (\H res ee' gt r. expr_exit res r /\ halt_exit H cx ee' res r /\
      (ctx_has_dalloca ctx ==> !z. r = Halt z ==> allocas_below_fmp z))
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `ctx_has_dalloca ctx` by (drule_all_then ACCEPT_TAC blueprint_append_has_dalloca) >>
  `!bb. MEM bb func.fn_blocks ==> phi_prefix_length bb.bb_instructions = 0` by
    (gen_tac >> disch_tac >>
     drule_all_then ACCEPT_TAC bodyFullIfExpReachTheory.body_inv_no_phi_mods) >>
  `valid_horizon cx st0 (storage_trace_horizon ee.storage_trace) ee.storage_trace` by
    fs[storage_trace_domain_def] >>
  qpat_assum `!H. valid_horizon _ _ H _ ==> stmt_state_rel _ _ _ _ _ _ s /\ _`
    (drule_then (map_every assume_tac o CONJUNCTS)) >>
  suspend "entry"
QED

Resume blueprint_prepared_mods[entry]:
  qpat_assum `stmt_state_rel _ ctx func cenv cx ee s`
    (mp_then Any (mp_then Any (map_every assume_tac o CONJUNCTS)
       accountsRelPropsTheory.state_rel_accounts) stateRelProjTheory.stmt_state_rel_state_rel) >>
  qabbrev_tac `address = typed_val_to_w256 (BaseTV AddressT) (BytesV bs)` >>
  `LENGTH code <= 24576 /\ code = (lookup_account (w2w address) s.vs_accounts).code` by
    (qpat_assum `accounts_agree _ _ ee.accounts s.vs_accounts`
       (mp_then Any mp_tac exprSimSliceExtcodeTheory.slice_extcode_account) >>
     disch_then (qspec_then `bs` mp_tac) >> simp[Abbr `address`]) >>
  `allocas_from lo s` by fs[ghost_inv_at_mods_def] >>
  `allocas_below_fmp s` by
    (qpat_assum `stmt_state_rel _ ctx func cenv cx ee s`
       (mp_then Any (drule_then ACCEPT_TAC) bodyFullHashKeccakFixedTheory.stmt_state_rel_allocas_below_fmp)) >>
  `s.vs_alloca_next <= w2n s.vs_fmp` by
    (qpat_assum `stmt_state_rel _ ctx func cenv cx ee s`
       (mp_then Any mp_tac stateRelProjTheory.stmt_state_rel_fmp_room) >>
     simp[fmp_room_def] >> decide_tac) >>
  suspend "guard"
QED

Resume blueprint_prepared_mods[guard]:
  qabbrev_tac `dh = DF (storage_trace_horizon ee.storage_trace)` >>
  mp_tac (Q.INST [`code_bytes` |-> `code`, `sm` |-> `sn`, `sa` |-> `sm`]
    (Q.INST [`code` |-> `codep`, `aw` |-> `address`, `D0` |-> `dh`, `explicit0` |-> `explicit`]
      (Q.INST [`s0` |-> `s`, `G0` |-> `G`, `tn0` |-> `tn`, `marks` |-> `[]`]
        blueprint_guard_prepare_from_append))) >>
  pure_rewrite_tac[LET_THM] >> BETA_TAC >>
  impl_tac
  >- (conj_tac
      >- (rpt gen_tac >> disch_then (ACCEPT_TAC o MATCH_MP (GEN_ALL blueprint_materialize_no_phi))) >>
      rpt conj_tac >> FIRST [first_assum ACCEPT_TAC, irule (cj 1 gas_origin_ptr_path_rules) >>
                              first_assum ACCEPT_TAC]) >>
  qpat_assum `n = blueprint_copy_size _ _` (PURE_ONCE_REWRITE_TAC o single o SYM) >>
  qabbrev_tac `good = if lit then blueprint_size_ok n else w2n ow < LENGTH code` >>
  reverse (Cases_on `good`) >> pure_rewrite_tac[COND_CLAUSES] >>
  RULE_ASSUM_TAC (PURE_REWRITE_RULE [COND_CLAUSES,NOT_CLAUSES])
  >- suspend "bad" >> suspend "good"
QED

Resume blueprint_prepared_mods[bad]:
  disch_then (qx_choosel_then [`tbad`,`Gbad`,`ttbad`] assume_tac) >>
  irule gas_outcome_full_mods_exit_revert >> reverse conj_tac >- first_assum ACCEPT_TAC >>
  qexistsl_tac [`Gbad`,`ee`,`INR (Error (RuntimeError "create source has no deployable code"))`,`ttbad`,`tbad`] >>
  simp[fragExecTheory.exit_result_def, expr_exit_def, halt_exit_def]
QED

Resume blueprint_prepared_mods[good]:
  disch_then (qx_choosel_then [`sc`,`p`,`len`,`t`,`Gmat`,`tt`] (map_every assume_tac o CONJUNCTS)) >>
  irule gas_outcome_full_mods_zero_prefix >> qexistsl_tac [`Gmat`,`t`,`tt`] >>
  conj_tac >- (gen_tac >> first_assum irule) >>
  suspend "frame"
QED

Resume blueprint_prepared_mods[frame]:
  `t.vs_alloca_next = s.vs_alloca_next /\ t.vs_labels = s.vs_labels` by
    (qpat_assum `t with <|vs_vars := _; vs_inst_idx := _; vs_memory := _; vs_fmp := _|> = s`
       (mp_tac o AP_TERM ``\z:venom_state. (z.vs_alloca_next,z.vs_labels)``) >> simp[NoAsms]) >>
  `alloca_inv s` by
    (qpat_assum `stmt_state_rel _ ctx func cenv cx ee s`
       (mp_then Any strip_assume_tac stateRelProjTheory.stmt_state_rel_local_ptrs_alloca) >>
     first_assum ACCEPT_TAC) >>
  `alloca_history func t` by
    (irule bodyFullPathHistoryTheory.body_full_path_alloca_history >>
     qpat_assum `!D explicit. gas_origin_ptr_path _ (s,G,tn) [] (OK t,Gmat,tt)`
       (qspecl_then [`dh`,`explicit`] (irule_at Any)) >>
     rpt conj_tac >> first_assum ACCEPT_TAC) >>
  `w2n s.vs_fmp = w2n s.vs_fmp` by REFL_TAC >>
  `!H. valid_horizon cx st0 H ee.storage_trace ==>
      stmt_state_rel H ctx func cenv cx ee t /\ immutable_frame_mods func cenv cx ee t /\
      storage_well_formed_on cx ee (FST H) /\ ghost_inv_at_mods (DF H) lo d cenv cx ee Gmat tt t /\
      wb_frame cenv es ee sa s0 t /\ ghost_kept_at lo cenv es sa G0 tn0 s0 Gmat tt /\
      return_buf_frame d cenv sm t` by suspend "horizons" >>
  suspend "operands"
QED

Resume blueprint_prepared_mods[horizons]:
  gen_tac >> disch_tac >>
  qpat_assum `!H. valid_horizon _ _ H _ ==> stmt_state_rel _ _ _ _ _ _ s /\ _`
    (drule_then (map_every assume_tac o CONJUNCTS)) >>
  qpat_assum `ghost_inv_at_mods (DF H) _ _ _ _ _ _ _ s`
    (mp_then Any (drule_all_then strip_assume_tac) materialized_window_frame_mods) >>
  rpt conj_tac >> first_assum ACCEPT_TAC
QED

Resume blueprint_prepared_mods[operands]:
  qpat_assum `!H. valid_horizon _ _ H _ ==> stmt_state_rel _ _ _ _ _ _ t /\ _`
    (drule_then (map_every assume_tac o CONJUNCTS)) >>
  `sa.cs_next_var <= sc.cs_next_var` by decide_tac >>
  `local_ptrs_reserved cenv sc` by metis_tac[local_ptrs_reserved_next_var] >>
  `(!x k. cenv.ce_return_buf = SOME (PtrVar (Var x) k) ==> not_fresh_at sc x) /\
   (!x k. cenv.ce_return_pc = SOME (PtrVar (Var x) k) ==> not_fresh_at sc x)` by
    metis_tac[not_fresh_at_mono] >>
  `return_buf_frame d cenv sc t` by
    (irule bodyMemoryDefsTheory.return_buf_frame_frame >>
     qpat_assum `return_buf_frame d cenv sm t` (irule_at Any) >> simp[]) >>
  `!op. (!x. op = Var x ==> not_fresh_at sm x) ==>
      eval_operand op t = eval_operand op s /\ op_prov Gmat op = op_prov G op /\
      op_taint tt op = op_taint tn op` by
    (match_mp_tac bodyPtrBytestringBuiltinsExternalSliceTheory.reserved_operand_ghost_frame >>
     rpt conj_tac >> first_assum ACCEPT_TAC) >>
  `!x. amount = Var x \/ sop = SOME (Var x) ==> not_fresh_at sm x` by
    (qpat_assum `!x. MEM (Var x) _ \/ _ ==> _` mp_tac >> simp[MEM] >> metis_tac[]) >>
  `eval_operand amount t = SOME aw /\ op_taint tt amount = {}` by
    (qpat_assum `!op. _ ==> eval_operand op t = _ /\ _` (qspec_then `amount` mp_tac) >>
     impl_tac >- metis_tac[] >> simp[]) >>
  `OPTREL (\op w. eval_operand op t = SOME w /\ op_taint tt op = {}) sop sw` by
    (qpat_x_assum `OPTREL _ sop sw` mp_tac >> namedCases_on `sop` ["","salt_op"] >> Cases_on `sw` >>
     simp[NoAsms,OPTREL_def] >> strip_tac >>
     qpat_assum `!op. _ ==> eval_operand op t = _ /\ _` (qspec_then `salt_op` mp_tac) >>
     impl_tac >- metis_tac[optionTheory.SOME_11] >> simp[]) >>
  suspend "continue"
QED

Resume blueprint_prepared_mods[continue]:
  `w2n (n2w (n + LENGTH args):bytes32) = n + LENGTH args` by simp[w2n_n2w] >>
  qpat_assum `!sc p len t Gmat tt pv sz. _ ==> gas_outcome_full_mods _ _ _ _ _ _ _ _`
    (qspecl_then [`sc`,`p`,`len`,`t`,`Gmat`,`tt`,`s.vs_fmp`,`n2w (n + LENGTH args)`] match_mp_tac) >>
  qpat_assum `w2n (n2w (n + LENGTH args)) = _` (PURE_REWRITE_TAC o single) >>
  `s0.vs_alloca_next <= t.vs_alloca_next` by decide_tac >>
  rpt conj_tac >> (REFL_TAC ORELSE first_assum ACCEPT_TAC ORELSE
    (gen_tac >> disch_tac >>
     qpat_assum `!H. valid_horizon _ _ H _ ==> stmt_state_rel _ _ _ _ _ _ t /\ _`
       (drule_then (map_every assume_tac o CONJUNCTS)) >>
     rpt conj_tac >> first_assum ACCEPT_TAC))
QED

Finalise blueprint_prepared_mods
