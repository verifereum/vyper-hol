(* Compile the raw blueprint argument at the actual child and header cuts. *)
Theory bodyCreateBlueprintRawArgsMods
Ancestors
  exprLowering compileEnv builtinCreate exprLoweringProps
  vyperAST venomInst pair bodyCreateBlueprintRawLayoutMods bodyCreateBlueprintRawCopyLandingMods
  bodyCreateBlueprintRawBorrowMods bodyCreateOperandCutMods bodyCreateRawHeadMods
  createSizeRawGasAdmissibleMods exprSimAbiEncodeArgsLabelReplay
  gasOutcomeFullZeroPrefixMods bodyAugGuardedPrefixMods
  gasShadowCompileConvert gasShadowCompileHelpers abiEncodeOwnership
  exprSimConvertFromBytes rawCallBufferPtr valueEncodingProps
  exprSimWordArgs bodyFullExtCallDirectPhase bodyBopBytestringBindMods
  freshWrites exprOperandVar words vyperState
  bodyFullForArrayRound gasShadowCompile bodyFullIfExpReach fragExec
  vyperStorageFootprint fragGasOriginPtr vyperStorageTrace gasShadowCompileBase
  exprReasonOperand bodyCopyReadPhysicalTypeMods exprBodyPreProps aggregateEvaluatedLayout
  exprSimHypsDefs loweringPosts bodyFullPostsMods bodyCreateBlueprintRawTypeMods
  bodyCreateBlueprintRawHeaderMods bodyMemoryDefs venomState bodyPtrDefs
Libs pairLib monadsyntax

Theorem blueprint_raw_args_parts_mods:
  compile_create_blueprint_args compile_expr cenv T later [e] sa = ((dp,len),sb) ==>
  ?vv sm sv ss ptr su sn.
    compile_expr cenv (expr_type e) e sa = (vv,sm) /\
    compile_snapshot_vv cenv (exprs_can_mutate cenv later) vv sm = (sv,ss) /\
    unwrap_value cenv sv ss = (ptr,su) /\
    emit_op MLOAD [ptr] su = (len,sn) /\
    emit_op ADD [ptr; Lit 32w] sn = (dp,sb)
Proof
  simp[compile_create_blueprint_args_def,comp_bind_def,comp_return_def] >>
  rpt (pairarg_tac >> gvs[]) >> strip_tac >> gvs[] >>
  rpt (goal_assum (drule_at Any))
QED

Theorem raw_borrow_header_input[local]:
  stmt_state_rel (H:(bool # bytes32 # type_value) list # num list) ctx func cenv cx es s /\
  evaluate_type (get_tenv cx) (BaseT (BytesT (Dynamic n))) =
     SOME (BaseTV (BytesT (Dynamic n))) /\
  expr_val_rel cx (BaseT (BytesT (Dynamic n))) (BytesV bs) op s /\
  expr_val_at cenv cx (BaseT (BytesT (Dynamic n))) sa sb es (BytesV bs) op s /\
  ptr_val_ok cx (BaseT (BytesT (Dynamic n))) (BytesV bs) op G tn s ==>
  ?p w. op = Var p /\ eval_operand (Var p) s = SOME w /\
    mload (w2n w) s = n2w (LENGTH bs) /\
    ptr_covers G tn p s (32 + LENGTH bs) /\
    w2n w + 32 < dimword (:256) /\ w2n w + 32 + LENGTH bs <= s.vs_alloca_next /\
    mem_bytes_at (w2n w + 32) (LENGTH bs) s.vs_memory = bs /\
    (!i. w2n w <= i /\ i < w2n w + 32 + LENGTH bs ==> i NOTIN tn.t_mem)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all exprSimConvertFromBytesTheory.dynamic_bytes_operand_memory >>
  disch_then (qx_choose_then `w` strip_assume_tac) >>
  `op_taint tn op = {} /\ ptr_mem_ok cx (BaseT (BytesT (Dynamic n))) (BytesV bs) op G tn s` by
    fs[ptr_val_ok_def,is_word_type_def] >>
  drule_all rawCallBufferPtrTheory.ptr_mem_ok_dynamic_bytes_site >> strip_tac >>
  drule_all rawCallBufferPtrTheory.ptr_mem_ok_dynamic_bytes_clean >> strip_tac >>
  `w2n w + 32 + LENGTH bs <= s.vs_alloca_next` by
    (`~is_word_type (BaseT (BytesT (Dynamic n)))` by simp[is_word_type_def] >>
     drule_all abiEncodeOwnershipTheory.abi_encode_owned_footprint_frontier >>
     simp_tac (srw_ss()) [loweringPostsTheory.val_footprint_def] >> decide_tac) >>
  `s.vs_alloca_next < dimword (:256)` by
    (drule_then (strip_assume_tac o MATCH_MP (GEN_ALL alloca_room_next_lt))
       stateRelProjTheory.stmt_state_rel_alloca_room >> first_assum ACCEPT_TAC) >>
  `lookup_var x s = SOME w /\ op_taint tn (Var x) = {}` by fs[eval_operand_def] >>
  `ptr_covers G tn x s (32 + LENGTH bs)` by
    (simp[ptr_covers_def] >> qexistsl [`w`,`b`,`sz`] >> simp[] >> decide_tac) >>
  `w2n w + 32 < dimword (:256)` by decide_tac >>
  qexistsl [`x`,`w`] >> simp[GSYM valueEncodingPropsTheory.mem_word_at_eq_mload,eval_operand_def] >>
  qx_gen_tac `i` >> strip_tac >> Cases_on `i < w2n w + 32`
  >- metis_tac[] >>
  `w2n w + 32 <= i /\ i < w2n w + 32 + LENGTH bs` by decide_tac >> metis_tac[]
QED

Theorem blueprint_raw_args_cut_mods:
  body_const_cells_agree_mods mods cx env es /\
  contract_inv mods exps ctx cenv cx /\ module_body_inv mods src tops cenv cx /\
  shadow_body_inv_mods mods exps ctx shadow_ctx /\
  expr_body_pre_mods mods cenv cx env e es /\ body_expr_full_ok_mods mods exps cx e /\
  expr_type e = BaseT (BytesT (Dynamic cap)) /\
  compile_create_blueprint_args compile_expr cenv T later [e] sa = ((data,cnt),sb) /\
  compile_create_blueprint_args compile_expr (gas_shadow_env T cenv) T (MAP gas_shadow_expr later)
    [gas_shadow_expr e] sh = ((data,cnt),shb) /\
  gas_shadow_state sa sh /\ gas_shadow_state sb shb /\
  gas_shadow_context ctx shadow_ctx /\ ctx_inst_ids_distinct ctx /\
  gas_shadow_function func shadow_func /\ MEM func ctx.ctx_functions /\
  MEM shadow_func shadow_ctx.ctx_functions /\ fn_inst_ids_distinct func /\
  fn_has_code sa sb func /\ fn_has_code sh shb shadow_func /\ local_ptrs_reserved cenv sa /\
  (!H. dead_lo_ok_mods H (DF H) lo cenv cx) /\
  (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  return_buf_frame d cenv sa s /\ alloca_history func s /\
  (ctx_has_dalloca ctx ==> allocas_below_fmp s) /\
  (!fn i z. frag_reachable ctx func s fn i z ==> dalloca_fmp_headroom i z) /\
  (!H. valid_horizon cx st0 H es.storage_trace ==>
    stmt_state_rel H ctx func cenv cx es s /\ immutable_frame_mods func cenv cx es s /\
    storage_well_formed_on cx es (FST H) /\ ghost_inv_at_mods (DF H) lo d cenv cx es G tn s) /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\ s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  (!vs. storage_trace_frame (next vs)) /\
  (!bs ee Gu tu u marks.
    LENGTH bs < 2 ** 64 /\
    (!tail. eval_exprs cx [e] (es with gas_obs := gas_explicit marks s.vs_gas_readings ++ tail) =
      (INL [BytesV bs],ee with gas_obs := tail)) /\
    expr_sim_inv_mods mods cenv cx env ee /\ body_const_cells_agree_mods mods cx env ee /\
    wb_frame cenv es ee sa s u /\ ghost_kept_at lo cenv es sa G tn s Gu tu /\
    MAP FDOM es.scopes = MAP FDOM ee.scopes /\ s.vs_alloca_next <= u.vs_alloca_next /\
    alloca_history func u /\ return_buf_frame d cenv sb u /\
    (ctx_has_dalloca ctx ==> allocas_below_fmp u) /\
    (!fn i z. frag_reachable ctx func u fn i z ==> dalloca_fmp_headroom i z) /\
    ~u.vs_halted /\ u.vs_current_bb = sb.cs_current_bb /\ u.vs_inst_idx = LENGTH sb.cs_current_insts /\
    (!x. data = Var x \/ cnt = Var x ==> not_fresh_at sb x) /\
    storage_trace_domain cx st0 ee.storage_trace /\
    (!H. valid_horizon cx st0 H ee.storage_trace ==>
      valid_horizon cx st0 H es.storage_trace /\ stmt_state_rel H ctx func cenv cx ee u /\
      immutable_frame_mods func cenv cx ee u /\
      storage_well_formed_on cx ee (FST H) /\ ghost_inv_at_mods (DF H) lo d cenv cx ee Gu tu u /\
      gas_origin_ptr_path (DF H,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
        (s,G,tn) marks (OK u,Gu,tu)) /\
    (!vs ef Gf tf f gs.
      (!tail. eval_exprs cx later (ee with gas_obs := gs ++ tail) = (INL vs,ef with gas_obs := tail)) /\
      wb_frame cenv ee ef sb u f /\ ghost_kept_at lo cenv ee sb Gu tu u Gf tf /\
      MAP FDOM ee.scopes = MAP FDOM ef.scopes /\ u.vs_alloca_next <= f.vs_alloca_next /\
      storage_trace_domain cx st0 ef.storage_trace /\
      (!H. valid_horizon cx st0 H ef.storage_trace ==>
        valid_horizon cx st0 H ee.storage_trace /\ stmt_state_rel H ctx func cenv cx ef f /\
        immutable_frame_mods func cenv cx ef f /\
        storage_well_formed_on cx ef (FST H) /\ ghost_inv_at_mods (DF H) lo d cenv cx ef Gf tf f) ==>
      eval_operand cnt f = SOME (n2w (LENGTH bs)) /\ op_taint tf cnt = {} /\ op_prov Gf cnt = NONE /\
      (cnt <> Lit 0w ==> ?q a. data = Var q /\ lookup_var q f = SOME a /\
        ptr_covers Gf tf q f (LENGTH bs) /\ (bs = [] \/ w2n a + LENGTH bs <= f.vs_alloca_next) /\
        (!i. w2n a <= i /\ i < w2n a + LENGTH bs ==> i NOTIN tf.t_mem) /\
        read_memory (w2n a) (LENGTH bs) f = bs)) ==>
    gas_outcome_full_mods (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
      cenv.ce_modules cx st0 (next [BytesV bs]) (ee,u,Gu,tu) Q
      (\H (res:value + exception) ef gt r. expr_exit res r /\ halt_exit H cx ef res r /\
         (ctx_has_dalloca ctx ==> !z. r = Halt z ==> allocas_below_fmp z))) ==>
  gas_outcome_full_mods (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
    cenv.ce_modules cx st0 (bind (eval_exprs cx [e]) next) (es,s,G,tn) Q
    (\H res ef gt r. expr_exit res r /\ halt_exit H cx ef res r /\
       (ctx_has_dalloca ctx ==> !z. r = Halt z ==> allocas_below_fmp z))
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all blueprint_raw_paired_cuts_mods >>
  disch_then (qx_choosel_then [`vv`,`sm`,`sv`,`ss`,`op`,`su`,`sn`,
    `shv`,`shm`,`shsv`,`shss`,`shop`,`shsu`,`shn`] (map_every assume_tac o CONJUNCTS)) >>
  `gas_shadow_state sm shm /\ vv = shv` by
    (drule_then (drule_all_then strip_assume_tac)
       (MATCH_MP nonslot_shadow_cut
         (cj 1 gas_shadow_compile_expr_env |> SPEC_ALL |>
          Q.INST [`shadow` |-> `T`] |> SIMP_RULE (srw_ss()) [])) >> simp[]) >>
  qpat_x_assum `vv = shv` SUBST_ALL_TAC >>
  `!bb. MEM bb func.fn_blocks ==> phi_prefix_length bb.bb_instructions = 0` by
    (drule_then drule body_inv_no_phi_mods >> simp[]) >>
  `fn_has_code sn sb func` by
    (`ci_mono sa sn` by (irule ci_mono_trans >> qexists `su` >> simp[] >>
        irule ci_mono_trans >> qexists `ss` >> simp[] >>
        irule ci_mono_trans >> qexists `sm` >> simp[]) >>
     qspecl_then [`sa`,`sn`,`sb`,`func`] mp_tac fn_has_code_split >>
     fs[ci_mono_def]) >>
  once_rewrite_tac[abi_args_singleton_source] >>
  simp[bind_assoc,bind_return] >> once_rewrite_tac[GSYM bind_assoc] >>
  Cases_on `exprs_can_mutate cenv later` >- suspend "copy" >> suspend "borrow"
QED

Resume blueprint_raw_args_cut_mods[copy]:
  `gas_admissible (eval_expr cx e) expr_vv_res_ok es` by
    drule_then ACCEPT_TAC create_raw_gas_admissible_mods >>
  qmatch_asmsub_rename_tac `compile_expr cenv _ e sa = (vv,sm)` >>
  `compile_snapshot_vv cenv T vv sm = (sv,ss)` by
    (qpat_assum `exprs_can_mutate cenv later` (fn h =>
      qpat_assum `compile_snapshot_vv cenv (exprs_can_mutate cenv later) vv sm = _`
        (ACCEPT_TAC o PURE_REWRITE_RULE [EQT_INTRO h]))) >>
  irule raw_create_head_read_cut_mods >> BETA_TAC >>
  rpt (conj_tac ORELSE first_assum ACCEPT_TAC)
  >- (gen_tac >> first_assum MATCH_ACCEPT_TAC)
  >- (qexistsl [`sm`,`d`,`sa`,`sh`,`shm`,`shadow_func`,`vv`] >>
      rpt (conj_tac ORELSE first_assum ACCEPT_TAC ORELSE REFL_TAC)
      >- suspend "copy_landing" >>
      gen_tac >> disch_tac >> first_assum (drule_then strip_assume_tac) >> simp[]) >>
  qexistsl [`env`,`exps`,`mods`,`src`,`tops`] >> simp[]
QED

Resume blueprint_raw_args_cut_mods[copy_landing]:
  qx_genl_tac [`marks`,`raw`,`v`,`ee`,`t`,`G1`,`tn1`] >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all bop_bytestring_operand_source_mods >>
  disch_then (qspec_then `st0` (map_every assume_tac o CONJUNCTS)) >>
  `valid_horizon cx st0 (storage_trace_horizon ee.storage_trace) ee.storage_trace` by
    fs[storage_trace_domain_def] >>
  qpat_assum `!H. _ ==> (_ /\ _) /\ gas_origin_ptr_path _ _ _ _`
    (drule_then (map_every assume_tac o CONJUNCTS o REWRITE_RULE [CONJ_ASSOC])) >>
  `~t.vs_halted` by simp[] >>
  `ee with gas_obs := [] = ee` by simp[evaluation_state_component_equality] >>
  `eval_expr cx e (es with gas_obs := gas_explicit marks s.vs_gas_readings) = (INL raw,ee)` by
    (qpat_assum `ee with gas_obs := [] = ee` (fn eq =>
       qpat_assum `!tail. eval_expr cx e _ = _`
         (qspec_then `[]` (ACCEPT_TAC o PURE_REWRITE_RULE [listTheory.APPEND_NIL,eq])))) >>
  `!H. valid_horizon cx st0 H ee.storage_trace ==> stmt_state_rel H ctx func cenv cx es s` by
    (gen_tac >> disch_tac >>
     qpat_assum `!H. _ ==> valid_horizon cx st0 H es.storage_trace` (drule_then assume_tac) >>
     qpat_assum `!H. _ ==> stmt_state_rel H _ _ _ _ es s /\ _` (drule_then (ACCEPT_TAC o CONJUNCT1))) >>
  `!H. valid_horizon cx st0 H ee.storage_trace ==>
     vv_post_mods H ctx func cenv cx e es sa sm s ee raw vv t /\
     ghost_inv_at_mods (DF H) lo d cenv cx ee G1 tn1 t` by
    (gen_tac >> disch_tac >>
     qpat_assum `!H. _ ==> (_ /\ _) /\ gas_origin_ptr_path _ _ _ _`
       (drule_then (map_every assume_tac o CONJUNCTS o REWRITE_RULE [CONJ_ASSOC])) >>
     conj_tac >> first_assum ACCEPT_TAC) >>
  `!fn i z. frag_reachable ctx func t fn i z ==> dalloca_fmp_headroom i z` by
    (rpt gen_tac >> strip_tac >> drule_all gas_origin_ptr_path_dalloca_fmp_headroom >> simp[]) >>
  qpat_assum `compile_snapshot_vv cenv T vv sm = _`
    (mp_then Any mp_tac blueprint_raw_copy_landing_mods) >>
  disch_then (fn th => qpat_assum `read_result cx raw ee = _` (mp_then Any mp_tac th)) >>
  disch_then (fn th => qpat_assum `emit_op MLOAD [op] su = _` (mp_then Any mp_tac th)) >>
  disch_then (fn th => qpat_assum `emit_op ADD [op;Lit 32w] sn = _` (mp_then Any mp_tac th)) >>
  disch_then (fn th => qpat_assum `return_buf_frame d cenv sa s` (mp_then Any mp_tac th)) >>
  disch_then (fn th => qpat_assum `ghost_kept_at lo cenv es sa G tn s G1 tn1` (mp_then Any mp_tac th)) >>
  disch_then (fn th => qpat_assum `eval_expr cx e (es with gas_obs := _) = (INL raw,ee)`
    (mp_then Any mp_tac th)) >>
  disch_then (fn th => qpat_assum `expr_body_pre_mods mods cenv cx env e es` (mp_then Any mp_tac th)) >>
  disch_then (qspecl_then [`st0`,`t`,`func`,`gas_explicit_sites ctx shadow_ctx`,`ctx`,`cap`,`PG`,`DF`] mp_tac) >>
  (impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)) >>
  disch_then (qx_choosel_then [`bs`,`u`,`Gu`,`tu`] (map_every assume_tac o CONJUNCTS)) >>
  qpat_x_assum `v = BytesV bs` SUBST_ALL_TAC >>
  `!tail. eval_exprs cx [e] (es with gas_obs := gas_explicit marks s.vs_gas_readings ++ tail) =
      (INL [BytesV bs],ee with gas_obs := tail)` by
    (pure_rewrite_tac[abi_args_singleton_source] >> gen_tac >> simp[Once bind_def,return_def]) >>
  irule augassign_zero_prefix_guarded_mods >>
  conj_tac >- first_assum MATCH_ACCEPT_TAC >>
  conj_tac >- first_assum ACCEPT_TAC >>
  qexistsl [`Gu`,`u`,`tu`] >> conj_tac
  >- (gen_tac >> disch_tac >>
      qpat_assum `!H. _ ==> gas_origin_ptr_path _ (t,G1,tn1) [] _ /\ _`
        (drule_then (ACCEPT_TAC o CONJUNCT1))) >>
  suspend "copy_continuation"
QED

Resume blueprint_raw_args_cut_mods[copy_continuation]:
  qpat_assum `!bs ee Gu tu u marks. _ ==> gas_outcome_full_mods _ _ _ _ (next [BytesV bs]) _ _ _`
    (qspecl_then [`bs`,`ee`,`Gu`,`tu`,`u`,`marks`] mp_tac) >>
  (impl_tac >- (
    rpt (conj_tac ORELSE first_assum ACCEPT_TAC)
    >- (gen_tac >> disch_tac >>
        qpat_assum `!H. _ ==> gas_origin_ptr_path _ (t,G1,tn1) [] _ /\ _`
          (drule_then (map_every assume_tac o CONJUNCTS)) >>
        qpat_assum `!H. _ ==> (_ /\ _) /\ gas_origin_ptr_path _ (s,G,tn) marks _`
          (drule_then (assume_tac o CONJUNCT2)) >>
        rpt (conj_tac ORELSE first_assum ACCEPT_TAC ORELSE first_assum MATCH_MP_TAC) >>
        qpat_assum `gas_origin_ptr_path _ (s,G,tn) marks _`
          (mp_tac o MATCH_MP gas_origin_ptr_path_append) >>
        disch_then (qspecl_then [`t`,`G1`,`tn1`,`[]`,`OK u`,`Gu`,`tu`] mp_tac) >> simp[]) >>
    rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
    rename1 `wb_frame cenv ee ef sb u f` >>
    first_assum MATCH_MP_TAC >> qexists `ef` >> rpt conj_tac >> first_assum ACCEPT_TAC)) >>
  disch_then ACCEPT_TAC
QED

Resume blueprint_raw_args_cut_mods[borrow]:
  qmatch_asmsub_rename_tac `compile_expr cenv _ e sa = (vv,sm)` >>
  `~is_word_type (vv_type vv)` by (
    drule_then assume_tac expr_body_pre_mods_inv >>
    drule_then assume_tac expr_body_pre_mods_well_typed >>
    `reason_uniform_shape compile_expr cenv (expr_type e) e` by
      (irule compile_expr_reason_uniform >> qexists `env` >> fs[expr_sim_inv_mods_def]) >>
    `is_word_type (lowered_value_type cenv e) = is_word_type (expr_type e)` by
      (irule arg_type_fits_word_type >> drule_all_then ACCEPT_TAC copy_lowered_fits_mods) >>
    `vv_type vv = expr_type e \/ vv_type vv = lowered_value_type cenv e` by
      (qpat_assum `reason_uniform_shape _ _ _ _`
         (strip_assume_tac o REWRITE_RULE [reason_uniform_shape_def]) >>
       qpat_x_assum `!sa vv sb. _ ==> reason_result_shape _ _ _` (drule_then mp_tac) >>
       Cases_on `vv` >> simp[reason_result_shape_def,contextTheory.vv_type_def]) >>
    qpat_assum `vv_type vv = _` (once_rewrite_tac o single) >>
    simp[is_word_type_def]) >>
  `~exprs_can_mutate (gas_shadow_env T cenv) (MAP gas_shadow_expr later)` by
    (simp[gas_shadow_expr_can_mutate] >> first_assum ACCEPT_TAC) >>
  map_every (fn (flag, pat) => qpat_assum flag (fn h =>
    qpat_x_assum pat (mp_tac o PURE_REWRITE_RULE [EQF_INTRO h])))
    [(`~exprs_can_mutate cenv later`,`compile_snapshot_vv cenv _ vv sm = _`),
     (`~exprs_can_mutate (gas_shadow_env T cenv) (MAP gas_shadow_expr later)`,
      `compile_snapshot_vv (gas_shadow_env T cenv) _ vv shm = _`)] >>
  qpat_assum `~is_word_type (vv_type vv)`
    (fn th => simp[compile_snapshot_vv_def, comp_return_def, NoAsms, th]) >>
  ntac 2 strip_tac >>
  qpat_x_assum `vv = shsv` (SUBST_ALL_TAC o SYM) >>
  qpat_x_assum `vv = sv` (SUBST_ALL_TAC o SYM) >>
  qpat_x_assum `sm = ss` (SUBST_ALL_TAC o SYM) >>
  qpat_x_assum `shm = shss` (SUBST_ALL_TAC o SYM) >>
  qpat_x_assum `unwrap_value (gas_shadow_env T cenv) vv shm = _`
    (assume_tac o REWRITE_RULE [unwrap_value_gas_shadow_env]) >>
  drule_then (drule_all_then strip_assume_tac)
    (MATCH_MP nonslot_shadow_cut gas_shadow_compiles_unwrap_value) >>
  qpat_x_assum `op = shop` (SUBST_ALL_TAC o SYM) >>
  `lower_value compile_expr cenv (expr_type e) e sa = (op,su) /\
   lower_value compile_expr (gas_shadow_env T cenv) (expr_type e)
     (gas_shadow_expr e) sh = (op,shsu)` by
    (pure_rewrite_tac[lower_value_def,comp_bind_def] >>
     asm_rewrite_tac[pairTheory.pair_case_thm,LET_THM,unwrap_value_gas_shadow_env] >>
     CONV_TAC (DEPTH_CONV PAIRED_BETA_CONV) >> BETA_TAC >> asm_rewrite_tac[]) >>
  `fn_has_code sa su func /\ fn_has_code sh shsu shadow_func` by (
    conj_tac
    >- (qspecl_then [`sa`,`su`,`sb`,`func`] mp_tac fn_has_code_split >>
        `ci_mono sa su /\ ci_mono su sb` by metis_tac[ci_mono_trans] >> fs[ci_mono_def]) >>
    qspecl_then [`sh`,`shsu`,`shb`,`shadow_func`] mp_tac fn_has_code_split >>
    `ci_mono sh shsu /\ ci_mono shsu shb` by metis_tac[ci_mono_trans] >> fs[ci_mono_def]) >>
  irule create_body_operand_cut_replay_mods >> BETA_TAC >>
  rpt (conj_tac ORELSE first_assum ACCEPT_TAC)
  >- (gen_tac >> first_assum MATCH_ACCEPT_TAC) >>
  qexistsl [`d`,`env`,`exps`,`mods`,`op`,`sa`,`su`,`sh`,`shadow_func`,`shsu`,`src`,`tops`] >>
  rpt (conj_tac ORELSE first_assum ACCEPT_TAC) >>
  suspend "borrow_landing"
QED

Resume blueprint_raw_args_cut_mods[borrow_landing]:
  rpt gen_tac >> disch_then (map_every strip_assume_tac o CONJUNCTS) >>
  `bind (eval_expr cx e) (read_result cx)
      (es with gas_obs := gas_explicit marks s.vs_gas_readings) = (INL v,ee)` by
    (`(ee with gas_obs := []) = ee` by simp[evaluation_state_component_equality] >>
     qpat_assum `!tail. bind (eval_expr cx e) (read_result cx) _ = _`
       (qspec_then `[]` (mp_tac o PURE_REWRITE_RULE[listTheory.APPEND_NIL])) >>
     asm_rewrite_tac[]) >>
  qpat_assum `bind (eval_expr cx e) (read_result cx) _ = (INL v,ee)`
    (mp_then Any mp_tac blueprint_raw_read_tag_mods) >>
  disch_then (qspecl_then [`vv`,`sm`,`sa`,`mods`,`env`,`cenv`,`cap`] mp_tac) >>
  (impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)) >>
  disch_then (map_every strip_assume_tac o CONJUNCTS) >>
  qpat_x_assum `v = BytesV bs` SUBST_ALL_TAC >>
  `valid_horizon cx st0 (storage_trace_horizon ee.storage_trace) ee.storage_trace` by
    fs[storage_trace_domain_def] >>
  qpat_assum `!H. valid_horizon _ _ H _ ==> expr_post_mods H _ _ _ _ e es sa su s ee _ op t /\ _`
    (drule_then (assume_tac o CONJUNCT1)) >>
  qhdtm_assum `expr_post_mods` (strip_assume_tac o REWRITE_RULE[expr_post_mods_def]) >>
  drule_then assume_tac expr_post_frame >>
  qhdtm_assum `expr_post` (strip_assume_tac o REWRITE_RULE[expr_post_def]) >>
  `post_value_type cenv e = BaseT (BytesT (Dynamic cap))` by metis_tac[] >>
  qpat_assum `post_value_type cenv e = BaseT _` (fn th =>
    map_every (fn pat => qpat_assum pat (assume_tac o PURE_REWRITE_RULE[th]))
      [`evaluate_type _ (post_value_type _ _) = _`, `expr_val_rel _ (post_value_type _ _) _ _ _`,
       `expr_val_at _ _ (post_value_type _ _) _ _ _ _ _ _`, `ptr_val_ok _ (post_value_type _ _) _ _ _ _ _`]) >>
  drule_all_then (qx_choosel_then [`p`,`w`] (map_every assume_tac o CONJUNCTS))
    raw_borrow_header_input >>
  qpat_x_assum `op = Var p` SUBST_ALL_TAC >>
  `not_fresh_at su p` by
    (qpat_assum `lower_value compile_expr cenv _ e sa = (Var p,su)`
       (mp_then (Pos hd) mp_tac compile_lower_value_var) >> simp[]) >>
  suspend "borrow_header"
QED

Resume blueprint_raw_args_cut_mods[borrow_header]:
  `!H. valid_horizon cx st0 H ee.storage_trace ==>
     stmt_state_rel H ctx func cenv cx ee t /\ immutable_frame_mods func cenv cx ee t /\
     storage_well_formed_on cx ee (FST H) /\ ghost_inv_at_mods (DF H) lo d cenv cx ee G1 tn1 t` by
    (gen_tac >> disch_tac >>
     qpat_assum `!H. valid_horizon _ _ H _ ==> expr_post_mods H _ _ _ _ e es sa su s ee _ _ t /\ _`
       (drule_then (strip_assume_tac o REWRITE_RULE[expr_post_mods_def,expr_post_def])) >>
     rpt conj_tac >> first_assum ACCEPT_TAC) >>
  `sa.cs_next_var <= su.cs_next_var /\ sa.cs_next_id <= su.cs_next_id /\ ci_mono su sb` by
    (`ci_mono sa su /\ ci_mono su sb` by metis_tac[ci_mono_trans] >> fs[ci_mono_def]) >>
  `local_ptrs_reserved cenv su` by
    (irule local_ptrs_reserved_next_var >> qexists `sa` >> simp[]) >>
  `!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at su x` by
    (rpt strip_tac >> irule freshWritesTheory.not_fresh_at_mono >> qexists `sa` >> simp[]) >>
  `!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at su x` by
    (rpt strip_tac >> irule freshWritesTheory.not_fresh_at_mono >> qexists `sa` >> simp[]) >>
  `eval_operand (Var p) t = SOME (n2w (w2n w))` by simp[n2w_w2n] >>
  qpat_assum `emit_op MLOAD [Var p] su = _`
    (mp_then Any mp_tac blueprint_raw_header_frame_mods) >>
  disch_then (fn th => qpat_assum `emit_op ADD [Var p;Lit 32w] sn = _` (mp_then Any mp_tac th)) >>
  disch_then (fn th => qpat_assum `eval_operand (Var p) t = SOME (n2w (w2n w))` (mp_then Any mp_tac th)) >>
  disch_then (fn th => qpat_assum `return_buf_frame d cenv su t` (mp_then Any mp_tac th)) >>
  disch_then (qspecl_then [`tn1`,`st0`,`lo`,`func`,`ee`,`cx`,`ctx`,`bs`,`PG`,`G1`,`DF`] mp_tac) >>
  (impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)) >>
  disch_then (qx_choosel_then [`l`,`q`,`u`,`Gu`,`tu`] (map_every assume_tac o CONJUNCTS)) >>
  irule gas_outcome_full_mods_zero_prefix >>
  qexistsl [`Gu`,`u`,`tu`] >> conj_tac
  >- (gen_tac >> first_assum MATCH_ACCEPT_TAC) >>
  suspend "borrow_continuation"
QED

Resume blueprint_raw_args_cut_mods[borrow_continuation]:
  `valid_horizon cx st0 (storage_trace_horizon ee.storage_trace) es.storage_trace` by
    (first_assum MATCH_MP_TAC >> first_assum ACCEPT_TAC) >>
  qpat_assum `!H. valid_horizon cx st0 H es.storage_trace ==> stmt_state_rel _ _ _ _ _ _ s /\ _`
    (drule_then (assume_tac o CONJUNCT1)) >>
  `MAP FDOM es.scopes = MAP FDOM ee.scopes` by fs[locals_kept_def] >>
  `wb_frame cenv es ee sa s u` by
    (irule (INST_TYPE [alpha |-> ``:256``] wb_frame_trans) >> simp[] >>
     conj_tac >- (qexistsl [`ee`,`su`,`t`] >> simp[]) >>
     goal_assum (drule_at Any)) >>
  `ghost_kept_at lo cenv es sa G tn s Gu tu` by
    (irule (INST_TYPE [beta |-> ``:256``] wordArgsPtrTheory.ghost_kept_at_wb_trans) >> simp[] >>
     conj_tac >- goal_assum (drule_at Any) >>
     qpat_assum `ghost_kept_at lo cenv ee su G1 tn1 t Gu tu` (irule_at Any) >>
     qexists `ee` >> simp[]) >>
  `s.vs_alloca_next <= u.vs_alloca_next /\ t.vs_alloca_next <= u.vs_alloca_next` by
    (asm_rewrite_tac[] >> simp[]) >>
  `!x. data = Var x \/ cnt = Var x ==> not_fresh_at sb x` by
    (asm_rewrite_tac[] >> rpt strip_tac >> gvs[]) >>
  `!tail. eval_exprs cx [e] (es with gas_obs := gas_explicit marks s.vs_gas_readings ++ tail) =
      (INL [BytesV bs],ee with gas_obs := tail)` by
    (pure_rewrite_tac[abi_args_singleton_source] >> gen_tac >> simp[Once bind_def,return_def]) >>
  qpat_assum `!bs ee Gu tu u marks. _ ==> gas_outcome_full_mods _ _ _ _ (next [BytesV bs]) _ _ _`
    (qspecl_then [`bs`,`ee`,`Gu`,`tu`,`u`,`marks`] mp_tac) >>
  (impl_tac >- (
    rpt (conj_tac ORELSE first_assum ACCEPT_TAC)
    >- (gen_tac >> disch_tac >>
        qpat_assum `!H. _ ==> stmt_state_rel _ _ _ _ _ ee u /\ _`
          (drule_then (map_every assume_tac o CONJUNCTS)) >>
        rpt (conj_tac ORELSE first_assum ACCEPT_TAC ORELSE first_assum MATCH_MP_TAC) >>
        qpat_assum `!H. _ ==> gas_origin_ptr_path _ (s,G,tn) marks (OK t,G1,tn1)`
          (drule_then (mp_tac o MATCH_MP gas_origin_ptr_path_append)) >>
        disch_then (qspecl_then [`t`,`G1`,`tn1`,`[]`,`OK u`,`Gu`,`tu`] mp_tac) >> simp[]) >>
    suspend "borrow_retention")) >>
  disch_then ACCEPT_TAC
QED

Resume blueprint_raw_args_cut_mods[borrow_retention]:
  rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
  `lookup_var q u = SOME (n2w (w2n w + 32))` by
    (qpat_assum `data = Var q` (fn th =>
       qpat_assum `eval_operand data u = SOME (n2w (w2n w + 32))`
         (mp_tac o PURE_REWRITE_RULE[th])) >> simp[eval_operand_def]) >>
  `!i. w2n w + 32 <= i /\ i < w2n w + 32 + LENGTH bs ==> i NOTIN tn1.t_mem` by
    (rpt strip_tac >>
     `w2n w <= i` by decide_tac >>
     qpat_assum `!i. w2n w <= i /\ _ ==> i NOTIN tn1.t_mem`
       (qspec_then `i` mp_tac) >> simp[]) >>
  irule blueprint_raw_borrowed_window_mods >>
  map_every (fn pat => qpat_assum pat (irule_at Any))
    [`wb_frame cenv ee ef sb u f`, `ghost_kept_at lo cenv ee su G1 tn1 t Gu tu`,
     `expr_val_at cenv cx (BaseT _) sa su ee (BytesV bs) (Var p) t`,
     `stmt_state_rel _ ctx func cenv cx ee t`, `eval_operand (Var p) t = SOME w`,
     `cnt = Var l`, `data = Var q`] >>
  qexistsl [`vs`,`later`,`gs`] >>
  rpt (conj_tac ORELSE first_assum ACCEPT_TAC ORELSE REFL_TAC) >> simp[]
QED

Finalise blueprint_raw_args_cut_mods
