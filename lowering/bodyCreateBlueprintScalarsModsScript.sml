(* The blueprint scalar suffix threads the reached frames and keeps the
   saved constructor payload at the continuation's actual landing. *)
Theory bodyCreateBlueprintScalarsMods
Ancestors
  bodyCreateOperandPreMods bodyCreateOperandCutMods bodyFullPredsMods bodyFullPostsMods
  blueprintLiteralOffsetProps exprBodyPreProps exprWordOperand exprSimPrecompiles
  exprSimWordArgs exprSimSend bodySimStmtFacts exprSafeOperand
  wordArgsPtr abiEncodeArgsSim emittedSeqComposePtr gasSummaryCompose fragGasOriginPtr
  bodyForcedStorageFrameMods vyperStorageTrace vyperCreate builtinCreate
  gasShadow gasShadowCompileHelpers exprLoweringProps loweringShapeDefs
  abiValueEncoding vyperTypeExprResult vyperTypeExprSoundness vyperTypeInvariants
  vyperTypeContractStaticMaps vyperTypeValues vyperTyping integer_word
  loweringPosts compileEnv vyperState vyperInterpreter list bodyPtrDefs exprLowering
  vyperStorageFootprint vyperTypeSystem exprSimSource venomState ptrDiscipline

Theorem blueprint_scalar_result_word[local]:
  expr_result_typed env e (Value v) /\ expr_type e = BaseT bt ==>
  value_has_type (BaseTV bt) v
Proof
  simp[expr_result_typed_def, expr_runtime_typed_def, value_result_typed_def] >>
  metis_tac[evaluate_type_base_result]
QED

Theorem blueprint_scalar_frames[local]:
  stmt_state_rel (H : (bool # 256 word # type_value) list # num list) ctx func cenv cx es s /\
  local_ptrs_reserved cenv sa /\
  ci_mono sa sm /\ wb_frame cenv es em sa s m /\ wb_frame cenv em ee sm m t /\
  ghost_kept_at lo cenv es sa G tn s Gm tm /\ ghost_kept_at lo cenv em sm Gm tm m G1 tn1 ==>
  wb_frame cenv es ee sa s t /\ ghost_kept_at lo cenv es sa G tn s G1 tn1
Proof
  strip_tac >>
  `MAP FDOM es.scopes = MAP FDOM em.scopes` by fs[wb_frame_def, locals_kept_def] >>
  fs[ci_mono_def] >> conj_asm1_tac
  >- (irule (INST_TYPE [alpha |-> ``:256``] wb_frame_trans) >>
      qpat_assum `stmt_state_rel _ _ _ _ _ es s` (irule_at Any) >>
      qpat_assum `wb_frame cenv em ee sm m t` (irule_at Any) >> simp[]) >>
  metis_tac[ghost_kept_at_wb_trans]
QED

Theorem blueprint_scalar_operand_kept[local]:
  wb_frame cenv es ee sa s t /\ ghost_kept_at lo cenv es sa G tn s G' tn' /\
  (!x. op = Var x ==> not_fresh_at sa x) /\ (!l. op <> Label l) /\
  eval_operand op s = SOME w /\ op_taint tn op = {} ==>
  eval_operand op t = SOME w /\ op_taint tn' op = {}
Proof
  strip_tac >> drule_all abi_args_operand_kept >> simp[] >>
  `op_taint tn' op = op_taint tn op` suffices_by simp[] >>
  irule old_operand_taint_frame >> qexists_tac `sa` >> fs[ghost_kept_at_def]
QED

Theorem blueprint_scalar_cons_replay[local]:
  (!tail. bind (eval_expr cx e) (read_result cx)
     (es with gas_obs := xs ++ tail) = (INL v,em with gas_obs := tail)) /\
  (!tail. eval_exprs cx rest (em with gas_obs := ys ++ tail) = (INL vs,ee with gas_obs := tail)) ==>
  !tail. eval_exprs cx (e::rest) (es with gas_obs := (xs ++ ys) ++ tail) =
    (INL (v::vs),ee with gas_obs := tail)
Proof
  strip_tac >> once_rewrite_tac[eval_exprs_cons_action] >>
  irule gas_source_bind_normal >> goal_assum (drule_at Any) >> simp[] >>
  gen_tac >> pure_once_rewrite_tac[bind_def] >> simp[return_def]
QED

Theorem blueprint_salt_word[local]:
  value_has_type (BaseTV (BytesT (Fixed 32))) v ==>
  dest_create_salt v = SOME (typed_val_to_w256 (BaseTV (BytesT (Fixed 32))) v)
Proof
  Cases_on `v` >>
  simp[value_has_type_def,dest_create_salt_def,vyperValueTheory.dest_BytesV_def,
       valueEncodingTheory.typed_val_to_w256_def,PAD_RIGHT]
QED

Theorem blueprint_literal_uint_word[local]:
  expr_body_pre_mods mods cenv cx env e es /\ expr_type e = BaseT (UintT 256) /\
  expr_int_literal (origin_fold_value e) = SOME i ==>
  dest_NumV (IntV i) = SOME (w2n (i2w i : bytes32))
Proof
  strip_tac >>
  `bind (eval_expr cx e) (read_result cx) es = (INL (IntV i),es)` by
    simp[blueprint_literal_offset_read] >>
  drule_all_then strip_assume_tac (REWRITE_RULE [ETA_THM] expr_body_pre_eval_mods) >>
  `value_has_type (BaseTV (UintT 256)) (IntV i)` by
    (fs[value_runtime_typed_def] >> metis_tac[evaluate_type_base_result]) >>
  drule_then mp_tac uint256_typed_dest >>
  simp[valueEncodingTheory.typed_val_to_w256_def,valueEncodingTheory.val_to_w256_def]
QED

(* Project the linked operand's actual write-back and horizon frames. *)
Theorem blueprint_word_landing[local]:
  expr_body_pre_mods mods cenv cx env e es /\ expr_result_typed env e (Value v) /\
  expr_type e = BaseT bt /\ is_word_type (BaseT bt) /\
  lower_value compile_expr cenv (expr_type e) e sa = (op,sb) /\
  ptr_val_ok cx (post_value_type cenv e) v op G tn t /\
  storage_trace_domain cx st0 ee.storage_trace /\
  (!H : (bool # 256 word # type_value) list # num list. valid_horizon cx st0 H ee.storage_trace ==>
    expr_post_mods H ctx func cenv cx e es sa sb s ee v op t /\
    ghost_inv_at_mods (DF H) lo d cenv cx ee G tn t) ==>
  value_has_type (BaseTV bt) v /\
  eval_operand op t = SOME (typed_val_to_w256 (BaseTV bt) v) /\
  op_taint tn op = {} /\ op_prov G op = NONE /\
  (!x. op = Var x ==> not_fresh_at sb x) /\ (!l. op <> Label l) /\
  wb_frame cenv es ee sa s t /\
  (!H : (bool # 256 word # type_value) list # num list. valid_horizon cx st0 H ee.storage_trace ==>
    stmt_state_rel H ctx func cenv cx ee t /\ immutable_frame_mods func cenv cx ee t /\
    storage_well_formed_on cx ee (FST H) /\ ghost_inv_at_mods (DF H) lo d cenv cx ee G tn t)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `valid_horizon cx st0 (storage_trace_horizon ee.storage_trace) ee.storage_trace`
    by fs[storage_trace_domain_def] >>
  first_assum (drule_then strip_assume_tac) >>
  drule_then strip_assume_tac (iffLR expr_post_mods_def) >>
  drule_all_then assume_tac blueprint_scalar_result_word >>
  drule_then assume_tac expr_post_frame >>
  drule_then assume_tac expr_body_pre_mods_well_typed >>
  drule_then assume_tac expr_body_pre_mods_inv >>
  drule_then assume_tac expr_sim_inv_mods_env >>
  drule_then assume_tac vyperTypeEvalCaseProofsTheory.env_consistent_type_defs_get_tenv >>
  `is_word_type (expr_type e)` by simp[] >>
  `!id ty. FLOOKUP env.var_types id = SOME ty ==> well_formed_type env.type_defs ty` by
    (simp[well_formed_type_def] >> rpt strip_tac >>
     drule_all env_consistent_var_type_evaluates >> simp[]) >>
  qpat_assum `lower_value _ _ _ e _ = _`
    (mp_then Any (drule_all_then strip_assume_tac) lower_value_word_shape) >>
  `evaluate_type (get_tenv cx) (expr_type e) = SOME (BaseTV bt)` by
    (drule_all well_typed_expr_type_well_formed >>
     simp[well_formed_type_def, optionTheory.IS_SOME_EXISTS] >>
     metis_tac[evaluate_type_base_result]) >>
  drule_all_then assume_tac expr_post_typed_stack_operand >>
  fs[ptr_val_ok_def,post_value_type_def] >>
  qx_gen_tac `H` >> disch_tac >>
  qpat_assum `!H. _ ==> expr_post_mods H _ _ _ _ _ _ _ _ _ _ _ _ _ /\ _`
    (drule_then strip_assume_tac) >>
  fs[expr_post_mods_def,expr_post_def]
QED

val body_context = ``contract_inv mods exps ctx cenv cx /\ module_body_inv mods src tops cenv cx /\
  shadow_body_inv_mods mods exps ctx shadow_ctx /\ gas_shadow_context ctx shadow_ctx /\
  ctx_inst_ids_distinct ctx /\ gas_shadow_function func shadow_func /\
  MEM func ctx.ctx_functions /\ MEM shadow_func shadow_ctx.ctx_functions /\
  fn_inst_ids_distinct func /\ (!H : (bool # 256 word # type_value) list # num list. dead_lo_ok_mods H (DF H) lo cenv cx)``;
val entry = ``body_const_cells_agree_mods mods cx env es /\ local_ptrs_reserved cenv sa /\
  (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  return_buf_frame d cenv sa s /\ alloca_history func s /\
  (ctx_has_dalloca ctx ==> allocas_below_fmp s) /\
  (!fn i z. frag_reachable ctx func s fn i z ==> dalloca_fmp_headroom i z) /\
  (!H : (bool # 256 word # type_value) list # num list. valid_horizon cx st0 H es.storage_trace ==>
    stmt_state_rel H ctx func cenv cx es s /\ immutable_frame_mods func cenv cx es s /\
    storage_well_formed_on cx es (FST H) /\ ghost_inv_at_mods (DF H) lo d cenv cx es G tn s) /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\ s.vs_inst_idx = LENGTH sa.cs_current_insts``;
val code = ``gas_shadow_state sa sh /\ gas_shadow_state sb shb /\
  fn_has_code sa sb func /\ fn_has_code sh shb shadow_func``;
val scalar_exit = ``\(H : (bool # 256 word # type_value) list # num list)
    (res:value + exception) ee (gt:(string |-> num # num) # taint) r.
  expr_exit res r /\ halt_exit H cx ee res r /\
  (ctx_has_dalloca ctx ==> !z. r = Halt z ==> allocas_below_fmp z)``;
val scalar_landing = ``
  storage_trace_domain cx st0 ee.storage_trace /\
  (!H : (bool # 256 word # type_value) list # num list. valid_horizon cx st0 H ee.storage_trace ==>
    valid_horizon cx st0 H es.storage_trace /\ stmt_state_rel H ctx func cenv cx ee t /\
    immutable_frame_mods func cenv cx ee t /\ storage_well_formed_on cx ee (FST H) /\
    ghost_inv_at_mods (DF H) lo d cenv cx ee G1 tn1 t /\
    gas_origin_ptr_path (DF H,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
      (s,G,tn) marks (OK t,G1,tn1)) /\
  (!tail. bind (eval_expr cx e) (read_result cx)
    (es with gas_obs := gas_explicit marks s.vs_gas_readings ++ tail) =
      (INL v,ee with gas_obs := tail)) /\
  t.vs_current_bb = sb.cs_current_bb /\ t.vs_inst_idx = LENGTH sb.cs_current_insts /\
  ~t.vs_halted /\ alloca_history func t /\ (ctx_has_dalloca ctx ==> allocas_below_fmp t) /\
  s.vs_alloca_next <= t.vs_alloca_next /\
  wb_frame cenv es ee sa s t /\ ghost_kept_at lo cenv es sa G tn s G1 tn1 /\
  return_buf_frame d cenv sb t /\
  (!fn i z. frag_reachable ctx func t fn i z ==> dalloca_fmp_headroom i z) /\
  body_const_cells_agree_mods mods cx env ee /\ expr_sim_inv_mods mods cenv cx env ee /\
  (?a tv b a' v' b'. eval_expr cx e a = (INL tv,b) /\ read_result cx tv a' = (INL v',b')) /\
  eval_operand op t = SOME w /\ op_taint tn1 op = {} /\ op_prov G1 op = NONE /\
  (!x. op = Var x ==> not_fresh_at sb x) /\ (!l. op <> Label l)``;

Theorem blueprint_word_cut[local]:
  ^body_context /\ ^entry /\ ^code /\
  expr_body_pre_mods mods cenv cx env e es /\ body_expr_full_ok_mods mods exps cx e /\
  expr_type e = BaseT bt /\ is_word_type (BaseT bt) /\
  lower_value compile_expr cenv (expr_type e) e sa = (op,sb) /\
  lower_value compile_expr (gas_shadow_env T cenv) (expr_type e) (gas_shadow_expr e) sh = (op,shb) /\
  (!v. storage_trace_frame (next v)) /\
  (!v ee G1 tn1 t marks w. ^scalar_landing /\ value_has_type (BaseTV bt) v /\
    w = typed_val_to_w256 (BaseTV bt) v ==>
    gas_outcome_full_mods (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
      cenv.ce_modules cx st0 (next v) (ee,t,G1,tn1) Q ^scalar_exit) ==>
  gas_outcome_full_mods (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
    cenv.ce_modules cx st0 (bind (bind (eval_expr cx e) (read_result cx)) next) (es,s,G,tn) Q ^scalar_exit
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  irule create_body_operand_cut_replay_mods >>
  rpt (first_assum (irule_at Any)) >> asm_rewrite_tac[] >>
  qx_genl_tac [`v`,`ee`,`G1`,`tn1`,`t`] >> disch_then (map_every assume_tac o CONJUNCTS) >>
  qpat_x_assum `?marks. _ /\ _` (qx_choose_then `marks` strip_assume_tac) >>
  `!H : (bool # 256 word # type_value) list # num list. valid_horizon cx st0 H ee.storage_trace ==>
    expr_post_mods H ctx func cenv cx e es sa sb s ee v op t /\
    ghost_inv_at_mods (DF H) lo d cenv cx ee G1 tn1 t` by
    (rpt strip_tac >> first_assum (drule_then strip_assume_tac) >> simp[]) >>
  drule_all_then strip_assume_tac blueprint_word_landing >>
  qpat_assum `!v ee G1 tn1 t marks w. _ ==> gas_outcome_full_mods _ _ _ _ _ _ _ _` irule >>
  simp[] >> conj_tac >- first_assum ACCEPT_TAC >>
  qexists_tac `marks` >> simp[] >> rpt strip_tac >>
  first_assum (drule_then strip_assume_tac) >> simp[]
QED

(* The folded literal contributes no instructions and no gas observations.
   Its read theorem is about this original expression, not a replay across
   linked constant substitution. *)
Theorem blueprint_offset_cut_mods[local]:
  ^body_context /\ ^entry /\ ^code /\
  expr_body_pre_mods mods cenv cx env e es /\ body_expr_full_ok_mods mods exps cx e /\
  expr_type e = BaseT (UintT 256) /\ storage_trace_domain cx st0 es.storage_trace /\
  (case expr_int_literal (origin_fold_value e) of SOME i => comp_return (Lit (i2w i))
   | NONE => lower_value compile_expr cenv (expr_type e) e) sa = (op,sb) /\
  (case expr_int_literal (origin_fold_value e) of SOME i => comp_return (Lit (i2w i))
   | NONE => lower_value compile_expr (gas_shadow_env T cenv) (expr_type e)
       (gas_shadow_expr e)) sh = (op,shb) /\
  (!v. storage_trace_frame (next v)) /\
  (!v ee G1 tn1 t marks w. ^scalar_landing /\ dest_NumV v = SOME (w2n w) ==>
    gas_outcome_full_mods (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
      cenv.ce_modules cx st0 (next v) (ee,t,G1,tn1) Q ^scalar_exit) ==>
  gas_outcome_full_mods (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
    cenv.ce_modules cx st0 (bind (bind (eval_expr cx e) (read_result cx)) next) (es,s,G,tn) Q ^scalar_exit
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  Cases_on `expr_int_literal (origin_fold_value e)`
  >- suspend "dynamic" >> suspend "literal"
QED

Resume blueprint_offset_cut_mods[dynamic]:
  fs[] >> irule blueprint_word_cut >> rpt (first_assum (irule_at Any)) >>
  asm_rewrite_tac[is_word_type_def] >>
  rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
  qpat_assum `!v ee G1 tn1 t marks w. _ ==> gas_outcome_full_mods _ _ _ _ _ _ _ _` irule >>
  simp[uint256_typed_dest] >> conj_tac >- first_assum ACCEPT_TAC >>
  goal_assum (drule_at Any) >> simp[] >> rpt strip_tac >>
  first_assum (drule_then strip_assume_tac) >> simp[]
QED

Resume blueprint_offset_cut_mods[literal]:
  rename1 `expr_int_literal (origin_fold_value e) = SOME i` >>
  `bind (eval_expr cx e) (read_result cx) = return (IntV i)` by
    simp[FUN_EQ_THM,blueprint_literal_offset_read,return_def] >>
  drule_all_then assume_tac blueprint_literal_uint_word >>
  `?a tv b a' v' b'. eval_expr cx e a = (INL tv,b) /\ read_result cx tv a' = (INL v',b')` by
    (drule_then (qspec_then `es` mp_tac) blueprint_literal_offset_read >>
     simp[bind_def, AllCaseEqs()] >> metis_tac[]) >>
  drule_then assume_tac expr_body_pre_mods_inv >>
  gvs[comp_return_def,bind_return] >>
  qpat_assum `!v ee G1 tn1 t marks w. _ ==> gas_outcome_full_mods _ _ _ _ _ _ _ _` irule >>
  asm_rewrite_tac[] >>
  simp[eval_operand_def,op_taint_def,op_prov_def,wb_frame_refl,ghost_kept_at_refl] >>
  conj_tac >- (qexists_tac `[]` >> simp[return_def, gas_origin_ptr_path_rules] >>
    rpt strip_tac >>
    qpat_assum `!H. valid_horizon _ _ H es.storage_trace ==> stmt_state_rel _ _ _ _ _ _ _ /\ _`
      (drule_then strip_assume_tac) >> simp[]) >>
  rpt (goal_assum (drule_at Any)) >> simp[]
QED

Finalise blueprint_offset_cut_mods

val saved_payload = ``eval_operand cnt t = SOME (n2w (LENGTH args)) /\
  op_taint tn1 cnt = {} /\ op_prov G1 cnt = NONE /\
  (cnt <> Lit 0w ==> ?q a. args_ptr = Var q /\ lookup_var q t = SOME a /\
    ptr_covers G1 tn1 q t (LENGTH args) /\ (args = [] \/ w2n a + LENGTH args <= t.vs_alloca_next) /\
    (!i. w2n a <= i /\ i < w2n a + LENGTH args ==> i NOTIN tn1.t_mem) /\
    read_memory (w2n a) (LENGTH args) t = args)``;
val scalar_replay = ``!tail.
  eval_exprs cx (amount::(salts ++ [offset])) (es with gas_obs := gs ++ tail) =
    (INL (av::((case sv of NONE => [] | SOME v => [v]) ++ [ov])),ee with gas_obs := tail)``;
val suffix_frame = ``wb_frame cenv es ee sa s t /\ ghost_kept_at lo cenv es sa G tn s G1 tn1 /\
  MAP FDOM es.scopes = MAP FDOM ee.scopes /\ s.vs_alloca_next <= t.vs_alloca_next /\
  alloca_history func t /\ (ctx_has_dalloca ctx ==> allocas_below_fmp t) /\
  ~t.vs_halted /\ t.vs_current_bb = sb.cs_current_bb /\ t.vs_inst_idx = LENGTH sb.cs_current_insts /\
  storage_trace_domain cx st0 ee.storage_trace /\
  (!H : (bool # 256 word # type_value) list # num list. valid_horizon cx st0 H ee.storage_trace ==>
    valid_horizon cx st0 H es.storage_trace /\ stmt_state_rel H ctx func cenv cx ee t /\
    immutable_frame_mods func cenv cx ee t /\ storage_well_formed_on cx ee (FST H) /\
    ghost_inv_at_mods (DF H) lo d cenv cx ee G1 tn1 t)``;

(* The byte-window producer supplies its stability test on the composed
   write-back frame, not on a second execution. The continuation gets the
   window at the same landing as the three evaluated scalars. *)
Theorem blueprint_scalar_suffix_cut_mods:
  ^body_context /\ ^entry /\
  expr_body_pre_mods mods cenv cx env
    (Call ann (CreateTarget (CreateFromBlueprint raw) salted rof ks)
      (target_e::amount::(salts ++ offset::ctor)) dflt) entry /\
  expr_sim_inv_mods mods cenv cx env es /\ body_exprs_full_ok_mods mods exps cx (amount::(salts ++ [offset])) /\
  expr_type amount = BaseT (UintT 256) /\ expr_type offset = BaseT (UintT 256) /\
  (if salted then ?e. salts = [e] /\ expr_type e = BaseT (BytesT (Fixed 32)) else salts = []) /\
  lower_value compile_expr cenv (expr_type amount) amount sa = (y,sm) /\
  lower_value compile_expr (gas_shadow_env T cenv) (expr_type amount) (gas_shadow_expr amount) sh = (y,shm) /\
  compile_create_salt compile_expr cenv (if salted then SOME (HD salts) else NONE) sm = (sop,sn) /\
  compile_create_salt compile_expr (gas_shadow_env T cenv)
    (OPTION_MAP gas_shadow_expr (if salted then SOME (HD salts) else NONE)) shm = (sop,shn) /\
  (case expr_int_literal (origin_fold_value offset) of SOME i => comp_return (Lit (i2w i))
   | NONE => lower_value compile_expr cenv (expr_type offset) offset) sn = (off,sb) /\
  (case expr_int_literal (origin_fold_value offset) of SOME i => comp_return (Lit (i2w i))
   | NONE => lower_value compile_expr (gas_shadow_env T cenv) (expr_type offset)
       (gas_shadow_expr offset)) shn = (off,shb) /\
  gas_shadow_state sa sh /\ gas_shadow_state sm shm /\ gas_shadow_state sn shn /\ gas_shadow_state sb shb /\
  fn_has_code sa sm func /\ fn_has_code sm sn func /\ fn_has_code sn sb func /\
  fn_has_code sh shm shadow_func /\ fn_has_code shm shn shadow_func /\ fn_has_code shn shb shadow_func /\
  ci_mono sa sm /\ ci_mono sm sn /\ ci_mono sn sb /\
  storage_trace_domain cx st0 es.storage_trace /\
  eval_operand target s = SOME aw /\ op_taint tn target = {} /\
  (!x. target = Var x ==> not_fresh_at sa x) /\ (!l. target <> Label l) /\
  (!x. args_ptr = Var x \/ cnt = Var x ==> not_fresh_at sa x) /\ LENGTH args < 2 ** 64 /\
  (!av sv ov. storage_trace_frame (next av sv ov)) /\
  (!av sv ov ee G1 tn1 t gs. ^scalar_replay /\ ^suffix_frame ==> ^saved_payload) /\
  (!av sv ov yw sw ow ee G1 tn1 t marks.
    dest_NumV av = SOME (w2n yw) /\ dest_optional_salt sv = SOME sw /\
    dest_NumV ov = SOME (w2n ow) /\ IS_SOME sv = salted /\
    eval_operand target t = SOME aw /\ op_taint tn1 target = {} /\
    eval_operand y t = SOME yw /\ op_taint tn1 y = {} /\
    OPTREL (\op w. eval_operand op t = SOME w /\ op_taint tn1 op = {}) sop sw /\
    eval_operand off t = SOME ow /\ op_taint tn1 off = {} /\ op_prov G1 off = NONE /\
    (!x. MEM (Var x) [target;off;args_ptr;cnt;y] \/ sop = SOME (Var x) ==> not_fresh_at sb x) /\
    ^saved_payload /\ ^suffix_frame /\
    body_const_cells_agree_mods mods cx env ee /\ expr_sim_inv_mods mods cenv cx env ee /\
    return_buf_frame d cenv sb t /\
    (!fn i z. frag_reachable ctx func t fn i z ==> dalloca_fmp_headroom i z) /\
    (!H. valid_horizon cx st0 H ee.storage_trace ==>
      gas_origin_ptr_path (DF H,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
        (s,G,tn) marks (OK t,G1,tn1)) ==>
    gas_outcome_full_mods (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
      cenv.ce_modules cx st0 (next av sv ov) (ee,t,G1,tn1) Q ^scalar_exit) ==>
  gas_outcome_full_mods (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
    cenv.ce_modules cx st0
    (bind (eval_exprs cx (amount::(salts ++ [offset])))
      (\vs. next (HD vs) (if salted then SOME (EL 1 vs) else NONE) (LAST vs)))
    (es,s,G,tn) Q ^scalar_exit
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `expr_body_pre_mods mods cenv cx env amount es` by
    (irule create_operand_pre_mods >>
     qpat_assum `expr_body_pre_mods _ _ _ _ (Call _ _ _ _) _` (irule_at Any) >> simp[]) >>
  qpat_x_assum `body_exprs_full_ok_mods _ _ _ (amount::_)` mp_tac >>
  pure_once_rewrite_tac[body_exprs_full_ok_mods_def] >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  once_rewrite_tac[eval_exprs_cons_action] >>
  simp[NoAsms,bind_assoc,bind_return] >> once_rewrite_tac[GSYM bind_assoc] >>
  qpat_assum `lower_value _ _ _ (gas_shadow_expr amount) sh = _`
    (mp_then (Pat `lower_value _ _ _ (gas_shadow_expr _) _ = _`) irule blueprint_word_cut) >>
  qpat_assum `lower_value _ _ _ amount sa = _` (irule_at Any) >>
  rpt (first_assum (irule_at Any)) >>
  asm_rewrite_tac[is_word_type_def] >> BETA_TAC >>
  conj_tac >- suspend "amount_trace" >> suspend "amount_landing"
QED

Resume blueprint_scalar_suffix_cut_mods[amount_trace]:
  simp[storage_trace_frame_bind_all, evaluate_storage_trace_frame]
QED

Resume blueprint_scalar_suffix_cut_mods[amount_landing]:
  qx_genl_tac [`av`,`em`,`Gm`,`tm`,`m`,`ma`,`yw`] >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  qpat_x_assum `_ ==> body_exprs_full_ok_mods _ _ _ _` (drule_then assume_tac) >>
  `dest_NumV av = SOME (w2n yw)` by simp[uint256_typed_dest] >>
  `sa.cs_next_var <= sm.cs_next_var /\ sm.cs_next_var <= sn.cs_next_var /\ sn.cs_next_var <= sb.cs_next_var`
    by fs[ci_mono_def] >>
  `ci_mono sa sn` by metis_tac[ci_mono_trans] >>
  `local_ptrs_reserved cenv sm /\ local_ptrs_reserved cenv sn` by
    metis_tac[local_ptrs_reserved_next_var,arithmeticTheory.LESS_EQ_TRANS] >>
  qsuff_tac `!sv sw en n Gn tnn mn.
    IS_SOME sv = salted /\ dest_optional_salt sv = SOME sw /\
    OPTREL (\op w. eval_operand op n = SOME w /\ op_taint tnn op = {} /\
      (!x. op = Var x ==> not_fresh_at sn x) /\ (!l. op <> Label l)) sop sw /\
    body_const_cells_agree_mods mods cx env en /\
    expr_sim_inv_mods mods cenv cx env en /\ body_expr_full_ok_mods mods exps cx offset /\
    storage_trace_domain cx st0 en.storage_trace /\
    (!H. valid_horizon cx st0 H en.storage_trace ==>
      valid_horizon cx st0 H es.storage_trace /\ stmt_state_rel H ctx func cenv cx en n /\
      immutable_frame_mods func cenv cx en n /\ storage_well_formed_on cx en (FST H) /\
      ghost_inv_at_mods (DF H) lo d cenv cx en Gn tnn n /\
      gas_origin_ptr_path (DF H,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
        (s,G,tn) mn (OK n,Gn,tnn)) /\
    ~n.vs_halted /\ n.vs_current_bb = sn.cs_current_bb /\ n.vs_inst_idx = LENGTH sn.cs_current_insts /\
    alloca_history func n /\ return_buf_frame d cenv sn n /\
    (ctx_has_dalloca ctx ==> allocas_below_fmp n) /\
    (!fn i z. frag_reachable ctx func n fn i z ==> dalloca_fmp_headroom i z) /\
    s.vs_alloca_next <= n.vs_alloca_next /\ wb_frame cenv es en sa s n /\
    ghost_kept_at lo cenv es sa G tn s Gn tnn /\
    eval_operand y n = SOME yw /\ op_taint tnn y = {} /\
    (!ov ee go.
      (!tail. eval_exprs cx [offset] (en with gas_obs := go ++ tail) = (INL [ov],ee with gas_obs := tail)) ==>
      ?gs. ^scalar_replay) ==>
    gas_outcome_full_mods (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
      cenv.ce_modules cx st0 (bind (bind (eval_expr cx offset) (read_result cx)) (next av sv))
      (en,n,Gn,tnn) Q ^scalar_exit`
  >- suspend "salt" >> suspend "offset"
QED

Resume blueprint_scalar_suffix_cut_mods[salt]:
  disch_tac >>
  `!z sz. cenv.ce_return_buf = SOME (PtrVar (Var z) sz) ==> not_fresh_at sm z` by
    metis_tac[not_fresh_at_mono] >>
  `!z sz. cenv.ce_return_pc = SOME (PtrVar (Var z) sz) ==> not_fresh_at sm z` by
    metis_tac[not_fresh_at_mono] >>
  Cases_on `salted` >> PURE_REWRITE_TAC[COND_CLAUSES] >>
  RULE_ASSUM_TAC (PURE_REWRITE_RULE [COND_CLAUSES])
  >- suspend "salt_some" >> suspend "salt_none"
QED

Resume blueprint_scalar_suffix_cut_mods[salt_none]:
  qpat_x_assum `salts = []` SUBST_ALL_TAC >>
  qpat_x_assum `compile_create_salt compile_expr cenv NONE sm = _`
    (map_every (SUBST_ALL_TAC o SYM) o CONJUNCTS o
     PURE_REWRITE_RULE [compile_create_salt_def,comp_return_def,pairTheory.PAIR_EQ]) >>
  qpat_x_assum `compile_create_salt compile_expr (gas_shadow_env T cenv) _ shm = _`
    (SUBST_ALL_TAC o SYM o cj 2 o
     PURE_REWRITE_RULE [optionTheory.OPTION_MAP_DEF,compile_create_salt_def,
                        comp_return_def,pairTheory.PAIR_EQ]) >>
  `eval_exprs cx [] = return []` by simp[FUN_EQ_THM,eval_exprs_nil,return_def] >>
  pure_rewrite_tac[APPEND] >> once_rewrite_tac[eval_exprs_cons_action] >>
  qpat_assum `eval_exprs cx [] = return []` (fn empty =>
    simp[NoAsms,empty,bind_assoc,bind_return,ETA_THM]) >>
  once_rewrite_tac[GSYM bind_assoc] >> rewrite_tac[ETA_THM] >>
  fs[Once body_exprs_full_ok_mods_def] >>
  qpat_assum `!en n Gn tnn mn. _ ==> gas_outcome_full_mods _ _ _ _ _ _ _ _` irule >>
  asm_rewrite_tac[dest_optional_salt_def] >>
  conj_tac >- (qexists_tac `ma` >> first_assum ACCEPT_TAC) >>
  map_every qx_gen_tac [`ov`,`ef`,`go`] >> disch_tac >>
  qexists_tac `gas_explicit ma s.vs_gas_readings ++ go` >>
  irule blueprint_scalar_cons_replay >> qexists_tac `em` >> simp[]
QED

Resume blueprint_scalar_suffix_cut_mods[salt_some]:
  qpat_x_assum `?e. salts = [e] /\ _`
    (qx_choose_then `salt` (CONJUNCTS_THEN2 SUBST_ALL_TAC assume_tac)) >>
  qpat_x_assum `compile_create_salt compile_expr cenv _ sm = _` mp_tac >>
  qpat_x_assum `compile_create_salt compile_expr (gas_shadow_env T cenv) _ shm = _` mp_tac >>
  simp[compile_create_salt_def, gas_shadow_expr_type] >>
  Cases_on `lower_value compile_expr cenv (BaseT (BytesT (Fixed 32))) salt sm` >>
  Cases_on `lower_value compile_expr (gas_shadow_env T cenv)
    (BaseT (BytesT (Fixed 32))) (gas_shadow_expr salt) shm` >>
  simp[comp_bind_def,comp_return_def] >> rpt strip_tac >> gvs[] >>
  `expr_body_pre_mods mods cenv cx env salt em` by
    (irule create_operand_pre_mods >>
     qpat_assum `expr_body_pre_mods _ _ _ _ (Call _ _ _ _) _` (irule_at Any) >> simp[]) >>
  fs[Once body_exprs_full_ok_mods_def] >>
  once_rewrite_tac[eval_exprs_cons_action] >>
  simp[NoAsms,bind_assoc,bind_return] >> once_rewrite_tac[GSYM bind_assoc] >>
  rename1 `lower_value _ _ _ salt sm = (salt_op,sn)` >>
  rename1 `lower_value _ _ _ (gas_shadow_expr salt) shm = (salt_op,shn)` >>
  `lower_value compile_expr cenv (expr_type salt) salt sm = (salt_op,sn)` by simp[] >>
  `lower_value compile_expr (gas_shadow_env T cenv) (expr_type salt) (gas_shadow_expr salt) shm =
     (salt_op,shn)` by simp[] >>
  qpat_assum `lower_value _ _ (expr_type salt) (gas_shadow_expr salt) shm = _`
    (mp_then (Pat `lower_value _ _ _ (gas_shadow_expr _) _ = _`) irule blueprint_word_cut) >>
  qpat_assum `lower_value _ _ (expr_type salt) salt sm = _` (irule_at Any) >>
  rpt (first_assum (irule_at Any)) >>
  asm_rewrite_tac[is_word_type_def, arithmeticTheory.LESS_EQ_REFL] >> BETA_TAC >> suspend "salt_word"
QED

Resume blueprint_scalar_suffix_cut_mods[salt_word]:
  conj_tac >- simp[storage_trace_frame_bind_all,evaluate_storage_trace_frame] >>
  conj_tac
  >- (rpt strip_tac >>
      qpat_assum `!H. valid_horizon _ _ H em.storage_trace ==> _` (drule_then strip_assume_tac) >> simp[]) >>
  qx_genl_tac [`sv`,`en`,`Gn`,`tnn`,`n`,`ms`,`sw`] >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  qpat_x_assum `_ ==> body_exprs_full_ok_mods _ _ _ _` (drule_then assume_tac) >>
  `dest_create_salt sv = SOME sw` by simp[blueprint_salt_word] >>
  `valid_horizon cx st0 (storage_trace_horizon em.storage_trace) em.storage_trace`
    by fs[storage_trace_domain_def] >>
  qpat_assum `!H. valid_horizon _ _ H em.storage_trace ==> _`
    (drule_then strip_assume_tac) >>
  qpat_assum `!H. valid_horizon _ _ H es.storage_trace ==> _`
    (drule_then strip_assume_tac) >>
  drule_all_then strip_assume_tac blueprint_scalar_frames >>
  qpat_assum `eval_operand y m = SOME _`
    (mp_then Any (drule_all_then strip_assume_tac) blueprint_scalar_operand_kept) >>
  `m.vs_alloca_next <= n.vs_alloca_next ==> s.vs_alloca_next <= n.vs_alloca_next` by decide_tac >>
  once_rewrite_tac[eval_exprs_cons_action] >>
  simp[NoAsms,Once evaluate_def,bind_assoc,bind_return,ETA_THM] >>
  once_rewrite_tac[GSYM bind_assoc] >> rewrite_tac[ETA_THM] >>
  qpat_assum `!sv sw en n Gn tnn mn. _ ==> gas_outcome_full_mods _ _ _ _ _ _ _ _` irule >>
  asm_rewrite_tac[] >> simp[dest_optional_salt_def,optionTheory.OPTREL_def] >>
  conj_tac
  >- (qexists_tac `ma ++ ms` >> rpt strip_tac >>
      qpat_assum `!H. valid_horizon _ _ H en.storage_trace ==> _` (drule_then strip_assume_tac) >>
      qpat_assum `!H. valid_horizon _ _ H em.storage_trace ==> _` (drule_then strip_assume_tac) >>
      simp[] >> irule gas_origin_ptr_path_append >>
      qexistsl_tac [`Gm`,`m`,`(OK m,Gm,tm)`,`tm`] >> simp[]) >>
  reverse conj_tac
  >- fs[Once body_exprs_full_ok_mods_def] >>
  map_every qx_gen_tac [`ov`,`ef`,`go`] >> disch_tac >>
  qexists_tac `gas_explicit ma s.vs_gas_readings ++ (gas_explicit ms m.vs_gas_readings ++ go)` >>
  irule blueprint_scalar_cons_replay >> qexists_tac `em` >> simp[] >>
  irule blueprint_scalar_cons_replay >> qexists_tac `en` >> simp[]
QED

Resume blueprint_scalar_suffix_cut_mods[offset]:
  qx_genl_tac [`sv`,`sw`,`en`,`n`,`Gn`,`tnn`,`mn`] >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `expr_body_pre_mods mods cenv cx env offset en` by
    (irule create_operand_pre_mods >>
     qpat_assum `expr_body_pre_mods _ _ _ _ (Call _ _ _ _) _` (irule_at Any) >> simp[]) >>
  `!z sz. cenv.ce_return_buf = SOME (PtrVar (Var z) sz) ==> not_fresh_at sn z` by
    metis_tac[not_fresh_at_mono] >>
  `!z sz. cenv.ce_return_pc = SOME (PtrVar (Var z) sz) ==> not_fresh_at sn z` by
    metis_tac[not_fresh_at_mono] >>
  irule (Q.INST [`sa` |-> `sn`, `sb` |-> `sb`, `sh` |-> `shn`,
                 `shb` |-> `shb`, `op` |-> `off`] blueprint_offset_cut_mods) >>
  rpt (first_assum (irule_at Any)) >> asm_rewrite_tac[] >> BETA_TAC >>
  conj_tac
  >- (rpt strip_tac >>
      qpat_assum `!H. valid_horizon _ _ H en.storage_trace ==> _`
        (drule_then strip_assume_tac) >> simp[]) >>
  qx_genl_tac [`ov`,`ee`,`G1`,`tn1`,`t`,`mo`,`ow`] >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `!tail. eval_exprs cx [offset]
       (en with gas_obs := gas_explicit mo n.vs_gas_readings ++ tail) =
       (INL [ov],ee with gas_obs := tail)` by
    (gen_tac >> once_rewrite_tac[eval_exprs_cons_action] >>
     pure_once_rewrite_tac[bind_def] >> simp[Once evaluate_def,bind_return,return_def]) >>
  qpat_assum `!ov ee go. _ ==> ?gs. _` (drule_then strip_assume_tac) >>
  `valid_horizon cx st0 (storage_trace_horizon en.storage_trace) en.storage_trace`
    by fs[storage_trace_domain_def] >>
  qpat_assum `!H. valid_horizon _ _ H en.storage_trace ==> _` (drule_then strip_assume_tac) >>
  qpat_assum `!H. valid_horizon _ _ H es.storage_trace ==> _` (drule_then strip_assume_tac) >>
  drule_all_then strip_assume_tac blueprint_scalar_frames >>
  `MAP FDOM es.scopes = MAP FDOM ee.scopes` by fs[wb_frame_def,locals_kept_def] >>
  `s.vs_alloca_next <= t.vs_alloca_next` by decide_tac >>
  `!H. valid_horizon cx st0 H ee.storage_trace ==>
    valid_horizon cx st0 H es.storage_trace /\ stmt_state_rel H ctx func cenv cx ee t /\
    immutable_frame_mods func cenv cx ee t /\ storage_well_formed_on cx ee (FST H) /\
    ghost_inv_at_mods (DF H) lo d cenv cx ee G1 tn1 t` by
    (rpt strip_tac >>
     qpat_assum `!H. valid_horizon _ _ H ee.storage_trace ==> _` (drule_then strip_assume_tac) >>
     qpat_assum `!H. valid_horizon _ _ H en.storage_trace ==> _` (drule_then strip_assume_tac) >>
     simp[]) >>
  `eval_operand target t = SOME aw /\ op_taint tn1 target = {}` by
    (qpat_assum `eval_operand target s = SOME aw`
       (mp_then Any (drule_all_then ACCEPT_TAC) blueprint_scalar_operand_kept)) >>
  `!x. y = Var x ==> not_fresh_at sn x` by metis_tac[not_fresh_at_mono] >>
  `eval_operand y t = SOME yw /\ op_taint tn1 y = {}` by
    (qpat_assum `eval_operand y n = SOME yw`
       (mp_then Any (drule_all_then ACCEPT_TAC) blueprint_scalar_operand_kept)) >>
  `OPTREL (\op w. eval_operand op t = SOME w /\ op_taint tn1 op = {}) sop sw /\
   (!x. sop = SOME (Var x) ==> not_fresh_at sb x)` by
    (namedCases_on `sop` ["","salt_op"] >> Cases_on `sw` >>
     qpat_x_assum `OPTREL _ _ _`
       (STRIP_ASSUME_TAC o SIMP_RULE (srw_ss()) [optionTheory.OPTREL_def]) >>
     simp[optionTheory.OPTREL_def] >>
     conj_tac
     >- (qpat_assum `eval_operand salt_op n = SOME _`
           (mp_then Any (drule_all_then ACCEPT_TAC) blueprint_scalar_operand_kept)) >>
     rpt strip_tac >> irule not_fresh_at_mono >> qexists_tac `sn` >> simp[]) >>
  qpat_assum `!av sv ov ee G1 tn1 t gs. _ ==> eval_operand cnt _ = _ /\ _`
    (drule_all_then (map_every assume_tac o CONJUNCTS)) >>
  `!x. MEM (Var x) [target;off;args_ptr;cnt;y] \/ sop = SOME (Var x) ==> not_fresh_at sb x` by
    (simp[NoAsms,MEM] >> rpt strip_tac >> metis_tac[not_fresh_at_mono,ci_mono_trans]) >>
  qpat_assum `!av sv ov yw sw ow ee G1 tn1 t marks. _ ==> gas_outcome_full_mods _ _ _ _ _ _ _ _` irule >>
  asm_rewrite_tac[] >> conj_tac
  >- (qexists_tac `mn ++ mo` >> rpt strip_tac >>
      qpat_assum `!H. valid_horizon _ _ H ee.storage_trace ==> _ /\ _ /\ _ /\ _ /\ _ /\ gas_origin_ptr_path _ _ mo _`
        (drule_then strip_assume_tac) >>
      qpat_assum `!H. valid_horizon _ _ H en.storage_trace ==> _` (drule_then strip_assume_tac) >>
      irule gas_origin_ptr_path_append >> qexistsl_tac [`Gn`,`n`,`(OK n,Gn,tnn)`,`tnn`] >> simp[]) >>
  simp[]
QED

Finalise blueprint_scalar_suffix_cut_mods
