(* From the saved constructor payload to the linked Create outcome. *)
Theory bodyCreateBlueprintScalarFinishMods
Ancestors
  bodyCreateBlueprintScalarsMods bodyCreateBlueprintPrepareMods bodyCreateDispatchMods
  bodyFullPredsMods bodyFullPostsMods exprSimHypsDefs
  exprSimWordArgs wordArgsPtr exprLoweringProps loweringShapeDefs
  vyperCreate vyperStorageTrace vyperStorageFootprint vyperValue vyperState
  gasShadow gasShadowCompileHelpers gasOutcomeFullMods fragGasOriginPtr
  builtinCreate ptrDiscipline venomInst loweringPosts compileEnv list rich_list words

Theorem blueprint_scalar_read_prepared[local]:
  IS_SOME ee.outcomes /\ dest_AddressV tv = SOME addr /\
  dest_NumV av = SOME value /\ dest_NumV ov = SOME off /\
  dest_optional_salt sv = SOME sw /\ LENGTH salts = (if IS_SOME sv then 1 else 0) /\
  (if raw then vs = [BytesV bytes]
   else encode_create_ctor_args (get_tenv cx) (MAP expr_type ctor) vs = SOME bytes) /\
  code = (lookup_account addr ee.accounts).code ==>
  bind (eval_create_operands cx (CreateFromBlueprint raw) (IS_SOME sv) rof
    (expr_type target_e::expr_type amount::(MAP expr_type salts ++ expr_type offset::MAP expr_type ctor)) lit
    (tv::(vs ++ av::((case sv of NONE => [] | SOME v => [v]) ++ [ov]))))
    (read_result cx) ee =
  if ~(if lit then blueprint_size_ok (blueprint_copy_size off code) else off < LENGTH code) then
    (INR (Error (RuntimeError "create source has no deployable code")),ee)
  else if LENGTH bytes + blueprint_copy_size off code > 2 * max_code_size then
    (INR (Error (RuntimeError "create initcode too large")),ee)
  else bind (ignore_bind (check_not_static cx)
    (create_oracle_result sw value (blueprint_initcode (blueprint_copy_size off code) off code bytes) rof))
    (read_result cx) ee
Proof
  Cases_on `sv` >>
  simp[eval_create_operands_def,create_operand_layout_def,DROP_LENGTH_APPEND,TAKE_LENGTH_APPEND,
       LENGTH_EQ_NUM_compute] >> strip_tac >> gvs[] >>
  Cases_on `if lit then blueprint_size_ok (blueprint_copy_size off (lookup_account addr ee.accounts).code)
            else off < LENGTH (lookup_account addr ee.accounts).code` >>
  simp[check_create_blueprint_def,blueprint_prefix_size_def,
       dest_create_args_def,make_create_operands_def,dest_optional_num_def,dest_optional_salt_def,
       bind_def,lift_option_def,get_accounts_def,return_def,raise_def] >>
  Cases_on `raw` >> gvs[dest_optional_salt_def] >>
  ONCE_REWRITE_TAC[eval_create_def] >>
  simp[dest_create_args_def,make_create_operands_def,create_arg_ctor_types_def,dest_optional_num_def,
       dest_optional_salt_def,lift_option_type_def,bind_return,build_create_code_def] >>
  simp[get_accounts_def,bind_def,return_def,ignore_bind_def,check_def,check_not_static_def,assert_def,raise_def] >>
  Cases_on `LENGTH bytes + blueprint_copy_size off (lookup_account addr ee.accounts).code <= 2 * max_code_size` >>
  Cases_on `cx.txn.is_static` >>
  simp[return_def,raise_def,arithmeticTheory.NOT_GREATER]
QED

val bp_call = ``Call ann (CreateTarget (CreateFromBlueprint raw) salted rof ks)
  (target_e::amount::(salts ++ offset::ctor)) dflt``;
val bp_next = ``\av sv ov. bind (eval_create_operands cx (CreateFromBlueprint raw) salted rof
  (MAP expr_type (target_e::amount::(salts ++ offset::ctor)))
  (blueprint_literal_offset cx salted (target_e::amount::(salts ++ offset::ctor)))
  (target_v::(vs ++ av::((case sv of NONE => [] | SOME v => [v]) ++ [ov])))) (read_result cx)``;
val normal_post = ``\(H : (bool # 256 word # type_value) list # num list) (res:value + exception) ee' G' tn' t. ?v. res = INL v /\
  expr_post_mods H ctx func cenv cx ^bp_call es0 sa0 sf s0 ee' v result t /\
  expr_store_bound cx (BaseT AddressT) v result t /\
  t.vs_current_bb = sf.cs_current_bb /\ t.vs_inst_idx = LENGTH sf.cs_current_insts /\
  alloca_history func t /\ (ctx_has_dalloca ctx ==> allocas_below_fmp t) /\
  s0.vs_alloca_next <= t.vs_alloca_next /\
  ghost_inv_at_mods (DF H) lo d cenv cx ee' G' tn' t /\
  ptr_val_ok cx (BaseT AddressT) v result G' tn' t /\
  ghost_kept_at lo cenv es0 sa0 G0 tn0 s0 G' tn'``;
val exit_post = ``\(H : (bool # 256 word # type_value) list # num list)
    (res:value + exception) ee' (gt:(string |-> num # num) # taint) r.
  expr_exit res r /\ halt_exit H cx ee' res r /\
  (ctx_has_dalloca ctx ==> !z. r = Halt z ==> allocas_below_fmp z)``;

Theorem blueprint_scalar_finish_mods:
  contract_inv mods exps ctx cenv cx /\ module_body_inv mods src tops cenv cx /\
  shadow_body_inv_mods mods exps ctx shadow_ctx /\ gas_shadow_context ctx shadow_ctx /\
  ctx_inst_ids_distinct ctx /\ gas_shadow_function func shadow_func /\
  MEM func ctx.ctx_functions /\ MEM shadow_func shadow_ctx.ctx_functions /\
  fn_inst_ids_distinct func /\ (!H. dead_lo_ok_mods H (DF H) lo cenv cx) /\
  body_const_cells_agree_mods mods cx env es /\ local_ptrs_reserved cenv sa /\
  (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  return_buf_frame d cenv sa s /\ alloca_history func s /\
  (ctx_has_dalloca ctx ==> allocas_below_fmp s) /\
  (!fn i z. frag_reachable ctx func s fn i z ==> dalloca_fmp_headroom i z) /\
  (!H. valid_horizon cx st0 H es.storage_trace ==>
    stmt_state_rel H ctx func cenv cx es s /\ immutable_frame_mods func cenv cx es s /\
    storage_well_formed_on cx es (FST H) /\ ghost_inv_at_mods (DF H) lo d cenv cx es G tn s) /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\ s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  expr_body_pre_mods mods cenv cx env ^bp_call entry /\
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
  LENGTH bs = 20 /\ dest_AddressV target_v = SOME (word_of_bytes_be bs) /\
  eval_operand target s = SOME (typed_val_to_w256 (BaseTV AddressT) (BytesV bs)) /\ op_taint tn target = {} /\
  (!x. target = Var x ==> not_fresh_at sa x) /\ (!l. target <> Label l) /\
  (!x. args_ptr = Var x \/ cnt = Var x ==> not_fresh_at sa x) /\ LENGTH bytes < 2 ** 64 /\
  (if raw then vs = [BytesV bytes] else
    encode_create_ctor_args (get_tenv cx) (MAP expr_type ctor) vs = SOME bytes) /\
  blueprint_literal_offset cx salted (target_e::amount::(salts ++ offset::ctor)) =
    IS_SOME (expr_int_literal (origin_fold_value offset)) /\
  compile_create_blueprint_check (IS_SOME (expr_int_literal (origin_fold_value offset))) target off sb = (codep,sc) /\
  compile_create_blueprint_append target y sop off codep args_ptr cnt rof sc = (result,sf) /\
  fn_has_code sb sf func /\
  stmt_state_rel (H0 : (bool # 256 word # type_value) list # num list) ctx func cenv cx es0 s0 /\
  local_ptrs_reserved cenv sa0 /\ ci_mono sa0 sa /\
  wb_frame cenv es0 es sa0 s0 s /\ ghost_kept_at lo cenv es0 sa0 G0 tn0 s0 G tn /\
  s0.vs_alloca_next <= s.vs_alloca_next /\
  post_value_type cenv ^bp_call = BaseT AddressT /\ expr_has_effect ^bp_call /\
  (!av sv ov ee G1 tn1 t gs.
    (!tail. eval_exprs cx (amount::(salts ++ [offset])) (es with gas_obs := gs ++ tail) =
      (INL (av::((case sv of NONE => [] | SOME v => [v]) ++ [ov])),ee with gas_obs := tail)) /\
    wb_frame cenv es ee sa s t /\ ghost_kept_at lo cenv es sa G tn s G1 tn1 /\
    MAP FDOM es.scopes = MAP FDOM ee.scopes /\ s.vs_alloca_next <= t.vs_alloca_next /\
    alloca_history func t /\ (ctx_has_dalloca ctx ==> allocas_below_fmp t) /\
    ~t.vs_halted /\ t.vs_current_bb = sb.cs_current_bb /\ t.vs_inst_idx = LENGTH sb.cs_current_insts /\
    storage_trace_domain cx st0 ee.storage_trace /\
    (!H. valid_horizon cx st0 H ee.storage_trace ==>
      valid_horizon cx st0 H es.storage_trace /\ stmt_state_rel H ctx func cenv cx ee t /\
      immutable_frame_mods func cenv cx ee t /\ storage_well_formed_on cx ee (FST H) /\
      ghost_inv_at_mods (DF H) lo d cenv cx ee G1 tn1 t) ==>
    eval_operand cnt t = SOME (n2w (LENGTH bytes)) /\ op_taint tn1 cnt = {} /\ op_prov G1 cnt = NONE /\
    (cnt <> Lit 0w ==> ?q a. args_ptr = Var q /\ lookup_var q t = SOME a /\
      ptr_covers G1 tn1 q t (LENGTH bytes) /\ (bytes = [] \/ w2n a + LENGTH bytes <= t.vs_alloca_next) /\
      (!i. w2n a <= i /\ i < w2n a + LENGTH bytes ==> i NOTIN tn1.t_mem) /\
      read_memory (w2n a) (LENGTH bytes) t = bytes)) ==>
  gas_outcome_full_mods (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
    cenv.ce_modules cx st0
    (bind (eval_exprs cx (amount::(salts ++ [offset])))
      (\ws. (^bp_next) (HD ws) (if salted then SOME (EL 1 ws) else NONE) (LAST ws)))
    (es,s,G,tn) ^normal_post ^exit_post
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  qabbrev_tac `next = ^bp_next` >>
  irule blueprint_scalar_suffix_cut_mods >>
  rpt conj_tac >> TRY (first_assum ACCEPT_TAC)
  >- simp[NoAsms,Abbr `next`,storage_trace_frame_bind_all,storage_trace_frame_create_operands,
          storage_trace_frame_read_result] >>
  qpat_assum `expr_body_pre_mods _ _ _ _ (Call _ _ _ _) _` (irule_at Any) >>
  qpat_assum `lower_value _ _ _ amount sa = _` (irule_at Any) >>
  qpat_assum `lower_value _ _ _ (gas_shadow_expr amount) sh = _` (irule_at Any) >>
  qpat_assum `compile_create_salt _ cenv _ sm = _` (irule_at Any) >>
  qpat_assum `compile_create_salt _ (gas_shadow_env _ _) _ shm = _` (irule_at Any) >>
  qpat_assum `fn_has_code sn sb func` (irule_at Any) >>
  qpat_assum `fn_has_code shn shb shadow_func` (irule_at Any) >>
  qpat_assum `return_buf_frame d cenv sa s` (irule_at Any) >>
  qpat_assum `module_body_inv mods src tops cenv cx` (irule_at Any) >>
  qpat_assum `contract_inv mods exps ctx cenv cx` (irule_at Any) >>
  qpat_assum `eval_operand target s = _` (irule_at Any) >>
  qexistsl [`off`,`cnt`,`args_ptr`,`bytes`] >>
  rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
  qx_genl_tac [`av`,`sv`,`ov`,`yw`,`sw`,`ow`,`ee`,`G1`,`tn1`,`t`,`marks`] >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  suspend "scalar_landing"
QED

Resume blueprint_scalar_finish_mods[scalar_landing]:
  `MAP FDOM es0.scopes = MAP FDOM es.scopes` by
    (qpat_assum `wb_frame cenv es0 es sa0 s0 s` mp_tac >>
     simp[NoAsms,wb_frame_def,locals_kept_def]) >>
  `ci_mono sa sb` by metis_tac[ci_mono_trans] >>
  `ci_mono sa0 sb` by metis_tac[ci_mono_trans] >>
  `sa0.cs_next_var <= sa.cs_next_var /\ sa0.cs_next_id <= sa.cs_next_id` by
    (qpat_assum `ci_mono sa0 sa` mp_tac >> simp[NoAsms,ci_mono_def]) >>
  `wb_frame cenv es0 ee sa0 s0 t` by
    (irule (INST_TYPE [alpha |-> ``:256``] wb_frame_trans) >>
     qpat_assum `stmt_state_rel _ ctx func cenv cx es0 s0` (irule_at Any) >>
     qpat_assum `wb_frame cenv es ee sa s t` (irule_at Any) >>
     rpt conj_tac >> first_assum ACCEPT_TAC) >>
  `ghost_kept_at lo cenv es0 sa0 G0 tn0 s0 G1 tn1` by
    (qpat_assum `stmt_state_rel _ ctx func cenv cx es0 s0`
       (mp_then (Pat `stmt_state_rel _ _ _ _ _ _ _`) irule ghost_kept_at_wb_trans) >>
     qpat_assum `ghost_kept_at lo cenv es sa G tn s G1 tn1` (irule_at Any) >>
     qexists `es` >> rpt conj_tac >> first_assum ACCEPT_TAC) >>
  `s0.vs_alloca_next <= t.vs_alloca_next` by decide_tac >>
  `sa.cs_next_var <= sb.cs_next_var /\ sa0.cs_next_var <= sb.cs_next_var` by
    (qpat_assum `ci_mono sa sb` mp_tac >> qpat_assum `ci_mono sa0 sb` mp_tac >>
     simp[NoAsms,ci_mono_def]) >>
  `local_ptrs_reserved cenv sb` by metis_tac[local_ptrs_reserved_next_var] >>
  `!x k. cenv.ce_return_buf = SOME (PtrVar (Var x) k) ==> not_fresh_at sb x` by
    metis_tac[not_fresh_at_mono] >>
  `!x k. cenv.ce_return_pc = SOME (PtrVar (Var x) k) ==> not_fresh_at sb x` by
    metis_tac[not_fresh_at_mono] >>
  `accounts_well_typed ee.accounts /\ outcomes_accounts_typed ee.outcomes /\ IS_SOME ee.outcomes` by
    (qpat_assum `expr_sim_inv_mods mods cenv cx env ee` mp_tac >> simp[NoAsms,expr_sim_inv_mods_def]) >>
  `!H. valid_horizon cx st0 H ee.storage_trace ==>
    stmt_state_rel H ctx func cenv cx ee t /\ immutable_frame_mods func cenv cx ee t /\
    storage_well_formed_on cx ee (FST H) /\ ghost_inv_at_mods (DF H) lo d cenv cx ee G1 tn1 t` by
    (gen_tac >> disch_tac >>
     qpat_assum `!H. valid_horizon _ _ H ee.storage_trace ==> valid_horizon _ _ H es.storage_trace /\ _`
       (drule_then strip_assume_tac) >> simp[NoAsms] >> rpt conj_tac >> first_assum ACCEPT_TAC) >>
  qpat_assum `stmt_state_rel _ ctx func cenv cx es0 s0`
    (mp_then (Pat `stmt_state_rel _ _ _ _ _ _ _`) irule blueprint_prepared_mods) >>
  qpat_assum `compile_create_blueprint_check _ target off sb = _` (irule_at Any) >>
  qpat_assum `compile_create_blueprint_append target y sop off _ args_ptr cnt rof sc = _`
    (irule_at Any) >>
  qpat_assum `contract_inv mods exps ctx cenv cx` (irule_at Any) >>
  qpat_assum `eval_operand y t = SOME yw` (irule_at Any) >>
  qpat_assum `eval_operand off t = SOME ow` (irule_at Any) >>
  qpat_assum `eval_operand cnt t = SOME (n2w (LENGTH bytes))` (irule_at Any) >>
  qpat_assum `LENGTH bs = 20` (irule_at Any) >>
  qpat_assum `OPTREL _ sop sw` (irule_at Any) >>
  qpat_assum `ghost_kept_at lo cenv es0 sa0 G0 tn0 s0 G1 tn1`
    (irule_at Any) >>
  qpat_assum `return_buf_frame d cenv sb t` (irule_at Any) >>
  qabbrev_tac `code = (lookup_account (word_of_bytes_be bs) ee.accounts).code` >>
  qexistsl [`blueprint_copy_size (w2n ow) code`,`code`] >>
  rpt conj_tac >> TRY (first_assum ACCEPT_TAC)
  >- suspend "dispatch"
  >- suspend "source"
  >> simp[NoAsms,Abbr `code`]
QED

Resume blueprint_scalar_finish_mods[source]:
  `LENGTH salts = (if salted then 1 else 0)` by
    (qpat_assum `if salted then _ else salts = []` mp_tac >>
     Cases_on `salted` >> simp[NoAsms] >> strip_tac >> simp[]) >>
  gen_tac >>
  simp[NoAsms,Abbr `next`,Abbr `code`,LENGTH_APPEND] >>
  qpat_assum `blueprint_literal_offset _ _ _ = _` (pure_once_rewrite_tac o single) >>
  qpat_assum `IS_SOME sv = salted` (pure_once_rewrite_tac o single o SYM) >>
  qpat_assum `dest_AddressV target_v = SOME _`
    (mp_then (Pat `dest_AddressV _ = _`) (fn cut =>
      dep_rewrite.DEP_ONCE_REWRITE_TAC [Q.INST [`sw` |-> `sw`, `value` |-> `w2n (yw:256 word)`,
        `off` |-> `w2n (ow:256 word)`, `bytes` |-> `bytes`,
        `code` |-> `(lookup_account (word_of_bytes_be bs) ee.accounts).code`] (SPEC_ALL cut)])
      blueprint_scalar_read_prepared) >>
  qpat_assum `IS_SOME sv = salted` (fn salt => simp[NoAsms,salt]) >>
  rpt conj_tac >> first_assum ACCEPT_TAC
QED

Resume blueprint_scalar_finish_mods[dispatch]:
  qx_genl_tac [`sd`,`p`,`len`,`u`,`Gu`,`tnu`,`pv`,`sz`] >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  qpat_assum `compile_create_dispatch (Var p) len y sop rof sd = _`
    (mp_then Any irule create_dispatch_outcome_full_mods) >>
  qpat_assum `wb_frame cenv es0 ee sa0 s0 u` (irule_at Any) >>
  qpat_assum `eval_operand (Var p) u = SOME pv` (irule_at Any) >>
  qpat_assum `eval_operand len u = SOME sz` (irule_at Any) >>
  qpat_assum `eval_operand y u = SOME yw` (irule_at Any) >>
  qpat_assum `read_memory (w2n pv) (w2n sz) u = _` (irule_at Any) >>
  qexists `sw` >>
  rpt conj_tac >> TRY (first_assum ACCEPT_TAC)
  >- (disch_tac >> first_assum ACCEPT_TAC)
  >- (disch_tac >> qexists `p` >> simp[])
  >- (disch_tac >> disj2_tac >> rpt conj_tac >> first_assum ACCEPT_TAC) >>
  qpat_x_assum `OPTREL (\op w. eval_operand op u = SOME w /\ op_taint tnu op = {}) sop sw` mp_tac >>
  Cases_on `sop` >> Cases_on `sw` >> simp[NoAsms,optionTheory.OPTREL_THM]
QED

Finalise blueprint_scalar_finish_mods
