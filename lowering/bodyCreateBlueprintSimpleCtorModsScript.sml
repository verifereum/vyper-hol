(* Reached raw and empty constructor branches of blueprint creation. *)
Theory bodyCreateBlueprintSimpleCtorMods
Ancestors
  bodyCreateBlueprintRawArgsMods bodyFullPredsMods bodyFullPostsMods
  exprLowering compileEnv gasShadowCompile exprSimWordArgs wordArgsPtr
  fragGasOriginPtr vyperStorageFootprint vyperStorageTrace vyperInterpreter
  vyperCreate vyperABI ptrDiscipline venomState vyperState
Libs monadsyntax

val later = ``(amount:expr)::(salts ++ [offset])``;
val body_context = ``body_const_cells_agree_mods mods cx env es /\
  contract_inv mods exps ctx cenv cx /\ module_body_inv mods src tops cenv cx /\
  shadow_body_inv_mods mods exps ctx shadow_ctx``;
val entry = ``gas_shadow_state sa sh /\ gas_shadow_state sb shb /\
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
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\ s.vs_inst_idx = LENGTH sa.cs_current_insts``;
val landed = ``LENGTH (bs:word8 list) < 2 ** 64 /\
  (!tail. eval_exprs cx ctor (es with gas_obs := gas_explicit marks s.vs_gas_readings ++ tail) =
    (INL vs,ee with gas_obs := tail)) /\
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
    immutable_frame_mods func cenv cx ee u /\ storage_well_formed_on cx ee (FST H) /\
    ghost_inv_at_mods (DF H) lo d cenv cx ee Gu tu u /\
    gas_origin_ptr_path (DF H,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
      (s,G,tn) marks (OK u,Gu,tu))``;
(* The payload certificate is conditional on the actual successful scalar replay,
   so it requires no assumption that the scalar suffix will return normally. *)
val saved_for_suffix = ``!ws ef Gf tf f gs.
  (!tail. eval_exprs cx ^later (ee with gas_obs := gs ++ tail) = (INL ws,ef with gas_obs := tail)) /\
  wb_frame cenv ee ef sb u f /\ ghost_kept_at lo cenv ee sb Gu tu u Gf tf /\
  MAP FDOM ee.scopes = MAP FDOM ef.scopes /\ u.vs_alloca_next <= f.vs_alloca_next /\
  storage_trace_domain cx st0 ef.storage_trace /\
  (!H. valid_horizon cx st0 H ef.storage_trace ==>
    valid_horizon cx st0 H ee.storage_trace /\ stmt_state_rel H ctx func cenv cx ef f /\
    immutable_frame_mods func cenv cx ef f /\ storage_well_formed_on cx ef (FST H) /\
    ghost_inv_at_mods (DF H) lo d cenv cx ef Gf tf f) ==>
  eval_operand cnt f = SOME (n2w (LENGTH bs)) /\ op_taint tf cnt = {} /\ op_prov Gf cnt = NONE /\
  (cnt <> Lit 0w ==> ?q a. data = Var q /\ lookup_var q f = SOME a /\
    ptr_covers Gf tf q f (LENGTH bs) /\ (bs = [] \/ w2n a + LENGTH bs <= f.vs_alloca_next) /\
    (!i. w2n a <= i /\ i < w2n a + LENGTH bs ==> i NOTIN tf.t_mem) /\
    read_memory (w2n a) (LENGTH bs) f = bs)``;
val linked_exit = ``\(H : (bool # 256 word # type_value) list # num list)
  (res:value + exception) ef (gt:(string |-> num # num) # taint) r.
  expr_exit res r /\ halt_exit H cx ef res r /\
  (ctx_has_dalloca ctx ==> !z. r = Halt z ==> allocas_below_fmp z)``;

Theorem blueprint_raw_ctor_continue_mods:
  ^body_context /\ ctor = [e] /\
  expr_body_pre_mods mods cenv cx env e es /\ body_expr_full_ok_mods mods exps cx e /\
  expr_type e = BaseT (BytesT (Dynamic cap)) /\
  compile_create_blueprint_args compile_expr cenv T ^later ctor sa = ((data,cnt),sb) /\
  compile_create_blueprint_args compile_expr (gas_shadow_env T cenv) T (MAP gas_shadow_expr ^later)
    (MAP gas_shadow_expr ctor) sh = ((data,cnt),shb) /\
  ^entry /\ (!vs. storage_trace_frame (next vs)) /\
  (!vs bs ee Gu tu u marks.
    vs = [BytesV bs] /\ ^landed /\ ^saved_for_suffix ==>
    gas_outcome_full_mods (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG) cenv.ce_modules cx st0 (next vs) (ee,u,Gu,tu) Q ^linked_exit) ==>
  gas_outcome_full_mods (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG) cenv.ce_modules cx st0
    (bind (eval_exprs cx ctor) next) (es,s,G,tn) Q ^linked_exit
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  qpat_x_assum `ctor = [e]` SUBST_ALL_TAC >>
  qpat_x_assum `compile_create_blueprint_args _ _ T _ (MAP gas_shadow_expr [e]) _ = _`
    (assume_tac o CONV_RULE
       (LAND_CONV (RATOR_CONV (RAND_CONV (SIMP_CONV bool_ss [listTheory.MAP]))))) >>
  irule blueprint_raw_args_cut_mods >>
  qpat_assum `compile_create_blueprint_args _ _ T _ [e] sa = _` (irule_at Any) >>
  qpat_assum `compile_create_blueprint_args _ _ T _ [gas_shadow_expr e] sh = _` (irule_at Any) >>
  rpt (first_assum (irule_at Any)) >>
  rpt (conj_tac ORELSE first_assum ACCEPT_TAC) >>
  qx_genl_tac [`bs`,`ee`,`Gu`,`tu`,`u`,`marks`] >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  qpat_assum `!vs bs ee Gu tu u marks. _ ==> gas_outcome_full_mods _ _ _ _ _ _ _ _`
    (qspecl_then [`[BytesV bs]`,`bs`] irule) >>
  rpt (conj_tac ORELSE first_assum ACCEPT_TAC ORELSE REFL_TAC) >>
  qexists_tac `marks` >> rpt (conj_tac ORELSE first_assum ACCEPT_TAC)
QED

Theorem blueprint_empty_ctor_continue_mods:
  ^body_context /\ ctor = [] /\ expr_sim_inv_mods mods cenv cx env es /\
  storage_trace_domain cx st0 es.storage_trace /\
  compile_create_blueprint_args compile_expr cenv F ^later ctor sa = ((data,cnt),sb) /\
  compile_create_blueprint_args compile_expr (gas_shadow_env T cenv) F (MAP gas_shadow_expr ^later)
    (MAP gas_shadow_expr ctor) sh = ((data,cnt),shb) /\
  ^entry /\
  (!vs bs ee Gu tu u marks.
    encode_create_ctor_args (get_tenv cx) (MAP expr_type ctor) vs = SOME bs /\
    ^landed /\ ^saved_for_suffix ==>
    gas_outcome_full_mods (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG) cenv.ce_modules cx st0 (next vs) (ee,u,Gu,tu) Q ^linked_exit) ==>
  gas_outcome_full_mods (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG) cenv.ce_modules cx st0
    (bind (eval_exprs cx ctor) next) (es,s,G,tn) Q ^linked_exit
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  qpat_x_assum `ctor = []` SUBST_ALL_TAC >>
  ntac 2 (qpat_x_assum `compile_create_blueprint_args _ _ F _ _ _ = _`
    (strip_assume_tac o SIMP_RULE (srw_ss()) [compile_create_blueprint_args_def,comp_return_def])) >>
  gvs[NoAsms] >>
  `eval_exprs cx [] = return []` by simp[FUN_EQ_THM,eval_exprs_nil,return_def] >>
  simp[bind_return] >>
  qpat_assum `!vs bs ee Gu tu u marks. _ ==> gas_outcome_full_mods _ _ _ _ _ _ _ _`
    (qspecl_then [`[]`,`[]`] irule) >>
  `encode_create_ctor_args (get_tenv cx) [] [] = SOME []` by EVAL_TAC >>
  simp[eval_exprs_nil,wb_frame_refl,ghost_kept_at_refl,eval_operand_def,op_taint_def] >>
  conj_tac >- first_assum ACCEPT_TAC >>
  qexists_tac `[]` >> simp[gas_origin_ptr_path_rules] >>
  gen_tac >> disch_tac >>
  qpat_assum `!H. valid_horizon cx st0 H es.storage_trace ==> stmt_state_rel _ _ _ _ _ _ _ /\ _`
    (drule_then strip_assume_tac) >> simp[]
QED
