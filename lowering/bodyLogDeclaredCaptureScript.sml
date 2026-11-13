(* Declared field capture for aggregate Log execution. *)
Theory bodyLogDeclaredCapture
Ancestors
  bodySimLogArgs stmtSimLogArgsRun stmtSimLogArgs stmtLogArgsMemory bodyMemoryPreds
  bodyPtrSubscriptSeamTupleLayoutBridge eventLoweringStructure exprSimIfExpCompat
  bodyExprPreFacts supportedExprs supportedExprTraverse vyperTypeInvariants
  exprSimMemDefs exprSimHypsDefs exprSimHyps exprSimProps exprSimSource
  exprLowering stmtSimProps loweringPosts
  compileEnv vyperInterpreter vyperState vyperTypeSystem vyperTyping
  allocLimits exprSimHashBoundary stmtSimAssignStorageCopy valueEncodingTyping
  gasOutcome gasSummary list
Libs
  monadsyntax

Theorem body_log_declared_capture:
EVERY (\e. body_stmt_safe tops (Expr e) /\ ~is_extcode e) args /\
body_inv tops ctx cenv cx /\ body_exprs_ok cx args /\
supported_pure_exprs tops args /\ well_typed_exprs env args /\
~supported_exprs_exists
  (\e. ~is_extcode e /\
       ~(byte_widths_expr e /\ alloc_limits_expr cenv e)) args /\
call_evaluation_safe cx (int_calls_exprs args) /\
(!target. supported_exprs_exists (expr_abi_decode_target_root target) args ==>
          occurs_abi_decode_target target tops) /\
supported_event_fields tops id = SOME fields /\
LIST_REL (\e ((name,dty),indexed).
  event_arg_compatible dty (expr_type e)) args fields /\
log_alloc_ok cenv id args /\
compile_log_eval_all cenv args sa = (ops,sb) /\
gas_admissible (eval_exprs cx args) log_args_res_ok es /\
fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
local_ptrs_reserved cenv sa /\ expr_sim_inv cenv cx env es /\
(!id ty. FLOOKUP env.var_types id = SOME ty ==>
  ?p sz. FLOOKUP cenv.ce_vars id = SOME (PtrVar (Var p) sz)) /\
stmt_state_rel ctx func cenv cx es s0 /\ ~s0.vs_halted /\
s0.vs_current_bb = sa.cs_current_bb /\
s0.vs_inst_idx = LENGTH sa.cs_current_insts ==>
gas_outcome F (cx_tops cx) (ctx,func) (eval_exprs cx args) (es,s0)
  (\res ee t. ?vs. res = INL vs /\
    stmt_state_rel ctx func cenv cx ee t /\
    wb_frame cenv es ee sa s0 t /\ ee.scopes = es.scopes /\
    t.vs_current_bb = sb.cs_current_bb /\
    t.vs_inst_idx = LENGTH sb.cs_current_insts /\
    LENGTH ops = LENGTH args /\ LENGTH args = LENGTH fields /\
    MAP SND ops = MAP (lowered_value_type cenv) args /\
    EVERY (\p. (!x. FST p = Var x ==> not_fresh_at sb x) /\
               (!lab. FST p <> Label lab)) ops /\
    LIST_REL (\((op,sty),(e,((name,dty),indexed))) v.
      event_arg_compatible dty (expr_type e) /\
      (~is_word_type dty /\ ~is_bytestring_type dty ==>
        sty = expr_type e) /\
      (?ltv. evaluate_type (get_tenv cx) (expr_type e) = SOME ltv /\
        value_has_type ltv v /\ val_wf ltv v) /\
      expr_val_rel cx (expr_type e) v op t /\
      expr_val_at cenv cx (expr_type e) sa sb ee v op t /\
      (!w tv. ~is_word_type (expr_type e) /\
        ~is_bytestring_type (expr_type e) /\
        eval_operand op t = SOME w /\
        evaluate_type (get_tenv cx) (expr_type e) = SOME tv ==>
        w2n w + type_memory_size tv < dimword (:256)) /\
      (~indexed ==>
        type_widens_to (get_tenv cx) (expr_type e) dty /\
        ?dtv. evaluate_type (get_tenv cx) dty = SOME dtv /\
          value_has_type dtv v /\ val_wf dtv v))
      (ZIP (ops, ZIP (args,fields))) vs)
  (\res ee r. expr_exit res r)

Proof
  rpt strip_tac >>
  `env.type_defs = get_tenv cx /\ env_consistent env cx es` by
    fs[expr_sim_inv_def, env_consistent_def, env_context_consistent_def] >>
  `(!id ty. FLOOKUP env.var_types id = SOME ty ==>
      well_formed_type env.type_defs ty) /\
    sfields_tenv_consistent cenv.ce_struct_fields env.type_defs /\
    (!fid sig. FLOOKUP env.fn_sigs fid = SOME sig ==>
      cenv.ce_func_return_type (nsid_to_string fid) = sig.ret_ty)` by
    (simp[] >> conj_tac
     >- (rpt strip_tac >> simp[well_formed_type_def] >>
         metis_tac[env_consistent_var_type_evaluates]) >>
     fs[expr_sim_inv_def]) >>
  `!e. MEM e args /\ ~is_bytestring_type (expr_type e) ==>
       lowered_value_type cenv e = expr_type e` by
    (rpt strip_tac >>
     `well_typed_expr env e /\ supported_pure_expr tops e` by
       (fs[supported_pure_exprs_every, EVERY_MEM] >>
        metis_tac[well_typed_exprs_member]) >>
     qspecl_then [`cenv`, `e`, `env`] mp_tac ifexp_lowered_type_classify >>
     impl_tac >- simp[] >>
     strip_tac >> gvs[supported_pure_expr_def]) >>
  `LENGTH ops = LENGTH args /\ LENGTH args = LENGTH fields /\
   MAP SND ops = MAP (lowered_value_type cenv) args` by
    (mp_tac (Q.SPECL [`cenv`, `args`, `sa`] compile_log_eval_all_types) >>
     mp_tac (Q.SPECL [`cenv`, `args`, `sa`] compile_log_eval_all_length) >>
     simp[] >> metis_tac[LIST_REL_LENGTH]) >>
  drule_all body_log_aggregate_metadata >> strip_tac >>
  `SUM (MAP (type_memory_bytes cenv)
      (log_non_indexed_types (MAP SND fields) (MAP (SND o FST) fields))) <
      2 ** 64` by fs[log_alloc_ok_def] >>
  `!fs name ty. MEM ((name,ty),F) fs ==>
    MEM ty (log_non_indexed_types (MAP SND fs) (MAP (SND o FST) fs))` by
    (Induct_on `fs` >> simp[log_non_indexed_types_def] >>
     qx_gen_tac `field_item` >> PairCases_on `field_item` >> Cases_on `field_item2` >>
     simp[log_non_indexed_types_def, combinTheory.o_DEF] >> metis_tac[]) >>
  `!name ty. MEM ((name,ty),F) fields ==> type_memory_bytes cenv ty < 2 ** 64` by
    (rpt strip_tac >>
     `MEM ty (log_non_indexed_types (MAP SND fields) (MAP (SND o FST) fields))`
       by metis_tac[] >>
     drule (Q.ISPEC `type_memory_bytes cenv` SUM_MAP_MEM_bound) >> decide_tac) >>
  qabbrev_tac `RR = \tail s.
    log_args_ready ctx func cenv cx (\s. expr_sim_inv cenv cx env s) tail /\
    supported_pure_exprs tops tail /\ expr_sim_inv cenv cx env s` >>
  `log_args_ready ctx func cenv cx (\s. expr_sim_inv cenv cx env s) args` by
    (irule body_log_args_ready >> simp[] >> metis_tac[]) >>
  `RR args es` by simp[Abbr `RR`] >>
  `~exprs_can_mutate cenv args` by
    metis_tac[supported_pure_expr_no_mutate] >>
  qspecl_then [`args`, `ctx`, `func`, `cenv`, `cx`, `RR`, `es`, `sa`,
    `ZIP (MAP FST ops, MAP expr_type args)`, `sb`, `s0`, `env`, `env`, `es`, `ops`]
    mp_tac compile_log_eval_all_pure_gas >>
  impl_tac
  >- (simp[] >> rpt conj_tac
      >- (simp[Abbr `RR`] >> rpt strip_tac >>
          drule_all body_log_args_pure_step >> simp[])
      >- simp[Abbr `RR`] >>
      metis_tac[log_capture_cons_scopes]) >>
  disch_then assume_tac >>
  irule gas_outcome_post_mono >> goal_assum (drule_at Any) >>
  rpt strip_tac >>
  `LENGTH args = LENGTH vs` by metis_tac[LIST_REL_LENGTH, LENGTH_MAP] >>
  qexists_tac `vs` >> asm_rewrite_tac [] >> conj_tac
  >- (gvs[EVERY_EL, EL_ZIP, EL_MAP] >> rpt strip_tac >> metis_tac[]) >>
  simp[LIST_REL_EL_EQN, EL_ZIP] >> gen_tac >> strip_tac >>
  `n < LENGTH args /\ n < LENGTH ops /\ n < LENGTH fields` by simp[] >>
  Cases_on `EL n ops` >> rename1 `EL n ops = (op,sty)` >>
  Cases_on `EL n fields` >> rename1 `EL n fields = (field,indexed)` >>
  Cases_on `field` >> rename1 `EL n fields = ((name,dty),indexed)` >>
  `event_arg_compatible dty (expr_type (EL n args)) /\
   expr_val_rel cx (expr_type (EL n args)) (EL n vs) op t /\
   expr_val_at cenv cx (expr_type (EL n args)) sa sb ee (EL n vs) op t /\
   ?ltv. evaluate_type (get_tenv cx) (expr_type (EL n args)) = SOME ltv /\
         value_has_type ltv (EL n vs)` by
    (fs[LIST_REL_EL_EQN, EL_ZIP, EL_MAP] >> metis_tac[]) >>
  `sty = lowered_value_type cenv (EL n args)` by
    (qpat_x_assum `MAP SND ops = _` (mp_tac o Q.AP_TERM `EL n`) >>
     simp[EL_MAP]) >>
  `~is_word_type dty /\ ~is_bytestring_type dty ==>
    sty = expr_type (EL n args)` by
    metis_tac[log_compatible_aggregate_source, MEM_EL] >>
  `val_wf ltv (EL n vs)` by metis_tac[value_has_type_val_wf] >>
  `~indexed ==>
    type_widens_to (get_tenv cx) (expr_type (EL n args)) dty /\
    ?dtv. evaluate_type (get_tenv cx) dty = SOME dtv /\
      value_has_type dtv (EL n vs) /\ val_wf dtv (EL n vs)` by
    (strip_tac >> gvs[] >>
     `type_memory_bytes cenv dty < 2 ** 64` by metis_tac[MEM_EL] >>
     `arg_type_fits (expr_type (EL n args)) dty` by
       fs[event_arg_compatible_alias_def] >>
     `IS_SOME (evaluate_type (get_tenv cx) dty)` by
       metis_tac[CONJUNCT1 log_compatible_bounded_evaluation] >>
     Cases_on `evaluate_type (get_tenv cx) dty` >> gvs[] >>
     metis_tac[log_compatible_evaluated_widening, log_compatible_declared_value]) >>
  `!w tv. ~is_word_type (expr_type (EL n args)) /\
     ~is_bytestring_type (expr_type (EL n args)) /\
     eval_operand op t = SOME w /\
     evaluate_type (get_tenv cx) (expr_type (EL n args)) = SOME tv ==>
     w2n w + type_memory_size tv < dimword (:256)` by
    (rpt strip_tac >>
     `val_footprint tv (EL n vs) = type_memory_size tv` by
       metis_tac[topcopy_val_footprint] >>
     `w2n w + val_footprint tv (EL n vs) < dimword (:256)` by
       (Cases_on `val_footprint tv (EL n vs) = 0` >- simp[w2n_lt] >>
        drule_all expr_val_at_footprint >> strip_tac
        >- (irule hash_live_footprint_bound >> goal_assum (drule_at Any) >> metis_tac[])
        >- (irule hash_live_footprint_bound >> goal_assum (drule_at Any) >> metis_tac[]) >>
        gvs[]) >> gvs[]) >>
  simp[] >> metis_tac[]
QED

Theorem body_log_declared_capture_mem:
EVERY (\e. body_stmt_safe tops (Expr e) /\ ~is_extcode e) args /\
body_inv tops ctx cenv cx /\ body_exprs_mem_ok cx args /\
supported_pure_exprs tops args /\ well_typed_exprs env args /\
~supported_exprs_exists
  (\e. ~is_extcode e /\
       ~(byte_widths_expr e /\ alloc_limits_expr cenv e)) args /\
call_evaluation_safe cx (int_calls_exprs args) /\
(!target. supported_exprs_exists (expr_abi_decode_target_root target) args ==>
          occurs_abi_decode_target target tops) /\
supported_event_fields tops id = SOME fields /\
LIST_REL (\e ((name,dty),indexed).
  event_arg_compatible dty (expr_type e)) args fields /\
log_alloc_ok cenv id args /\
compile_log_eval_all cenv args sa = (ops,sb) /\
gas_admissible (eval_exprs cx args)
  (\r. !exc. r = INR exc ==> expr_res_ok (INR exc : value + exception)) es /\
fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
local_ptrs_reserved cenv sa /\ expr_sim_inv cenv cx env es /\
(!id ty. FLOOKUP env.var_types id = SOME ty ==>
  ?p sz. FLOOKUP cenv.ce_vars id = SOME (PtrVar (Var p) sz)) /\
stmt_state_rel ctx func cenv cx es s0 /\ alloca_history func s0 /\
~s0.vs_halted /\ s0.vs_current_bb = sa.cs_current_bb /\
s0.vs_inst_idx = LENGTH sa.cs_current_insts ==>
gas_outcome T (cx_tops cx) (ctx,func) (eval_exprs cx args) (es,s0)
  (\res ee t. ?vs. res = INL vs /\
    stmt_state_rel ctx func cenv cx ee t /\
    wb_frame cenv es ee sa s0 t /\ ee.scopes = es.scopes /\
    t.vs_current_bb = sb.cs_current_bb /\
    t.vs_inst_idx = LENGTH sb.cs_current_insts /\
    alloca_history func t /\ s0.vs_alloca_next <= t.vs_alloca_next /\
    LENGTH ops = LENGTH args /\ LENGTH args = LENGTH fields /\
    MAP SND ops = MAP (lowered_value_type cenv) args /\
    EVERY (\p. (!x. FST p = Var x ==> not_fresh_at sb x) /\
               (!lab. FST p <> Label lab)) ops /\
    LIST_REL (\((op,sty),(e,((name,dty),indexed))) v.
      event_arg_compatible dty (expr_type e) /\
      (~is_word_type dty /\ ~is_bytestring_type dty ==>
        sty = expr_type e) /\
      (?ltv. evaluate_type (get_tenv cx) (expr_type e) = SOME ltv /\
        value_has_type ltv v /\ val_wf ltv v) /\
      expr_val_rel cx (expr_type e) v op t /\
      expr_val_at cenv cx (expr_type e) sa sb ee v op t /\
      expr_store_bound cx (expr_type e) v op t /\
      (~indexed ==>
        type_widens_to (get_tenv cx) (expr_type e) dty /\
        ?dtv. evaluate_type (get_tenv cx) dty = SOME dtv /\
          value_has_type dtv v /\ val_wf dtv v))
      (ZIP (ops, ZIP (args,fields))) vs)
  (\res ee r. expr_exit res r)

Proof
  rpt strip_tac >>
  `env.type_defs = get_tenv cx /\ env_consistent env cx es` by
    fs[expr_sim_inv_def, env_consistent_def, env_context_consistent_def] >>
  `(!id ty. FLOOKUP env.var_types id = SOME ty ==>
      well_formed_type env.type_defs ty) /\
    sfields_tenv_consistent cenv.ce_struct_fields env.type_defs /\
    (!fid sig. FLOOKUP env.fn_sigs fid = SOME sig ==>
      cenv.ce_func_return_type (nsid_to_string fid) = sig.ret_ty)` by
    (simp[] >> conj_tac
     >- (rpt strip_tac >> simp[well_formed_type_def] >>
         metis_tac[env_consistent_var_type_evaluates]) >>
     fs[expr_sim_inv_def]) >>
  `!e. MEM e args /\ ~is_bytestring_type (expr_type e) ==>
       lowered_value_type cenv e = expr_type e` by
    (rpt strip_tac >>
     `well_typed_expr env e /\ supported_pure_expr tops e` by
       (fs[supported_pure_exprs_every, EVERY_MEM] >>
        metis_tac[well_typed_exprs_member]) >>
     qspecl_then [`cenv`, `e`, `env`] mp_tac ifexp_lowered_type_classify >>
     impl_tac >- simp[] >>
     strip_tac >> gvs[supported_pure_expr_def]) >>
  `LENGTH ops = LENGTH args /\ LENGTH args = LENGTH fields /\
   MAP SND ops = MAP (lowered_value_type cenv) args` by
    (mp_tac (Q.SPECL [`cenv`, `args`, `sa`] compile_log_eval_all_types) >>
     mp_tac (Q.SPECL [`cenv`, `args`, `sa`] compile_log_eval_all_length) >>
     simp[] >> metis_tac[LIST_REL_LENGTH]) >>
  drule_all body_log_aggregate_metadata >> strip_tac >>
  `SUM (MAP (type_memory_bytes cenv)
      (log_non_indexed_types (MAP SND fields) (MAP (SND o FST) fields))) <
      2 ** 64` by fs[log_alloc_ok_def] >>
  `!fs name ty. MEM ((name,ty),F) fs ==>
    MEM ty (log_non_indexed_types (MAP SND fs) (MAP (SND o FST) fs))` by
    (Induct_on `fs` >> simp[log_non_indexed_types_def] >>
     qx_gen_tac `field_item` >> PairCases_on `field_item` >> Cases_on `field_item2` >>
     simp[log_non_indexed_types_def, combinTheory.o_DEF] >> metis_tac[]) >>
  `!name ty. MEM ((name,ty),F) fields ==> type_memory_bytes cenv ty < 2 ** 64` by
    (rpt strip_tac >>
     `MEM ty (log_non_indexed_types (MAP SND fields) (MAP (SND o FST) fields))`
       by metis_tac[] >>
     drule (Q.ISPEC `type_memory_bytes cenv` SUM_MAP_MEM_bound) >> decide_tac) >>
  qabbrev_tac `RR = \tail s.
    EVERY (\e. body_stmt_safe tops (Expr e) /\ ~is_extcode e) tail /\
    body_exprs_mem_ok cx tail /\ expr_sim_inv cenv cx env s /\
    supported_pure_exprs tops tail /\ well_typed_exprs env tail /\
    ~supported_exprs_exists (\e. ~is_extcode e /\
      ~(byte_widths_expr e /\ alloc_limits_expr cenv e)) tail /\
    call_evaluation_safe cx (int_calls_exprs tail) /\
    (!target. supported_exprs_exists (expr_abi_decode_target_root target) tail ==>
      occurs_abi_decode_target target tops)` >>
  `RR args es` by simp[Abbr `RR`] >>
  `~exprs_can_mutate cenv args` by
    metis_tac[supported_pure_expr_no_mutate] >>
  qspecl_then [`args`, `ctx`, `func`, `cenv`, `cx`, `RR`, `es`, `sa`,
    `ZIP (MAP FST ops, MAP expr_type args)`, `sb`, `s0`, `env`, `env`, `es`, `ops`]
    mp_tac compile_log_eval_all_pure_gas_mem >>
  impl_tac
  >- (simp[] >> rpt conj_tac
      >- (simp[Abbr `RR`] >> rpt strip_tac >>
          drule_all body_log_mem_args_pure_step >> simp[])
      >- simp[Abbr `RR`] >>
      metis_tac[log_capture_cons_scopes]) >>
  disch_then assume_tac >>
  irule gas_outcome_post_mono >> goal_assum (drule_at Any) >>
  rpt strip_tac >>
  `LENGTH args = LENGTH vs` by metis_tac[LIST_REL_LENGTH, LENGTH_MAP] >>
  qexists_tac `vs` >> asm_rewrite_tac [] >> conj_tac
  >- (gvs[EVERY_EL, EL_ZIP, EL_MAP] >> rpt strip_tac >> metis_tac[]) >>
  simp[LIST_REL_EL_EQN, EL_ZIP] >> gen_tac >> strip_tac >>
  `n < LENGTH args /\ n < LENGTH ops /\ n < LENGTH fields` by simp[] >>
  Cases_on `EL n ops` >> rename1 `EL n ops = (op,sty)` >>
  Cases_on `EL n fields` >> rename1 `EL n fields = (field,indexed)` >>
  Cases_on `field` >> rename1 `EL n fields = ((name,dty),indexed)` >>
  `event_arg_compatible dty (expr_type (EL n args)) /\
   expr_val_rel cx (expr_type (EL n args)) (EL n vs) op t /\
   expr_val_at cenv cx (expr_type (EL n args)) sa sb ee (EL n vs) op t /\
   ?ltv. evaluate_type (get_tenv cx) (expr_type (EL n args)) = SOME ltv /\
         value_has_type ltv (EL n vs)` by
    (fs[LIST_REL_EL_EQN, EL_ZIP, EL_MAP] >> metis_tac[]) >>
  `sty = lowered_value_type cenv (EL n args)` by
    (qpat_x_assum `MAP SND ops = _` (mp_tac o Q.AP_TERM `EL n`) >>
     simp[EL_MAP]) >>
  `~is_word_type dty /\ ~is_bytestring_type dty ==>
    sty = expr_type (EL n args)` by
    metis_tac[log_compatible_aggregate_source, MEM_EL] >>
  `val_wf ltv (EL n vs)` by metis_tac[value_has_type_val_wf] >>
  `~indexed ==>
    type_widens_to (get_tenv cx) (expr_type (EL n args)) dty /\
    ?dtv. evaluate_type (get_tenv cx) dty = SOME dtv /\
      value_has_type dtv (EL n vs) /\ val_wf dtv (EL n vs)` by
    (strip_tac >> gvs[] >>
     `type_memory_bytes cenv dty < 2 ** 64` by metis_tac[MEM_EL] >>
     `arg_type_fits (expr_type (EL n args)) dty` by
       fs[event_arg_compatible_alias_def] >>
     `IS_SOME (evaluate_type (get_tenv cx) dty)` by
       metis_tac[CONJUNCT1 log_compatible_bounded_evaluation] >>
     Cases_on `evaluate_type (get_tenv cx) dty` >> gvs[] >>
     metis_tac[log_compatible_evaluated_widening, log_compatible_declared_value]) >>
  `expr_store_bound cx (expr_type (EL n args)) (EL n vs) op t` by
    (fs[LIST_REL_EL_EQN, EL_ZIP, EL_MAP] >> metis_tac[]) >>
  simp[] >> metis_tac[]
QED
