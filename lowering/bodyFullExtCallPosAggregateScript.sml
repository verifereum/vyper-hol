(* The nonmutating aggregate snapshot emits no instructions. The source
   still performs its immediate read at the child's physical endpoint. *)
Theory bodyFullExtCallPosAggregate
Ancestors
  bodyFullShadowBodyInv
  bodyFullPreds bodySimFull gasOutcomeFullCompose gasOutcomeFull
  exprSimUnwrap exprSimMemorySource exprSimSource exprSimHyps exprSimProps
  exprPtrUnwrapStorageShape targetPureSourceFrame fragGasOriginPtr fragExec
  loweringPosts bodyPtrDefs bodyMemoryDefs compileEnv exprLowering
  contextRawReachable ptrDiscipline unitTransformDefs vyperStorageTrace
  vyperStorageFootprint vyperState stmtSimProps exprSimDefs context exprSimMemDefs
  exprSimHypsDefs abiEncodeArgsCase abiEncodeArgsSim abiEncodeMaterialize aggregateEvaluatedLayout
  valueCopyBytes exprReasonOperand bodyFullAssign vyperEvalExprPreservesScopesDom
  vyperTypeExprSoundness vyperTypeInvariants exprSimConcatResult exprNamedConstResult
  exprSimSend[qualified,ignore_grammar] abiBuiltinDispatchCorrect
  list[qualified,ignore_grammar]

(* A stack result keeps its compiler tag when staged. The only forms
   with a narrowed physical type return a pointer or use the call's
   declared result type. *)
Theorem extcall_operand_snapshot_type:
  expr_body_pre cenv cx env e es /\
  compile_expr cenv (expr_type e) e sa = (vv,sm) ==>
  vv_type (ext_call_arg_value (lowered_value_type cenv e) vv) =
    lowered_value_type cenv e
Proof
  strip_tac >> namedCases_on `vv` ["tag op", "tag p"] >>
  simp[ext_call_arg_value_def, vv_type_def] >>
  Cases_on `lowered_value_type cenv e = expr_type e`
  >- (`well_typed_expr env e /\
       (!id t. FLOOKUP env.var_types id = SOME t ==>
         ?p sz. FLOOKUP cenv.ce_vars id = SOME (PtrVar (Var p) sz))` by
        fs[expr_body_pre_def, expr_sim_inv_def] >>
      `reason_uniform_shape compile_expr cenv (expr_type e) e` by
        metis_tac[compile_expr_reason_uniform] >>
      qpat_x_assum `reason_uniform_shape _ _ _ _`
        (strip_assume_tac o REWRITE_RULE [reason_uniform_shape_def]) >>
      qpat_x_assum `!sa vv sb. _ ==> reason_result_shape _ _ _`
        (drule_then assume_tac) >>
      gvs[reason_result_shape_def]) >>
  `(?n st. e = Literal (BaseT (StringT n)) (StringL st)) \/
   (?n bs. e = Literal (BaseT (BytesT (Dynamic n))) (BytesL bs)) \/
   (?n bs. e = Literal (BaseT (BytesT (Dynamic n))) (HexBytesL bs)) \/
   (?ann n args. e = Builtin ann (Concat n) args) \/
   (?ann en method tys args. e = TypeBuiltin ann (AbiEncode en method) tys args) \/
   (?ann fid args dr. e = Call ann (IntCall fid) args dr)` by
    (qpat_x_assum `lowered_value_type cenv e <> expr_type e` mp_tac >>
     Cases_on `e` >> simp[lowered_value_type_def]
     >~ [`Literal ty lit`]
     >- (Cases_on `ty` >> simp[lowered_value_type_def] >>
         rename1 `BaseT bt` >> Cases_on `bt` >>
         Cases_on `lit` >> simp[lowered_value_type_def] >>
         rename1 `BytesT bound` >> Cases_on `bound` >>
         simp[lowered_value_type_def])
     >~ [`Builtin ann bt args`]
     >- (Cases_on `bt` >> simp[lowered_value_type_def] >>
         Cases_on `is_word_type ann`
         >- (`is_word_type (expr_type (Builtin ann NamedConst args))` by
               simp[vyperASTTheory.expr_type_def] >>
             irule vyperTypeArgFitsTheory.arg_type_fits_prim_word >>
             simp[membership_element_word_boundary] >>
             irule expr_body_pre_lowered_fits >> metis_tac[]) >>
         drule_all named_const_nonword_compile_shape >> simp[])
     >~ [`TypeBuiltin ann tb tys args`]
     >- (Cases_on `tb` >> simp[lowered_value_type_def]) >>
     rename1 `Call ann tgt args dr` >> Cases_on `tgt` >>
     simp[lowered_value_type_def]) >>
  pop_assum mp_tac >> strip_tac
  >- (gvs[Once compile_expr_raw_def, compile_expr_body_def, vyperASTTheory.expr_type_def,
          compile_literal_vv_def, comp_bind_def, comp_return_def] >>
      pairarg_tac >> gvs[])
  >- (gvs[Once compile_expr_raw_def, compile_expr_body_def, vyperASTTheory.expr_type_def,
          compile_literal_vv_def, comp_bind_def, comp_return_def] >>
      pairarg_tac >> gvs[])
  >- (gvs[Once compile_expr_raw_def, compile_expr_body_def, vyperASTTheory.expr_type_def,
          compile_literal_vv_def, comp_bind_def, comp_return_def] >>
      pairarg_tac >> gvs[])
  >- (gvs[] >> drule concat_compile_shape >> simp[])
  >- (qpat_x_assum `compile_expr _ _ _ _ = _` mp_tac >>
      simp[Once compile_expr_component_eq] >>
      simp[Once compile_expr_raw_def, compile_type_builtin_dispatch_body_def] >>
      rpt (pairarg_tac >> gvs[]) >> rpt strip_tac >>
      rpt (pairarg_tac >> gvs[]) >>
      Cases_on `LENGTH args = 1 /\ ~en` >>
      Cases_on `is_word_type (expr_type (HD args))` >>
      gvs[] >> drule as_ptr_val_result >> simp[])
  >> (gvs[exprSimSendTheory.compile_expr_call] >>
      drule reason_compile_call >> simp[reason_result_shape_def])
QED

(* Retagging a memory pointer changes its copy layout, but it does not
   change how unwrap reaches its source bytes. Other locations keep their
   original tag. *)
Theorem extcall_operand_materialize_retag:
  expr_body_pre cenv cx env e es /\
  compile_expr cenv (expr_type e) e sa = (vv,sm) ==>
  (is_word_type (vv_type (ext_call_arg_value (lowered_value_type cenv e) vv)) <=>
   is_word_type (expr_type e)) /\
  (~is_word_type (expr_type e) ==>
   compile_materialize_vv cenv (lowered_value_type cenv e)
     (ext_call_arg_value (lowered_value_type cenv e) vv) =
   compile_materialize_vv cenv (lowered_value_type cenv e) vv)
Proof
  strip_tac >>
  `well_typed_expr env e /\
   (!id t. FLOOKUP env.var_types id = SOME t ==>
     ?p sz. FLOOKUP cenv.ce_vars id = SOME (PtrVar (Var p) sz))` by
    fs[expr_body_pre_def, expr_sim_inv_def] >>
  `vv_type vv = expr_type e \/ vv_type vv = lowered_value_type cenv e` by
    (`reason_uniform_shape compile_expr cenv (expr_type e) e` by
       metis_tac[compile_expr_reason_uniform] >>
     qpat_x_assum `reason_uniform_shape _ _ _ _`
       (strip_assume_tac o REWRITE_RULE [reason_uniform_shape_def]) >>
     qpat_x_assum `!sa vv sb. _ ==> reason_result_shape _ _ _`
       (drule_then assume_tac) >>
     Cases_on `vv` >> gvs[reason_result_shape_def, vv_type_def]) >>
  `is_word_type (lowered_value_type cenv e) <=> is_word_type (expr_type e)` by
    metis_tac[expr_body_pre_lowered_fits, arg_type_fits_word_type] >>
  `is_word_type (vv_type vv) <=> is_word_type (expr_type e)` by metis_tac[] >>
  namedCases_on `vv` ["tag op", "tag p"] >>
  fs[ext_call_arg_value_def, vv_type_def] >>
  Cases_on `p.ptr_location = LocMemory`
  >- simp[compile_materialize_vv_def, unwrap_value_def] >>
  `lowered_value_type cenv e = expr_type e` by
    (MATCH_MP_TAC (Q.INST [`ty` |-> `expr_type e`, `t` |-> `tag`,
        `sa` |-> `sa`, `sm` |-> `sm`, `p` |-> `p`]
       compile_nonmemory_lowered_value_type) >> simp[]) >>
  gvs[compile_materialize_vv_def, unwrap_value_def]
QED

Theorem snapshot_bytes_ptr_retag[local]:
  is_bytestring_type src /\ is_bytestring_type dst /\
  evaluate_type (get_tenv cx) src = SOME sv /\
  evaluate_type (get_tenv cx) dst = SOME dv /\
  value_has_type sv v /\ value_has_type dv v /\
  ptr_mem_ok cx src v op G tn s ==>
  ptr_mem_ok cx dst v op G tn s
Proof
  strip_tac >>
  `val_footprint sv v = val_footprint dv v` by metis_tac[bytestring_val_footprint_eq] >>
  `val_store_size sv v = val_store_size dv v` by metis_tac[bytestring_val_store_size_eq] >>
  fs[ptr_mem_ok_def] >> rpt strip_tac >> gvs[] >>
  metis_tac[bytestring_val_in_memory_transfer]
QED

(* The snapshot saves the read value, not the source place.  Retagging
   therefore retains the region/local value witness without retagging a
   memory path in the source store. *)
Theorem snapshot_bytes_retag:
  expr_body_pre ce cx env e es /\ post_value_type ce e = expr_type e /\
  is_bytestring_type (expr_type e) /\ is_bytestring_type (lowered_value_type ce e) /\
  eval_expr cx e es = (INL raw,ee) /\ read_result cx raw ee = (INL v,ee) /\
  ((?tag op. vv = StackValue tag op) \/
   (?tag p. vv = LocatedValue tag p /\ p.ptr_location = LocMemory)) /\
  vv_holds ce cx (expr_type e) raw vv ee s /\
  vv_at ce cx (expr_type e) sa sb ee raw vv s /\
  ptr_vv_ok cx (expr_type e) raw vv ee G tn s /\
  vv_store_bound cx (expr_type e) (lowered_value_type ce e) ee raw vv s ==>
  vv_holds ce cx (lowered_value_type ce e) (Value v)
    (ext_call_arg_value (lowered_value_type ce e) vv) ee s /\
  vv_at ce cx (lowered_value_type ce e) sa sb ee (Value v)
    (ext_call_arg_value (lowered_value_type ce e) vv) s /\
  ptr_vv_ok cx (lowered_value_type ce e) (Value v)
    (ext_call_arg_value (lowered_value_type ce e) vv) ee G tn s /\
  vv_store_bound cx (expr_type e) (lowered_value_type ce e) ee (Value v)
    (ext_call_arg_value (lowered_value_type ce e) vv) s
Proof
  strip_tac >>
  `~is_word_type (expr_type e) /\ ~is_word_type (lowered_value_type ce e)` by
    metis_tac[is_bytestring_word_type] >>
  `(bind (eval_expr cx e) (read_result cx)) es = (INL v,ee)` by
    simp[bind_def] >>
  `?dst_tv. evaluate_type (get_tenv cx) (lowered_value_type ce e) = SOME dst_tv /\
     value_has_type dst_tv v /\ val_wf dst_tv v` by
    metis_tac[cj 3 abi_args_success_ready] >>
  drule_all expr_body_pre_runtime_typed >> strip_tac >>
  rename1 `evaluate_type (get_tenv cx) (expr_type e) = SOME src_tv` >>
  rename1 `evaluate_type (get_tenv cx) (lowered_value_type ce e) = SOME dst_tv` >>
  `value_has_type src_tv v` by metis_tac[] >>
  `expr_val_at ce cx (expr_type e) sa sb ee v (vv_operand vv) s` by
    (Cases_on `vv` >> gvs[vv_operand_def] >>
     metis_tac[vv_at_def, vv_at_memory_val_at]) >>
  `expr_val_rel cx (expr_type e) v (vv_operand vv) s` by
    (Cases_on `vv` >> gvs[vv_operand_def, vv_holds_def, expr_val_rel_def] >> metis_tac[]) >>
  `expr_val_at ce cx (lowered_value_type ce e) sa sb ee v (vv_operand vv) s /\
   expr_val_rel cx (lowered_value_type ce e) v (vv_operand vv) s` by
    metis_tac[abi_args_at_lowered_transport, abi_args_rel_lowered_transport] >>
  gvs[ext_call_arg_value_def, vv_operand_def] >>
  `read_result cx (Value v) ee = (INL v,ee)` by simp[read_result_def, return_def] >>
  (conj_tac >-
     (simp[vv_holds_def] >> fs[expr_val_rel_def] >> metis_tac[])) >>
  (conj_tac >-
     (simp[vv_at_def] >>
      qpat_assum `expr_val_at ce cx (lowered_value_type ce e) _ _ _ _ _ _`
        (mp_tac o REWRITE_RULE [expr_val_at_def]) >> simp[])) >>
  (conj_tac >-
     (gvs[ptr_vv_ok_def, ptr_val_ok_def] >> metis_tac[snapshot_bytes_ptr_retag])) >>
  gvs[vv_store_bound_def]
QED

(* The retained row is a property of the chosen child endpoint. It is
   shared by the full outcome and the first-exit scoped outcome. *)
Theorem extcall_pos_aggregate_read_at:
  body_inv tops ctx cenv cx /\ expr_body_pre cenv cx env e es /\
  compile_expr cenv (expr_type e) e sa = (vv,sb) /\
  sv = ext_call_arg_value (lowered_value_type cenv e) vv /\
  ~is_word_type (vv_type sv) /\
  eval_expr cx e (es with gas_obs := obs) = (INL tv,ee) /\
  read_result cx tv ee = (INL v,ee) /\
  valid_horizon cx (es with gas_obs := obs) H ee.storage_trace /\
  vv_post H ctx func cenv cx e es sa sb s0 ee tv vv t /\
  vv_store_bound cx (post_value_type cenv e) (lowered_value_type cenv e) ee tv vv t /\
  ptr_vv_ok cx (post_value_type cenv e) tv vv ee G tn t /\
  (!tag op. vv = StackValue tag op /\ ~is_word_type (post_value_type cenv e) ==>
    ptr_buf_ok cenv e op G t) /\
  (!tag p. vv = LocatedValue tag p /\ p.ptr_location = LocMemory ==>
    ptr_buf_ok cenv e p.ptr_operand G t) /\
  (cenv.ce_is_ctor /\ vv_location vv = SOME LocCode ==>
    !rt w. evaluate_type (get_tenv cx) (post_value_type cenv e) = SOME rt /\
      eval_operand (vv_operand vv) t = SOME w ==>
      w2n w + type_memory_size rt <= lo /\
      (!mem. mem_agree_outside tn.t_mem t.vs_memory mem ==>
        val_in_memory rt v (w2n w) mem)) ==>
  ((?tag op0. sv = StackValue tag op0) \/
   (?p. sv = LocatedValue (lowered_value_type cenv e) p /\
     ~is_word_type (lowered_value_type cenv e) /\ p.ptr_location = LocMemory) \/
   (?p. sv = LocatedValue (lowered_value_type cenv e) p /\
     ~is_word_type (lowered_value_type cenv e) /\ p.ptr_location <> LocMemory /\
     lowered_value_type cenv e = expr_type e /\ sv = vv)) /\
  (?raw. read_result cx raw ee = (INL v,ee) /\
    vv_holds cenv cx (lowered_value_type cenv e) raw sv ee t /\
    vv_at cenv cx (lowered_value_type cenv e) sa sb ee raw sv t /\
    ptr_vv_ok cx (lowered_value_type cenv e) raw sv ee G tn t /\
    vv_store_bound cx (post_value_type cenv e) (lowered_value_type cenv e) ee raw sv t) /\
  vv_storage_live H cx sv ee t /\
  (!tag op. sv = StackValue tag op /\ ~is_word_type (lowered_value_type cenv e) ==>
    ptr_buf_ok cenv e op G t) /\
  (!tag p. sv = LocatedValue tag p /\ p.ptr_location = LocMemory ==>
    ptr_buf_ok cenv e p.ptr_operand G t) /\
  (cenv.ce_is_ctor /\ vv_location sv = SOME LocCode ==>
    !rt w. evaluate_type (get_tenv cx) (lowered_value_type cenv e) = SOME rt /\
      eval_operand (vv_operand sv) t = SOME w ==>
      w2n w + type_memory_size rt <= lo /\
      (!mem. mem_agree_outside tn.t_mem t.vs_memory mem ==>
        val_in_memory rt v (w2n w) mem))
Proof
  strip_tac >>
  `vv_storage_live H cx vv ee t` by
    (`functions_well_typed cx` by fs[expr_body_pre_def, expr_sim_inv_def] >>
     irule body_assign_rhs_storage_live >> simp[] >>
     qexistsl [`cenv`,`ctx`,`e`,`env`,`es with gas_obs := obs`,
               `func`,`tv`,`s0`,`sa`,`sb`,`tops`] >>
     `expr_body_pre cenv cx env e (es with gas_obs := obs)` by simp[] >>
     qpat_x_assum `expr_body_pre _ _ _ _ (_ with gas_obs := _)`
       (strip_assume_tac o REWRITE_RULE [expr_body_pre_def, expr_sim_inv_def]) >>
     simp[exprSimPropsTheory.vv_post_initial_gas, runtime_consistent_def]) >>
  qpat_x_assum `vv_post H ctx func cenv cx e es sa sb s0 ee tv vv t`
    (strip_assume_tac o REWRITE_RULE [vv_post_def]) >>
  `arg_type_fits (lowered_value_type cenv e) (expr_type e)` by
    metis_tac[expr_body_pre_lowered_fits] >>
  `(is_word_type (lowered_value_type cenv e) <=> is_word_type (expr_type e))` by
    metis_tac[arg_type_fits_word_type] >>
  namedCases_on `vv` ["tag op", "tag p"] >>
  gvs[ext_call_arg_value_def, vv_type_def, vv_location_def, vv_operand_def]
  >- (Cases_on `lowered_value_type cenv e = post_value_type cenv e` >> gvs[]
      >- (qexists `tv` >> simp[]) >> suspend "retag") >>
  Cases_on `p.ptr_location = LocMemory`
  >- (gvs[] >> Cases_on `lowered_value_type cenv e = post_value_type cenv e` >> gvs[]
      >- (qexists `tv` >> gvs[vv_holds_def, vv_at_def, ptr_vv_ok_def,
                            vv_store_bound_def]) >> suspend "retag") >>
  `lowered_value_type cenv e = expr_type e` by
    (irule compile_nonmemory_lowered_value_type >>
     qpat_assum `compile_expr _ _ e sa = (LocatedValue _ p,sb)`
       (irule_at Any) >> simp[]) >>
  `post_value_type cenv e = expr_type e` by simp[post_value_type_lowered] >>
  `tag = expr_type e` by fs[vv_holds_def] >>
  gvs[] >> qexists `tv` >> simp[]
QED

Resume extcall_pos_aggregate_read_at[retag]:
  markerLib.RESUME_TAC >>
  `post_value_type cenv e <> lowered_value_type cenv e` by metis_tac[] >>
  `~is_word_type (expr_type e)` by
    (strip_tac >>
     `lowered_value_type cenv e = expr_type e` by (irule abi_args_word_fits_eq >> simp[]) >>
     fs[post_value_type_word]) >>
  `post_value_type cenv e = expr_type e` by
    (Cases_on `e` >> simp[post_value_type_def] >>
     rename1 `Call _ tgt _ _` >> Cases_on `tgt` >>
     fs[post_value_type_def, vyperASTTheory.expr_type_def] >>
     IF_CASES_TAC >> gvs[]) >>
  drule_all (Q.SPECL [`cenv`,`e`] materialize_post_lowered_classify) >> simp[] >> strip_tac >>
  `expr_body_pre cenv cx env e (es with gas_obs := obs)` by simp[] >>
  qmatch_asmsub_abbrev_tac `vv_holds cenv cx _ tv vv0 ee t` >>
  mp_tac (Q.INST [`ce` |-> `cenv`, `cx` |-> `cx`, `env` |-> `env`, `e` |-> `e`,
    `es` |-> `es with gas_obs := obs`, `ee` |-> `ee`, `raw` |-> `tv`, `v` |-> `v`,
    `vv` |-> `vv0`, `s` |-> `t`, `G` |-> `G`, `tn` |-> `tn`] snapshot_bytes_retag) >>
  impl_tac >- (fs[Abbr `vv0`] >> metis_tac[]) >>
  simp[Abbr `vv0`, ext_call_arg_value_def] >> strip_tac >>
  TRY (qexists_tac `Value v`) >> fs[read_result_def, return_def]
QED

Finalise extcall_pos_aggregate_read_at

Theorem extcall_horizon_gas[local]:
  valid_horizon cx (es with gas_obs := gs) H obs <=>
  valid_horizon cx es H obs
Proof
  `storage_well_formed_on cx (es with gas_obs := gs) (FST H) <=>
   storage_well_formed_on cx es (FST H)` by
    (irule storage_well_formed_on_backends >> simp[]) >>
  simp[valid_horizon_def]
QED

Theorem extcall_pos_aggregate_outcome:
  body_expr_full_ok cx e /\ body_inv tops ctx cenv cx /\
  shadow_body_inv tops ctx shadow_ctx /\
  body_const_cells_agree [(NONE,tops)] cx env es /\
  expr_body_pre cenv cx env e es /\
  compile_expr cenv (expr_type e) e sa = (vv,sb) /\
  compile_expr (gas_shadow_env T cenv) (expr_type e) (gas_shadow_expr e) shadow_sa = (vv,shadow_sb) /\
  compile_snapshot_vv cenv F
    (ext_call_arg_value (lowered_value_type cenv e) vv) sb = (sv,sb) /\
  ~is_word_type (vv_type (ext_call_arg_value (lowered_value_type cenv e) vv)) /\
  gas_shadow_state sa shadow_sa /\ gas_shadow_state sb shadow_sb /\
  gas_shadow_context ctx shadow_ctx /\ ctx_inst_ids_distinct ctx /\
  gas_shadow_function func shadow_func /\ MEM func ctx.ctx_functions /\
  MEM shadow_func shadow_ctx.ctx_functions /\
  fn_has_code sa sb func /\ fn_has_code shadow_sa shadow_sb shadow_func /\
  fn_inst_ids_distinct func /\ local_ptrs_reserved cenv sa /\
  (!fn inst z. frag_reachable ctx func s0 fn inst z ==> dalloca_fmp_headroom inst z) /\
  (!H. dead_lo_ok H (DF H) lo cenv cx) /\
  (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  return_buf_frame d cenv sa s0 /\ alloca_history func s0 /\
  (!H. valid_horizon cx st0 H es.storage_trace ==>
    stmt_state_rel H ctx func cenv cx es s0 /\
    storage_well_formed_on cx es (FST H) /\
    ghost_inv_at (DF H) lo d cenv cx es G0 tn0 s0) /\
  ~s0.vs_halted /\ s0.vs_current_bb = sa.cs_current_bb /\
  s0.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  gas_outcome_full
    (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
    (cx_tops cx) cx st0 (bind (eval_expr cx e) (read_result cx)) (es,s0,G0,tn0)
    (\H res ee G tn t. ?v. res = INL v /\
      ((?tag op0. sv = StackValue tag op0) \/
       (?p. sv = LocatedValue (lowered_value_type cenv e) p /\
         ~is_word_type (lowered_value_type cenv e) /\ p.ptr_location = LocMemory) \/
       (?p. sv = LocatedValue (lowered_value_type cenv e) p /\
         ~is_word_type (lowered_value_type cenv e) /\ p.ptr_location <> LocMemory /\
         lowered_value_type cenv e = expr_type e /\
         compile_expr cenv (expr_type e) e sa = (sv,sb))) /\
      (?raw. read_result cx raw ee = (INL v,ee) /\
        vv_holds cenv cx (lowered_value_type cenv e) raw sv ee t /\
        vv_at cenv cx (lowered_value_type cenv e) sa sb ee raw sv t /\
        ptr_vv_ok cx (lowered_value_type cenv e) raw sv ee G tn t /\
        vv_store_bound cx (post_value_type cenv e) (lowered_value_type cenv e) ee raw sv t) /\
      vv_storage_live H cx sv ee t /\
      (!tag op. sv = StackValue tag op /\ ~is_word_type (lowered_value_type cenv e) ==>
        ptr_buf_ok cenv e op G t) /\
      (!tag p. sv = LocatedValue tag p /\ p.ptr_location = LocMemory ==>
        ptr_buf_ok cenv e p.ptr_operand G t) /\
      (cenv.ce_is_ctor /\ vv_location sv = SOME LocCode ==>
        !rt w. evaluate_type (get_tenv cx) (lowered_value_type cenv e) = SOME rt /\
          eval_operand (vv_operand sv) t = SOME w ==>
          w2n w + type_memory_size rt <= lo /\
          (!mem. mem_agree_outside tn.t_mem t.vs_memory mem ==>
            val_in_memory rt v (w2n w) mem)) /\
      stmt_state_rel H ctx func cenv cx ee t /\
      storage_well_formed_on cx ee (FST H) /\
      return_buf_frame d cenv sb t /\ ghost_inv_at (DF H) lo d cenv cx ee G tn t /\
      ghost_kept_at lo cenv es sa G0 tn0 s0 G tn /\
      alloca_history func t /\ s0.vs_alloca_next <= t.vs_alloca_next /\
      ~t.vs_halted /\ t.vs_current_bb = sb.cs_current_bb /\
      t.vs_inst_idx = LENGTH sb.cs_current_insts /\
      wb_frame cenv es ee sa s0 t /\
      MAP FDOM ee.scopes = MAP FDOM es.scopes /\
      (~expr_has_effect e ==> pure_frame cenv func es sa s0 t) /\
      (!x w. not_fresh_at sa x /\ lookup_var x s0 = SOME w ==> lookup_var x t = SOME w) /\
      (!aid b. FLOOKUP s0.vs_allocas aid = SOME b ==> FLOOKUP t.vs_allocas aid = SOME b) /\
      (~expr_has_effect e ==>
       (ee with <|gas_obs := []; outcomes := NONE; requests := []; storage_trace := []|>) =
       (es with <|gas_obs := []; outcomes := NONE; requests := []; storage_trace := []|>)))
    (\H res ee gt r. expr_exit res r /\ halt_exit H cx ee res r /\
      (ctx_has_dalloca ctx ==> !s. r = Halt s ==> allocas_below_fmp s))
Proof
  strip_tac >>
  irule gas_outcome_full_initial_domain >>
  simp[vyperStorageTraceTheory.storage_trace_frame_bind_all,
       cj 5 vyperStorageTraceTheory.evaluate_storage_trace_frame,
       vyperStorageTraceTheory.storage_trace_frame_read_result] >>
  strip_tac >>
  `ctx_has_dalloca ctx ==> allocas_below_fmp s0` by
    (`valid_horizon cx st0 (storage_trace_horizon es.storage_trace) es.storage_trace` by
       fs[vyperStorageFootprintTheory.storage_trace_domain_def] >>
     qpat_assum `!H. valid_horizon _ _ H _ ==> stmt_state_rel H ctx func cenv cx es s0 /\ _`
       (qspec_then `storage_trace_horizon es.storage_trace` (drule_then strip_assume_tac)) >>
     qpat_assum `stmt_state_rel _ ctx func cenv cx es s0`
       (ACCEPT_TAC o MATCH_MP bodyFullHashKeccakFixedTheory.stmt_state_rel_allocas_below_fmp)) >>
  gvs[compile_snapshot_vv_def, comp_return_def] >>
  `expr_vv_sim_full (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
     cenv cx (expr_type e) e es` by metis_tac[body_expr_full_ok_def] >>
  `gas_admissible (eval_expr cx e) expr_vv_res_ok es` by
    metis_tac[expr_body_pre_gas_admissible, forced_expr_admissible_raw] >>
  qpat_x_assum `expr_vv_sim_full _ _ _ _ _ _` mp_tac >>
  rewrite_tac[expr_vv_sim_full_def] >>
  disch_then (qspecl_then [`st0`,`sa`,`sb`,`shadow_sa`,`shadow_sb`,`vv`,
    `s0`,`G0`,`tn0`] mp_tac) >> simp[] >>
  (impl_tac >- first_assum ACCEPT_TAC) >> strip_tac >>
  qmatch_asmsub_abbrev_tac `gas_outcome_full _ _ _ _ _ _ childQ childR` >>
  irule gas_outcome_full_bind_all >>
  rpt conj_tac
  >~ [`storage_trace_frame (eval_expr _ _)`]
  >- simp[cj 5 evaluate_storage_trace_frame]
  >~ [`!v. storage_trace_frame (read_result cx v)`]
  >- simp[storage_trace_frame_read_result]
  >~ [`gas_marked_exec _ _ _ _ _ _ _`]
  >- (rpt strip_tac >> drule gasExemptCertTheory.gas_exempt_cert_bind_result >> simp[] >>
      disch_then irule >> simp[])
  >~ [`gas_exempt_cert _ _ _ _ _ _ _ _`]
  >- (rpt strip_tac >> irule gasExemptCertTheory.gas_exempt_cert_error_result >>
      first_assum ACCEPT_TAC) >>
  qexists `\H res ee G tn t. childQ H res ee G tn t /\ ee.gas_obs = [] /\ ~t.vs_halted` >>
  reverse conj_tac
  >- (irule gas_outcome_full_post_source >>
      first_assum (irule_at Any) >> simp[Abbr `childR`] >>
      rpt strip_tac >> Cases_on `res` >>
      gvs[expr_exit_def, halt_exit_def, expr_exit_INR_type]) >>
  suspend "read"
QED

Resume extcall_pos_aggregate_outcome[read]:
  qx_genl_tac [`marks`,`res`,`ee`,`G1`,`tn1`,`t`] >> BETA_TAC >> strip_tac >>
  `valid_horizon cx st0 (storage_trace_horizon ee.storage_trace) ee.storage_trace` by
    gvs[storage_trace_domain_def] >>
  qpat_assum `!H. _ ==> childQ H _ _ _ _ _ /\ _`
    (qspec_then `storage_trace_horizon ee.storage_trace` mp_tac) >>
  (impl_tac >- first_assum ACCEPT_TAC) >>
  qunabbrev_tac `childQ` >> disch_then (strip_assume_tac o BETA_RULE) >> gvs[] >>
  qpat_assum `!tail. eval_expr _ _ _ = _`
    (qspec_then `[]` (assume_tac o SIMP_RULE (srw_ss()) [])) >>
  `ee with gas_obs := [] = ee` by simp[evaluation_state_component_equality] >>
  gvs[] >>
  Cases_on `read_result cx tv ee` >>
  rename1 `read_result cx tv ee = (read_res,read_state)` >>
  drule read_result_state >> strip_tac >> gvs[] >>
  Cases_on `read_res`
  >- (rename1 `read_result cx tv ee = (INL v,ee)` >> suspend "package") >>
  metis_tac[vv_post_failed_read]
QED

Resume extcall_pos_aggregate_outcome[package]:
  irule gas_outcome_full_pure >>
  reverse conj_tac >- simp[] >>
  qexistsl [`G1`,`ee`,`INL v`,`t`,`tn1`] >>
  simp[] >> conj_tac >- metis_tac[read_result_gas_obs] >>
  rpt gen_tac >> disch_tac >>
  qpat_assum `!H. _ ==> vv_post H _ _ _ _ _ _ _ _ _ _ _ _ _ /\ _` drule >>
  strip_tac >> simp[gas_origin_ptr_path_rules] >>
  `~expr_has_effect e ==>
   (ee with <|gas_obs := []; outcomes := NONE; requests := []; storage_trace := []|>) =
   (es with <|gas_obs := []; outcomes := NONE; requests := []; storage_trace := []|>)` by
    (strip_tac >> drule_all effect_free_source_projection >> simp[]) >>
  `MAP FDOM ee.scopes = MAP FDOM es.scopes` by
    (drule eval_expr_preserves_scopes_dom >> simp[]) >>
  `valid_horizon cx (es with gas_obs := gas_explicit marks s0.vs_gas_readings)
        H ee.storage_trace` by
    (qpat_assum `eval_expr cx e (es with gas_obs := _) = (INL tv,ee)`
       (mp_then Any mp_tac valid_horizon_frame) >>
     simp[cj 5 evaluate_storage_trace_frame] >> strip_tac >>
     `valid_horizon cx st0 H es.storage_trace` by metis_tac[] >>
     `storage_well_formed_on cx es (FST H)` by metis_tac[] >>
     fs[extcall_horizon_gas, valid_horizon_def]) >>
  `cenv.ce_is_ctor /\ vv_location vv = SOME LocCode ==>
   !rt w. evaluate_type (get_tenv cx) (post_value_type cenv e) = SOME rt /\
     eval_operand (vv_operand vv) t = SOME w ==>
     w2n w + type_memory_size rt <= lo /\
     (!mem. mem_agree_outside tn1.t_mem t.vs_memory mem ==>
       val_in_memory rt v (w2n w) mem)` by fs[arithmeticTheory.ADD_COMM] >>
  drule_all (REWRITE_RULE [] (Q.INST
    [`sv` |-> `ext_call_arg_value (lowered_value_type cenv e) vv`]
    extcall_pos_aggregate_read_at)) >> strip_tac >>
  `sa.cs_next_var <= sb.cs_next_var` by metis_tac[compile_expr_extends] >>
  qpat_x_assum `vv_post H ctx func cenv cx e es sa sb s0 ee tv vv t`
    (strip_assume_tac o REWRITE_RULE [vv_post_def]) >>
  `wb_frame cenv es ee sa s0 t` by
    (rewrite_tac[wb_frame_def] >> rpt conj_tac >> first_assum ACCEPT_TAC) >>
  `return_buf_frame d cenv sb t` by
    (irule return_buf_frame_frame >> qexistsl [`cenv`,`s0`,`sa`] >> simp[]) >>
  gvs[] >> qexists_tac `raw` >> simp[]
QED

Finalise extcall_pos_aggregate_outcome
