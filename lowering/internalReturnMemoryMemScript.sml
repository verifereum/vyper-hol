(* Source endpoint and compiler boundary for memory-valued internal returns. *)
Theory internalReturnMemoryMem
Ancestors
  internalReturnComposeMem internalReturnCompileMem internalReturnImmutableTypes
  vyperTypeEnvPreservation exprSimHypsDefs stmtLowering stmtLoweringMono
  exprLoweringProps compileEnv loweringPosts vyperState vyperInterpreter
  stmtSimReturn stmtSimReturnWiden intCallReturnMem bodySim ctorReturnFrame
  venomExecSemantics venomState fragExec freshWrites exprOperandVar
  bodySimFull annAssignPtrDestination ptrSafetyTransport fragGasOriginPtrExec
  gasOutcomeFullCompose context emitHelper venomInst gasShadowState
  gasOutcomeFull bodyPtrDefs exprSimDefs annAssignPtrMemorySource annAssignPtrMemoryCont

Theorem internal_return_source_env[local]:
  env_consistent env cx es /\
  bind (eval_expr cx e) (read_result cx) (es with gas_obs := gs) =
    (INL v,ee) ==>
  env_consistent env cx ee
Proof
  simp[bind_def, AllCaseEqs()] >> rpt strip_tac >>
  imp_res_tac read_result_state >> gvs[] >>
  irule eval_expr_preserves_ec >> metis_tac[vyperTypeInvariantsTheory.gas_obs_type_invariants]
QED

Theorem internal_return_memory_code[local]:
  cenv.ce_return_pc = SOME (PtrVar (Var rpc) rsz) /\
  cenv.ce_returns_count = 0 /\
  cenv.ce_return_buf = SOME (PtrVar (Var bp) cap) /\
  stmt_env cenv lctx ty (Return (SOME e)) sa = (cenv'',sb) /\
  lower_value compile_expr cenv ty e sa = (op,s1) ==>
  compile_internal_return cenv (SOME op) (Var rpc) 0 ty
    (lowered_value_type cenv e)
    (case ty of TupleT tys => tys | StructT nsid =>
       MAP (FST o SND) (get_struct_fields cenv.ce_struct_fields
          (nsid_to_string nsid)) | _ => []) (SOME (Var bp)) s1 = ((),sb)
Proof
  strip_tac >> qpat_x_assum `stmt_env _ _ _ _ _ = _` mp_tac >>
  simp[stmt_env_def, declare_stmt_local_def, compile_stmt_def, comp_bind_def,
       comp_ignore_bind_def, comp_return_def, compile_internal_return_from_env_def] >>
  Cases_on `compile_internal_return cenv (SOME op) (Var rpc) 0 ty
    (lowered_value_type cenv e)
    (case ty of TupleT tys => tys | StructT nsid =>
       MAP (FST o SND) (get_struct_fields cenv.ce_struct_fields
          (nsid_to_string nsid)) | _ => []) (SOME (Var bp)) s1` >>
  simp[oneTheory.one]
QED

Theorem internal_return_memory_exit[local]:
  same_frame ce cenv /\
  intret_mem_q func cenv cx tv bw v (ee with scopes := []) r ==>
  !tail. intret_mem_q func ce cx tv bw v
    ((ee with gas_obs := tail) with scopes := []) r
Proof
  simp[intret_mem_q_def, intret_q_def] >> rpt strip_tac >>
  gvs[result_rel_def] >>
  `ee with <|scopes := []; gas_obs := tail|> =
    (ee with scopes := []) with gas_obs := tail` by simp[] >>
  pop_assum SUBST1_TAC >> simp[state_rel_gas_obs] >>
  drule_all constructor_exit_state_rel >> simp[]
QED

Theorem internal_return_memory_suffix[local]:
  same_frame ce cenv /\
  compile_internal_return cenv (SOME op) (Var rpc) 0 ty sty elems
    (SOME (Var bp)) sa = ((),sb) /\
  (sty = ty \/ is_bytestring_type ty) /\
  type_widens_to (get_tenv cx) sty ty /\
  evaluate_type (get_tenv cx) sty = SOME stv /\
  evaluate_type (get_tenv cx) ty = SOME tv /\
  value_has_type stv v /\ value_has_type tv v /\
  val_wf stv v /\ val_wf tv v /\
  acyclic_struct_metadata cenv.ce_struct_fields /\
  sfields_tenv_consistent cenv.ce_struct_fields (get_tenv cx) /\
  (!name fields. FLOOKUP cenv.ce_struct_fields name = SOME fields ==>
     ALL_DISTINCT (MAP FST fields) /\
     EVERY (\(fname,fty,sz). !tv. evaluate_type (get_tenv cx) fty = SOME tv ==>
       sz = type_memory_size tv) fields) /\
  type_memory_bytes cenv ty = type_memory_size tv /\
  cenv.ce_imm_alloca = NONE /\
  w2n bw + type_memory_size tv + 64 < dimword (:256) /\
  (cenv.ce_is_ctor ==> !name itv iv off.
     FLOOKUP cenv.ce_module_vars (cenv.ce_module,name) = SOME (ImmutableLoc off) /\
     FLOOKUP (case ALOOKUP ee.immutables cx.txn.target of NONE => FEMPTY
       | SOME imms => get_source_immutables cenv.ce_module imms) name =
       SOME (itv,iv) ==>
     regions_disjoint off (type_memory_size itv) (w2n bw) (type_memory_size tv)) /\
  stmt_state_rel ctx func cenv cx (ee with scopes := []) t /\
  expr_val_rel cx sty v op t /\ expr_store_bound cx sty v op t /\
  lookup_var bp t = SOME bw /\ lookup_var rpc t = SOME pc /\
  w2n bw + type_memory_size tv <= t.vs_alloca_next /\
  (!x. op = Var x ==> not_fresh_at sa x) /\
  not_fresh_at sa bp /\ not_fresh_at sa rpc /\
  fn_has_code sa sb func /\ ~t.vs_halted /\
  t.vs_current_bb = sa.cs_current_bb /\
  t.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?n r. gas_path_mem ctx func t n r /\ exit_result r /\
    !tail. intret_mem_q func ce cx tv bw v
      ((ee with gas_obs := tail) with scopes := []) r
Proof
  strip_tac >>
  `frag_exec ctx sa sb
    (\s. stmt_state_rel ctx func cenv cx (ee with scopes := []) s /\
         expr_val_rel cx sty v op s /\ eval_operand (Var bp) s = SOME bw /\
         (sty <> ty /\ ~is_word_type ty /\ ~is_bytestring_type ty ==>
          ?sw. eval_operand op s = SOME sw /\
               w2n sw + type_memory_size stv < dimword (:256) /\
               (w2n sw + type_memory_size stv <= w2n bw \/
                w2n bw + type_memory_size tv <= w2n sw)) /\
         ?pc. eval_operand (Var rpc) s = SOME pc)
    (\s. F) (intret_mem_q func cenv cx tv bw v (ee with scopes := []))` by
    (irule compile_internal_return_memory_widen_frag >> simp[] >> metis_tac[]) >>
  `eval_operand (Var bp) t = SOME bw /\
   lookup_var rpc t = SOME pc /\
   (sty = ty \/ is_bytestring_type ty /\ type_widens_to (get_tenv cx) sty ty)` by
    simp[eval_operand_def] >>
  `?u. gas_path_mem ctx func t 0
      (IntRet <|iret_values := []; iret_adopt_fmp := NONE|> u) /\
    intret_mem_q func cenv cx tv bw v (ee with scopes := [])
      (IntRet <|iret_values := []; iret_adopt_fmp := NONE|> u)` by
    (irule compile_internal_return_memory_path_mem >>
     simp[Once CONJ_ASSOC] >>
     qpat_assum `compile_internal_return _ _ _ _ _ _ _ _ _ = _`
       (irule_at Any) >>
     qpat_assum `frag_exec _ _ _ _ _ _` (irule_at Any) >>
     qexistsl_tac [`v`, `tv`, `stv`, `pc`, `bw`, `cx`] >>
     gvs[eval_operand_def] >> metis_tac[]) >>
  qexists_tac `0` >> goal_assum (drule_at Any) >>
  simp[exit_result_def] >> irule internal_return_memory_exit >> metis_tac[]
QED

Theorem internal_return_memory_mem:
  body_inv tops ctx cenv cx /\ cenv.ce_module = NONE /\
  cenv.ce_module_vars =
    add_immutable_locations (get_struct_fields (make_struct_fields_map tops))
      tops 0 (add_module_var_locations tops FEMPTY) /\
  same_frame ce cenv /\ expr_sim_inv cenv cx env es /\
  cenv.ce_return_pc = SOME (PtrVar (Var rpc) rsz) /\
  cenv.ce_returns_count = 0 /\ cenv.ce_imm_alloca = NONE /\
  lowered_value_type cenv e = expr_type e /\
  (expr_type e = ty \/ is_bytestring_type ty) /\
  evaluate_type (get_tenv cx) ty = SOME tv /\
  IS_SOME (type_stmt env ty (Return (SOME e))) /\
  call_evaluation_safe cx (int_calls_stmt (Return (SOME e))) /\
  w2n bw + type_memory_size tv + 64 < dimword (:256) /\
  (cenv.ce_is_ctor ==> !nm io ity itv.
    FLOOKUP cenv.ce_module_vars (cenv.ce_module,nm) = SOME (ImmutableLoc io) /\
    cenv.ce_module_var_type (cenv.ce_module,nm) = SOME ity /\
    evaluate_type (get_tenv cx) ity = SOME itv ==>
    regions_disjoint io (type_memory_size itv) (w2n bw) (type_memory_size tv)) /\
  expr_sim_mem ctx func cenv cx ty e es ==>
  stmt_frag_mem (SOME (bw,type_memory_size tv)) ctx func cx lctx
    (intret_mem_q func ce cx tv bw) cenv
    (stmt_env cenv lctx ty (Return (SOME e)))
    (eval_stmt cx (Return (SOME e))) es
Proof
  strip_tac >> (irule internal_return_value_counted_mem >> simp[] >> conj_tac
  >- (rpt strip_tac >>
      qpat_x_assum `stmt_env _ _ _ _ _ = _` mp_tac >>
      simp[stmt_env_def, declare_stmt_local_def, compile_stmt_def,
        comp_bind_def, comp_ignore_bind_def, comp_return_def] >>
      pairarg_tac >> simp[] >> strip_tac >> gvs[] >>
      qpat_x_assum `compile_internal_return_from_env _ _ _ _ _ _ = _` mp_tac >>
      rpt (pop_assum kall_tac) >>
      metis_tac[cj 2 ci_mono_return_helpers, ci_mono_def, pairTheory.SND]) >>
  rpt strip_tac >> suspend "normal")
QED

Resume internal_return_memory_mem[normal]:
  markerLib.RESUME_TAC >>
  `?bp cap. cenv.ce_return_buf = SOME (PtrVar (Var bp) cap) /\
    lookup_var bp s0 = SOME bw /\ not_fresh_at sa bp /\
    w2n bw + type_memory_size tv <= s0.vs_alloca_next` by
    fs[return_buf_frame_def] >>
  `cs_extends sa s1 /\ sa.cs_next_var <= s1.cs_next_var` by
    metis_tac[ci_mono_compile_expr_sa, ci_mono_def, pairTheory.SND] >>
  drule_all internal_return_memory_code >> strip_tac >>
  `cs_extends s1 sb` by
    metis_tac[cj 1 ci_mono_return_helpers, ci_mono_def, pairTheory.SND] >>
  `fn_has_code s1 sb func` by metis_tac[fn_has_code_split] >>
  `?stv. evaluate_type (get_tenv cx) (expr_type e) = SOME stv /\
    value_has_type stv v` by (drule_all returnValueTypedTheory.return_value_typed >> fs[]) >>
  `env_consistent env cx ee` by
    (irule internal_return_source_env >> fs[expr_sim_inv_def] >> metis_tac[]) >>
  `type_widens_to (get_tenv cx) (expr_type e) ty` by
    fs[vyperTypeSystemTheory.type_stmt_def, expr_sim_inv_def,
      vyperTypeInvariantsTheory.env_consistent_def,
      vyperTypeInvariantsTheory.env_context_consistent_def, AllCaseEqs()] >>
  `value_has_type tv v` by
    (drule_all vyperTypeArgFitsTheory.type_widens_to_value_has_type >> simp[]) >>
  `val_wf stv v /\ val_wf tv v` by
    metis_tac[valueTypingMemoryPropsTheory.value_has_type_memory_wf] >>
  suspend "suffix"
QED

Resume internal_return_memory_mem[suffix]:
  markerLib.RESUME_TAC >> irule internal_return_memory_suffix >>
  qpat_assum `compile_internal_return _ _ _ _ _ _ _ _ _ = _` (irule_at Any) >>
  suspend "resources"
QED
Resume internal_return_memory_mem[resources]:
  markerLib.RESUME_TAC >>
  `?pc. lookup_var rpc t = SOME pc` by
    (fs[ret_pc_ok_def, expr_post_def] >> metis_tac[]) >>
  qexistsl_tac [`stv`, `pc`] >>
  `lookup_var bp t = SOME bw` by (fs[expr_post_def] >> metis_tac[]) >>
  `not_fresh_at s1 bp /\ not_fresh_at s1 rpc` by
    (fs[ret_pc_ok_def] >> metis_tac[not_fresh_at_mono]) >>
  `!x. op = Var x ==> not_fresh_at s1 x` by
    metis_tac[compile_lower_value_var] >>
  `stmt_state_rel ctx func cenv cx (ee with scopes := []) t` by
    (fs[expr_post_def, stmt_state_rel_def, immutable_alloca_sep_def,
        local_region_def, lookup_scopes_def] >> conj_tac
     >- (irule constructor_exit_state_rel >> qexists_tac `cenv` >> simp[]) >>
     metis_tac[]) >>
  `type_memory_bytes cenv ty = type_memory_size tv` by
    metis_tac[exprSimHypsTheory.expr_sim_inv_memory_size] >>
  `cenv.ce_is_ctor ==> !name itv iv off.
     FLOOKUP cenv.ce_module_vars (cenv.ce_module,name) = SOME (ImmutableLoc off) /\
     FLOOKUP (case ALOOKUP ee.immutables cx.txn.target of NONE => FEMPTY
       | SOME imms => get_source_immutables cenv.ce_module imms) name =
       SOME (itv,iv) ==>
     regions_disjoint off (type_memory_size itv) (w2n bw) (type_memory_size tv)` by
    metis_tac[internal_return_immutable_separation] >>
  `post_value_type cenv e = expr_type e` by metis_tac[post_value_type_lowered] >>
  `acyclic_struct_metadata cenv.ce_struct_fields` by fs[body_inv_def] >>
  gvs[expr_post_def, expr_sim_inv_def] >>
  (conj_tac >- first_assum ACCEPT_TAC) >> first_assum ACCEPT_TAC
QED
Finalise internal_return_memory_mem

Theorem internal_return_shadow_type[local]:
  lowered_value_type cenv (gas_shadow_expr e) = lowered_value_type cenv e
Proof
  Cases_on `e` >>
  simp[gasShadowTheory.gas_shadow_expr_def,
    exprLoweringTheory.lowered_value_type_def, vyperASTTheory.expr_type_def]
  >- (Cases_on `b` >>
      simp[gasShadowTheory.gas_shadow_builtin_def,
        exprLoweringTheory.lowered_value_type_def, vyperASTTheory.expr_type_def,
        listTheory.MAP_MAP_o, combinTheory.o_DEF] >>
      metis_tac[gasShadowTheory.gas_shadow_builtin_def,
        exprLoweringTheory.lowered_value_type_def, vyperASTTheory.expr_type_def,
        listTheory.MAP_MAP_o, combinTheory.o_DEF])
  >- (Cases_on `t0` >>
      simp[exprLoweringTheory.lowered_value_type_def, vyperASTTheory.expr_type_def,
        listTheory.MAP_MAP_o, combinTheory.o_DEF,
        gasShadowTheory.gas_shadow_expr_type] >>
      Cases_on `l` >> simp[gasShadowTheory.gas_shadow_expr_type, ETA_THM])
  >> Cases_on `c` >>
  simp[exprLoweringTheory.lowered_value_type_def, vyperASTTheory.expr_type_def]
QED

Theorem internal_return_full_shadow_copy[local]:
  ~is_word_type ty /\ 0 < type_memory_bytes cenv ty /\
  compile_store_memory cenv op dst ty ty sa = ((),sm) /\
  emit_inst RET [rpc] [] sm = ((),sb) /\
  compile_store_memory cenv op' dst ty ty sa' = ((),sm') /\
  emit_inst RET [rpc] [] sm' = ((),sb') /\
  gas_shadow_state sb sb' ==>
  op = op' /\ gas_shadow_state sa sa'
Proof
  Cases_on `is_bytestring_type ty` >>
  simp[compile_store_memory_def, compile_store_bytestring_def,
    compile_bytestring_copy_len_def, comp_bind_def, comp_ignore_bind_def,
    emit_op_def, emit_void_def, emit_inst_def, fresh_var_def, fresh_id_def,
    emit_def, comp_return_def] >>
  strip_tac >>
  gvs[comp_bind_def, comp_ignore_bind_def, fresh_var_def, fresh_id_def,
    emit_def, comp_return_def, gas_shadow_state_def, gas_shadow_inst_def,
    mk_inst_def] >>
  Cases_on `type_memory_bytes cenv ty` >>
  gvs[contextTheory.compile_copy_memory_def, emitHelperTheory.emit_void_def,
    emitHelperTheory.emit_inst_def, comp_ignore_bind_def, comp_bind_def,
    fresh_id_def, emit_def, comp_return_def,
    gasShadowStateTheory.gas_shadow_inst_def, venomInstTheory.mk_inst_def]
QED

Theorem internal_return_full_prefix[local]:
  cenv.ce_return_pc = SOME (PtrVar (Var rpc) rsz) /\
  cenv.ce_returns_count = 0 /\
  cenv.ce_return_buf = SOME (PtrVar (Var bp) cap) /\
  stmt_env cenv lctx ty (Return (SOME e)) sa = (cenv',sb) /\
  fn_has_code sa sb func ==>
  cenv' = cenv /\
  ?op sm. lower_value compile_expr cenv ty e sa = (op,sm) /\
    fn_has_code sa sm func /\ fn_has_code sm sb func
Proof
  strip_tac >>
  qpat_x_assum `stmt_env _ _ _ _ _ = _` mp_tac >>
  simp[stmt_env_def, declare_stmt_local_def, compile_stmt_def,
    comp_bind_def, comp_ignore_bind_def, comp_return_def,
    compile_internal_return_from_env_def] >>
  pairarg_tac >> simp[] >> strip_tac >> gvs[] >>
  pairarg_tac >> gvs[] >>
  `cs_extends sa cs''` by
    metis_tac[ci_mono_compile_expr_sa, ci_mono_def, pairTheory.SND] >>
  `cs_extends cs'' cs'` by
    metis_tac[cj 1 ci_mono_return_helpers, ci_mono_def, pairTheory.SND] >>
  metis_tac[fn_has_code_split]
QED

Theorem internal_return_buffer_ret_ptr[local]:
  emit_inst RET [Var rpc] [] sa = ((),sb) /\
  fn_has_code sa sb func /\ lookup_var rpc s = SOME pc /\
  op_taint tn (Var rpc) = {} /\ ~ctx_has_dalloca ctx /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  gas_path_ptr D 0 ctx func PG G tn s 0 G tn
    (IntRet <|iret_values := []; iret_adopt_fmp := NONE|> s)
Proof
  strip_tac >>
  qpat_x_assum `emit_inst _ _ _ _ = _` mp_tac >>
  simp[emit_inst_def, comp_bind_def, fresh_id_def, emit_def] >>
  strip_tac >> gvs[] >>
  drule fn_has_code_same_block >> simp[] >> strip_tac >>
  `!fuel. step_inst fuel ctx (mk_inst sa.cs_next_id RET [Var rpc] []) s =
    IntRet <|iret_values := []; iret_adopt_fmp := NONE|> s` by
    (simp[step_inst_non_invoke, mk_inst_def] >>
     irule (step_ret_values |> Q.SPEC `sa.cs_next_id` |> Q.SPEC `[]` |> SRULE [mk_inst_def, eval_operands_def]) >>
     metis_tac[]) >>
  irule (cj 3 fragGasPathPtrTheory.gas_path_ptr_rules) >>
  simp[exit_result_def, fragGasPathPtrTheory.gas_path_ptr_edge_def] >>
  qexists_tac `0` >>
  simp[gasCountTheory.gas_count_step_def, ptrSafeRunTheory.ptr_safe_step_def,
       ptrSafeRunTheory.ptr_inst_ok_def, mk_inst_def,
       ptrDisciplineTheory.access_ok_def, ptrDisciplineTheory.taint_ok_def,
       ptrDisciplineTheory.allocas_from_def,
       contextCodegenRelTheory.source_memory_read_ranges_def,
       codegenRelTheory.source_memory_write_ranges_def]
QED

Theorem internal_return_memory_full:
  !D lo ctx shadow_ctx PG func shadow_func tops cx ce cenv env es
   ty tv e lctx bw rpc rsz.
  body_inv tops ctx cenv cx /\ cenv.ce_module = NONE /\
  cenv.ce_module_vars =
    add_immutable_locations (get_struct_fields (make_struct_fields_map tops))
      tops 0 (add_module_var_locations tops FEMPTY) /\
  same_frame ce cenv /\ expr_sim_inv cenv cx env es /\
  cenv.ce_return_pc = SOME (PtrVar (Var rpc) rsz) /\
  cenv.ce_returns_count = 0 /\ cenv.ce_imm_alloca = NONE /\
  lowered_value_type cenv e = expr_type e /\ expr_type e = ty /\
  ~is_word_type ty /\
  evaluate_type (get_tenv cx) ty = SOME tv /\ 0 < type_memory_size tv /\
  stmt_exprs_ok cenv (Return (SOME e)) /\
  IS_SOME (type_stmt env ty (Return (SOME e))) /\
  call_evaluation_safe cx (int_calls_stmt (Return (SOME e))) /\
  w2n bw + type_memory_size tv + 64 < dimword (:256) /\
  (cenv.ce_is_ctor ==> !nm io ity itv.
    FLOOKUP cenv.ce_module_vars (cenv.ce_module,nm) = SOME (ImmutableLoc io) /\
    cenv.ce_module_var_type (cenv.ce_module,nm) = SOME ity /\
    evaluate_type (get_tenv cx) ity = SOME itv ==>
    regions_disjoint io (type_memory_size itv) (w2n bw) (type_memory_size tv)) /\
  (!ety. expr_sim_full
     (D,lo,SOME (bw,type_memory_size tv),ctx,shadow_ctx,PG,func,shadow_func)
     cenv cx ety e es /\
   expr_vv_sim_full
     (D,lo,SOME (bw,type_memory_size tv),ctx,shadow_ctx,PG,func,shadow_func)
     cenv cx ety e es) ==>
  stmt_frag_full
    (D,lo,SOME (bw,type_memory_size tv),ctx,shadow_ctx,PG,func,shadow_func)
    cx lctx (\v ee gt r. intret_mem_q func ce cx tv bw v ee r) cenv
    (stmt_env cenv lctx ty (Return (SOME e)))
    (stmt_env cenv lctx ty (Return (SOME (gas_shadow_expr e))))
    (eval_stmt cx (Return (SOME e))) es
Proof
  rpt gen_tac >> strip_tac >>
  pure_rewrite_tac[stmt_frag_full_def] >> rpt gen_tac >> strip_tac >>
  `?bp cap. cenv.ce_return_buf = SOME (PtrVar (Var bp) cap) /\
    lookup_var bp s0 = SOME bw /\ not_fresh_at sa bp /\
    w2n bw + type_memory_size tv <= s0.vs_alloca_next` by
    fs[return_buf_frame_def] >>
  qpat_assum `stmt_env _ _ _ (Return (SOME e)) sa = _`
    (mp_then Any mp_tac internal_return_full_prefix) >>
  simp[] >> disch_then drule_all >> strip_tac >>
  qpat_assum `stmt_env _ _ _ (Return (SOME (gas_shadow_expr e))) shadow_sa = _`
    (mp_then Any mp_tac internal_return_full_prefix) >>
  simp[] >> disch_then drule_all >> strip_tac >>
  `type_memory_bytes cenv ty = type_memory_size tv` by
    metis_tac[exprSimHypsTheory.expr_sim_inv_memory_size] >>
  `compile_internal_return cenv (SOME op) (Var rpc) 0 ty ty
    (case ty of TupleT tys => tys | StructT nsid =>
      MAP (FST o SND) (get_struct_fields cenv.ce_struct_fields
        (nsid_to_string nsid)) | _ => []) (SOME (Var bp)) sm = ((),sb)` by
    (qpat_assum `stmt_env _ _ _ (Return (SOME e)) sa = _`
       (mp_then Any mp_tac internal_return_memory_code) >>
     simp[] >> disch_then drule_all >> simp[]) >>
  `lowered_value_type cenv (gas_shadow_expr e) = ty` by
    simp[internal_return_shadow_type] >>
  `compile_internal_return cenv (SOME op') (Var rpc) 0 ty ty
    (case ty of TupleT tys => tys | StructT nsid =>
      MAP (FST o SND) (get_struct_fields cenv.ce_struct_fields
        (nsid_to_string nsid)) | _ => []) (SOME (Var bp)) sm' = ((),shadow_sb)` by
    (qpat_assum `stmt_env _ _ _ (Return (SOME (gas_shadow_expr e))) shadow_sa = _`
       (mp_then Any mp_tac internal_return_memory_code) >> simp[] >>
     disch_then drule_all >> simp[]) >>
  qpat_x_assum `compile_internal_return _ (SOME op) _ _ _ _ _ _ _ = _` mp_tac >>
  simp[compile_internal_return_def, comp_ignore_bind_def, comp_bind_def] >>
  pairarg_tac >> simp[] >> strip_tac >>
  qpat_x_assum `compile_internal_return _ (SOME op') _ _ _ _ _ _ _ = _` mp_tac >>
  simp[compile_internal_return_def, comp_ignore_bind_def, comp_bind_def] >>
  pairarg_tac >> simp[] >> strip_tac >>
  fs[oneTheory.one] >>
  `0 < type_memory_bytes cenv ty` by metis_tac[] >>
  drule_all internal_return_full_shadow_copy >> strip_tac >>
  qpat_x_assum `op = op'` (SUBST_ALL_TAC o SYM) >>
  `gas_admissible (bind (eval_expr cx e) (read_result cx)) expr_res_ok es` by
    metis_tac[return_forced_admissible] >>
  `!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==>
     not_fresh_at sa x` by metis_tac[ret_pc_ok_def] >>
  qpat_x_assum `!ety. _` (qspec_then `ty` strip_assume_tac) >>
  qpat_x_assum `expr_sim_full _ _ _ _ _ _` mp_tac >>
  pure_rewrite_tac[expr_sim_full_def] >> strip_tac >>
  qpat_x_assum `!sa sb shadow_sa shadow_sb op s0 G0 tn0. _`
    (qspecl_then [`sa`, `sm`, `shadow_sa`, `sm'`, `op`, `s0`, `G0`, `tn0`] mp_tac) >>
  simp[] >> strip_tac >>
  qpat_x_assum `gas_outcome_full _ _ (bind _ _) _ _ _`
    (strip_assume_tac o ONCE_REWRITE_RULE [gas_outcome_full_def])
  >- suspend "normal_joint_suffix"
  >- (gvs[] >> Cases_on `res`
      >- gvs[expr_exit_def] >>
      rename1 `expr_exit (INR err) r` >>
      pure_rewrite_tac[gas_outcome_full_def] >>
      qexists_tac `marks` >> disj1_tac >>
      qexistsl_tac [`INR err`, `ee`, `r`, `G'`, `tn'`] >>
      conj_tac
      >- (gen_tac >> gvs[eval_return_forced, bind_def]) >>
      simp[] >> disj2_tac >>
      Cases_on `err` >> Cases_on `r` >>
      gvs[stmt_exit_ptr_def, expr_exit_def] >>
      rename1 `Error err` >> Cases_on `err` >> gvs[expr_exit_def]) >>
  simp[gas_outcome_full_def] >> qexists_tac `marks` >> disj2_tac >>
  metis_tac[return_forced_exempt]
QED

Resume internal_return_memory_full[normal_joint_suffix]:
  markerLib.RESUME_TAC >> fs[] >>
  `~t.vs_halted` by
    (drule gas_origin_ptr_path_exec >> simp[exit_result_def] >> metis_tac[]) >>
  `post_value_type cenv e = ty` by metis_tac[post_value_type_lowered] >>
  `?pc. lookup_var rpc t = SOME pc` by
    (fs[ret_pc_ok_def, expr_post_def] >> metis_tac[]) >>
  `lookup_var bp t = SOME bw` by (fs[expr_post_def] >> metis_tac[]) >>
  `not_fresh_at sm bp /\ not_fresh_at sm rpc` by
    metis_tac[not_fresh_at_mono, ci_mono_compile_expr_sa, ci_mono_def, pairTheory.SND] >>
  `!x. op = Var x ==> not_fresh_at sm x` by
    metis_tac[compile_lower_value_var] >>
  `?w. eval_operand op t = SOME w` by
    (fs[expr_post_def, expr_val_rel_def] >> metis_tac[]) >>
  `?src. op = Var src` by
    (fs[ptr_buf_ok_def] >> gvs[]) >>
  `bind (eval_expr cx e) (read_result cx)
     (es with gas_obs := gas_explicit marks s0.vs_gas_readings) =
     (INL v,ee with gas_obs := [])` by
    (qpat_assum `!tail. bind _ _ _ = _`
       (qspec_then `[]` assume_tac) >> fs[listTheory.APPEND_NIL]) >>
  `value_has_type tv v` by
    (drule_all returnValueTypedTheory.return_value_typed >> fs[]) >>
  `val_wf tv v` by
    metis_tac[valueTypingMemoryPropsTheory.value_has_type_memory_wf] >>
  `env_consistent env cx (ee with gas_obs := [])` by
    (irule internal_return_source_env >> fs[expr_sim_inv_def] >> metis_tac[]) >>
  `stmt_state_rel ctx func cenv cx
     ((ee with gas_obs := []) with scopes := []) t` by
    (fs[expr_post_def, stmt_state_rel_def, immutable_alloca_sep_def,
        local_region_def, lookup_scopes_def] >> conj_tac
     >- (irule constructor_exit_state_rel >> qexists_tac `cenv` >> simp[state_rel_gas_obs]) >>
     metis_tac[]) >>
  `cenv.ce_is_ctor ==> !name itv iv off.
     FLOOKUP cenv.ce_module_vars (cenv.ce_module,name) = SOME (ImmutableLoc off) /\
     FLOOKUP (case ALOOKUP ee.immutables cx.txn.target of NONE => FEMPTY
       | SOME imms => get_source_immutables cenv.ce_module imms) name =
       SOME (itv,iv) ==>
     regions_disjoint off (type_memory_size itv) (w2n bw) (type_memory_size tv)` by
    (strip_tac >>
     drule_at (Pos (el 5)) internal_return_immutable_separation >>
     simp[] >> metis_tac[]) >>
  `compile_internal_return cenv (SOME op) (Var rpc) 0 ty ty
     (case ty of TupleT tys => tys | StructT nsid =>
       MAP (FST o SND) (get_struct_fields cenv.ce_struct_fields
         (nsid_to_string nsid)) | _ => []) (SOME (Var bp)) sm = ((),sb)` by
    (qpat_assum `stmt_env _ _ _ (Return (SOME e)) sa = _`
       (mp_then Any mp_tac internal_return_memory_code) >>
     simp[] >> disch_then drule_all >> simp[]) >>
  `?n rr. gas_path_mem ctx func t n rr /\ exit_result rr /\
     !tail. intret_mem_q func ce cx tv bw v
       ((ee with gas_obs := tail) with scopes := []) rr` by
    (irule internal_return_memory_suffix >>
     qpat_assum `compile_internal_return _ _ _ _ _ _ _ _ _ = _` (irule_at Any) >>
     qexistsl_tac [`tv`, `pc`] >>
     `acyclic_struct_metadata cenv.ce_struct_fields` by fs[body_inv_def] >>
     fs[expr_post_def, expr_sim_inv_def] >>
     rpt conj_tac >- first_assum ACCEPT_TAC
     >- gvs[] >>
     qpat_x_assum `stmt_state_rel _ _ _ _ (ee with <|scopes := []; gas_obs := []|>) t` mp_tac >>
     `ee with <|scopes := []; gas_obs := []|> =
       (ee with scopes := []) with gas_obs := []` by simp[] >>
     pop_assum SUBST1_TAC >>
     simp[exprSimWordArgsTheory.stmt_state_rel_gas_obs]) >>
  `?a. lookup_var src t = SOME a /\
     ptr_covers G' tn' src t (type_memory_size tv) /\
     (!m. mem_agree_outside tn'.t_mem t.vs_memory m ==>
       val_in_memory tv v (w2n a) m)` by
    (drule annassign_memory_rhs_layout_ptr >>
     disch_then (qspecl_then [`G'`, `tn'`, `tv`, `ty`, `tv`] mp_tac) >>
     simp[] >> metis_tac[]) >>
  `ptr_covers G' tn' bp t (type_memory_size tv)` by
    (fs[ghost_inv_at_def, return_buf_ptr_def] >> gvs[]) >>
  `?len k. k < dimword (:256) /\
     ptr_covers G' tn' src t k /\ ptr_covers G' tn' bp t k /\
     (if is_bytestring_type ty then
       k = 32 + 32 * ((len + 31) DIV 32) /\ mload (w2n a) t = n2w len /\
       (!i. w2n a <= i /\ i < w2n a + 32 ==> i NOTIN tn'.t_mem)
      else k = type_memory_bytes cenv ty) /\ val_footprint tv v <= k` by
    (Cases_on `is_bytestring_type ty`
     >- (drule annassign_bytestring_window_ptr >>
         disch_then (qspecl_then [`get_tenv cx`, `ty`, `tv`, `tv`, `v`, `w2n a`, `t`, `tn'`] mp_tac) >>
         simp[] >> strip_tac >> qexists_tac `len` >>
         simp[] >>
         conj_tac >- (fs[ptr_covers_def] >> metis_tac[arithmeticTheory.LESS_EQ_TRANS, arithmeticTheory.LESS_EQ_LESS_EQ_MONO]) >>
         fs[ptr_covers_def] >> metis_tac[arithmeticTheory.LESS_EQ_TRANS, arithmeticTheory.LESS_EQ_LESS_EQ_MONO]) >>
     qexistsl_tac [`0`, `type_memory_size tv`] >> simp[] >>
     irule annassign_memory_source_footprint_ptr >> metis_tac[]) >>
  `cs_extends sm cs' /\ cs_extends cs' sb` by
    metis_tac[externalEntryShapeTheory.compile_store_memory_labels, cs_extends_emit_inst, pairTheory.SND] >>
  `fn_has_code sm cs' func /\ fn_has_code cs' sb func` by
    metis_tac[fn_has_code_split] >>
  qpat_assum `op = Var src` SUBST_ALL_TAC >>
  `not_fresh_at sm src` by metis_tac[] >>
  drule_all (annassign_store_memory_path_ptr |> SPEC_ALL |>
    Q.INST [`sty` |-> `ty`] |> SRULE []) >>
  disch_then (qspecl_then [`PG`, `D`] strip_assume_tac) >>
  `lookup_var rpc sf = SOME pc /\ op_taint tnf (Var rpc) = {}` by
    (fs[ghost_inv_at_def] >> metis_tac[]) >>
  `gas_path_ptr D 0 ctx func PG Gf tnf sf 0 Gf tnf
    (IntRet <|iret_values := []; iret_adopt_fmp := NONE|> sf)` by
    (irule internal_return_buffer_ret_ptr >> metis_tac[]) >>
  `gas_path_ptr D 0 ctx func PG G' tn' t 0 Gf tnf
    (IntRet <|iret_values := []; iret_adopt_fmp := NONE|> sf)` by
    metis_tac[fragGasPathPtrTheory.gas_path_ptr_then, arithmeticTheory.ADD_0] >>
  `?fuel. run_from fuel ctx func t = rr` by
    metis_tac[fragGasPathMemTheory.gas_path_mem_exec, exit_result_def] >>
  `?fuel'. run_from fuel' ctx func t =
    IntRet <|iret_values := []; iret_adopt_fmp := NONE|> sf` by
    (drule gasPathPtrExecTheory.gas_path_ptr_exec >>
     simp[exit_result_def] >> metis_tac[]) >>
  `rr = IntRet <|iret_values := []; iret_adopt_fmp := NONE|> sf` by
    (metis_tac[fragGasPathTheory.gas_run_from_fuel_mono,
       exit_result_not_error, exit_result_def, arithmeticTheory.LESS_EQ_CASES]) >>
  `gas_path_ptr D lo ctx func PG G' tn' t 0 Gf tnf rr` by
    (irule ptrSafetyTransportTheory.gas_path_ptr_lower_bound_transport >>
     fs[ghost_inv_at_def] >> qexists_tac `0` >> simp[]) >>
  `gas_origin_ptr_path (D,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
     (t,G',tn') [] (rr,Gf,tnf)` by
    (irule gas_terminal_zero_ptr_joint >> metis_tac[]) >>
  `gas_origin_ptr_path (D,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
     (s0,G0,tn0) marks (rr,Gf,tnf)` by
    metis_tac[fragGasOriginPtrTheory.gas_origin_ptr_path_append, listTheory.APPEND_NIL] >>
  pure_rewrite_tac[gas_outcome_full_def] >>
  qexists_tac `marks` >> disj1_tac >>
  qexistsl_tac [`INR (ReturnException v)`, `ee`, `rr`, `Gf`, `tnf`] >>
  conj_tac
  >- (gen_tac >> gvs[eval_return_forced, bind_def, raise_def]) >>
  simp[stmt_exit_ptr_def] >> metis_tac[]
QED
Finalise internal_return_memory_full
