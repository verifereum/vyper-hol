(* Source endpoint and compiler boundary for memory-valued internal returns. *)
Theory internalReturnMemoryMem
Ancestors
  internalReturnComposeMem internalReturnCompileMem internalReturnImmutableTypes
  vyperTypeEnvPreservation exprSimHypsDefs stmtLowering stmtLoweringMono
  exprLoweringProps compileEnv loweringPosts vyperState vyperInterpreter
  stmtSimReturn stmtSimReturnWiden intCallReturnMem bodySim ctorReturnFrame
  venomExecSemantics venomState fragExec freshWrites exprOperandVar
  bodySimFull annAssignPtrDestination ptrSafetyTransport fragGasOriginPtrExec
  gasOutcomeFullCompose

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
  FAIL_TAC "pending"
QED
