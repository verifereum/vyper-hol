(* Source endpoint and compiler boundary for memory-valued internal returns. *)
Theory internalReturnMemoryMem
Ancestors
  internalReturnComposeMem internalReturnCompileMem internalReturnImmutableTypes
  vyperTypeEnvPreservation exprSimHypsDefs stmtLowering stmtLoweringMono
  exprLoweringProps compileEnv loweringPosts vyperState vyperInterpreter
  stmtSimReturn stmtSimReturnWiden intCallReturnMem bodySim ctorReturnFrame
  venomExecSemantics venomState fragExec

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
