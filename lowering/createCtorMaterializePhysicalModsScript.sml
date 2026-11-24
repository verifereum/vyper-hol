(* The materialization source is interpreted at the endpoint of the
   ordinary unwrap, not at the endpoint of a second execution. *)
Theory createCtorMaterializePhysicalMods
Ancestors
  createCtorMaterializePhysical createExprSizeExitDefsMods
  assignEffectfulIndexPhysical bodyMemSnapshotSourceLocation
  immutableDeployPhysicalSource aggregateEvaluatedLayout bodyFullStructLitInputs
  exprBodyPreProps exprSimHyps exprLowering context loweringPosts bodyPtrDefs
  assignTuplePtrCopyLen[qualified] loweringStateRelDefs vyperState
  vyperTypeExprSoundness valueCopyBytes finite_map pred_set

Theorem ctor_physical_static_mods[local]:
  expr_sim_inv_mods mods ce cx env es ==>
  !e. well_typed_expr env e ==>
    arg_type_fits (lowered_value_type ce e) (expr_type e) /\
    (post_value_type ce e = expr_type e \/
     post_value_type ce e = lowered_value_type ce e) /\
    (post_value_type ce e = lowered_value_type ce e \/
     is_bytestring_type (post_value_type ce e) /\
     is_bytestring_type (lowered_value_type ce e))
Proof
  strip_tac >> gen_tac >> strip_tac >>
  `!fid sg. FLOOKUP env.fn_sigs fid = SOME sg ==>
            ce.ce_func_return_type (nsid_to_string fid) = sg.ret_ty` by
    metis_tac[expr_sim_inv_mods_return_type] >>
  Cases_on `?ty fid args drv. e = Call ty (IntCall fid) args drv`
  >- (pop_assum strip_assume_tac >> gvs[] >> PairCases_on `fid` >>
      gvs[vyperTypeSystemTheory.well_typed_expr_def, lowered_value_type_def,
          vyperASTTheory.expr_type_def] >>
      first_x_assum (drule_then SUBST1_TAC) >>
      rename1 `type_widens_to env.type_defs sg.ret_ty ty` >>
      `arg_type_fits sg.ret_ty ty` by
        fs[vyperTypeSystemTheory.type_widens_to_def] >>
      Cases_on `is_word_type ty` >> simp[]
      >- metis_tac[compileEnvTheory.type_widens_to_word] >>
      Cases_on `is_bytestring_type ty` >> simp[] >>
      disj2_tac >> irule compileEnvTheory.arg_type_fits_bytestring_source >>
      goal_assum drule >> simp[]) >>
  `env_consistent env cx es` by metis_tac[expr_sim_inv_mods_env] >>
  `env.type_defs = get_tenv cx` by
    fs[vyperTypeInvariantsTheory.env_consistent_def,
       vyperTypeInvariantsTheory.env_context_consistent_def] >>
  `!id t. FLOOKUP env.var_types id = SOME t ==>
          well_formed_type env.type_defs t` by
    metis_tac[exprSimSourceTheory.env_consistent_var_type_evaluates,
              vyperTypeSystemTheory.well_formed_type_def] >>
  `sfields_tenv_consistent ce.ce_struct_fields env.type_defs` by
    fs[exprSimHypsDefsTheory.expr_sim_inv_mods_def] >>
  `post_value_type ce e = expr_type e` by
    metis_tac[post_value_type_not_int_call] >>
  drule_all exprSimIfExpCompatTheory.ifexp_lowered_type_classify >>
  strip_tac >> gvs[]
QED

Theorem ctor_physical_memory_size_mods[local]:
  expr_sim_inv_mods mods ce cx env es /\
  evaluate_type (get_tenv cx) ty = SOME rt ==>
  type_memory_bytes ce ty = type_memory_size rt
Proof
  strip_tac >> irule typedMemoryCopyTheory.typed_copy_memory_size >>
  qexists_tac `get_tenv cx` >> fs[exprSimHypsDefsTheory.expr_sim_inv_mods_def] >> metis_tac[]
QED

Theorem ctor_materialize_unwrap_retag_mods:
  expr_body_pre_mods mods ce cx env e es /\
  compile_expr ce ty e sa = (vv,sm) /\
  eval_expr cx e es = (INL tv,ee) /\
  read_result cx tv ee = (INL v,ee) /\
  vv_post_mods H ctx func ce cx e es sa sm s0 ee tv vv a /\
  ~is_word_type (lowered_value_type ce e) /\
  unwrap_value ce (ext_call_arg_value (lowered_value_type ce e) vv) mid = (op,su) ==>
  unwrap_value ce vv mid = (op,su) /\
  ~is_word_type (post_value_type ce e) /\
  ?rty. evaluate_type (get_tenv cx) (post_value_type ce e) = SOME rty /\
        (!val. read_result cx tv ee = (INL val,ee) ==> value_has_type rty val) /\
        type_memory_bytes ce (post_value_type ce e) = type_memory_size rty /\
        type_memory_size rty < 2 ** 64
Proof
  cheat
QED

Theorem ctor_materialize_unwrap_physical_mods:
  expr_body_pre_mods mods ce cx env e es /\
  eval_expr cx e es = (INL tv,ee) /\
  read_result cx tv ee = (INL v,ee) /\
  ~is_word_type (lowered_value_type ce e) /\
  expr_post_mods H ctx func ce cx e es sa su s0 ee v op z /\
  ptr_val_ok cx (post_value_type ce e) v op Gz tz z /\
  ptr_buf_ok ce e op Gz z /\
  (!rt w. evaluate_type (get_tenv cx) (lowered_value_type ce e) = SOME rt /\
          eval_operand op z = SOME w ==>
          type_memory_size rt = 0 \/ w2n w + type_memory_size rt <= z.vs_alloca_next) /\
  wb_frame ce ee ee mid a z /\
  ghost_kept_at lo ce ee mid Ga ta a Gz tz ==>
  (?stv sw.
     evaluate_type (get_tenv cx) (lowered_value_type ce e) = SOME stv /\
     value_has_type stv v /\ val_wf stv v /\
     type_memory_bytes ce (lowered_value_type ce e) = type_memory_size stv /\
     eval_operand op z = SOME sw /\ op_taint tz op = {} /\
     (!mem. mem_agree_outside tz.t_mem z.vs_memory mem ==>
            val_in_memory stv v (w2n sw) mem) /\
     (type_memory_size stv = 0 \/ w2n sw + type_memory_size stv <= z.vs_alloca_next) /\
     (0 < type_memory_size stv ==>
      ?src. op = Var src /\ ptr_covers Gz tz src z (type_memory_size stv))) /\
  (!p w aid b n.
     not_fresh_at mid p /\ lookup_var p a = SOME w /\ ptr_covers Ga ta p a n /\
     FLOOKUP a.vs_allocas aid = SOME (b,n) /\ aid < mid.cs_next_id /\
     (!id base len. local_region ce ee.scopes a id base len ==>
                    regions_disjoint b n base len) ==>
     lookup_var p z = SOME w /\ ptr_covers Gz tz p z n /\
     FLOOKUP Gz p = FLOOKUP Ga p /\ op_taint tz (Var p) = op_taint ta (Var p) /\
     FLOOKUP z.vs_allocas aid = SOME (b,n) /\
     mem_bytes_at b n z.vs_memory = mem_bytes_at b n a.vs_memory /\
     (!i. b <= i /\ i < b+n /\ i IN tz.t_mem ==> i IN ta.t_mem))
Proof
  cheat
QED
