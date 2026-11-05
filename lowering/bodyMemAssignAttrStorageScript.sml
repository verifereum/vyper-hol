(* Memory case of the body induction, assignment to a base target
   (bodyMemAssign's dispatch): a word field of a storage or transient struct (S1's body_assign_attr_storage). *)
Theory bodyMemAssignAttrStorage
Ancestors
  bodyMemoryPreds bodyMemAugAssignAttrStorage vyperInterpreter vyperState
  vyperStorageBackend loweringPosts exprSimProps compileEnv venomExecSemantics venomState
  exprSimMemUnwrap exprLoweringProps exprSimMemDefs
Libs
  monadsyntax

Theorem eval_assign_attr_toplevel_action_mem_src[local]:
  get_module_code cx src = SOME ts /\
  find_var_decl_by_name id ts = SOME (StorageVarDecl tr typ, id_str) /\
  lookup_var_slot_from_layout cx tr src id_str = SOME slot /\
  evaluate_type (get_tenv cx) typ = SOME (StructTV fs) /\
  struct_field_slot fs fld = SOME (off, ftv) ==>
  eval_stmt cx
    (Assign (BaseTarget (AttributeTarget (TopLevelNameTarget (src,id)) fld)) e) =
  bind (bind (eval_expr cx e) (read_result cx))
    (write_storage_slot cx tr (n2w slot + n2w off) ftv)
Proof
  strip_tac >>
  `!es. eval_target_place cx
    (AttributeTarget (TopLevelNameTarget (src,id)) fld) es =
    (INL (StoragePlace tr (n2w slot + n2w off) ftv), es)` by
    (gen_tac >> irule (cj 1 eval_target_place_attr_toplevel_field_mem_src) >>
     goal_assum (drule_at Any) >> simp[]) >>
  simp[Once evaluate_def, FUN_EQ_THM, bind_def] >> qx_gen_tac `st` >>
  Cases_on `eval_expr cx e st` >> Cases_on `q` >> simp[] >>
  simp[write_place_def, bind_def] >>
  Cases_on `read_result cx x' r` >> Cases_on `q` >> simp[]
QED

Theorem vv_at_start_var_mem_src[local]:
  vv_at ce cx ty (sa with cs_next_var := n) sb es tv vv s <=>
  vv_at ce cx ty sa sb es tv vv s
Proof
  Cases_on `vv` >> simp[vv_at_def, expr_val_at_def]
QED

Theorem vv_post_rebase_mem_src[local]:
  vv_post ctx func ce cx e es sa sm s0 ee tv vv s ==>
  vv_post ctx func ce cx e ee (sa with cs_next_var := sm.cs_next_var)
    sm s ee tv vv s
Proof
  simp[vv_post_def, vv_at_start_var_mem_src, locals_kept_refl]
QED

Theorem expr_post_rebased_operand_mem_src[local]:
  expr_post ctx func ce cx e ee (sa with cs_next_var := sm.cs_next_var)
    sb s ee v op u /\
  (?x. dst = Var x /\ not_fresh_at sm x) /\
  eval_operand dst s = SOME w ==>
  eval_operand dst u = SOME w
Proof
  strip_tac >> gvs[eval_operand_def] >>
  qpat_x_assum `expr_post _ _ _ _ _ _ _ _ _ _ _ _ _` mp_tac >>
  simp[expr_post_def] >> strip_tac >>
  first_x_assum irule >> gvs[not_fresh_at_def]
QED

Theorem unwrap_value_rebased_read_mem_src[local]:
  unwrap_value cenv vv sm = (op,sb) /\
  local_ptrs_reserved cenv sa /\ sa.cs_next_var <= sm.cs_next_var /\
  sa.cs_next_id <= sm.cs_next_id /\
  fn_has_code sm sb func /\ fn_inst_ids_distinct func /\
  (!x. vv_operand vv = Var x ==> not_fresh_at sm x) /\
  is_word_type (expr_type e) /\
  (?tvt. evaluate_type (get_tenv cx) (expr_type e) = SOME tvt) /\
  vv_post ctx func cenv cx e es sa sm s0 ee tv vv s /\
  vv_store_bound cx (expr_type e) (lowered_value_type cenv e) ee tv vv s /\
  alloca_history func s /\
  ~s.vs_halted /\ s.vs_current_bb = sm.cs_current_bb /\
  s.vs_inst_idx = LENGTH sm.cs_current_insts /\
  (?x. dst = Var x /\ not_fresh_at sm x) /\
  eval_operand dst s = SOME w ==>
  ?v u. gas_marked_exec T (ctx,func) (read_result cx tv) (ee,s)
          [] (INL v) ee (OK u) /\
    expr_post ctx func cenv cx e ee (sa with cs_next_var := sm.cs_next_var)
      sb s ee v op u /\
    expr_store_bound cx (expr_type e) v op u /\
    u.vs_current_bb = sb.cs_current_bb /\
    u.vs_inst_idx = LENGTH sb.cs_current_insts /\
    alloca_history func u /\ s.vs_alloca_next <= u.vs_alloca_next /\
    eval_operand dst u = SOME w
Proof
  strip_tac >>
  drule vv_post_rebase_mem_src >> strip_tac >>
  `local_ptrs_reserved cenv sm` by
    (irule local_ptrs_reserved_next_var >> goal_assum (drule_at Any) >> simp[]) >>
  `local_ptrs_reserved cenv (sa with cs_next_var := sm.cs_next_var)` by
    (qpat_x_assum `local_ptrs_reserved cenv sm` mp_tac >>
     simp_tac (srw_ss()) [local_ptrs_reserved_def, not_fresh_at_def] >>
     metis_tac[]) >>
  qpat_x_assum `vv_post _ _ _ _ _ es _ _ _ _ _ _ _` kall_tac >>
  drule_at (Pat `unwrap_value _ _ _ = _`) unwrap_value_marked_read_mem >>
  disch_then (drule_at (Pat `vv_post _ _ _ _ _ _ _ _ _ _ _ _ _`)) >>
  impl_tac >- simp[] >> strip_tac >>
  qexistsl_tac [`v`, `u`] >> simp[] >>
  irule expr_post_rebased_operand_mem_src >> goal_assum (drule_at Any) >> gvs[]
QED

Theorem body_assign_attr_storage_mem:
  !cx nsid fld e fty d tops bindings ctx func cenv env env' ret_ty lctx RetQ es.
    body_expr_mem_ok cx e /\
    body_inv tops ctx cenv cx /\ supported_stmt tops bindings
      (Assign (BaseTarget (AttributeTarget (TopLevelNameTarget nsid) fld)) e) /\
    (!target. supported_stmt_expr_exists
       (expr_abi_decode_target_root target) (Assign (BaseTarget (AttributeTarget (TopLevelNameTarget nsid) fld)) e) ==>
       occurs_abi_decode_target target tops) /\
    expr_sim_inv cenv cx env es /\ ce_locals_declared cenv env /\
    locals_alloc_ok cenv env /\
    type_stmt env ret_ty (Assign (BaseTarget (AttributeTarget (TopLevelNameTarget nsid) fld)) e) = SOME env' /\
    stmt_exprs_ok cenv (Assign (BaseTarget (AttributeTarget (TopLevelNameTarget nsid) fld)) e) /\
    call_evaluation_safe cx (int_calls_stmt (Assign (BaseTarget (AttributeTarget (TopLevelNameTarget nsid) fld)) e)) /\
    frame_ret_ok_mem d ctx func cx RetQ cenv ret_ty /\
    supported_storage_field_write tops nsid fld /\
    type_place_target env (AttributeTarget (TopLevelNameTarget nsid) fld) =
      SOME (Type fty) /\
    is_word_type fty ==>
    stmt_frag_mem d ctx func cx lctx RetQ cenv
      (stmt_env cenv lctx ret_ty (Assign (BaseTarget (AttributeTarget (TopLevelNameTarget nsid) fld)) e))
      (eval_stmt cx (Assign (BaseTarget (AttributeTarget (TopLevelNameTarget nsid) fld)) e)) es
Proof
  cheat
QED
