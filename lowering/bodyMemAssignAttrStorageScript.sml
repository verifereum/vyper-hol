(* Memory case of the body induction, assignment to a base target
   (bodyMemAssign's dispatch): a word field of a storage or transient struct (S1's body_assign_attr_storage). *)
Theory bodyMemAssignAttrStorage
Ancestors
  bodyMemoryPreds bodyMemAugAssignAttrStorage vyperInterpreter vyperState
  vyperStorageBackend
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
