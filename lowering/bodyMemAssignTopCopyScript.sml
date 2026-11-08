(* Memory case of the body induction, assignment to a base target
   (bodyMemAssign's dispatch): a storage or transient variable of an aggregate type, copied from
   memory (S1's body_assign_toplevel_copy). *)
Theory bodyMemAssignTopCopy
Ancestors
  bodyMemoryPreds bodyMemAssignTopCopyOutcome bodyMemAssignTopSparse bodyMemAssignTopCopyFacts
  supportedProgram supportedStmts supportedTypes bodySim exprSimDefs
  vyperStorageLayoutSafety vyperTypeEnv exprSimHypsDefs
  vyperLookupStorage bodyStorageMetadata supportedDecls

Theorem body_assign_toplevel_copy_mem:
  !cx nsid e mut ty slot d tops bindings ctx func cenv env env' ret_ty lctx RetQ es.
    body_expr_mem_ok cx e /\
    body_inv tops ctx cenv cx /\ supported_stmt tops bindings
      (Assign (BaseTarget (TopLevelNameTarget nsid)) e) /\
    (!target. supported_stmt_expr_exists
       (expr_abi_decode_target_root target) (Assign (BaseTarget (TopLevelNameTarget nsid)) e) ==>
       occurs_abi_decode_target target tops) /\
    expr_sim_inv cenv cx env es /\ ce_locals_declared cenv env /\
    locals_alloc_ok cenv env /\
    type_stmt env ret_ty (Assign (BaseTarget (TopLevelNameTarget nsid)) e) = SOME env' /\
    stmt_exprs_ok cenv (Assign (BaseTarget (TopLevelNameTarget nsid)) e) /\
    call_evaluation_safe cx (int_calls_stmt (Assign (BaseTarget (TopLevelNameTarget nsid)) e)) /\
    frame_ret_ok_mem d ctx func cx RetQ cenv ret_ty /\
    supported_variable_decl tops nsid =
      SOME (Private, mut, ty, SOME slot) /\
    (mut = Storage \/ mut = Transient) /\
    ~is_word_type ty /\ (!elem n. ty <> ArrayT elem (Dynamic n)) /\
    0 < type_memory_bytes cenv ty /\ expr_type e = ty ==>
    stmt_frag_mem d ctx func cx lctx RetQ cenv
      (stmt_env cenv lctx ret_ty (Assign (BaseTarget (TopLevelNameTarget nsid)) e))
      (eval_stmt cx (Assign (BaseTarget (TopLevelNameTarget nsid)) e)) es
Proof
  rpt gen_tac >> Cases_on `nsid` >>
  rename1 `supported_variable_decl tops (src,id)` >> strip_tac >>
  `supported_expr tops e` by
    gvs[supported_stmt_def, supported_assignment_def] >>
  drule_at (Pos (el 2)) topcopy_target >>
  disch_then drule >> simp[] >> disch_then drule >>
  disch_then drule >> strip_tac >> gvs[] >>
  `expr_body_pre cenv cx env e es` by
    (irule topcopy_rhs_pre >> goal_assum (drule_at Any) >> simp[] >> metis_tac[]) >>
  drule_all topcopy_memory_size >> strip_tac >>
  `storage_layout_safe cx` by fs[expr_sim_inv_def] >>
  `storage_var_info cx NONE id = SOME (tr,off,tvt)` by
    simp[storage_var_info_def] >>
  drule_all topcopy_region >> strip_tac >>
  `supported_storage_type tops (expr_type e)` by
    (`supported_program tops` by fs[body_inv_def] >>
     drule supported_variable_decl_mem >> strip_tac >>
     drule_all supportedProgramTheory.supported_program_declaration >>
     gvs[supported_declaration_header_def]) >>
  `lowered_value_type cenv e = expr_type e` by
    metis_tac[topcopy_rhs_lowered_type] >>
  `~is_bytestring_type (expr_type e) /\ ~has_length_word (expr_type e)` by
    metis_tac[bodySimStmtCasesTheory.topcopy_not_bytestring,
              bodySimStmtCasesTheory.topcopy_no_length_word] >>
  `expr_sim_mem ctx func cenv cx (expr_type e) e es` by
    metis_tac[topcopy_rhs_memory] >>
  `sfields_tenv_consistent cenv.ce_struct_fields (get_tenv cx)` by
    fs[expr_sim_inv_def] >>
  Cases_on `is_abi_dynamic cenv.ce_struct_fields (expr_type e)`
  >- (`acyclic_struct_metadata cenv.ce_struct_fields` by fs[body_inv_def] >>
      `!name fields.
         FLOOKUP cenv.ce_struct_fields name = SOME fields ==>
         ALL_DISTINCT (MAP FST fields) /\
         EVERY (\(fname, fty, sz). !tv.
           evaluate_type (get_tenv cx) fty = SOME tv ==>
           sz = type_memory_size tv) fields` by fs[expr_sim_inv_def] >>
      irule compile_assign_storage_sparse_stmt_frag_mem >>
      goal_assum (drule_at Any) >> simp[] >>
      rpt strip_tac >> metis_tac[topcopy_rhs_value_typed, pairTheory.PAIR_EQ]) >>
  irule compile_assign_storage_copy_stmt_frag_mem >>
  goal_assum (drule_at Any) >> simp[] >>
  rpt strip_tac >> drule_all topcopy_rhs_value_typed >> simp[]
QED
