(* Empty-path immutable augmented-assignment entry interfaces. *)
Theory immutableAugAssignRootEntry
Ancestors
  bodyAugAssignOther bodyAugPlaceTarget immutableWordReadMemory
  immutableAugAssignRootPrefix
  exprSimPopImmutableTarget augAssignPlaceCompileMemory immutableAugAssignRootSource
  supportedStmts supportedExprForms supportedTypes vyperTypeSystem vyperTypeInvariants

Theorem immutable_augassign_root_metadata:
  body_inv tops ctx cenv cx /\ expr_sim_inv cenv cx env es /\
  supported_stmt tops bindings (AugAssign ty (TopLevelNameTarget (src,id)) bop e) /\
  type_stmt env ret_ty (AugAssign ty (TopLevelNameTarget (src,id)) bop e) = SOME env' /\
  immutable_root cx (TopLevelNameTarget (src,id)) ==>
  ?ts off tv iv.
    get_module_code cx src = SOME ts /\ find_var_decl_by_name id ts = NONE /\
    src = cenv.ce_module /\ cx.in_deploy /\ cenv.ce_is_ctor /\
    cenv.ce_module_var_type (src,id) = SOME ty /\
    FLOOKUP env.bare_global_assignable (src,id) = SOME ty /\
    FLOOKUP cenv.ce_module_vars (src,id) = SOME (ImmutableLoc off) /\
    off + type_memory_size tv < dimword (:256) /\
    FLOOKUP (case ALOOKUP es.immutables cx.txn.target of
               NONE => FEMPTY | SOME imms => get_source_immutables src imms) id =
      SOME (tv,iv) /\
    evaluate_type (get_tenv cx) ty = SOME tv /\
    well_typed_binop ty bop ty (expr_type e) /\ bop <> In /\ bop <> NotIn /\
    (bop = Exp ==> nonneg_int_literal e) /\
    (bop = ShL \/ bop = ShR ==> shift_amount_ok e)
Proof
  strip_tac >>
  `type_place_target env (TopLevelNameTarget (src,id)) = SOME (Type ty) /\
   well_typed_binop ty bop ty (expr_type e) /\ bop <> In /\ bop <> NotIn /\
   augassign_operand_ok ty bop e` by
    gvs[type_stmt_def, well_typed_target_def, AllCaseEqs()] >>
  `!ts. get_module_code cx src = SOME ts ==> find_var_decl_by_name id ts = NONE` by
    gvs[targetPlaceSimTheory.immutable_root_def, targetPlaceSimTheory.target_root_def] >>
  drule_all imm_target_root_assignable >> strip_tac >>
  drule_all imm_target_root_layout >> strip_tac >>
  `cx.in_deploy /\ cenv.ce_is_ctor /\
   cenv.ce_module_var_type (src,id) = SOME ty` by
    (conj_asm1_tac
     >- (spose_not_then assume_tac >>
         fs[exprSimHypsDefsTheory.expr_sim_inv_def, env_consistent_def,
            env_context_consistent_def, bare_global_assignable_complete_def] >>
         gvs[]) >>
     gvs[exprSimHypsDefsTheory.expr_sim_inv_def,
         exprSimHypsDefsTheory.bare_globals_layout_def,
         env_consistent_def, env_context_consistent_def] >>
     qpat_x_assum `!src id ty. FLOOKUP env.bare_global_assignable _ = _ ==> ?ts. _`
       drule >> strip_tac >>
     qpat_x_assum `!src id ty. FLOOKUP env.bare_globals _ = _ ==>
                              cenv.ce_module_var_type _ = _` drule >> simp[] >>
     metis_tac[exprSimHypsDefsTheory.expr_sim_inv_def,
       env_consistent_def, env_context_consistent_def,
       bare_global_assignable_complete_def, exprSimHypsDefsTheory.bare_globals_layout_def]) >>
  drule stmtSimAugAssignTheory.augassign_operand_ok_operands >> simp[] >>
  metis_tac[]
QED
