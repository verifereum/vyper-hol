(*
 * Assignment-target context and assignment-operation bridge lemmas.
 *)

Theory vyperTypeAssignContext
Ancestors
  list rich_list pred_set prim_rec arithmetic finite_map option pair sum
  vyperAST vyperValue vyperValueOperation vyperMisc vyperABI
  vyperInterpreter vyperState vyperContext vyperStorage vyperTyping
  vyperEncodeDecode vyperArith vyperTypeSystem vyperTypeInvariants vyperTypeValues
  vyperTypeEnv vyperTypeEnvExtension vyperTypeEnvPreservation vyperTypeScopePop
  vyperTypeABI vyperTypeBindArguments vyperTypeExprResult vyperTypeStmtResult
  vyperTypeExtCallSoundness vyperTypeGlobalLookupSoundness
  vyperTypeBuiltins vyperTypeExprSoundness vyperTypeAssignSoundness
  vyperAssignTarget vyperExprNoControl vyperScopePreservation vyperEvalPreservesScopes
  vyperEvalMisc vyperStatePreservation vyperAssignPreservesType vyperTypeStatePreservation
Libs
  wordsLib markerLib intLib

Theorem assign_target_assignable_context_ScopedVar_equals_assignable:
  assign_target_assignable_context cx (BaseTargetV (ScopedVar id) sbs) st =
   assign_target_assignable (BaseTargetV (ScopedVar id) sbs) st
Proof
  simp[assign_target_assignable_context_def]
QED

Theorem assign_target_assignable_context_ImmutableVar[simp]:
  assign_target_assignable_context cx (BaseTargetV (ImmutableVar id) sbs) st = T
Proof
  simp[assign_target_assignable_context_def, assign_target_assignable_def]
QED

(* ===== Static assignable context predicate ===== *)
(* This predicate captures exactly the cx-dependent (non-dynamic, non-st-dependent)
   part of assign_target_assignable_context for already-evaluated assignment values.
   For ScopedVar/ImmutableVar it is trivial. For TopLevelVar it requires
   get_module_code, find_var_decl_by_num, evaluate_type, and lookup_var_slot_from_layout
   to return SOME — these are the preconditions that assign_target checks before
   proceeding, so they hold at INL-success sites and must be supplied as a premise
   at INR/no-TypeError sites. *)

Definition assignment_value_static_assignable_context_def:
  (assignment_value_static_assignable_context cx (BaseTargetV (TopLevelVar src id) sbs) =
     ?code p. get_module_code cx src = SOME code ∧
              find_var_decl_by_num (string_to_num id) code = SOME p ∧
              (case FST p of
                | StorageVarDecl is_transient typ =>
                    IS_SOME (evaluate_type (get_tenv cx) typ) ∧
                    IS_SOME (lookup_var_slot_from_layout cx is_transient src (SND p))
                | HashMapVarDecl is_transient kt vt =>
                    sbs <> [] ∧
                    IS_SOME (lookup_var_slot_from_layout cx is_transient src (SND p)))) ∧
  (assignment_value_static_assignable_context cx (BaseTargetV (ScopedVar _) sbs) = T) ∧
  (assignment_value_static_assignable_context cx (BaseTargetV (ImmutableVar _) sbs) = T) ∧
  (assignment_value_static_assignable_context cx (TupleTargetV tgts) =
     EVERY (assignment_value_static_assignable_context cx) tgts)
End

Theorem assignment_value_static_assignable_context_ScopedVar[simp]:
  assignment_value_static_assignable_context cx (BaseTargetV (ScopedVar id) sbs) = T
Proof
  simp[assignment_value_static_assignable_context_def]
QED

Theorem assignment_value_static_assignable_context_ImmutableVar[simp]:
  assignment_value_static_assignable_context cx (BaseTargetV (ImmutableVar id) sbs) = T
Proof
  simp[assignment_value_static_assignable_context_def]
QED

Theorem assignment_value_static_assignable_context_TupleTargetV[simp]:
  assignment_value_static_assignable_context cx (TupleTargetV gvs) =
  EVERY (assignment_value_static_assignable_context cx) gvs
Proof
  simp[assignment_value_static_assignable_context_def] >>
  metis_tac[ETA_AX]
QED

Theorem assignment_value_static_assignable_context_TopLevelVar:
  assignment_value_static_assignable_context cx (BaseTargetV (TopLevelVar src id) sbs) ⇔
    ∃code p. get_module_code cx src = SOME code ∧
             find_var_decl_by_num (string_to_num id) code = SOME p ∧
             (case FST p of
               | StorageVarDecl is_transient typ =>
                   IS_SOME (evaluate_type (get_tenv cx) typ) ∧
                   IS_SOME (lookup_var_slot_from_layout cx is_transient src (SND p))
               | HashMapVarDecl is_transient kt vt =>
                   sbs ≠ [] ∧
                   IS_SOME (lookup_var_slot_from_layout cx is_transient src (SND p)))
Proof
  simp[assignment_value_static_assignable_context_def]
QED

(* Bridge lemma C5.2.3 (mutual form): runtime typed target + env_consistent +
   static context implies the full assign_target_assignable_context.
   Uses recInduct on target_runtime_typed_ind so that the tuple branch
   gets the IH for sub-targets automatically. *)
Theorem target_runtime_typed_static_imp_assignable_context_mutual:
  (!env cx st tgt ty gv.
     target_runtime_typed env cx st tgt ty gv ∧
     env_consistent env cx st ∧
     assignment_value_static_assignable_context cx gv ==>
     assign_target_assignable_context cx gv st) ∧
  (!env cx st tgts tys gvs.
     target_values_runtime_typed env cx st tgts tys gvs ∧
     env_consistent env cx st ∧
     EVERY (assignment_value_static_assignable_context cx) gvs ==>
     EVERY (λgv. assign_target_assignable_context cx gv st) gvs)
Proof
  ho_match_mp_tac target_runtime_typed_ind >> rpt strip_tac
  >- (Cases_on `loc`
      >- metis_tac[target_runtime_typed_ScopedVar_imp_assignable_context]
      >- simp[assign_target_assignable_context_def, assign_target_assignable_def]
      >- (simp[assign_target_assignable_context_def, assign_target_assignable_def] >>
          irule (iffLR (GEN_ALL assignment_value_static_assignable_context_TopLevelVar)) >>
          metis_tac[]))
  >- gvs[target_runtime_typed_def]
  >- gvs[target_runtime_typed_def]
  >- (gvs[target_runtime_typed_def, assign_target_assignable_context_def] >>
      first_x_assum (qspecl_then [`tys`] mp_tac) >> simp[] >> metis_tac[])
  >- simp[]
  >- (fs[target_runtime_typed_def] >> metis_tac[])
  >- gvs[target_runtime_typed_def]
  >- gvs[target_runtime_typed_def]
  >- gvs[target_runtime_typed_def]
  >- gvs[target_runtime_typed_def]
QED

(* Projected single-target form for convenient use *)
Theorem target_runtime_typed_static_imp_assignable_context:
  !env cx st tgt ty gv.
    target_runtime_typed env cx st tgt ty gv ∧
    env_consistent env cx st ∧
    assignment_value_static_assignable_context cx gv ==>
    assign_target_assignable_context cx gv st
Proof
  metis_tac[cj 1 target_runtime_typed_static_imp_assignable_context_mutual]
QED

(* Projected list form for convenient use *)
Theorem target_values_runtime_typed_static_imp_EVERY_assignable_context:
  !env cx st tgts tys gvs.
    target_values_runtime_typed env cx st tgts tys gvs ∧
    env_consistent env cx st ∧
    EVERY (assignment_value_static_assignable_context cx) gvs ==>
    EVERY (λgv. assign_target_assignable_context cx gv st) gvs
Proof
  metis_tac[cj 2 target_runtime_typed_static_imp_assignable_context_mutual]
QED

(* C5.4.3: Static assignable context for evaluated TopLevelVar targets.
   This produces the missing premise for C5.2.3 in INR statement branches. *)

(* Helper: TopLevelVar locations with well-typed base targets are not bare globals.
   Uses type_place_target (any vtype) rather than well_typed_target (Type ty only)
   because SubscriptTarget/AttributeTarget recursion may give HashMapT etc. *)
Theorem base_target_value_shape_TopLevelVar_imp_bare_globals_none:
  !env bt loc sbs vt.
    base_target_value_shape env bt loc sbs ==>
    type_place_target env bt = SOME vt ==>
    !src id. loc = TopLevelVar src id ==>
    FLOOKUP env.bare_globals (src, string_to_num id) = NONE
Proof
  recInduct base_target_value_shape_ind >>
  rw[] >>
  gvs[base_target_value_shape_def]
  >- (* TopLevelNameTarget case *)
     fs[type_place_target_TopLevelNameTarget]
  >- (* AttributeTarget case *)
     metis_tac[type_place_target_AttributeTarget]
  >- (* SubscriptTarget case *)
     metis_tac[type_place_target_SubscriptTarget]
QED

(* Specialized corollary where loc is already TopLevelVar, avoiding
   the nested universal quantifier that makes irule/drule matching hard. *)
Theorem base_target_value_shape_TopLevelVar_imp_bare_globals_none_spec:
  !env bt src id sbs vt.
    base_target_value_shape env bt (TopLevelVar src id) sbs ==>
    type_place_target env bt = SOME vt ==>
    FLOOKUP env.bare_globals (src, string_to_num id) = NONE
Proof
  metis_tac[base_target_value_shape_TopLevelVar_imp_bare_globals_none]
QED

Theorem target_runtime_typed_TopLevelVar_imp_static_context:
  !env cx st bt ty src id sbs.
    target_runtime_typed env cx st (BaseTarget bt) ty (BaseTargetV (TopLevelVar src id) sbs) /\
    env_consistent env cx st ==>
    assignment_value_static_assignable_context cx (BaseTargetV (TopLevelVar src id) sbs)
Proof
  rpt strip_tac >>
  fs[target_runtime_typed_def] >>
  fs[target_value_shape_def, well_typed_atarget_def] >>
  fs[well_typed_target_def] >>
  `FLOOKUP env.bare_globals (src, string_to_num id) = NONE`
    by metis_tac[base_target_value_shape_TopLevelVar_imp_bare_globals_none_spec] >>
  (* Expand location_runtime_typed to expose the FLOOKUP for drule/metis *)
  fs[location_runtime_typed_def] >>
  Cases_on `vt` >> fs[]
  >- (* Type: use env_consistent projection then the TopLevelVar biconditional *)
     (drule_all env_consistent_toplevel_storage_static >> strip_tac >>
      rw[assignment_value_static_assignable_context_TopLevelVar] >>
      qexists_tac `ts` >> qexists_tac `(StorageVarDecl is_transient typ, id_str)` >>
      simp[])
  >- (* HashMapT: similar but sbs <> [] from target_path_type *)
     (drule_all env_consistent_toplevel_hashmap_static >> strip_tac >>
      rw[assignment_value_static_assignable_context_TopLevelVar] >>
      metis_tac[target_path_type_HashMapT_not_nil])
QED

Theorem target_runtime_typed_imp_static_assignable_context_mutual:
  (!env cx st tgt ty gv.
     target_runtime_typed env cx st tgt ty gv /\
     env_consistent env cx st ==>
     assignment_value_static_assignable_context cx gv) /\
  (!env cx st tgts tys gvs.
     target_values_runtime_typed env cx st tgts tys gvs /\
     env_consistent env cx st ==>
     EVERY (assignment_value_static_assignable_context cx) gvs)
Proof
  ho_match_mp_tac target_runtime_typed_ind >> rpt strip_tac
  (* Goal 1: BaseTarget / BaseTargetV *)
  >- (Cases_on `loc` >> simp[]
      >- metis_tac[target_runtime_typed_TopLevelVar_imp_static_context])
  (* Goal 2: BaseTarget / TupleTargetV *)
  >- gvs[target_runtime_typed_def]
  (* Goal 3: TupleTarget / BaseTargetV *)
  >- gvs[target_runtime_typed_def]
  (* Goal 4: TupleTarget / TupleTargetV *)
  >- (fs[target_runtime_typed_def] >>
      simp[assignment_value_static_assignable_context_TupleTargetV] >>
      metis_tac[])
  (* Goal 5: target_values_runtime_typed [] [] [] *)
  >- simp[]
  (* Goal 6: target_values_runtime_typed cons case *)
  >- (fs[target_runtime_typed_def] >> metis_tac[])
  (* Remaining goals: mismatched length cases *)
  >- gvs[target_runtime_typed_def]
  >- gvs[target_runtime_typed_def]
  >- gvs[target_runtime_typed_def]
  >- gvs[target_runtime_typed_def]
QED

Theorem target_runtime_typed_imp_static_assignable_context:
  !env cx st tgt ty gv.
    target_runtime_typed env cx st tgt ty gv ==>
    env_consistent env cx st ==>
    assignment_value_static_assignable_context cx gv
Proof
  metis_tac[cj 1 target_runtime_typed_imp_static_assignable_context_mutual]
QED

Theorem target_values_runtime_typed_imp_EVERY_static_assignable_context:
  !env cx st tgts tys gvs.
    target_values_runtime_typed env cx st tgts tys gvs ==>
    env_consistent env cx st ==>
    EVERY (assignment_value_static_assignable_context cx) gvs
Proof
  metis_tac[cj 2 target_runtime_typed_imp_static_assignable_context_mutual]
QED

(* C5.4.4: Direct bridges from target_runtime_typed + env_consistent to
   assign_target_assignable_context, combining C5.4.3 (static context
   derivation) with C5.2.3 (static+runtime → assignable context). *)

Theorem target_runtime_typed_imp_assignable_context:
  !env cx st tgt ty gv.
    target_runtime_typed env cx st tgt ty gv ==>
    env_consistent env cx st ==>
    assign_target_assignable_context cx gv st
Proof
  metis_tac[target_runtime_typed_imp_static_assignable_context,
            target_runtime_typed_static_imp_assignable_context]
QED

Theorem target_values_runtime_typed_imp_EVERY_assignable_context:
  !env cx st tgts tys gvs.
    target_values_runtime_typed env cx st tgts tys gvs ==>
    env_consistent env cx st ==>
    EVERY (\gv. assign_target_assignable_context cx gv st) gvs
Proof
  metis_tac[target_values_runtime_typed_imp_EVERY_static_assignable_context,
            target_values_runtime_typed_static_imp_EVERY_assignable_context]
QED

(* C2.2: exact assignment-operation bridge lemmas for statement assignment call sites. *)
Theorem stmt_assign_operation_runtime_typed_Update_from_value_runtime_typed_binop:
  !env ty bop rhs_ty v.
    value_runtime_typed env rhs_ty v /\ well_typed_binop ty bop ty rhs_ty ==>
    assign_operation_runtime_typed env ty (Update ty bop v)
Proof
  rw[assign_operation_runtime_typed_def] >> metis_tac[]
QED

Theorem stmt_assign_operation_runtime_typed_Append_from_value_has_type:
  !env elem_ty n elem_tv v.
    evaluate_type env.type_defs elem_ty = SOME elem_tv /\ value_has_type elem_tv v ==>
    assign_operation_runtime_typed env (ArrayT elem_ty (Dynamic n)) (AppendOp v)
Proof
  rw[assign_operation_runtime_typed_def] >> metis_tac[]
QED

Theorem stmt_assign_operation_runtime_typed_Pop_from_dynamic_array:
  !env elem_ty n elem_tv.
    evaluate_type env.type_defs elem_ty = SOME elem_tv ==>
    assign_operation_runtime_typed env (ArrayT elem_ty (Dynamic n)) PopOp
Proof
  rw[assign_operation_runtime_typed_def] >> metis_tac[]
QED

Theorem well_typed_expr_Pop_dynamic_target:
  !env ty tgt.
    well_typed_expr env (Pop ty tgt) ==>
    ?n. type_place_target env tgt = SOME (Type (ArrayT ty (Dynamic n)))
Proof
  simp[Once well_typed_expr_def] >> metis_tac[]
QED

Theorem well_typed_expr_Pop_dynamic_target_assignable:
  !env ty tgt.
    well_typed_expr env (Pop ty tgt) ==>
    ?n. type_place_target env tgt = SOME (Type (ArrayT ty (Dynamic n))) /\
        assignable_type env.type_defs (ArrayT ty (Dynamic n))
Proof
  simp[Once well_typed_expr_def]
QED


Theorem stmt_assign_operation_matches_target_shape_BaseTargetV:
  !loc sbs op. assign_operation_matches_target_shape (BaseTargetV loc sbs) op
Proof
  rw[assign_operation_matches_target_shape_def]
QED

Theorem stmt_assign_operation_matches_target_shape_Update_BaseTargetV:
  !loc sbs ty bop v.
    assign_operation_matches_target_shape (BaseTargetV loc sbs) (Update ty bop v)
Proof
  rw[assign_operation_matches_target_shape_def]
QED

Theorem stmt_assign_operation_matches_target_shape_Append_BaseTargetV:
  !loc sbs v.
    assign_operation_matches_target_shape (BaseTargetV loc sbs) (AppendOp v)
Proof
  rw[assign_operation_matches_target_shape_def]
QED

Theorem stmt_assign_operation_matches_target_shape_Pop_BaseTargetV:
  !loc sbs. assign_operation_matches_target_shape (BaseTargetV loc sbs) PopOp
Proof
  rw[assign_operation_matches_target_shape_def]
QED
Theorem assign_target_TopLevelVar_INL_imp_assignable_context:
  !cx src id sbs op st res st'.
    assign_target cx (BaseTargetV (TopLevelVar src id) sbs) op st = (INL res, st') ==>
    assign_target_assignable_context cx (BaseTargetV (TopLevelVar src id) sbs) st
Proof
  rpt gen_tac >> strip_tac >>
  (* For TopLevelVar, assign_target_assignable is T (wildcard case), so
     assign_target_assignable_context reduces to just the static context existential. *)
  simp[assign_target_assignable_context_def, assign_target_assignable_def] >>
  (* Goal: ∃code p. get_module_code cx src = SOME code ∧
                    find_var_decl_by_num (string_to_num id) code = SOME p ∧
                    (case FST p of StorageVarDecl ... | HashMapVarDecl ...) *)
  drule assign_target_TopLevelVar_success_imp_lookup_global_INL >> strip_tac >>
  drule lookup_global_INL_imp_decl_facts >> strip_tac >>
  (* Now have: get_module_code cx src = SOME code *)
  qexists `code` >>
  (* Now need ∃p. find_var_decl_by_num ... = SOME p ∧ (case FST p of ...)
     Use metis_tac to resolve the universally quantified helper lemma against assumptions *)
  `?p. find_var_decl_by_num (string_to_num id) code = SOME p`
    by metis_tac[assign_target_TopLevelVar_INL_imp_find_decl_SOME] >>
  (* p is now in scope; provide it as the existential witness *)
  qexists `p` >> simp[] >>
  (* Remaining goal: case FST p of StorageVarDecl => IS_SOME ... | HashMapVarDecl => ... *)
  PairCases_on `p` >> gvs[] >>
  Cases_on `p0` >> gvs[]
  >- (
    (* StorageVarDecl: need IS_SOME (evaluate_type) and IS_SOME (lookup_var_slot_from_layout)
       metis_tac handles instantiation of universally quantified antecedents *)
    metis_tac[lookup_global_INL_StorageVarDecl_imp_IS_SOME])
  >- (
    (* HashMapVarDecl: need sbs ≠ [] and IS_SOME (lookup_var_slot_from_layout) *)
    conj_tac
    >- metis_tac[assign_target_TopLevelVar_INL_HashMapVarDecl_imp_sbs_ne] >>
    metis_tac[lookup_global_INL_HashMapVarDecl_imp_IS_SOME])
QED


(* C5.2.5 was removed: the theorems assign_target_INL_imp_assignable_context_stmt_ind
   and assign_target_INL_imp_assignable_context_stmt had zero downstream consumers
   and the TupleTargetV branch was cheated. Deleted to eliminate CHEAT warning. *)


(* ===== Environment threading facts for executable statement typing ===== *)

(* Generic static env-extension facts moved to vyperTypeEnvExtension. *)

