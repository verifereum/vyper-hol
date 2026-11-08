(* Direct-store boundary probes. Zero-capacity supported aggregates must not
   silently be strengthened to positive-capacity inputs by the continuation. *)
Theory assignBasePtrStorageDirect
Ancestors assignBasePtrStorageExtent supportedTypes vyperValue vyperAST
  compileEnv exprLowering vyperTypeSystem vyperTypeInvariants valueEncodingProps
  exprSimHypsDefs

Theorem assign_base_empty_struct_storage_shape:
  supported_storage_type [StructDecl "Empty" []] (StructT (NONE,"Empty")) /\
  ~is_word_type (StructT (NONE,"Empty")) /\
  (!elem n. StructT (NONE,"Empty") <> ArrayT elem (Dynamic n)) /\
  type_memory_size (StructTV []) = 0
Proof
  EVAL_TAC >> simp[]
QED

(* Actual assignment typing, unlike the syntactic whitelist, excludes zero
   storage-slot types. This is a body-premise consequence, not a new guard. *)
Theorem assign_base_typed_assignment_memory_positive:
  !cenv cx env es ret target e env' tv.
    expr_sim_inv cenv cx env es /\
    type_stmt env ret (Assign target e) = SOME env' /\
    evaluate_type (get_tenv cx) (expr_type e) = SOME tv ==>
    0 < type_memory_size tv
Proof
  rpt strip_tac >>
  `env.type_defs = get_tenv cx` by
    fs[expr_sim_inv_def, env_consistent_def, env_context_consistent_def] >>
  `assignable_type (get_tenv cx) (expr_type e)` by
    gvs[type_stmt_def, AllCaseEqs()] >>
  drule_all assignable_type_slot_size_pos >>
  metis_tac[type_memory_size_pos]
QED

Theorem assign_base_typed_assignment_capacity_positive:
  !cenv cx env es ret target e env' tv.
    expr_body_pre cenv cx env e es /\
    type_stmt env ret (Assign target e) = SOME env' /\
    evaluate_type (get_tenv cx) (expr_type e) = SOME tv /\
    ~is_word_type (expr_type e) ==>
    0 < type_memory_bytes cenv (expr_type e)
Proof
  rpt strip_tac >>
  `expr_sim_inv cenv cx env es` by fs[expr_body_pre_def] >>
  drule_all assign_base_typed_assignment_memory_positive >> strip_tac >>
  drule_all exprSimHypsTheory.expr_body_pre_copy_ok >> simp[]
QED
