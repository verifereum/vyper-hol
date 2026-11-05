(* Boundary facts for the supported storage/transient Append case. *)
Theory bodyAppendStorageFacts
Ancestors
  bodySim supportedExprForms supportedTypes vyperValue vyperTypeSystem
  compileVyper compileEnv vyperAST words supportedDecls vyperInterpreter
  vyperState bodyStorageMetadata exprOpenCases vyperTypeEnv
  exprSimHyps finite_map vyperTypeInvariants

Theorem supported_append_storage_decl:
  supported_storage_dynamic_array tops nid ==>
  ?elem n slot mut.
    supported_variable_decl tops nid =
      SOME (Private, mut, ArrayT elem (Dynamic n), SOME slot) /\
    (mut = Storage \/ mut = Transient) /\ supported_full_word_type elem
Proof
  cheat
QED

Theorem supported_append_element_layout:
  supported_full_word_type elem ==>
  is_word_type elem /\
  ?tv. evaluate_type tenv elem = SOME tv /\ type_slot_size tv = 1
Proof
  cheat
QED

Theorem append_capacity_word_bound:
  supported_full_word_type elem /\
  assignable_type tenv (ArrayT elem (Dynamic n)) ==>
  0 < n /\ n + 1 < dimword(:256)
Proof
  cheat
QED

Theorem supported_append_capacity_lookup:
  !tops src id vis mut elem n slot.
    supported_variable_decl tops (src,id) =
      SOME (vis,mut,ArrayT elem (Dynamic n),slot) ==>
    src = NONE /\
    build_dynarray_capacity (collect_module_vars tops) (NONE,id) = n
Proof
  cheat
QED

Theorem body_append_capacity_lookup:
  body_inv tops ctx cenv cx /\
  supported_variable_decl tops nid =
    SOME (vis,mut,ArrayT elem (Dynamic n),slot) ==>
  cenv.ce_module_dynarray_capacity nid = n
Proof
  cheat
QED

Theorem append_storage_target_eval:
  get_module_code cx src = SOME tops /\
  find_var_decl_by_name id tops = SOME (StorageVarDecl tr ty,key) /\
  lookup_var_slot_from_layout cx tr src key = SOME slot /\
  evaluate_type (get_tenv cx) ty = SOME tv ==>
  eval_target_place cx (TopLevelNameTarget (src,id)) es =
    (INL (StoragePlace tr (n2w slot) tv),es)
Proof
  cheat
QED

Theorem body_append_root_metadata:
  body_inv tops ctx cenv cx /\
  supported_variable_decl tops nid =
    SOME (vis,mut,ArrayT elem (Dynamic n),slot) ==>
  cenv.ce_module_var_type nid = SOME (ArrayT elem (Dynamic n)) /\
  cenv.ce_hashmap_info nid = NONE /\
  cenv.ce_module_dynarray_capacity nid = n
Proof
  cheat
QED

Theorem append_typed_storage_target:
  env_consistent env cx es /\
  get_module_code cx src = SOME tops /\
  find_var_decl_by_name id tops <> NONE /\
  type_place_target env (TopLevelNameTarget (src,id)) = SOME (Type ty) ==>
  ?tr key slot tv.
    find_var_decl_by_name id tops = SOME (StorageVarDecl tr ty,key) /\
    lookup_var_slot_from_layout cx tr src key = SOME slot /\
    evaluate_type (get_tenv cx) ty = SOME tv
Proof
  cheat
QED

Theorem body_append_runtime_metadata:
  body_inv tops ctx cenv cx /\
  supported_storage_dynamic_array tops (src,id) /\
  env_consistent env cx es /\
  type_place_target env (TopLevelNameTarget (src,id)) = SOME (Type ty) ==>
  ?elem n tr key slot tv.
    ty = ArrayT elem (Dynamic n) /\ supported_full_word_type elem /\
    cenv.ce_module_var_type (src,id) = SOME ty /\
    cenv.ce_module_dynarray_capacity (src,id) = n /\
    find_var_decl_by_name id tops = SOME (StorageVarDecl tr ty,key) /\
    lookup_var_slot_from_layout cx tr src key = SOME slot /\
    evaluate_type (get_tenv cx) ty = SOME tv /\
    eval_target_place cx (TopLevelNameTarget (src,id)) es =
      (INL (StoragePlace tr (n2w slot) tv),es)
Proof
  cheat
QED

Theorem append_storage_compiler_location:
  storage_vars_rel cenv cx /\ transient_vars_rel cenv cx /\
  get_module_code cx src = SOME tops /\
  find_var_decl_by_name id tops = SOME (StorageVarDecl tr ty,key) /\
  lookup_var_slot_from_layout cx tr src key = SOME slot ==>
  FLOOKUP cenv.ce_module_vars (src,id) =
    SOME (if tr then TransientLoc (n2w slot) else StorageLoc (n2w slot))
Proof
  cheat
QED

Theorem append_typing_target:
  type_stmt env ret_ty (Append tgt e) = SOME env' ==>
  ?elem n.
    type_place_target env tgt = SOME (Type (ArrayT elem (Dynamic n))) /\
    well_typed_expr env e /\
    type_widens_to env.type_defs (expr_type e) elem /\
    assignable_type env.type_defs elem
Proof
  cheat
QED

Theorem body_append_target_bounds:
  body_inv tops ctx cenv cx /\
  supported_storage_dynamic_array tops (src,id) /\
  expr_sim_inv cenv cx env es /\
  type_stmt env ret_ty (Append (TopLevelNameTarget (src,id)) e) = SOME env' ==>
  ?elem n tr key slot tv.
    supported_full_word_type elem /\ 0 < n /\ n + 1 < dimword(:256) /\
    cenv.ce_module_var_type (src,id) = SOME (ArrayT elem (Dynamic n)) /\
    cenv.ce_module_dynarray_capacity (src,id) = n /\
    find_var_decl_by_name id tops =
      SOME (StorageVarDecl tr (ArrayT elem (Dynamic n)),key) /\
    lookup_var_slot_from_layout cx tr src key = SOME slot /\
    evaluate_type (get_tenv cx) (ArrayT elem (Dynamic n)) = SOME tv /\
    eval_target_place cx (TopLevelNameTarget (src,id)) es =
      (INL (StoragePlace tr (n2w slot) tv),es)
Proof
  cheat
QED

(* A word type takes no wider type (type_widens_to). *)
Theorem type_widens_to_word:
  !tenv t u. type_widens_to tenv t u /\ is_word_type u ==> t = u
Proof
  cheat
QED
