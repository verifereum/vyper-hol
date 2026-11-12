(* Pointer safety of an assignment to a top-level storage or transient
   variable of an ABI-dynamic type: a struct, tuple or static array with a
   nested DynArray or bytestring part.  The lowering stores only the live
   slots (compile_store_slots); stmtSimAssignStorageSparse proves that store
   without the pointer check, and assignBasePtrStorageFragment has the
   ABI-static (dense copy) case. *)
Theory assignBasePtrStorageSparse
Ancestors
  assignBasePtrStorageFragment stmtSimAssignStorageSparse placeStoreSlots
  bodyPtrDefs stmtFragPtr stmtLowering exprLowering context compileEnv
  exprSimHypsDefs exprSimDefs vyperState vyperTyping vyperStorageBackend
  vyperStorageLayoutSafety bodySimStmtCases exprSimSource
Libs monadsyntax

(* The premises are those of compile_assign_storage_copy_stmt_frag_ptr, with
   the type ABI-dynamic.  supported_storage_type excludes bytestrings and the
   DynArray premise excludes a top-level length word, so the value is a
   struct, tuple or static array; acyclic_struct_metadata comes from
   body_inv. *)
Theorem compile_assign_storage_sparse_stmt_frag_ptr:
  body_inv tops bctx cenv cx /\ expr_sim_inv cenv cx env es /\
  expr_body_pre cenv cx env e es /\ supported_expr tops e /\
  type_stmt env ret (Assign (BaseTarget (TopLevelNameTarget nid)) e) = SOME env' /\
  supported_storage_type tops (expr_type e) /\ ~is_word_type (expr_type e) /\
  (!elem n. expr_type e <> ArrayT elem (Dynamic n)) /\
  is_abi_dynamic cenv.ce_struct_fields (expr_type e) /\
  evaluate_type (get_tenv cx) (expr_type e) = SOME tv /\
  well_formed_type_value tv /\
  (storage_vars_rel cenv cx /\ transient_vars_rel cenv cx ==>
   FLOOKUP cenv.ce_module_vars nid =
    SOME (if tr then TransientLoc k else StorageLoc k)) /\
  cenv.ce_hashmap_info nid = NONE /\ cenv.ce_module_var_type nid = SOME (expr_type e) /\
  declared_storage_region cx mid id [] = SOME (tr,k,tv) /\
  w2n k + type_slot_size tv <= dimword (:256) /\
  (!mid' id' subs' k' tv'.
     declared_storage_region cx mid' id' subs' = SOME (tr,k',tv') /\
     (k',tv') <> (k,tv) ==>
     ranges_disjoint (w2n k) (type_slot_size tv) (w2n k') (type_slot_size tv')) /\
  eval_stmt cx (Assign (BaseTarget (TopLevelNameTarget nid)) e) =
    bind (bind (eval_expr cx e) (read_result cx)) (write_storage_slot cx tr k tv) /\
  (!gs v es1. bind (eval_expr cx e) (read_result cx) (es with gas_obs := gs) =
     (INL v,es1) ==> value_has_type tv v) /\
  expr_sim_ptr d ctx PG func cenv cx (expr_type e) e es ==>
  stmt_frag_ptr d ctx PG func cx lctx RetQ cenv
    (stmt_env cenv lctx ret (Assign (BaseTarget (TopLevelNameTarget nid)) e))
    (eval_stmt cx (Assign (BaseTarget (TopLevelNameTarget nid)) e)) es
Proof
  cheat
QED
