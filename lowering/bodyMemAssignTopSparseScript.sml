(* Memory twin of S1's sparse storage store (stmtSimAssignStorageSparse):
   assigning an ABI-dynamic aggregate to a storage or transient variable
   stores only its live slots (compile_store_slots). *)
Theory bodyMemAssignTopSparse
Ancestors
  bodyMemAssignTopCopyOutcome stmtSimAssignStorageSparse placeStoreSlots
  bodyMemoryDefs bodyMemoryPreds exprSimMemDefs exprSimDefs
  stmtSimDefs stmtLowering exprLowering compileEnv context
  vyperStorageLayoutSafety vyperStorage vyperValue vyperTyping
  loweringPosts bodySim vyperState
Libs
  monadsyntax

Theorem compile_assign_storage_sparse_stmt_frag_mem:
  !d ctx func cx lctx RetQ cenv ty src id e es ts tr typ id_str slot tvt.
    get_module_code cx src = SOME ts /\
    find_var_decl_by_name id ts = SOME (StorageVarDecl tr typ, id_str) /\
    lookup_var_slot_from_layout cx tr src id_str = SOME slot /\
    expr_type e = typ /\ lowered_value_type cenv e = expr_type e /\
    ~is_word_type typ /\ ~is_bytestring_type typ /\ ~has_length_word typ /\
    (!elem n. typ <> ArrayT elem (Dynamic n)) /\
    sfields_tenv_consistent cenv.ce_struct_fields (get_tenv cx) /\
    acyclic_struct_metadata cenv.ce_struct_fields /\
    is_abi_dynamic cenv.ce_struct_fields typ /\
    evaluate_type (get_tenv cx) typ = SOME tvt /\
    0 < type_slot_size tvt /\
    type_memory_bytes cenv typ = type_memory_size tvt /\
    cenv.ce_hashmap_info (src, id) = NONE /\
    cenv.ce_module_var_type (src, id) = SOME typ /\
    slot + type_slot_size tvt <= dimword (:256) /\
    (!mid' n' subs' k' tv'.
       declared_storage_region cx mid' n' subs' = SOME (tr, k', tv') /\
       (k', tv') <> (n2w slot, tvt) ==>
       ranges_disjoint slot (type_slot_size tvt) (w2n k') (type_slot_size tv')) /\
    (!gs v es1.
       (do result <- eval_expr cx e; read_result cx result od)
         (es with gas_obs := gs) = (INL v, es1) ==> value_has_type tvt v) /\
    expr_sim_mem ctx func cenv cx (expr_type e) e es ==>
    stmt_frag_mem d ctx func cx lctx RetQ cenv
      (stmt_env cenv lctx ty
         (Assign (BaseTarget (TopLevelNameTarget (src, id))) e))
      (eval_stmt cx (Assign (BaseTarget (TopLevelNameTarget (src, id))) e)) es
Proof
  cheat
QED
