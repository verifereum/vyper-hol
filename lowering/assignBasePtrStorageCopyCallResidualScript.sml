(* Residual leaf for a storage copy-assignment of an internal call whose
   lowered return type differs from the call site's annotation. *)
Theory assignBasePtrStorageCopyCallResidual
Ancestors assignBasePtrStorageTypes 
  stmtSimAssignStorage bodyPtrDefs stmtFragPtr
  stmtLowering exprLowering context compileEnv loweringPosts finite_map
  exprSimProps stmtSimProps stmtLoweringMono stmtSimForced gasSummaryComposePtr
  gasExemptCert fragGasPathPtr fragGasPath fragGasMode gasSummary exprSimHypsDefs
  exprSimDefs fragExec exprLoweringProps vyperState assignBasePtrStorageDirect
  exprOperandVar venomState vyperTyping vyperStorageBackend
  assignBasePtrStorageExtent assignBasePtrStorageLoop exprSimHyps valueEncodingProps
  list exprOpenTerminals exprOpenPrimitives emitHelperProps venomInst bodySimStmtCases exprSimSource
Libs monadsyntax

(* RESIDUAL: internal-call storage copy source under Decision 18; held for the post_value_type_widens port, cf. exprSimBopRestWordCompose *)
Theorem assign_storage_copy_call_frag_ptr:
  post_value_type cenv e <> expr_type e /\
  body_inv tops bctx cenv cx /\ expr_sim_inv cenv cx env es /\
  expr_body_pre cenv cx env e es /\ supported_expr tops e /\
  type_stmt env ret (Assign (BaseTarget (TopLevelNameTarget nid)) e) = SOME env' /\
  supported_storage_type tops (expr_type e) /\ ~is_word_type (expr_type e) /\
  (!elem n. expr_type e <> ArrayT elem (Dynamic n)) /\
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
