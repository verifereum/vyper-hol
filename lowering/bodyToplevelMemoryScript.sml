(* Code-free storage/transient value views; forcing is not certified here. *)
Theory bodyToplevelMemory
Ancestors
  loweringPosts
  bodyMemoryDefs exprSimLeaves exprSimHyps exprSimDefs exprLowering
  compileEnv fragExecMem venomState loweringSlice valueEncoding
  exprLoweringProps accountsRelProps
  vyperAST vyperInterpreter vyperState vyperTypeSystem vyperTyping
  vyperValueOperation vyperStorageLayoutSafety vyperLookupStorage
  vyperTypeGlobalLookupSoundness vyperTypeInvariants vyperTypeEnv list

Theorem compile_toplevel_storage_vv_sim_mem:
  !ctx func cenv cx env ty ann src id es ts tr typ id_str slot tvt v.
    expr_sim_pre cenv cx env (TopLevelName ann (src, id)) es /\
    get_module_code cx src = SOME ts /\
    find_var_decl_by_name id ts = SOME (StorageVarDecl tr typ, id_str) /\
    lookup_var_slot_from_layout cx tr src id_str = SOME slot /\
    evaluate_type (get_tenv cx) typ = SOME tvt /\
    read_storage_slot cx tr (n2w slot) tvt es = (INL v, es) ==>
    expr_vv_sim_mem ctx func cenv cx ty (TopLevelName ann (src, id)) es
Proof
  cheat
QED

Theorem compile_toplevel_storage_undecodable_sim_mem:
  !ctx func cenv cx env ty ann src id es ts tr typ id_str.
    expr_sim_pre cenv cx env (TopLevelName ann (src, id)) es /\
    get_module_code cx src = SOME ts /\
    find_var_decl_by_name id ts = SOME (StorageVarDecl tr typ, id_str) /\
    ~(?slot tvt v. lookup_var_slot_from_layout cx tr src id_str = SOME slot /\
                   evaluate_type (get_tenv cx) typ = SOME tvt /\
                   read_storage_slot cx tr (n2w slot) tvt es = (INL v, es)) ==>
    expr_vv_sim_mem ctx func cenv cx ty (TopLevelName ann (src, id)) es
Proof
  cheat
QED

Theorem compile_toplevel_immutable_sim_mem:
  !ctx func cenv cx env ty ann src id es ts.
    expr_sim_pre cenv cx env (TopLevelName ann (src, id)) es /\
    get_module_code cx src = SOME ts /\ find_var_decl_by_name id ts = NONE ==>
    expr_vv_sim_mem ctx func cenv cx ty (TopLevelName ann (src, id)) es
Proof
  cheat
QED

Theorem compile_toplevel_no_module_sim_mem:
  !ctx func cenv cx ty ann src id es.
    get_module_code cx src = NONE ==>
    expr_vv_sim_mem ctx func cenv cx ty (TopLevelName ann (src, id)) es
Proof
  cheat
QED

Theorem compile_toplevel_name_vv_sim_mem:
  !ctx func cenv cx env ty ann nsid es.
    expr_sim_pre cenv cx env (TopLevelName ann nsid) es ==>
    expr_vv_sim_mem ctx func cenv cx ty (TopLevelName ann nsid) es
Proof
  cheat
QED

