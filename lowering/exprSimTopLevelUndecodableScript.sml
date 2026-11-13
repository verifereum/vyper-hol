(* Counted top-level name simulation: undecodable. *)
Theory exprSimTopLevelUndecodable
Ancestors
  exprSimTopLevelProps exprSimMemorySource
  exprSimProps exprSimHypsDefs exprSimDefs loweringPosts
  gasOutcome gasSummary gasSummaryCompose gasContext fragGasPath fragGasMode
  list finite_map exprLowering exprLoweringProps compileEnv context
  vyperAST vyperInterpreter vyperState vyperTypeSystem vyperTypeEnv
  vyperTypeInvariants vyperTypeGlobalLookupSoundness vyperTyping
  vyperValueOperation valueEncoding fragExec venomState
  vyperStorageLayoutSafety vyperLookupStorage

val lookup_global_tac =
  simp[Once evaluate_def, lookup_global_def, bind_def, lift_option_type_def,
       return_def, raise_def, LET_THM];


Theorem compile_toplevel_storage_undecodable_sim:
  !ctx func cenv cx env ty ann src id es ts tr typ id_str.
    expr_sim_pre cenv cx env (TopLevelName ann (src, id)) es /\
    get_module_code cx src = SOME ts /\
    find_var_decl_by_name id ts = SOME (StorageVarDecl tr typ, id_str) /\
    ~(?slot tvt v. lookup_var_slot_from_layout cx tr src id_str = SOME slot /\
                   evaluate_type (get_tenv cx) typ = SOME tvt /\
                   read_storage_slot cx tr (n2w slot) tvt es = (INL v, es)) ==>
    expr_vv_sim ctx func cenv cx ty (TopLevelName ann (src, id)) es
Proof
  rpt strip_tac >> simp[expr_vv_sim_def] >> rpt gen_tac >> strip_tac >>
  `F` suffices_by simp[] >>
  drule_all admissible_toplevel_storage_lookup >> strip_tac >>
  `contract_storage_well_formed cx es` by
    gvs[expr_sim_pre_def, expr_sim_inv_def] >>
  drule_all toplevel_storage_read_decodes >> metis_tac[]
QED

