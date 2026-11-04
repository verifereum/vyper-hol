(* Counted top-level name simulation: missing. *)
Theory exprSimTopLevelMissing
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

Theorem compile_toplevel_no_module_sim:
  !ctx func cenv cx ty ann src id es.
    get_module_code cx src = NONE ==>
    expr_vv_sim ctx func cenv cx ty (TopLevelName ann (src, id)) es
Proof
  rw[expr_vv_sim_def] >>
  qpat_x_assum `eval_expr _ _ _ = _` mp_tac >> lookup_global_tac >>
  strip_tac >> gvs[expr_vv_res_ok_def, expr_res_ok_def]
QED
