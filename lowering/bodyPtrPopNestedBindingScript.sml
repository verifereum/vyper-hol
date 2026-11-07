Theory bodyPtrPopNestedBinding
Ancestors bodyPtrPopNestedLocation bodyPtrPopNestedRuntimeTyping
  compileEnv exprLowering exprLoweringProps vyperAST vyperState

(* Unlike the StorageVarDecl-specific public location facts, this boundary
   also handles hashmap declarations. The general targetPlaceSim fact is local. *)
Theorem pop_declared_root_binding:
  state_rel fn cenv cx es s /\
  get_module_code cx src = SOME ts /\
  find_var_decl_by_name name ts = SOME (d,id) /\
  lookup_var_slot_from_layout cx (var_decl_transient d) src id = SOME slot
  ==>
  FLOOKUP cenv.ce_module_vars (src,name) =
    SOME (if var_decl_transient d then TransientLoc (n2w slot)
          else StorageLoc (n2w slot))
Proof
  strip_tac >> Cases_on `var_decl_transient d` >>
  gvs[state_rel_def, storage_vars_rel_def, transient_vars_rel_def] >>
  metis_tac[]
QED

Theorem pop_declared_root_location:
  state_rel fn cenv cx es s /\
  get_module_code cx src = SOME ts /\
  find_var_decl_by_name name ts = SOME (d,id) /\
  lookup_var_slot_from_layout cx (var_decl_transient d) src id = SOME slot /\
  compile_get_target_ptr f cenv (TopLevelNameTarget (src,name)) sa =
    ((hdr,lo,pt),sb)
  ==> lo = SOME (if var_decl_transient d then LocTransient else LocStorage)
Proof
  strip_tac >> drule_all pop_declared_root_binding >> strip_tac >>
  qpat_x_assum `compile_get_target_ptr _ _ _ _ = _` mp_tac >>
  Cases_on `var_decl_transient d` >>
  simp[compile_get_target_ptr_def, comp_return_def]
QED

Theorem pop_nested_declared_slot_exclusion:
  body_inv tops ctx cenv cx /\ ~cx.in_deploy /\
  stmt_state_rel ctx fn cenv cx es s /\
  (~(?id. bt = NameTarget id)) /\
  (~(?nid. bt = TopLevelNameTarget nid)) /\
  compile_get_target_ptr compile_expr cenv bt sa = ((hdr,lo,pt),sm) /\
  compile_expr cenv ty (Pop ann bt) sa = (vv,sb) /\
  fn_has_code sa sb fn /\
  target_root bt = TopLevelNameTarget (src,name) /\
  get_module_code cx src = SOME ts /\
  find_var_decl_by_name name ts = SOME (d,id) /\
  lookup_var_slot_from_layout cx (var_decl_transient d) src id = SOME slot
  ==> F
Proof
  strip_tac >>
  Cases_on `compile_get_target_ptr compile_expr cenv (target_root bt) sa` >>
  PairCases_on `q` >>
  `state_rel fn cenv cx es s` by metis_tac[stmt_state_rel_def] >>
  drule_all pop_nested_root_nonstorage >> strip_tac >>
  qpat_x_assum `compile_get_target_ptr _ _ (target_root _) _ = _` mp_tac >>
  asm_rewrite_tac[] >> strip_tac >>
  drule_all pop_declared_root_location >>
  Cases_on `var_decl_transient d` >> simp[]
QED
