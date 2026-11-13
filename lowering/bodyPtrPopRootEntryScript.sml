Theory bodyPtrPopRootEntry
Ancestors
  bodyPtrPreds exprSimPopStorage exprSimTopLevelProps exprSimSource
  exprSimDefs exprSimHyps exprSimHypsDefs exprLoweringProps compileEnv
  context vyperInterpreter vyperTypeEnv vyperTypeInvariants vyperTyping
  vyperTypeSystem vyperTypeCallGraph

Theorem pop_root_body_pre:
  expr_body_pre cenv cx env (Pop ann (TopLevelNameTarget nid)) es ==>
  expr_sim_pre cenv cx env (Pop ann (TopLevelNameTarget nid)) es
Proof
  simp[expr_sim_pre_body, int_calls_expr_def]
QED

(* Declaration existence is separate from storage normalization: typing
   excludes the absent-module/absent-declaration cases first. *)
Theorem pop_root_has_decl:
  expr_sim_pre cenv cx env (Pop ann (TopLevelNameTarget (src,id))) es ==>
  ?ts d. get_module_code cx src = SOME ts /\
         find_var_decl_by_name id ts = SOME d
Proof
  strip_tac >> spose_not_then assume_tac >>
  `!ts. get_module_code cx src = SOME ts ==>
        find_var_decl_by_name id ts = NONE` by
    (rpt strip_tac >> Cases_on `find_var_decl_by_name id ts` >> metis_tac[]) >>
  fs[expr_sim_pre_def, expr_sim_inv_def, env_consistent_def,
     env_context_consistent_def, Once well_typed_expr_def,
     type_place_target_TopLevelNameTarget] >>
  Cases_on `FLOOKUP env.bare_global_assignable (src,id)` >> gvs[] >>
  qpat_x_assum
    `!src id ty. FLOOKUP env.toplevel_vtypes (src,id) = SOME (Type ty) /\
                 FLOOKUP env.bare_globals (src,id) = NONE ==> _`
    (qspecl_then [`src`, `id`, `ArrayT ann (Dynamic n)`] mp_tac) >>
  simp[] >> rpt strip_tac >>
  qpat_x_assum `!ts. get_module_code cx src = SOME ts ==> _`
    (qspec_then `ts` mp_tac) >> simp[]
QED

Theorem pop_root_storage_entry:
  expr_sim_pre cenv cx env (Pop ann (TopLevelNameTarget (src,id))) es /\
  storage_vars_rel cenv cx /\ transient_vars_rel cenv cx ==>
  ?ts n tr name slot tv.
    get_module_code cx src = SOME ts /\
    find_var_decl_by_name id ts =
      SOME (StorageVarDecl tr (ArrayT ann (Dynamic n)),name) /\
    lookup_var_slot_from_layout cx tr src name = SOME slot /\
    evaluate_type (get_tenv cx) ann = SOME tv /\
    evaluate_type (get_tenv cx) (ArrayT ann (Dynamic n)) =
      SOME (ArrayTV tv (Dynamic n)) /\
    FLOOKUP cenv.ce_module_vars (src,id) =
      SOME (if tr then TransientLoc (n2w slot) else StorageLoc (n2w slot)) /\
    cenv.ce_hashmap_info (src,id) = NONE /\
    cenv.ce_module_var_type (src,id) = SOME (ArrayT ann (Dynamic n)) /\
    elem_size_in_location cenv (if tr then LocTransient else LocStorage) ann =
      type_slot_size tv
Proof
  strip_tac >> drule pop_root_has_decl >> strip_tac >>
  `expr_sim_inv cenv cx env es` by fs[expr_sim_pre_def] >>
  `well_typed_expr env (Pop ann (TopLevelNameTarget (src,id))) /\
   env_consistent env cx es` by
    fs[expr_sim_pre_def, expr_sim_inv_def] >>
  drule_all pop_storage_target_facts >> strip_tac >> gvs[] >>
  drule_all toplevel_storage_ce_vars >> strip_tac >>
  drule_all pop_storage_compiler_facts >> strip_tac >>
  `!tr. elem_size_in_location cenv
      (if tr then LocTransient else LocStorage) ann = type_slot_size tv` by
    (gen_tac >> irule pop_storage_element_size >>
     goal_assum (drule_at Any) >> simp[] >>
     goal_assum (drule_at Any)) >>
  goal_assum (drule_at Any) >> simp[] >>
  goal_assum (drule_at Any) >> simp[]
QED

(* Consumer-facing compiler equation: the storage layout facts remain in
   pop_root_storage_entry, while the existing slice theorem handles both
   zero and positive runtime headers without an entry nonemptiness premise. *)
Theorem pop_root_compile:
  expr_sim_inv cenv cx env es /\
  FLOOKUP cenv.ce_module_vars (src,id) =
    SOME (if tr then TransientLoc slot else StorageLoc slot) /\
  cenv.ce_hashmap_info (src,id) = NONE /\
  cenv.ce_module_var_type (src,id) = SOME (ArrayT ann bd) /\
  evaluate_type (get_tenv cx) ann = SOME tv /\
  compile_dynarray_pop (Lit slot) 1 (type_slot_size tv)
    cenv.ce_is_ctor cenv.ce_imm_alloca
    (if tr then LocTransient else LocStorage) sa = (op,sb) ==>
  compile_expr cenv ty (Pop ann (TopLevelNameTarget (src,id))) sa =
    (LocatedValue ann (mk_ptr op (if tr then LocTransient else LocStorage)),sb)
Proof
  strip_tac >>
  `elem_size_in_location cenv (if tr then LocTransient else LocStorage) ann =
   type_slot_size tv` by
    (irule pop_storage_element_size >>
     goal_assum (drule_at Any) >> simp[] >>
     goal_assum (drule_at Any)) >>
  drule_all compile_expr_pop_storage >> simp[]
QED
