Theory linkedGetterConstantSubstitution
Ancestors
  vyperGetter constSubstMods pair list publicGetterValueTyping
  vyperTypeContractGetter vyperTypeContract vyperTypeSystem vyperAST
  supportedPlaceAssignable alist finite_map

Theorem build_getter_subst_mods:
  !e kt vt n args ret exp.
    build_getter e kt vt n = (args,ret,exp) ==>
    !E. build_getter (subst_consts_expr_mods E e) kt vt n =
      (args,ret,subst_consts_expr_mods E exp)
Proof
  recInduct build_getter_ind >> conj_tac >> rpt gen_tac >> strip_tac >>
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `build_getter _ _ _ _ = _`
    (mp_tac o ONCE_REWRITE_RULE [build_getter_def]) >>
  simp[AllCaseEqs()] >> strip_tac >> gvs[] >>
  rpt (pairarg_tac >> gvs[]) >>
  simp[Once build_getter_def, subst_consts_expr_mods_def] >>
  gvs[subst_consts_expr_mods_def]
QED

Theorem constant_expr_function_entry_typing:
  constant_expr mods e /\
  well_typed_expr (artifact_env art mods src) e ==>
  well_typed_expr (function_entry_env art mods src vis args) e
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `(!env x. constant_expr mods x ==> !id ty wr.
      (well_typed_expr (extend_local env id ty wr) x <=> well_typed_expr env x)) /\
    (!env x. constant_expr mods x ==> !id ty wr.
      type_place_expr (extend_local env id ty wr) x = type_place_expr env x) /\
    (!env:typing_env tgt:base_assignment_target. T) /\
    (!env xs. EVERY (constant_expr mods) xs ==> !id ty wr.
      (well_typed_exprs (extend_local env id ty wr) xs <=> well_typed_exprs env xs)) /\
    (!env:typing_env x:expr option. T) /\
    (!env xs. EVERY (constant_expr mods) (MAP SND xs) ==> !id ty wr.
      (well_typed_named_exprs (extend_local env id ty wr) xs <=>
       well_typed_named_exprs env xs))` by
    (ho_match_mp_tac well_typed_expr_ind >>
     simp[constant_expr_def, well_typed_expr_def, extend_local_def, SF ETA_ss] >>
     rpt strip_tac >> gs[] >>
     Cases_on `x` >> gs[constant_expr_def, subscript_base_type_exact_def, extend_local_def]) >>
  qpat_assum `!env x. constant_expr mods x ==> !id ty wr.
      (well_typed_expr (extend_local env id ty wr) x <=> well_typed_expr env x)`
    (mk_asm "constant_extend_typing") >>
  `!params env. well_typed_expr env e ==>
      well_typed_expr (FOLDL (\en (id,ty). extend_local en id ty (vis = Internal))
        env params) e` by
    (Induct >> simp[] >> qx_gen_tac `param` >> PairCases_on `param` >>
     simp[] >> rpt strip_tac >>
     qpat_assum `!env. well_typed_expr env e ==> _` irule >>
     asm "constant_extend_typing" (qspecl_then [`env`,`e`] mp_tac) >>
     simp[]) >>
  PURE_REWRITE_TAC [function_entry_env_def] >>
  qpat_assum `!params env. well_typed_expr env e ==> _` irule >>
  first_assum ACCEPT_TAC
QED

Theorem constant_public_getter_typing_mods:
  external_getter_tuple src
    (VariableDecl (Public vis) (Constant init) name ty slot) =
    SOME (mut,nr,args,[]:expr list,ret,fbody) /\
  ALOOKUP E (src,name) = SOME r /\ expr_type r = ty /\
  well_typed_expr env r /\ constant_expr mods r /\
  well_formed_type env.type_defs ty /\
  (!id pt. MEM (id,pt) args ==> FLOOKUP env.var_types id = SOME pt) /\
  type_stmts env ret fbody = SOME env' ==>
  type_stmts env ret (subst_consts_stmts_mods E fbody) = SOME env'
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `subscript_base_type_exact env r` by
    (qpat_assum `constant_expr mods r` mp_tac >> Cases_on `r` >>
     simp[NoAsms, subscript_base_type_exact_def, constant_expr_def]) >>
  qpat_x_assum `external_getter_tuple _ _ = _` mp_tac >>
  simp[external_getter_tuple_def, getter_def, AllCaseEqs()] >>
  rpt strip_tac >>
  gvs[subst_consts_stmt_mods_def,
      subst_consts_expr_mods_def, type_stmt_def, AllCaseEqs(),
      expr_type_def, type_widens_to_def] >>
  rpt (pairarg_tac >>
       gvs[subst_consts_stmt_mods_def, type_stmt_def,
           AllCaseEqs()]) >>
  Cases_on `expr_type r` >> gvs[is_ArrayT_def, ArrayT_type_def] >>
  drule build_getter_subst_mods >>
  disch_then (qspec_then `E` mp_tac) >>
  simp[subst_consts_expr_mods_def] >> strip_tac >>
  qpat_x_assum `build_getter (TopLevelName _ _) _ _ _ = _` kall_tac >>
  drule value_build_getter_typing >>
  disch_then (qspec_then `env` mp_tac) >>
  simp[subscript_type_ok_def, expr_type_def, is_int_type_def, type_widens_to_def] >>
  drule supportedPlaceAssignableTheory.well_formed_array_element >>
  simp[type_stmt_def, type_widens_to_def]
QED
