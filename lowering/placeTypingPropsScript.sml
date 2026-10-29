Theory placeTypingProps
Ancestors
  exprLowering compileVyper vyperTypeSystem

(* Agreement projects only map declarations. Annotation typing, struct layout
   and compiled-value locations remain separate obligations. *)
Definition place_map_tables_agree_def:
  place_map_tables_agree cenv env <=>
    !nsid. OPTION_MAP (\(tr,kt,vt). (kt,vt))
             (cenv.ce_hashmap_info (module_var_key nsid)) =
      (case FLOOKUP env.toplevel_vtypes nsid of
         SOME (HashMapT kt vt) => SOME (kt,vt)
       | _ => NONE)
End

Theorem place_map_tables_agree_cong:
  cenv'.ce_hashmap_info = cenv.ce_hashmap_info /\
  env'.toplevel_vtypes = env.toplevel_vtypes ==>
  (place_map_tables_agree cenv' env' <=> place_map_tables_agree cenv env)
Proof
  simp[place_map_tables_agree_def]
QED

Theorem type_place_expr_annotation:
  !e env ty. type_place_expr env e = SOME (Type ty) ==>
    expr_type e = ty
Proof
  Induct >> simp[Once well_typed_expr_def, vyperASTTheory.expr_type_def] >>
  rpt strip_tac >> gvs[AllCaseEqs(), vtype_annotation_ok_def] >>
  PairCases_on `p` >>
  gvs[Once well_typed_expr_def, AllCaseEqs(), vtype_annotation_ok_def]
QED

Theorem place_type_checked_place:
  !e cenv env vt.
    place_map_tables_agree cenv env /\
    type_place_expr env e = SOME vt ==>
    place_type cenv e = value_type_place vt
Proof
  Induct >> simp[Once well_typed_expr_def, place_type_def] >>
  rpt strip_tac >> gvs[AllCaseEqs(), vtype_annotation_ok_def]
  >- (PairCases_on `p` >>
      gvs[Once well_typed_expr_def, AllCaseEqs()] >>
      qpat_x_assum `place_map_tables_agree _ _` mp_tac >>
      simp[place_map_tables_agree_def] >>
      disch_then (qspec_then `(p0,p1)` mp_tac) >>
      Cases_on `vt` >>
      gvs[vtype_annotation_ok_def, value_type_place_def] >>
      Cases_on `cenv.ce_hashmap_info (module_var_key (p0,p1))` >>
      gvs[] >> PairCases_on `x` >> gvs[])
  >> `place_type cenv e = value_type_place vt'` by metis_tac[]
  >> Cases_on `vt'`
  >> gvs[value_type_place_def, subscript_vtype_def, AllCaseEqs()]
  >> Cases_on `t'`
  >> gvs[subscript_vtype_def, AllCaseEqs(),
         vtype_annotation_ok_def, value_type_place_def]
QED

Theorem place_map_tables_agree_local_updates[simp]:
  place_map_tables_agree
    (cenv with <| ce_vars := vars; ce_var_type := tys |>)
    (extend_local env id ty assignable) <=>
  place_map_tables_agree cenv env
Proof
  irule place_map_tables_agree_cong >> simp[extend_local_def]
QED

(* Construction need agree only at defined checker entries. This includes
   ordinary values, so a spurious compiler map cannot change their dispatch. *)
Definition place_map_tables_agree_on_defined_def:
  place_map_tables_agree_on_defined cenv env <=>
    !nsid vt. FLOOKUP env.toplevel_vtypes nsid = SOME vt ==>
      OPTION_MAP (\(tr,kt,vt). (kt,vt))
        (cenv.ce_hashmap_info (module_var_key nsid)) =
      (case vt of HashMapT kt v => SOME (kt,v) | _ => NONE)
End

Theorem place_map_tables_agree_on_defined_cong:
  cenv'.ce_hashmap_info = cenv.ce_hashmap_info /\
  env'.toplevel_vtypes = env.toplevel_vtypes ==>
  (place_map_tables_agree_on_defined cenv' env' <=>
   place_map_tables_agree_on_defined cenv env)
Proof
  simp[place_map_tables_agree_on_defined_def]
QED

Theorem place_map_tables_agree_implies_on_defined:
  place_map_tables_agree cenv env ==>
  place_map_tables_agree_on_defined cenv env
Proof
  rw[place_map_tables_agree_def, place_map_tables_agree_on_defined_def] >>
  first_x_assum (qspec_then `nsid` mp_tac) >> simp[]
QED

Theorem place_map_tables_agree_on_defined_local_updates[simp]:
  place_map_tables_agree_on_defined
    (cenv with <| ce_vars := vars; ce_var_type := tys |>)
    (extend_local env id ty assignable) <=>
  place_map_tables_agree_on_defined cenv env
Proof
  irule place_map_tables_agree_on_defined_cong >> simp[extend_local_def]
QED

Theorem place_type_checked_place_on_defined:
  !e cenv env vt.
    place_map_tables_agree_on_defined cenv env /\
    type_place_expr env e = SOME vt ==>
    place_type cenv e = value_type_place vt
Proof
  Induct >> simp[Once well_typed_expr_def, place_type_def] >>
  rpt strip_tac >> gvs[AllCaseEqs(), vtype_annotation_ok_def]
  >- (PairCases_on `p` >>
      gvs[Once well_typed_expr_def, AllCaseEqs()] >>
      qpat_x_assum `place_map_tables_agree_on_defined _ _` mp_tac >>
      simp[place_map_tables_agree_on_defined_def] >>
      disch_then (qspec_then `(p0,p1)` mp_tac) >>
      disch_then (qspec_then `vt` mp_tac) >>
      Cases_on `vt` >>
      gvs[vtype_annotation_ok_def, value_type_place_def] >>
      Cases_on `cenv.ce_hashmap_info (module_var_key (p0,p1))` >>
      gvs[] >> PairCases_on `x` >> gvs[])
  >> `place_type cenv e = value_type_place vt'` by metis_tac[]
  >> Cases_on `vt'`
  >> gvs[value_type_place_def, subscript_vtype_def, AllCaseEqs()]
  >> Cases_on `t'`
  >> gvs[subscript_vtype_def, AllCaseEqs(),
         vtype_annotation_ok_def, value_type_place_def]
QED

Theorem place_type_defined_module_map:
  place_map_tables_agree_on_defined cenv env /\
  FLOOKUP env.toplevel_vtypes nsid = SOME (HashMapT kt vt) ==>
  place_type cenv (TopLevelName ty nsid) = MapPT kt vt
Proof
  rw[place_map_tables_agree_on_defined_def] >>
  first_x_assum (qspec_then `nsid` mp_tac) >> simp[] >>
  Cases_on `cenv.ce_hashmap_info (module_var_key nsid)` >> simp[] >>
  PairCases_on `x` >> simp[] >> rpt strip_tac >>
  simp[place_type_def]
QED

Theorem place_type_defined_module_value:
  place_map_tables_agree_on_defined cenv env /\
  FLOOKUP env.toplevel_vtypes nsid = SOME (Type ty) ==>
  place_type cenv (TopLevelName ty nsid) = ValPT ty
Proof
  rw[place_map_tables_agree_on_defined_def] >>
  first_x_assum (qspec_then `nsid` mp_tac) >> simp[] >>
  Cases_on `cenv.ce_hashmap_info (module_var_key nsid)` >> simp[] >>
  simp[place_type_def]
QED

(* Fail the build rather than silently export an admitted bridge. *)
val _ = List.app (fn (name,th) =>
  if List.all (fn tag => tag = "DISK_THM")
       (fst (Tag.dest_tag (Thm.tag th))) then ()
  else raise Fail ("oracle in place typing bridge: " ^ name))
  (DB.thms "placeTypingProps");
