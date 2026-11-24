Theory publicGetterValueTyping
Ancestors
  vyperGetter vyperTypeSystem vyperAST supportedPlaceAssignable finite_map pair list

Theorem value_build_getter_typing:
  !e kt vt n args ret exp env ty.
    build_getter e kt vt n = (args,ret,exp) /\ vt = Type ty /\
    well_typed_expr env e /\ subscript_base_type_exact env e /\
    subscript_type_ok (expr_type e) (Name kt (num_to_dec_string n)) ty /\
    well_formed_type env.type_defs ty /\
    (!id pt. MEM (id,pt) args ==> FLOOKUP env.var_types id = SOME pt) ==>
    well_typed_expr env exp /\ expr_type exp = ret
Proof
  recInduct build_getter_ind >> conj_tac >> rpt gen_tac >> strip_tac >>
  rpt gen_tac >> strip_tac >> gvs[] >>
  qpat_x_assum `build_getter _ _ _ _ = _`
    (mp_tac o ONCE_REWRITE_RULE [build_getter_def]) >>
  simp[AllCaseEqs()] >> strip_tac >> gvs[]
  >- (pairarg_tac >> gvs[] >>
      rename1 `is_ArrayT ty` >> Cases_on `ty` >>
      gvs[is_ArrayT_def, ArrayT_type_def] >>
      first_x_assum (qspec_then `env` mp_tac) >>
      simp[well_typed_expr_def, subscript_base_type_exact_def, expr_type_def,
           subscript_type_ok_def, is_int_type_def] >>
      metis_tac[supportedPlaceAssignableTheory.well_formed_array_element]) >>
  simp[well_typed_expr_def, expr_type_def] >> metis_tac[]
QED
