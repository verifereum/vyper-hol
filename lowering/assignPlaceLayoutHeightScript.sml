Theory assignPlaceLayoutHeight
Ancestors
  placeMemoryTypeInterfaces exprSimProps loweringPosts vyperValue compileEnv
  vyperTypeArgFits vyperTypeSystem vyperTypeValues vyperAST list arithmetic

Definition layout_height_def:
  layout_height (BaseTV bt) = 0 /\
  layout_height (FlagTV m) = 0 /\
  layout_height NoneTV = 0 /\
  layout_height (ArrayTV tv bd) = SUC (layout_height tv) /\
  layout_height (TupleTV tvs) = SUC (layout_height_list tvs) /\
  layout_height (StructTV fields) = SUC (layout_height_fields fields) /\
  layout_height_list [] = 0 /\
  layout_height_list (tv::tvs) = MAX (layout_height tv) (layout_height_list tvs) /\
  layout_height_fields [] = 0 /\
  layout_height_fields ((nm,tv)::fields) =
    MAX (layout_height tv) (layout_height_fields fields)
End

Theorem nonbytes_nonword_local_val_path:
  ~is_word_type t /\ ~is_bytestring_type t /\
  evaluate_type (get_tenv cx) t = SOME tv /\
  local_val_at cenv cx n k tv v ==>
  local_path_at cenv cx n k tv
Proof
  Cases_on `t`
  >- (rename1 `BaseT bt` >> Cases_on `bt` >>
      simp[is_word_type_def, is_bytestring_type_def] >>
      rename1 `BytesT bd` >> Cases_on `bd` >>
      simp[evaluate_type_def, is_word_type_def, is_bytestring_type_def] >>
      rpt strip_tac >> gvs[]) >>
  rpt strip_tac >> gvs[evaluate_type_def, local_val_at_def, AllCaseEqs()]
QED

Theorem arg_type_fits_layout_height:
  (!t u. arg_type_fits t u ==> !tenv tv uv.
    evaluate_type tenv t = SOME tv /\ evaluate_type tenv u = SOME uv ==>
    layout_height tv = layout_height uv) /\
  (!ts us. arg_types_fit ts us ==> !tenv tvs uvs.
    LIST_REL (\t tv. evaluate_type tenv t = SOME tv) ts tvs /\
    LIST_REL (\u uv. evaluate_type tenv u = SOME uv) us uvs ==>
    layout_height_list tvs = layout_height_list uvs)
Proof
  ho_match_mp_tac arg_type_fits_ind >> rw[arg_type_fits_def] >>
  imp_res_tac evaluate_type_ArrayT_cases >>
  imp_res_tac evaluate_type_TupleT_cases >>
  gvs[evaluate_type_def, layout_height_def] >> metis_tac[]
QED

Theorem layout_height_list_member:
  !tvs tv. MEM tv tvs ==> layout_height tv <= layout_height_list tvs
Proof
  Induct >> simp[layout_height_def] >> rpt strip_tac >> gvs[] >>
  metis_tac[MAX_LE, MAX_COMM, LESS_EQ_TRANS]
QED

Theorem mem_field_offset_layout_height:
  !fields id k tv. mem_field_offset fields id = SOME (k,tv) ==>
    layout_height tv <= layout_height_fields fields
Proof
  Induct >> simp[mem_field_offset_def] >> gen_tac >> PairCases_on `h` >>
  rpt gen_tac >> simp[mem_field_offset_def, layout_height_def] >>
  Cases_on `h0 = id` >> simp[AllCaseEqs()] >> rpt strip_tac >> gvs[] >>
  PairCases_on `z` >> gvs[] >> metis_tac[]
QED

Theorem mem_step_offset_layout_height:
  mem_step_offset tv sb = SOME (k,uv) ==>
  layout_height uv < layout_height tv
Proof
  strip_tac >> drule mem_step_offset_shape >> strip_tac >>
  gvs[layout_height_def]
  >- (drule mem_field_offset_layout_height >> simp[]) >>
  `layout_height (EL (Num i) tvs) <= layout_height_list tvs` by
    (irule layout_height_list_member >> simp[EL_MEM]) >> decide_tac
QED

Theorem mem_path_offset_layout_height:
  !path tv k uv. mem_path_offset tv path = SOME (k,uv) ==>
    layout_height uv <= layout_height tv /\
    (path <> [] ==> layout_height uv < layout_height tv)
Proof
  Induct >> simp[mem_path_offset_def] >> rpt strip_tac >>
  gvs[AllCaseEqs()] >>
  PairCases_on `z` >> gvs[] >>
  drule mem_step_offset_layout_height >>
  first_x_assum drule >> simp[]
QED
