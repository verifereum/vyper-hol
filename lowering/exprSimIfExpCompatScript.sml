Theory exprSimIfExpCompat
Ancestors
  loweringPosts
  list rich_list finite_map marker exprSimHyps exprSimHypsDefs exprSimSource
  exprSafeOperand
  exprLowering compileEnv loweringStateRelDefs context vyperAST vyperValue
Libs
  pairLib

Theorem ifexp_sfields_partial[local]:
  sfields_tenv_consistent sf env ==>
  !nsid args fields.
    FLOOKUP env nsid = SOME (StructArgs args) /\
    FLOOKUP sf (nsid_to_string nsid) = SOME fields ==>
    MAP (\(name,ty,sz). (name,ty)) fields = args
Proof
  simp[sfields_tenv_consistent_def] >> strip_tac >> rpt gen_tac >> strip_tac >>
  qpat_x_assum `!nsid args. FLOOKUP env nsid = SOME (StructArgs args) ==> _` drule >>
  strip_tac >> gvs[] >>
  qpat_x_assum `MAP FST fields = _` mp_tac >>
  qpat_x_assum `MAP (FST o SND) fields = _` mp_tac >>
  rpt (pop_assum kall_tac) >>
  qid_spec_tac `args` >> Induct_on `fields` >> Cases_on `args` >>
  simp[pairTheory.FORALL_PROD] >> rpt strip_tac >> gvs[] >> metis_tac[]
QED

Theorem ifexp_sfields_partial_delete[local]:
  (!nsid args fields.
    FLOOKUP env nsid = SOME (StructArgs args) /\
    FLOOKUP sf (nsid_to_string nsid) = SOME fields ==>
    MAP (\(name,ty,sz). (name,ty)) fields = args) ==>
  !key nsid args fields.
    FLOOKUP (env \\ key) nsid = SOME (StructArgs args) /\
    FLOOKUP (sf \\ nsid_to_string key) (nsid_to_string nsid) = SOME fields ==>
    MAP (\(name,ty,sz). (name,ty)) fields = args
Proof
  simp[DOMSUB_FLOOKUP_THM, AllCaseEqs()] >> metis_tac[]
QED

Theorem ifexp_sfields_partial_types[local]:
  (!nsid args fields.
    FLOOKUP env nsid = SOME (StructArgs args) /\
    FLOOKUP sf (nsid_to_string nsid) = SOME fields ==>
    MAP (\(name,ty,sz). (name,ty)) fields = args) /\
  FLOOKUP env nsid = SOME (StructArgs args) /\
  FLOOKUP sf (nsid_to_string nsid) = SOME fields ==>
  MAP (FST o SND) fields = MAP SND args
Proof
  strip_tac >> first_x_assum drule_all >> disch_then (SUBST1_TAC o SYM) >>
  simp[MAP_MAP_o, combinTheory.o_DEF, pairTheory.LAMBDA_PROD]
QED

Theorem ifexp_abi_missing_struct[local]:
  FLOOKUP sf (nsid_to_string nsid) = NONE ==>
  ~is_abi_dynamic sf (StructT nsid) /\
  abi_size_bound sf (StructT nsid) = 0 /\
  abi_static_size sf (StructT nsid) = 0
Proof
  simp[Once is_abi_dynamic_def, Once abi_size_bound_def,
       Once abi_static_size_def]
QED

Theorem ifexp_abi_members_dynamic[local]:
  !tys. EVERY (\ty. is_abi_dynamic sf ty ==> vyper_is_dynamic env ty) tys ==>
  EXISTS (is_abi_dynamic sf) tys ==> vyper_any_dynamic env tys
Proof
  Induct >> simp[vyperABITheory.vyper_is_dynamic_def] >> metis_tac[]
QED

Theorem ifexp_abi_members_bound[local]:
  !tys. EVERY (\ty.
    (is_abi_dynamic sf ty ==> vyper_is_dynamic env ty) /\
    abi_size_bound sf ty <= vyper_abi_size_bound env ty /\
    (~is_abi_dynamic sf ty ==>
       abi_static_size sf ty <= vyper_abi_size_bound env ty)) tys ==>
  SUM (MAP (\t. (if is_abi_dynamic sf t then 32 else abi_static_size sf t) +
                 (if is_abi_dynamic sf t then abi_size_bound sf t else 0)) tys)
    <= vyper_abi_size_bound_list env tys
Proof
  Induct >> simp[vyperABITheory.vyper_abi_size_bound_def] >> rpt strip_tac >>
  first_x_assum drule >> strip_tac >>
  Cases_on `is_abi_dynamic sf h` >> Cases_on `vyper_is_dynamic env h` >>
  gvs[] >> decide_tac
QED

Theorem ifexp_abi_static_members_bound[local]:
  !tys. EVERY (\ty.
    (is_abi_dynamic sf ty ==> vyper_is_dynamic env ty) /\
    abi_size_bound sf ty <= vyper_abi_size_bound env ty /\
    (~is_abi_dynamic sf ty ==>
       abi_static_size sf ty <= vyper_abi_size_bound env ty)) tys /\
  ~EXISTS (is_abi_dynamic sf) tys ==>
  SUM (MAP (abi_static_size sf) tys) <= vyper_abi_size_bound_list env tys
Proof
  Induct >> simp[vyperABITheory.vyper_abi_size_bound_def] >> rpt strip_tac >>
  first_x_assum drule_all >> strip_tac >>
  Cases_on `vyper_is_dynamic env h` >> gvs[] >> decide_tac
QED

Theorem ifexp_abi_bound_induction[local]:
  (!env ty. !tv (sf : (string, (string # type # num) list) fmap).
    evaluate_type env ty = SOME tv /\
    (!nsid args fields.
      FLOOKUP env nsid = SOME (StructArgs args) /\
      FLOOKUP sf (nsid_to_string nsid) = SOME fields ==>
      MAP (\(name,ty,sz). (name,ty)) fields = args) ==>
    (is_abi_dynamic sf ty ==> vyper_is_dynamic env ty) /\
    abi_size_bound sf ty <= vyper_abi_size_bound env ty /\
    (~is_abi_dynamic sf ty ==> abi_static_size sf ty <= vyper_abi_size_bound env ty)) /\
  (!env tys acc. !tvs (sf : (string, (string # type # num) list) fmap).
    evaluate_types env tys acc = SOME tvs /\
    (!nsid args fields.
      FLOOKUP env nsid = SOME (StructArgs args) /\
      FLOOKUP sf (nsid_to_string nsid) = SOME fields ==>
      MAP (\(name,ty,sz). (name,ty)) fields = args) ==>
    EVERY (\ty.
      (is_abi_dynamic sf ty ==> vyper_is_dynamic env ty) /\
      abi_size_bound sf ty <= vyper_abi_size_bound env ty /\
      (~is_abi_dynamic sf ty ==> abi_static_size sf ty <= vyper_abi_size_bound env ty)) tys)
Proof
  ho_match_mp_tac evaluate_type_ind >>
  conj_tac >- suspend "base" >>
  conj_tac >- suspend "tuple" >>
  conj_tac >- suspend "array" >>
  conj_tac >- suspend "struct" >>
  conj_tac >- suspend "flag" >>
  conj_tac >- suspend "none" >>
  conj_tac >- simp[] >>
  suspend "cons"
QED

Resume ifexp_abi_bound_induction[base]:
  Cases_on `bt` >> simp[is_abi_dynamic_def, abi_size_bound_def,
    abi_static_size_def, vyperABITheory.vyper_is_dynamic_def,
    vyperABITheory.vyper_abi_size_bound_def, contractABITheory.ceil32_def] >>
  rename1 `BytesT bound` >> Cases_on `bound` >> simp[is_abi_dynamic_def, abi_size_bound_def,
    abi_static_size_def, vyperABITheory.vyper_is_dynamic_def,
    vyperABITheory.vyper_abi_size_bound_def, contractABITheory.ceil32_def]
QED
Resume ifexp_abi_bound_induction[tuple]:
  rpt gen_tac >> strip_tac >> rpt gen_tac >> strip_tac >>
  gvs[Once evaluate_type_def, AllCaseEqs()] >>
  qpat_x_assum `!sf. _ ==> EVERY _ tys` mp_tac >>
  disch_then (qspec_then `sf` mp_tac) >>
  (impl_tac >- (rpt strip_tac >> first_x_assum drule_all >> simp[])) >>
  strip_tac >>
  simp[Once is_abi_dynamic_def, Once abi_size_bound_def,
       Once abi_static_size_def, abi_embedded_static_size_def,
       Once vyperABITheory.vyper_is_dynamic_def,
       Once vyperABITheory.vyper_abi_size_bound_def] >>
  conj_tac >- (strip_tac >> irule (INST_TYPE [``:'a`` |-> ``:string``, ``:'b`` |-> ``:num``] ifexp_abi_members_dynamic) >>
    qexists_tac `sf` >> gvs[EVERY_MEM, ETA_THM] >> metis_tac[]) >>
  conj_tac >- (irule ifexp_abi_members_bound >> simp[]) >>
  strip_tac >>
  gvs[Once is_abi_dynamic_def, Once vyperABITheory.vyper_abi_size_bound_def] >>
  `MAP (\t. if is_abi_dynamic sf t then 32 else abi_static_size sf t) tys =
   MAP (abi_static_size sf) tys` by
    (irule MAP_CONG >> gvs[EVERY_MEM, combinTheory.o_DEF] >> metis_tac[]) >>
  simp[] >> irule ifexp_abi_static_members_bound >>
  gvs[EVERY_MEM, combinTheory.o_DEF] >> metis_tac[]
QED
Resume ifexp_abi_bound_induction[array]:
  rpt gen_tac >> strip_tac >> rpt gen_tac >> strip_tac >>
  gvs[Once evaluate_type_def, AllCaseEqs()] >>
  qpat_x_assum `!sf. _ ==> (_ /\ _ /\ _)` (qspec_then `sf` mp_tac) >>
  (impl_tac >- (rpt strip_tac >> first_x_assum drule_all >> simp[])) >>
  strip_tac >> Cases_on `bd` >>
  simp[is_abi_dynamic_def, abi_size_bound_def, abi_static_size_def,
       abi_embedded_static_size_def, vyperABITheory.vyper_is_dynamic_def,
       vyperABITheory.vyper_abi_size_bound_def] >>
  Cases_on `is_abi_dynamic sf ty` >> Cases_on `vyper_is_dynamic env ty` >>
  gvs[]
QED
Resume ifexp_abi_bound_induction[struct]:
  rpt gen_tac >> strip_tac >> rpt gen_tac >> strip_tac >>
  gvs[Once evaluate_type_def, AllCaseEqs()] >>
  Cases_on `FLOOKUP sf (nsid_to_string nsid)`
  >- (drule ifexp_abi_missing_struct >> simp[]) >>
  rename1 `FLOOKUP sf (nsid_to_string nsid) = SOME fields` >>
  `MAP (FST o SND) fields = MAP SND args` by
    (irule ifexp_sfields_partial_types >> metis_tac[]) >>
  qpat_x_assum `!sf. _ ==> EVERY _ _`
    (qspec_then `sf \\ nsid_to_string nsid` mp_tac) >>
  (impl_tac >- (rpt gen_tac >> strip_tac >>
    irule ifexp_sfields_partial_delete >> metis_tac[])) >>
  strip_tac >>
  simp[Once is_abi_dynamic_def, Once abi_size_bound_def,
       Once abi_static_size_def, abi_embedded_static_size_def,
       Once vyperABITheory.vyper_is_dynamic_def,
       Once vyperABITheory.vyper_abi_size_bound_def] >>
  conj_tac >- (strip_tac >>
    irule (INST_TYPE [``:'a`` |-> ``:string``, ``:'b`` |-> ``:num``]
      ifexp_abi_members_dynamic) >>
    qexists_tac `sf \\ nsid_to_string nsid` >>
    gvs[EVERY_MEM, combinTheory.o_DEF] >> metis_tac[]) >>
  conj_tac >- (irule ifexp_abi_members_bound >> simp[]) >>
  strip_tac >>
  gvs[Once is_abi_dynamic_def, Once vyperABITheory.vyper_abi_size_bound_def] >>
  qmatch_goalsub_abbrev_tac `SUM (MAP (\t. if is_abi_dynamic sf1 t then 32 else abi_static_size sf1 t) tys)` >>
  `MAP (\t. if is_abi_dynamic sf1 t then 32 else abi_static_size sf1 t) tys =
   MAP (abi_static_size sf1) tys` by
    (irule MAP_CONG >> gvs[EVERY_MEM, combinTheory.o_DEF, Abbr `sf1`, Abbr `tys`] >>
     metis_tac[]) >>
  simp[] >> irule ifexp_abi_static_members_bound >>
  gvs[EVERY_MEM, combinTheory.o_DEF, Abbr `sf1`, Abbr `tys`] >> metis_tac[]
QED
Resume ifexp_abi_bound_induction[flag]:
  simp[is_abi_dynamic_def, abi_size_bound_def, abi_static_size_def,
       vyperABITheory.vyper_is_dynamic_def, vyperABITheory.vyper_abi_size_bound_def]
QED
Resume ifexp_abi_bound_induction[none]:
  simp[is_abi_dynamic_def, abi_size_bound_def, abi_static_size_def,
       vyperABITheory.vyper_is_dynamic_def, vyperABITheory.vyper_abi_size_bound_def]
QED
Resume ifexp_abi_bound_induction[cons]:
  rpt gen_tac >> strip_tac >> rpt gen_tac >> strip_tac >>
  gvs[Once evaluate_type_def, AllCaseEqs()] >>
  qpat_x_assum `!sf. _ ==> EVERY _ tys` (qspec_then `sf` mp_tac) >>
  (impl_tac >- (rpt strip_tac >> first_x_assum drule_all >> simp[])) >>
  strip_tac >> simp[] >>
  qpat_x_assum `!sf. _ ==> (_ /\ _ /\ _)` (qspec_then `sf` mp_tac) >>
  (impl_tac >- (rpt strip_tac >> first_x_assum drule_all >> simp[])) >> simp[]
QED
Finalise ifexp_abi_bound_induction[local]

Theorem ifexp_compat_abi_size_bound_source:
  evaluate_type env ty = SOME tv /\
  sfields_tenv_consistent (sf : (string, (string # type # num) list) fmap) env ==>
  abi_size_bound sf ty <= vyper_abi_size_bound env ty
Proof
  strip_tac >>
  `!nsid args fields.
    FLOOKUP env nsid = SOME (StructArgs args) /\
    FLOOKUP sf (nsid_to_string nsid) = SOME fields ==>
    MAP (\(name,ty,sz). (name,ty)) fields = args` by
      (rpt gen_tac >> strip_tac >> irule ifexp_sfields_partial >> metis_tac[]) >>
  drule (cj 1 ifexp_abi_bound_induction) >>
  disch_then (qspec_then `sf` mp_tac) >>
  (impl_tac >- (rpt strip_tac >> first_x_assum drule_all >> simp[])) >> simp[]
QED

Theorem ifexp_compat_abi_tuple_size_bound_source:
  evaluate_types env tys [] = SOME tvs /\
  sfields_tenv_consistent (sf : (string, (string # type # num) list) fmap) env ==>
  abi_size_bound sf (TupleT tys) <= vyper_abi_size_bound env (TupleT tys)
Proof
  strip_tac >>
  `!nsid args fields.
    FLOOKUP env nsid = SOME (StructArgs args) /\
    FLOOKUP sf (nsid_to_string nsid) = SOME fields ==>
    MAP (\(name,ty,sz). (name,ty)) fields = args` by
      (rpt gen_tac >> strip_tac >> irule ifexp_sfields_partial >> metis_tac[]) >>
  drule (cj 2 ifexp_abi_bound_induction) >>
  disch_then (qspec_then `sf` mp_tac) >>
  (impl_tac >- (rpt strip_tac >> first_x_assum drule_all >> simp[])) >>
  strip_tac >>
  simp[Once abi_size_bound_def, abi_embedded_static_size_def,
       Once vyperABITheory.vyper_abi_size_bound_def] >>
  irule ifexp_abi_members_bound >> simp[]
QED

Theorem ifexp_concat_lowered_fits[local]:
  !ty n args.
    well_typed_builtin_app ty (Concat n) (MAP expr_type args) ==>
    is_bytestring_type ty /\
    is_bytestring_type
      (concat_buffer_type ty (SUM (MAP (concat_payload_capacity o expr_type) args))) /\
    arg_type_fits
      (concat_buffer_type ty (SUM (MAP (concat_payload_capacity o expr_type) args))) ty
Proof
  rpt gen_tac >> simp[vyperTypeSystemTheory.well_typed_builtin_app_def] >>
  strip_tac >>
  `!ts. EVERY (\t. (?bd. t = BaseT (BytesT bd)) \/ ?m. t = BaseT (StringT m)) ts ==>
        MAP bytelike_type_bound ts = MAP concat_payload_capacity ts` by
    (Induct >> simp[] >> rpt strip_tac >>
     gvs[vyperTypeSystemTheory.bytelike_type_bound_def, concat_payload_capacity_def] >>
     rename1 `BytesT bd` >> Cases_on `bd` >>
     simp[vyperASTTheory.bound_length_def, concat_payload_capacity_def]) >>
  `MAP bytelike_type_bound (MAP expr_type args) =
   MAP concat_payload_capacity (MAP expr_type args)` by
    (first_x_assum irule >> fs[EVERY_MEM]) >>
  fs[MAP_MAP_o] >>
  gvs[concat_buffer_type_def, is_bytestring_type_def,
      vyperTypeSystemTheory.arg_type_fits_def]
QED

Theorem ifexp_lowered_type_classify:
  !ce e env.
  well_typed_expr env e /\
  (!id t. FLOOKUP env.var_types id = SOME t ==>
          well_formed_type env.type_defs t) /\
  sfields_tenv_consistent ce.ce_struct_fields env.type_defs ==>
  lowered_value_type ce e = expr_type e \/
  is_bytestring_type (expr_type e) /\ is_bytestring_type (lowered_value_type ce e) /\
    arg_type_fits (lowered_value_type ce e) (expr_type e) \/
  (?ty fid args drv. e = Call ty (IntCall fid) args drv)
Proof
  ho_match_mp_tac lowered_value_type_ind >>
  simp[lowered_value_type_def, expr_type_def,
       vyperTypeSystemTheory.well_typed_expr_def,
       vyperTypeSystemTheory.type_builtin_result_ok_def,
       vyperTypeCallGraphTheory.int_calls_expr_def,
       is_bytestring_type_def] >>
  rpt strip_tac >> gvs[vyperTypeSystemTheory.well_typed_literal_def,
    vyperTypeSystemTheory.arg_type_fits_def, vyperValueTheory.compatible_bound_def] >>
  `!xs. well_typed_exprs env xs ==>
         EVERY (well_formed_type env.type_defs o expr_type) xs` by
    (Induct >> simp[vyperTypeSystemTheory.well_typed_expr_def] >>
     rpt strip_tac >> irule exprSafeOperandTheory.well_typed_expr_type_well_formed >>
     goal_assum drule >> simp[]) >>
  `EVERY (well_formed_type env.type_defs o expr_type) args` by metis_tac[] >>
  `!xs acc. EVERY (well_formed_type env.type_defs o expr_type) xs ==>
     ?tvs. evaluate_types env.type_defs (MAP expr_type xs) acc = SOME tvs` by
    (Induct >> simp[evaluate_type_def, vyperTypeSystemTheory.well_formed_type_def] >>
     rpt strip_tac >> gvs[optionTheory.IS_SOME_EXISTS] >> simp[]) >>
  `?tvs. evaluate_types env.type_defs (MAP expr_type args) [] = SOME tvs` by metis_tac[] >>
  TRY (disj2_tac >> irule ifexp_concat_lowered_fits >>
       goal_assum drule >> NO_TAC) >>
  qmatch_goalsub_abbrev_tac `abi_size_bound ce.ce_struct_fields enc_ty` >>
  `abi_size_bound ce.ce_struct_fields enc_ty <= vyper_abi_size_bound env.type_defs enc_ty` by
    (simp[Abbr `enc_ty`] >> IF_CASES_TAC >-
       (`?tv. evaluate_type env.type_defs (expr_type (HD args)) = SOME tv` by
          (gvs[LENGTH_EQ_NUM_compute, combinTheory.o_DEF,
               evaluate_type_def, AllCaseEqs()]) >>
        irule ifexp_compat_abi_size_bound_source >> simp[] >> metis_tac[]) >>
     irule ifexp_compat_abi_tuple_size_bound_source >> simp[] >> metis_tac[]) >>
  `abi_encode_method_id_size method_id = if IS_SOME method_id then 4 else 0` by
    (Cases_on `method_id` >>
     gvs[vyperTypeSystemTheory.well_typed_type_builtin_args_def,
         vyperTypeSystemTheory.abi_encode_method_id_size_def,
         vyperASTTheory.abi_encode_method_id_bytes_def]) >>
  qpat_x_assum `abi_encode_size_ok _ _ _ _ _` mp_tac >>
  simp[vyperTypeSystemTheory.abi_encode_size_ok_def] >>
  Cases_on `args` >>
  gvs[vyperTypeSystemTheory.well_typed_type_builtin_args_def] >>
  simp[Abbr `enc_ty`, is_bytestring_type_def] >>
  qmatch_asmsub_rename_tac `well_typed_exprs env (head::rest)` >>
  Cases_on `ensure` >> Cases_on `rest` >>
  gvs[is_bytestring_type_def] >> decide_tac
QED

Theorem ifexp_compat_lowered_type:
  !ce e env.
  well_typed_expr env e /\
  (!id t. FLOOKUP env.var_types id = SOME t ==>
          well_formed_type env.type_defs t) /\
  sfields_tenv_consistent ce.ce_struct_fields env.type_defs /\
  (int_calls_expr e = [] \/ same_memory_layout ce (lowered_value_type ce e) (expr_type e)) ==>
  lowered_value_type ce e = expr_type e \/
  is_bytestring_type (expr_type e) /\ is_bytestring_type (lowered_value_type ce e) /\
    arg_type_fits (lowered_value_type ce e) (expr_type e) \/
  same_memory_layout ce (lowered_value_type ce e) (expr_type e)
Proof
  rpt strip_tac >> drule ifexp_lowered_type_classify >>
  disch_then (qspec_then `ce` mp_tac) >>
  (impl_tac >- metis_tac[]) >> strip_tac >>
  gvs[vyperTypeCallGraphTheory.int_calls_expr_def]
QED

Theorem ifexp_compat_body_pre_lowered_type:
  expr_body_pre ce cx env e es /\
  (int_calls_expr e = [] \/ same_memory_layout ce (lowered_value_type ce e) (expr_type e)) ==>
  lowered_value_type ce e = expr_type e \/
  is_bytestring_type (expr_type e) /\ is_bytestring_type (lowered_value_type ce e) /\
    arg_type_fits (lowered_value_type ce e) (expr_type e) \/
  (same_memory_layout ce (lowered_value_type ce e) (expr_type e) /\
   arg_type_fits (lowered_value_type ce e) (expr_type e) /\
   (?tvp. evaluate_type (get_tenv cx) (lowered_value_type ce e) = SOME tvp))
Proof
  strip_tac >>
  drule expr_body_pre_var_types_well_formed >> strip_tac >>
  `well_typed_expr env e /\
   sfields_tenv_consistent ce.ce_struct_fields env.type_defs` by
    gvs[expr_body_pre_def, expr_sim_inv_def,
        vyperTypeInvariantsTheory.env_consistent_def,
        vyperTypeInvariantsTheory.env_context_consistent_def] >>
  drule ifexp_lowered_type_classify >>
  disch_then (qspec_then `ce` mp_tac) >>
  (impl_tac >- metis_tac[]) >> strip_tac >> gvs[] >>
  drule ifexp_body_pre_intcall_physical >>
  gvs[vyperTypeCallGraphTheory.int_calls_expr_def, expr_type_def]
QED
