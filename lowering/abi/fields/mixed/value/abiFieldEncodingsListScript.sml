(* TOP-LEVEL: per-field constructions compose the actual tuple metadata,
   packed-value descriptions and source ABI conversion for complete lists. *)
Theory abiFieldEncodingsList
Ancestors
  abiFieldEncodingDefs abiFieldValueDefs abiFieldTypeMetadata abiFieldDefs abiFieldSource abiFieldLayoutDefs
  vyperABI contractABI list pair

Theorem abi_field_encodings_properties:
  !tys tenv sfields cenv tvs vs avs rows.
    abi_field_encodings tenv sfields cenv tys tvs vs avs rows ==>
    LIST_REL (abi_field_type_row sfields cenv) tys rows /\ abi_field_values tenv rows tvs vs /\
    vyper_to_abi_list tenv tys vs = SOME avs /\
    MAP abi_field_output rows = MAP2 (\ty v. (is_dynamic ty,enc ty v)) (MAP (vyper_to_abi_type tenv) tys) avs /\
    (EXISTS (\row. FST (abi_field_output row)) rows = EXISTS (\ty. is_dynamic (vyper_to_abi_type tenv ty)) tys)
Proof
  Induct_on `tys`
  >- (rpt gen_tac >> Cases_on `tvs` >> Cases_on `vs` >> Cases_on `avs` >> Cases_on `rows` >>
      simp[abi_field_encodings_def, abi_field_values_def, Once vyper_to_abi_def]) >>
  qx_gen_tac `ty` >> rpt gen_tac >> Cases_on `tvs` >> Cases_on `vs` >> Cases_on `avs` >> Cases_on `rows` >>
  simp_tac bool_ss [abi_field_encodings_def] >> strip_tac >>
  rename1 `abi_field_encoding tenv sfields cenv ty head_tv head_value head_abi head_row` >>
  rename1 `abi_field_encodings tenv sfields cenv tys tail_tvs tail_values tail_abis tail_rows` >>
  first_x_assum (qspecl_then [`tenv`, `sfields`, `cenv`, `tail_tvs`, `tail_values`, `tail_abis`, `tail_rows`] mp_tac) >>
  impl_tac >- first_assum MATCH_ACCEPT_TAC >> strip_tac >>
  qpat_x_assum `abi_field_encoding _ _ _ _ _ _ _ _` (strip_assume_tac o PURE_REWRITE_RULE [abi_field_encoding_def]) >>
  asm_simp_tac bool_ss [LIST_REL_def, abi_field_values_def, MAP, MAP2, EXISTS_DEF, FST, Once vyper_to_abi_def] >> simp[]
QED

Theorem abi_field_encodings_source_bytes:
  !tenv sfields cenv tys tvs vs avs rows.
    abi_field_encodings tenv sfields cenv tys tvs vs avs rows /\
    LIST_REL (\ty av. ~is_dynamic ty ==> LENGTH (enc ty av) = static_length ty)
      (MAP (vyper_to_abi_type tenv) tys) avs ==>
    enc (Tuple (MAP (vyper_to_abi_type tenv) tys)) (ListV avs) =
      abi_field_bytes (abi_field_head_size (MAP abi_field_output rows)) (MAP abi_field_output rows)
Proof
  rpt gen_tac >> strip_tac >> drule_all abi_field_encodings_properties >> strip_tac >>
  drule_all enc_tuple_head_size >> DISCH_TAC >> asm_simp_tac bool_ss []
QED

Theorem abi_field_encodings_build:
  !tys tenv sfields cenv tvs vs.
    LENGTH tvs = LENGTH vs /\
    LIST_REL (\ty pair. ?row av. abi_field_encoding tenv sfields cenv ty (FST pair) (SND pair) av row) tys (ZIP (tvs,vs)) ==>
    ?rows avs. abi_field_encodings tenv sfields cenv tys tvs vs avs rows
Proof
  Induct_on `tys`
  >- (rpt gen_tac >> Cases_on `tvs` >> Cases_on `vs` >> simp_tac (srw_ss()) [LENGTH, ZIP, LIST_REL_def] >>
      qexistsl_tac [`[]`, `[]`] >> simp[abi_field_encodings_def]) >>
  qx_gen_tac `ty` >> rpt gen_tac >> Cases_on `tvs`
  >- (Cases_on `vs` >> simp[LENGTH, ZIP]) >> Cases_on `vs` >- simp[LENGTH, ZIP] >>
  simp_tac (srw_ss()) [LENGTH, ZIP, LIST_REL_def, FST, SND] >> strip_tac >>
  rename1 `abi_field_encoding tenv sfields cenv ty head_tv head_value head_abi head_row` >>
  rename1 `LIST_REL _ tys (ZIP (tail_tvs,tail_values))` >>
  first_x_assum (qspecl_then [`tenv`, `sfields`, `cenv`, `tail_tvs`, `tail_values`] mp_tac) >>
  impl_tac >- (rpt conj_tac >> first_assum MATCH_ACCEPT_TAC) >>
  disch_then (qx_choose_then `tail_rows` (qx_choose_then `tail_abis` ASSUME_TAC)) >>
  qexistsl_tac [`head_row::tail_rows`, `head_abi::tail_abis`] >> simp[abi_field_encodings_def]
QED

val () = List.app (fn (name,th) =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th)
  in if null axioms andalso null (Thm.hyp th) andalso
      List.all (fn s => s = "DISK_THM") oracles
    then () else raise Fail ("unclosed complete lists of source/compiler field encodings: " ^ name)
  end) (DB.thms "abiFieldEncodingsList")
