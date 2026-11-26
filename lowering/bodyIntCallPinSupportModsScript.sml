Theory bodyIntCallPinSupportMods
Ancestors
  exprLowering compileEnv context allocLimitsProps pair

Theorem type_memory_bytes_module_pin:
  !ce src ty. type_memory_bytes (ce with ce_module := src) ty =
              type_memory_bytes ce ty
Proof
  rpt gen_tac >> irule type_memory_bytes_struct_fields >> simp[]
QED

Theorem lowered_value_type_module_pin:
  !ce src e. lowered_value_type (ce with ce_module := src) e =
             lowered_value_type ce e
Proof
  rpt gen_tac >> irule lowered_value_type_frame >> simp[]
QED

Theorem place_type_module_pin:
  !ce src e. place_type (ce with ce_module := src) e = place_type ce e
Proof
  rpt gen_tac >> irule place_type_env_cong >> simp[]
QED

Theorem unwrap_value_module_pin:
  !ce src vv. unwrap_value (ce with ce_module := src) vv = unwrap_value ce vv
Proof
  rpt gen_tac >> Cases_on `vv` >> simp[unwrap_value_def, type_memory_bytes_module_pin]
QED

Theorem typed_copy_module_pin[local]:
  (!ce dst dt src st. compile_store_memory_typed (ce with ce_module := md) dst dt src st =
                      compile_store_memory_typed ce dst dt src st) /\
  (!ce dst src dts sts doff soff.
    compile_typed_copy_fields (ce with ce_module := md) dst src dts sts doff soff =
    compile_typed_copy_fields ce dst src dts sts doff soff) /\
  (!ce dst dt src st n.
    compile_copy_sarray_typed (ce with ce_module := md) dst dt src st n =
    compile_copy_sarray_typed ce dst dt src st n) /\
  (!ce dst dt n src st.
    compile_copy_dynarray_typed (ce with ce_module := md) dst dt n src st =
    compile_copy_dynarray_typed ce dst dt n src st) /\
  (!ce dst src dfs sfs doff soff.
    compile_struct_typed_copy (ce with ce_module := md) dst src dfs sfs doff soff =
    compile_struct_typed_copy ce dst src dfs sfs doff soff)
Proof
  ho_match_mp_tac compile_store_memory_typed_ind >>
  rpt conj_tac >> rpt gen_tac >> TRY (DISCH_THEN (MAP_EVERY ASSUME_TAC o CONJUNCTS)) >>
  once_rewrite_tac[compile_store_memory_typed_def] >>
  simp[type_memory_bytes_module_pin, comp_bind_def, comp_ignore_bind_def,
       FUN_EQ_THM, LET_THM]
  >~ [`is_word_type dt`] >-
    (Cases_on `dt` >> Cases_on `st` >> simp[] >>
     rpt (CHANGED_TAC (BasicProvers.TOP_CASE_TAC >> gvs[]))) >>
  rpt (pairarg_tac >> fs[])
QED

Theorem compile_store_memory_module_pin:
  !ce src a b dt st_ty.
    compile_store_memory (ce with ce_module := src) a b dt st_ty =
    compile_store_memory ce a b dt st_ty
Proof
  simp[compile_store_memory_def, typed_copy_module_pin, type_memory_bytes_module_pin]
QED

Theorem compile_ifexp_arm_module_pin:
  !ce src ret_ty arm_ty vv.
    compile_ifexp_arm (ce with ce_module := src) ret_ty arm_ty vv =
    compile_ifexp_arm ce ret_ty arm_ty vv
Proof
  rpt gen_tac >>
  `(!ce t u. punnable (ce with ce_module := src) t u = punnable ce t u) /\
    (!ce ts us. punnable_list (ce with ce_module := src) ts us =
                punnable_list ce ts us)` by
    (ho_match_mp_tac punnable_ind >>
     rpt conj_tac >> rpt gen_tac >> TRY (DISCH_THEN (MAP_EVERY ASSUME_TAC o CONJUNCTS)) >>
     once_rewrite_tac[punnable_def] >> fs[type_memory_bytes_module_pin]) >>
  simp[compile_ifexp_arm_def, same_memory_layout_def, type_memory_bytes_module_pin,
       unwrap_value_module_pin, compile_store_memory_module_pin]
QED

Theorem type_to_abi_enc_info_module_pin:
  !sf ce ty src. type_to_abi_enc_info sf (ce with ce_module := src) ty =
                  type_to_abi_enc_info sf ce ty
Proof
  ho_match_mp_tac type_to_abi_enc_info_ind >>
  rpt conj_tac >> rpt gen_tac >>
  TRY (DISCH_THEN ASSUME_TAC >> gen_tac) >>
  once_rewrite_tac[type_to_abi_enc_info_def] >>
  simp[type_memory_bytes_module_pin, Cong listTheory.GENLIST_CONG,
       Cong listTheory.MAP_CONG, pairTheory.FORALL_PROD]
  >- (IF_CASES_TAC >> gvs[] >> irule listTheory.GENLIST_CONG >>
      simp[] >> rpt strip_tac >> first_x_assum irule >> qexists `m` >> simp[]) >>
  IF_CASES_TAC >> gvs[] >>
  Cases_on `FLOOKUP sf (nsid_to_string nsid)` >> gvs[] >>
  irule listTheory.MAP_CONG >>
  simp[pairTheory.FORALL_PROD] >> rpt strip_tac >> first_x_assum irule >>
  metis_tac[]
QED

Theorem type_to_abi_dec_info_module_pin:
  !sf ce ty src. type_to_abi_dec_info sf (ce with ce_module := src) ty =
                  type_to_abi_dec_info sf ce ty
Proof
  ho_match_mp_tac type_to_abi_dec_info_ind >>
  rpt conj_tac >> rpt gen_tac >>
  TRY (DISCH_THEN ASSUME_TAC >> gen_tac) >>
  once_rewrite_tac[type_to_abi_dec_info_def] >>
  simp[type_memory_bytes_module_pin, Cong listTheory.GENLIST_CONG,
       Cong listTheory.MAP_CONG, pairTheory.FORALL_PROD]
  >- (irule listTheory.GENLIST_CONG >> simp[] >> rpt strip_tac >>
      first_x_assum irule >> qexists `m` >> simp[]) >>
  Cases_on `FLOOKUP sf (nsid_to_string nsid)` >> gvs[] >>
  irule listTheory.MAP_CONG >> simp[pairTheory.FORALL_PROD] >>
  rpt strip_tac >> first_x_assum irule >> metis_tac[]
QED

Theorem encode_value_rows_module_pin[local]:
  !rows dst cursor off.
    compile_abi_encode_value_rows (ce with ce_module := src) dst cursor off rows =
    compile_abi_encode_value_rows ce dst cursor off rows
Proof
  Induct >- simp[compile_abi_encode_value_rows_def] >>
  Cases >> simp[compile_abi_encode_value_rows_def, unwrap_value_module_pin,
                 type_to_abi_enc_info_module_pin, compile_store_memory_module_pin]
QED

Theorem encode_values_to_buf_module_pin[local]:
  compile_abi_encode_values_to_buf (ce with ce_module := src) dst rows =
  compile_abi_encode_values_to_buf ce dst rows
Proof
  simp[compile_abi_encode_values_to_buf_def, encode_value_rows_module_pin]
QED

Theorem compile_abi_encode_payload_module_pin:
  !ce src single vals tys dst st.
    compile_abi_encode_payload (ce with ce_module := src) single vals tys dst st =
    compile_abi_encode_payload ce single vals tys dst st
Proof
  simp[compile_abi_encode_payload_def, unwrap_value_module_pin,
       type_to_abi_enc_info_module_pin, encode_values_to_buf_module_pin]
QED

Theorem default_return_path_module_pin[local]:
  compile_default_return_path (ce with ce_module := src) ret_ty dflt_ty buf res
    dflt addr skip minsz retsz dec_info =
  compile_default_return_path ce ret_ty dflt_ty buf res dflt addr skip minsz retsz dec_info
Proof
  simp[compile_default_return_path_def, compile_store_memory_module_pin]
QED

Theorem compile_external_call_kwargs_module_pin:
  !ce src addr vals tys abisz mid retsz minsz outsz stat cv gas skip has_dflt dflt ret_ty dflt_ty dec_info st.
    compile_external_call_kwargs (ce with ce_module := src) addr vals tys abisz mid retsz minsz outsz stat cv gas skip has_dflt dflt ret_ty dflt_ty dec_info st =
    compile_external_call_kwargs ce addr vals tys abisz mid retsz minsz outsz stat cv gas skip has_dflt dflt ret_ty dflt_ty dec_info st
Proof
  simp[compile_external_call_kwargs_def, encode_values_to_buf_module_pin,
       default_return_path_module_pin]
QED
