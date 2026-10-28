(* TOP-LEVEL: actual Vyper tuple and struct metadata select the mixed field
   encoder. The relation concerns pure type metadata, with no execution premise. *)
Theory abiFieldTypeMetadata
Ancestors
  abiFieldDefs abiFieldComplexCode exprLowering compileEnv finite_map list pair combin arithmetic

Definition abi_field_type_row_def:
  abi_field_type_row sfields cenv ty row <=>
    abi_field_entry sfields cenv row =
      (type_to_abi_enc_info sfields cenv ty, abi_embedded_static_size cenv.ce_struct_fields ty,
       type_memory_bytes cenv ty, is_abi_dynamic cenv.ce_struct_fields ty)
End

Theorem abi_field_type_rows_metadata:
  !sfields cenv tys rows.
    LIST_REL (abi_field_type_row sfields cenv) tys rows ==>
    MAP (\ty. (type_to_abi_enc_info sfields cenv ty, abi_embedded_static_size cenv.ce_struct_fields ty,
      type_memory_bytes cenv ty, is_abi_dynamic cenv.ce_struct_fields ty)) tys = MAP (abi_field_entry sfields cenv) rows
Proof
  MAP_EVERY qx_gen_tac [`sfields`, `cenv`] >> Induct_on `tys` >- (Cases >> simp[]) >>
  qx_gen_tac `ty` >> Cases >- simp[] >> simp_tac list_ss [abi_field_type_row_def] >> strip_tac >>
  rename1 `LIST_REL (abi_field_type_row sfields cenv) tys tail_rows` >>
  qpat_x_assum `!rows. _` (qspec_then `tail_rows` mp_tac) >> impl_tac >- first_assum MATCH_ACCEPT_TAC >> gvs[]
QED

Theorem abi_field_type_rows_dynamic:
  !sfields cenv tys rows.
    LIST_REL (abi_field_type_row sfields cenv) tys rows ==>
    (EXISTS (is_abi_dynamic cenv.ce_struct_fields) tys = EXISTS (\row. FST (abi_field_output row)) rows)
Proof
  rpt gen_tac >> DISCH_TAC >> drule_all abi_field_type_rows_metadata >> DISCH_TAC >>
  qpat_x_assum `MAP _ tys = MAP (abi_field_entry sfields cenv) rows`
    (mp_tac o AP_TERM ``EXISTS (\(info:abi_enc_info,head:num,mem:num,flag:bool). flag)``) >>
  PURE_REWRITE_TAC [abi_field_entries_dynamic] >> simp[EXISTS_MAP] >> CONV_TAC (DEPTH_CONV ETA_CONV) >> simp[]
QED

Theorem abi_field_tuple_metadata:
  !sfields cenv tys rows.
    LIST_REL (abi_field_type_row sfields cenv) tys rows /\ EXISTS (\row. FST (abi_field_output row)) rows ==>
    type_to_abi_enc_info sfields cenv (TupleT tys) = AbiComplex (MAP (abi_field_entry sfields cenv) rows)
Proof
  rpt gen_tac >> strip_tac >> drule_all abi_field_type_rows_metadata >> DISCH_TAC >>
  drule_all abi_field_type_rows_dynamic >> DISCH_TAC >>
  `is_abi_dynamic cenv.ce_struct_fields (TupleT tys)` by
    (PURE_ONCE_REWRITE_TAC [is_abi_dynamic_def] >> CONV_TAC (DEPTH_CONV ETA_CONV) >> asm_simp_tac bool_ss []) >>
  asm_simp_tac (srw_ss()) [Once type_to_abi_enc_info_def]
QED

Theorem abi_field_struct_metadata:
  !sfields cenv nsid decl_fields rows.
    is_abi_dynamic cenv.ce_struct_fields (StructT nsid) /\ FLOOKUP sfields (nsid_to_string nsid) = SOME decl_fields /\
    LIST_REL (abi_field_type_row (sfields \\ nsid_to_string nsid) cenv) (MAP (FST o SND) decl_fields) rows ==>
    type_to_abi_enc_info sfields cenv (StructT nsid) = AbiComplex (MAP (abi_field_entry (sfields \\ nsid_to_string nsid) cenv) rows)
Proof
  rpt gen_tac >> strip_tac >> drule_all abi_field_type_rows_metadata >> DISCH_TAC >>
  asm_simp_tac (srw_ss()) [Once type_to_abi_enc_info_def, LET_THM] >>
  qpat_x_assum `MAP _ (MAP _ decl_fields) = MAP (abi_field_entry _ cenv) rows` (SUBST1_TAC o SYM) >>
  simp_tac bool_ss [MAP_MAP_o] >> irule MAP_CONG >> simp[FORALL_PROD, o_DEF]
QED

val () = List.app (fn (name,th) =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th)
  in if null axioms andalso null (Thm.hyp th) andalso
      List.all (fn s => s = "DISK_THM") oracles
    then () else raise Fail ("unclosed actual Vyper metadata for mixed field encoding: " ^ name)
  end) (DB.thms "abiFieldTypeMetadata")
