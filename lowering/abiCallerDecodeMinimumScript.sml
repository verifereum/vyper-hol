(* Source validity supplies the actual compiler minimum-length guard.
   Dynamic member offsets use validity's head extents, including empty fixed arrays. *)
Theory abiCallerDecodeMinimum
Ancestors
  abiCallerAbiShape abiCallerStructMap abiCallerCoherenceNodes abiValidAggregateHeads
  abiValidMembers abiDecodeRanges compileVyper compileEnv vyperValue vyperABI
  vyperABIValid contractABI finite_map list pair combin arithmetic

Theorem abi_caller_embedded_head:
  abi_caller_abi_shape sf env ty ==>
  abi_embedded_static_size sf ty = abi_member_head_size (vyper_to_abi_type env ty)
Proof
  Cases_on `is_dynamic (vyper_to_abi_type env ty)` >>
  simp[abi_caller_abi_shape_def, abi_embedded_static_size_def, abi_member_head_size_def]
QED

Theorem abi_caller_members_head:
  !tys. EVERY (abi_caller_abi_shape sf env) tys ==>
  MAP (\ty. if is_abi_dynamic sf ty then 32 else abi_static_size sf ty) tys =
    MAP abi_member_head_size (vyper_to_abi_types env tys)
Proof
  Induct_on `tys` >> simp[vyper_to_abi_type_def] >>
  qx_gen_tac `elem_ty` >> strip_tac >>
  `abi_embedded_static_size sf elem_ty =
    abi_member_head_size (vyper_to_abi_type env elem_ty)` by
    (irule abi_caller_embedded_head >> simp[]) >>
  fs[abi_embedded_static_size_def]
QED

Theorem abi_caller_decode_minimum_fixed:
  abi_caller_abi_shape sf env ty /\
  valid_enc (vyper_to_abi_type env (ArrayT ty (Fixed n))) bs ==>
  abi_static_size sf (ArrayT ty (Fixed n)) <= LENGTH bs
Proof
  strip_tac >> drule abi_caller_embedded_head >> strip_tac >>
  qpat_x_assum `valid_enc _ _` mp_tac >>
  simp_tac bool_ss [Once vyper_to_abi_type_def, Once valid_enc_def, LET_THM] >>
  strip_tac >> drule abi_valid_array_heads >> strip_tac >>
  asm_simp_tac bool_ss [Once abi_static_size_def, GSYM abi_embedded_static_size_def]
QED

Theorem abi_caller_decode_minimum_tuple:
  EVERY (abi_caller_abi_shape sf env) tys /\
  valid_enc (vyper_to_abi_type env (TupleT tys)) bs ==>
  abi_static_size sf (TupleT tys) <= LENGTH bs
Proof
  strip_tac >> drule abi_caller_members_head >> strip_tac >>
  `valid_enc (Tuple (vyper_to_abi_types env tys)) bs` by
    fs[Once vyper_to_abi_type_def] >>
  drule abi_valid_tuple_view >> strip_tac >>
  asm_simp_tac bool_ss [Once abi_static_size_def]
QED

Theorem abi_caller_decode_minimum_struct:
  FLOOKUP env nsid = SOME (StructArgs args) /\
  FLOOKUP sf (nsid_to_string nsid) = SOME fields /\
  MAP (\(name,ty,sz). (name,ty)) fields = args /\
  EVERY (abi_caller_abi_shape (sf \\ nsid_to_string nsid) (env \\ nsid))
    (MAP SND args) /\
  valid_enc (vyper_to_abi_type env (StructT nsid)) bs ==>
  abi_static_size sf (StructT nsid) <= LENGTH bs
Proof
  strip_tac >> drule_all abi_caller_struct_map_field_types >> strip_tac >>
  drule abi_caller_members_head >> strip_tac >>
  `valid_enc (Tuple (vyper_to_abi_types (env \\ nsid) (MAP SND args))) bs` by
    (qpat_assum `valid_enc (vyper_to_abi_type env (StructT nsid)) bs`
       (mp_tac o ONCE_REWRITE_RULE [vyper_to_abi_type_def]) >>
     asm_simp_tac (srw_ss()) [Excl "valid_enc_def", Excl "dec_def"]) >>
  drule abi_valid_tuple_view >> strip_tac >>
  asm_simp_tac (srw_ss()) [Once abi_static_size_def, LET_THM]
QED

Theorem abi_caller_decode_minimum_array_eval:
  evaluate_type env (ArrayT ty bound) = SOME tv /\
  abi_caller_struct_map sf env /\
  valid_enc (vyper_to_abi_type env (ArrayT ty bound)) bs ==>
  abi_static_size sf (ArrayT ty bound) <= LENGTH bs
Proof
  strip_tac >> Cases_on `bound`
  >- (qpat_x_assum `evaluate_type _ _ = _` mp_tac >>
      simp_tac bool_ss [Once evaluate_type_def, LET_THM] >> strip_tac >>
      gvs[AllCaseEqs(), Excl "valid_enc_def", Excl "dec_def", Excl "vyper_to_abi_type_def"] >>
      drule_all (cj 1 abi_caller_abi_shape_induction) >> strip_tac >>
      drule_all abi_caller_decode_minimum_fixed >> simp[]) >>
  simp[abi_static_size_def]
QED

Theorem abi_caller_decode_minimum_tuple_eval:
  evaluate_type env (TupleT tys) = SOME tv /\ abi_caller_struct_map sf env /\
  valid_enc (vyper_to_abi_type env (TupleT tys)) bs ==>
  abi_static_size sf (TupleT tys) <= LENGTH bs
Proof
  strip_tac >> qpat_x_assum `evaluate_type _ _ = _` mp_tac >>
  simp_tac bool_ss [Once evaluate_type_def, LET_THM] >> strip_tac >>
  gvs[AllCaseEqs(), Excl "valid_enc_def", Excl "dec_def", Excl "vyper_to_abi_type_def"] >>
  drule_all (cj 2 abi_caller_abi_shape_induction) >> strip_tac >>
  drule_all abi_caller_decode_minimum_tuple >> simp[]
QED

Theorem abi_caller_decode_minimum_struct_eval:
  evaluate_type env (StructT nsid) = SOME tv /\ abi_caller_struct_map sf env /\
  valid_enc (vyper_to_abi_type env (StructT nsid)) bs ==>
  abi_static_size sf (StructT nsid) <= LENGTH bs
Proof
  strip_tac >> qpat_x_assum `evaluate_type _ _ = _` mp_tac >>
  simp_tac bool_ss [Once evaluate_type_def, LET_THM] >> strip_tac >>
  gvs[AllCaseEqs(), Excl "valid_enc_def", Excl "dec_def", Excl "vyper_to_abi_type_def"] >>
  rename1 `FLOOKUP env nsid = SOME (StructArgs args)` >>
  drule_all abi_caller_struct_map_namespace >> strip_tac >>
  `abi_caller_struct_map (sf \\ nsid_to_string nsid) (env \\ nsid)` by
    (Cases_on `nsid` >> gvs[nsid_to_string_def] >>
     irule abi_caller_struct_map_delete >> simp[]) >>
  drule_all (cj 2 abi_caller_abi_shape_induction) >> strip_tac >>
  drule_all abi_caller_struct_map_lookup >> strip_tac >>
  drule_all abi_caller_decode_minimum_struct >> simp[]
QED

Theorem abi_caller_decode_minimum_base:
  static_length (vyper_to_abi_type env (BaseT bt)) <= LENGTH bs ==>
  abi_static_size (sf:string |-> (string # vyperAST$type # num) list) (BaseT bt) <= LENGTH bs
Proof
  Cases_on `bt` >>
  FIRST [rename1 `BytesT bound` >> Cases_on `bound`, all_tac] >>
  simp[abi_static_size_def, vyper_base_to_abi_type_def, vyper_to_abi_type_def]
QED

Theorem abi_caller_decode_minimum:
  evaluate_type env ty = SOME tv /\ abi_caller_struct_map sf env /\
  vyper_valid_enc env ty bs ==>
  abi_static_size sf ty <= LENGTH bs
Proof
  strip_tac >> drule vyper_valid_enc_valid_enc >> strip_tac >>
  drule vyper_valid_enc_length_lower >> strip_tac >>
  Cases_on `ty` >>
  FIRST [drule_all abi_caller_decode_minimum_array_eval >> simp[],
    drule_all abi_caller_decode_minimum_tuple_eval >> simp[],
    drule_all abi_caller_decode_minimum_struct_eval >> simp[],
    drule_all abi_caller_decode_minimum_base >>
      disch_then (qspec_then `sf` ACCEPT_TAC),
    fs[abi_static_size_def]]
QED

Theorem abi_caller_source_decode_minimum:
  contract_namespaces_ok in_deploy [((NONE:num option),tops)] /\
  evaluate_type (type_env tops) ty = SOME tv /\
  evaluate_abi_decode (type_env tops) ty bs = INL v ==>
  abi_static_size
    (build_compile_env tops vis mut func_name fargs ret_type
      (code_stmts:stmt list) use_trans).ce_struct_fields ty <= LENGTH bs
Proof
  strip_tac >> drule evaluate_abi_decode_vyper_valid_enc >> strip_tac >>
  `abi_caller_struct_map
    (build_compile_env tops vis mut func_name fargs ret_type
      code_stmts use_trans).ce_struct_fields (type_env tops)` by
    (irule abi_caller_constructed_struct_map >>
     qexists_tac `in_deploy` >> asm_simp_tac bool_ss []) >>
  drule_all abi_caller_decode_minimum >> simp[]
QED

val () = List.app (fn (n,th) =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th) in
    if null (Thm.hyp th) andalso null axioms andalso
       List.all (fn s => s = "DISK_THM") oracles then
      print ("ABI_CALLER_DECODE_MINIMUM_KERNEL_CLOSED " ^ n ^ "\n")
    else raise Fail ("ABI caller minimum length not kernel closed: " ^ n)
  end) (DB.thms "abiCallerDecodeMinimum");
