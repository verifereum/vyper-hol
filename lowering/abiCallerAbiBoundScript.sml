(* Compiler maximum ABI sizes agree with source bounds under the actual struct map.
   The internal relation also retains both dynamic tags and the static-size case. *)
Theory abiCallerAbiBound
Ancestors
  abiCallerStructMap abiCallerAbiShape compileVyper compileEnv vyperValue vyperABI
  vyperABIValid contractABI finite_map list pair combin arithmetic

Definition abi_caller_abi_bound_def:
  abi_caller_abi_bound sf env ty <=>
    is_abi_dynamic sf ty = is_dynamic (vyper_to_abi_type env ty) /\
    is_abi_dynamic sf ty = vyper_is_dynamic env ty /\
    abi_size_bound sf ty = vyper_abi_size_bound env ty /\
    (~is_abi_dynamic sf ty ==> abi_size_bound sf ty = abi_static_size sf ty)
End

Theorem abi_caller_abi_bound_base:
  abi_caller_abi_bound sf env (BaseT bt)
Proof
  Cases_on `bt` >>
  FIRST [rename1 `BytesT bound` >> Cases_on `bound`, all_tac] >>
  simp[abi_caller_abi_bound_def, is_abi_dynamic_def, abi_static_size_def, abi_size_bound_def,
    vyper_base_to_abi_type_def, vyper_is_dynamic_def, vyper_abi_size_bound_def,
    is_dynamic_def, ceil32_def]
QED

Theorem abi_caller_abi_bound_array:
  abi_caller_abi_bound sf env ty ==>
  abi_caller_abi_bound sf env (ArrayT ty bound)
Proof
  Cases_on `bound` >> Cases_on `is_abi_dynamic sf ty` >>
  gvs[abi_caller_abi_bound_def, is_abi_dynamic_def, abi_static_size_def, abi_size_bound_def,
    abi_embedded_static_size_def, vyper_is_dynamic_def, vyper_abi_size_bound_def,
    is_dynamic_def]
QED

Theorem abi_caller_abi_bound_members:
  !tys. EVERY (abi_caller_abi_bound sf env) tys ==>
  EXISTS (is_abi_dynamic sf) tys = any_dynamic (vyper_to_abi_types env tys) /\
  EXISTS (is_abi_dynamic sf) tys = vyper_any_dynamic env tys /\
  SUM (MAP (\ty. abi_embedded_static_size sf ty +
    (if is_abi_dynamic sf ty then abi_size_bound sf ty else 0)) tys) =
    vyper_abi_size_bound_list env tys /\
  (~EXISTS (is_abi_dynamic sf) tys ==>
    SUM (MAP (\ty. abi_embedded_static_size sf ty +
      (if is_abi_dynamic sf ty then abi_size_bound sf ty else 0)) tys) =
    SUM (MAP (\ty. if is_abi_dynamic sf ty then 32 else abi_static_size sf ty) tys))
Proof
  Induct_on `tys`
  >- simp[vyper_to_abi_type_def, vyper_is_dynamic_def, vyper_abi_size_bound_def] >>
  qx_gen_tac `elem_ty` >>
  simp[abi_caller_abi_bound_def, abi_embedded_static_size_def,
    vyper_to_abi_type_def, vyper_is_dynamic_def, vyper_abi_size_bound_def] >>
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  qpat_x_assum `EVERY (abi_caller_abi_bound sf env) tys ==> _`
    (fn ih => drule_all ih) >> strip_tac >>
  Cases_on `is_abi_dynamic sf elem_ty` >> gvs[abi_embedded_static_size_def] >> decide_tac
QED

Theorem abi_caller_abi_bound_tuple:
  EVERY (abi_caller_abi_bound sf env) tys ==>
  abi_caller_abi_bound sf env (TupleT tys)
Proof
  strip_tac >> drule abi_caller_abi_bound_members >>
  simp[abi_caller_abi_bound_def, is_abi_dynamic_def, abi_static_size_def,
    abi_size_bound_def, vyper_is_dynamic_def, vyper_abi_size_bound_def, is_dynamic_def] >>
  CONV_TAC (DEPTH_CONV ETA_CONV) >> simp[] >> strip_tac >> gvs[]
QED

Theorem abi_caller_abi_bound_struct:
  FLOOKUP env nsid = SOME (StructArgs args) /\
  FLOOKUP sf (nsid_to_string nsid) = SOME fields /\
  MAP (\(name,ty,sz). (name,ty)) fields = args /\
  EVERY (abi_caller_abi_bound (sf \\ nsid_to_string nsid) (env \\ nsid))
    (MAP SND args) ==>
  abi_caller_abi_bound sf env (StructT nsid)
Proof
  strip_tac >> drule_all abi_caller_struct_map_field_types >> strip_tac >>
  drule abi_caller_abi_bound_members >>
  simp[abi_caller_abi_bound_def, is_abi_dynamic_def, abi_static_size_def,
    abi_size_bound_def, vyper_is_dynamic_def, vyper_abi_size_bound_def, is_dynamic_def] >>
  CONV_TAC (DEPTH_CONV ETA_CONV) >> simp[] >> strip_tac >> gvs[]
QED

Theorem abi_caller_abi_bound_struct_children:
  abi_caller_struct_map sf env /\
  FLOOKUP env nsid = SOME (StructArgs args) /\
  (!child_sf. abi_caller_struct_map child_sf (env \\ nsid) ==>
    EVERY (abi_caller_abi_bound child_sf (env \\ nsid)) (MAP SND args)) ==>
  abi_caller_abi_bound sf env (StructT nsid)
Proof
  strip_tac >>
  qpat_assum `abi_caller_struct_map sf env`
    (mp_tac o REWRITE_RULE [abi_caller_struct_map_def]) >>
  disch_then drule >> strip_tac >> gvs[] >>
  rename1 `FLOOKUP sf struct_name = SOME field_rows` >>
  irule abi_caller_abi_bound_struct >>
  qexistsl_tac [`MAP (\(field_name,ty,sz). (field_name,ty)) field_rows`, `field_rows`] >>
  simp[nsid_to_string_def] >>
  first_x_assum irule >> irule abi_caller_struct_map_delete >> simp[]
QED

Theorem abi_caller_abi_bound_induction:
  (!env ty. !tv sf.
    evaluate_type env ty = SOME tv /\ abi_caller_struct_map sf env ==>
    abi_caller_abi_bound sf env ty) /\
  (!env tys acc. !tvs sf.
    evaluate_types env tys acc = SOME tvs /\ abi_caller_struct_map sf env ==>
    EVERY (abi_caller_abi_bound sf env) tys)
Proof
  ho_match_mp_tac evaluate_type_ind >>
  conj_tac >- simp[abi_caller_abi_bound_base] >>
  conj_tac
  >- (rpt gen_tac >> strip_tac >> rpt gen_tac >> strip_tac >>
      gvs[Once evaluate_type_def, AllCaseEqs()] >>
      irule abi_caller_abi_bound_tuple >> first_x_assum irule >> simp[]) >>
  conj_tac
  >- (rpt gen_tac >> strip_tac >> rpt gen_tac >> strip_tac >>
      gvs[Once evaluate_type_def, AllCaseEqs()] >>
      irule abi_caller_abi_bound_array >> first_x_assum irule >> simp[]) >>
  conj_tac
  >- (rpt gen_tac >> strip_tac >> rpt gen_tac >> strip_tac >>
      gvs[Once evaluate_type_def, AllCaseEqs()] >>
      irule abi_caller_abi_bound_struct_children >> simp[]) >>
  conj_tac >- simp[abi_caller_abi_bound_def, is_abi_dynamic_def,
    abi_size_bound_def, abi_static_size_def, vyper_is_dynamic_def,
    vyper_abi_size_bound_def] >>
  conj_tac >- simp[abi_caller_abi_bound_def, is_abi_dynamic_def,
    abi_size_bound_def, abi_static_size_def, vyper_is_dynamic_def,
    vyper_abi_size_bound_def] >>
  conj_tac >- simp[] >>
  rpt gen_tac >> strip_tac >> rpt gen_tac >> strip_tac >>
  gvs[Once evaluate_type_def, AllCaseEqs()] >>
  first_x_assum (fn th => drule_all (cj 1 th)) >> strip_tac >>
  simp[] >> first_x_assum drule_all >> simp[]
QED

Theorem abi_caller_constructed_abi_bound:
  contract_namespaces_ok in_deploy [((NONE:num option),tops)] /\
  evaluate_type (type_env tops) ty = SOME tv ==>
  abi_caller_abi_bound
    (build_compile_env tops vis mut func_name fargs ret_type
      (code_stmts:stmt list) use_trans).ce_struct_fields (type_env tops) ty
Proof
  strip_tac >> irule (cj 1 abi_caller_abi_bound_induction) >>
  simp[] >> irule abi_caller_constructed_struct_map >>
  qexists_tac `in_deploy` >> simp[]
QED

Theorem abi_caller_source_decode_maximum:
  contract_namespaces_ok in_deploy [((NONE:num option),tops)] /\
  evaluate_type (type_env tops) ty = SOME tv /\
  evaluate_abi_decode (type_env tops) ty bs = INL v ==>
  LENGTH bs <= abi_size_bound
    (build_compile_env tops vis mut func_name fargs ret_type
      (code_stmts:stmt list) use_trans).ce_struct_fields ty
Proof
  strip_tac >> mp_tac abi_caller_constructed_abi_bound >>
  impl_tac >- asm_simp_tac bool_ss [] >>
  simp_tac bool_ss [abi_caller_abi_bound_def] >> strip_tac >>
  drule evaluate_abi_decode_vyper_valid_enc >> strip_tac >>
  drule vyper_valid_enc_length_upper >> fs[]
QED
