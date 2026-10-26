(* Compiler ABI dynamic tags and static heads agree with semantic translation.
   The structural map premise is supplied by actual checked construction in
   abiCallerStructMap. This boundary assumes no byte-size or header equality. *)
Theory abiCallerAbiShape
Ancestors
  abiCallerStructMap compileEnv vyperValue vyperABI contractABI
  finite_map list pair combin

Definition abi_caller_abi_shape_def:
  abi_caller_abi_shape (sf:(string, (string # type # num) list) fmap) env ty <=>
    is_abi_dynamic sf ty = is_dynamic (vyper_to_abi_type env ty) /\
    (~is_dynamic (vyper_to_abi_type env ty) ==>
      abi_static_size sf ty = static_length (vyper_to_abi_type env ty))
End

Theorem abi_caller_abi_shape_base:
  abi_caller_abi_shape sf env (BaseT bt)
Proof
  Cases_on `bt` >>
  FIRST [rename1 `BytesT bound` >> Cases_on `bound`, all_tac] >>
  simp[abi_caller_abi_shape_def, is_abi_dynamic_def, abi_static_size_def,
       vyper_base_to_abi_type_def, is_dynamic_def, static_length_def]
QED

Theorem abi_caller_abi_shape_array:
  abi_caller_abi_shape sf env ty ==>
  abi_caller_abi_shape sf env (ArrayT ty bound)
Proof
  Cases_on `bound` >>
  simp[abi_caller_abi_shape_def, is_abi_dynamic_def, abi_static_size_def,
       is_dynamic_def, static_length_def] >> metis_tac[]
QED

Theorem abi_caller_abi_shape_list:
  !tys. EVERY (abi_caller_abi_shape sf env) tys ==>
    any_dynamic (vyper_to_abi_types env tys) = EXISTS (is_abi_dynamic sf) tys /\
    (~any_dynamic (vyper_to_abi_types env tys) ==>
      SUM (MAP (\ty. if is_abi_dynamic sf ty then 32 else abi_static_size sf ty) tys) =
      static_length (Tuple (vyper_to_abi_types env tys)))
Proof
  Induct >> simp[abi_caller_abi_shape_def, static_length_Tuple_SUM] >>
  rpt strip_tac >> gvs[]
QED

Theorem abi_caller_abi_shape_tuple:
  EVERY (abi_caller_abi_shape sf env) tys ==>
  abi_caller_abi_shape sf env (TupleT tys)
Proof
  strip_tac >> drule abi_caller_abi_shape_list >>
  simp[abi_caller_abi_shape_def, is_abi_dynamic_def, abi_static_size_def] >>
  CONV_TAC (DEPTH_CONV ETA_CONV) >> simp[]
QED

Theorem abi_caller_struct_map_field_types:
  MAP (\(name,ty,sz). (name,ty)) fields = args ==>
  MAP (FST o SND) fields = MAP SND args
Proof
  strip_tac >> pop_assum (SUBST1_TAC o SYM) >>
  simp[MAP_MAP_o, o_DEF, LAMBDA_PROD]
QED

Theorem abi_caller_abi_shape_struct:
  FLOOKUP env nsid = SOME (StructArgs args) /\
  FLOOKUP sf (nsid_to_string nsid) = SOME fields /\
  MAP (\(name,ty,sz). (name,ty)) fields = args /\
  EVERY (abi_caller_abi_shape (sf \\ nsid_to_string nsid) (env \\ nsid))
    (MAP SND args) ==>
  abi_caller_abi_shape sf env (StructT nsid)
Proof
  strip_tac >> drule_all abi_caller_struct_map_field_types >> strip_tac >>
  drule abi_caller_abi_shape_list >>
  simp[abi_caller_abi_shape_def, is_abi_dynamic_def, abi_static_size_def] >>
  CONV_TAC (DEPTH_CONV ETA_CONV) >> simp[]
QED

Theorem abi_caller_abi_shape_struct_children:
  abi_caller_struct_map sf env /\
  FLOOKUP env nsid = SOME (StructArgs args) /\
  (!child_sf. abi_caller_struct_map child_sf (env \\ nsid) ==>
    EVERY (abi_caller_abi_shape child_sf (env \\ nsid)) (MAP SND args)) ==>
  abi_caller_abi_shape sf env (StructT nsid)
Proof
  strip_tac >>
  qpat_assum `abi_caller_struct_map sf env`
    (mp_tac o REWRITE_RULE [abi_caller_struct_map_def]) >>
  disch_then drule >> strip_tac >> gvs[] >>
  rename1 `FLOOKUP sf struct_name = SOME field_rows` >>
  irule abi_caller_abi_shape_struct >>
  qexistsl_tac [`MAP (\(field_name,ty,sz). (field_name,ty)) field_rows`,
    `field_rows`] >> simp[nsid_to_string_def] >>
  first_x_assum irule >> irule abi_caller_struct_map_delete >> simp[]
QED

Theorem abi_caller_abi_shape_induction:
  (!env ty. !tv sf.
    evaluate_type env ty = SOME tv /\ abi_caller_struct_map sf env ==>
    abi_caller_abi_shape sf env ty) /\
  (!env tys acc. !tvs sf.
    evaluate_types env tys acc = SOME tvs /\ abi_caller_struct_map sf env ==>
    EVERY (abi_caller_abi_shape sf env) tys)
Proof
  ho_match_mp_tac evaluate_type_ind >>
  conj_tac >- simp[abi_caller_abi_shape_base] >>
  conj_tac
  >- (rpt gen_tac >> strip_tac >> rpt gen_tac >> strip_tac >>
      gvs[Once evaluate_type_def, AllCaseEqs()] >>
      irule abi_caller_abi_shape_tuple >> first_x_assum irule >> simp[]) >>
  conj_tac
  >- (rpt gen_tac >> strip_tac >> rpt gen_tac >> strip_tac >>
      gvs[Once evaluate_type_def, AllCaseEqs()] >>
      irule abi_caller_abi_shape_array >> first_x_assum irule >> simp[]) >>
  conj_tac
  >- (rpt gen_tac >> strip_tac >> rpt gen_tac >> strip_tac >>
      gvs[Once evaluate_type_def, AllCaseEqs()] >>
      irule abi_caller_abi_shape_struct_children >> simp[]) >>
  conj_tac
  >- simp[abi_caller_abi_shape_def, is_abi_dynamic_def, abi_static_size_def] >>
  conj_tac
  >- simp[abi_caller_abi_shape_def, is_abi_dynamic_def, abi_static_size_def] >>
  conj_tac >- simp[] >>
  rpt gen_tac >> strip_tac >> rpt gen_tac >> strip_tac >>
  gvs[Once evaluate_type_def, AllCaseEqs()] >>
  first_x_assum (fn th => drule_all (cj 1 th)) >> strip_tac >>
  simp[] >> first_x_assum drule_all >> simp[]
QED

Theorem abi_caller_constructed_abi_shape:
  contract_namespaces_ok in_deploy [((NONE:num option),tops)] /\
  evaluate_type (type_env tops) ty = SOME tv ==>
  abi_caller_abi_shape
    (build_compile_env tops vis mut func_name fargs ret_type
      (code_stmts:stmt list) use_trans).ce_struct_fields (type_env tops) ty
Proof
  strip_tac >> irule (cj 1 abi_caller_abi_shape_induction) >>
  simp[] >> irule abi_caller_constructed_struct_map >>
  qexists_tac `in_deploy` >> simp[]
QED

val () = List.app (fn (n,th) =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th) in
    if null (Thm.hyp th) andalso null axioms andalso
       List.all (fn s => s = "DISK_THM") oracles then
      print ("ABI_CALLER_ABI_SHAPE_KERNEL_CLOSED " ^ n ^ "\n")
    else raise Fail ("ABI caller ABI shape not kernel closed: " ^ n)
  end) (DB.thms "abiCallerAbiShape");
