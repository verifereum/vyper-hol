Theory abiCallerTupleLayout
Ancestors
  valueEncodingTyping vyperTypeABI vyperABI vyperValue valueEncoding vfmConstants list pair
  arithmetic abiCallerStructSize abiCallerTypeEnv compileVyper compileEnv vyperContext vyperAST
  finite_map abiCallerAbiShape abiDecoderCoherence abiDecodeRanges contractABI
  abiDecoderCallerFlags abiDecoderPrimitiveCaller abiTupleEncodeSourceLayout
  abiTupleEncodeLayout

(* Static ABI lengths equal semantic memory sizes for successfully evaluated
   types. This semantic boundary assumes no compiler metadata or coherence. *)
Theorem abi_caller_static_base_memory:
  evaluate_type env (BaseT bt) = SOME tv /\
  ~is_dynamic (vyper_to_abi_type env (BaseT bt)) ==>
  static_length (vyper_to_abi_type env (BaseT bt)) = type_memory_size tv
Proof
  Cases_on `bt` >>
  FIRST [rename1 `BytesT bound` >> Cases_on `bound`, all_tac] >>
  simp_tac bool_ss [Once evaluate_type_def, AllCaseEqs(), LET_THM] >>
  rpt strip_tac >> gvs[] >>
  simp_tac bool_ss [Once type_memory_size_def, word_size_def]
QED

Theorem abi_caller_static_fixed_array_memory:
  (!child. evaluate_type env ty = SOME child /\
     ~is_dynamic (vyper_to_abi_type env ty) ==>
     static_length (vyper_to_abi_type env ty) = type_memory_size child) /\
  evaluate_type env (ArrayT ty (Fixed n)) = SOME tv /\
  ~is_dynamic (vyper_to_abi_type env ty) ==>
  static_length (vyper_to_abi_type env (ArrayT ty (Fixed n))) = type_memory_size tv
Proof
  strip_tac >>
  qpat_x_assum `evaluate_type _ (ArrayT _ _) = SOME _`
    (mp_tac o ONCE_REWRITE_RULE [evaluate_type_def]) >>
  simp_tac bool_ss [LET_THM] >> strip_tac >>
  gvs[AllCaseEqs(), type_memory_size_def]
QED

Theorem abi_caller_static_tuple_memory:
  (!tvs. LIST_REL (\ty tv. evaluate_type env ty = SOME tv) tys tvs /\
     ~any_dynamic (vyper_to_abi_types env tys) ==>
     static_length (Tuple (vyper_to_abi_types env tys)) = type_memory_size_list tvs) /\
  evaluate_type env (TupleT tys) = SOME tv /\
  ~any_dynamic (vyper_to_abi_types env tys) ==>
  static_length (vyper_to_abi_type env (TupleT tys)) = type_memory_size tv
Proof
  strip_tac >>
  qpat_x_assum `evaluate_type _ (TupleT _) = SOME _`
    (mp_tac o ONCE_REWRITE_RULE [evaluate_type_def]) >>
  simp_tac bool_ss [LET_THM] >> strip_tac >> gvs[AllCaseEqs()] >>
  drule evaluate_types_LIST_REL >> strip_tac >>
  simp[type_memory_size_def] >> first_x_assum irule >> simp[]
QED

(* Upstream form of the positional size fact also used by decoder consumers. *)

Theorem abi_caller_static_struct_memory:
  (!args. FLOOKUP env nsid = SOME (StructArgs args) ==>
    !tvs. LIST_REL (\ty tv. evaluate_type (env \\ nsid) ty = SOME tv)
        (MAP SND args) tvs /\
      ~any_dynamic (vyper_to_abi_types (env \\ nsid) (MAP SND args)) ==>
      static_length (Tuple (vyper_to_abi_types (env \\ nsid) (MAP SND args))) =
        type_memory_size_list tvs) /\
  evaluate_type env (StructT nsid) = SOME tv /\
  ~is_dynamic (vyper_to_abi_type env (StructT nsid)) ==>
  static_length (vyper_to_abi_type env (StructT nsid)) = type_memory_size tv
Proof
  strip_tac >>
  qpat_x_assum `evaluate_type _ (StructT _) = SOME _`
    (mp_tac o ONCE_REWRITE_RULE [evaluate_type_def]) >>
  simp_tac bool_ss [LET_THM] >> strip_tac >> gvs[AllCaseEqs()] >>
  rename1 `FLOOKUP env nsid = SOME (StructArgs field_args)` >>
  rename1 `evaluate_types _ _ [] = SOME field_tvs` >>
  drule evaluate_types_LIST_REL >> strip_tac >>
  `LENGTH (MAP FST field_args) = LENGTH field_tvs` by fs[LIST_REL_EL_EQN] >>
  simp[type_memory_size_def, type_memory_size_fields_zip] >>
  first_x_assum irule >> simp[]
QED

Theorem abi_caller_static_memory_induction:
  (!env ty. !tv. evaluate_type env ty = SOME tv /\
    ~is_dynamic (vyper_to_abi_type env ty) ==>
    static_length (vyper_to_abi_type env ty) = type_memory_size tv) /\
  (!env tys. !tvs. LIST_REL (\ty tv. evaluate_type env ty = SOME tv) tys tvs /\
    ~any_dynamic (vyper_to_abi_types env tys) ==>
    static_length (Tuple (vyper_to_abi_types env tys)) = type_memory_size_list tvs)
Proof
  ho_match_mp_tac vyper_to_abi_type_ind >>
  conj_tac >- simp[abi_caller_static_base_memory] >>
  conj_tac
  >- (rpt gen_tac >> strip_tac >> rpt gen_tac >> strip_tac >>
      irule abi_caller_static_tuple_memory >> gvs[]) >>
  conj_tac >- simp[] >>
  conj_tac
  >- (rpt gen_tac >> strip_tac >> rpt gen_tac >> strip_tac >>
      irule abi_caller_static_fixed_array_memory >> gvs[]) >>
  conj_tac
  >- (rpt gen_tac >> strip_tac >> rpt gen_tac >> strip_tac >>
      irule abi_caller_static_struct_memory >> simp[]) >>
  conj_tac
  >- (simp[Once evaluate_type_def, AllCaseEqs()] >>
      rpt strip_tac >> gvs[type_memory_size_def]) >>
  conj_tac >- simp[evaluate_type_def, type_memory_size_def] >>
  conj_tac >- simp[type_memory_size_def] >>
  rpt gen_tac >> strip_tac >> qx_gen_tac `tvs` >> Cases_on `tvs` >>
  simp[type_memory_size_def] >> rpt strip_tac >>
  qpat_x_assum `!tv. evaluate_type _ _ = SOME tv /\ _ ==> _`
    (fn ih => drule_all ih) >> strip_tac >>
  qpat_x_assum `!tvs. LIST_REL _ _ tvs /\ _ ==> _`
    (fn ih => drule_all ih) >> simp[]
QED

Theorem abi_caller_static_memory:
  evaluate_type env ty = SOME tv /\ ~is_dynamic (vyper_to_abi_type env ty) ==>
  static_length (vyper_to_abi_type env ty) = type_memory_size tv
Proof
  metis_tac[abi_caller_static_memory_induction]
QED

(* Byte-size agreement supplied by actual checked compiler construction.
   Structs use the full-environment field builder; array and tuple cases use
   successful child type evaluation. No layout-agreement predicate is assumed. *)
Theorem abi_caller_base_memory_size:
  evaluate_type env (BaseT bt) = SOME tv ==>
  type_memory_bytes ce (BaseT bt) = type_memory_size tv
Proof
  Cases_on `bt` >>
  FIRST [rename1 `BytesT bnd` >> Cases_on `bnd`, all_tac] >>
  simp_tac bool_ss [Once evaluate_type_def, AllCaseEqs(), LET_THM] >>
  rpt strip_tac >> gvs[] >>
  simp_tac bool_ss
    [Once type_memory_bytes_def, Once type_memory_size_def, word_size_def, MULT_COMM]
QED

Theorem abi_caller_flag_memory_size:
  evaluate_type env (FlagT nsid) = SOME tv ==>
  type_memory_bytes ce (FlagT nsid) = type_memory_size tv
Proof
  simp_tac bool_ss [Once evaluate_type_def, AllCaseEqs()] >>
  rpt strip_tac >> gvs[] >>
  simp_tac bool_ss [Once type_memory_bytes_def, Once type_memory_size_def]
QED

Theorem abi_caller_array_memory_size:
  evaluate_type env (ArrayT ty bnd) = SOME tv /\
  (!child. evaluate_type env ty = SOME child ==>
    type_memory_bytes ce ty = type_memory_size child) ==>
  type_memory_bytes ce (ArrayT ty bnd) = type_memory_size tv
Proof
  strip_tac >>
  qpat_x_assum `evaluate_type _ (ArrayT _ _) = SOME _`
    (mp_tac o ONCE_REWRITE_RULE [evaluate_type_def]) >>
  simp_tac bool_ss [LET_THM] >> strip_tac >> gvs[AllCaseEqs()] >>
  Cases_on `bnd` >>
  asm_simp_tac bool_ss [Once type_memory_bytes_def, Once type_memory_size_def]
QED

Theorem abi_caller_memory_size_list:
  !tys tvs.
  LIST_REL (\ty tv. type_memory_bytes ce ty = type_memory_size tv) tys tvs ==>
  SUM (MAP (type_memory_bytes ce) tys) = type_memory_size_list tvs
Proof
  Induct_on `tys` >> Cases_on `tvs` >> simp[type_memory_size_def] >>
  rpt strip_tac >>
  qpat_x_assum `!tvs. LIST_REL _ _ tvs ==> _` drule >> simp[ADD_COMM]
QED

Theorem abi_caller_tuple_memory_size:
  evaluate_type env (TupleT tys) = SOME tv /\
  (!ty. MEM ty tys ==> !child.
    evaluate_type env ty = SOME child ==>
    type_memory_bytes ce ty = type_memory_size child) ==>
  type_memory_bytes ce (TupleT tys) = type_memory_size tv
Proof
  strip_tac >>
  qpat_x_assum `evaluate_type _ (TupleT _) = SOME _`
    (mp_tac o ONCE_REWRITE_RULE [evaluate_type_def]) >>
  simp_tac bool_ss [LET_THM] >> strip_tac >> gvs[AllCaseEqs()] >>
  rename1 `evaluate_types env tys [] = SOME tvs` >>
  drule evaluate_types_LIST_REL >> strip_tac >>
  simp[type_memory_bytes_def, type_memory_size_def] >>
  CONV_TAC (DEPTH_CONV ETA_CONV) >>
  irule abi_caller_memory_size_list >>
  fs[LIST_REL_EL_EQN] >> rpt strip_tac >>
  rename1 `type_memory_bytes ce (EL ix tys)` >>
  `ix < LENGTH tys` by fs[] >>
  `MEM (EL ix tys) tys` by simp[EL_MEM] >>
  `evaluate_type env (EL ix tys) = SOME (EL ix tvs)` by fs[] >>
  qpat_x_assum `!ty. MEM ty tys ==> _` (fn ih => drule_all ih) >>
  simp[]
QED

Theorem abi_caller_struct_namespace:
  evaluate_type (type_env tops) (StructT nsid) = SOME tv ==>
  FST nsid = NONE
Proof
  Cases_on `nsid` >> strip_tac >>
  qpat_x_assum `evaluate_type _ _ = SOME _`
    (mp_tac o ONCE_REWRITE_RULE [evaluate_type_def]) >>
  simp_tac bool_ss [LET_THM] >> strip_tac >> gvs[AllCaseEqs()] >>
  qpat_assum `FLOOKUP (type_env tops) _ = SOME (StructArgs _)`
    (mp_tac o PURE_REWRITE_RULE [type_env_def]) >> strip_tac >>
  drule (Q.INST [`src` |-> `NONE:num option`] abi_caller_type_env_struct) >> simp[]
QED

Theorem abi_caller_struct_memory_size_namespace:
  !tops vis mut func_name fargs ret_type (code_stmts:stmt list) use_trans
    in_deploy nsid tv.
  contract_namespaces_ok in_deploy [((NONE:num option),tops)] /\
  evaluate_type (type_env tops) (StructT nsid) = SOME tv ==>
  type_memory_bytes
    (build_compile_env tops vis mut func_name fargs ret_type code_stmts use_trans)
    (StructT nsid) = type_memory_size tv
Proof
  rpt gen_tac >> strip_tac >> drule abi_caller_struct_namespace >> strip_tac >>
  Cases_on `nsid` >> gvs[] >>
  irule abi_caller_struct_memory_size >> simp[] >>
  qexists_tac `in_deploy` >> simp[]
QED

Theorem abi_caller_memory_size_induction:
  !tops in_deploy.
  contract_namespaces_ok in_deploy [((NONE:num option),tops)] ==>
  !vis mut func_name fargs ret_type (code_stmts:stmt list) use_trans ce ty tv.
  ce = build_compile_env tops vis mut func_name fargs ret_type code_stmts use_trans /\
  evaluate_type (type_env tops) ty = SOME tv ==>
  type_memory_bytes ce ty = type_memory_size tv
Proof
  map_every qx_gen_tac [`tops`, `in_deploy`] >> strip_tac >>
  map_every qx_gen_tac [`vis`, `mut`, `func_name`, `fargs`, `ret_type`,
                       `code_stmts`, `use_trans`] >>
  ho_match_mp_tac type_memory_bytes_ind >>
  rpt conj_tac >> rpt gen_tac >> rpt strip_tac >> gvs[]
  >- (irule (Q.INST [`env` |-> `type_env tops`,
        `ce` |-> `build_compile_env tops vis mut func_name fargs ret_type code_stmts use_trans`] abi_caller_base_memory_size) >>
      first_assum ACCEPT_TAC) >>
  FIRST
    [irule (Q.INST [`env` |-> `type_env tops`,
        `ce` |-> `build_compile_env tops vis mut func_name fargs ret_type code_stmts use_trans`] abi_caller_base_memory_size) >>
       first_assum ACCEPT_TAC,
     irule (Q.INST [`env` |-> `type_env tops`,
        `ce` |-> `build_compile_env tops vis mut func_name fargs ret_type code_stmts use_trans`] abi_caller_flag_memory_size) >>
       first_assum ACCEPT_TAC,
     irule (Q.INST [`env` |-> `type_env tops`,
        `ce` |-> `build_compile_env tops vis mut func_name fargs ret_type code_stmts use_trans`] abi_caller_array_memory_size) >>
       conj_tac >> first_assum ACCEPT_TAC,
     irule (Q.INST [`env` |-> `type_env tops`,
        `ce` |-> `build_compile_env tops vis mut func_name fargs ret_type code_stmts use_trans`] abi_caller_tuple_memory_size) >>
       conj_tac >> first_assum ACCEPT_TAC,
     irule abi_caller_struct_memory_size_namespace >>
       simp[] >> qexists_tac `in_deploy` >> simp[],
     simp[type_memory_bytes_def, type_memory_size_def]]
QED

Theorem abi_caller_memory_size:
  !tops vis mut func_name fargs ret_type (code_stmts:stmt list) use_trans
    in_deploy ty tv.
  contract_namespaces_ok in_deploy [((NONE:num option),tops)] /\
  evaluate_type (type_env tops) ty = SOME tv ==>
  type_memory_bytes
    (build_compile_env tops vis mut func_name fargs ret_type code_stmts use_trans) ty =
    type_memory_size tv
Proof
  rpt gen_tac >> strip_tac >> drule abi_caller_memory_size_induction >>
  disch_then (qspecl_then [`vis`, `mut`, `func_name`, `fargs`, `ret_type`,
    `code_stmts`, `use_trans`,
    `build_compile_env tops vis mut func_name fargs ret_type code_stmts use_trans`,
    `ty`, `tv`] mp_tac) >> simp[]
QED

Theorem abi_caller_descended_memory_size:
  contract_namespaces_ok in_deploy [((NONE:num option),tops)] /\
  env SUBMAP type_env tops /\ evaluate_type env ty = SOME tv ==>
  type_memory_bytes
    (build_compile_env tops vis mut func_name fargs ret_type
      (code_stmts:stmt list) use_trans) ty = type_memory_size tv
Proof
  strip_tac >> drule_all abi_caller_type_submap >> strip_tac >>
  irule abi_caller_memory_size >> simp[] >>
  qexists_tac `in_deploy` >> simp[]
QED

(* Actual checked compiler construction supplies every decoder header fact.
   Semantic environments may have declarations removed during struct descent.
   No coherence, dynamic-tag or size agreement is assumed at the public API. *)
Theorem abi_caller_header_from_shape:
  evaluate_type env ty = SOME tv /\
  type_memory_bytes ce ty = type_memory_size tv /\
  abi_caller_abi_shape ce.ce_struct_fields env ty ==>
  abi_decoder_header ce env ty tv
Proof
  strip_tac >> Cases_on `is_dynamic (vyper_to_abi_type env ty)` >>
  gvs[abi_decoder_header_def, abi_caller_abi_shape_def,
      abi_embedded_static_size_def, abi_member_head_size_def] >>
  irule abi_caller_static_memory >> simp[]
QED

Theorem abi_caller_descended_abi_shape:
  contract_namespaces_ok in_deploy [((NONE:num option),tops)] /\
  env SUBMAP type_env tops /\ evaluate_type env ty = SOME tv ==>
  abi_caller_abi_shape
    (build_compile_env tops vis mut func_name fargs ret_type
      (code_stmts:stmt list) use_trans).ce_struct_fields env ty
Proof
  strip_tac >> drule_all abi_caller_type_submap >> strip_tac >>
  drule_all abi_caller_abi_type_submap >> strip_tac >>
  mp_tac (Q.INST [`tops` |-> `tops`, `ty` |-> `ty`,
    `in_deploy` |-> `in_deploy`, `tv` |-> `tv`,
    `vis` |-> `vis`, `mut` |-> `mut`, `func_name` |-> `func_name`,
    `fargs` |-> `fargs`, `ret_type` |-> `ret_type`,
    `code_stmts` |-> `code_stmts`, `use_trans` |-> `use_trans`]
      abi_caller_constructed_abi_shape) >>
  simp[abi_caller_abi_shape_def]
QED

Theorem abi_caller_header:
  contract_namespaces_ok in_deploy [((NONE:num option),tops)] /\
  env SUBMAP type_env tops /\ evaluate_type env ty = SOME tv ==>
  abi_decoder_header
    (build_compile_env tops vis mut func_name fargs ret_type
      (code_stmts:stmt list) use_trans) env ty tv
Proof
  strip_tac >> drule_all abi_caller_descended_memory_size >> strip_tac >>
  drule_all abi_caller_descended_abi_shape >> strip_tac >>
  irule abi_caller_header_from_shape >> simp[]
QED

(* Checked construction supplies flag counts, including during semantic
   environment descent. Base-type coherence is reused from the primitive
   caller theory and needs no struct-map invariant. *)
Theorem abi_caller_flag_namespace:
  FLOOKUP (type_env tops) nsid = SOME (FlagArgs n) ==>
  FST nsid = NONE
Proof
  Cases_on `nsid` >> simp[type_env_def] >> strip_tac >>
  drule (Q.INST [`src` |-> `NONE:num option`] type_env_flag_declaration) >> simp[]
QED

Theorem abi_caller_flag_count:
  contract_namespaces_ok in_deploy [((NONE:num option),tops)] /\
  FLOOKUP (type_env tops) nsid = SOME (FlagArgs n) ==>
  (build_compile_env tops vis mut func_name fargs ret_type
    (code_stmts:stmt list) use_trans).ce_flag_n_members (nsid_to_string nsid) = n
Proof
  strip_tac >> drule abi_caller_flag_namespace >> strip_tac >>
  Cases_on `nsid` >> gvs[] >>
  drule_all decoder_caller_flag_count >> simp[nsid_to_string_def]
QED

Theorem abi_caller_flag_coherent:
  contract_namespaces_ok in_deploy [((NONE:num option),tops)] /\
  env SUBMAP type_env tops /\ evaluate_type env (FlagT nsid) = SOME tv ==>
  abi_decoder_coherent
    (build_compile_env tops vis mut func_name fargs ret_type
      (code_stmts:stmt list) use_trans) env sf (FlagT nsid) tv
Proof
  strip_tac >>
  qpat_assum `evaluate_type _ (FlagT _) = SOME _`
    (mp_tac o ONCE_REWRITE_RULE [evaluate_type_def]) >>
  simp_tac bool_ss [LET_THM] >> strip_tac >> gvs[AllCaseEqs()] >>
  rename1 `FLOOKUP env nsid = SOME (FlagArgs members)` >>
  `FLOOKUP (type_env tops) nsid = SOME (FlagArgs members)` by
    (irule FLOOKUP_SUBMAP >> qexists_tac `env` >> simp[]) >>
  drule_all abi_caller_flag_count >> strip_tac >>
  drule_all abi_caller_header >> strip_tac >>
  simp[abi_decoder_coherent_flag_iff]
QED

(* Actual checked construction supplies tuple staging layout directly from
   source type evaluation. Complete argument memory remains a producer fact. *)
Theorem abi_caller_tuple_layout:
  contract_namespaces_ok in_deploy [((NONE:num option),tops)] /\
  LENGTH ops = LENGTH tys /\
  LIST_REL (\ty tv. evaluate_type (type_env tops) ty = SOME tv) tys tvs ==>
  abi_tuple_encode_layout
    (build_compile_env tops vis mut func_name fargs ret_type
      (code_stmts:stmt list) use_trans)
    (ZIP (ops,tys)) (vyper_to_abi_types (type_env tops) tys)
Proof
  strip_tac >>
  `LIST_REL (abi_decoder_header
    (build_compile_env tops vis mut func_name fargs ret_type code_stmts use_trans)
    (type_env tops)) tys tvs` by
    (irule LIST_REL_mono >>
     qexists_tac `\ty tv. evaluate_type (type_env tops) ty = SOME tv` >>
     asm_simp_tac bool_ss [] >> rpt strip_tac >>
     irule abi_caller_header >> simp[] >> qexists_tac `in_deploy` >> simp[]) >>
  drule_all abi_tuple_encode_layout_headers >> simp[]
QED
