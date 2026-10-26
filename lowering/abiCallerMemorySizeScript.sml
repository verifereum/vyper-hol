(* Byte-size agreement supplied by actual checked compiler construction.
   Structs use the full-environment field builder; array and tuple cases use
   successful child type evaluation. No layout-agreement predicate is assumed. *)
Theory abiCallerMemorySize
Ancestors
  abiCallerStructSize abiCallerStructFields abiCallerTypeEnv compileVyper compileEnv valueEncoding
  vyperTypeABI vyperValue vyperContext vyperAST vfmConstants
  finite_map list pair arithmetic

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
