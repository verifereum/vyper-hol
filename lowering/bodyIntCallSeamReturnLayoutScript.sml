Theory bodyIntCallSeamReturnLayout
Ancestors bodyIntCallMetadata bodyIntCallPackageBoundary compileEnv exprLowering
  bodySim supportedNames supportedProgram compileVyper
  exprSimHyps exprSimHypsDefs vyperTypeSystem vyperTypeInvariants

Theorem returns_stack_count_bound:
  !sft ty. returns_stack_count sft ty <= 2
Proof
  rpt gen_tac >> Cases_on `ty` >>
  simp[returns_stack_count_def, tuple_like_stack_count_def,
    MAX_STACK_RETURNS_def] >> rpt IF_CASES_TAC >> simp[]
QED

Theorem body_internal_decl_info:
  body_inv tops ctx ce cx /\
  MEM (FunctionDecl Internal mut nr rr name args dflts ret stmts) tops /\
  ce.ce_func_info (nsid_to_string (NONE,name)) = (rcn,rbs,pvs) ==>
  compute_func_info
    (\n. MAP (FST o SND) (get_struct_fields ce.ce_struct_fields n)) ret
    (type_mem_bytes (get_struct_fields ce.ce_struct_fields) ret)
    (MAP SND args) = (rcn,rbs,pvs)
Proof
  strip_tac >>
  `ALL_DISTINCT (supported_function_names tops)` by
    (fs[body_inv_def] >> drule supported_program_names >>
     simp[supported_declaration_names_def]) >>
  drule_all (SRULE [] (Q.SPEC `Internal`
    (Q.GEN `vis` (SPEC_ALL build_func_info_distinct)))) >>
  disch_then (qspec_then `get_struct_fields ce.ce_struct_fields` mp_tac) >>
  fs[body_inv_def, nsid_to_string_def] >>
  qpat_x_assum `ce.ce_func_info = _` (fn th =>
    qpat_x_assum `ce.ce_func_info name = _` (mp_tac o REWRITE_RULE [th])) >>
  simp[]
QED

Theorem body_internal_return_physical:
  body_inv tops ctx ce cx /\
  MEM (FunctionDecl Internal mut F rr name args [] ret ss) tops /\
  expr_body_pre ce cx env (Call ann (IntCall (NONE,name)) es dflt) es0 ==>
  arg_type_fits ret ann /\
  ?tv. evaluate_type (get_tenv cx) ret = SOME tv
Proof
  strip_tac >>
  drule_all bodyIntCallAssemblyTheory.body_internal_decl_return_type >>
  strip_tac >> drule ifexp_body_pre_intcall_physical >>
  simp[lowered_value_type_def]
QED

Theorem body_internal_return_buffer_size:
  body_inv tops ctx ce cx /\
  MEM (FunctionDecl Internal mut nr rr name args dflts ret ss) tops /\
  ce.ce_func_info (nsid_to_string (NONE,name)) = (0,rbs,pvs) /\
  ret <> NoneT /\ expr_sim_inv ce cx env es0 /\
  evaluate_type (get_tenv cx) ret = SOME tv ==>
  rbs = type_memory_size tv
Proof
  strip_tac >> drule_all body_internal_decl_info >> strip_tac >>
  `type_memory_bytes ce ret = type_memory_size tv` by
    (irule typedMemoryCopyTheory.typed_copy_memory_size >>
     fs[expr_sim_inv_def] >> metis_tac[listTheory.EVERY_MONOTONIC]) >>
  Cases_on `ret` >>
  gvs[compute_func_info_def, entryStateRelTheory.type_mem_bytes_type_memory_bytes]
QED

Theorem arg_type_fits_memory_bytes_mono:
  (!t u. arg_type_fits t u ==>
     type_memory_bytes ce t <= type_memory_bytes ce u) /\
  (!ts us. arg_types_fit ts us ==>
     SUM (MAP (type_memory_bytes ce) ts) <=
     SUM (MAP (type_memory_bytes ce) us))
Proof
  ho_match_mp_tac arg_type_fits_ind >>
  simp[type_memory_bytes_def] >> rpt strip_tac >>
  gvs[arg_type_fits_def, type_memory_bytes_def]
  >- (irule arithmeticTheory.DIV_LE_MONOTONE >> simp[])
  >- (irule arithmeticTheory.DIV_LE_MONOTONE >> simp[])
  >- (irule arithmeticTheory.LESS_MONO_MULT2 >> simp[]) >>
  metis_tac[]
QED

Theorem arg_type_fits_alloc_bound:
  arg_type_fits t u /\ type_alloc_ok ce u ==>
  type_memory_bytes ce t < 2 ** 64
Proof
  strip_tac >>
  `type_memory_bytes ce t <= type_memory_bytes ce u` by
    metis_tac[cj 1 arg_type_fits_memory_bytes_mono] >>
  Cases_on `is_word_type u`
  >- (drule abiBuiltinEncodeWordTheory.abi_builtin_encode_word_info >>
      strip_tac >> gvs[] >> decide_tac) >>
  fs[allocLimitsTheory.type_alloc_ok_def]
QED

Theorem body_internal_return_buffer_bound:
  body_inv tops ctx ce cx /\
  MEM (FunctionDecl Internal mut F rr name args [] ret ss) tops /\
  ce.ce_func_info (nsid_to_string (NONE,name)) = (0,rbs,pvs) /\
  ret <> NoneT /\
  expr_body_pre ce cx env (Call ann (IntCall (NONE,name)) es dflt) es0 ==>
  ?tv. evaluate_type (get_tenv cx) ret = SOME tv /\
       rbs = type_memory_size tv /\ rbs < dimword (:256)
Proof
  strip_tac >> drule_all body_internal_return_physical >> strip_tac >>
  `expr_sim_inv ce cx env es0` by fs[expr_body_pre_def] >>
  `rbs = type_memory_size tv` by
    (irule body_internal_return_buffer_size >> metis_tac[]) >>
  `type_memory_bytes ce ret = type_memory_size tv` by
    (irule typedMemoryCopyTheory.typed_copy_memory_size >>
     fs[expr_sim_inv_def] >> metis_tac[listTheory.EVERY_MONOTONIC]) >>
  `type_alloc_ok ce ann` by
    fs[expr_body_pre_def, allocLimitsTheory.alloc_limits_expr_def] >>
  drule_all arg_type_fits_alloc_bound >> strip_tac >>
  qexists_tac `tv` >> simp[wordsTheory.dimword_def] >> gvs[]
QED
