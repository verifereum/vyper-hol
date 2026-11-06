Theory bodyPtrPopCalleeExclusion
Ancestors
  bodyPtrPopCalleeCandidate bodyPtrPopStoreContainment bodyPtrPopCallContainment fragExec venomInst
  bodyPtrPopIndexDecomposition bodyPtrPopGuardNormalization exprLoweringProps
  exprLowering exprCallBounds compileEnv context vyperAST vyperValue list

Theorem pop_callee_opcode_separation:
  EVERY (\fn.
    EVERY (\i. i.inst_opcode <> INVOKE) (fn_insts fn) \/
    EVERY (\i. i.inst_opcode <> SSTORE) (fn_insts fn))
    pop_callee_unit.cu_context.ctx_functions
Proof
  EVAL_TAC >> simp[SF wordsLib.SIZES_ss, type_slot_size_def] >> EVAL_TAC
QED

Theorem pop_callee_call_guard:
  expr_child_callback (base_assignment_target_size pop_callee_target + 259)
    compile_expr pop_callee_cenv pop_callee_word pop_callee_index sc =
  compile_call compile_expr pop_callee_cenv pop_callee_word pop_callee_word
    (IntCall (NONE,"shorten")) [] NONE sc
Proof
  simp[expr_child_callback_def, pop_callee_target_def, pop_callee_index_def,
       pop_callee_word_def] >>
  simp[Once compile_expr_def] >>
  simp[expr_type_def, compile_call_def, compile_multi_vvs_def]
QED

Theorem pop_callee_call_decomposition:
  !ret_ty sa vv sb.
    compile_expr pop_callee_cenv ret_ty
      (Pop pop_callee_word pop_callee_target) sa = (vv,sb) ==>
    ?sc sd cv.
      cs_extends sa sc /\
      compile_call compile_expr pop_callee_cenv pop_callee_word pop_callee_word
        (IntCall (NONE,"shorten")) [] NONE sc = (cv,sd) /\
      cs_extends sc sd /\ cs_extends sd sb
Proof
  rpt gen_tac >>
  `type_size pop_callee_word + 1 = 259` by EVAL_TAC >>
  simp[Once compile_expr_def] >>
  pairarg_tac >> simp[] >> pairarg_tac >> simp[] >>
  strip_tac >> gvs[] >>
  `!ce ty e s. ci_mono s
     (SND (expr_child_callback
       (base_assignment_target_size pop_callee_target + 259)
       compile_expr ce ty e s))` by
    (irule ci_mono_expr_child_callback >>
     simp[cj 1 compile_expr_ci_mono]) >>
  qpat_x_assum `compile_get_target_ptr _ _ _ _ = _` mp_tac >>
  pure_rewrite_tac[pop_callee_target_def] >> strip_tac >>
  qpat_x_assum `!ce ty e s. _`
    (assume_tac o PURE_REWRITE_RULE [pop_callee_target_def]) >>
  drule_all pop_subscript_index_decomposition >> strip_tac >>
  `expr_type pop_callee_index = pop_callee_word` by EVAL_TAC >>
  qpat_x_assum `expr_type pop_callee_index = _` (fn th =>
    rule_assum_tac (PURE_REWRITE_RULE
      [GSYM pop_callee_target_def, th, pop_callee_call_guard])) >>
  `ci_mono st1 sb` by
    metis_tac[ci_mono_compile_dynarray_pop, pairTheory.SND] >>
  qexistsl_tac [`sc`,`sd`,`cv`] >>
  gvs[ci_mono_def] >> metis_tac[cs_extends_trans]
QED

Theorem pop_callee_root_descriptor:
  FLOOKUP pop_callee_cenv.ce_module_vars (NONE,"b") = SOME (StorageLoc 0w) /\
  pop_callee_cenv.ce_hashmap_info (NONE,"b") = NONE /\
  pop_callee_cenv.ce_module_var_type (NONE,"b") = SOME pop_callee_root_type
Proof
  EVAL_TAC
QED

Theorem pop_callee_target_location:
  !cfn sa out sb.
    compile_get_target_ptr cfn pop_callee_cenv pop_callee_target sa = (out,sb) ==>
    FST (SND out) = SOME LocStorage
Proof
  rpt gen_tac >>
  simp[pop_callee_target_def, compile_get_target_ptr_def,
       pop_callee_root_descriptor, pop_callee_root_type_def,
       pop_callee_middle_def, comp_bind_def, comp_return_def] >>
  rpt (pairarg_tac >> gvs[comp_bind_def, comp_return_def]) >>
  strip_tac >> gvs[]
QED

Theorem pop_callee_fn_store:
  !ret_ty sa vv sb fn.
    compile_expr pop_callee_cenv ret_ty
      (Pop pop_callee_word pop_callee_target) sa = (vv,sb) /\
    fn_has_code sa sb fn ==>
    ?i. MEM i (fn_insts fn) /\ i.inst_opcode = SSTORE
Proof
  rpt gen_tac >>
  `type_size pop_callee_word + 1 = 259` by EVAL_TAC >>
  simp[Once compile_expr_def] >>
  pairarg_tac >> simp[] >> pairarg_tac >> simp[] >>
  strip_tac >> gvs[] >>
  drule pop_callee_target_location >> simp[] >> strip_tac >> gvs[] >>
  `!ce ty e s. ci_mono s
     (SND (expr_child_callback
       (base_assignment_target_size pop_callee_target + 259)
       compile_expr ce ty e s))` by
    (irule ci_mono_expr_child_callback >>
     simp[cj 1 compile_expr_ci_mono]) >>
  `ci_mono sa st1` by
    (drule ci_mono_compile_get_target_ptr_cfn >>
     disch_then (qspecl_then [`pop_callee_target`,`pop_callee_cenv`,`sa`] mp_tac) >>
     simp[]) >>
  `ci_mono st1 sb` by
    metis_tac[ci_mono_compile_dynarray_pop, pairTheory.SND] >>
  `fn_has_code st1 sb fn` by
    (gvs[ci_mono_def] >> metis_tac[fn_has_code_mid, cs_extends_refl]) >>
  drule_all pop_compile_storage_pop_fn_store >> simp[]
QED

Theorem pop_callee_no_containment:
  !ret_ty sa vv sb name fn.
    compile_expr pop_callee_cenv ret_ty
      (Pop pop_callee_word pop_callee_target) sa = (vv,sb) /\
    venomInst$lookup_function name pop_callee_unit.cu_context.ctx_functions = SOME fn ==>
    ~fn_has_code sa sb fn
Proof
  rpt strip_tac >>
  drule pop_callee_call_decomposition >> strip_tac >>
  `fn_has_code sc sd fn` by metis_tac[fn_has_code_mid] >>
  drule_all pop_compile_intcall_fn_invoke >> strip_tac >>
  drule_all pop_callee_fn_store >> strip_tac >>
  drule venomInstTheory.lookup_function_MEM >> strip_tac >>
  mp_tac pop_callee_opcode_separation >> simp[EVERY_MEM, EXISTS_MEM] >>
  metis_tac[]
QED
