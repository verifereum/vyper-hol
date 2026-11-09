(* The entry of the lowered runtime unit up to the selected external
   function's entry checks: from the initial state, the selector dispatch
   reaches the start of compile_entry_checks for the function the source
   selects (external_entry_reaches_checks), for the s1-entry-return
   pieces. *)
Theory externalEntryChecks
Ancestors
  externalEntryShape
  stmtSimProps stmtSimDefs exprSimDefs loweringPosts
  list pair fragExec bodySim bodySimMain loweringHalt stmtLoweringMono
  exprLoweringProps compileEnv compileVyper moduleLowering stmtLowering
  e2eDefs supportedProgram vyperLoweringCorrect rawReturnHeader
  entryChecksProps moduleLoweringProps entryDispatchProps supportedNames
  abiDecoderCounters context supportedDecls supportedExprForms
  supportedStmts
  vyperTypeSelectedEntrySoundness vyperTypeSystem
  vyperInterpreter vyperState vyperContext
  venomState venomExecSemantics venomWf
Libs
  monadsyntax

val () = enable_monad "compilation";
val () = enable_monadsyntax ();
val _ = Parse.hide "body";

Theorem supported_entry_no_getters:
  supported_program tops ==>
  (!nr mut ty x name. ~MEM (VariableDecl (Public nr) mut name ty x) tops) /\
  (!nr b kt vt x name. ~MEM (HashMapDecl (Public nr) b name kt vt x) tops)
Proof
  simp[supported_program_def, supported_declaration_headers_def,
       EVERY_MEM] >> rpt strip_tac >>
  qpat_x_assum `!e. MEM e tops ==> supported_declaration_header tops e`
    drule >> simp[supported_declaration_header_def]
QED

Theorem selected_external_dispatch:
  supported_program tops /\ valid_vyper_call tops tx cd ret /\
  lookup_function NONE tx.function_name External tops =
    SOME (mut, F, args, [], ret, fbody) ==>
  (?rr. MEM (mut, F, rr, tx.function_name, args, [], ret, fbody)
          (FST (classify_functions tops))) /\
  (!fb. linear_dispatch_target cd
    (MAP (\(sel, lbl, _). (sel, lbl))
      (build_selectors (type_env tops) (FST (classify_functions tops)))) fb =
    "fn_" ++ tx.function_name)
Proof
  strip_tac >>
  drule supported_entry_no_getters >> strip_tac >>
  gvs[valid_vyper_call_def] >> conj_tac
  >- (irule lookup_function_external_mem >> simp[] >>
      qexists_tac `NONE` >> simp[]) >>
  gen_tac >>
  `ALL_DISTINCT (MAP FST (build_selectors (type_env tops)
     (FST (classify_functions tops))))` by
    gvs[supported_program_def, supported_declaration_names_def,
        supported_selectors_distinct_def] >>
  drule linear_dispatch_selects_function >> simp[] >>
  disch_then (qspec_then `tx.args` mp_tac) >> simp[]
QED

Theorem compile_decode_args_vars_mono:
  !args cenv offset opc hi base.
    abi_decoder_vars_mono (compile_decode_args cenv args offset opc hi base)
Proof
  Induct >> simp[compile_decode_args_def, abi_decoder_vars_mono_return] >>
  gen_tac >> PairCases_on `h` >> rpt gen_tac >>
  Cases_on `h1`
  >- (simp[compile_decode_args_def, LET_THM] >>
      ho_match_mp_tac abi_decoder_vars_mono_bind >> conj_tac
      >- simp[abi_decoder_vars_mono_prims] >>
      gen_tac >> ho_match_mp_tac abi_decoder_vars_mono_bind >> conj_tac
      >- simp[abi_decoder_vars_mono_prims] >>
      gen_tac >> ho_match_mp_tac abi_decoder_vars_mono_ignore_bind >> conj_tac
      >- simp[abi_decoder_vars_mono_abi_clamp] >>
      ho_match_mp_tac abi_decoder_vars_mono_ignore_bind >> conj_tac
      >- (Cases_on `FLOOKUP cenv.ce_vars h0` >>
          simp[abi_decoder_vars_mono_return] >>
          Cases_on `var_location_decode_operand x` >>
          simp[abi_decoder_vars_mono_return, abi_decoder_vars_mono_prims]) >>
      simp[]) >>
  Cases_on `h2` >> simp[compile_decode_args_def] >>
  Cases_on `FLOOKUP cenv.ce_vars h0` >> simp[] >>
  Cases_on `var_location_decode_operand x` >> simp[]
  >- (ntac 3 (ho_match_mp_tac abi_decoder_vars_mono_bind >> conj_tac
              >- simp[abi_decoder_vars_mono_prims] >> gen_tac) >>
      ho_match_mp_tac abi_decoder_vars_mono_ignore_bind >>
      simp[abi_decoder_vars_mono_mutual]) >>
  ho_match_mp_tac abi_decoder_vars_mono_bind >> conj_tac
  >- simp[abi_decoder_vars_mono_prims] >>
  gen_tac >> ho_match_mp_tac abi_decoder_vars_mono_ignore_bind >>
  simp[abi_decoder_vars_mono_mutual]
QED

Theorem compile_register_positional_args_vars_mono:
  !args cenv offset.
    abi_decoder_vars_mono (compile_register_positional_args cenv args offset)
Proof
  Induct >> simp[compile_register_positional_args_def,
                 abi_decoder_vars_mono_return] >>
  gen_tac >> PairCases_on `h` >> rpt gen_tac >>
  simp[compile_register_positional_args_def] >>
  Cases_on `FLOOKUP cenv.ce_vars h0` >> simp[] >>
  Cases_on `var_location_memory_size x` >> simp[] >>
  ho_match_mp_tac abi_decoder_vars_mono_bind >> conj_tac
  >- simp[abi_decoder_vars_mono_abi_alloc_buffer] >>
  gen_tac >> ho_match_mp_tac abi_decoder_vars_mono_bind >> conj_tac
  >- simp[abi_decoder_vars_mono_return] >>
  gen_tac >> ho_match_mp_tac abi_decoder_vars_mono_ignore_bind >>
  simp[compile_decode_args_vars_mono]
QED

Theorem compile_register_positional_args_next_var:
  compile_register_positional_args cenv args offset sa = (ce, sb) ==>
  sa.cs_next_var <= sb.cs_next_var
Proof
  strip_tac >>
  mp_tac (Q.SPECL [`args`, `cenv`, `offset`]
    compile_register_positional_args_vars_mono) >>
  simp[abi_decoder_vars_mono_def] >>
  disch_then (qspec_then `sa` mp_tac) >> simp[]
QED

Theorem compile_stmts_vars_mono:
  abi_decoder_vars_mono (compile_stmts ce lc ty ss)
Proof
  mp_tac compile_stmt_cs_mono >>
  simp[cs_mono_def, abi_decoder_vars_mono_def] >>
  rpt strip_tac >>
  Cases_on `compile_stmts ce lc ty ss st` >>
  rename1 `_ = (u, sb)` >> Cases_on `u` >>
  first_x_assum drule >> simp[]
QED

Theorem compile_entry_checks_vars_mono:
  abi_decoder_vars_mono (compile_entry_checks min_cds payable)
Proof
  Cases_on `payable` >> Cases_on `min_cds > 4` >>
  simp[compile_entry_checks_def, abi_decoder_vars_mono_return] >>
  rpt (FIRST [
    CHANGED_TAC (simp[abi_decoder_vars_mono_prims,
      abi_decoder_vars_mono_return]),
    (ho_match_mp_tac abi_decoder_vars_mono_bind >> conj_tac),
    (ho_match_mp_tac abi_decoder_vars_mono_ignore_bind >> conj_tac),
    gen_tac])
QED

Theorem compile_nonreentrant_vars_mono:
  abi_decoder_vars_mono (compile_nonreentrant_lock key transient view) /\
  abi_decoder_vars_mono (compile_nonreentrant_unlock key transient view)
Proof
  Cases_on `transient` >> Cases_on `view` >>
  simp[compile_nonreentrant_lock_def, compile_nonreentrant_unlock_def,
    abi_decoder_vars_mono_prims, abi_decoder_vars_mono_return] >>
  rpt (FIRST [
    CHANGED_TAC (simp[abi_decoder_vars_mono_prims,
      abi_decoder_vars_mono_return]),
    (ho_match_mp_tac abi_decoder_vars_mono_bind >> conj_tac),
    (ho_match_mp_tac abi_decoder_vars_mono_ignore_bind >> conj_tac),
    gen_tac])
QED

Theorem comp_get_vars_mono:
  abi_decoder_vars_mono comp_get
Proof
  simp[abi_decoder_vars_mono_def, comp_get_def]
QED

Theorem compile_guarded_body_vars_mono:
  abi_decoder_vars_mono (compile_guarded_body ce nr key transient view body rt)
Proof
  Cases_on `nr` >> Cases_on `rt` >>
  simp[compile_guarded_body_def] >>
  rpt (FIRST [
    CHANGED_TAC (simp[abi_decoder_vars_mono_prims,
      abi_decoder_vars_mono_return, compile_nonreentrant_vars_mono,
      compile_stmts_vars_mono, comp_get_vars_mono]),
    (ho_match_mp_tac abi_decoder_vars_mono_bind >> conj_tac),
    (ho_match_mp_tac abi_decoder_vars_mono_ignore_bind >> conj_tac),
    gen_tac,
    (IF_CASES_TAC >> simp[])])
QED

Theorem compile_external_function_body_vars_mono:
  abi_decoder_vars_mono
    (compile_external_function_body ce args nr key transient view body rt)
Proof
  rewrite_tac[compile_external_function_body_def] >>
  ho_match_mp_tac abi_decoder_vars_mono_bind >>
  simp[compile_register_positional_args_vars_mono,
       compile_guarded_body_vars_mono]
QED

Theorem compile_entry_checks_next_var:
  compile_entry_checks min_cds payable sa = ((), sb) ==>
  sa.cs_next_var <= sb.cs_next_var
Proof
  strip_tac >>
  mp_tac compile_entry_checks_vars_mono >>
  simp[abi_decoder_vars_mono_def] >>
  disch_then (qspec_then `sa` mp_tac) >> simp[]
QED

Theorem compile_external_function_body_next_var:
  compile_external_function_body ce args nr key transient view body rt sa =
    ((), sb) ==> sa.cs_next_var <= sb.cs_next_var
Proof
  strip_tac >>
  mp_tac compile_external_function_body_vars_mono >>
  simp[abi_decoder_vars_mono_def] >>
  disch_then (qspec_then `sa` mp_tac) >> simp[]
QED

Theorem external_checks_occurrence:
  !packages lbl ce args min_cds pay nr key ut iv body rt sd sf.
    MEM (lbl,ce,args,min_cds,pay,nr,key,ut,iv,body,rt) packages /\
    compile_external_fn_bodies packages sd = ((),sf) ==>
    ?pre post sa st st' sb.
      packages = pre ++ (lbl,ce,args,min_cds,pay,nr,key,ut,iv,body,rt)::post /\
      compile_external_fn_bodies pre sd = ((),sa) /\
      new_block lbl sa = (sa.cs_current_bb,st) /\
      compile_entry_checks min_cds pay st = ((),st') /\
      compile_external_function_body ce args nr key ut iv body rt st' = ((),sb) /\
      compile_external_fn_bodies post sb = ((),sf) /\
      st.cs_current_bb = lbl /\ st.cs_current_insts = [] /\
      sd.cs_next_var <= st.cs_next_var
Proof
  Induct >> simp[MEM] >>
  gen_tac >> PairCases_on `h` >> rpt gen_tac >> strip_tac >>
  qpat_x_assum `compile_external_fn_bodies _ _ = _` mp_tac >>
  simp_tac std_ss [compile_external_fn_bodies_def, comp_ignore_bind_def,
                   comp_bind_def] >>
  Cases_on `new_block h0 sd` >>
  rename1 `new_block h0 sd = (old,s1)` >> simp[] >>
  Cases_on `compile_entry_checks h3 h4 s1` >>
  rename1 `compile_entry_checks h3 h4 s1 = (u,s2)` >>
  Cases_on `u` >> simp[] >>
  Cases_on `compile_external_function_body h1 h2 h5 h6 h7 h8 h9 h10 s2` >>
  rename1 `compile_external_function_body _ _ _ _ _ _ _ _ _ = (u,s3)` >>
  Cases_on `u` >> simp[] >> strip_tac
  >- (gvs[] >>
      qexistsl_tac [`[]`, `packages`, `sd`, `s1`, `s2`, `s3`] >>
      gvs[compile_external_fn_bodies_def, comp_return_def, new_block_def,
          LET_THM]) >>
  first_x_assum drule >> disch_then drule >> strip_tac >>
  `sd.cs_next_var = s1.cs_next_var` by gvs[new_block_def, LET_THM] >>
  `s1.cs_next_var <= s2.cs_next_var` by
    (rev_drule compile_entry_checks_next_var >> simp[]) >>
  `s2.cs_next_var <= s3.cs_next_var` by
    (rev_drule compile_external_function_body_next_var >> simp[]) >>
  qexistsl_tac [`(h0,h1,h2,h3,h4,h5,h6,h7,h8,h9,h10)::pre`,
                 `post`, `sa`, `st`, `st'`, `sb`] >>
  simp[compile_external_fn_bodies_def, comp_ignore_bind_def, comp_bind_def] >>
  decide_tac
QED

Theorem compile_entry_checks_same_blocks:
  compile_entry_checks min_cds pay st = ((),st') ==>
  same_blocks st st'
Proof
  Cases_on `pay` >> Cases_on `4 < min_cds` >>
  simp[compile_entry_checks_def, comp_bind_def, comp_ignore_bind_def,
       comp_return_def, emitHelperTheory.emit_op_def, emitHelperTheory.emit_void_def, fresh_id_def,
       fresh_var_def, emit_def, same_blocks_def] >>
  strip_tac >> gvs[]
QED

Theorem external_checks_unshadowed:
  !pre post lbl ce args min_cds pay nr key ut iv body rt sd sa st st'.
    EVERY external_fn_shape_ok
      (pre ++ (lbl,ce,args,min_cds,pay,nr,key,ut,iv,body,rt)::post) /\
    ALL_DISTINCT (MAP FST
      (pre ++ (lbl,ce,args,min_cds,pay,nr,key,ut,iv,body,rt)::post)) /\
    shape_state sd /\ ~compiler_label lbl /\
    ~MEM lbl (MAP (\bb. bb.bb_label) (all_blocks sd)) /\
    compile_external_fn_bodies pre sd = ((),sa) /\
    new_block lbl sa = (sa.cs_current_bb,st) /\
    compile_entry_checks min_cds pay st = ((),st') ==>
    ~MEM lbl (MAP (\bb. bb.bb_label) (REVERSE st.cs_blocks)) /\
    !se func. cs_extends st' se /\ func.fn_blocks = all_blocks se ==>
      fn_has_code st st' func
Proof
  rpt gen_tac >> strip_tac >>
  `EVERY external_fn_shape_ok pre /\ ~MEM lbl (MAP FST pre)` by
    (gvs[EVERY_APPEND, ALL_DISTINCT_APPEND] >> metis_tac[]) >>
  drule_all externalEntryShapeTheory.compile_external_fn_bodies_label_absent >> strip_tac >>
  `st.cs_current_bb = lbl /\
   ~MEM lbl (MAP (\bb. bb.bb_label) (REVERSE st.cs_blocks))` by
    gvs[new_block_def, loweringShapeDefsTheory.all_blocks_def, LET_THM] >>
  conj_tac >- simp[] >>
  rpt gen_tac >> strip_tac >>
  drule compile_entry_checks_same_blocks >>
  rewrite_tac[same_blocks_def] >> strip_tac >>
  simp[fn_has_code_def, emitted_blocks_def] >>
  drule externalEntryShapeTheory.cs_extends_open_lookup >> simp[]
QED

Theorem selected_external_package:
  !tops target mut rr name args ret fbody.
  ?cenv pos_args min_cds is_payable nkey ut iv rt.
    set_external_package_target target
      (package_external_fn tops F (assign_nkeys tops 0)
        (mut, F, rr, name, args, ([] : expr list), ret, fbody)) =
    ("fn_" ++ name, cenv, pos_args, min_cds, is_payable, F,
     nkey, ut, iv, fbody, rt)
Proof
  rpt gen_tac >>
  simp[package_external_fn_def, set_external_package_target_def, LET_THM]
QED

(* ADMITTED (#639): the run from __entry reaches the start st of the entry
   checks of the function the source selects: run_context starts the entry
   function func at its first block, compile_selector_dispatch_linear_correct
   brings it to "fn_" ++ tx.function_name (linear_dispatch_selects_function,
   supported_program giving distinct selectors), and
   compile_external_fn_bodies opens that label's block with the entry
   checks.  Only variables and the position change
   on the way, and every result from s0 is a result of run_context. *)
Theorem linear_dispatch_prefix_code:
  !selectors fallback sa sd se func.
    fresh_label "fallback" (initial_compile_state "__entry") = (fallback, sa) /\
    compile_selector_dispatch_linear selectors fallback sa = ((), sd) /\
    cs_extends sd se /\ func.fn_blocks = all_blocks se ==>
    ALL_DISTINCT (MAP (\bb. bb.bb_label) (all_blocks sd)) /\
    (!l. l IN bound_labels sd ==> ~isPREFIX "fn_" l) /\
    fn_has_code sa sd func
Proof
  rpt gen_tac >> strip_tac >>
  `compile_state_ok (initial_compile_state "__entry")` by
    (irule compile_state_ok_initial >>
     simp[compiler_labels_future_def, fresh_label_output_def]) >>
  drule_all emitHelperPropsTheory.fresh_label_produces_external >> strip_tac >>
  `compile_state_ok sd` by
    (drule_all compile_selector_dispatch_linear_state_ok >> simp[]) >>
  conj_tac
  >- (irule externalEntryShapeTheory.compile_state_ok_all_blocks_distinct >> simp[]) >>
  conj_tac
  >- (gen_tac >> strip_tac >>
      drule compile_selector_dispatch_linear_no_fn_labels >>
      disch_then irule >> simp[] >>
      simp_tac std_ss [vyperCompilerTheory.initial_compile_state_def, bound_labels_def,
                       pred_setTheory.IN_INSERT, pred_setTheory.NOT_IN_EMPTY] >>
      rpt strip_tac >> gvs[] >> EVAL_TAC) >>
  irule externalEntryShapeTheory.cs_extends_fn_has_code >> simp[] >>
  goal_assum (drule_at Any) >> simp[]
QED

Theorem linear_dispatch_shape:
  !selectors fallback sa sd.
    EVERY (\(sel,lbl). jump_label_ok lbl) selectors /\
    fresh_label "fallback" (initial_compile_state "__entry") = (fallback,sa) /\
    compile_selector_dispatch_linear selectors fallback sa = ((),sd) ==>
    shape_state sd /\ cs_extends sa sd /\ jump_label_ok fallback /\
    EVERY (\l. ~internal_label_ok l) (added_labels sa sd)
Proof
  rpt gen_tac >> strip_tac >>
  `shape_state (initial_compile_state "__entry")` by
    simp[loweringShapePropsTheory.shape_state_initial_compile_state] >>
  mp_tac (Q.SPECL [`F`, `jump_label_ok`, `\st. T`, `"fallback"`]
    loweringShapeRulesTheory.shape_step_fresh_label_sfx) >>
  simp[loweringShapeDefsTheory.shape_stable_def,
       loweringShapeDefsTheory.shape_step_def] >>
  disch_then drule_all >> strip_tac >>
  `jump_label_ok fallback` by simp[loweringShapeDefsTheory.jump_label_ok_def] >>
  `~label_sfx "dispatch" fallback` by
    (`"fallback" <> "dispatch"` by simp[] >>
     metis_tac[loweringShapeRulesTheory.label_sfx_distinct]) >>
  drule_all loweringShapePropsTheory.compile_selector_dispatch_linear_shape >>
  rewrite_tac[loweringShapeDefsTheory.shape_step_def] >>
  disch_then drule_all >>
  simp[loweringShapeDefsTheory.shape_extends_def]
QED

Theorem run_lowering_entry_function:
  !selectors external_fns internal_fns fallback_fn rpolicy buckets metadata dense info unit.
    run_lowering selectors external_fns internal_fns fallback_fn rpolicy
      buckets metadata dense info "__entry" = SOME unit /\
    EVERY (\(sel,lbl,z). isPREFIX "fn_" lbl) selectors /\
    EVERY external_fn_shape_ok external_fns /\ fallback_shape_ok fallback_fn /\
    EVERY internal_fn_shape_ok internal_fns /\
    EVERY (\d. internal_label_ok (FST d)) (internal_fn_descriptors internal_fns) /\
    ALL_DISTINCT (MAP FST (internal_fn_descriptors internal_fns)) ==>
    ?se func.
      (do fb <- fresh_label "fallback";
          compile_selector_dispatch_linear (MAP (\(sel,lbl,z). (sel,lbl)) selectors) fb;
          compile_external_fn_bodies external_fns;
          new_block fb;
          (case fallback_fn of
             NONE => emit_inst REVERT [Lit 0w; Lit 0w] []
           | SOME (ce,pay,nr,key,ut,iv,body,rt) =>
               compile_fallback_body ce pay nr key ut iv body rt)
       od) (initial_compile_state "__entry") = ((),se) /\
      unit.cu_context.ctx_entry = SOME "__entry" /\
      venomInst$lookup_function "__entry" unit.cu_context.ctx_functions = SOME func /\
      func.fn_blocks = all_blocks se /\
      func.fn_blocks <> [] /\ (HD func.fn_blocks).bb_label = "__entry"
Proof
  rpt gen_tac >> strip_tac >>
  `lowering_policy_ok rpolicy` by
    (qpat_x_assum `run_lowering _ _ _ _ _ _ _ _ _ _ = _` mp_tac >>
     rw[vyperCompilerTheory.run_lowering_def]) >>
  `rpolicy.rpol_frontend_dispatch = Linear` by
    fs[vyperCompilerTheory.lowering_policy_ok_def] >>
  Cases_on `compile_generate_runtime selectors external_fns internal_fns fallback_fn
    Linear buckets metadata dense info (initial_compile_state "__entry")` >>
  rename1 `_ = (u,sf)` >> Cases_on `u` >>
  drule_all compile_generate_runtime_entry_shape >> strip_tac >>
  `?fs. package_internal_blocks (internal_fn_descriptors internal_fns)
     (entry_blocks ++ FLAT segs) = SOME (entry_blocks,fs)` by
    (irule_at Any loweringShapePropsTheory.package_internal_blocks_segments >> simp[] >>
     rewrite_tac[EVERY_MEM] >> rpt strip_tac >> BETA_TAC >>
     irule loweringShapePropsTheory.internal_name_not_entry_label >>
     gvs[EVERY_MEM]) >>
  qexistsl_tac [`entry_st`, `mk_raw_function "__entry" entry_blocks`] >>
  simp[] >>
  qpat_x_assum `run_lowering _ _ _ _ _ _ _ _ _ _ = _` mp_tac >>
  gvs[vyperCompilerTheory.run_lowering_def,
      vyperCompilerTheory.extract_context_with_internals_def,
      loweringShapeDefsTheory.all_blocks_def,
      venomInstTheory.mk_venom_context_def, venomInstTheory.mk_raw_function_def,
      venomInstTheory.lookup_function_def, FIND_thm] >>
  strip_tac >> gvs[FIND_thm]
QED

Theorem external_checks_suffix_extends:
  !pre post lbl ce args min_cds pay nr key ut iv fbody rt sd sa st st' sb sx.
    EVERY external_fn_shape_ok
      (pre ++ (lbl,ce,args,min_cds,pay,nr,key,ut,iv,fbody,rt)::post) /\
    shape_state sd /\
    compile_external_fn_bodies pre sd = ((),sa) /\
    new_block lbl sa = (sa.cs_current_bb,st) /\
    compile_entry_checks min_cds pay st = ((),st') /\
    compile_external_function_body ce args nr key ut iv fbody rt st' = ((),sb) /\
    compile_external_fn_bodies post sb = ((),sx) ==>
    cs_extends st' sx
Proof
  rpt gen_tac >> strip_tac >>
  `EVERY external_fn_shape_ok pre /\ EVERY external_fn_shape_ok post /\
   cenv_static_ok ce /\ ce.ce_return_pc = NONE /\
   ~supported_stmts_expr_exists expr_shape_root fbody` by
    gvs[EVERY_APPEND, loweringShapePropsTheory.external_fn_shape_ok_def] >>
  `shape_state sa` by
    (qspec_then `pre` mp_tac loweringShapePropsTheory.compile_external_fn_bodies_shape >>
     (impl_tac >- simp[]) >>
     rewrite_tac[loweringShapeDefsTheory.shape_step_def] >>
     disch_then drule_all >> simp[]) >>
  `shape_state st` by
    (drule_all loweringShapePropsTheory.shape_state_new_block >> simp[]) >>
  `shape_state st'` by
    (mp_tac loweringShapePropsTheory.compile_entry_checks_shape >>
     rewrite_tac[loweringShapeDefsTheory.shape_step_def] >>
     disch_then drule_all >> simp[]) >>
  `shape_state sb /\ cs_extends st' sb` by
    (drule_all loweringShapePropsTheory.compile_external_function_body_shape >>
     rewrite_tac[loweringShapeDefsTheory.shape_step_def] >>
     disch_then drule_all >> simp[loweringShapeDefsTheory.shape_extends_def]) >>
  `cs_extends sb sx` by
    (drule_all loweringShapePropsTheory.compile_external_fn_bodies_shape >>
     rewrite_tac[loweringShapeDefsTheory.shape_step_def] >>
     disch_then drule_all >> simp[loweringShapeDefsTheory.shape_extends_def]) >>
  irule cs_extends_trans >> goal_assum (drule_at Any) >> simp[]
QED

Theorem runtime_entry_dispatch_code:
  !selectors packages fallback_fn se func.
    EVERY (\(sel,lbl). jump_label_ok lbl) selectors /\
    EVERY external_fn_shape_ok packages /\ fallback_shape_ok fallback_fn /\
    (do fb <- fresh_label "fallback";
        compile_selector_dispatch_linear selectors fb;
        compile_external_fn_bodies packages;
        new_block fb;
        (case fallback_fn of
           NONE => emit_inst REVERT [Lit 0w; Lit 0w] []
         | SOME (ce,pay,nr,key,ut,iv,fbody,rt) =>
             compile_fallback_body ce pay nr key ut iv fbody rt)
     od) (initial_compile_state "__entry") = ((),se) /\
    func.fn_blocks = all_blocks se ==>
    ?fb sa sd sx.
      fresh_label "fallback" (initial_compile_state "__entry") = (fb,sa) /\
      compile_selector_dispatch_linear selectors fb sa = ((),sd) /\
      compile_external_fn_bodies packages sd = ((),sx) /\
      shape_state sd /\ cs_extends sd se /\ cs_extends sx se /\
      (!l. l IN bound_labels sd ==> ~isPREFIX "fn_" l) /\
      fn_has_code sa sd func
Proof
  rpt gen_tac >> strip_tac >>
  Cases_on `fresh_label "fallback" (initial_compile_state "__entry")` >>
  rename1 `_ = (fb,sa)` >>
  Cases_on `compile_selector_dispatch_linear selectors fb sa` >>
  rename1 `_ = (u,sd)` >> Cases_on `u` >>
  Cases_on `compile_external_fn_bodies packages sd` >>
  rename1 `_ = (u,sx)` >> Cases_on `u` >>
  `shape_state sd /\ cs_extends sa sd /\ jump_label_ok fb` by
    (drule_all linear_dispatch_shape >> simp[]) >>
  `(do new_block fb;
      (case fallback_fn of
         NONE => emit_inst REVERT [Lit 0w; Lit 0w] []
       | SOME (ce,pay,nr,key,ut,iv,fbody,rt) =>
           compile_fallback_body ce pay nr key ut iv fbody rt)
    od) sx = ((),se)` by
    (qpat_x_assum `_ (initial_compile_state "__entry") = ((),se)` mp_tac >>
     simp[comp_bind_def, comp_ignore_bind_def]) >>
  `shape_state sx /\ cs_extends sd sx` by
    (drule_all loweringShapePropsTheory.compile_external_fn_bodies_shape >>
     rewrite_tac[loweringShapeDefsTheory.shape_step_def] >>
     disch_then drule_all >>
     simp[loweringShapeDefsTheory.shape_extends_def]) >>
  `cs_extends sx se` by
    (drule_all externalEntryShapeTheory.runtime_fallback_suffix_shape >>
     rewrite_tac[loweringShapeDefsTheory.shape_step_def] >>
     disch_then drule_all >>
     simp[loweringShapeDefsTheory.shape_extends_def]) >>
  `cs_extends sd se` by (irule cs_extends_trans >> goal_assum (drule_at Any) >> simp[]) >>
  drule_all linear_dispatch_prefix_code >> strip_tac >>
  qexistsl_tac [`fb`, `sa`, `sd`, `sx`] >> simp[]
QED

Theorem runtime_entry_dispatch_code_labels:
  !selectors packages fallback_fn se func.
    EVERY (\(sel,lbl). jump_label_ok lbl) selectors /\
    EVERY (\p. isPREFIX "fn_" (FST p)) packages /\
    (do fb <- fresh_label "fallback";
        compile_selector_dispatch_linear selectors fb;
        compile_external_fn_bodies packages;
        new_block fb;
        (case fallback_fn of
           NONE => emit_inst REVERT [Lit 0w; Lit 0w] []
         | SOME (ce,pay,nr,key,ut,iv,fbody,rt) =>
             compile_fallback_body ce pay nr key ut iv fbody rt)
     od) (initial_compile_state "__entry") = ((),se) /\
    func.fn_blocks = all_blocks se ==>
    ?fb sa sd sx.
      fresh_label "fallback" (initial_compile_state "__entry") = (fb,sa) /\
      compile_selector_dispatch_linear selectors fb sa = ((),sd) /\
      compile_external_fn_bodies packages sd = ((),sx) /\
      shape_state sd /\ cs_extends sd se /\ cs_extends sx se /\
      (!l. l IN bound_labels sd ==> ~isPREFIX "fn_" l) /\
      fn_has_code sa sd func /\
      EVERY (\l. ~internal_label_ok l)
        (MAP (\bb. bb.bb_label) (all_blocks se)) /\
      all_blocks se <> [] /\ (HD (all_blocks se)).bb_label = "__entry"
Proof
  rpt gen_tac >> strip_tac >>
  Cases_on `fresh_label "fallback" (initial_compile_state "__entry")` >>
  rename1 `_ = (fb,sa)` >>
  Cases_on `compile_selector_dispatch_linear selectors fb sa` >>
  rename1 `_ = (u,sd)` >> Cases_on `u` >>
  Cases_on `compile_external_fn_bodies packages sd` >>
  rename1 `_ = (u,sx)` >> Cases_on `u` >>
  `shape_state sd /\ cs_extends sa sd /\ jump_label_ok fb /\
   EVERY (\l. ~internal_label_ok l) (added_labels sa sd)` by
    (drule_all linear_dispatch_shape >> simp[]) >>
  `(do new_block fb;
      (case fallback_fn of
         NONE => emit_inst REVERT [Lit 0w; Lit 0w] []
       | SOME (ce,pay,nr,key,ut,iv,fbody,rt) =>
           compile_fallback_body ce pay nr key ut iv fbody rt)
    od) sx = ((),se)` by
    (qpat_x_assum `_ (initial_compile_state "__entry") = ((),se)` mp_tac >>
     simp[comp_bind_def, comp_ignore_bind_def]) >>
  `cs_extends sd sx /\
   EVERY (\l. ~internal_label_ok l) (added_labels sd sx)` by
    (qspecl_then [`packages`, `\l. ~internal_label_ok l`] mp_tac
       externalEntryShapeTheory.compile_external_fn_bodies_labels >>
     (impl_tac >-
       (conj_tac
        >- (simp_tac std_ss [EVERY_MEM] >> gen_tac >> disch_tac >>
            irule loweringShapeRulesTheory.jump_label_ok_not_internal >>
            simp_tac std_ss [loweringShapeDefsTheory.jump_label_ok_def] >>
            disj2_tac >> gvs[EVERY_MEM]) >>
        gen_tac >> disch_tac >> BETA_TAC >>
        Cases_on `l` >> gvs[loweringShapeDefsTheory.internal_label_ok_def])) >>
     disch_then (qspec_then `sd` mp_tac) >> simp[]) >>
  `cs_extends sx se /\
   EVERY (\l. ~internal_label_ok l) (added_labels sx se)` by
    (qspecl_then [`fb`, `fallback_fn`, `\l. ~internal_label_ok l`] mp_tac
       externalEntryShapeTheory.runtime_fallback_suffix_labels >>
     (impl_tac >-
       (conj_tac >- metis_tac[loweringShapeRulesTheory.jump_label_ok_not_internal] >>
        gen_tac >> disch_tac >> BETA_TAC >>
        Cases_on `l` >> gvs[loweringShapeDefsTheory.internal_label_ok_def])) >>
     disch_then (qspec_then `sx` mp_tac) >> simp[]) >>
  `cs_extends sd se` by (irule cs_extends_trans >> goal_assum (drule_at Any) >> simp[]) >>
  drule_all linear_dispatch_prefix_code >> strip_tac >>
  qexistsl_tac [`fb`, `sa`, `sd`, `sx`] >> simp[] >>
  `cs_extends sa se` by
    (irule cs_extends_trans >> goal_assum (drule_at Any) >> simp[]) >>
  conj_tac
  >- (qpat_assum `cs_extends sx se` (mp_tac o MATCH_MP externalEntryShapeTheory.cs_extends_labels) >>
      qpat_assum `cs_extends sd sx` (mp_tac o MATCH_MP externalEntryShapeTheory.cs_extends_labels) >>
      qpat_assum `cs_extends sa sd` (mp_tac o MATCH_MP externalEntryShapeTheory.cs_extends_labels) >>
      simp[] >> rpt disch_tac >>
      asm_rewrite_tac[EVERY_APPEND] >>
      gvs[fresh_label_def, vyperCompilerTheory.initial_compile_state_def,
          loweringShapeDefsTheory.all_blocks_def,
          loweringShapeDefsTheory.internal_label_ok_def]) >>
  drule externalEntryShapeTheory.cs_extends_block_stream_labels >> strip_tac >>
  gvs[fresh_label_def, vyperCompilerTheory.initial_compile_state_def,
      loweringShapeDefsTheory.all_blocks_def]
QED

Theorem run_lowering_entry_function_labels:
  !selectors external_fns internal_fns fallback_fn rpolicy buckets metadata dense info unit.
    run_lowering selectors external_fns internal_fns fallback_fn rpolicy
      buckets metadata dense info "__entry" = SOME unit /\
    EVERY (\(sel,lbl,z). isPREFIX "fn_" lbl) selectors /\
    EVERY (\p. isPREFIX "fn_" (FST p)) external_fns /\
    EVERY (\d. internal_label_ok (FST d)) (internal_fn_descriptors internal_fns) ==>
    ?se func.
      (do fb <- fresh_label "fallback";
          compile_selector_dispatch_linear (MAP (\(sel,lbl,z). (sel,lbl)) selectors) fb;
          compile_external_fn_bodies external_fns;
          new_block fb;
          (case fallback_fn of
             NONE => emit_inst REVERT [Lit 0w; Lit 0w] []
           | SOME (ce,pay,nr,key,ut,iv,fbody,rt) =>
               compile_fallback_body ce pay nr key ut iv fbody rt)
       od) (initial_compile_state "__entry") = ((),se) /\
      unit.cu_context.ctx_entry = SOME "__entry" /\
      venomInst$lookup_function "__entry" unit.cu_context.ctx_functions = SOME func /\
      func.fn_blocks = all_blocks se /\
      func.fn_blocks <> [] /\ (HD func.fn_blocks).bb_label = "__entry"
Proof
  rpt gen_tac >> strip_tac >>
  `lowering_policy_ok rpolicy` by
    (qpat_x_assum `run_lowering _ _ _ _ _ _ _ _ _ _ = _` mp_tac >>
     rw[vyperCompilerTheory.run_lowering_def]) >>
  `rpolicy.rpol_frontend_dispatch = Linear` by
    fs[vyperCompilerTheory.lowering_policy_ok_def] >>
  qabbrev_tac `prefix =
    do fb <- fresh_label "fallback";
       compile_selector_dispatch_linear (MAP (\(sel,lbl,z). (sel,lbl)) selectors) fb;
       compile_external_fn_bodies external_fns;
       new_block fb;
       (case fallback_fn of
          NONE => emit_inst REVERT [Lit 0w; Lit 0w] []
        | SOME (ce,pay,nr,key,ut,iv,fbody,rt) =>
            compile_fallback_body ce pay nr key ut iv fbody rt)
    od` >>
  Cases_on `prefix (initial_compile_state "__entry")` >>
  rename1 `_ = (u,se)` >> Cases_on `u` >>
  Cases_on `compile_internal_fn_bodies internal_fns se` >>
  rename1 `_ = (u,sf)` >> Cases_on `u` >>
  `compile_generate_runtime selectors external_fns internal_fns fallback_fn
     Linear buckets metadata dense info (initial_compile_state "__entry") = ((),sf)` by
    (`compile_generate_runtime selectors external_fns internal_fns fallback_fn
        Linear buckets metadata dense info =
      (do prefix; _ <- compile_internal_fn_bodies internal_fns; comp_return () od)` by
       simp[Abbr `prefix`, compile_generate_runtime_def,
            comp_ignore_bind_def, comp_bind_assoc] >>
     asm_rewrite_tac[] >>
     simp[comp_ignore_bind_def, comp_bind_def, comp_return_def]) >>
  `EVERY (\(sel,lbl). jump_label_ok lbl)
     (MAP (\(sel,lbl,z). (sel,lbl)) selectors)` by
    (gvs[EVERY_MAP, EVERY_MEM, FORALL_PROD,
         loweringShapeDefsTheory.jump_label_ok_def] >> metis_tac[]) >>
  `EVERY (\l. ~internal_label_ok l) (MAP (\bb. bb.bb_label) (all_blocks se)) /\
   all_blocks se <> [] /\ (HD (all_blocks se)).bb_label = "__entry"` by
    (qpat_assum `prefix _ = _` mp_tac >>
     simp_tac std_ss [Abbr `prefix`] >> disch_tac >>
     drule_at (Pat `_ _ = ((),_)`) runtime_entry_dispatch_code_labels >>
     disch_then (qspec_then `mk_raw_function "__entry" (all_blocks se)` mp_tac) >>
     simp[venomInstTheory.mk_raw_function_def] >> metis_tac[]) >>
  qpat_x_assum `run_lowering _ _ _ _ _ _ _ _ _ _ = _` mp_tac >>
  simp[vyperCompilerTheory.run_lowering_def,
       vyperCompilerTheory.extract_context_with_internals_def,
       GSYM loweringShapeDefsTheory.all_blocks_def] >>
  strip_tac >> gvs[AllCaseEqs()] >>
  `entry_blocks = all_blocks se` by
    (irule externalEntryShapeTheory.compile_internal_fn_bodies_entry_prefix >>
     goal_assum (drule_at Any) >> goal_assum (drule_at Any) >>
     Cases_on `internal_fns` >> simp[] >> PairCases_on `h` >>
     gvs[vyperCompilerTheory.internal_fn_descriptors_def, EVERY_MEM] >>
     qpat_x_assum `!d. _ ==> internal_label_ok (FST d)`
       (qspec_then `(h0,h3,h1.ce_returns_count)` mp_tac) >>
     simp[] >> metis_tac[]) >>
  qexists_tac `mk_raw_function "__entry" entry_blocks` >>
  gvs[venomInstTheory.mk_venom_context_def, venomInstTheory.mk_raw_function_def,
      venomInstTheory.lookup_function_def, FIND_thm]
QED

Theorem external_checks_code:
  !packages lbl ce args min_cds pay nr key ut iv fbody rt sd sx se func.
    MEM (lbl,ce,args,min_cds,pay,nr,key,ut,iv,fbody,rt) packages /\
    EVERY external_fn_shape_ok packages /\ ALL_DISTINCT (MAP FST packages) /\
    shape_state sd /\ (!l. l IN bound_labels sd ==> ~isPREFIX "fn_" l) /\
    compile_external_fn_bodies packages sd = ((),sx) /\
    cs_extends sx se /\ func.fn_blocks = all_blocks se ==>
    ?st st'. compile_entry_checks min_cds pay st = ((),st') /\
      fn_has_code st st' func /\ st.cs_current_bb = lbl /\
      st.cs_current_insts = [] /\ sd.cs_next_var <= st.cs_next_var
Proof
  rpt gen_tac >> strip_tac >>
  `isPREFIX "fn_" lbl` by
    (gvs[EVERY_MEM] >> first_x_assum drule >>
     simp[loweringShapePropsTheory.external_fn_shape_ok_def]) >>
  `~compiler_label lbl` by
    (gvs[loweringShapeDefsTheory.compiler_label_def, compiler_labels_future_def,
         fresh_label_output_def] >>
     Cases_on `lbl` >> gvs[]) >>
  `~MEM lbl (MAP (\bb. bb.bb_label) (all_blocks sd))` by
    (qpat_x_assum `!l. _` (qspec_then `lbl` mp_tac) >>
     simp[bound_labels_def, loweringShapeDefsTheory.all_blocks_def, MAP_REVERSE]) >>
  drule_all external_checks_occurrence >> strip_tac >>
  `cs_extends st' sx` by
    (qpat_x_assum `packages = _` SUBST_ALL_TAC >>
     drule_all external_checks_suffix_extends >> simp[]) >>
  `cs_extends st' se` by
    (irule cs_extends_trans >> goal_assum (drule_at Any) >> simp[]) >>
  qpat_x_assum `packages = _` SUBST_ALL_TAC >>
  drule_all external_checks_unshadowed >> strip_tac >>
  qexistsl_tac [`st`, `st'`] >> simp[] >> first_x_assum irule >>
  qexists_tac `se` >> simp[]
QED

(* The label-only variant needs no instruction-shape or immutable premise. *)
Theorem external_checks_labels_unshadowed:
  !pre lbl mincd pay sd sa st st'.
    ~MEM lbl (MAP FST pre) /\ ~isPREFIX "@" lbl /\
    ~MEM lbl (MAP (\bb. bb.bb_label) (all_blocks sd)) /\
    compile_external_fn_bodies pre sd = ((),sa) /\
    new_block lbl sa = (sa.cs_current_bb,st) /\
    compile_entry_checks mincd pay st = ((),st') ==>
    !se func. cs_extends st' se /\ func.fn_blocks = all_blocks se ==>
      fn_has_code st st' func
Proof
  rpt gen_tac >> strip_tac >>
  `~MEM lbl (MAP (\bb. bb.bb_label) (all_blocks sa))` by
    (drule_all externalEntryShapeTheory.compile_external_fn_bodies_preserves_label_absent >>
     simp[]) >>
  `st.cs_current_bb = lbl /\
   ~MEM lbl (MAP (\bb. bb.bb_label) (REVERSE st.cs_blocks))` by
    gvs[new_block_def, loweringShapeDefsTheory.all_blocks_def, LET_THM] >>
  rpt gen_tac >> strip_tac >>
  drule compile_entry_checks_same_blocks >>
  rewrite_tac[same_blocks_def] >> strip_tac >>
  simp[fn_has_code_def, emitted_blocks_def] >>
  drule externalEntryShapeTheory.cs_extends_open_lookup >> simp[]
QED

Theorem external_checks_labels_code:
  !packages lbl ce args mincd pay nr key ut iv body rt sd sx se func.
    MEM (lbl,ce,args,mincd,pay,nr,key,ut,iv,body,rt) packages /\
    ALL_DISTINCT (MAP FST packages) /\ ~isPREFIX "@" lbl /\
    ~MEM lbl (MAP (\bb. bb.bb_label) (all_blocks sd)) /\
    compile_external_fn_bodies packages sd = ((),sx) /\
    cs_extends sx se /\ func.fn_blocks = all_blocks se ==>
    ?st st'. compile_entry_checks mincd pay st = ((),st') /\
      fn_has_code st st' func /\ st.cs_current_bb = lbl /\
      st.cs_current_insts = [] /\ sd.cs_next_var <= st.cs_next_var
Proof
  rpt gen_tac >> strip_tac >>
  drule_all external_checks_occurrence >> strip_tac >>
  `cs_extends st' sb` by
    (qspecl_then [`ce`, `args`, `nr`, `key`, `ut`, `iv`, `body`, `rt`, `st'`]
       mp_tac externalEntryShapeTheory.compile_external_function_body_labels >> simp[]) >>
  `cs_extends sb sx` by
    (qspecl_then [`post`, `sb`] mp_tac
       externalEntryShapeTheory.compile_external_fn_bodies_label_partition >> simp[]) >>
  `cs_extends st' se` by metis_tac[cs_extends_trans] >>
  `~MEM lbl (MAP FST pre)` by
    (gvs[ALL_DISTINCT_APPEND] >> metis_tac[]) >>
  drule_all external_checks_labels_unshadowed >> strip_tac >>
  qexistsl_tac [`st`, `st'`] >> simp[]
QED

Theorem run_lowering_entry_checks_code:
  !selectors packages internal_fns fallback_fn rpolicy buckets metadata dense info unit
   lbl ce args min_cds pay nr key ut iv fbody rt.
    run_lowering selectors packages internal_fns fallback_fn rpolicy
      buckets metadata dense info "__entry" = SOME unit /\
    EVERY (\(sel,lbl,z). isPREFIX "fn_" lbl) selectors /\
    EVERY external_fn_shape_ok packages /\ fallback_shape_ok fallback_fn /\
    EVERY internal_fn_shape_ok internal_fns /\
    EVERY (\d. internal_label_ok (FST d)) (internal_fn_descriptors internal_fns) /\
    ALL_DISTINCT (MAP FST (internal_fn_descriptors internal_fns)) /\
    ALL_DISTINCT (MAP FST packages) /\
    MEM (lbl,ce,args,min_cds,pay,nr,key,ut,iv,fbody,rt) packages ==>
    ?func fb sa sd st st'.
      unit.cu_context.ctx_entry = SOME "__entry" /\
      venomInst$lookup_function "__entry" unit.cu_context.ctx_functions = SOME func /\
      func.fn_blocks <> [] /\ (HD func.fn_blocks).bb_label = "__entry" /\
      fresh_label "fallback" (initial_compile_state "__entry") = (fb,sa) /\
      compile_selector_dispatch_linear (MAP (\(sel,lbl,z). (sel,lbl)) selectors)
        fb sa = ((),sd) /\ fn_has_code sa sd func /\
      compile_entry_checks min_cds pay st = ((),st') /\ fn_has_code st st' func /\
      st.cs_current_bb = lbl /\ st.cs_current_insts = [] /\
      sd.cs_next_var <= st.cs_next_var
Proof
  rpt gen_tac >> strip_tac >>
  drule_all run_lowering_entry_function >> strip_tac >>
  `EVERY (\(sel,lbl). jump_label_ok lbl)
     (MAP (\(sel,lbl,z). (sel,lbl)) selectors)` by
    (gvs[EVERY_MAP, EVERY_MEM, pairTheory.FORALL_PROD,
         loweringShapeDefsTheory.jump_label_ok_def] >> metis_tac[]) >>
  drule_all runtime_entry_dispatch_code >> strip_tac >>
  drule_all external_checks_code >> strip_tac >>
  qexistsl_tac [`func`, `fb`, `sa`, `sd`, `st`, `st'`] >> simp[]
QED

Theorem run_lowering_entry_checks_code_labels:
  !selectors packages internal_fns fallback_fn rpolicy buckets metadata dense info unit
   lbl ce args min_cds pay nr key ut iv fbody rt.
    run_lowering selectors packages internal_fns fallback_fn rpolicy
      buckets metadata dense info "__entry" = SOME unit /\
    EVERY (\(sel,lbl,z). isPREFIX "fn_" lbl) selectors /\
    EVERY (\p. isPREFIX "fn_" (FST p)) packages /\
    EVERY (\d. internal_label_ok (FST d)) (internal_fn_descriptors internal_fns) /\
    ALL_DISTINCT (MAP FST packages) /\
    MEM (lbl,ce,args,min_cds,pay,nr,key,ut,iv,fbody,rt) packages ==>
    ?func fb sa sd st st'.
      unit.cu_context.ctx_entry = SOME "__entry" /\
      venomInst$lookup_function "__entry" unit.cu_context.ctx_functions = SOME func /\
      func.fn_blocks <> [] /\ (HD func.fn_blocks).bb_label = "__entry" /\
      fresh_label "fallback" (initial_compile_state "__entry") = (fb,sa) /\
      compile_selector_dispatch_linear (MAP (\(sel,lbl,z). (sel,lbl)) selectors)
        fb sa = ((),sd) /\ fn_has_code sa sd func /\
      compile_entry_checks min_cds pay st = ((),st') /\ fn_has_code st st' func /\
      st.cs_current_bb = lbl /\ st.cs_current_insts = [] /\
      sd.cs_next_var <= st.cs_next_var
Proof
  rpt gen_tac >> strip_tac >>
  drule_all run_lowering_entry_function_labels >> strip_tac >>
  `EVERY (\(sel,lbl). jump_label_ok lbl)
     (MAP (\(sel,lbl,z). (sel,lbl)) selectors)` by
    (gvs[EVERY_MAP, EVERY_MEM, pairTheory.FORALL_PROD,
         loweringShapeDefsTheory.jump_label_ok_def] >> metis_tac[]) >>
  drule_all runtime_entry_dispatch_code_labels >> strip_tac >>
  `isPREFIX "fn_" lbl` by (gvs[EVERY_MEM] >> metis_tac[pairTheory.FST]) >>
  `~isPREFIX "@" lbl` by (Cases_on `lbl` >> gvs[]) >>
  `~MEM lbl (MAP (\bb. bb.bb_label) (all_blocks sd))` by
    (simp[MEM_MAP] >> rpt strip_tac >>
     `lbl IN bound_labels sd` by
       (gvs[loweringShapeDefsTheory.all_blocks_def, bound_labels_def, MEM_MAP] >>
        metis_tac[]) >> metis_tac[]) >>
  drule_all external_checks_labels_code >> strip_tac >>
  qexistsl_tac [`func`, `fb`, `sa`, `sd`, `st`, `st'`] >> simp[]
QED

Theorem classified_external_labels_distinct:
  !tops. ALL_DISTINCT (supported_function_names tops) ==>
    ALL_DISTINCT (MAP (\(mut,nr,rr,name,args,dflts,ret,fbody). "fn_" ++ name)
      (FST (classify_functions tops)))
Proof
  Induct >> simp[classify_functions_def] >> gen_tac >>
  Cases_on `classify_functions tops` >> PairCases_on `r` >>
  Cases_on `h` >>
  gvs[Once classify_functions_def, classify_function_def, supported_function_names_def] >>
  rename1 `case vis of External => _ | Internal => _ | Deploy => _` >>
  Cases_on `vis` >> gvs[classify_function_def] >>
  IF_CASES_TAC >> gvs[] >>
  simp[MEM_MAP, FORALL_PROD] >> rpt strip_tac >>
  rename1 `MEM (mut,nr,rr,name,args,dflts,ret,fbody) q` >>
  `MEM (mut,nr,rr,name,args,dflts,ret,fbody) (FST (classify_functions tops))` by
    simp[classify_functions_def] >>
  drule loweringShapePropsTheory.classify_functions_external_source >>
  strip_tac >>
  metis_tac[loweringShapePropsTheory.MEM_supported_function_names]
QED

Theorem source_runtime_entry_checks_code:
  !tops rpolicy unit mut nr rr name args dflts ret fbody
   lbl ce pos_args min_cds pay nr' key ut iv rt.
    lower_vyper_runtime_unit tops rpolicy = SOME unit /\ supported_program tops /\
    MEM (mut,nr,rr,name,args,dflts,ret,fbody) (FST (classify_functions tops)) /\
    set_external_package_target rpolicy.rpol_target
      (package_external_fn tops F (assign_nkeys tops 0)
        (mut,nr,rr,name,args,dflts,ret,fbody)) =
      (lbl,ce,pos_args,min_cds,pay,nr',key,ut,iv,fbody,rt) ==>
    ?func fb sa sd st st'.
      unit.cu_context.ctx_entry = SOME "__entry" /\
      venomInst$lookup_function "__entry" unit.cu_context.ctx_functions = SOME func /\
      func.fn_blocks <> [] /\ (HD func.fn_blocks).bb_label = "__entry" /\
      fresh_label "fallback" (initial_compile_state "__entry") = (fb,sa) /\
      compile_selector_dispatch_linear
        (MAP (\(sel,lbl,z). (sel,lbl))
          (build_selectors (type_env tops) (FST (classify_functions tops))))
        fb sa = ((),sd) /\ fn_has_code sa sd func /\
      compile_entry_checks min_cds pay st = ((),st') /\ fn_has_code st st' func /\
      st.cs_current_bb = lbl /\ st.cs_current_insts = [] /\
      sd.cs_next_var <= st.cs_next_var
Proof
  rpt gen_tac >> strip_tac >>
  `ALL_DISTINCT (supported_function_names tops)` by
    gvs[supported_program_def, supported_declaration_names_def] >>
  drule classified_external_labels_distinct >> disch_tac >>
  qpat_x_assum `lower_vyper_runtime_unit _ _ = _` mp_tac >>
  simp[lower_vyper_runtime_unit_def] >>
  Cases_on `classify_functions tops` >> PairCases_on `r` >>
  rename1 `classify_functions tops = (exts,ints,fallback,ctor)` >>
  simp[] >> strip_tac >>
  `EVERY (\(sel,lbl,z). isPREFIX "fn_" lbl)
     (build_selectors (type_env tops) exts)` by
    simp[loweringShapePropsTheory.build_selectors_fn_labels] >>
  qmatch_asmsub_abbrev_tac `run_lowering selectors packages internal_fns fallback_fn` >>
  `EVERY (\p. isPREFIX "fn_" (FST p)) packages` by
    (simp[Abbr `packages`, EVERY_MAP, EVERY_MEM, FORALL_PROD,
          set_external_package_target_def, package_external_fn_def, LET_THM]) >>
  `ALL_DISTINCT (MAP FST packages)` by
    (gvs[Abbr `packages`, MAP_MAP_o, combinTheory.o_DEF,
         pairTheory.LAMBDA_PROD, set_external_package_target_def,
         package_external_fn_def, LET_THM]) >>
  `EVERY (\d. internal_label_ok (FST d)) (internal_fn_descriptors internal_fns)` by
    (simp_tac std_ss [Abbr `internal_fns`, GSYM MAP_MAP_o,
          internal_fn_descriptors_set_internal_package_target,
          internal_fn_descriptors_MAP_package_internal_fn] >>
     simp_tac std_ss [EVERY_MAP, EVERY_MEM, FORALL_PROD,
          source_internal_fn_descriptor_def, LET_THM] >>
     rewrite_tac[loweringShapeDefsTheory.internal_label_ok_def,
                 internal_fn_label_prefix]) >>
  `MEM (lbl,ce,pos_args,min_cds,pay,nr',key,ut,iv,fbody,rt) packages` by
    (simp[Abbr `packages`, MEM_MAP] >> fs[] >>
     goal_assum (drule_at Any) >> simp[]) >>
  drule_all run_lowering_entry_checks_code_labels >>
  simp[Abbr `selectors`]
QED

Theorem linear_dispatch_entry_no_phi:
  !selectors fallback sa sd func.
    compile_selector_dispatch_linear selectors fallback sa = ((),sd) /\
    fn_has_code sa sd func /\ sa.cs_current_insts = [] ==>
    ?bb. lookup_block sa.cs_current_bb func.fn_blocks = SOME bb /\
         phi_prefix_length bb.bb_instructions = 0
Proof
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `compile_selector_dispatch_linear _ _ _ = _` mp_tac >>
  simp[compile_selector_dispatch_linear_def, comp_bind_def, comp_ignore_bind_def] >>
  rpt (pairarg_tac >> fs[]) >> strip_tac >>
  rename1 `emit_inst JMP _ _ a9 = (_,sd)` >>
  rename1 `compile_selector_checks _ _ a8 = (_,a9)` >>
  rename1 `emit_op SHR _ a7 = (_,a8)` >>
  rename1 `emit_op CALLDATALOAD _ a6 = (_,a7)` >>
  rename1 `new_block dispatch_lbl a5 = (_,a6)` >>
  rename1 `emit_inst JNZ _ _ a4 = (_,a5)` >>
  rename1 `fresh_label "dispatch" a3 = (_,a4)` >>
  rename1 `emit_op ISZERO _ a2 = (_,a3)` >>
  rename1 `emit_op LT _ a1 = (_,a2)` >>
  `cs_extends sa a1 /\ cs_extends a1 a2 /\ cs_extends a2 a3 /\
   cs_extends a3 a4 /\ cs_extends a4 a5 /\ cs_extends a5 a6 /\
   cs_extends a6 a7 /\ cs_extends a7 a8 /\ cs_extends a8 a9 /\
   cs_extends a9 sd` by
    (rpt conj_tac >> metis_tac[cs_appends_def, cs_appends_emit_helpers,
                             cs_appends_prims, compile_selector_checks_appends]) >>
  `fn_has_code a5 a6 func` by
    metis_tac[fn_has_code_mid, fn_has_code_split, cs_extends_trans] >>
  drule_all fn_has_code_new_block >> strip_tac >>
  `a5.cs_current_bb = sa.cs_current_bb /\
   phi_prefix_length a5.cs_current_insts = 0` suffices_by
    (strip_tac >> qexists_tac `<|bb_label := a5.cs_current_bb;
                               bb_instructions := a5.cs_current_insts|>` >> gvs[]) >>
  qpat_x_assum `sa.cs_current_insts = []` mp_tac >>
  qpat_x_assum `emit_inst JNZ _ _ _ = _` mp_tac >>
  qpat_x_assum `fresh_label "dispatch" _ = _` mp_tac >>
  qpat_x_assum `emit_op ISZERO _ _ = _` mp_tac >>
  qpat_x_assum `emit_op LT _ _ = _` mp_tac >>
  qpat_x_assum `emit_op CALLDATASIZE _ _ = _` mp_tac >>
  POP_ASSUM_LIST (K ALL_TAC) >>
  simp_tac std_ss [emitHelperTheory.emit_op_def, emitHelperTheory.emit_void_def,
    emitHelperTheory.emit_inst_def, comp_bind_def, comp_ignore_bind_def,
    comp_return_def, fresh_var_def, fresh_id_def, fresh_label_def, emit_def,
    LET_THM] >> rpt strip_tac >> gvs[phi_prefix_length_def, venomInstTheory.mk_inst_def]
QED

Theorem entry_context_continuation:
  !ctx func vs s0 bb.
    ctx.ctx_entry = SOME "__entry" /\
    venomInst$lookup_function "__entry" ctx.ctx_functions = SOME func /\
    fn_entry_label func = SOME "__entry" /\
    lookup_block "__entry" func.fn_blocks = SOME bb /\
    phi_prefix_length bb.bb_instructions = 0 /\
    runs_through ctx func
      (vs with <|vs_prev_bb := NONE; vs_current_bb := "__entry"; vs_inst_idx := 0|>) s0 ==>
    !fuel r. run_from fuel ctx func s0 = r /\ (!e. r <> Error e) ==>
      ?fuel'. run_context fuel' ctx vs = r
Proof
  rpt gen_tac >> strip_tac >> rpt gen_tac >> strip_tac >>
  qpat_x_assum `runs_through _ _ _ _` mp_tac >>
  rewrite_tac[runs_through_def] >> disch_then drule_all >> strip_tac >>
  rename1 `run_from entry_fuel _ _ _ = r` >>
  qexists_tac `SUC entry_fuel` >>
  drule_all run_context_run_blocks >> disch_then (fn th => rewrite_tac[th]) >>
  `lookup_block
     (vs with <|vs_prev_bb := NONE; vs_current_bb := "__entry"; vs_inst_idx := 0|>).vs_current_bb
     func.fn_blocks = SOME bb` by simp[] >>
  drule_all run_blocks_run_from_no_phi >> simp[]
QED

Theorem linear_dispatch_context_reaches:
  !ctx func selectors fb sa sd st vs.
    ctx.ctx_entry = SOME "__entry" /\
    venomInst$lookup_function "__entry" ctx.ctx_functions = SOME func /\
    fn_entry_label func = SOME "__entry" /\
    fresh_label "fallback" (initial_compile_state "__entry") = (fb,sa) /\
    compile_selector_dispatch_linear selectors fb sa = ((),sd) /\
    fn_has_code sa sd func /\ EVERY (\(sel,lbl). sel < 2 ** 32) selectors /\
    LENGTH vs.vs_call_ctx.cc_calldata < dimword (:256) /\
    vs.vs_vars = FEMPTY /\ ~vs.vs_halted /\
    linear_dispatch_target vs.vs_call_ctx.cc_calldata selectors fb = st.cs_current_bb /\
    st.cs_current_insts = [] /\ sd.cs_next_var <= st.cs_next_var ==>
    ?s0. vars_pc_only vs s0 /\ fresh_vars_wrt st s0 /\ ~s0.vs_halted /\
      s0.vs_current_bb = st.cs_current_bb /\
      s0.vs_inst_idx = LENGTH st.cs_current_insts /\
      !fuel r. run_from fuel ctx func s0 = r /\ (!e. r <> Error e) ==>
        ?fuel'. run_context fuel' ctx vs = r
Proof
  rpt gen_tac >> strip_tac >>
  `sa.cs_current_bb = "__entry" /\ sa.cs_current_insts = []` by
    (qpat_x_assum `fresh_label _ _ = _` mp_tac >>
     simp[fresh_label_def, vyperCompilerTheory.initial_compile_state_def, LET_THM] >>
     strip_tac >> gvs[]) >>
  qabbrev_tac `ss = vs with <|vs_prev_bb := NONE;
    vs_current_bb := "__entry"; vs_inst_idx := 0|>` >>
  `fresh_vars_wrt sa ss /\ ~ss.vs_halted /\
   ss.vs_current_bb = sa.cs_current_bb /\
   ss.vs_inst_idx = LENGTH sa.cs_current_insts /\
   LENGTH ss.vs_call_ctx.cc_calldata < dimword (:256)` by
    simp[Abbr `ss`, fresh_vars_wrt_def] >>
  drule_all compile_selector_dispatch_linear_correct >>
  disch_then (qspec_then `ctx` strip_assume_tac) >>
  `vars_pc_only vs ss` by
    simp[vars_pc_only_def, Abbr `ss`, venom_state_component_equality] >>
  `vars_pc_only vs tt` by (drule_all vars_pc_only_trans >> simp[]) >>
  `fresh_vars_wrt st tt` by
    (irule emitHelperPropsTheory.fresh_vars_wrt_mono >> qexists_tac `sd` >> simp[]) >>
  `~tt.vs_halted` by
    (qpat_x_assum `vars_pc_only vs tt` mp_tac >>
     simp[vars_pc_only_def, venom_state_component_equality]) >>
  `tt.vs_current_bb = st.cs_current_bb` by gvs[Abbr `ss`] >>
  drule_all linear_dispatch_entry_no_phi >> strip_tac >>
  qexists_tac `tt` >> simp[] >>
  rpt gen_tac >> strip_tac >>
  irule entry_context_continuation >> simp[] >>
  qexistsl_tac [`bb`, `fuel`, `tt`] >> gvs[Abbr `ss`]
QED

Theorem external_entry_reaches_checks:
  !tops rpolicy unit am tx ret vs mut args fbody.
    lower_vyper_runtime_unit tops rpolicy = SOME unit /\
    supported_program tops /\
    source_typing_ok tops am tx /\
    source_deployment_rel tops am tx /\
    valid_vyper_call tops tx vs.vs_call_ctx.cc_calldata ret /\
    initial_venom_state_rel tops am tx vs /\
    lookup_function NONE tx.function_name External tops =
      SOME (mut, F, args, [], ret, fbody) ==>
    ?rr lbl cenv0 pos_args min_cds is_payable nkey ut' iv rt st st' func
     s0.
      set_external_package_target rpolicy.rpol_target
        (package_external_fn tops F (assign_nkeys tops 0)
           (mut, F, rr, tx.function_name, args, ([] : expr list), ret, fbody)) =
        (lbl, cenv0, pos_args, min_cds, is_payable, F, nkey, ut', iv, fbody,
         rt) /\
      compile_entry_checks min_cds is_payable st = ((), st') /\
      fn_has_code st st' func /\
      vars_pc_only vs s0 /\ fresh_vars_wrt st s0 /\ ~s0.vs_halted /\
      s0.vs_current_bb = st.cs_current_bb /\
      s0.vs_inst_idx = LENGTH st.cs_current_insts /\
      !fuel r. run_from fuel unit.cu_context func s0 = r /\
               (!e. r <> Error e) ==>
               ?fuel'. run_context fuel' unit.cu_context vs = r
Proof
  rpt gen_tac >> strip_tac >>
  drule_all selected_external_dispatch >> strip_tac >>
  qspecl_then [`tops`, `rpolicy.rpol_target`, `mut`, `rr`,
               `tx.function_name`, `args`, `ret`, `fbody`]
    strip_assume_tac selected_external_package >>
  drule_all source_runtime_entry_checks_code >> strip_tac >>
  `fn_entry_label func = SOME "__entry"` by
    simp[venomInstTheory.fn_entry_label_def, venomInstTheory.entry_block_def,
         listTheory.NULL_EQ] >>
  `LENGTH vs.vs_call_ctx.cc_calldata < dimword (:256)` by
    (drule_all initial_venom_state_calldata_length >> simp[]) >>
  `vs.vs_vars = FEMPTY /\ ~vs.vs_halted` by
    fs[initial_venom_state_rel_def] >>
  `EVERY (\(sel,lbl). sel < 2 ** 32)
     (MAP (\(sel,lbl,z). (sel,lbl))
       (build_selectors (type_env tops) (FST (classify_functions tops))))` by
    simp[linear_selectors_lt] >>
  `linear_dispatch_target vs.vs_call_ctx.cc_calldata
     (MAP (\(sel,lbl,z). (sel,lbl))
       (build_selectors (type_env tops) (FST (classify_functions tops)))) fb =
     st.cs_current_bb` by simp[] >>
  drule_all linear_dispatch_context_reaches >> strip_tac >>
  qexistsl_tac [`rr`, `"fn_" ++ tx.function_name`, `cenv`, `pos_args`,
                `min_cds`, `is_payable`, `nkey`, `ut`, `iv`, `rt`,
                `st`, `st'`, `func`, `s0`] >> simp[] >>
  rpt strip_tac >> first_x_assum irule >> simp[] >>
  qexists_tac `fuel` >> simp[]
QED

