(* Compiler boundary for non-word storage Append. *)
Theory bodyIntCallFamStmtMutationAppendAggregateCompile
Ancestors
  stmtSimAppendStorageCompose stmtSimAssignStorage externalEntryShape
  stmtLoweringMono loweringHalt

Theorem intcall_append_aggregate_compile:
  stmt_env ce lc rt (Append (TopLevelNameTarget nid) e) sa = (ce',sf) /\
  FLOOKUP ce.ce_module_vars nid =
    SOME (if tr then TransientLoc slot else StorageLoc slot) /\
  ce.ce_module_var_type nid = SOME (ArrayT elem (Dynamic cap)) /\
  ce.ce_hashmap_info nid = NONE /\
  ~is_word_type elem /\ lowered_value_type ce e = elem ==>
  ce' = ce /\ ?raw sm buf sn sp.
    lower_value compile_expr ce elem e sa = (raw,sm) /\
    compile_alloc_buffer (type_memory_bytes ce elem) sm = (buf,sn) /\
    compile_store_memory ce raw buf.buf_operand elem elem sn = ((),sp) /\
    compile_dynarray_append ce (Lit slot) buf.buf_operand 1
      ((type_memory_bytes ce elem + 31) DIV 32) elem elem cap F
      (if tr then TLOAD else SLOAD) (if tr then TSTORE else SSTORE)
      sp = ((),sf)
Proof
  strip_tac >>
  drule_all stmtSimAssignStorageTheory.compile_get_target_ptr_toplevel >>
  strip_tac >>
  qpat_x_assum `stmt_env _ _ _ _ _ = _` mp_tac >>
  simp[loweringPostsTheory.stmt_env_def,
       stmtLoweringTheory.declare_stmt_local_def,
       compileEnvTheory.comp_bind_def, compileEnvTheory.comp_ignore_bind_def,
       compileEnvTheory.comp_return_def, Once stmtLoweringTheory.compile_stmt_def] >>
  Cases_on `tr` >>
  simp[compileEnvTheory.word_scale_def, compileEnvTheory.elem_size_in_location_def,
       compileEnvTheory.is_slot_addressed_def, compileEnvTheory.load_opc_for_def,
       compileEnvTheory.store_opc_for_def] >>
  rpt (pairarg_tac >> gvs[]) >> strip_tac >> gvs[] >> metis_tac[]
QED

Theorem intcall_append_aggregate_code_frame:
  lower_value compile_expr ce elem e sa = (raw,sm) /\
  compile_alloc_buffer (type_memory_bytes ce elem) sm = (buf,sn) /\
  compile_store_memory ce raw buf.buf_operand elem elem sn = ((),sp) /\
  compile_dynarray_append ce (Lit slot) buf.buf_operand 1 sz elem elem cap F
    (if tr then TLOAD else SLOAD) (if tr then TSTORE else SSTORE)
    sp = ((),sf) /\ fn_has_code sa sf func ==>
  cs_extends sa sm /\ cs_extends sm sn /\ cs_extends sn sp /\
  cs_extends sp sf /\ fn_has_code sa sm func /\ fn_has_code sm sn func /\
  fn_has_code sn sp func /\ fn_has_code sp sf func /\
  sa.cs_next_var <= sm.cs_next_var /\ sm.cs_next_var <= sn.cs_next_var /\
  sn.cs_next_var <= sp.cs_next_var /\ sp.cs_next_var <= sf.cs_next_var
Proof
  strip_tac >>
  `cs_extends sa sm /\ sa.cs_next_var <= sm.cs_next_var` by
    metis_tac[cj 2 exprLoweringPropsTheory.compile_expr_grows] >>
  `cs_extends sm sn` by metis_tac[loweringHaltTheory.compile_alloc_buffer_extends] >>
  `cs_extends sn sp` by
    metis_tac[externalEntryShapeTheory.compile_store_memory_labels, pairTheory.SND] >>
  `cs_extends sp sf` by
    metis_tac[externalEntryShapeTheory.compile_dynarray_append_labels, pairTheory.SND] >>
  `cs_extends sn sf /\ cs_extends sm sf` by
    metis_tac[compileEnvTheory.cs_extends_trans] >>
  drule_all fragExecTheory.fn_has_code_split >> strip_tac >>
  `fn_has_code sm sn func /\ fn_has_code sn sf func` by
    metis_tac[fragExecTheory.fn_has_code_split] >>
  `fn_has_code sn sp func /\ fn_has_code sp sf func` by
    metis_tac[fragExecTheory.fn_has_code_split] >>
  simp[] >>
  conj_tac
  >- (drule loweringHaltTheory.compile_alloc_buffer_emission >> strip_tac >> simp[]) >>
  conj_tac
  >- metis_tac[exprLoweringPropsTheory.ci_mono_compile_store_memory,
               exprLoweringPropsTheory.ci_mono_def, pairTheory.SND] >>
  metis_tac[stmtLoweringMonoTheory.ci_mono_compile_dynarray_append,
            exprLoweringPropsTheory.ci_mono_def, pairTheory.SND]
QED
