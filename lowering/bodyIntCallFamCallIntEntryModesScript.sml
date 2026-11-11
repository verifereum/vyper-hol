(* Compiler modes expose all code slices before argument staging is run. *)
Theory bodyIntCallFamCallIntEntryModes
Ancestors
  bodyIntCallCompilerBoundary intCallStep exprLoweringProps fragExec
  stmtLoweringMono compileEnv bodyIntCallMetadata bodySim supportedNames
  supportedProgram

Theorem intcall_compiler_stage_slices:
  compile_multi_vvs compile_expr ce ds sa = (vs,a) /\ ci_mono a b /\
  compile_stage_intcall_args ce vs flags tys b = (ops,c) /\ ci_mono c sb /\
  fn_has_code sa sb func ==>
  fn_has_code sa a func /\ fn_has_code a b func /\ fn_has_code b c func /\
  fn_has_code c sb func
Proof
  strip_tac >>
  `ci_mono sa a` by
    (qspecl_then [`compile_expr`,`ce`,`ds`,`sa`] mp_tac
       ci_mono_compile_multi_vvs >> simp[cj 1 ci_mono_compile_expr_sa]) >>
  `ci_mono b c` by
    (qspecl_then [`ce`,`vs`,`flags`,`tys`,`b`] mp_tac
       ci_mono_compile_stage_intcall_args >> simp[]) >>
  fs[ci_mono_def] >>
  `cs_extends b sb` by metis_tac[cs_extends_trans] >>
  `cs_extends a sb` by metis_tac[cs_extends_trans] >>
  metis_tac[fn_has_code_split]
QED

Theorem intcall_void_mode_code:
  compile_call compile_expr ce ret_ty ty (IntCall fid) ds dflt sa = (vv,sb) /\
  ce.ce_func_info (nsid_to_string fid) = (0,rbs,flags) /\
  ce.ce_func_return_type (nsid_to_string fid) = NoneT /\
  fn_has_code sa sb func ==>
  ?vs a ops c u.
    compile_multi_vvs compile_expr ce ds sa = (vs,a) /\
    compile_stage_intcall_args ce vs flags (MAP expr_type ds) a = (ops,c) /\
    emit_void INVOKE
      (Label (internal_fn_label (ce.ce_func_ids (nsid_to_string fid))
        (nsid_to_string fid) (ce.ce_func_param_types (nsid_to_string fid))
        ce.ce_is_ctor) :: ops) c = (u,sb) /\
    vv = StackValue NoneT (Lit 0w) /\
    fn_has_code sa a func /\ fn_has_code a c func /\ fn_has_code c sb func
Proof
  strip_tac >> drule_all compile_call_intcall_shape >> strip_tac >> gvs[] >>
  rename1 `compile_multi_vvs _ _ _ _ = (vs,a)` >>
  rename1 `compile_stage_intcall_args _ _ _ _ a = (ops,c)` >>
  qpat_x_assum `emit_void INVOKE _ c = _` mp_tac >>
  qmatch_goalsub_abbrev_tac `emit_void INVOKE argv c` >> strip_tac >>
  `ci_mono c sb` by
    (qspecl_then [`INVOKE`,`argv`,`c`] mp_tac ci_mono_emit_void >> simp[]) >>
  `fn_has_code sa a func /\ fn_has_code a c func /\ fn_has_code c sb func` by
    metis_tac[intcall_compiler_stage_slices, ci_mono_refl] >>
  goal_assum (drule_at Any) >> simp[Abbr `argv`]
QED

Theorem intcall_stack_mode_code:
  compile_call compile_expr ce ret_ty ty (IntCall fid) ds dflt sa = (vv,sb) /\
  ce.ce_func_info (nsid_to_string fid) = (nret,rbs,flags) /\ 0 < nret /\
  fn_has_code sa sb func ==>
  ?vs a b ops c rb results d u.
    compile_multi_vvs compile_expr ce ds sa = (vs,a) /\
    compile_alloc_buffer (32 * nret) a = (rb,b) /\
    compile_stage_intcall_args ce vs flags (MAP expr_type ds) b = (ops,c) /\
    emit_multi_op INVOKE
      (Label (internal_fn_label (ce.ce_func_ids (nsid_to_string fid))
        (nsid_to_string fid) (ce.ce_func_param_types (nsid_to_string fid))
        ce.ce_is_ctor) :: ops) nret c = (results,d) /\
    store_multi_results rb.buf_operand results 0 d = (u,sb) /\
    vv = LocatedValue (ce.ce_func_return_type (nsid_to_string fid)) (base_ptr rb) /\
    fn_has_code sa a func /\ fn_has_code a b func /\ fn_has_code b c func /\
    fn_has_code c d func /\ fn_has_code d sb func
Proof
  strip_tac >> drule_all compile_call_intcall_shape >> strip_tac >> gvs[] >>
  rename1 `compile_multi_vvs _ _ _ _ = (vs,a)` >>
  rename1 `compile_alloc_buffer _ a = (rb,b)` >>
  rename1 `compile_stage_intcall_args _ _ _ _ b = (ops,c)` >>
  rename1 `store_multi_results _ results 0 d = _` >>
  qpat_x_assum `emit_multi_op INVOKE _ _ c = _` mp_tac >>
  qmatch_goalsub_abbrev_tac `emit_multi_op INVOKE argv nret c` >> strip_tac >>
  `ci_mono a b` by
    (qspecl_then [`32 * nret`,`a`] mp_tac ci_mono_compile_alloc_buffer >> simp[]) >>
  `ci_mono c d` by
    (qspecl_then [`INVOKE`,`argv`,`nret`,`c`] mp_tac ci_mono_emit_multi_op >> simp[]) >>
  `ci_mono d sb` by
    (qspecl_then [`rb.buf_operand`,`results`,`0`,`d`] mp_tac
       ci_mono_store_multi_results >> simp[]) >>
  `ci_mono c sb` by
    (fs[ci_mono_def] >> metis_tac[cs_extends_trans, arithmeticTheory.LESS_EQ_TRANS]) >>
  drule_all intcall_compiler_stage_slices >> strip_tac >>
  `fn_has_code c d func /\ fn_has_code d sb func` by
    metis_tac[fn_has_code_split, ci_mono_def] >>
  goal_assum (drule_at Any) >> simp[Abbr `argv`] >>
  goal_assum (drule_at Any) >> simp[]
QED

Theorem intcall_buffer_mode_code:
  compile_call compile_expr ce ret_ty ty (IntCall fid) ds dflt sa = (vv,sb) /\
  ce.ce_func_info (nsid_to_string fid) = (0,rbs,flags) /\
  ce.ce_func_return_type (nsid_to_string fid) <> NoneT /\
  fn_has_code sa sb func ==>
  ?vs a b ops c rb u.
    compile_multi_vvs compile_expr ce ds sa = (vs,a) /\
    compile_alloc_buffer rbs a = (rb,b) /\
    compile_stage_intcall_args ce vs flags (MAP expr_type ds) b = (ops,c) /\
    emit_void INVOKE
      (Label (internal_fn_label (ce.ce_func_ids (nsid_to_string fid))
        (nsid_to_string fid) (ce.ce_func_param_types (nsid_to_string fid))
        ce.ce_is_ctor) :: rb.buf_operand :: ops) c = (u,sb) /\
    vv = LocatedValue (ce.ce_func_return_type (nsid_to_string fid)) (base_ptr rb) /\
    fn_has_code sa a func /\ fn_has_code a b func /\ fn_has_code b c func /\
    fn_has_code c sb func
Proof
  strip_tac >> drule_all compile_call_intcall_shape >> strip_tac >> gvs[] >>
  rename1 `compile_multi_vvs _ _ _ _ = (vs,a)` >>
  rename1 `compile_alloc_buffer _ a = (rb,b)` >>
  rename1 `compile_stage_intcall_args _ _ _ _ b = (ops,c)` >>
  qpat_x_assum `emit_void INVOKE _ c = _` mp_tac >>
  qmatch_goalsub_abbrev_tac `emit_void INVOKE argv c` >> strip_tac >>
  `ci_mono a b` by
    (qspecl_then [`rbs`,`a`] mp_tac ci_mono_compile_alloc_buffer >> simp[]) >>
  `ci_mono c sb` by
    (qspecl_then [`INVOKE`,`argv`,`c`] mp_tac ci_mono_emit_void >> simp[]) >>
  drule_all intcall_compiler_stage_slices >> strip_tac >>
  goal_assum (drule_at Any) >> simp[Abbr `argv`] >>
  goal_assum (drule_at Any) >> simp[]
QED

Theorem intcall_nonstack_return_buffer_size:
  body_inv tops ctx ce cx /\
  MEM (FunctionDecl Internal mut nr rr name args dflts ret ss) tops /\
  ce.ce_func_info (nsid_to_string (NONE,name)) = (0,rbs,pvs) /\ ret <> NoneT ==>
  rbs = type_mem_bytes (get_struct_fields ce.ce_struct_fields) ret
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
  simp[compute_func_info_def] >>
  Cases_on `ret` >> gvs[]
QED
