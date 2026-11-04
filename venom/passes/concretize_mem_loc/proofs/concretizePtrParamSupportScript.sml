Theory concretizePtrParamSupport
Ancestors concretizePtrRuntimeOrigins concretizeAnalysisRoots ptrDiscipline
  pointerClosure pointerConfinedDefs venomInst venomWf finite_map list pred_set words

Definition ptr_params_ok_def:
  ptr_params_ok P fn PG <=>
    !k site. k < LENGTH PG /\ EL k PG = SOME site ==> k IN P fn.fn_name
End

Definition ptr_static_support_def:
  ptr_static_support P fn G <=>
    !v site. FLOOKUP G v = SOME site ==> v IN fn_pv P fn
End

Theorem ptr_params_empty[simp]:
  ptr_params_ok P fn []
Proof simp[ptr_params_ok_def]
QED

Theorem ptr_static_empty[simp]:
  ptr_static_support P fn FEMPTY
Proof simp[ptr_static_support_def]
QED

Theorem ptr_static_restrict:
  ptr_static_support P fn G ==> ptr_static_support P fn (DRESTRICT G keys)
Proof
  simp[ptr_static_support_def, FLOOKUP_DRESTRICT] >> metis_tac[]
QED

Theorem ptr_static_site_iff:
  ptr_static_support P fn G <=> !site. ptr_site_supported (fn_pv P fn) G site
Proof simp[ptr_static_support_def, ptr_site_supported_def] >> metis_tac[]
QED

Theorem ptr_static_entry:
  ptr_static_support P fn G ==> ptr_static_support P fn (entry_prov fn s G)
Proof
  simp[ptr_static_site_iff] >> rpt strip_tac >> irule ptr_site_entry >>
  simp[] >>
  metis_tac[pointer_derived_vars_closed, ptr_roots_finite, fn_pv_def]
QED

Theorem ptr_static_step:
  ptr_params_ok P fn PG /\ ptr_static_support P fn G /\
  MEM inst (fn_insts fn) /\ fn_ptr_ok P fn /\ EVERY inst_wf (fn_insts fn) ==>
  ptr_static_support P fn (step_prov PG G inst s')
Proof
  strip_tac >> simp[ptr_static_site_iff] >> gen_tac >>
  irule ptr_site_step >> simp[] >>
  reverse conj_tac
  >- (conj_tac
      >- (qexists `fn` >> simp[] >>
          metis_tac[pointer_derived_vars_closed, ptr_roots_finite, fn_pv_def]) >>
      gvs[ptr_static_site_iff]) >>
  strip_tac >> rpt strip_tac >>
  `inst_wf inst` by fs[EVERY_MEM] >>
  qpat_x_assum `EVERY _ _` kall_tac >>
  `inst_output inst = SOME out` by
    (gvs[inst_wf_def] >>
     Cases_on `inst.inst_outputs` >> gvs[inst_output_def] >>
     Cases_on `t` >> gvs[]) >>
  `out IN ptr_roots P fn` by
    (gvs[ptr_roots_def, alloca_roots_def, out_prov_def, AllCaseEqs(), ptr_params_ok_def] >>
     metis_tac[]) >>
  metis_tac[pointer_derived_vars_roots, ptr_roots_finite, fn_pv_def, SUBSET_DEF]
QED

Theorem ptr_static_invoke_params:
  ptr_static_support P fn G /\ fn_ptr_ok P fn /\
  MEM callinst (fn_insts fn) /\ callinst.inst_opcode = INVOKE /\
  decode_invoke callinst = SOME (nm,ops) /\
  lookup_function nm ctx.ctx_functions = SOME callee ==>
  ptr_params_ok P callee (MAP (op_prov G) ops)
Proof
  strip_tac >>
  `callee.fn_name = nm` by
    (`!fns. lookup_function nm fns = SOME callee ==> callee.fn_name = nm`
       suffices_by metis_tac[] >>
     Induct >> simp[lookup_function_def, FIND_thm] >>
     rpt strip_tac >> gvs[AllCaseEqs()] >> metis_tac[lookup_function_def]) >>
  `ptr_use_ok P (fn_pv P fn) callinst` by
    (fs[fn_ptr_ok_def] >> metis_tac[]) >>
  gvs[ptr_use_ok_def, ptr_params_ok_def] >> rpt strip_tac >> gvs[EL_MAP] >>
  Cases_on `EL k ops` >> gvs[op_prov_def, ptr_static_support_def] >> metis_tac[]
QED
