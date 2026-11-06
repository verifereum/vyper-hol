Theory bodyPtrIfExpReturnMetadata
Ancestors bodyPtrIfExpEndpointTyping entryStateRel compileVyper compileEnv supportedNames vyperInterpreter vyperTypeContractStaticMaps

(* Local calling-convention algebra, before lookup in the framed program. *)
Theorem ifexp_compute_func_info_buffer_size:
  !sft ret bytes args rc rbs pvs.
    compute_func_info sft ret bytes args = (rc,rbs,pvs) /\
    rc = 0 /\ 0 < rbs ==> rbs = bytes
Proof
  rpt gen_tac >> Cases_on `ret` >>
  simp[compute_func_info_def] >> rpt strip_tac >> gvs[]
QED

Theorem ifexp_compute_func_info_zero_size:
  !sft ret bytes args pvs.
    compute_func_info sft ret bytes args = (0,0,pvs) ==>
    ret = NoneT \/ bytes = 0
Proof
  rpt gen_tac >> Cases_on `ret` >>
  simp[compute_func_info_def] >> rpt strip_tac >> gvs[]
QED

Theorem ifexp_function_member_name:
  !tops vis mut nr rr name args dflts ret stmts.
    MEM (FunctionDecl vis mut nr rr name args dflts ret stmts) tops ==>
    MEM name (supported_function_names tops)
Proof
  Induct_on `tops` >- simp[] >> rpt gen_tac >> Cases_on `h` >>
  simp[supported_function_names_def] >> metis_tac[]
QED

Theorem ifexp_build_func_info_distinct:
  !tops sft vis mut nr rr name args dflts ret stmts.
    ALL_DISTINCT (supported_function_names tops) /\ vis <> External /\
    MEM (FunctionDecl vis mut nr rr name args dflts ret stmts) tops ==>
    build_func_info sft tops name =
      compute_func_info (\n. MAP (FST o SND) (sft n)) ret
        (type_mem_bytes sft ret) (MAP SND args)
Proof
  Induct_on `tops` >- simp[] >> rpt gen_tac >> Cases_on `h` >>
  simp[supported_function_names_def, build_func_info_def] >>
  rpt strip_tac >> gvs[] >> rw[] >>
  metis_tac[ifexp_function_member_name]
QED

Theorem ifexp_deploy_info_map:
  !tops sft name fm nr args dflts ret body.
    lookup_function NONE name Internal tops = NONE /\
    lookup_function NONE name Deploy tops = SOME (fm,nr,args,dflts,ret,body) ==>
    build_func_info sft tops name =
      compute_func_info (\n. MAP (FST o SND) (sft n)) ret
        (type_mem_bytes sft ret) (MAP SND args)
Proof
  Induct_on `tops`
  >- simp[lookup_function_def, build_func_info_def, AllCaseEqs(),
          compute_func_info_def, returns_stack_count_def,
          compute_pass_via_stack_def] >>
  rpt gen_tac >> Cases_on `h` >>
  simp[lookup_function_def, build_func_info_def] >>
  rpt strip_tac >> gvs[AllCaseEqs()]
  >- (Cases_on `f` >> gvs[] >> metis_tac[]) >>
  Cases_on `v` >> gvs[lookup_function_def] >> metis_tac[]
QED

Theorem ifexp_callable_info_map:
  !tops sft deploying name fm nr args dflts ret body.
    ALL_DISTINCT (supported_function_names tops) /\
    lookup_callable_function deploying name tops = SOME (fm,nr,args,dflts,ret,body) ==>
    build_func_info sft tops name =
      compute_func_info (\n. MAP (FST o SND) (sft n)) ret
        (type_mem_bytes sft ret) (MAP SND args)
Proof
  rpt strip_tac >> gvs[lookup_callable_function_def, AllCaseEqs()]
  >- metis_tac[ifexp_deploy_info_map] >>
  drule lookup_function_Internal_SOME_MEM >> strip_tac >>
  irule ifexp_build_func_info_distinct >>
  goal_assum (drule_at Any) >> simp[] >>
  goal_assum (drule_at Any) >> simp[]
QED

Theorem ifexp_internal_call_info_bridge:
  !tops ctx ce cx env es ann id args drv sig.
    body_inv tops ctx ce cx /\
    expr_body_pre ce cx env (Call ann (IntCall id) args drv) es /\
    FLOOKUP env.fn_sigs id = SOME sig ==>
    ce.ce_func_info (nsid_to_string id) =
      compute_func_info
        (\n. MAP (FST o SND) (get_struct_fields ce.ce_struct_fields n))
        sig.ret_ty (type_memory_bytes ce sig.ret_ty) sig.param_types
Proof
  rpt strip_tac >>
  `ce.ce_func_info =
     build_func_info (get_struct_fields (make_struct_fields_map tops)) tops /\
   ce.ce_struct_fields = make_struct_fields_map tops /\
   supported_program tops /\ get_module_code cx NONE = SOME tops` by
    gvs[bodySimTheory.body_inv_def] >>
  `ALL_DISTINCT (supported_function_names tops)` by
    metis_tac[supportedProgramTheory.supported_program_def,
      supportedNamesTheory.supported_declaration_names_unique] >>
  `expr_sim_inv ce cx env es` by gvs[exprSimHypsDefsTheory.expr_body_pre_def] >>
  `FST id = NONE` by
    gvs[exprSimHypsDefsTheory.expr_body_pre_def, vyperTypeCallGraphTheory.int_calls_expr_def] >>
  `fn_sigs_consistent env.fn_sigs cx` by
    gvs[exprSimHypsDefsTheory.expr_sim_inv_def,
        vyperTypeInvariantsTheory.env_consistent_def,
        vyperTypeInvariantsTheory.env_context_consistent_def] >>
  PairCases_on `id` >> gvs[] >>
  qpat_x_assum `fn_sigs_consistent _ _` mp_tac >>
  rewrite_tac[vyperTypeInvariantsTheory.fn_sigs_consistent_def] >>
  disch_then drule >> strip_tac >> gvs[] >>
  simp[nsid_to_string_def] >>
  drule_all ifexp_callable_info_map >>
  disch_then (qspec_then `get_struct_fields (make_struct_fields_map tops)` mp_tac) >>
  `type_mem_bytes (get_struct_fields (make_struct_fields_map tops)) sig.ret_ty =
   type_memory_bytes ce sig.ret_ty` by
    metis_tac[type_mem_bytes_type_memory_bytes] >> simp[]
QED

Theorem ifexp_internal_call_buffer_extent:
  !tops ctx ce cx env es ann id args drv rc rbs pvs.
    body_inv tops ctx ce cx /\
    expr_body_pre ce cx env (Call ann (IntCall id) args drv) es /\
    ce.ce_func_info (nsid_to_string id) = (rc,rbs,pvs) /\
    rc = 0 /\ 0 < rbs ==>
    rbs = type_memory_bytes ce (ce.ce_func_return_type (nsid_to_string id))
Proof
  rpt strip_tac >>
  `?sig. FLOOKUP env.fn_sigs id = SOME sig` by
    (Cases_on `id` >>
     gvs[exprSimHypsDefsTheory.expr_body_pre_def,
         vyperTypeSystemTheory.well_typed_expr_def,
         optionTheory.IS_SOME_EXISTS]) >>
  drule_all ifexp_internal_call_info_bridge >> strip_tac >>
  drule_all ifexp_internal_call_return_bridge >> strip_tac >>
  gvs[] >> drule ifexp_compute_func_info_buffer_size >> simp[]
QED

Theorem ifexp_internal_call_zero_extent:
  !tops ctx ce cx env es ann id args drv pvs.
    body_inv tops ctx ce cx /\
    expr_body_pre ce cx env (Call ann (IntCall id) args drv) es /\
    ce.ce_func_info (nsid_to_string id) = (0,0,pvs) ==>
    ce.ce_func_return_type (nsid_to_string id) = NoneT \/
    type_memory_bytes ce (ce.ce_func_return_type (nsid_to_string id)) = 0
Proof
  rpt strip_tac >>
  `?sig. FLOOKUP env.fn_sigs id = SOME sig` by
    (Cases_on `id` >>
     gvs[exprSimHypsDefsTheory.expr_body_pre_def,
         vyperTypeSystemTheory.well_typed_expr_def,
         optionTheory.IS_SOME_EXISTS]) >>
  drule_all ifexp_internal_call_info_bridge >> strip_tac >>
  drule_all ifexp_internal_call_return_bridge >> strip_tac >>
  gvs[] >> drule ifexp_compute_func_info_zero_size >> simp[]
QED
