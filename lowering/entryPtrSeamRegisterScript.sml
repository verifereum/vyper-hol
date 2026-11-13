(*
 * Seam of external_entry_reaches_body_ptr (loweringPtrCorrect): the
 * selected external function's argument registration
 * (compile_register_positional_args: per parameter an ALLOCA buffer and
 * compile_decode_args from calldata into it), run from the state the entry
 * checks leave, reaches the guarded body's start s0 with
 *   - the S1 relation there (stmt_state_rel, as loweringRuntimeCorrect's
 *     admitted external_entry_reaches_body states it, here at the state the
 *     run actually reaches), and
 *   - a ghost (G0, tn0) in ghost_inv NONE: each parameter's pointer covered
 *     by its ALLOCA and its value robust to the tainted bytes,
 * with safety of the run from s0 giving safety from the registration's
 * start, for any dead-byte bound D.
 *
 * The start state s1 and its ghost (G1, tn1) are what
 * entryPtrSeamPrefix's external_entry_reaches_registration_ptr provides.
 *)
Theory entryPtrSeamRegister
Ancestors
  sourceOwnedCoherentPtr sourceOwnedComplexPtr sourceOwnedArrayConstructorPtr decoderArrayInitPtr entryPtrSeamDecoder entryDecoderBudgetBoundary actualDecoderAllocationPtr actualAllocaReplayPtr
  actualAllocSitesCredit acceptedContextPhi sourceWordDecoderPtr sourceBytesRepresentation
  sourceEncodingWindows sourceEncodingLayout sourcePrimitiveMemberPtr sourcePrimitiveReentryPtr canonicalMemberTraversalPtr sourcePrimitiveComplexPtr sourceRecursiveComplexPtr
  entryStateRel entryArgPtrs entryLocals registrationGuardPtr
  entryDecodePlanProps entryDecodeProps bodySimEntry actualRegistrationCode
  vyperCompiler moduleLoweringProps exprLoweringProps vyperInterpreter
  vyperContext venomExecSemantics venomState compileEnv loweringStateRelDefs supportedProgram
  fragExec venomInst ptrDiscipline ptrSafeRun vyperLoweringCorrect
  loweringRuntimeCorrect bodyPtrDefs moduleLowering venomWf
  list rich_list selectorDispatch byte contractABI vyperABIRoundtrip
  valueEncoding valueEncodingDefs entryDispatchProps ctorDeployInitcode abiCallerBuiltinInput compileVyper
  ctorDeployMemoryFrontier registrationSizeAdmissibility argumentRegistrationOpen

(* Supported checked source excludes all runtime DALLOCA producers.  This
   rules out the proposed near-limit source family before budgeting it. *)
Theorem registration_supported_no_dalloca:
  lower_vyper_runtime_unit tops rpolicy = SOME unit /\
  supported_program tops /\ source_typing_ok tops am tx ==>
  ~ctx_has_dalloca unit.cu_context
Proof
  strip_tac >>
  `raw_shape_free_program tops` by
    metis_tac[loweringShapeSourceTheory.supported_program_raw_shape_free_program] >>
  `o1_source_unit_ok unit` by
    (fs[e2eDefsTheory.source_typing_ok_def] >>
     drule_all lower_vyper_runtime_unit_source_unit_ok >> simp[]) >>
  metis_tac[o1PipelineCorrectTheory.o1_source_unit_ok_no_dalloca]
QED

Theorem registration_fmp_room_necessary:
  fmp_room ctx fn s /\
  (EXISTS (\inst. inst.inst_opcode = DALLOCA) (fn_insts fn) \/
   (?g f. TC (fn_directly_calls ctx) fn.fn_name g /\
     MEM f ctx.ctx_functions /\ f.fn_name = g /\
     EXISTS (\inst. inst.inst_opcode = DALLOCA) (fn_insts f))) ==>
  s.vs_alloca_next + pending_alloca_size fn s +
    CARD {g | TC (fn_directly_calls ctx) fn.fn_name g} *
      unit_alloca_frame ctx + 2 ** 65 < dimword (:256)
Proof
  simp[fmp_room_def] >> rpt strip_tac >>
  qpat_x_assum `_ ==> _` mp_tac >>
  (impl_tac >- metis_tac[]) >> strip_tac >> decide_tac
QED

Theorem registration_noop_or_open:
  !args ce off st ce' sa.
    compile_register_positional_args ce args off st = (ce',sa) ==>
    sa = st \/ ~block_is_terminated sa
Proof
  Induct >- simp[compile_register_positional_args_def, comp_return_def] >>
  PairCases >> rpt gen_tac >>
  simp[compile_register_positional_args_def, vyperMiscTheory.option_CASE_rator,
       AllCaseEqs(), comp_bind_def, comp_ignore_bind_def, comp_return_def] >>
  rpt strip_tac >> rpt (pairarg_tac >> gvs[]) >>
  first_x_assum (drule_then strip_assume_tac) >> gvs[] >>
  disj2_tac >>
  irule compile_decode_args_open >>
  goal_assum $ drule_at (Pat `compile_decode_args _ _ _ _ _ _ _ = _`) >>
  simp[is_terminator_def] >>
  irule exprOpenPrimitivesTheory.compile_alloc_buffer_open >>
  goal_assum $ drule_at Any
QED

Theorem registration_absent_cursor_safe:
  ~(?bb inst. lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
              get_instruction bb s.vs_inst_idx = SOME inst) ==>
  !D lo fuel ctx PG G tn. ptr_safe_run D lo fuel ctx fn PG G tn s
Proof
  strip_tac >> rpt gen_tac >>
  Cases_on `lookup_block s.vs_current_bb fn.fn_blocks` >>
  simp[ptr_safe_run_def] >>
  Cases_on `get_instruction x s.vs_inst_idx` >>
  gvs[ptr_safe_run_def, Once ptr_safe_defs]
QED

Theorem registration_cursor_active_or_safe_if_terminal:
  compile_register_positional_args ce args off st = (ce',sa) /\
  fn_has_code st sa fn /\
  s.vs_current_bb = st.cs_current_bb /\
  s.vs_inst_idx = LENGTH st.cs_current_insts /\
  (!lbl bb. lookup_block lbl fn.fn_blocks = SOME bb ==>
    bb.bb_instructions <> [] /\
    is_terminator (LAST bb.bb_instructions).inst_opcode) ==>
  (?bb inst. lookup_block sa.cs_current_bb fn.fn_blocks = SOME bb /\
    get_instruction bb (LENGTH sa.cs_current_insts) = SOME inst) \/
  (!D lo fuel ctx PG G tn. ptr_safe_run D lo fuel ctx fn PG G tn s)
Proof
  strip_tac >> drule registration_noop_or_open >> strip_tac
  >- (gvs[] >>
      Cases_on `?bb inst. lookup_block sa.cs_current_bb fn.fn_blocks = SOME bb /\
        get_instruction bb (LENGTH sa.cs_current_insts) = SOME inst`
      >- simp[] >>
      disj2_tac >> irule registration_absent_cursor_safe >> metis_tac[]) >>
  disj1_tac >> fs[fn_has_code_def] >>
  first_x_assum drule >> strip_tac >>
  `LENGTH sa.cs_current_insts < LENGTH bb.bb_instructions` by
    (fs[IS_PREFIX_APPEND] >>
     Cases_on `l` >> gvs[block_is_terminated_def] >>
     Cases_on `sa.cs_current_insts` >> gvs[]) >>
  simp[get_instruction_def]
QED

(* Source lookup selects a declaration whose original byte sizes were checked. *)
Theorem registration_external_allocs_ok:
  lower_vyper_runtime_unit tops rpolicy = SOME unit /\
  supported_program tops /\ name <> "__default__" /\
  lookup_function NONE name External tops =
    SOME (mut,nr,args,defaults,ret,fbody) ==>
  ?rr:bool. fn_allocs_ok tops (mut,nr,rr,name,args,defaults,ret,fbody)
Proof
  strip_tac >>
  `supported_declaration_headers tops` by fs[supported_program_def] >>
  drule_all supported_headers_external_member >> strip_tac >>
  Cases_on `classify_functions tops` >> PairCases_on `r` >> gvs[] >>
  qexists_tac `rr` >> irule lower_vyper_runtime_unit_allocs_ok >>
  metis_tac[]
QED

(* Argument registration starts before any allocation or memory write. *)
Theorem registration_start_resources:
  initial_venom_state_rel tops am tx vs /\
  vars_pc_only vs s ==>
  s.vs_allocas = FEMPTY /\ s.vs_alloca_next = 0 /\
  s.vs_memory = [] /\ alloca_inv s /\ allocas_from lower s /\
  s.vs_call_ctx = vs.vs_call_ctx
Proof
  simp[initial_venom_state_rel_def, vars_pc_only_def,
       venom_state_component_equality] >>
  rpt strip_tac >>
  simp[venomMemDefsTheory.alloca_inv_def,
       venomMemDefsTheory.allocas_non_overlapping_def,
       venomMemDefsTheory.alloca_next_valid_def, allocas_from_def]
QED

(* The logical entry relations do not constrain the code-generator's
   initial free-memory-pointer field. *)
Theorem registration_stmt_initial_fmp:
  stmt_state_rel ctx func cenv cx es (s with vs_initial_fmp := w) <=>
  stmt_state_rel ctx func cenv cx es s
Proof
  simp[stmt_state_rel_def, state_rel_def, immutable_base_zero_alt,
       immutable_alloca_sep_def, immutable_decl_sep_def,
       local_ptrs_rel_def, local_region_def,
       local_backed_def, lookup_var_def, storage_rel_def, transient_rel_def,
       immutables_rel_def, logs_rel_def, call_ctx_rel_def, accounts_rel_def,
       contract_storage_def, contract_transient_def,
       venomMemDefsTheory.alloca_inv_def,
       venomMemDefsTheory.allocas_non_overlapping_def,
       venomMemDefsTheory.alloca_next_valid_def,
       alloca_room_def, pending_alloca_size_def, fmp_room_def]
QED

Theorem registration_ghost_initial_fmp:
  ghost_inv d cenv cx es G tn (s with vs_initial_fmp := w) <=>
  ghost_inv d cenv cx es G tn s
Proof
  Cases_on `d` >- simp[ghost_inv_def, return_buf_ptr_def,
    ptr_covers_def, lookup_var_def, stor_taint_ok_def] >>
  PairCases_on `x` >>
  simp[ghost_inv_def, ptr_covers_def, return_buf_ptr_def,
       lookup_var_def, stor_taint_ok_def]
QED

Theorem registration_active_dalloca_obstruction:
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  get_instruction bb s.vs_inst_idx = SOME inst /\
  ctx_has_dalloca ctx /\ ~allocas_below_fmp s ==>
  ~ptr_safe_run D lo fuel ctx fn PG G tn s
Proof
  strip_tac >>
  simp[ptr_safe_run_def, Once ptr_safe_block_def, ptr_safe_step_def,
       ptr_inst_ok_def]
QED

Theorem registration_dalloca_vacuous_continuation:
  ctx_has_dalloca ctx /\
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  get_instruction bb s.vs_inst_idx = SOME inst /\
  w2n s.vs_fmp + 1 < dimword (:256) ==>
  !D. ~(!fuel. ptr_safe_run D lo fuel ctx fn PG G tn
    (s with vs_initial_fmp := n2w (w2n s.vs_fmp + 1)))
Proof
  strip_tac >> gen_tac >> strip_tac >>
  `~allocas_below_fmp
     (s with vs_initial_fmp := n2w (w2n s.vs_fmp + 1))` by
    simp[allocas_below_fmp_def] >>
  qpat_x_assum `!fuel. _` (qspec_then `0` mp_tac) >>
  simp[ptr_safe_run_def, Once ptr_safe_block_def, ptr_safe_step_def,
       ptr_inst_ok_def]
QED

Theorem registration_empty_frontier:
  lowering_context_ok ctx /\ ctx.ctx_entry = SOME name /\
  lookup_function name ctx.ctx_functions = SOME fn /\ s.vs_alloca_next = 0 ==>
  alloca_frontier_inv ctx fn site s /\ unit_alloca_budget ctx < dimword (:256)
Proof
  strip_tac >> drule_all ctorDeployMemoryFrontierTheory.lowered_unit_entry_facts >> strip_tac >>
  `fn.fn_name = name /\ MEM fn ctx.ctx_functions` by
    metis_tac[lookup_function_result_name, lookup_function_MEM] >>
  `fcg_is_reachable (fcg_analyze ctx) name` by
    (irule fcgCorrectnessProofTheory.fcg_analyze_reachable_complete_proof >>
     simp[fcgDefsTheory.fcg_path_def, venomInstTheory.ctx_fn_names_def] >>
     metis_tac[lookup_function_mem]) >>
  reverse conj_tac
  >- (fs[lowering_context_ok_def] >> decide_tac) >>
  simp[allocaFrontierBoundTheory.alloca_frontier_inv_def] >> conj_tac
  >- (rpt strip_tac >>
      `reachable_fcg_acyclic ctx (fcg_analyze ctx)` by
        fs[lowering_context_ok_def] >>
      `fcg_is_reachable (fcg_analyze ctx) g` by
        metis_tac[fcgPostorderTheory.reachable_fcg_acyclic_tc_rank] >>
      metis_tac[fcgPostorderTheory.reachable_fcg_acyclic_no_reachable_cycle]) >>
  simp_tac bool_ss [unit_alloca_budget_def, LET_THM] >>
  qmatch_goalsub_abbrev_tac `CARD below * frame + r <= (1+n)*frame` >>
  `r <= frame` by
    simp[Abbr `r`, Abbr `frame`, allocaFrontierBoundTheory.remaining_alloca_budget_frame] >>
  `CARD below <= n` by
    simp[Abbr `below`, Abbr `n`, allocaFrontierBoundTheory.call_targets_card] >>
  `CARD below * frame <= n * frame` by (irule arithmeticTheory.LESS_MONO_MULT >> simp[]) >>
  full_simp_tac bool_ss [arithmeticTheory.RIGHT_ADD_DISTRIB,
    arithmeticTheory.MULT_LEFT_1] >> decide_tac
QED

Theorem registration_runtime_acceptance:
  lower_vyper_runtime_unit tops policy = SOME unit ==>
  lowering_context_ok unit.cu_context /\ unit.cu_context.ctx_entry = SOME "__entry"
Proof
  metis_tac[vyperLoweringCorrectTheory.lower_vyper_runtime_unit_context_entry]
QED

Theorem registration_initial_ptr_resources:
  lower_vyper_runtime_unit tops policy = SOME unit /\
  initial_venom_state_rel tops am tx vs /\
  vars_pc_only (vs with <| vs_prev_bb := NONE; vs_current_bb := elbl;
    vs_inst_idx := 0 |>) s /\
  lookup_function "__entry" unit.cu_context.ctx_functions = SOME fn /\
  ~ctx_has_dalloca unit.cu_context ==>
  s.vs_allocas = FEMPTY /\ s.vs_alloca_next = 0 /\ s.vs_memory = [] /\
  alloca_inv s /\ allocas_from 0 s /\ s.vs_call_ctx = vs.vs_call_ctx /\
  alloca_frontier_inv unit.cu_context fn site s /\
  unit_alloca_budget unit.cu_context < dimword (:256) /\
  (!label bb. lookup_block label fn.fn_blocks = SOME bb ==>
    phi_prefix_length bb.bb_instructions = 0)
Proof
  strip_tac >>
  `vars_pc_only vs s` by
    gvs[vars_pc_only_def, venom_state_component_equality] >>
  drule_all registration_start_resources >>
  disch_then (qspec_then `0` strip_assume_tac) >>
  drule registration_runtime_acceptance >> strip_tac >>
  drule_all registration_empty_frontier >>
  disch_then (qspec_then `site` strip_assume_tac) >>
  asm_rewrite_tac [] >> rpt strip_tac >>
  irule acceptedContextPhiTheory.lowering_context_ok_block_phi >>
  goal_assum (drule_at Any) >> goal_assum (drule_at Any) >>
  asm_rewrite_tac [] >> qexists_tac `"__entry"` >> asm_rewrite_tac []
QED

Theorem registration_package_inputs:
  ALL_DISTINCT (FLAT (MAP (type_def_keys_toplevel (NONE:num option)) tops)) /\
  ALL_DISTINCT (MAP FST args) /\
  set_external_package_target target
    (package_external_fn tops ut nk (mut,nr,rr,name,args,dflts,ret,fbody)) =
    (lbl,ce,pos,mincd,pay,nr',key,ut',iv,fbody',rt) ==>
  pos = build_positional_args ce args /\ dec_cenv_agrees ce (type_env tops) /\
  EVERY (\a. ?off. FLOOKUP ce.ce_vars (FST a) =
    SOME (MemLoc off (type_memory_bytes ce (SND a)))) args /\
  (!k. ~MEM k (MAP FST args) ==> FLOOKUP ce.ce_vars k = NONE)
Proof
  strip_tac >>
  Cases_on `package_external_fn tops ut nk (mut,nr,rr,name,args,dflts,ret,fbody)` >>
  PairCases_on `r` >> gvs[set_external_package_target_def] >>
  drule_all package_external_fn_dec_cenv_agrees >> strip_tac >>
  drule_all package_external_fn_vars >> strip_tac >>
  `!ty. type_memory_bytes (r0 with ce_target := target) ty = type_memory_bytes r0 ty` by
    (gen_tac >> irule type_memory_bytes_struct_fields >> simp[]) >>
  `build_positional_args (r0 with ce_target := target) args = build_positional_args r0 args` by
    (irule build_positional_args_layout_cong >> simp[]) >>
  gvs[dec_cenv_agrees_def]
QED

Theorem registration_package_decoder_layout:
  set_external_package_target target
    (package_external_fn tops ut nk
      (mut,nr,rr,name,args,dflts,ret,fbody)) =
    (lbl,ce,pos,mincd,pay,nr',key,ut',iv,fbody',rt) ==>
  ce.ce_struct_fields =
    (build_compile_env tops External mut name args ret fbody ut).ce_struct_fields /\
  ce.ce_flag_n_members =
    (build_compile_env tops External mut name args ret fbody ut).ce_flag_n_members
Proof
  simp[package_external_fn_def, set_external_package_target_def,
       update_cenv_nonreentrant_def] >>
  Cases_on `ret = NoneT` >>
  simp[update_cenv_ret_abi_def] >> strip_tac >> gvs[]
QED

Theorem registration_package_coherent:
  contract_namespaces_ok dep [((NONE:num option),tops)] /\
  assignable_type (type_env tops) ty /\
  evaluate_type (type_env tops) ty = SOME tv /\
  set_external_package_target target
    (package_external_fn tops ut nk
      (mut,nr,rr,name,args,dflts,ret,fbody)) =
    (lbl,ce,pos,mincd,pay,nr',key,ut',iv,fbody',rt) ==>
  abi_decoder_coherent ce (type_env tops) ce.ce_struct_fields ty tv
Proof
  strip_tac >> drule registration_package_decoder_layout >> strip_tac >>
  irule abiDecoderCoherenceTheory.abi_decoder_coherent_layout_transport >>
  qexists_tac `build_compile_env tops External mut name args ret fbody ut` >>
  simp[] >> irule abi_caller_coherent >> metis_tac[]
QED

Theorem registration_bound_parameters:
  abi_caller_metadata ce env /\
  abi_caller_struct_map ce.ce_struct_fields env /\
  EVERY (assignable_type env) (MAP SND params) /\
  bind_arguments env params vs = SOME scope ==>
  ?tvs.
    LIST_REL (abi_decoder_coherent ce env ce.ce_struct_fields)
      (MAP SND params) tvs /\
    LIST_REL value_has_type tvs vs
Proof
  strip_tac >> drule bind_arguments_values_typed >> strip_tac >>
  qexists_tac `tvs` >>
  reverse conj_tac
  >- gvs[vyperTypeDefaultsTheory.values_have_types_LIST_REL] >>
  drule abi_caller_coherent_from_metadata >> strip_tac >>
  first_x_assum irule >> simp[]
QED

Theorem registration_source_parameter_inputs:
  supported_program tops /\ source_typing_ok tops am tx /\
  lookup_function NONE tx.function_name External tops =
    SOME (mut,F,args,[],ret,fbody) /\
  bind_arguments (type_env tops) args tx.args = SOME scope /\
  set_external_package_target target
    (package_external_fn tops ut nk (mut,F,rr,tx.function_name,args,[],ret,fbody)) =
    (lbl,ce,pos,mincd,pay,nr',key,ut',iv,fbody',rt) ==>
  ALL_DISTINCT (MAP FST args) /\ pos = build_positional_args ce args /\
  dec_cenv_agrees ce (type_env tops) /\
  (!k. ~MEM k (MAP FST args) ==> FLOOKUP ce.ce_vars k = NONE) /\
  ?tvs.
    LIST_REL (\ty tv. evaluate_type (type_env tops) ty = SOME tv)
      (MAP SND args) tvs /\
    LIST_REL (abi_decoder_coherent ce (type_env tops) ce.ce_struct_fields)
      (MAP SND args) tvs /\
    LIST_REL value_has_type tvs tx.args /\
    (!i. i < LENGTH args ==> ?off.
      FLOOKUP ce.ce_vars (FST (EL i args)) =
        SOME (MemLoc off (type_memory_size (EL i tvs))))
Proof
  strip_tac >>
  `params_ok (type_env tops) args` by suspend "params" >>
  `contract_namespaces_ok F [((NONE:num option),tops)]` by
    (fs[e2eDefsTheory.source_typing_ok_def] >>
     drule vyperTypeContractContextTheory.check_contract_namespaces_ok >> simp[]) >>
  `ALL_DISTINCT (FLAT (MAP (type_def_keys_toplevel (NONE:num option)) tops))` by
    metis_tac[source_typing_ok_type_def_keys_distinct] >>
  `ALL_DISTINCT (MAP FST args)` by fs[vyperTypeContractTheory.params_ok_def] >>
  drule_all registration_package_inputs >> strip_tac >>
  asm_rewrite_tac [] >>
  drule bind_arguments_values_typed >> strip_tac >>
  qexists_tac `tvs` >> asm_rewrite_tac [] >>
  conj_tac >- suspend "coherent" >>
  conj_tac >- gvs[vyperTypeDefaultsTheory.values_have_types_LIST_REL] >>
  rpt strip_tac >>
  `MEM (EL i args) args` by simp[EL_MEM] >>
  `?off. FLOOKUP ce.ce_vars (FST (EL i args)) =
    SOME (MemLoc off (type_memory_bytes ce (SND (EL i args))))` by
    fs[EVERY_MEM] >>
  qexists_tac `off` >> asm_rewrite_tac [] >> AP_TERM_TAC >> AP_TERM_TAC >>
  fs[dec_cenv_agrees_def, LIST_REL_EL_EQN] >>
  first_x_assum irule >> simp[EL_MAP] >>
  qpat_x_assum `!n. n < LENGTH args ==> _`
    (qspec_then `i` mp_tac) >> simp[EL_MAP]
QED

Resume registration_source_parameter_inputs[params]:
  `supported_declaration_headers tops` by fs[supported_program_def] >>
  drule_all source_typing_ok_params_ok >> simp[]
QED

Resume registration_source_parameter_inputs[coherent]:
  fs[LIST_REL_EL_EQN] >> rpt strip_tac >>
  `evaluate_type (type_env tops) (EL n (MAP SND args)) = SOME (EL n tvs)` by
    (first_x_assum irule >> simp[]) >>
  `assignable_type (type_env tops) (EL n (MAP SND args))` by
    (fs[vyperTypeContractTheory.params_ok_def, EVERY_MEM] >>
     qpat_x_assum `!e. MEM e args ==> (\(nm,ty). assignable_type (type_env tops) ty) e`
       (qspec_then `EL n args` mp_tac) >>
     simp[EL_MEM, EL_MAP] >> Cases_on `EL n args` >> simp[]) >>
  drule_all registration_package_coherent >> simp[]
QED

Finalise registration_source_parameter_inputs

Theorem registration_owned_entry_inputs:
  lower_vyper_runtime_unit tops rpolicy = SOME unit /\
  supported_program tops /\ source_typing_ok tops am tx /\
  valid_vyper_call tops tx vs.vs_call_ctx.cc_calldata ret /\
  initial_venom_state_rel tops am tx vs /\
  lookup_function NONE tx.function_name External tops =
    SOME (mut,F,args,[],ret,fbody) /\
  bind_arguments (type_env tops) args tx.args = SOME scope /\
  set_external_package_target target
    (package_external_fn tops ut nk (mut,F,rr,tx.function_name,args,[],ret,fbody)) =
    (lbl,ce,pos,mincd,pay,nr',key,ut',iv,fbody',rt) /\
  vars_pc_only (vs with <| vs_prev_bb := NONE; vs_current_bb := elbl;
    vs_inst_idx := 0 |>) s /\
  lookup_function "__entry" unit.cu_context.ctx_functions = SOME fn /\
  ~ctx_has_dalloca unit.cu_context ==>
  ALL_DISTINCT (MAP FST args) /\ pos = build_positional_args ce args /\
  dec_cenv_agrees ce (type_env tops) /\
  (!k. ~MEM k (MAP FST args) ==> FLOOKUP ce.ce_vars k = NONE) /\
  s.vs_allocas = FEMPTY /\ s.vs_alloca_next = 0 /\ s.vs_memory = [] /\
  alloca_inv s /\ allocas_from 0 s /\ s.vs_call_ctx = vs.vs_call_ctx /\
  alloca_frontier_inv unit.cu_context fn site s /\
  unit_alloca_budget unit.cu_context < dimword (:256) /\
  (!label bb. lookup_block label fn.fn_blocks = SOME bb ==>
    phi_prefix_length bb.bb_instructions = 0) /\
  calldata_encodes (type_env tops) tx.function_name (MAP SND args)
    tx.args vs.vs_call_ctx.cc_calldata /\
  LENGTH vs.vs_call_ctx.cc_calldata < dimword (:256) /\
  ?tvs.
    LIST_REL (\ty tv. evaluate_type (type_env tops) ty = SOME tv)
      (MAP SND args) tvs /\
    LIST_REL (abi_decoder_coherent ce (type_env tops) ce.ce_struct_fields)
      (MAP SND args) tvs /\
    LIST_REL value_has_type tvs tx.args /\
    (!i. i < LENGTH args ==> ?off.
      FLOOKUP ce.ce_vars (FST (EL i args)) =
        SOME (MemLoc off (type_memory_size (EL i tvs)))) /\
    (!i. i < LENGTH args ==>
      type_memory_size (EL i tvs) < dimword (:256))
Proof
  strip_tac >>
  drule_all registration_source_parameter_inputs >> strip_tac >>
  drule_all registration_initial_ptr_resources >>
  disch_then (qspec_then `site` strip_assume_tac) >>
  `calldata_encodes (type_env tops) tx.function_name (MAP SND args)
     tx.args vs.vs_call_ctx.cc_calldata` by
    gvs[e2eDefsTheory.valid_vyper_call_def] >>
  `LENGTH vs.vs_call_ctx.cc_calldata < dimword (:256)` by
    (fs[initial_venom_state_rel_def, venom_env_rel_def, call_ctx_rel_def,
        e2eDefsTheory.source_typing_ok_def,
        vyperTypeContractSoundnessTheory.call_tx_well_typed_def] >>
     gvs[wordsTheory.dimword_def]) >>
  asm_rewrite_tac [] >> qexists_tac `tvs` >> asm_rewrite_tac [] >>
  `tx.function_name <> "__default__"` by fs[e2eDefsTheory.valid_vyper_call_def] >>
  drule_all registration_external_allocs_ok >> strip_tac >>
  `ALL_DISTINCT (FLAT (MAP (type_def_keys_toplevel (NONE:num option)) tops))` by
    metis_tac[source_typing_ok_type_def_keys_distinct] >>
  rpt strip_tac >>
  `evaluate_type (type_env tops) (SND (EL i args)) = SOME (EL i tvs)` by
    (fs[LIST_REL_EL_EQN, EL_MAP] >> metis_tac[]) >>
  `type_memory_size (EL i tvs) < 2 ** 64` by
    (irule registration_parameter_memory_limit >>
     goal_assum (drule_at Any) >> simp[] >>
     goal_assum (drule_at Any) >> simp[] >>
     qexists_tac `FST (EL i args)` >> simp[EL_MEM]) >>
  `2 ** 64 < dimword (:256)` by
    (rewrite_tac[wordsTheory.dimword_def, fcpTheory.index_bit0,
       fcpTheory.finite_bit0, fcpTheory.index_one, fcpTheory.finite_one] >>
     EVAL_TAC) >> decide_tac
QED

(* A selected argument occupies its canonical tuple window, including dynamic
   tails.  This source-only interface is independent of execution resources. *)
Theorem registration_calldata_argument:
  calldata_encodes env fname tys vs cd /\
  LIST_REL (abi_decoder_coherent ce env sf) tys tvs /\
  LIST_REL value_has_type tvs vs /\
  LENGTH cd < dimword (:256) /\ i < LENGTH tys ==>
  ?avs.
    vyper_to_abi_list env tys vs = SOME avs /\
    vyper_to_abi env (EL i tys) (EL i vs) = SOME (EL i avs) /\
    value_has_type (EL i tvs) (EL i vs) /\
    abi_decoder_coherent ce env sf (EL i tys) (EL i tvs) /\
    mem_bytes_at
      (4 + abi_tuple_child_offset (MAP (vyper_to_abi_type env) tys) avs i)
      (LENGTH (enc (vyper_to_abi_type env (EL i tys)) (EL i avs))) cd =
      enc (vyper_to_abi_type env (EL i tys)) (EL i avs) /\
    4 + abi_tuple_child_offset (MAP (vyper_to_abi_type env) tys) avs i +
      LENGTH (enc (vyper_to_abi_type env (EL i tys)) (EL i avs)) <
      dimword (:256)
Proof
  strip_tac >>
  `LENGTH tys = LENGTH vs` by metis_tac[LIST_REL_LENGTH] >>
  fs[calldata_encodes_def, GSYM abiDecoderMembersTheory.vyper_to_abi_types_MAP,
     Excl "enc_def"] >>
  `TAKE (LENGTH vs) tys = tys` by
    metis_tac[TAKE_LENGTH_ID] >>
  fs[abiDecoderMembersTheory.vyper_to_abi_types_MAP, Excl "enc_def",
     Excl "TAKE_LENGTH_ID_rwt2"] >>
  drule_all coherent_source_list_head_lengths >> strip_tac >>
  `mem_bytes_at 4
    (LENGTH (enc (Tuple (MAP (vyper_to_abi_type env) tys)) (ListV abi_vals)))
    (function_selector fname (MAP (vyper_to_abi_type env) tys) ++
      enc (Tuple (MAP (vyper_to_abi_type env) tys)) (ListV abi_vals)) =
    enc (Tuple (MAP (vyper_to_abi_type env) tys)) (ListV abi_vals)` by
    simp[mem_bytes_at_def, DROP_APPEND2, function_selector_length,
         TAKE_LENGTH_APPEND] >>
  `i < LENGTH (MAP (vyper_to_abi_type env) tys)` by simp[] >>
  drule_all structural_tuple_indexed_source >>
  simp[EL_MAP, function_selector_length, Excl "enc_def"] >> strip_tac >>
  drule vyper_to_abi_list_EL >> strip_tac >>
  gvs[LIST_REL_EL_EQN, function_selector_length, Excl "enc_def"] >>
  simp[] >> decide_tac
QED

Theorem registration_calldata_index_ready:
  calldata_encodes env fname tys vs s.vs_call_ctx.cc_calldata /\
  LIST_REL (abi_decoder_coherent ce env sf) tys tvs /\
  LIST_REL value_has_type tvs vs /\
  LENGTH s.vs_call_ctx.cc_calldata < dimword (:256) /\ i < LENGTH tys /\
  h = SUM (MAP abi_member_head_size (TAKE i (MAP (vyper_to_abi_type env) tys))) ==>
  ?av delta srcpos.
    vyper_to_abi env (EL i tys) (EL i vs) = SOME av /\
    value_has_type (EL i tvs) (EL i vs) /\
    abi_decoder_coherent ce env sf (EL i tys) (EL i tvs) /\
    mem_bytes_at srcpos (LENGTH (enc (vyper_to_abi_type env (EL i tys)) av))
      s.vs_call_ctx.cc_calldata = enc (vyper_to_abi_type env (EL i tys)) av /\
    srcpos + LENGTH (enc (vyper_to_abi_type env (EL i tys)) av) < dimword (:256) /\
    srcpos = 4 + (if is_dynamic (vyper_to_abi_type env (EL i tys)) then delta else h) /\
    (is_dynamic (vyper_to_abi_type env (EL i tys)) ==>
      abi_decode_load CALLDATALOAD (n2w (4+h) : bytes32) s = n2w delta /\
      4+delta < dimword (:256))
Proof
  strip_tac >> drule_all registration_calldata_argument >> strip_tac >>
  qexistsl_tac [`EL i avs`, `abi_tuple_child_offset (MAP (vyper_to_abi_type env) tys) avs i`,
    `4 + abi_tuple_child_offset (MAP (vyper_to_abi_type env) tys) avs i`] >>
  asm_rewrite_tac [] >>
  reverse conj_tac
  >- suspend "dynamic_load" >>
  simp[abiDecoderMemberSliceTheory.abi_tuple_child_offset_def, EL_MAP]
QED

Resume registration_calldata_index_ready[dynamic_load]:
  strip_tac >>
  `LENGTH tys = LENGTH vs` by metis_tac[LIST_REL_LENGTH] >>
  `TAKE (LENGTH vs) tys = tys` by metis_tac[TAKE_LENGTH_ID] >>
  fs[calldata_encodes_def, abiDecoderMembersTheory.vyper_to_abi_types_MAP,
    Excl "enc_def", Excl "TAKE_LENGTH_ID_rwt2"] >>
  drule_all coherent_source_list_head_lengths >> strip_tac >>
  once_rewrite_tac [arithmeticTheory.ADD_COMM] >>
  irule canonicalMemberTraversalPtrTheory.structural_tuple_indexed_offset_load >>
  simp[abiDecoderContractTheory.abi_decode_source_def, EL_MAP, Excl "enc_def"] >>
  gvs[mem_bytes_at_def, function_selector_length, DROP_APPEND2,
    TAKE_LENGTH_APPEND, Excl "enc_def"]
QED

Finalise registration_calldata_index_ready

(* Exact preparation instructions: dynamic offsets are tuple-relative. *)
Theorem registration_aggregate_prepare_phases:
  compile_register_positional_args ce [(name,F,dyn,sz,di)] off st = (ce',last) /\
  FLOOKUP ce.ce_vars name = SOME loc /\
  var_location_memory_size loc = SOME n ==>
  ?buf a src first.
    compile_alloc_buffer n st = (buf,a) /\
    ce' = ce with ce_vars updated_by
      (\m. m |+ (name,PtrVar buf.buf_operand n)) /\
    (if dyn then
       ?head b delta c g.
         emit_op ADD [Lit 4w; Lit (n2w (off-4))] a = (head,b) /\
         emit_op CALLDATALOAD [head] b = (delta,c) /\
         emit_op ADD [Lit 4w; delta] c = (src,g) /\
         compile_abi_arg_ptr_guard CALLDATALOAD src (Lit 4w) g = ((),first)
     else emit_op ADD [Lit 4w; Lit (n2w (off-4))] a = (src,first)) /\
    compile_abi_decode_to_buf buf.buf_operand src CALLDATALOAD
      (Lit 0w) (Lit 0w) di first = ((),last)
Proof
  strip_tac >>
  qpat_x_assum `compile_register_positional_args _ _ _ _ = _` mp_tac >>
  simp[compile_register_positional_args_def, comp_bind_def,
       comp_ignore_bind_def, comp_return_def] >>
  rpt (pairarg_tac >> fs[]) >> strip_tac >> gvs[] >>
  qpat_x_assum `compile_decode_args _ _ _ _ _ _ _ = _` mp_tac >>
  simp[compile_decode_args_def, finite_mapTheory.FLOOKUP_UPDATE,
       var_location_decode_operand_def, comp_bind_def, comp_ignore_bind_def,
       comp_return_def] >>
  Cases_on `dyn` >>
  simp[comp_bind_def, comp_ignore_bind_def, comp_return_def] >>
  rpt (pairarg_tac >> fs[]) >> strip_tac >> gvs[] >>
  metis_tac[]
QED

Theorem registration_aggregate_phases:
  compile_register_positional_args ce [(name,F,dyn,sz,di)] (4+h) st = (ce',last) /\
  FLOOKUP ce.ce_vars name = SOME loc /\
  var_location_memory_size loc = SOME n ==>
  ?buf a src mid first.
    compile_alloc_buffer n st = (buf,a) /\
    ce' = ce with ce_vars updated_by
      (\m. m |+ (name,PtrVar buf.buf_operand n)) /\
    compile_getelemptr_abi (Lit 4w) dyn h CALLDATALOAD (Lit 0w) (Lit 0w)
      a = (src,mid) /\
    (if dyn then
       compile_abi_arg_ptr_guard CALLDATALOAD src (Lit 4w) mid = ((),first)
     else first = mid) /\
    compile_abi_decode_to_buf buf.buf_operand src CALLDATALOAD
      (Lit 0w) (Lit 0w) di first = ((),last)
Proof
  strip_tac >> drule_all registration_aggregate_prepare_phases >>
  Cases_on `dyn` >> simp[] >> strip_tac
  >- (qexistsl_tac [`buf`, `a`, `src`, `g`, `first`] >>
      simp[abiEncoderTheory.compile_getelemptr_abi_def,
           abiEncoderTheory.compile_abi_dec_addr_def,
           comp_bind_def, comp_ignore_bind_def, comp_return_def]) >>
  qexistsl_tac [`buf`, `a`, `src`, `first`] >>
  simp[abiEncoderTheory.compile_getelemptr_abi_def,
       abiEncoderTheory.compile_abi_dec_addr_def,
       comp_bind_def, comp_ignore_bind_def, comp_return_def]
QED

Theorem registration_primitive_phases:
  compile_register_positional_args ce [(name,T,F,sz,DecPrimWord clamp)] (4+h) st =
    (ce',last) /\
  FLOOKUP ce.ce_vars name = SOME loc /\
  var_location_memory_size loc = SOME n ==>
  ?buf a src first.
    compile_alloc_buffer n st = (buf,a) /\
    ce' = ce with ce_vars updated_by
      (\m. m |+ (name,PtrVar buf.buf_operand n)) /\
    compile_getelemptr_abi (Lit 4w) F h CALLDATALOAD (Lit 0w) (Lit 0w)
      a = (src,first) /\
    compile_abi_decode_to_buf buf.buf_operand src CALLDATALOAD
      (Lit 0w) (Lit 0w) (DecPrimWord clamp) first = ((),last)
Proof
  strip_tac >>
  qpat_x_assum `compile_register_positional_args _ _ _ _ = _` mp_tac >>
  simp[compile_register_positional_args_def, comp_bind_def,
       comp_ignore_bind_def, comp_return_def] >>
  rpt (pairarg_tac >> fs[]) >> strip_tac >> gvs[] >>
  qpat_x_assum `compile_decode_args _ _ _ _ _ _ _ = _` mp_tac >>
  simp[compile_decode_args_def, finite_mapTheory.FLOOKUP_UPDATE,
       var_location_decode_operand_def, comp_bind_def, comp_ignore_bind_def,
       comp_return_def] >>
  rpt (pairarg_tac >> fs[]) >> strip_tac >> gvs[] >>
  simp[abiEncoderTheory.compile_getelemptr_abi_def,
       abiEncoderTheory.compile_abi_decode_to_buf_def,
       abiEncoderTheory.compile_abi_dec_addr_def,
       abiEncoderTheory.compile_abi_decode_static_def,
       comp_bind_def, comp_ignore_bind_def, comp_return_def] >>
  metis_tac[]
QED

Theorem registration_primitive_as_aggregate:
  compile_register_positional_args ce
    ((name,T,F,sz,DecPrimWord clamp)::rest) off st =
  compile_register_positional_args ce
    ((name,F,F,sz,DecPrimWord clamp)::rest) off st
Proof
  simp[Ntimes compile_register_positional_args_def 2] >>
  Cases_on `FLOOKUP ce.ce_vars name` >> simp[] >>
  Cases_on `var_location_memory_size x` >> simp[] >>
  simp[comp_bind_def, comp_ignore_bind_def, comp_return_def] >>
  pairarg_tac >> simp[] >>
  simp[compile_decode_args_def, finite_mapTheory.FLOOKUP_UPDATE,
       var_location_decode_operand_def,
       abiEncoderTheory.compile_abi_decode_to_buf_def,
       abiEncoderTheory.compile_abi_decode_static_def,
       abiEncoderTheory.compile_abi_dec_addr_def,
       comp_bind_def, comp_ignore_bind_def, comp_return_def] >>
  Cases_on `emit_op ADD [Lit 4w; Lit (n2w (off - 4))] cs'` >> simp[] >>
  rename1 `emit_op ADD _ cs' = (src,b)` >>
  Cases_on `emit_op CALLDATALOAD [src] b` >> simp[] >>
  rename1 `emit_op CALLDATALOAD _ b = (v,c)` >>
  Cases_on `compile_abi_clamp_basetype v clamp c` >> simp[] >>
  rename1 `compile_abi_clamp_basetype _ _ _ = (u,d)` >>
  Cases_on `emit_void MSTORE [buf.buf_operand;v] d` >> simp[]
QED

(* Supplied physical success for an owner buffer of arbitrary size. *)
Theorem registration_owner_alloca_ptr:
  emit_op ALLOCA [Lit (n2w n)] sa = (ip,sb) /\
  step_inst_base (mk_inst sa.cs_next_id ALLOCA [Lit (n2w n)]
    [STRING #"%" (toString sa.cs_next_var)]) s = OK t /\
  ((FLOOKUP s.vs_allocas sa.cs_next_id = NONE /\
      s.vs_alloca_next + n < dimword (:256)) \/
   (?b. FLOOKUP s.vs_allocas sa.cs_next_id = SOME (b,n) /\
      b+n < dimword (:256))) /\
  t.vs_current_bb = s.vs_current_bb ==>
  ?H u q.
    ip = Var q /\
    H = step_prov PG G (mk_inst sa.cs_next_id ALLOCA [Lit (n2w n)] [q]) t /\
    u = step_taint (mk_inst sa.cs_next_id ALLOCA [Lit (n2w n)] [q]) s t tn /\
    ptr_covers H u q t n /\
    (!p sz. p <> q /\ ptr_covers G tn p s sz ==>
      ptr_covers H u p t sz) /\
    (!D lower ctx func.
      fn_has_code sa sb func /\ allocas_from lower s /\ ~ctx_has_dalloca ctx /\
      s.vs_current_bb = sa.cs_current_bb /\
      s.vs_inst_idx = LENGTH sa.cs_current_insts /\
      (!fuel. ptr_safe_run D lower fuel ctx func PG H u
        (t with vs_inst_idx := LENGTH sb.cs_current_insts)) ==>
      !fuel. ptr_safe_run D lower fuel ctx func PG G tn s)
Proof
  disch_then (CONJUNCTS_THEN2 assume_tac
    (CONJUNCTS_THEN2 assume_tac
      (CONJUNCTS_THEN2 assume_tac assume_tac))) >>
  drule emitHelperPropsTheory.emitted_insts_emit_op >> strip_tac >>
  qmatch_asmsub_abbrev_tac `step_inst_base ins s = OK t` >>
  qexistsl_tac [`step_prov PG G ins t`, `step_taint ins s t tn`] >>
  simp[] >> conj_tac
  >- (simp[Abbr `ins`] >>
      Cases_on `FLOOKUP s.vs_allocas sa.cs_next_id = NONE`
      >- (gvs[] >> simp[allocationPtrTheory.fresh_alloca_ptr_covers]) >>
      gvs[] >>
      drule allocationPtrTheory.reused_alloca_step >>
      disch_then (qspec_then `STRING #"%" (toString sa.cs_next_var)` mp_tac) >>
      strip_tac >> gvs[] >>
      metis_tac[allocationPtrTheory.reused_alloca_ptr_covers]) >>
  conj_tac
  >- (simp[Abbr `ins`] >> rpt strip_tac >>
      Cases_on `FLOOKUP s.vs_allocas sa.cs_next_id = NONE`
      >- (gvs[] >> simp[allocationPtrTheory.fresh_alloca_ptr_covers]) >>
      gvs[] >> drule allocationPtrTheory.reused_alloca_step >>
      disch_then (qspec_then `STRING #"%" (toString sa.cs_next_var)` mp_tac) >>
      strip_tac >> gvs[] >>
      metis_tac[allocationPtrTheory.reused_alloca_ptr_covers]) >>
  rpt gen_tac >> strip_tac >>
  `sb.cs_current_bb = sa.cs_current_bb` by
    (qpat_x_assum `emit_op _ _ _ = _` mp_tac >>
     simp[emitHelperTheory.emit_op_def, fresh_var_def, fresh_id_def, emit_def,
          comp_bind_def, comp_ignore_bind_def, comp_return_def] >>
     strip_tac >> gvs[]) >>
  irule decoderSetupStepPtrTheory.setup_instruction_continuation >>
  qexistsl_tac [`step_prov PG G ins t`, `ins`, `sa`, `sb`, `t`,
                 `step_taint ins s t tn`] >>
  gvs[Abbr `ins`, mk_inst_def, is_terminator_def] >>
  gen_tac >> irule ptrSafetyTransportTheory.ptr_inst_ok_lower_bound_transport >>
  simp[] >> qexists_tac `0` >>
  rewrite_tac[GSYM mk_inst_def] >> simp[fragExecPtrTheory.ptr_inst_ok_alloca]
QED

Theorem registration_alloc_buffer_ptr:
  compile_alloc_buffer n st = (buf,last) /\ fn_has_code st last fn /\
  alloca_inv s /\ alloca_frontier_inv ctx fn site s /\
  ALL_DISTINCT (MAP (\i. i.inst_id) (fn_insts fn)) /\
  n < dimword (:256) /\ unit_alloca_budget ctx < dimword (:256) /\
  (!entry. FLOOKUP s.vs_allocas st.cs_next_id = SOME entry ==>
    ?p. entry = (p,n) /\ p+n < dimword (:256)) ==>
  ?t H u q p.
    buf.buf_operand = Var q /\
    H = step_prov PG G (mk_inst st.cs_next_id ALLOCA [Lit (n2w n)] [q]) t /\
    u = step_taint (mk_inst st.cs_next_id ALLOCA [Lit (n2w n)] [q]) s t tn /\
    run_inst_seq (emitted_insts st last) s = OK t /\
    lookup_var q t = SOME (n2w p) /\ ptr_covers H u q t n /\
    FLOOKUP t.vs_allocas st.cs_next_id = SOME (p,n) /\
    p+n < dimword (:256) /\ alloca_inv t /\
    alloca_frontier_inv ctx fn site t /\
    s.vs_alloca_next <= t.vs_alloca_next /\
    t.vs_memory = s.vs_memory /\ t.vs_call_ctx = s.vs_call_ctx /\
    t.vs_data_section = s.vs_data_section /\
    t.vs_current_bb = s.vs_current_bb /\ t.vs_halted = s.vs_halted /\
    (fresh_vars_wrt st s ==> fresh_vars_wrt last t) /\
    (!op. abi_decoder_operand_live st.cs_next_var op ==>
      eval_operand op t = eval_operand op s) /\
    (!id entry. FLOOKUP s.vs_allocas id = SOME entry ==>
      FLOOKUP t.vs_allocas id = SOME entry) /\
    (!id. id <> st.cs_next_id ==> FLOOKUP t.vs_allocas id = FLOOKUP s.vs_allocas id) /\
    t.vs_accounts = s.vs_accounts /\ t.vs_transient = s.vs_transient /\
    t.vs_logs = s.vs_logs /\ t.vs_outcomes = s.vs_outcomes /\
    t.vs_requests = s.vs_requests /\
    t.vs_pending_deletions = s.vs_pending_deletions /\ t.vs_tx_ctx = s.vs_tx_ctx /\
    t.vs_block_ctx = s.vs_block_ctx /\ t.vs_fmp = s.vs_fmp /\
    t.vs_gas_readings = s.vs_gas_readings /\
    (!p sz. p <> q /\ ptr_covers G tn p s sz ==> ptr_covers H u p t sz) /\
    (!D lower ctx' func.
      fn_has_code st last func /\ allocas_from lower s /\ ~ctx_has_dalloca ctx' /\
      s.vs_current_bb = st.cs_current_bb /\
      s.vs_inst_idx = LENGTH st.cs_current_insts /\
      (!fuel. ptr_safe_run D lower fuel ctx' func PG H u
        (t with vs_inst_idx := LENGTH last.cs_current_insts)) ==>
      !fuel. ptr_safe_run D lower fuel ctx' func PG G tn s)
Proof
  strip_tac >>
  drule_all actualAllocExecTheory.actual_alloc_buffer_site >> strip_tac >>
  qmatch_asmsub_abbrev_tac `MEM ins (fn_insts fn)` >>
  `ins.inst_opcode = ALLOCA /\ ins.inst_operands = [Lit (n2w n)] /\
   ins.inst_outputs = [STRING #"%" (toString st.cs_next_var)] /\
   ins.inst_id = st.cs_next_id` by simp[Abbr `ins`, mk_inst_def] >>
  `!entry. FLOOKUP s.vs_allocas ins.inst_id = SOME entry ==>
     ?p. entry = (p,n) /\ p+n < dimword (:256)` by simp[] >>
  drule_all actualAllocExecTheory.actual_literal_alloca_owned_step >> strip_tac >>
  `((FLOOKUP s.vs_allocas st.cs_next_id = NONE /\
       s.vs_alloca_next + n < dimword (:256)) \/
    (?b. FLOOKUP s.vs_allocas st.cs_next_id = SOME (b,n) /\
       b+n < dimword (:256)))` by
    (Cases_on `FLOOKUP s.vs_allocas st.cs_next_id` >> simp[]
     >- (`FLOOKUP s.vs_allocas ins.inst_id = NONE` by simp[] >>
         drule_all actualAllocExecTheory.actual_literal_alloca_fresh_run >>
         strip_tac >> gvs[]) >> metis_tac[]) >>
  `emit_op ALLOCA [Lit (n2w n)] st = (buf.buf_operand,last)` by
    (qpat_x_assum `compile_alloc_buffer _ _ = _` mp_tac >>
     simp[contextTheory.compile_alloc_buffer_def, comp_bind_def, comp_return_def] >>
     pairarg_tac >> simp[] >> strip_tac >> gvs[]) >>
  fs[Abbr `ins`] >>
  drule_at (Pos (el 2)) registration_owner_alloca_ptr >> simp[] >>
  disch_then (qspecl_then [`tn`, `PG`, `G`] strip_assume_tac) >>
  drule emitHelperPropsTheory.emitted_insts_emit_op >> strip_tac >>
  `fresh_vars_wrt st s ==> fresh_vars_wrt last t` by
    (strip_tac >>
     qpat_x_assum `exec_alloca _ _ _ = OK t` mp_tac >>
     simp[exec_alloca_def, mk_inst_def] >>
     strip_tac >> gvs[AllCaseEqs(), fresh_vars_wrt_def, update_var_def] >>
     rpt strip_tac >> first_x_assum irule >> decide_tac) >>
  `!op. abi_decoder_operand_live st.cs_next_var op ==>
     eval_operand op t = eval_operand op s` by
    (rpt strip_tac >> first_x_assum irule >>
     Cases_on `op` >> gvs[abiDecoderReentryTheory.abi_decoder_operand_live_def,
         abiDecoderReentryTheory.abi_decoder_older_vars_def]) >>
  drule_at (Pos (el 2)) decoderWorldFramePtrTheory.decoder_step_world_frame >>
  simp[mk_inst_def, abiDecoderVarSequenceTheory.abi_decoder_reentry_opcode_def] >>
  strip_tac >> qexistsl_tac [`t`, `p`] >>
  gvs[run_inst_seq_def, mk_inst_def]
QED

(* Source arithmetic with progressive freshness and compiler-normalized PCs. *)
Theorem registration_source_add_ptr:
  emit_op ADD [left;right] sa = (out,sb) /\
  eval_operand left s = SOME a /\ eval_operand right s = SOME b /\
  fresh_vars_wrt sa s /\
  op_taint tn left = {} /\ op_taint tn right = {} /\
  op_prov G left = NONE /\ op_prov G right = NONE /\
  fn_has_code sa sb fn /\ allocas_from lo s /\ ~ctx_has_dalloca ctx /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?t H u.
    ~t.vs_halted /\ t.vs_current_bb = sb.cs_current_bb /\
    t.vs_inst_idx = LENGTH sb.cs_current_insts /\ fresh_vars_wrt sb t /\
    eval_operand out t = SOME (a+b) /\ op_taint u out = {} /\
    op_prov H out = NONE /\
    (!op w. eval_operand op s = SOME w ==> eval_operand op t = SOME w) /\
    t.vs_memory = s.vs_memory /\ t.vs_call_ctx = s.vs_call_ctx /\
    t.vs_data_section = s.vs_data_section /\
    t.vs_allocas = s.vs_allocas /\ t.vs_alloca_next = s.vs_alloca_next /\
    u.t_mem = tn.t_mem /\ u.t_stor = tn.t_stor /\
    u.t_trans = tn.t_trans /\ u.t_imm = tn.t_imm /\
    (!x. not_fresh_at sa x ==> FLOOKUP H x = FLOOKUP G x /\
      op_taint u (Var x) = op_taint tn (Var x)) /\
    t.vs_accounts = s.vs_accounts /\ t.vs_transient = s.vs_transient /\
    t.vs_logs = s.vs_logs /\ t.vs_outcomes = s.vs_outcomes /\
    t.vs_requests = s.vs_requests /\
    t.vs_pending_deletions = s.vs_pending_deletions /\ t.vs_tx_ctx = s.vs_tx_ctx /\
    t.vs_block_ctx = s.vs_block_ctx /\ t.vs_fmp = s.vs_fmp /\
    t.vs_gas_readings = s.vs_gas_readings /\
    (!D. (!fuel. ptr_safe_run D lo fuel ctx fn PG H u t) ==>
      !fuel. ptr_safe_run D lo fuel ctx fn PG G tn s)
Proof
  strip_tac >>
  drule_all abiDecoderBytesBoundTheory.abi_decode_add_sequence >> strip_tac >>
  drule_all (SRULE [] (Q.INST [`opc` |-> `ADD`]
    decoderRawEndpointPtrTheory.emit_scalar_binop_raw_endpoint_ptr)) >>
  simp[] >> disch_then (qspec_then `PG` strip_assume_tac) >>
  `t.vs_halted = s.vs_halted /\ sb.cs_current_bb = sa.cs_current_bb` by
    (drule emitHelperPropsTheory.emitted_insts_emit_op >> strip_tac >>
     gvs[run_inst_seq_def, step_inst_base_opcode_eqs, mk_inst_def, exec_pure2_def,
         AllCaseEqs()] >>
     qpat_x_assum `emit_op _ _ _ = _` mp_tac >>
     simp[emitHelperTheory.emit_op_def, fresh_var_def, fresh_id_def, emit_def,
          comp_bind_def, comp_ignore_bind_def, comp_return_def] >>
     strip_tac >> gvs[]) >>
  `EVERY (\i. abi_decoder_reentry_opcode i.inst_opcode)
     (emitted_insts sa sb)` by
    (drule emitHelperPropsTheory.emitted_insts_emit_op >> strip_tac >>
     simp[mk_inst_def, abiDecoderVarSequenceTheory.abi_decoder_reentry_opcode_def]) >>
  drule_all decoderWorldFramePtrTheory.decoder_run_world_frame >> strip_tac >>
  qexistsl_tac [`t with vs_inst_idx := LENGTH sb.cs_current_insts`, `H`, `u`] >>
  simp[GSYM fresh_vars_wrt_def, instIdxIndepTheory.eval_op_inst_idx] >>
  conj_tac >- gvs[fresh_vars_wrt_def] >>
  `s with vs_inst_idx := LENGTH sa.cs_current_insts = s` by
    simp[venom_state_component_equality] >>
  metis_tac[]
QED

(* Dynamic calldata heads contain offsets relative to the tuple at byte 4. *)
Theorem registration_dynamic_source_ptr:
  emit_op ADD [Lit 4w; Lit (n2w (off-4))] sa = (head,sb) /\
  emit_op CALLDATALOAD [head] sb = (delta,sc) /\
  emit_op ADD [Lit 4w; delta] sc = (src,sd) /\
  fn_has_code sa sb fn /\ fn_has_code sb sc fn /\ fn_has_code sc sd fn /\
  fn_inst_ids_distinct fn /\ fresh_vars_wrt sa s /\ allocas_from lo s /\
  ~ctx_has_dalloca ctx /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?t H u.
    ~t.vs_halted /\ t.vs_current_bb = sd.cs_current_bb /\
    t.vs_inst_idx = LENGTH sd.cs_current_insts /\ fresh_vars_wrt sd t /\
    eval_operand src t = SOME
      (4w + abi_decode_load CALLDATALOAD (4w + n2w (off-4) : bytes32) s) /\
    op_taint u src = {} /\ op_prov H src = NONE /\
    (!op w. eval_operand op s = SOME w ==> eval_operand op t = SOME w) /\
    t.vs_memory = s.vs_memory /\ t.vs_call_ctx = s.vs_call_ctx /\
    t.vs_allocas = s.vs_allocas /\ t.vs_alloca_next = s.vs_alloca_next /\
    u.t_mem = tn.t_mem /\ u.t_stor = tn.t_stor /\
    u.t_trans = tn.t_trans /\ u.t_imm = tn.t_imm /\
    (!x. not_fresh_at sa x ==> FLOOKUP H x = FLOOKUP G x /\
      op_taint u (Var x) = op_taint tn (Var x)) /\
    t.vs_accounts = s.vs_accounts /\ t.vs_transient = s.vs_transient /\
    t.vs_logs = s.vs_logs /\ t.vs_outcomes = s.vs_outcomes /\
    t.vs_requests = s.vs_requests /\
    t.vs_pending_deletions = s.vs_pending_deletions /\ t.vs_tx_ctx = s.vs_tx_ctx /\
    t.vs_block_ctx = s.vs_block_ctx /\ t.vs_fmp = s.vs_fmp /\
    t.vs_gas_readings = s.vs_gas_readings /\
    (!D. (!fuel. ptr_safe_run D lo fuel ctx fn PG H u t) ==>
      !fuel. ptr_safe_run D lo fuel ctx fn PG G tn s)
Proof
  strip_tac >>
  `eval_operand (Lit 4w) s = SOME 4w /\
   eval_operand (Lit (n2w (off-4))) s = SOME (n2w (off-4)) /\
   op_taint tn (Lit 4w) = {} /\ op_taint tn (Lit (n2w (off-4))) = {} /\
   op_prov G (Lit 4w) = NONE /\ op_prov G (Lit (n2w (off-4))) = NONE` by
    simp[eval_operand_def, op_taint_def, op_prov_def] >>
  drule_all registration_source_add_ptr >>
  disch_then (qspec_then `PG` strip_assume_tac) >>
  rename1 `eval_operand head hstate = SOME (4w + n2w (off-4))` >>
  `allocas_from lo hstate` by (gvs[allocas_from_def] >> metis_tac[]) >>
  drule_all calldataWordStepsPtrTheory.calldata_load_prefix_framed_uniform >>
  disch_then (qspecl_then [`PG`, `H`] strip_assume_tac) >>
  rename1 `eval_operand delta dstate = SOME _` >>
  `allocas_from lo dstate` by (gvs[allocas_from_def] >> metis_tac[]) >>
  `eval_operand (Lit 4w) dstate = SOME 4w /\
   op_taint u' (Lit 4w) = {} /\ op_prov H' (Lit 4w) = NONE` by
    simp[eval_operand_def, op_taint_def, op_prov_def] >>
  drule_all registration_source_add_ptr >>
  disch_then (qspec_then `PG` strip_assume_tac) >>
  `EVERY (\i. abi_decoder_reentry_opcode i.inst_opcode)
    (emitted_insts sb sc)` by
    (qpat_assum `emit_op CALLDATALOAD _ _ = _`
       (mp_then Any strip_assume_tac emitHelperPropsTheory.emitted_insts_emit_op) >>
     simp[mk_inst_def, abiDecoderVarSequenceTheory.abi_decoder_reentry_opcode_def]) >>
  drule_all decoderWorldFramePtrTheory.decoder_run_world_frame >>
  simp[] >> strip_tac >>
  `sa.cs_next_var <= sb.cs_next_var /\ sb.cs_next_var <= sc.cs_next_var` by
    (qpat_assum `emit_op ADD _ sa = _`
       (mp_then Any strip_assume_tac emitHelperPropsTheory.emitted_insts_emit_op) >>
     qpat_assum `emit_op CALLDATALOAD _ _ = _`
       (mp_then Any strip_assume_tac emitHelperPropsTheory.emitted_insts_emit_op) >>
     simp[]) >>
  qexistsl_tac [`t`, `H''`, `u''`] >>
  simp[abiDecoderContractTheory.abi_decode_load_def,
       abiDecoderContractTheory.abi_decode_source_def] >>
  simp[] >> qx_gen_tac `x` >> strip_tac >>
  `not_fresh_at sb x` by
    (irule freshWritesTheory.not_fresh_at_mono >> qexists_tac `sa` >> simp[]) >>
  `not_fresh_at sc x` by
    (irule freshWritesTheory.not_fresh_at_mono >> qexists_tac `sb` >> simp[]) >>
  qpat_x_assum `!x. not_fresh_at sc x ==> _` drule >>
  qpat_x_assum `!x. not_fresh_at sb x ==> _` drule >>
  qpat_x_assum `!x. not_fresh_at sa x ==> _` drule >> simp[]
QED

(* Canonical dynamic offset word, at the selected tuple head in calldata. *)
Theorem registration_calldata_offset:
  calldata_encodes env fname tys vs s.vs_call_ctx.cc_calldata /\
  LIST_REL (abi_decoder_coherent ce env sf) tys tvs /\
  LIST_REL value_has_type tvs vs /\
  vyper_to_abi_list env tys vs = SOME avs /\
  LENGTH s.vs_call_ctx.cc_calldata < dimword (:256) /\
  i < LENGTH tys /\ is_dynamic (vyper_to_abi_type env (EL i tys)) ==>
  abi_decode_load CALLDATALOAD
    (n2w (4 + SUM (MAP abi_member_head_size
      (TAKE i (MAP (vyper_to_abi_type env) tys)))) : bytes32) s =
    n2w (abi_tuple_child_offset (MAP (vyper_to_abi_type env) tys) avs i)
Proof
  strip_tac >>
  `LENGTH tys = LENGTH vs` by metis_tac[LIST_REL_LENGTH] >>
  fs[calldata_encodes_def, GSYM abiDecoderMembersTheory.vyper_to_abi_types_MAP,
     Excl "enc_def"] >>
  `TAKE (LENGTH vs) tys = tys` by metis_tac[TAKE_LENGTH_ID] >>
  fs[abiDecoderMembersTheory.vyper_to_abi_types_MAP, Excl "enc_def",
     Excl "TAKE_LENGTH_ID_rwt2"] >>
  drule_all coherent_source_list_head_lengths >> strip_tac >>
  `mem_bytes_at 4
    (LENGTH (enc (Tuple (MAP (vyper_to_abi_type env) tys)) (ListV avs)))
    (abi_decode_source CALLDATALOAD s) =
    enc (Tuple (MAP (vyper_to_abi_type env) tys)) (ListV avs)` by
    simp[abiDecoderContractTheory.abi_decode_source_def, mem_bytes_at_def,
         DROP_APPEND2, function_selector_length, TAKE_LENGTH_APPEND] >>
  gvs[Excl "enc_def"] >> once_rewrite_tac[arithmeticTheory.ADD_COMM] >>
  irule canonicalMemberTraversalPtrTheory.structural_tuple_indexed_offset_load >>
  simp[EL_MAP, function_selector_length, Excl "enc_def"] >>
  gvs[function_selector_length, Excl "enc_def"]
QED

(* One owner's allocation followed by static or dynamic calldata navigation. *)
Theorem registration_argument_prepare_forward_robust_resources:
  compile_alloc_buffer n st = (buf,a) /\
  compile_getelemptr_abi (Lit 4w) dyn off CALLDATALOAD (Lit 0w) (Lit 0w)
    a = (src,first) /\
  (dyn ==> abi_decode_load CALLDATALOAD (n2w (4+off) : bytes32) s = n2w delta /\
    4+delta < dimword (:256)) /\
  fn_has_code st a fn /\ fn_has_code a first fn /\
  alloca_inv s /\ alloca_frontier_inv ctx fn site s /\
  ALL_DISTINCT (MAP (\i. i.inst_id) (fn_insts fn)) /\
  n < dimword (:256) /\ unit_alloca_budget ctx < dimword (:256) /\
  (!entry. FLOOKUP s.vs_allocas st.cs_next_id = SOME entry ==>
    ?p. entry = (p,n) /\ p+n < dimword (:256)) /\
  fresh_vars_wrt st s /\ allocas_from lo s /\ lo <= s.vs_alloca_next /\
  ~ctx_has_dalloca ctx /\
  ~s.vs_halted /\ s.vs_current_bb = st.cs_current_bb /\
  s.vs_inst_idx = LENGTH st.cs_current_insts ==>
  ?t H u q p.
    buf.buf_operand = Var q /\ lookup_var q t = SOME (n2w p) /\
    ptr_covers H u q t n /\
    FLOOKUP t.vs_allocas st.cs_next_id = SOME (p,n) /\
    p+n < dimword (:256) /\ alloca_inv t /\
    alloca_frontier_inv ctx fn site t /\ allocas_from lo t /\
    s.vs_alloca_next <= t.vs_alloca_next /\
    ~t.vs_halted /\ t.vs_current_bb = first.cs_current_bb /\
    t.vs_inst_idx = LENGTH first.cs_current_insts /\ fresh_vars_wrt first t /\
    eval_operand src t = SOME (n2w (4 + if dyn then delta else off)) /\
    op_taint u src = {} /\ op_prov H src = NONE /\
    abi_decoder_operand_live first.cs_next_var src /\
    abi_decoder_operand_live first.cs_next_var (Var q) /\
    t.vs_memory = s.vs_memory /\ t.vs_call_ctx = s.vs_call_ctx /\
    t.vs_data_section = s.vs_data_section /\
    (!id entry. FLOOKUP s.vs_allocas id = SOME entry ==>
      FLOOKUP t.vs_allocas id = SOME entry) /\
    (!id. id <> st.cs_next_id ==>
      FLOOKUP t.vs_allocas id = FLOOKUP s.vs_allocas id) /\
    (!op. abi_decoder_operand_live st.cs_next_var op ==>
      eval_operand op t = eval_operand op s) /\
    (!p k. ptr_covers G tn p s k ==> ptr_covers H u p t k) /\
    u.t_stor = tn.t_stor /\ u.t_trans = tn.t_trans /\ u.t_imm = tn.t_imm /\
    t.vs_accounts = s.vs_accounts /\ t.vs_transient = s.vs_transient /\
    t.vs_logs = s.vs_logs /\ t.vs_outcomes = s.vs_outcomes /\
    t.vs_requests = s.vs_requests /\
    t.vs_pending_deletions = s.vs_pending_deletions /\ t.vs_tx_ctx = s.vs_tx_ctx /\
    t.vs_block_ctx = s.vs_block_ctx /\ t.vs_fmp = s.vs_fmp /\
    t.vs_gas_readings = s.vs_gas_readings /\
    (!tv0 v0 p0. val_wf tv0 v0 /\
      (!i. p0 <= i /\ i < p0 + val_footprint tv0 v0 ==> i < s.vs_alloca_next) /\
      (!mem. mem_agree_outside tn.t_mem s.vs_memory mem ==>
        val_in_memory tv0 v0 p0 mem) ==>
      !mem. mem_agree_outside u.t_mem t.vs_memory mem ==>
        val_in_memory tv0 v0 p0 mem) /\
    (!D. (!fuel. ptr_safe_run D lo fuel ctx fn PG H u t) ==>
      !fuel. ptr_safe_run D lo fuel ctx fn PG G tn s)
Proof
  strip_tac >> drule_all registration_alloc_buffer_ptr >>
  disch_then (qspecl_then [`tn`, `PG`, `G`] strip_assume_tac) >>
  rename1 `lookup_var q allocated = SOME (n2w p)` >>
  `emit_op ALLOCA [Lit (n2w n)] st = (buf.buf_operand,a)` by
    (qpat_x_assum `compile_alloc_buffer _ _ = _` mp_tac >>
     simp[contextTheory.compile_alloc_buffer_def, comp_bind_def, comp_return_def] >>
     pairarg_tac >> simp[] >> strip_tac >> gvs[]) >>
  qpat_assum `emit_op ALLOCA _ _ = _`
    (mp_then Any strip_assume_tac emitHelperPropsTheory.emitted_insts_emit_op) >>
  `q = STRCAT "%" (toString st.cs_next_var)` by gvs[] >>
  `!v w. lookup_var v s = SOME w ==> v <> q` by
    (rpt gen_tac >> strip_tac >> strip_tac >> gvs[] >>
     qpat_x_assum `fresh_vars_wrt st s` mp_tac >>
     rewrite_tac[fresh_vars_wrt_def] >>
     disch_then (qspec_then `st.cs_next_var` mp_tac) >>
     gvs[lookup_var_def, finite_mapTheory.FLOOKUP_DEF]) >>
  `!v k. ptr_covers G tn v s k ==> ptr_covers H u v allocated k` by
    (rpt strip_tac >>
     `v <> q` by
       (qpat_x_assum `ptr_covers G tn v s k` mp_tac >>
        simp[ptr_covers_def] >> strip_tac >>
        first_x_assum drule >> simp[]) >>
     qpat_x_assum `!p sz. p <> q /\ _ ==> _` irule >> simp[]) >>
  `fresh_vars_wrt a allocated` by simp[] >>
  `abi_decode_source_opcode CALLDATALOAD /\
   eval_operand (Lit 4w) allocated = SOME (n2w 4) /\
   (dyn ==> eval_operand (Lit 0w) allocated = SOME (n2w 0) /\
     abi_decode_load CALLDATALOAD (n2w (0+(4+off)) : bytes32) allocated = n2w delta /\
     4+delta < dimword (:256))` by
    gvs[abiDecoderContractTheory.abi_decode_source_opcode_def, eval_operand_def,
        abiDecoderContractTheory.abi_decode_load_def,
        abiDecoderContractTheory.abi_decode_source_def] >>
  drule_all abiDecoderReentryPointerTheory.abi_decoder_member_pointer_sequence >>
  strip_tac >> rename1 `run_inst_seq (emitted_insts a first) allocated = OK ready` >>
  `(!q. Lit 4w = Var q ==> not_fresh_at a q) /\
   op_taint u (Lit 4w) = {} /\ op_prov H (Lit 4w) = NONE` by
    simp[op_taint_def, op_prov_def] >>
  `a.cs_current_bb = st.cs_current_bb` by
    (drule emit_op_same_blocks >> simp[same_blocks_def]) >>
  `allocas_from lo allocated` by
    (qpat_assum `emit_op ALLOCA _ _ = _`
       (mp_then Any strip_assume_tac emitHelperPropsTheory.emitted_insts_emit_op) >>
     `exec_alloca (mk_inst st.cs_next_id ALLOCA [Lit (n2w n)] [q]) s
        (n2w n : bytes32) = OK allocated` by
       gvs[run_inst_seq_def, step_inst_base_opcode_eqs, mk_inst_def, AllCaseEqs()] >>
     drule_all decoderAllocationBoundsPtrTheory.exec_alloca_preserves_allocas_from >>
     simp[]) >>
  `!tv0 v0 p0. val_wf tv0 v0 /\
    (!i. p0 <= i /\ i < p0 + val_footprint tv0 v0 ==> i < s.vs_alloca_next) /\
    (!mem. mem_agree_outside tn.t_mem s.vs_memory mem ==>
      val_in_memory tv0 v0 p0 mem) ==>
    !mem. mem_agree_outside u.t_mem allocated.vs_memory mem ==>
      val_in_memory tv0 v0 p0 mem` by
    (rpt gen_tac >> strip_tac >>
     `step_inst_base (mk_inst st.cs_next_id ALLOCA [Lit (n2w n)] [q]) s =
        OK allocated` by
       gvs[run_inst_seq_def, emitHelperPropsTheory.emitted_insts_emit_op,
           AllCaseEqs()] >>
     drule_at (Pat `step_inst_base`)
       bodyPtrIfExpAllocFrameTheory.alloca_step_robust_below_frontier >>
     disch_then (qspecl_then [`tn`, `tv0`, `v0`, `p0`] mp_tac) >> simp[]) >>
  `allocated.vs_current_bb = a.cs_current_bb` by simp[] >>
  drule_all decoderMemberPrefixPtrTheory.member_navigation_source_endpoint_uniform >>
  disch_then (qspec_then `PG` strip_assume_tac) >>
  `dyn ==> abi_decode_source_opcode CALLDATALOAD` by simp[] >>
  drule_all abiDecoderReservationTheory.abi_decode_member_pointer_allocation_shape >>
  strip_tac >>
  drule_all abiDecoderReservationTheory.abi_decode_sequence_allocation_frame >> strip_tac >>
  drule_all abiDecoderReentryPointerTheory.abi_decoder_member_pointer_code >> strip_tac >>
  drule_all decoderWorldFramePtrTheory.decoder_run_world_frame >> strip_tac >>
  `ready.vs_labels = allocated.vs_labels` by
    (drule_all ctorAbiActualObservationsTheory.ctor_actual_sequence_labels >> simp[]) >>
  `ready.vs_halted = allocated.vs_halted` by
    (qpat_assum `run_inst_seq (emitted_insts a first) _ = _`
       (mp_then Any mp_tac abiDecoderReentryPointerTheory.abi_decoder_sequence_halted) >>
     simp[]) >>
  `first.cs_current_bb = a.cs_current_bb` by
    (qpat_x_assum `compile_getelemptr_abi _ _ _ _ _ _ _ = _` mp_tac >>
     Cases_on `dyn` >>
     simp[abiEncoderTheory.compile_getelemptr_abi_def,
          abiEncoderTheory.compile_abi_dec_addr_def, comp_bind_def,
          comp_ignore_bind_def, comp_return_def] >>
     rpt (pairarg_tac >> fs[]) >> strip_tac >> gvs[] >>
     metis_tac[emit_op_same_blocks, same_blocks_def]) >>
  `!v k. ptr_covers H u v allocated k ==> ptr_covers H' u' v ready k` by
    (rpt gen_tac >> simp[ptr_covers_def] >> strip_tac >>
     `eval_operand (Var v) allocated = SOME w` by simp[eval_operand_def] >>
     `not_fresh_at a v` by
       (drule_at (Pat `eval_operand`) calldataClampPtrTheory.evaluated_operand_not_fresh >>
        simp[]) >>
     qpat_x_assum `!q. not_fresh_at a q ==> _` drule >> simp[] >>
     metis_tac[]) >>
  `lookup_var q ready = SOME (n2w p)` by
    (qpat_x_assum `!op w. eval_operand op allocated = SOME w ==> _`
       (qspec_then `Var q` mp_tac) >> simp[eval_operand_def]) >>
  drule abiDecoderReentryPointerTheory.abi_decoder_member_pointer_counters >> strip_tac >>
  `abi_decoder_operand_live first.cs_next_var (Var q)` by
    (simp[calldataDynOwnedTheory.calldata_operand_live_not_fresh] >>
     `eval_operand (Var q) ready = SOME (n2w p)` by simp[eval_operand_def] >>
     drule_at (Pat `eval_operand`) calldataClampPtrTheory.evaluated_operand_not_fresh >>
     simp[]) >>
  qpat_assum `emit_op ALLOCA _ _ = _`
    (mp_then Any strip_assume_tac emitHelperPropsTheory.emitted_insts_emit_op) >>
  `!op. abi_decoder_operand_live st.cs_next_var op ==>
     eval_operand op ready = eval_operand op s` by
    (rpt strip_tac >>
     `abi_decoder_operand_live a.cs_next_var op` by
       (irule abiDecoderReentryTheory.abi_decoder_operand_live_mono >>
        qexists_tac `st.cs_next_var` >> simp[]) >>
     `eval_operand op ready = eval_operand op allocated` by
       (Cases_on `op` >> gvs[eval_operand_def,
          calldataDynOwnedTheory.calldata_operand_live_not_fresh] >>
        qpat_x_assum `!q. not_fresh_at a q ==> _` drule >> simp[]) >>
     simp[]) >>
  `!v k. ptr_covers G tn v s k ==> ptr_covers H' u' v ready k` by
    (rpt strip_tac >>
     qpat_x_assum `!v k. ptr_covers H u v allocated k ==> _` irule >>
     qpat_x_assum `!v k. ptr_covers G tn v s k ==> _` irule >> simp[]) >>
  qexistsl_tac [`ready with vs_inst_idx := LENGTH first.cs_current_insts`,
                `H'`, `u'`, `q`, `p`] >>
  simp[instIdxIndepTheory.eval_op_inst_idx, lookup_var_def] >>
  `alloca_inv ready /\ alloca_frontier_inv ctx fn site ready` by
    (drule_all calldataDynOwnedTheory.calldata_alloca_invariants_fields >>
     simp[]) >>
  `u.t_stor = tn.t_stor /\ u.t_trans = tn.t_trans /\ u.t_imm = tn.t_imm` by
    simp[step_taint_def, store_taint_def, adopt_reset_def, imm_taint_def, mk_inst_def] >>
  qpat_x_assum `H = step_prov _ _ _ _` kall_tac >>
  qpat_x_assum `u = step_taint _ _ _ _` kall_tac >>
  gvs[lookup_var_def, fresh_vars_wrt_def, allocas_from_def] >>
  simp[step_taint_def, store_taint_def, adopt_reset_def, imm_taint_def, mk_inst_def] >>
  gvs[]
QED

(* The same through the calldata pointer guard of a dynamic argument,
   which passes since the pointer is 4 + delta. *)
Theorem registration_argument_prepare_guarded_robust_resources:
  compile_alloc_buffer n st = (buf,a) /\
  compile_getelemptr_abi (Lit 4w) dyn off CALLDATALOAD (Lit 0w) (Lit 0w)
    a = (src,mid) /\
  (if dyn then compile_abi_arg_ptr_guard CALLDATALOAD src (Lit 4w) mid = ((),first)
   else first = mid) /\
  (dyn ==> abi_decode_load CALLDATALOAD (n2w (4+off) : bytes32) s = n2w delta /\
    4+delta < dimword (:256)) /\
  fn_has_code st a fn /\ fn_has_code a first fn /\ fn_inst_ids_distinct fn /\
  alloca_inv s /\ alloca_frontier_inv ctx fn site s /\
  ALL_DISTINCT (MAP (\i. i.inst_id) (fn_insts fn)) /\
  n < dimword (:256) /\ unit_alloca_budget ctx < dimword (:256) /\
  (!entry. FLOOKUP s.vs_allocas st.cs_next_id = SOME entry ==>
    ?p. entry = (p,n) /\ p+n < dimword (:256)) /\
  fresh_vars_wrt st s /\ allocas_from lo s /\ lo <= s.vs_alloca_next /\
  ~ctx_has_dalloca ctx /\
  ~s.vs_halted /\ s.vs_current_bb = st.cs_current_bb /\
  s.vs_inst_idx = LENGTH st.cs_current_insts ==>
  ?t H u q p.
    buf.buf_operand = Var q /\ lookup_var q t = SOME (n2w p) /\
    ptr_covers H u q t n /\
    FLOOKUP t.vs_allocas st.cs_next_id = SOME (p,n) /\
    p+n < dimword (:256) /\ alloca_inv t /\
    alloca_frontier_inv ctx fn site t /\ allocas_from lo t /\
    s.vs_alloca_next <= t.vs_alloca_next /\
    ~t.vs_halted /\ t.vs_current_bb = first.cs_current_bb /\
    t.vs_inst_idx = LENGTH first.cs_current_insts /\ fresh_vars_wrt first t /\
    eval_operand src t = SOME (n2w (4 + if dyn then delta else off)) /\
    op_taint u src = {} /\ op_prov H src = NONE /\
    abi_decoder_operand_live first.cs_next_var src /\
    abi_decoder_operand_live first.cs_next_var (Var q) /\
    t.vs_memory = s.vs_memory /\ t.vs_call_ctx = s.vs_call_ctx /\
    t.vs_data_section = s.vs_data_section /\
    (!id entry. FLOOKUP s.vs_allocas id = SOME entry ==>
      FLOOKUP t.vs_allocas id = SOME entry) /\
    (!id. id <> st.cs_next_id ==>
      FLOOKUP t.vs_allocas id = FLOOKUP s.vs_allocas id) /\
    (!op. abi_decoder_operand_live st.cs_next_var op ==>
      eval_operand op t = eval_operand op s) /\
    (!p k. ptr_covers G tn p s k ==> ptr_covers H u p t k) /\
    u.t_stor = tn.t_stor /\ u.t_trans = tn.t_trans /\ u.t_imm = tn.t_imm /\
    t.vs_accounts = s.vs_accounts /\ t.vs_transient = s.vs_transient /\
    t.vs_logs = s.vs_logs /\ t.vs_outcomes = s.vs_outcomes /\
    t.vs_requests = s.vs_requests /\
    t.vs_pending_deletions = s.vs_pending_deletions /\ t.vs_tx_ctx = s.vs_tx_ctx /\
    t.vs_block_ctx = s.vs_block_ctx /\ t.vs_fmp = s.vs_fmp /\
    t.vs_gas_readings = s.vs_gas_readings /\
    (!tv0 v0 p0. val_wf tv0 v0 /\
      (!i. p0 <= i /\ i < p0 + val_footprint tv0 v0 ==> i < s.vs_alloca_next) /\
      (!mem. mem_agree_outside tn.t_mem s.vs_memory mem ==>
        val_in_memory tv0 v0 p0 mem) ==>
      !mem. mem_agree_outside u.t_mem t.vs_memory mem ==>
        val_in_memory tv0 v0 p0 mem) /\
    (!D. (!fuel. ptr_safe_run D lo fuel ctx fn PG H u t) ==>
      !fuel. ptr_safe_run D lo fuel ctx fn PG G tn s)
Proof
  strip_tac >>
  `cs_extends a mid` by
    metis_tac[abiDecoderAppendTheory.cs_appends_abi_member_pointer,
      fragExecTheory.cs_appends_def] >>
  `cs_extends mid first` by
    (Cases_on `dyn` >> fs[compileEnvTheory.cs_extends_refl] >>
     metis_tac[calldataRegistrationExecTheory.registration_ptr_guard_extends]) >>
  `fn_has_code a mid fn /\ fn_has_code mid first fn` by
    metis_tac[fragExecTheory.fn_has_code_split] >>
  `st.cs_next_var <= mid.cs_next_var` by
    metis_tac[abiDecoderCountersTheory.abi_decoder_vars_mono_abi_alloc_buffer,
      abiDecoderCountersTheory.abi_decoder_vars_mono_abi_member_pointer,
      abiDecoderCountersTheory.abi_decoder_vars_mono_def, pairTheory.SND,
      arithmeticTheory.LESS_EQ_TRANS] >>
  qpat_x_assum `fn_has_code a first fn` kall_tac >>
  drule_all registration_argument_prepare_forward_robust_resources >>
  disch_then (qspecl_then [`tn`, `PG`, `G`] strip_assume_tac) >>
  reverse (Cases_on `dyn`) >> fs[]
  >- (qexistsl_tac [`t`, `H`, `u`, `p`] >> gvs[]) >>
  suspend "guard"
QED

Resume registration_argument_prepare_guarded_robust_resources[guard]:
  `w2n (n2w (delta + 4) : bytes32) = delta + 4` by
    (rewrite_tac[wordsTheory.w2n_n2w] >> irule arithmeticTheory.LESS_MOD >>
     first_assum ACCEPT_TAC) >>
  `~(n2w (delta + 4) <+ (4w:bytes32))` by
    (rewrite_tac[wordsTheory.WORD_LO] >>
     qpat_x_assum `w2n _ = delta + 4` (fn th => rewrite_tac[th]) >>
     `w2n (4w:bytes32) <= 4` by
       (rewrite_tac[wordsTheory.w2n_n2w] >>
        irule arithmeticTheory.MOD_LESS_EQ >> simp[wordsTheory.ZERO_LT_dimword]) >>
     decide_tac) >>
  `!x. src = Var x ==> not_fresh_at mid x` by
    (rpt strip_tac >> gvs[calldataDynOwnedTheory.calldata_operand_live_not_fresh]) >>
  drule_all registrationGuardPtrTheory.registration_ptr_guard_ptr_frame >>
  disch_then (qspec_then `PG` strip_assume_tac) >>
  drule calldataRegistrationExecTheory.registration_ptr_guard_code >> strip_tac >>
  qabbrev_tac `t' = t with <|vs_vars := vars;
    vs_inst_idx := LENGTH first.cs_current_insts|>` >>
  `!x. not_fresh_at mid x ==> lookup_var x t' = lookup_var x t` by
    (rpt strip_tac >> fs[Abbr `t'`, lookup_var_def]) >>
  `!op. abi_decoder_operand_live mid.cs_next_var op ==>
     eval_operand op t' = eval_operand op t` by
    (Cases >> simp[eval_operand_def] >>
     TRY (simp[Abbr `t'`] >> NO_TAC) >>
     simp[calldataDynOwnedTheory.calldata_operand_live_not_fresh] >>
     strip_tac >> fs[]) >>
  `!v k. ptr_covers H u v t k ==> ptr_covers G' tn' v t' k` by
    (rpt gen_tac >> simp[ptr_covers_def] >> strip_tac >>
     `not_fresh_at mid v` by
       (qpat_x_assum `fresh_vars_wrt mid t` mp_tac >>
        qpat_x_assum `lookup_var v t = SOME _` mp_tac >>
        rpt (pop_assum kall_tac) >>
        metis_tac[calldataClampPtrTheory.evaluated_operand_not_fresh,
                  eval_operand_def]) >>
     qpat_x_assum `!x. not_fresh_at mid x ==> lookup_var x t' = _`
       (drule_then (fn th => rewrite_tac[th])) >>
     qpat_x_assum `!x. not_fresh_at mid x ==> FLOOKUP vars x = _ /\ _`
       (drule_then (fn th => rewrite_tac[th])) >>
     conj_tac >- first_assum ACCEPT_TAC >>
     qexistsl_tac [`w`, `b`, `sz'`] >> rpt conj_tac >> first_assum ACCEPT_TAC) >>
  `not_fresh_at mid q` by
    (qpat_x_assum `abi_decoder_operand_live mid.cs_next_var (Var q)` mp_tac >>
     rewrite_tac[calldataDynOwnedTheory.calldata_operand_live_not_fresh]) >>
  `lookup_var q t' = SOME (n2w p)` by
    (qpat_assum `!x. not_fresh_at mid x ==> lookup_var x t' = _`
       (qspec_then `q` mp_tac) >>
     impl_tac >- first_assum ACCEPT_TAC >>
     disch_then (fn th => rewrite_tac[th]) >> first_assum ACCEPT_TAC) >>
  `ptr_covers G' tn' q t' n` by
    (qpat_assum `!v k. ptr_covers H u v t k ==> _` irule >>
     first_assum ACCEPT_TAC) >>
  `eval_operand src t' = SOME (n2w (delta + 4))` by
    (qpat_assum `!op. abi_decoder_operand_live mid.cs_next_var op ==> _`
       (qspec_then `src` mp_tac) >>
     impl_tac >- first_assum ACCEPT_TAC >>
     disch_then (fn th => rewrite_tac[th]) >> first_assum ACCEPT_TAC) >>
  `op_taint tn' src = {} /\ op_prov G' src = NONE` by
    (Cases_on `src` >> TRY (simp[op_taint_def, op_prov_def] >> NO_TAC) >>
     rename1 `Var x0` >>
     `not_fresh_at mid x0` by
       (qpat_x_assum `!x. Var _ = Var x ==> _` (qspec_then `x0` mp_tac) >>
        simp[]) >>
     qpat_x_assum `!x. not_fresh_at mid x ==> FLOOKUP vars x = _ /\ _` drule >>
     qpat_x_assum `op_taint u (Var _) = {}` mp_tac >>
     qpat_x_assum `op_prov H (Var _) = NONE` mp_tac >>
     simp[op_taint_def, op_prov_def]) >>
  `mid.cs_next_var <= first.cs_next_var` by
    (qpat_assum `first.cs_next_var = _` (fn th => rewrite_tac[th]) >>
     decide_tac) >>
  `abi_decoder_operand_live first.cs_next_var src /\
   abi_decoder_operand_live first.cs_next_var (Var q)` by
    (conj_tac >> irule abiDecoderReentryTheory.abi_decoder_operand_live_mono >>
     qexists_tac `mid.cs_next_var` >> conj_tac >> first_assum ACCEPT_TAC) >>
  `!op. abi_decoder_operand_live st.cs_next_var op ==>
     eval_operand op t' = eval_operand op s` by
    (rpt strip_tac >>
     `abi_decoder_operand_live mid.cs_next_var op` by
       (irule abiDecoderReentryTheory.abi_decoder_operand_live_mono >>
        qexists_tac `st.cs_next_var` >> conj_tac >> first_assum ACCEPT_TAC) >>
     qpat_assum `!op. abi_decoder_operand_live mid.cs_next_var op ==> _`
       (qspec_then `op` mp_tac) >>
     impl_tac >- first_assum ACCEPT_TAC >>
     disch_then (fn th => rewrite_tac[th]) >>
     qpat_assum `!op. abi_decoder_operand_live st.cs_next_var op ==> _`
       (qspec_then `op` mp_tac) >>
     impl_tac >- first_assum ACCEPT_TAC >>
     disch_then (fn th => rewrite_tac[th])) >>
  `!v k. ptr_covers G tn v s k ==> ptr_covers G' tn' v t' k` by
    (rpt strip_tac >>
     qpat_assum `!v k. ptr_covers H u v t k ==> _` irule >>
     qpat_assum `!p k. ptr_covers G tn p s k ==> _` irule >>
     first_assum ACCEPT_TAC) >>
  `!D. (!fuel. ptr_safe_run D lo fuel ctx fn PG G' tn' t') ==>
     !fuel. ptr_safe_run D lo fuel ctx fn PG G tn s` by
    (gen_tac >>
     qpat_x_assum `!D. (!fuel. ptr_safe_run D lo fuel ctx fn PG H u t) ==> _`
       (qspec_then `D` (fn i2 =>
     qpat_x_assum `!D. (!fuel. ptr_safe_run D lo fuel ctx fn PG G' tn' _) ==> _`
       (qspec_then `D` (fn i1 =>
     disch_then (fn a => ACCEPT_TAC (MP i2 (MP i1 a)))))))) >>
  `alloca_inv t' /\ alloca_frontier_inv ctx fn site t'` by
    (`t'.vs_allocas = t.vs_allocas /\ t'.vs_alloca_next = t.vs_alloca_next` by
       simp[Abbr `t'`] >>
     drule_all calldataDynOwnedTheory.calldata_alloca_invariants_fields >>
     disch_then (fn th => rewrite_tac[th]) >>
     conj_tac >> first_assum ACCEPT_TAC) >>
  `fresh_vars_wrt first t'` by
    (qpat_x_assum `fresh_vars_wrt first (t with vs_vars := vars)` mp_tac >>
     simp[Abbr `t'`, fresh_vars_wrt_def]) >>
  qexistsl_tac [`t'`, `G'`, `tn'`, `p`] >>
  rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
  qpat_assum `tn'.t_mem = _`
    (fn th => simp_tac (srw_ss()) [Abbr `t'`, th, allocas_from_def]) >>
  TRY (first_assum ACCEPT_TAC) >>
  TRY (qpat_x_assum `allocas_from lo t` mp_tac >>
       simp_tac (srw_ss()) [allocas_from_def] >> NO_TAC) >>
  simp[]
QED

Finalise registration_argument_prepare_guarded_robust_resources

Theorem registration_argument_prepare_forward_robust_ptr:
  compile_alloc_buffer n st = (buf,a) /\
  compile_getelemptr_abi (Lit 4w) dyn off CALLDATALOAD (Lit 0w) (Lit 0w)
    a = (src,first) /\
  (dyn ==> abi_decode_load CALLDATALOAD (n2w (4+off) : bytes32) s = n2w delta /\
    4+delta < dimword (:256)) /\
  fn_has_code st a fn /\ fn_has_code a first fn /\
  alloca_inv s /\ alloca_frontier_inv ctx fn site s /\
  ALL_DISTINCT (MAP (\i. i.inst_id) (fn_insts fn)) /\
  n < dimword (:256) /\ unit_alloca_budget ctx < dimword (:256) /\
  (!entry. FLOOKUP s.vs_allocas st.cs_next_id = SOME entry ==>
    ?p. entry = (p,n) /\ p+n < dimword (:256)) /\
  fresh_vars_wrt st s /\ allocas_from lo s /\ lo <= s.vs_alloca_next /\
  ~ctx_has_dalloca ctx /\
  ~s.vs_halted /\ s.vs_current_bb = st.cs_current_bb /\
  s.vs_inst_idx = LENGTH st.cs_current_insts ==>
  ?t H u q p.
    buf.buf_operand = Var q /\ lookup_var q t = SOME (n2w p) /\
    ptr_covers H u q t n /\
    FLOOKUP t.vs_allocas st.cs_next_id = SOME (p,n) /\
    p+n < dimword (:256) /\ alloca_inv t /\
    alloca_frontier_inv ctx fn site t /\ allocas_from lo t /\
    s.vs_alloca_next <= t.vs_alloca_next /\
    ~t.vs_halted /\ t.vs_current_bb = first.cs_current_bb /\
    t.vs_inst_idx = LENGTH first.cs_current_insts /\ fresh_vars_wrt first t /\
    eval_operand src t = SOME (n2w (4 + if dyn then delta else off)) /\
    op_taint u src = {} /\ op_prov H src = NONE /\
    abi_decoder_operand_live first.cs_next_var src /\
    abi_decoder_operand_live first.cs_next_var (Var q) /\
    t.vs_memory = s.vs_memory /\ t.vs_call_ctx = s.vs_call_ctx /\
    (!id entry. FLOOKUP s.vs_allocas id = SOME entry ==>
      FLOOKUP t.vs_allocas id = SOME entry) /\
    (!id. id <> st.cs_next_id ==>
      FLOOKUP t.vs_allocas id = FLOOKUP s.vs_allocas id) /\
    (!op. abi_decoder_operand_live st.cs_next_var op ==>
      eval_operand op t = eval_operand op s) /\
    (!p k. ptr_covers G tn p s k ==> ptr_covers H u p t k) /\
    u.t_stor = tn.t_stor /\ u.t_trans = tn.t_trans /\ u.t_imm = tn.t_imm /\
    t.vs_accounts = s.vs_accounts /\ t.vs_transient = s.vs_transient /\
    t.vs_logs = s.vs_logs /\ t.vs_outcomes = s.vs_outcomes /\
    t.vs_requests = s.vs_requests /\
    t.vs_pending_deletions = s.vs_pending_deletions /\ t.vs_tx_ctx = s.vs_tx_ctx /\
    t.vs_block_ctx = s.vs_block_ctx /\ t.vs_fmp = s.vs_fmp /\
    t.vs_gas_readings = s.vs_gas_readings /\
    (!tv0 v0 p0. val_wf tv0 v0 /\
      (!i. p0 <= i /\ i < p0 + val_footprint tv0 v0 ==> i < s.vs_alloca_next) /\
      (!mem. mem_agree_outside tn.t_mem s.vs_memory mem ==>
        val_in_memory tv0 v0 p0 mem) ==>
      !mem. mem_agree_outside u.t_mem t.vs_memory mem ==>
        val_in_memory tv0 v0 p0 mem) /\
    (!D. (!fuel. ptr_safe_run D lo fuel ctx fn PG H u t) ==>
      !fuel. ptr_safe_run D lo fuel ctx fn PG G tn s)
Proof
  strip_tac >> drule_all registration_argument_prepare_forward_robust_resources >>
  disch_then (qspecl_then [`tn`, `PG`, `G`] strip_assume_tac) >>
  qexistsl_tac [`t`, `H`, `u`, `q`, `p`] >> simp[]
QED

Theorem registration_argument_prepare_forward_ptr:
  compile_alloc_buffer n st = (buf,a) /\
  compile_getelemptr_abi (Lit 4w) dyn off CALLDATALOAD (Lit 0w) (Lit 0w)
    a = (src,first) /\
  (dyn ==> abi_decode_load CALLDATALOAD (n2w (4+off) : bytes32) s = n2w delta /\
    4+delta < dimword (:256)) /\
  fn_has_code st a fn /\ fn_has_code a first fn /\
  alloca_inv s /\ alloca_frontier_inv ctx fn site s /\
  ALL_DISTINCT (MAP (\i. i.inst_id) (fn_insts fn)) /\
  n < dimword (:256) /\ unit_alloca_budget ctx < dimword (:256) /\
  (!entry. FLOOKUP s.vs_allocas st.cs_next_id = SOME entry ==>
    ?p. entry = (p,n) /\ p+n < dimword (:256)) /\
  fresh_vars_wrt st s /\ allocas_from lo s /\ lo <= s.vs_alloca_next /\
  ~ctx_has_dalloca ctx /\
  ~s.vs_halted /\ s.vs_current_bb = st.cs_current_bb /\
  s.vs_inst_idx = LENGTH st.cs_current_insts ==>
  ?t H u q p.
    buf.buf_operand = Var q /\ lookup_var q t = SOME (n2w p) /\
    ptr_covers H u q t n /\
    FLOOKUP t.vs_allocas st.cs_next_id = SOME (p,n) /\
    p+n < dimword (:256) /\ alloca_inv t /\
    alloca_frontier_inv ctx fn site t /\ allocas_from lo t /\
    s.vs_alloca_next <= t.vs_alloca_next /\
    ~t.vs_halted /\ t.vs_current_bb = first.cs_current_bb /\
    t.vs_inst_idx = LENGTH first.cs_current_insts /\ fresh_vars_wrt first t /\
    eval_operand src t = SOME (n2w (4 + if dyn then delta else off)) /\
    op_taint u src = {} /\ op_prov H src = NONE /\
    abi_decoder_operand_live first.cs_next_var src /\
    abi_decoder_operand_live first.cs_next_var (Var q) /\
    t.vs_memory = s.vs_memory /\ t.vs_call_ctx = s.vs_call_ctx /\
    (!id entry. FLOOKUP s.vs_allocas id = SOME entry ==>
      FLOOKUP t.vs_allocas id = SOME entry) /\
    (!id. id <> st.cs_next_id ==>
      FLOOKUP t.vs_allocas id = FLOOKUP s.vs_allocas id) /\
    (!op. abi_decoder_operand_live st.cs_next_var op ==>
      eval_operand op t = eval_operand op s) /\
    (!p k. ptr_covers G tn p s k ==> ptr_covers H u p t k) /\
    u.t_stor = tn.t_stor /\ u.t_trans = tn.t_trans /\ u.t_imm = tn.t_imm /\
    t.vs_accounts = s.vs_accounts /\ t.vs_transient = s.vs_transient /\
    t.vs_logs = s.vs_logs /\ t.vs_outcomes = s.vs_outcomes /\
    t.vs_requests = s.vs_requests /\
    t.vs_pending_deletions = s.vs_pending_deletions /\ t.vs_tx_ctx = s.vs_tx_ctx /\
    t.vs_block_ctx = s.vs_block_ctx /\ t.vs_fmp = s.vs_fmp /\
    t.vs_gas_readings = s.vs_gas_readings /\
    (!D. (!fuel. ptr_safe_run D lo fuel ctx fn PG H u t) ==>
      !fuel. ptr_safe_run D lo fuel ctx fn PG G tn s)
Proof
  strip_tac >> drule_all registration_argument_prepare_forward_robust_ptr >>
  disch_then (qspecl_then [`tn`, `PG`, `G`] strip_assume_tac) >>
  qexistsl_tac [`t`, `H`, `u`, `q`, `p`] >> simp[]
QED

Theorem registration_argument_prepare_ptr:
  compile_alloc_buffer n st = (buf,a) /\
  compile_getelemptr_abi (Lit 4w) dyn off CALLDATALOAD (Lit 0w) (Lit 0w)
    a = (src,first) /\
  (dyn ==> abi_decode_load CALLDATALOAD (n2w (4+off) : bytes32) s = n2w delta /\
    4+delta < dimword (:256)) /\
  fn_has_code st a fn /\ fn_has_code a first fn /\
  alloca_inv s /\ alloca_frontier_inv ctx fn site s /\
  ALL_DISTINCT (MAP (\i. i.inst_id) (fn_insts fn)) /\
  n < dimword (:256) /\ unit_alloca_budget ctx < dimword (:256) /\
  (!entry. FLOOKUP s.vs_allocas st.cs_next_id = SOME entry ==>
    ?p. entry = (p,n) /\ p+n < dimword (:256)) /\
  fresh_vars_wrt st s /\ allocas_from lo s /\ lo <= s.vs_alloca_next /\
  ~ctx_has_dalloca ctx /\
  ~s.vs_halted /\ s.vs_current_bb = st.cs_current_bb /\
  s.vs_inst_idx = LENGTH st.cs_current_insts ==>
  ?t H u q p.
    buf.buf_operand = Var q /\ lookup_var q t = SOME (n2w p) /\
    ptr_covers H u q t n /\
    FLOOKUP t.vs_allocas st.cs_next_id = SOME (p,n) /\
    p+n < dimword (:256) /\ alloca_inv t /\
    alloca_frontier_inv ctx fn site t /\ allocas_from lo t /\
    s.vs_alloca_next <= t.vs_alloca_next /\
    ~t.vs_halted /\ t.vs_current_bb = first.cs_current_bb /\
    t.vs_inst_idx = LENGTH first.cs_current_insts /\ fresh_vars_wrt first t /\
    eval_operand src t = SOME (n2w (4 + if dyn then delta else off)) /\
    op_taint u src = {} /\ op_prov H src = NONE /\
    abi_decoder_operand_live first.cs_next_var src /\
    abi_decoder_operand_live first.cs_next_var (Var q) /\
    t.vs_memory = s.vs_memory /\ t.vs_call_ctx = s.vs_call_ctx /\
    (!id entry. FLOOKUP s.vs_allocas id = SOME entry ==>
      FLOOKUP t.vs_allocas id = SOME entry) /\
    (!op. abi_decoder_operand_live st.cs_next_var op ==>
      eval_operand op t = eval_operand op s) /\
    (!p k. ptr_covers G tn p s k ==> ptr_covers H u p t k) /\
    u.t_stor = tn.t_stor /\ u.t_trans = tn.t_trans /\ u.t_imm = tn.t_imm /\
    t.vs_accounts = s.vs_accounts /\ t.vs_transient = s.vs_transient /\
    t.vs_logs = s.vs_logs /\ t.vs_outcomes = s.vs_outcomes /\
    t.vs_requests = s.vs_requests /\
    t.vs_pending_deletions = s.vs_pending_deletions /\ t.vs_tx_ctx = s.vs_tx_ctx /\
    t.vs_block_ctx = s.vs_block_ctx /\ t.vs_fmp = s.vs_fmp /\
    t.vs_gas_readings = s.vs_gas_readings /\
    (!D. (!fuel. ptr_safe_run D lo fuel ctx fn PG H u t) ==>
      !fuel. ptr_safe_run D lo fuel ctx fn PG G tn s)
Proof
  strip_tac >> drule_all registration_argument_prepare_forward_ptr >>
  disch_then (qspecl_then [`tn`, `PG`, `G`] strip_assume_tac) >>
  qexistsl_tac [`t`, `H`, `u`, `q`, `p`] >> simp[]
QED

Theorem registration_preparation_forward_slots:
  compile_alloc_buffer n st = (buf,a) /\
  compile_getelemptr_abi (Lit 4w) dyn off CALLDATALOAD (Lit 0w) (Lit 0w)
    a = (src,first) /\
  (!id. id <> st.cs_next_id ==>
    FLOOKUP t.vs_allocas id = FLOOKUP s.vs_allocas id) /\
  (!id entry. FLOOKUP s.vs_allocas id = SOME entry ==> id < st.cs_next_id) ==>
  (!id entry. FLOOKUP t.vs_allocas id = SOME entry ==> id < first.cs_next_id) /\
  (!id. first.cs_next_id <= id ==> FLOOKUP t.vs_allocas id = NONE)
Proof
  strip_tac >>
  `emit_op ALLOCA [Lit (n2w n)] st = (buf.buf_operand,a)` by
    (qpat_x_assum `compile_alloc_buffer _ _ = _` mp_tac >>
     simp[contextTheory.compile_alloc_buffer_def, comp_bind_def, comp_return_def] >>
     pairarg_tac >> simp[] >> strip_tac >> gvs[]) >>
  drule emitHelperPropsTheory.emitted_insts_emit_op >> strip_tac >>
  `dyn ==> abi_decode_source_opcode CALLDATALOAD` by
    simp[abiDecoderContractTheory.abi_decode_source_opcode_def] >>
  drule_all abiDecoderReservationTheory.abi_decode_member_pointer_allocation_shape >>
  strip_tac >>
  `st.cs_next_id < first.cs_next_id` by decide_tac >>
  `!id entry. FLOOKUP t.vs_allocas id = SOME entry ==> id < first.cs_next_id` by
    (rpt strip_tac >> Cases_on `id = st.cs_next_id` >- simp[] >>
     `FLOOKUP s.vs_allocas id = SOME entry` by metis_tac[] >>
     qpat_x_assum `!id entry. FLOOKUP s.vs_allocas id = SOME entry ==> _`
       drule >> decide_tac) >>
  (conj_tac >- first_assum ACCEPT_TAC) >>
  rpt strip_tac >> Cases_on `FLOOKUP t.vs_allocas id` >- simp[] >>
  qpat_x_assum `!id entry. FLOOKUP t.vs_allocas id = SOME entry ==> _`
    drule >> simp[]
QED

(* Decoder writes are separated from each earlier installed local slot. *)
Theorem registration_owned_footprint_disjoint:
  alloca_inv t /\
  FLOOKUP t.vs_allocas old = SOME (b,n) /\
  FLOOKUP t.vs_allocas owner = SOME (d,k) /\ old <> owner /\
  d <= e /\ e+m <= d+k /\ b <= p /\ p+sz <= b+n /\
  (!a z. MEM (a,z) fp ==> ?id. first <= id /\ id < last /\
    FLOOKUP t.vs_allocas id = SOME (a,z)) /\
  (old < first \/ last <= old) ==>
  abi_footprint_disjoint p sz ((e,m)::fp)
Proof
  strip_tac >> simp[abiDecoderFrameTheory.abi_footprint_disjoint_def] >>
  (rpt gen_tac >> strip_tac
   >- (gvs[] >> drule_all abiCallerAllocationTheory.abi_caller_allocation_separate >>
       decide_tac) >>
   qpat_x_assum `!a z. MEM (a,z) fp ==> _`
     (qspecl_then [`d'`, `sz'`] mp_tac) >> simp[] >> strip_tac >>
   `old <> id` by decide_tac >>
   drule_all abiCallerAllocationTheory.abi_caller_allocation_separate >> decide_tac)
QED

Theorem registration_owned_local_frame:
  alloca_inv t /\
  FLOOKUP t.vs_allocas old = SOME (b,n) /\
  FLOOKUP t.vs_allocas owner = SOME (d,k) /\ old <> owner /\
  d <= e /\ e+m <= d+k /\ b <= p /\
  p + val_footprint tv v <= b+n /\
  (!a z. MEM (a,z) fp ==> ?id. first <= id /\ id < last /\
    FLOOKUP t.vs_allocas id = SOME (a,z)) /\
  (old < first \/ last <= old) /\
  abi_decode_footprint_frame ((e,m)::fp) s t /\
  val_wf tv v /\ u.t_mem SUBSET tn.t_mem /\
  (!mem. mem_agree_outside tn.t_mem s.vs_memory mem ==>
    val_in_memory tv v p mem) /\
  ptr_covers G tn q s sz /\
  lookup_var q t = lookup_var q s /\ FLOOKUP H q = FLOOKUP G q /\
  op_taint u (Var q) = op_taint tn (Var q) ==>
  ptr_covers H u q t sz /\ val_in_memory tv v p t.vs_memory /\
  (!mem. mem_agree_outside u.t_mem t.vs_memory mem ==>
    val_in_memory tv v p mem)
Proof
  strip_tac >>
  `abi_footprint_disjoint p (val_footprint tv v) ((e,m)::fp)` by
    (irule registration_owned_footprint_disjoint >>
     qexistsl_tac [`b`, `d`, `first`, `k`, `last`, `n`, `old`, `owner`, `t`] >>
     simp[]) >>
  (conj_tac >- gvs[ptr_covers_def]) >>
  drule_all sourceRecursiveComplexPtrTheory.robust_value_footprint_frame >> simp[]
QED

Theorem registration_fn_insts_blocks_inst_ids[local]:
  !bbs. MAP (\i. i.inst_id) (fn_insts_blocks bbs) =
        FLAT (MAP (\bb. MAP (\i. i.inst_id) bb.bb_instructions) bbs)
Proof
  Induct >> simp[venomInstTheory.fn_insts_blocks_def]
QED

Theorem registration_aggregate_singleton_ptr_resources:
  compile_register_positional_args ce
    [(name,F,dyn,sz,type_to_abi_dec_info sf ce ty)] (4+h) st = (ce',last) /\
  FLOOKUP ce.ce_vars name = SOME loc /\
  var_location_memory_size loc = SOME (type_memory_size tv) /\
  abi_decoder_coherent ce env sf ty tv /\ value_has_type tv v /\
  vyper_to_abi env ty v = SOME av /\
  mem_bytes_at srcpos (LENGTH (enc (vyper_to_abi_type env ty) av))
    s.vs_call_ctx.cc_calldata = enc (vyper_to_abi_type env ty) av /\
  srcpos + LENGTH (enc (vyper_to_abi_type env ty) av) < dimword (:256) /\
  srcpos = 4 + (if dyn then delta else h) /\
  (dyn ==> abi_decode_load CALLDATALOAD (n2w (4+h) : bytes32) s = n2w delta /\
    4+delta < dimword (:256)) /\
  type_memory_size tv < dimword (:256) /\
  (!id entry. FLOOKUP s.vs_allocas id = SOME entry ==> id < st.cs_next_id) /\
  alloca_inv s /\ alloca_frontier_inv ctx fn site s /\
  unit_alloca_budget ctx < dimword (:256) /\
  fn_has_code st last fn /\ fn_inst_ids_distinct fn /\
  (!bb. lookup_block last.cs_current_bb fn.fn_blocks = SOME bb ==>
    phi_prefix_length bb.bb_instructions = 0) /\
  fresh_vars_wrt st s /\ allocas_from lo s /\ lo <= s.vs_alloca_next /\
  ~ctx_has_dalloca ctx /\ ~s.vs_halted /\
  s.vs_current_bb = st.cs_current_bb /\
  s.vs_inst_idx = LENGTH st.cs_current_insts ==>
  ?t H u q p.
    t.vs_data_section = s.vs_data_section /\
    ((!inst w b n. MEM inst (fn_insts fn) /\ inst.inst_opcode = ALLOCA /\
        inst.inst_operands = [Lit w] /\
        FLOOKUP s.vs_allocas inst.inst_id = SOME (b,n) ==> n = w2n w) ==>
     (!inst w b n. MEM inst (fn_insts fn) /\ inst.inst_opcode = ALLOCA /\
        inst.inst_operands = [Lit w] /\
        FLOOKUP t.vs_allocas inst.inst_id = SOME (b,n) ==> n = w2n w)) /\
    ce' = ce with ce_vars updated_by
      (\m. m |+ (name,PtrVar (Var q) (type_memory_size tv))) /\
    lookup_var q t = SOME (n2w p) /\
    FLOOKUP t.vs_allocas st.cs_next_id = SOME (p,type_memory_size tv) /\
    ptr_covers H u q t (type_memory_size tv) /\
    val_in_memory tv v p t.vs_memory /\
    (!mem. mem_agree_outside u.t_mem t.vs_memory mem ==>
      val_in_memory tv v p mem) /\
    (!id entry. FLOOKUP t.vs_allocas id = SOME entry ==> id < last.cs_next_id) /\
    alloca_inv t /\ alloca_frontier_inv ctx fn site t /\ allocas_from lo t /\
    s.vs_alloca_next <= t.vs_alloca_next /\ fresh_vars_wrt last t /\
    ~t.vs_halted /\ t.vs_current_bb = last.cs_current_bb /\
    t.vs_inst_idx = LENGTH last.cs_current_insts /\
    (!old q0 p0 n0 tv0 v0.
      old < st.cs_next_id /\ FLOOKUP s.vs_allocas old = SOME (p0,n0) /\
      lookup_var q0 s = SOME (n2w p0) /\ ptr_covers G tn q0 s n0 /\
      val_wf tv0 v0 /\ val_footprint tv0 v0 <= n0 /\
      (!mem. mem_agree_outside tn.t_mem s.vs_memory mem ==>
        val_in_memory tv0 v0 p0 mem) ==>
      old < last.cs_next_id /\ FLOOKUP t.vs_allocas old = SOME (p0,n0) /\
      lookup_var q0 t = SOME (n2w p0) /\ ptr_covers H u q0 t n0 /\
      val_wf tv0 v0 /\ val_footprint tv0 v0 <= n0 /\
      (!mem. mem_agree_outside u.t_mem t.vs_memory mem ==>
        val_in_memory tv0 v0 p0 mem)) /\
    (!op. abi_decoder_operand_live st.cs_next_var op ==>
      eval_operand op t = eval_operand op s) /\
    (!id entry. FLOOKUP s.vs_allocas id = SOME entry ==>
      FLOOKUP t.vs_allocas id = SOME entry) /\
    u.t_stor = tn.t_stor /\ u.t_trans = tn.t_trans /\ u.t_imm = tn.t_imm /\
    t.vs_call_ctx = s.vs_call_ctx /\
    t.vs_accounts = s.vs_accounts /\ t.vs_transient = s.vs_transient /\
    t.vs_logs = s.vs_logs /\ t.vs_outcomes = s.vs_outcomes /\
    t.vs_requests = s.vs_requests /\
    t.vs_pending_deletions = s.vs_pending_deletions /\ t.vs_tx_ctx = s.vs_tx_ctx /\
    t.vs_block_ctx = s.vs_block_ctx /\ t.vs_fmp = s.vs_fmp /\
    t.vs_gas_readings = s.vs_gas_readings /\
    (!D. (!fuel. ptr_safe_run D lo fuel ctx fn PG H u t) ==>
      !fuel. ptr_safe_run D lo fuel ctx fn PG G tn s)
Proof
  strip_tac >> drule_all registration_aggregate_phases >> strip_tac >>
  `cs_extends st a /\ cs_extends a mid /\ cs_extends first last` by
    metis_tac[abiDecoderAppendTheory.cs_appends_abi_alloc_buffer,
      abiDecoderAppendTheory.cs_appends_abi_member_pointer,
      abiDecoderAppendTheory.cs_appends_abi_decode_mutual,
      fragExecTheory.cs_appends_def] >>
  `cs_extends mid first /\ mid.cs_next_var <= first.cs_next_var` by
    (Cases_on `dyn` >> fs[compileEnvTheory.cs_extends_refl] >>
     drule calldataRegistrationExecTheory.registration_ptr_guard_code >>
     strip_tac >>
     metis_tac[calldataRegistrationExecTheory.registration_ptr_guard_extends,
       arithmeticTheory.LESS_EQ_ADD]) >>
  `cs_extends a first` by metis_tac[compileEnvTheory.cs_extends_trans] >>
  `fn_has_code st a fn /\ fn_has_code a first fn /\ fn_has_code first last fn` by
    metis_tac[fragExecTheory.fn_has_code_split, compileEnvTheory.cs_extends_trans] >>
  `!entry. FLOOKUP s.vs_allocas st.cs_next_id = SOME entry ==>
    ?p. entry = (p,type_memory_size tv) /\ p+type_memory_size tv < dimword (:256)` by
    (rpt strip_tac >> first_x_assum drule >> simp[]) >>
  `ALL_DISTINCT (MAP (\i. i.inst_id) (fn_insts fn))` by
    gvs[fn_inst_ids_distinct_def, venomInstTheory.fn_insts_def,
        registration_fn_insts_blocks_inst_ids] >>
  drule_all registration_argument_prepare_guarded_robust_resources >>
  disch_then (qspecl_then [`tn`, `PG`, `G`] strip_assume_tac) >>
  rename1 `lookup_var q ready = SOME (n2w p)` >>
  drule_all registration_preparation_forward_slots >> strip_tac >>
  `mid.cs_next_id <= first.cs_next_id` by
    (Cases_on `dyn` >> fs[] >>
     drule calldataRegistrationExecTheory.registration_ptr_guard_code >>
     simp[]) >>
  `st.cs_next_id < first.cs_next_id` by
    (`st.cs_next_id < mid.cs_next_id` by
       (qpat_x_assum `!id entry. FLOOKUP ready.vs_allocas id = SOME entry ==>
                        id < mid.cs_next_id` irule >>
        qexists_tac `(p,type_memory_size tv)` >> first_assum ACCEPT_TAC) >>
     decide_tac) >>
  `first.cs_next_var <= last.cs_next_var` by
    metis_tac[abiDecoderCountersTheory.abi_decoder_vars_mono_mutual,
      abiDecoderCountersTheory.abi_decoder_vars_mono_def, pairTheory.SND] >>
  `fresh_vars_wrt last ready` by
    (irule emitHelperPropsTheory.fresh_vars_wrt_mono >>
     qexists_tac `first` >> simp[]) >>
  `lo <= ready.vs_alloca_next` by decide_tac >>
  `compile_abi_decode_to_buf (Var q) src CALLDATALOAD (Lit 0w) (Lit 0w)
    (type_to_abi_dec_info sf ce ty) first = ((),last)` by metis_tac[] >>
  drule sourceOwnedCoherentPtrTheory.source_owned_coherent_decoder_ptr >>
  disch_then (drule_at (Pat `compile_abi_decode_to_buf`)) >>
  disch_then (drule_at (Pat `ptr_covers`)) >>
  disch_then (drule_at (Pat `ptr_covers`)) >>
  disch_then (drule_at (Pat `FLOOKUP _ _ = SOME (_,_)`)) >>
  disch_then (drule_at (Pat `fresh_vars_wrt`)) >>
  disch_then (drule_at (Pat `alloca_frontier_inv`)) >>
  disch_then (drule_at (Pat `value_has_type`)) >>
  disch_then (drule_at (Pat `vyper_to_abi`)) >>
  disch_then (drule_at (Pat `lookup_var`)) >>
  disch_then (drule_at (Pat `lookup_var`)) >>
  disch_then (drule_at (Pat `allocas_from`)) >>
  disch_then (qspecl_then [`srcpos`, `PG`] mp_tac) >>
  (impl_tac >-
    (gvs[Excl "enc_def"] >> rpt strip_tac >>
     qpat_x_assum `!id entry. FLOOKUP ready.vs_allocas id = SOME entry ==> _`
       drule >> simp[] >> rpt strip_tac >> decide_tac)) >>
  strip_tac >>
  qexistsl_tac [`t`, `H'`, `u'`, `q`, `p`] >>
  `CALLDATALOAD <> ALLOCA` by simp[] >>
  `first.cs_next_id <= last.cs_next_id` by
    metis_tac[abiDecoderCodeTheory.abi_decoder_code_mutual,
      abiDecoderCodeTheory.abi_decoder_code_def, pairTheory.SND] >>
  `st.cs_next_id <= last.cs_next_id` by decide_tac >>
  `st.cs_next_var <= first.cs_next_var` by
    metis_tac[abiDecoderCountersTheory.abi_decoder_vars_mono_abi_alloc_buffer,
      abiDecoderCountersTheory.abi_decoder_vars_mono_abi_member_pointer,
      abiDecoderCountersTheory.abi_decoder_vars_mono_def, pairTheory.SND,
      arithmeticTheory.LESS_EQ_TRANS] >>
  `!id entry. FLOOKUP t.vs_allocas id = SOME entry ==> id < last.cs_next_id` by
    (rpt strip_tac >> spose_not_then assume_tac >>
     `FLOOKUP t.vs_allocas id = FLOOKUP ready.vs_allocas id` by
       (qpat_x_assum `!id. _ \/ _ ==> FLOOKUP t.vs_allocas id = _`
          (qspec_then `id` mp_tac) >> simp[]) >>
     `first.cs_next_id <= id` by decide_tac >>
     qpat_x_assum `!id. mid.cs_next_id <= id ==> FLOOKUP ready.vs_allocas id = NONE`
       (qspec_then `id` mp_tac) >>
     impl_tac >- decide_tac >>
     qpat_x_assum `FLOOKUP t.vs_allocas id = FLOOKUP ready.vs_allocas id`
       (fn th => rewrite_tac[GSYM th]) >>
     qpat_x_assum `FLOOKUP t.vs_allocas id = SOME _` (fn th => rewrite_tac[th]) >>
     rewrite_tac[optionTheory.NOT_SOME_NONE]) >>
  `t.vs_call_ctx = s.vs_call_ctx /\ t.vs_data_section = s.vs_data_section` by
    (qpat_x_assum `abi_decode_footprint_frame _ ready t`
       (strip_assume_tac o REWRITE_RULE [abiDecoderFrameTheory.abi_decode_footprint_frame_def]) >>
     metis_tac[]) >>
  conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac >- suspend "slot_classification" >>
  asm_rewrite_tac [] >>
  (conj_tac >-
    (qpat_x_assum `!op. abi_decoder_operand_live first.cs_next_var op ==> _`
       (qspec_then `Var q` mp_tac) >>
     asm_rewrite_tac [abiDecoderReentryTheory.abi_decoder_operand_live_def,
       venomStateTheory.eval_operand_def])) >>
  (conj_tac >- decide_tac) >>
  (conj_tac >- suspend "old_local") >>
  (conj_tac >-
    (rpt strip_tac >>
     `abi_decoder_operand_live first.cs_next_var op` by
       (irule abiDecoderReentryTheory.abi_decoder_operand_live_mono >>
        qexists_tac `st.cs_next_var` >> asm_rewrite_tac []) >>
     qpat_x_assum `!op. abi_decoder_operand_live first.cs_next_var op ==> _`
       (qspec_then `op` mp_tac) >>
     qpat_x_assum `!op. abi_decoder_operand_live st.cs_next_var op ==> _`
       (qspec_then `op` mp_tac) >> asm_rewrite_tac [] >>
     rpt strip_tac >> metis_tac[])) >>
  (conj_tac >-
    (rpt strip_tac >> PairCases_on `entry` >> metis_tac[])) >>
  gen_tac >> strip_tac >>
  qpat_x_assum `!D. _ ==> !fuel. ptr_safe_run D lo fuel ctx fn PG G tn s`
    (qspec_then `D` irule) >>
  qpat_x_assum `!D. _ ==> !fuel. ptr_safe_run D lo fuel ctx fn PG H u ready`
    (qspec_then `D` irule) >> first_assum ACCEPT_TAC
QED

Resume registration_aggregate_singleton_ptr_resources[old_local]:
  rpt gen_tac >> strip_tac >>
  `old < first.cs_next_id /\ old < last.cs_next_id /\ old <> st.cs_next_id` by
    decide_tac >>
  `FLOOKUP ready.vs_allocas old = SOME (p0,n0) /\
   FLOOKUP t.vs_allocas old = SOME (p0,n0)` by metis_tac[] >>
  `ptr_covers H u q0 ready n0` by metis_tac[] >>
  `p0 + n0 <= s.vs_alloca_next` by
    (qpat_x_assum `alloca_inv s` mp_tac >>
     rewrite_tac [venomMemDefsTheory.alloca_inv_def,
       venomMemDefsTheory.alloca_next_valid_def] >>
     metis_tac[]) >>
  `!mem. mem_agree_outside u.t_mem ready.vs_memory mem ==>
    val_in_memory tv0 v0 p0 mem` by
    (first_assum (qspecl_then [`tv0`, `v0`, `p0`] mp_tac) >>
     (impl_tac >-
       (asm_rewrite_tac [] >> rpt strip_tac >> decide_tac)) >>
     disch_then ACCEPT_TAC) >>
  `not_fresh_at st q0` by
    (rewrite_tac [not_fresh_at_def] >> rpt strip_tac >>
     qpat_x_assum `fresh_vars_wrt st s` mp_tac >>
     rewrite_tac [fresh_vars_wrt_def] >>
     disch_then (qspec_then `n` mp_tac) >>
     (impl_tac >- decide_tac) >> strip_tac >>
     qpat_x_assum `lookup_var q0 s = SOME _` mp_tac >>
     asm_rewrite_tac [venomStateTheory.lookup_var_def, finite_mapTheory.FLOOKUP_DEF] >>
     simp[NoAsms]) >>
  `abi_decoder_operand_live st.cs_next_var (Var q0)` by
    asm_rewrite_tac [calldataDynOwnedTheory.calldata_operand_live_not_fresh] >>
  `abi_decoder_operand_live first.cs_next_var (Var q0)` by
    (irule abiDecoderReentryTheory.abi_decoder_operand_live_mono >>
     qexists_tac `st.cs_next_var` >> asm_rewrite_tac []) >>
  `not_fresh_at first q0` by
    metis_tac[calldataDynOwnedTheory.calldata_operand_live_not_fresh] >>
  `lookup_var q0 ready = SOME (n2w p0) /\ lookup_var q0 t = SOME (n2w p0)` by
    (qpat_x_assum `!op. abi_decoder_operand_live st.cs_next_var op ==> _`
       (qspec_then `Var q0` mp_tac) >>
     qpat_x_assum `!op. abi_decoder_operand_live first.cs_next_var op ==> _`
       (qspec_then `Var q0` mp_tac) >>
     asm_rewrite_tac [venomStateTheory.eval_operand_def] >>
     rpt strip_tac >> asm_rewrite_tac []) >>
  `FLOOKUP H' q0 = FLOOKUP H q0 /\
   op_taint u' (Var q0) = op_taint u (Var q0)` by metis_tac[] >>
  `lookup_var q0 t = lookup_var q0 ready` by asm_rewrite_tac [] >>
  drule_at (Pat `abi_decode_footprint_frame`) registration_owned_local_frame >>
  disch_then (drule_at (Pat `val_wf`)) >>
  disch_then (drule_at (Pat `ptr_covers`)) >>
  disch_then (drule_at (Pat `FLOOKUP _ _ = SOME (_,_)`)) >>
  disch_then (drule_at (Pat `op_taint _ _ = op_taint _ _`)) >>
  disch_then (drule_at (Pat `FLOOKUP _ _ = FLOOKUP _ _`)) >>
  disch_then (drule_at (Pat `!mem. mem_agree_outside tm memory mem ==> val_in_memory tv v p mem`)) >>
  disch_then (qspec_then `st.cs_next_id` mp_tac) >>
  disch_then (qspecl_then
    [`last.cs_next_id`, `type_memory_size tv`, `first.cs_next_id`, `p`] mp_tac) >>
  (impl_tac >-
    (asm_rewrite_tac [] >> decide_tac)) >> strip_tac >>
  asm_rewrite_tac []
QED

Resume registration_aggregate_singleton_ptr_resources[slot_classification]:
  rpt strip_tac >>
  Cases_on `first.cs_next_id <= inst.inst_id /\ inst.inst_id < last.cs_next_id`
  >- (qpat_x_assum `!id p k. first.cs_next_id <= id /\ _ ==> _`
        (qspecl_then [`inst.inst_id`, `b`, `n`] mp_tac) >>
      simp[] >> strip_tac >>
      `inst = ins` by metis_tac[localPtrsPropsTheory.fn_inst_ids_distinct_inj] >>
      `[Lit w] = [Lit 32w]` by metis_tac[] >>
      qpat_x_assum `[Lit w] = _` mp_tac >> simp[wordsTheory.dimword_def]) >>
  `FLOOKUP ready.vs_allocas inst.inst_id = SOME (b,n)` by
    (qpat_x_assum `!id. id < first.cs_next_id \/ _ ==> _`
      (qspec_then `inst.inst_id` mp_tac) >>
     (impl_tac >- decide_tac) >> disch_tac >> metis_tac[]) >>
  Cases_on `inst.inst_id = st.cs_next_id`
  >- (drule_all actualAllocExecTheory.actual_alloc_buffer_site >> disch_tac >>
      `inst = mk_inst st.cs_next_id ALLOCA [Lit (n2w (type_memory_size tv))]
          [STRING #"%" (toString st.cs_next_var)]` by
        (irule localPtrsPropsTheory.fn_inst_ids_distinct_inj >>
         asm_rewrite_tac [] >> simp_tac (srw_ss()) [venomInstTheory.mk_inst_def] >>
         qexists_tac `fn` >> asm_rewrite_tac [] >>
         qpat_x_assum `MEM (mk_inst _ _ _ _) _` mp_tac >>
         simp_tac (srw_ss()) [venomInstTheory.mk_inst_def]) >>
      `inst.inst_operands = [Lit (n2w (type_memory_size tv))]` by
        (qpat_x_assum `inst = mk_inst _ _ _ _` mp_tac >>
         POP_ASSUM_LIST (K all_tac) >>
         simp_tac (srw_ss()) [venomInstTheory.mk_inst_def] >> strip_tac >> simp[]) >>
      `n = type_memory_size tv` by metis_tac[optionTheory.SOME_11, pairTheory.PAIR_EQ] >>
      qpat_x_assum `inst.inst_operands = [Lit (n2w _)]` mp_tac >>
      asm_rewrite_tac [] >>
      qpat_x_assum `type_memory_size tv < _` mp_tac >>
      POP_ASSUM_LIST (K all_tac) >> simp[]) >>
  `FLOOKUP s.vs_allocas inst.inst_id = SOME (b,n)` by metis_tac[] >>
  first_x_assum drule_all >> simp[]
QED

Finalise registration_aggregate_singleton_ptr_resources

Theorem registration_aggregate_singleton_ptr_framed:
  compile_register_positional_args ce
    [(name,F,dyn,sz,type_to_abi_dec_info sf ce ty)] (4+h) st = (ce',last) /\
  FLOOKUP ce.ce_vars name = SOME loc /\
  var_location_memory_size loc = SOME (type_memory_size tv) /\
  abi_decoder_coherent ce env sf ty tv /\ value_has_type tv v /\
  vyper_to_abi env ty v = SOME av /\
  mem_bytes_at srcpos (LENGTH (enc (vyper_to_abi_type env ty) av))
    s.vs_call_ctx.cc_calldata = enc (vyper_to_abi_type env ty) av /\
  srcpos + LENGTH (enc (vyper_to_abi_type env ty) av) < dimword (:256) /\
  srcpos = 4 + (if dyn then delta else h) /\
  (dyn ==> abi_decode_load CALLDATALOAD (n2w (4+h) : bytes32) s = n2w delta /\
    4+delta < dimword (:256)) /\
  type_memory_size tv < dimword (:256) /\
  (!id entry. FLOOKUP s.vs_allocas id = SOME entry ==> id < st.cs_next_id) /\
  alloca_inv s /\ alloca_frontier_inv ctx fn site s /\
  unit_alloca_budget ctx < dimword (:256) /\
  fn_has_code st last fn /\ fn_inst_ids_distinct fn /\
  (!bb. lookup_block last.cs_current_bb fn.fn_blocks = SOME bb ==>
    phi_prefix_length bb.bb_instructions = 0) /\
  fresh_vars_wrt st s /\ allocas_from lo s /\ lo <= s.vs_alloca_next /\
  ~ctx_has_dalloca ctx /\ ~s.vs_halted /\
  s.vs_current_bb = st.cs_current_bb /\
  s.vs_inst_idx = LENGTH st.cs_current_insts ==>
  ?t H u q p.
    ce' = ce with ce_vars updated_by
      (\m. m |+ (name,PtrVar (Var q) (type_memory_size tv))) /\
    lookup_var q t = SOME (n2w p) /\
    FLOOKUP t.vs_allocas st.cs_next_id = SOME (p,type_memory_size tv) /\
    ptr_covers H u q t (type_memory_size tv) /\
    val_in_memory tv v p t.vs_memory /\
    (!mem. mem_agree_outside u.t_mem t.vs_memory mem ==>
      val_in_memory tv v p mem) /\
    (!id entry. FLOOKUP t.vs_allocas id = SOME entry ==> id < last.cs_next_id) /\
    alloca_inv t /\ alloca_frontier_inv ctx fn site t /\ allocas_from lo t /\
    s.vs_alloca_next <= t.vs_alloca_next /\ fresh_vars_wrt last t /\
    ~t.vs_halted /\ t.vs_current_bb = last.cs_current_bb /\
    t.vs_inst_idx = LENGTH last.cs_current_insts /\
    (!old q0 p0 n0 tv0 v0.
      old < st.cs_next_id /\ FLOOKUP s.vs_allocas old = SOME (p0,n0) /\
      lookup_var q0 s = SOME (n2w p0) /\ ptr_covers G tn q0 s n0 /\
      val_wf tv0 v0 /\ val_footprint tv0 v0 <= n0 /\
      (!mem. mem_agree_outside tn.t_mem s.vs_memory mem ==>
        val_in_memory tv0 v0 p0 mem) ==>
      old < last.cs_next_id /\ FLOOKUP t.vs_allocas old = SOME (p0,n0) /\
      lookup_var q0 t = SOME (n2w p0) /\ ptr_covers H u q0 t n0 /\
      val_wf tv0 v0 /\ val_footprint tv0 v0 <= n0 /\
      (!mem. mem_agree_outside u.t_mem t.vs_memory mem ==>
        val_in_memory tv0 v0 p0 mem)) /\
    (!op. abi_decoder_operand_live st.cs_next_var op ==>
      eval_operand op t = eval_operand op s) /\
    (!id entry. FLOOKUP s.vs_allocas id = SOME entry ==>
      FLOOKUP t.vs_allocas id = SOME entry) /\
    u.t_stor = tn.t_stor /\ u.t_trans = tn.t_trans /\ u.t_imm = tn.t_imm /\
    t.vs_call_ctx = s.vs_call_ctx /\
    t.vs_accounts = s.vs_accounts /\ t.vs_transient = s.vs_transient /\
    t.vs_logs = s.vs_logs /\ t.vs_outcomes = s.vs_outcomes /\
    t.vs_requests = s.vs_requests /\
    t.vs_pending_deletions = s.vs_pending_deletions /\ t.vs_tx_ctx = s.vs_tx_ctx /\
    t.vs_block_ctx = s.vs_block_ctx /\ t.vs_fmp = s.vs_fmp /\
    t.vs_gas_readings = s.vs_gas_readings /\
    (!D. (!fuel. ptr_safe_run D lo fuel ctx fn PG H u t) ==>
      !fuel. ptr_safe_run D lo fuel ctx fn PG G tn s)
Proof
  strip_tac >> drule_all registration_aggregate_singleton_ptr_resources >>
  disch_then (qspecl_then [`tn`, `PG`, `G`] strip_assume_tac) >>
  qexistsl_tac [`t`, `H`, `u`, `q`, `p`] >> asm_rewrite_tac []
QED

Theorem registration_singleton_ptr_resources:
  compile_register_positional_args ce
    [(name,prim,dyn,sz,type_to_abi_dec_info sf ce ty)] (4+h) st = (ce',last) /\
  (prim ==> ~dyn /\ ?clamp. type_to_abi_dec_info sf ce ty = DecPrimWord clamp) /\
  FLOOKUP ce.ce_vars name = SOME loc /\
  var_location_memory_size loc = SOME (type_memory_size tv) /\
  abi_decoder_coherent ce env sf ty tv /\ value_has_type tv v /\
  vyper_to_abi env ty v = SOME av /\
  mem_bytes_at srcpos (LENGTH (enc (vyper_to_abi_type env ty) av))
    s.vs_call_ctx.cc_calldata = enc (vyper_to_abi_type env ty) av /\
  srcpos + LENGTH (enc (vyper_to_abi_type env ty) av) < dimword (:256) /\
  srcpos = 4 + (if dyn then delta else h) /\
  (dyn ==> abi_decode_load CALLDATALOAD (n2w (4+h) : bytes32) s = n2w delta /\
    4+delta < dimword (:256)) /\
  type_memory_size tv < dimword (:256) /\
  (!id entry. FLOOKUP s.vs_allocas id = SOME entry ==> id < st.cs_next_id) /\
  alloca_inv s /\ alloca_frontier_inv ctx fn site s /\
  unit_alloca_budget ctx < dimword (:256) /\
  fn_has_code st last fn /\ fn_inst_ids_distinct fn /\
  (!bb. lookup_block last.cs_current_bb fn.fn_blocks = SOME bb ==>
    phi_prefix_length bb.bb_instructions = 0) /\
  fresh_vars_wrt st s /\ allocas_from lo s /\ lo <= s.vs_alloca_next /\
  ~ctx_has_dalloca ctx /\ ~s.vs_halted /\
  s.vs_current_bb = st.cs_current_bb /\
  s.vs_inst_idx = LENGTH st.cs_current_insts ==>
  ?t H u q p.
    t.vs_data_section = s.vs_data_section /\
    ((!inst w b n. MEM inst (fn_insts fn) /\ inst.inst_opcode = ALLOCA /\
        inst.inst_operands = [Lit w] /\
        FLOOKUP s.vs_allocas inst.inst_id = SOME (b,n) ==> n = w2n w) ==>
     (!inst w b n. MEM inst (fn_insts fn) /\ inst.inst_opcode = ALLOCA /\
        inst.inst_operands = [Lit w] /\
        FLOOKUP t.vs_allocas inst.inst_id = SOME (b,n) ==> n = w2n w)) /\
    ce' = ce with ce_vars updated_by
      (\m. m |+ (name,PtrVar (Var q) (type_memory_size tv))) /\
    lookup_var q t = SOME (n2w p) /\
    FLOOKUP t.vs_allocas st.cs_next_id = SOME (p,type_memory_size tv) /\
    ptr_covers H u q t (type_memory_size tv) /\
    val_in_memory tv v p t.vs_memory /\
    (!mem. mem_agree_outside u.t_mem t.vs_memory mem ==>
      val_in_memory tv v p mem) /\
    (!id entry. FLOOKUP t.vs_allocas id = SOME entry ==> id < last.cs_next_id) /\
    alloca_inv t /\ alloca_frontier_inv ctx fn site t /\ allocas_from lo t /\
    s.vs_alloca_next <= t.vs_alloca_next /\ fresh_vars_wrt last t /\
    ~t.vs_halted /\ t.vs_current_bb = last.cs_current_bb /\
    t.vs_inst_idx = LENGTH last.cs_current_insts /\
    (!old q0 p0 n0 tv0 v0.
      old < st.cs_next_id /\ FLOOKUP s.vs_allocas old = SOME (p0,n0) /\
      lookup_var q0 s = SOME (n2w p0) /\ ptr_covers G tn q0 s n0 /\
      val_wf tv0 v0 /\ val_footprint tv0 v0 <= n0 /\
      (!mem. mem_agree_outside tn.t_mem s.vs_memory mem ==>
        val_in_memory tv0 v0 p0 mem) ==>
      old < last.cs_next_id /\ FLOOKUP t.vs_allocas old = SOME (p0,n0) /\
      lookup_var q0 t = SOME (n2w p0) /\ ptr_covers H u q0 t n0 /\
      val_wf tv0 v0 /\ val_footprint tv0 v0 <= n0 /\
      (!mem. mem_agree_outside u.t_mem t.vs_memory mem ==>
        val_in_memory tv0 v0 p0 mem)) /\
    (!op. abi_decoder_operand_live st.cs_next_var op ==>
      eval_operand op t = eval_operand op s) /\
    (!id entry. FLOOKUP s.vs_allocas id = SOME entry ==>
      FLOOKUP t.vs_allocas id = SOME entry) /\
    u.t_stor = tn.t_stor /\ u.t_trans = tn.t_trans /\ u.t_imm = tn.t_imm /\
    t.vs_call_ctx = s.vs_call_ctx /\
    t.vs_accounts = s.vs_accounts /\ t.vs_transient = s.vs_transient /\
    t.vs_logs = s.vs_logs /\ t.vs_outcomes = s.vs_outcomes /\
    t.vs_requests = s.vs_requests /\
    t.vs_pending_deletions = s.vs_pending_deletions /\ t.vs_tx_ctx = s.vs_tx_ctx /\
    t.vs_block_ctx = s.vs_block_ctx /\ t.vs_fmp = s.vs_fmp /\
    t.vs_gas_readings = s.vs_gas_readings /\
    (!D. (!fuel. ptr_safe_run D lo fuel ctx fn PG H u t) ==>
      !fuel. ptr_safe_run D lo fuel ctx fn PG G tn s)
Proof
  strip_tac >>
  `compile_register_positional_args ce
    [(name,F,dyn,sz,type_to_abi_dec_info sf ce ty)] (4+h) st = (ce',last)` by
    (Cases_on `prim` >> gvs[registration_primitive_as_aggregate]) >>
  drule_all registration_aggregate_singleton_ptr_resources >>
  simp[]
QED

Theorem registration_singleton_ptr_framed:
  compile_register_positional_args ce
    [(name,prim,dyn,sz,type_to_abi_dec_info sf ce ty)] (4+h) st = (ce',last) /\
  (prim ==> ~dyn /\ ?clamp. type_to_abi_dec_info sf ce ty = DecPrimWord clamp) /\
  FLOOKUP ce.ce_vars name = SOME loc /\
  var_location_memory_size loc = SOME (type_memory_size tv) /\
  abi_decoder_coherent ce env sf ty tv /\ value_has_type tv v /\
  vyper_to_abi env ty v = SOME av /\
  mem_bytes_at srcpos (LENGTH (enc (vyper_to_abi_type env ty) av))
    s.vs_call_ctx.cc_calldata = enc (vyper_to_abi_type env ty) av /\
  srcpos + LENGTH (enc (vyper_to_abi_type env ty) av) < dimword (:256) /\
  srcpos = 4 + (if dyn then delta else h) /\
  (dyn ==> abi_decode_load CALLDATALOAD (n2w (4+h) : bytes32) s = n2w delta /\
    4+delta < dimword (:256)) /\
  type_memory_size tv < dimword (:256) /\
  (!id entry. FLOOKUP s.vs_allocas id = SOME entry ==> id < st.cs_next_id) /\
  alloca_inv s /\ alloca_frontier_inv ctx fn site s /\
  unit_alloca_budget ctx < dimword (:256) /\
  fn_has_code st last fn /\ fn_inst_ids_distinct fn /\
  (!bb. lookup_block last.cs_current_bb fn.fn_blocks = SOME bb ==>
    phi_prefix_length bb.bb_instructions = 0) /\
  fresh_vars_wrt st s /\ allocas_from lo s /\ lo <= s.vs_alloca_next /\
  ~ctx_has_dalloca ctx /\ ~s.vs_halted /\
  s.vs_current_bb = st.cs_current_bb /\
  s.vs_inst_idx = LENGTH st.cs_current_insts ==>
  ?t H u q p.
    ce' = ce with ce_vars updated_by
      (\m. m |+ (name,PtrVar (Var q) (type_memory_size tv))) /\
    lookup_var q t = SOME (n2w p) /\
    FLOOKUP t.vs_allocas st.cs_next_id = SOME (p,type_memory_size tv) /\
    ptr_covers H u q t (type_memory_size tv) /\
    val_in_memory tv v p t.vs_memory /\
    (!mem. mem_agree_outside u.t_mem t.vs_memory mem ==>
      val_in_memory tv v p mem) /\
    (!id entry. FLOOKUP t.vs_allocas id = SOME entry ==> id < last.cs_next_id) /\
    alloca_inv t /\ alloca_frontier_inv ctx fn site t /\ allocas_from lo t /\
    s.vs_alloca_next <= t.vs_alloca_next /\ fresh_vars_wrt last t /\
    ~t.vs_halted /\ t.vs_current_bb = last.cs_current_bb /\
    t.vs_inst_idx = LENGTH last.cs_current_insts /\
    (!old q0 p0 n0 tv0 v0.
      old < st.cs_next_id /\ FLOOKUP s.vs_allocas old = SOME (p0,n0) /\
      lookup_var q0 s = SOME (n2w p0) /\ ptr_covers G tn q0 s n0 /\
      val_wf tv0 v0 /\ val_footprint tv0 v0 <= n0 /\
      (!mem. mem_agree_outside tn.t_mem s.vs_memory mem ==>
        val_in_memory tv0 v0 p0 mem) ==>
      old < last.cs_next_id /\ FLOOKUP t.vs_allocas old = SOME (p0,n0) /\
      lookup_var q0 t = SOME (n2w p0) /\ ptr_covers H u q0 t n0 /\
      val_wf tv0 v0 /\ val_footprint tv0 v0 <= n0 /\
      (!mem. mem_agree_outside u.t_mem t.vs_memory mem ==>
        val_in_memory tv0 v0 p0 mem)) /\
    (!op. abi_decoder_operand_live st.cs_next_var op ==>
      eval_operand op t = eval_operand op s) /\
    (!id entry. FLOOKUP s.vs_allocas id = SOME entry ==>
      FLOOKUP t.vs_allocas id = SOME entry) /\
    u.t_stor = tn.t_stor /\ u.t_trans = tn.t_trans /\ u.t_imm = tn.t_imm /\
    t.vs_call_ctx = s.vs_call_ctx /\
    t.vs_accounts = s.vs_accounts /\ t.vs_transient = s.vs_transient /\
    t.vs_logs = s.vs_logs /\ t.vs_outcomes = s.vs_outcomes /\
    t.vs_requests = s.vs_requests /\
    t.vs_pending_deletions = s.vs_pending_deletions /\ t.vs_tx_ctx = s.vs_tx_ctx /\
    t.vs_block_ctx = s.vs_block_ctx /\ t.vs_fmp = s.vs_fmp /\
    t.vs_gas_readings = s.vs_gas_readings /\
    (!D. (!fuel. ptr_safe_run D lo fuel ctx fn PG H u t) ==>
      !fuel. ptr_safe_run D lo fuel ctx fn PG G tn s)
Proof
  strip_tac >> drule_all registration_singleton_ptr_resources >>
  disch_then (qspecl_then [`tn`, `PG`, `G`] strip_assume_tac) >>
  qexistsl_tac [`t`, `H`, `u`, `q`, `p`] >> asm_rewrite_tac []
QED

Theorem registration_singleton_owner_instruction:
  compile_register_positional_args ce [(name,prim,dyn,sz,di)] (4+h) st = (ce',last) /\
  (prim ==> ~dyn /\ ?clamp. di = DecPrimWord clamp) /\
  FLOOKUP ce.ce_vars name = SOME loc /\ var_location_memory_size loc = SOME n /\
  ce' = ce with ce_vars updated_by (\m. m |+ (name,PtrVar (Var q) n)) /\
  fn_has_code st last fn ==>
  MEM (mk_inst st.cs_next_id ALLOCA [Lit (n2w n)] [q]) (fn_insts fn)
Proof
  strip_tac >>
  `compile_register_positional_args ce [(name,F,dyn,sz,di)] (4+h) st = (ce',last)` by
    (Cases_on `prim` >> gvs[registration_primitive_as_aggregate]) >>
  drule_all registration_aggregate_phases >> strip_tac >>
  `cs_extends st a /\ cs_extends a mid /\ cs_extends first last` by
    metis_tac[abiDecoderAppendTheory.cs_appends_abi_alloc_buffer,
      abiDecoderAppendTheory.cs_appends_abi_member_pointer,
      abiDecoderAppendTheory.cs_appends_abi_decode_mutual,
      fragExecTheory.cs_appends_def] >>
  `cs_extends a first` by
    (Cases_on `dyn` >> gvs[] >>
     metis_tac[calldataRegistrationExecTheory.registration_ptr_guard_extends,
       compileEnvTheory.cs_extends_trans]) >>
  `fn_has_code st a fn` by
    metis_tac[fn_has_code_split, cs_extends_trans] >>
  drule_all actualAllocExecTheory.actual_alloc_buffer_site >>
  `buf.buf_operand = Var q` by
    (qpat_x_assum `ce' = ce with ce_vars updated_by (\m. m |+ (name,PtrVar buf.buf_operand n))`
      mp_tac >>
     qpat_x_assum `ce' = ce with ce_vars updated_by (\m. m |+ (name,PtrVar (Var q) n))`
      mp_tac >>
     POP_ASSUM_LIST (K all_tac) >>
     gvs[compile_env_component_equality, finite_mapTheory.fmap_eq_flookup,
       finite_mapTheory.FLOOKUP_UPDATE] >> rpt strip_tac >>
     first_x_assum (qspec_then `name` mp_tac) >> simp[]) >>
  drule loweringHaltTheory.compile_alloc_buffer_parts >> simp[] >>
  metis_tac[]
QED

(* The indexed owner invariant advances independently of the decoder's
   implementation.  The frame premise is the singleton's old-local frame. *)
Theorem registration_owned_prefix_invariant_update:
  ALL_DISTINCT names /\ i < LENGTH names /\
  ce' = ce with ce_vars updated_by
    (\m. m |+ (EL i names,PtrVar (Var q) (type_memory_size (EL i tvs)))) /\
  (!j. j < i ==> ?aid q p n.
    R aid q n /\ aid < st.cs_next_id /\ FLOOKUP s.vs_allocas aid = SOME (p,n) /\
    FLOOKUP ce.ce_vars (EL j names) = SOME (PtrVar (Var q) n) /\
    lookup_var q s = SOME (n2w p) /\ n = type_memory_size (EL j tvs) /\
    ptr_covers G tn q s n /\ val_wf (EL j tvs) (EL j vals) /\
    val_footprint (EL j tvs) (EL j vals) <= n /\
    (!mem. mem_agree_outside tn.t_mem s.vs_memory mem ==>
      val_in_memory (EL j tvs) (EL j vals) p mem)) /\
  (!old q0 p0 n0 tv0 v0.
    old < st.cs_next_id /\ FLOOKUP s.vs_allocas old = SOME (p0,n0) /\
    lookup_var q0 s = SOME (n2w p0) /\ ptr_covers G tn q0 s n0 /\
    val_wf tv0 v0 /\ val_footprint tv0 v0 <= n0 /\
    (!mem. mem_agree_outside tn.t_mem s.vs_memory mem ==>
      val_in_memory tv0 v0 p0 mem) ==>
    old < last.cs_next_id /\ FLOOKUP t.vs_allocas old = SOME (p0,n0) /\
    lookup_var q0 t = SOME (n2w p0) /\ ptr_covers H u q0 t n0 /\
    val_wf tv0 v0 /\ val_footprint tv0 v0 <= n0 /\
    (!mem. mem_agree_outside u.t_mem t.vs_memory mem ==>
      val_in_memory tv0 v0 p0 mem)) /\
  R st.cs_next_id q (type_memory_size (EL i tvs)) /\
  st.cs_next_id < last.cs_next_id /\
  FLOOKUP t.vs_allocas st.cs_next_id = SOME (p,type_memory_size (EL i tvs)) /\
  lookup_var q t = SOME (n2w p) /\
  ptr_covers H u q t (type_memory_size (EL i tvs)) /\
  val_wf (EL i tvs) (EL i vals) /\
  val_footprint (EL i tvs) (EL i vals) <= type_memory_size (EL i tvs) /\
  (!mem. mem_agree_outside u.t_mem t.vs_memory mem ==>
    val_in_memory (EL i tvs) (EL i vals) p mem) ==>
  !j. j < SUC i ==> ?aid q p n.
    R aid q n /\ aid < last.cs_next_id /\ FLOOKUP t.vs_allocas aid = SOME (p,n) /\
    FLOOKUP ce'.ce_vars (EL j names) = SOME (PtrVar (Var q) n) /\
    lookup_var q t = SOME (n2w p) /\ n = type_memory_size (EL j tvs) /\
    ptr_covers H u q t n /\ val_wf (EL j tvs) (EL j vals) /\
    val_footprint (EL j tvs) (EL j vals) <= n /\
    (!mem. mem_agree_outside u.t_mem t.vs_memory mem ==>
      val_in_memory (EL j tvs) (EL j vals) p mem)
Proof
  strip_tac >> gen_tac >> strip_tac >>
  Cases_on `j = i`
  >- (gvs[] >> qexistsl_tac [`st.cs_next_id`, `q`, `p`] >>
      simp[finite_mapTheory.FLOOKUP_UPDATE]) >>
  `j < i` by decide_tac >>
  `EL j names <> EL i names` by gvs[EL_ALL_DISTINCT_EL_EQ] >>
  qpat_x_assum `!j. j < i ==> _` drule >> strip_tac >>
  qpat_x_assum `!old q0 p0 n0 tv0 v0. _` drule_all >> strip_tac >>
  qexistsl_tac [`aid`, `q'`, `p'`, `n`] >>
  gvs[finite_mapTheory.FLOOKUP_UPDATE]
QED

Theorem registration_owned_prefix_update:
  ALL_DISTINCT names /\ i < LENGTH names /\
  ce' = ce with ce_vars updated_by
    (\m. m |+ (EL i names,PtrVar (Var q) (type_memory_size (EL i tvs)))) /\
  (!j. j < i ==> ?aid q p n.
    aid < st.cs_next_id /\ FLOOKUP s.vs_allocas aid = SOME (p,n) /\
    FLOOKUP ce.ce_vars (EL j names) = SOME (PtrVar (Var q) n) /\
    lookup_var q s = SOME (n2w p) /\ n = type_memory_size (EL j tvs) /\
    ptr_covers G tn q s n /\ val_wf (EL j tvs) (EL j vals) /\
    val_footprint (EL j tvs) (EL j vals) <= n /\
    (!mem. mem_agree_outside tn.t_mem s.vs_memory mem ==>
      val_in_memory (EL j tvs) (EL j vals) p mem)) /\
  (!old q0 p0 n0 tv0 v0.
    old < st.cs_next_id /\ FLOOKUP s.vs_allocas old = SOME (p0,n0) /\
    lookup_var q0 s = SOME (n2w p0) /\ ptr_covers G tn q0 s n0 /\
    val_wf tv0 v0 /\ val_footprint tv0 v0 <= n0 /\
    (!mem. mem_agree_outside tn.t_mem s.vs_memory mem ==>
      val_in_memory tv0 v0 p0 mem) ==>
    old < last.cs_next_id /\ FLOOKUP t.vs_allocas old = SOME (p0,n0) /\
    lookup_var q0 t = SOME (n2w p0) /\ ptr_covers H u q0 t n0 /\
    val_wf tv0 v0 /\ val_footprint tv0 v0 <= n0 /\
    (!mem. mem_agree_outside u.t_mem t.vs_memory mem ==>
      val_in_memory tv0 v0 p0 mem)) /\
  st.cs_next_id < last.cs_next_id /\
  FLOOKUP t.vs_allocas st.cs_next_id = SOME (p,type_memory_size (EL i tvs)) /\
  lookup_var q t = SOME (n2w p) /\
  ptr_covers H u q t (type_memory_size (EL i tvs)) /\
  val_wf (EL i tvs) (EL i vals) /\
  val_footprint (EL i tvs) (EL i vals) <= type_memory_size (EL i tvs) /\
  (!mem. mem_agree_outside u.t_mem t.vs_memory mem ==>
    val_in_memory (EL i tvs) (EL i vals) p mem) ==>
  !j. j < SUC i ==> ?aid q p n.
    aid < last.cs_next_id /\ FLOOKUP t.vs_allocas aid = SOME (p,n) /\
    FLOOKUP ce'.ce_vars (EL j names) = SOME (PtrVar (Var q) n) /\
    lookup_var q t = SOME (n2w p) /\ n = type_memory_size (EL j tvs) /\
    ptr_covers H u q t n /\ val_wf (EL j tvs) (EL j vals) /\
    val_footprint (EL j tvs) (EL j vals) <= n /\
    (!mem. mem_agree_outside u.t_mem t.vs_memory mem ==>
      val_in_memory (EL j tvs) (EL j vals) p mem)
Proof
  strip_tac >> simp[] >>
  match_mp_tac (registration_owned_prefix_invariant_update
    |> SPEC_ALL |> Q.INST [`R` |-> `\aid q n. T`] |> SRULE []) >>
  asm_rewrite_tac [] >> metis_tac[]
QED

(* Caller readiness is quantified over the unchanged decoder metadata and
   calldata; no package or source-interpreter facts enter this induction. *)
Theorem registration_owned_suffix_invariant_resources:
  !R ce0 args tvs vals env sf cd ctx fn site lo PG.
  (!ce2 st2 ce3 last2 name prim dyn sz di h loc n q.
    compile_register_positional_args ce2 [(name,prim,dyn,sz,di)] (4+h) st2 = (ce3,last2) /\
    (prim ==> ~dyn /\ ?clamp. di = DecPrimWord clamp) /\
    FLOOKUP ce2.ce_vars name = SOME loc /\ var_location_memory_size loc = SOME n /\
    ce3 = ce2 with ce_vars updated_by (\m. m |+ (name,PtrVar (Var q) n)) /\
    fn_has_code st2 last2 fn ==> R st2.cs_next_id q n) ==>
  !i ce st s G tn cf last.
  ALL_DISTINCT (MAP FST args) /\
  (!j. j < LENGTH args ==> ?loc.
    FLOOKUP ce0.ce_vars (FST (EL j args)) = SOME loc /\
    var_location_memory_size loc = SOME (type_memory_size (EL j tvs))) /\
  (!j ce1 s1. j < LENGTH args /\
    ce1 = ce0 with ce_vars := ce1.ce_vars /\ s1.vs_call_ctx = cd ==>
    ?prim dyn sz av delta srcpos.
    build_positional_arg ce0 (EL j args) =
      (FST (EL j args),prim,dyn,sz,type_to_abi_dec_info sf ce1 (SND (EL j args))) /\
    sz = abi_member_head_size (vyper_to_abi_type env (SND (EL j args))) /\
    (prim ==> ~dyn /\ ?clamp.
      type_to_abi_dec_info sf ce1 (SND (EL j args)) = DecPrimWord clamp) /\
    abi_decoder_coherent ce1 env sf (SND (EL j args)) (EL j tvs) /\
    value_has_type (EL j tvs) (EL j vals) /\
    vyper_to_abi env (SND (EL j args)) (EL j vals) = SOME av /\
    mem_bytes_at srcpos
      (LENGTH (enc (vyper_to_abi_type env (SND (EL j args))) av)) cd.cc_calldata =
      enc (vyper_to_abi_type env (SND (EL j args))) av /\
    srcpos + LENGTH (enc (vyper_to_abi_type env (SND (EL j args))) av) <
      dimword (:256) /\
    srcpos = 4 + (if dyn then delta else
      SUM (MAP (abi_member_head_size o vyper_to_abi_type env o SND) (TAKE j args))) /\
    (dyn ==> abi_decode_load CALLDATALOAD
      (n2w (4 + SUM (MAP (abi_member_head_size o vyper_to_abi_type env o SND)
        (TAKE j args))) : bytes32) s1 = n2w delta /\
      4+delta < dimword (:256)) /\
    type_memory_size (EL j tvs) < dimword (:256)) /\
  i <= LENGTH args /\ ce = ce0 with ce_vars := ce.ce_vars /\
  s.vs_call_ctx = cd /\
  compile_register_positional_args ce (build_positional_args ce0 (DROP i args))
    (4 + SUM (MAP (abi_member_head_size o vyper_to_abi_type env o SND)
      (TAKE i args))) st = (cf,last) /\
  (!j. i <= j /\ j < LENGTH args ==>
    FLOOKUP ce.ce_vars (FST (EL j args)) = FLOOKUP ce0.ce_vars (FST (EL j args))) /\
  (!j. j < i ==> ?aid q p n.
    R aid q n /\ aid < st.cs_next_id /\ FLOOKUP s.vs_allocas aid = SOME (p,n) /\
    FLOOKUP ce.ce_vars (FST (EL j args)) = SOME (PtrVar (Var q) n) /\
    lookup_var q s = SOME (n2w p) /\ n = type_memory_size (EL j tvs) /\
    ptr_covers G tn q s n /\ val_wf (EL j tvs) (EL j vals) /\
    val_footprint (EL j tvs) (EL j vals) <= n /\
    (!mem. mem_agree_outside tn.t_mem s.vs_memory mem ==>
      val_in_memory (EL j tvs) (EL j vals) p mem)) /\
  (!id entry. FLOOKUP s.vs_allocas id = SOME entry ==> id < st.cs_next_id) /\
  alloca_inv s /\ alloca_frontier_inv ctx fn site s /\
  unit_alloca_budget ctx < dimword (:256) /\
  fn_has_code st last fn /\ fn_inst_ids_distinct fn /\
  (!label bb. lookup_block label fn.fn_blocks = SOME bb ==>
    phi_prefix_length bb.bb_instructions = 0) /\
  fresh_vars_wrt st s /\ allocas_from lo s /\ lo <= s.vs_alloca_next /\
  ~ctx_has_dalloca ctx /\ ~s.vs_halted /\
  s.vs_current_bb = st.cs_current_bb /\
  s.vs_inst_idx = LENGTH st.cs_current_insts ==>
  ?t H u.
    t.vs_data_section = s.vs_data_section /\
    ((!inst w b n. MEM inst (fn_insts fn) /\ inst.inst_opcode = ALLOCA /\
        inst.inst_operands = [Lit w] /\
        FLOOKUP s.vs_allocas inst.inst_id = SOME (b,n) ==> n = w2n w) ==>
     (!inst w b n. MEM inst (fn_insts fn) /\ inst.inst_opcode = ALLOCA /\
        inst.inst_operands = [Lit w] /\
        FLOOKUP t.vs_allocas inst.inst_id = SOME (b,n) ==> n = w2n w)) /\
    (!j. j < LENGTH args ==> ?aid q p n.
      R aid q n /\ aid < last.cs_next_id /\ FLOOKUP t.vs_allocas aid = SOME (p,n) /\
      FLOOKUP cf.ce_vars (FST (EL j args)) = SOME (PtrVar (Var q) n) /\
      lookup_var q t = SOME (n2w p) /\ n = type_memory_size (EL j tvs) /\
      ptr_covers H u q t n /\ val_wf (EL j tvs) (EL j vals) /\
      val_footprint (EL j tvs) (EL j vals) <= n /\
      (!mem. mem_agree_outside u.t_mem t.vs_memory mem ==>
        val_in_memory (EL j tvs) (EL j vals) p mem)) /\
    cf = ce0 with ce_vars := cf.ce_vars /\
    (!id entry. FLOOKUP t.vs_allocas id = SOME entry ==> id < last.cs_next_id) /\
    alloca_inv t /\ alloca_frontier_inv ctx fn site t /\ allocas_from lo t /\
    s.vs_alloca_next <= t.vs_alloca_next /\ fresh_vars_wrt last t /\
    ~t.vs_halted /\ t.vs_current_bb = last.cs_current_bb /\
    t.vs_inst_idx = LENGTH last.cs_current_insts /\
    u.t_stor = tn.t_stor /\ u.t_trans = tn.t_trans /\ u.t_imm = tn.t_imm /\
    t.vs_call_ctx = s.vs_call_ctx /\
    t.vs_accounts = s.vs_accounts /\ t.vs_transient = s.vs_transient /\
    t.vs_logs = s.vs_logs /\ t.vs_outcomes = s.vs_outcomes /\
    t.vs_requests = s.vs_requests /\
    t.vs_pending_deletions = s.vs_pending_deletions /\ t.vs_tx_ctx = s.vs_tx_ctx /\
    t.vs_block_ctx = s.vs_block_ctx /\ t.vs_fmp = s.vs_fmp /\
    t.vs_gas_readings = s.vs_gas_readings /\
    (!D. (!fuel. ptr_safe_run D lo fuel ctx fn PG H u t) ==>
      !fuel. ptr_safe_run D lo fuel ctx fn PG G tn s)
Proof
  ntac 13 gen_tac >> disch_tac >> gen_tac >> measureInduct_on `LENGTH args - i` >>
  rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
  Cases_on `i = LENGTH args`
  >- (gvs[build_positional_args_def, register_positional_args_nil] >>
      qexistsl_tac [`s`, `G`, `tn`] >> simp[]) >>
  `i < LENGTH args` by decide_tac >>
  qpat_assum `!j ce1 s1. _`
    (qspecl_then [`i`, `ce`, `s`] mp_tac) >>
  (impl_tac >- simp[]) >> strip_tac >>
  `DROP i args = EL i args :: DROP (SUC i) args` by
    metis_tac[DROP_CONS_EL] >>
  `build_positional_args ce0 (DROP i args) =
    [build_positional_arg ce0 (EL i args)] ++
    build_positional_args ce0 (DROP (SUC i) args)` by
    simp[build_positional_args_def] >>
  qpat_x_assum `compile_register_positional_args _ _ _ _ = _` mp_tac >>
  qpat_x_assum `build_positional_args ce0 (DROP i args) = _`
    (fn th => pure_once_rewrite_tac[th]) >>
  qpat_assum `build_positional_arg ce0 (EL i args) = _`
    (fn th => pure_once_rewrite_tac[th]) >>
  rewrite_tac[register_positional_args_append] >>
  simp_tac (srw_ss()) [MAP, SUM, pairTheory.pair_case_thm, arithmeticTheory.ADD_0] >>
  strip_tac >>
  rename1 `compile_register_positional_args ce [_] _ st = (ce1,mid)` >>
  `cs_extends st mid /\ cs_extends mid last` by
    metis_tac[register_positional_args_suffix_extends] >>
  `fn_has_code st mid fn /\ fn_has_code mid last fn` by
    metis_tac[fn_has_code_split] >>
  qpat_assum `!j. j < LENGTH args ==> ?loc. _` (qspec_then `i` mp_tac) >>
  (impl_tac >- simp[]) >> strip_tac >>
  `FLOOKUP ce.ce_vars (FST (EL i args)) = SOME loc` by
    (qpat_assum `!j. i <= j /\ _ ==> _` (qspec_then `i` mp_tac) >>
     simp[]) >>
  `!bb. lookup_block mid.cs_current_bb fn.fn_blocks = SOME bb ==>
    phi_prefix_length bb.bb_instructions = 0` by metis_tac[] >>
  qpat_x_assum `mem_bytes_at _ _ cd.cc_calldata = _` mp_tac >>
  qpat_assum `s.vs_call_ctx = cd`
    (fn th => pure_once_rewrite_tac[GSYM th]) >> disch_tac >>
  drule_all registration_singleton_ptr_resources >>
  disch_then (qspecl_then [`tn`, `PG`, `G`] strip_assume_tac) >>
  rename1 `ptr_covers H1 u1 q a (type_memory_size (EL i tvs))` >>
  `val_wf (EL i tvs) (EL i vals)` by
    metis_tac[valueEncodingTypingTheory.value_has_type_val_wf] >>
  `val_footprint (EL i tvs) (EL i vals) <= type_memory_size (EL i tvs)` by
    metis_tac[exprSimPropsTheory.val_footprint_le] >>
  `st.cs_next_id < mid.cs_next_id` by
    (qpat_assum `!id entry. FLOOKUP a.vs_allocas id = SOME entry ==> _` drule >>
     simp[]) >>
  `R st.cs_next_id q (type_memory_size (EL i tvs))` by
    (qpat_assum `!ce2 st2 ce3 last2 name prim dyn sz di h loc n q. _`
       drule_all >> simp[]) >>
  `!j. j < SUC i ==> ?aid q p n.
    R aid q n /\ aid < mid.cs_next_id /\ FLOOKUP a.vs_allocas aid = SOME (p,n) /\
    FLOOKUP ce1.ce_vars (EL j (MAP FST args)) = SOME (PtrVar (Var q) n) /\
    lookup_var q a = SOME (n2w p) /\ n = type_memory_size (EL j tvs) /\
    ptr_covers H1 u1 q a n /\ val_wf (EL j tvs) (EL j vals) /\
    val_footprint (EL j tvs) (EL j vals) <= n /\
    (!mem. mem_agree_outside u1.t_mem a.vs_memory mem ==>
      val_in_memory (EL j tvs) (EL j vals) p mem)` by
    (match_mp_tac registration_owned_prefix_invariant_update >>
     qpat_x_assum `!y. LENGTH args - y < _ ==> _` kall_tac >>
     qpat_x_assum `!j ce1 s1. j < LENGTH args /\ _ ==> _` kall_tac >>
     qpat_x_assum `ce = ce0 with ce_vars := ce.ce_vars` kall_tac >>
     gvs[EL_MAP] >>
     qpat_x_assum `!old q0 p0 n0 tv0 v0. _` mp_tac >>
     qpat_x_assum `!id entry. FLOOKUP a.vs_allocas id = SOME entry ==> _` mp_tac >>
     qpat_x_assum `FLOOKUP a.vs_allocas st.cs_next_id = SOME _` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >> ntac 3 strip_tac >>
     `st.cs_next_id < mid.cs_next_id` by
       (qpat_x_assum `!id entry. _` drule >> simp[]) >>
     rpt gen_tac >> strip_tac >> conj_tac >- decide_tac >>
     first_x_assum irule >> simp[] >> qexists_tac `old` >> simp[]) >>
  `ce1 = ce0 with ce_vars := ce1.ce_vars` by
    (qpat_assum `ce1 = ce with ce_vars updated_by _`
       (fn th => pure_rewrite_tac[th]) >>
     qpat_x_assum `ce = ce0 with ce_vars := ce.ce_vars` mp_tac >>
     simp_tac (srw_ss()) [compileEnvTheory.compile_env_component_equality]) >>
  `!j. SUC i <= j /\ j < LENGTH args ==>
    FLOOKUP ce1.ce_vars (FST (EL j args)) = FLOOKUP ce0.ce_vars (FST (EL j args))` by
    (rpt gen_tac >> strip_tac >>
     `FST (EL i args) <> FST (EL j args)` by
       (qspecl_then [`MAP FST args`, `i`, `j`] mp_tac ALL_DISTINCT_EL_IMP >>
        simp[EL_MAP]) >>
     qpat_assum `ce1 = ce with ce_vars updated_by _`
       (fn th => pure_rewrite_tac[th]) >>
     simp[finite_mapTheory.FLOOKUP_UPDATE,
       IgnAsm `ce = ce0 with ce_vars := ce.ce_vars`]) >>
  `TAKE (SUC i) args = TAKE i args ++ [EL i args]` by
    metis_tac[TAKE_EL_SNOC, arithmeticTheory.ADD1, SNOC_APPEND] >>
  `SUM (MAP (abi_member_head_size o vyper_to_abi_type env o SND) (TAKE (SUC i) args)) =
    SUM (MAP (abi_member_head_size o vyper_to_abi_type env o SND) (TAKE i args)) + sz` by
    (qpat_assum `TAKE (SUC i) args = _` (fn th => pure_rewrite_tac[th]) >>
     simp[IgnAsm `ce = ce0 with ce_vars := ce.ce_vars`,
       IgnAsm `ce1 = ce0 with ce_vars := ce1.ce_vars`, SUM_APPEND]) >>
  `compile_register_positional_args ce1 (build_positional_args ce0 (DROP (SUC i) args))
    (4 + SUM (MAP (abi_member_head_size o vyper_to_abi_type env o SND)
      (TAKE (SUC i) args))) mid = (cf,last)` by
    (qpat_assum `SUM (MAP _ (TAKE (SUC i) args)) = _`
       (fn th => pure_once_rewrite_tac[th]) >>
     pure_rewrite_tac[arithmeticTheory.ADD_ASSOC] >> first_assum ACCEPT_TAC) >>
  qpat_x_assum `!y. LENGTH args - y < _ ==> _` (qspec_then `SUC i` mp_tac) >>
  (impl_tac >- decide_tac) >>
  disch_then (drule_at (Pat `compile_register_positional_args _ _ _ _ = _`)) >>
  disch_then (drule_at (Pat `fresh_vars_wrt _ _`)) >>
  disch_then (qspecl_then [`H1`, `u1`] mp_tac) >>
  impl_tac >-
    (ntac 3 (conj_tac >- first_assum ACCEPT_TAC) >>
     conj_tac >- decide_tac >>
     conj_tac >- first_assum ACCEPT_TAC >>
     conj_tac >-
       (qpat_assum `a.vs_call_ctx = s.vs_call_ctx`
          (fn th => pure_rewrite_tac[th]) >> first_assum ACCEPT_TAC) >>
     conj_tac >- first_assum ACCEPT_TAC >>
     conj_tac >-
       (rpt gen_tac >> strip_tac >>
        `j < LENGTH args` by decide_tac >>
        qpat_x_assum `!j. j < SUC i ==> _` (qspec_then `j` mp_tac) >>
        qpat_x_assum `j < LENGTH args` mp_tac >>
        qpat_x_assum `j < SUC i` mp_tac >>
        POP_ASSUM_LIST (K all_tac) >> ntac 2 strip_tac >>
        simp[EL_MAP]) >>
     `lo <= a.vs_alloca_next` by decide_tac >>
     rpt conj_tac >> first_assum ACCEPT_TAC) >>
  strip_tac >> qexistsl_tac [`t`, `H`, `u`] >>
  conj_tac >- metis_tac[] >>
  conj_tac >-
    (qpat_x_assum `(!inst w b n. _ ) ==> _` mp_tac >>
     qpat_x_assum `(!inst w b n. _ ) ==> _` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >> tautLib.TAUT_TAC) >>
  conj_tac >-
    (qpat_assum `!j. j < LENGTH args ==> ?aid q p n. _`
       (ACCEPT_TAC o SRULE [])) >>
  conj_tac >- first_assum ACCEPT_TAC >>
  qpat_x_assum `!j ce1 s1. j < LENGTH args /\ _ ==> _` kall_tac >>
  qpat_x_assum `ce = ce0 with ce_vars := ce.ce_vars` kall_tac >>
  qpat_x_assum `ce1 = ce0 with ce_vars := ce1.ce_vars` kall_tac >>
  qpat_x_assum `cf = ce0 with ce_vars := cf.ce_vars` kall_tac >>
  simp[] >>
  qpat_x_assum `!D. (!fuel. ptr_safe_run D _ _ _ _ _ _ _ t) ==> _` mp_tac >>
  qpat_x_assum `!D. (!fuel. ptr_safe_run D _ _ _ _ _ _ _ a) ==> _` mp_tac >>
  POP_ASSUM_LIST (K all_tac) >> metis_tac[]
QED

Theorem registration_owned_suffix_invariant_ptr:
  !R ce0 args tvs vals env sf cd ctx fn site lo PG.
  (!ce2 st2 ce3 last2 name prim dyn sz di h loc n q.
    compile_register_positional_args ce2 [(name,prim,dyn,sz,di)] (4+h) st2 = (ce3,last2) /\
    (prim ==> ~dyn /\ ?clamp. di = DecPrimWord clamp) /\
    FLOOKUP ce2.ce_vars name = SOME loc /\ var_location_memory_size loc = SOME n /\
    ce3 = ce2 with ce_vars updated_by (\m. m |+ (name,PtrVar (Var q) n)) /\
    fn_has_code st2 last2 fn ==> R st2.cs_next_id q n) ==>
  !i ce st s G tn cf last.
  ALL_DISTINCT (MAP FST args) /\
  (!j. j < LENGTH args ==> ?loc.
    FLOOKUP ce0.ce_vars (FST (EL j args)) = SOME loc /\
    var_location_memory_size loc = SOME (type_memory_size (EL j tvs))) /\
  (!j ce1 s1. j < LENGTH args /\
    ce1 = ce0 with ce_vars := ce1.ce_vars /\ s1.vs_call_ctx = cd ==>
    ?prim dyn sz av delta srcpos.
    build_positional_arg ce0 (EL j args) =
      (FST (EL j args),prim,dyn,sz,type_to_abi_dec_info sf ce1 (SND (EL j args))) /\
    sz = abi_member_head_size (vyper_to_abi_type env (SND (EL j args))) /\
    (prim ==> ~dyn /\ ?clamp.
      type_to_abi_dec_info sf ce1 (SND (EL j args)) = DecPrimWord clamp) /\
    abi_decoder_coherent ce1 env sf (SND (EL j args)) (EL j tvs) /\
    value_has_type (EL j tvs) (EL j vals) /\
    vyper_to_abi env (SND (EL j args)) (EL j vals) = SOME av /\
    mem_bytes_at srcpos
      (LENGTH (enc (vyper_to_abi_type env (SND (EL j args))) av)) cd.cc_calldata =
      enc (vyper_to_abi_type env (SND (EL j args))) av /\
    srcpos + LENGTH (enc (vyper_to_abi_type env (SND (EL j args))) av) <
      dimword (:256) /\
    srcpos = 4 + (if dyn then delta else
      SUM (MAP (abi_member_head_size o vyper_to_abi_type env o SND) (TAKE j args))) /\
    (dyn ==> abi_decode_load CALLDATALOAD
      (n2w (4 + SUM (MAP (abi_member_head_size o vyper_to_abi_type env o SND)
        (TAKE j args))) : bytes32) s1 = n2w delta /\
      4+delta < dimword (:256)) /\
    type_memory_size (EL j tvs) < dimword (:256)) /\
  i <= LENGTH args /\ ce = ce0 with ce_vars := ce.ce_vars /\
  s.vs_call_ctx = cd /\
  compile_register_positional_args ce (build_positional_args ce0 (DROP i args))
    (4 + SUM (MAP (abi_member_head_size o vyper_to_abi_type env o SND)
      (TAKE i args))) st = (cf,last) /\
  (!j. i <= j /\ j < LENGTH args ==>
    FLOOKUP ce.ce_vars (FST (EL j args)) = FLOOKUP ce0.ce_vars (FST (EL j args))) /\
  (!j. j < i ==> ?aid q p n.
    R aid q n /\ aid < st.cs_next_id /\ FLOOKUP s.vs_allocas aid = SOME (p,n) /\
    FLOOKUP ce.ce_vars (FST (EL j args)) = SOME (PtrVar (Var q) n) /\
    lookup_var q s = SOME (n2w p) /\ n = type_memory_size (EL j tvs) /\
    ptr_covers G tn q s n /\ val_wf (EL j tvs) (EL j vals) /\
    val_footprint (EL j tvs) (EL j vals) <= n /\
    (!mem. mem_agree_outside tn.t_mem s.vs_memory mem ==>
      val_in_memory (EL j tvs) (EL j vals) p mem)) /\
  (!id entry. FLOOKUP s.vs_allocas id = SOME entry ==> id < st.cs_next_id) /\
  alloca_inv s /\ alloca_frontier_inv ctx fn site s /\
  unit_alloca_budget ctx < dimword (:256) /\
  fn_has_code st last fn /\ fn_inst_ids_distinct fn /\
  (!label bb. lookup_block label fn.fn_blocks = SOME bb ==>
    phi_prefix_length bb.bb_instructions = 0) /\
  fresh_vars_wrt st s /\ allocas_from lo s /\ lo <= s.vs_alloca_next /\
  ~ctx_has_dalloca ctx /\ ~s.vs_halted /\
  s.vs_current_bb = st.cs_current_bb /\
  s.vs_inst_idx = LENGTH st.cs_current_insts ==>
  ?t H u.
    (!j. j < LENGTH args ==> ?aid q p n.
      R aid q n /\ aid < last.cs_next_id /\ FLOOKUP t.vs_allocas aid = SOME (p,n) /\
      FLOOKUP cf.ce_vars (FST (EL j args)) = SOME (PtrVar (Var q) n) /\
      lookup_var q t = SOME (n2w p) /\ n = type_memory_size (EL j tvs) /\
      ptr_covers H u q t n /\ val_wf (EL j tvs) (EL j vals) /\
      val_footprint (EL j tvs) (EL j vals) <= n /\
      (!mem. mem_agree_outside u.t_mem t.vs_memory mem ==>
        val_in_memory (EL j tvs) (EL j vals) p mem)) /\
    cf = ce0 with ce_vars := cf.ce_vars /\
    (!id entry. FLOOKUP t.vs_allocas id = SOME entry ==> id < last.cs_next_id) /\
    alloca_inv t /\ alloca_frontier_inv ctx fn site t /\ allocas_from lo t /\
    s.vs_alloca_next <= t.vs_alloca_next /\ fresh_vars_wrt last t /\
    ~t.vs_halted /\ t.vs_current_bb = last.cs_current_bb /\
    t.vs_inst_idx = LENGTH last.cs_current_insts /\
    u.t_stor = tn.t_stor /\ u.t_trans = tn.t_trans /\ u.t_imm = tn.t_imm /\
    t.vs_call_ctx = s.vs_call_ctx /\
    t.vs_accounts = s.vs_accounts /\ t.vs_transient = s.vs_transient /\
    t.vs_logs = s.vs_logs /\ t.vs_outcomes = s.vs_outcomes /\
    t.vs_requests = s.vs_requests /\
    t.vs_pending_deletions = s.vs_pending_deletions /\ t.vs_tx_ctx = s.vs_tx_ctx /\
    t.vs_block_ctx = s.vs_block_ctx /\ t.vs_fmp = s.vs_fmp /\
    t.vs_gas_readings = s.vs_gas_readings /\
    (!D. (!fuel. ptr_safe_run D lo fuel ctx fn PG H u t) ==>
      !fuel. ptr_safe_run D lo fuel ctx fn PG G tn s)
Proof
  ntac 13 gen_tac >> disch_tac >> rpt gen_tac >> strip_tac >>
  drule_all registration_owned_suffix_invariant_resources >>
  disch_then (qspec_then `PG` strip_assume_tac) >>
  qexistsl_tac [`t`, `H`, `u`] >> simp[]
QED

Theorem registration_owned_suffix_ptr:
  !ce0 args tvs vals env sf cd ctx fn site lo PG i ce st s G tn cf last.
  ALL_DISTINCT (MAP FST args) /\
  (!j. j < LENGTH args ==> ?loc.
    FLOOKUP ce0.ce_vars (FST (EL j args)) = SOME loc /\
    var_location_memory_size loc = SOME (type_memory_size (EL j tvs))) /\
  (!j ce1 s1. j < LENGTH args /\
    ce1 = ce0 with ce_vars := ce1.ce_vars /\ s1.vs_call_ctx = cd ==>
    ?prim dyn sz av delta srcpos.
    build_positional_arg ce0 (EL j args) =
      (FST (EL j args),prim,dyn,sz,type_to_abi_dec_info sf ce1 (SND (EL j args))) /\
    sz = abi_member_head_size (vyper_to_abi_type env (SND (EL j args))) /\
    (prim ==> ~dyn /\ ?clamp.
      type_to_abi_dec_info sf ce1 (SND (EL j args)) = DecPrimWord clamp) /\
    abi_decoder_coherent ce1 env sf (SND (EL j args)) (EL j tvs) /\
    value_has_type (EL j tvs) (EL j vals) /\
    vyper_to_abi env (SND (EL j args)) (EL j vals) = SOME av /\
    mem_bytes_at srcpos
      (LENGTH (enc (vyper_to_abi_type env (SND (EL j args))) av)) cd.cc_calldata =
      enc (vyper_to_abi_type env (SND (EL j args))) av /\
    srcpos + LENGTH (enc (vyper_to_abi_type env (SND (EL j args))) av) <
      dimword (:256) /\
    srcpos = 4 + (if dyn then delta else
      SUM (MAP (abi_member_head_size o vyper_to_abi_type env o SND) (TAKE j args))) /\
    (dyn ==> abi_decode_load CALLDATALOAD
      (n2w (4 + SUM (MAP (abi_member_head_size o vyper_to_abi_type env o SND)
        (TAKE j args))) : bytes32) s1 = n2w delta /\
      4+delta < dimword (:256)) /\
    type_memory_size (EL j tvs) < dimword (:256)) /\
  i <= LENGTH args /\ ce = ce0 with ce_vars := ce.ce_vars /\
  s.vs_call_ctx = cd /\
  compile_register_positional_args ce (build_positional_args ce0 (DROP i args))
    (4 + SUM (MAP (abi_member_head_size o vyper_to_abi_type env o SND)
      (TAKE i args))) st = (cf,last) /\
  (!j. i <= j /\ j < LENGTH args ==>
    FLOOKUP ce.ce_vars (FST (EL j args)) = FLOOKUP ce0.ce_vars (FST (EL j args))) /\
  (!j. j < i ==> ?aid q p n.
    aid < st.cs_next_id /\ FLOOKUP s.vs_allocas aid = SOME (p,n) /\
    FLOOKUP ce.ce_vars (FST (EL j args)) = SOME (PtrVar (Var q) n) /\
    lookup_var q s = SOME (n2w p) /\ n = type_memory_size (EL j tvs) /\
    ptr_covers G tn q s n /\ val_wf (EL j tvs) (EL j vals) /\
    val_footprint (EL j tvs) (EL j vals) <= n /\
    (!mem. mem_agree_outside tn.t_mem s.vs_memory mem ==>
      val_in_memory (EL j tvs) (EL j vals) p mem)) /\
  (!id entry. FLOOKUP s.vs_allocas id = SOME entry ==> id < st.cs_next_id) /\
  alloca_inv s /\ alloca_frontier_inv ctx fn site s /\
  unit_alloca_budget ctx < dimword (:256) /\
  fn_has_code st last fn /\ fn_inst_ids_distinct fn /\
  (!label bb. lookup_block label fn.fn_blocks = SOME bb ==>
    phi_prefix_length bb.bb_instructions = 0) /\
  fresh_vars_wrt st s /\ allocas_from lo s /\ lo <= s.vs_alloca_next /\
  ~ctx_has_dalloca ctx /\ ~s.vs_halted /\
  s.vs_current_bb = st.cs_current_bb /\
  s.vs_inst_idx = LENGTH st.cs_current_insts ==>
  ?t H u.
    (!j. j < LENGTH args ==> ?aid q p n.
      aid < last.cs_next_id /\ FLOOKUP t.vs_allocas aid = SOME (p,n) /\
      FLOOKUP cf.ce_vars (FST (EL j args)) = SOME (PtrVar (Var q) n) /\
      lookup_var q t = SOME (n2w p) /\ n = type_memory_size (EL j tvs) /\
      ptr_covers H u q t n /\ val_wf (EL j tvs) (EL j vals) /\
      val_footprint (EL j tvs) (EL j vals) <= n /\
      (!mem. mem_agree_outside u.t_mem t.vs_memory mem ==>
        val_in_memory (EL j tvs) (EL j vals) p mem)) /\
    cf = ce0 with ce_vars := cf.ce_vars /\
    (!id entry. FLOOKUP t.vs_allocas id = SOME entry ==> id < last.cs_next_id) /\
    alloca_inv t /\ alloca_frontier_inv ctx fn site t /\ allocas_from lo t /\
    s.vs_alloca_next <= t.vs_alloca_next /\ fresh_vars_wrt last t /\
    ~t.vs_halted /\ t.vs_current_bb = last.cs_current_bb /\
    t.vs_inst_idx = LENGTH last.cs_current_insts /\
    u.t_stor = tn.t_stor /\ u.t_trans = tn.t_trans /\ u.t_imm = tn.t_imm /\
    t.vs_call_ctx = s.vs_call_ctx /\
    t.vs_accounts = s.vs_accounts /\ t.vs_transient = s.vs_transient /\
    t.vs_logs = s.vs_logs /\ t.vs_outcomes = s.vs_outcomes /\
    t.vs_requests = s.vs_requests /\
    t.vs_pending_deletions = s.vs_pending_deletions /\ t.vs_tx_ctx = s.vs_tx_ctx /\
    t.vs_block_ctx = s.vs_block_ctx /\ t.vs_fmp = s.vs_fmp /\
    t.vs_gas_readings = s.vs_gas_readings /\
    (!D. (!fuel. ptr_safe_run D lo fuel ctx fn PG H u t) ==>
      !fuel. ptr_safe_run D lo fuel ctx fn PG G tn s)
Proof
  rpt gen_tac >> strip_tac >> simp_tac (srw_ss()) [] >>
  match_mp_tac (registration_owned_suffix_invariant_ptr
    |> Q.SPEC `\aid q n. T` |> SRULE []) >>
  goal_assum (drule_at (Pat `compile_register_positional_args _ _ _ _ = _`)) >>
  goal_assum (drule_at (Pat `fresh_vars_wrt _ _`)) >>
  qexists_tac `sf` >>
  qpat_assum `s.vs_call_ctx = cd` (fn th => pure_rewrite_tac[th]) >>
  rpt conj_tac >> first_assum (ACCEPT_TAC o SRULE [])
QED

(* Assemble the fold's caller readiness without exposing allocation state. *)
Theorem registration_owned_source_ready:
  calldata_encodes env fname (MAP SND args) vals cd.cc_calldata /\
  LIST_REL (abi_decoder_coherent ce0 env ce0.ce_struct_fields)
    (MAP SND args) tvs /\ LIST_REL value_has_type tvs vals /\
  LENGTH cd.cc_calldata < dimword (:256) /\
  (!j. j < LENGTH args ==> type_memory_size (EL j tvs) < dimword (:256)) ==>
  !j ce1 s. j < LENGTH args /\
    ce1 = ce0 with ce_vars := ce1.ce_vars /\ s.vs_call_ctx = cd ==>
  ?prim dyn sz av delta srcpos.
    build_positional_arg ce0 (EL j args) =
      (FST (EL j args),prim,dyn,sz,
        type_to_abi_dec_info ce0.ce_struct_fields ce1 (SND (EL j args))) /\
    sz = abi_member_head_size (vyper_to_abi_type env (SND (EL j args))) /\
    (prim ==> ~dyn /\ ?clamp.
      type_to_abi_dec_info ce0.ce_struct_fields ce1 (SND (EL j args)) =
        DecPrimWord clamp) /\
    abi_decoder_coherent ce1 env ce0.ce_struct_fields (SND (EL j args)) (EL j tvs) /\
    value_has_type (EL j tvs) (EL j vals) /\
    vyper_to_abi env (SND (EL j args)) (EL j vals) = SOME av /\
    mem_bytes_at srcpos
      (LENGTH (enc (vyper_to_abi_type env (SND (EL j args))) av)) cd.cc_calldata =
      enc (vyper_to_abi_type env (SND (EL j args))) av /\
    srcpos + LENGTH (enc (vyper_to_abi_type env (SND (EL j args))) av) < dimword (:256) /\
    srcpos = 4 + (if dyn then delta else
      SUM (MAP (abi_member_head_size o vyper_to_abi_type env o SND) (TAKE j args))) /\
    (dyn ==> abi_decode_load CALLDATALOAD
      (n2w (4 + SUM (MAP (abi_member_head_size o vyper_to_abi_type env o SND)
        (TAKE j args))) : bytes32) s = n2w delta /\ 4+delta < dimword (:256)) /\
    type_memory_size (EL j tvs) < dimword (:256)
Proof
  strip_tac >> rpt gen_tac >> strip_tac >>
  `ce1.ce_struct_fields = ce0.ce_struct_fields /\
   ce1.ce_flag_n_members = ce0.ce_flag_n_members` by
    (qpat_assum `ce1 = ce0 with ce_vars := ce1.ce_vars`
       (fn th => pure_once_rewrite_tac[th]) >> simp[]) >>
  `LIST_REL (abi_decoder_coherent ce1 env ce0.ce_struct_fields)
    (MAP SND args) tvs` by
    (irule LIST_REL_mono >> goal_assum (drule_at Any) >>
     rpt strip_tac >> irule abiDecoderCoherenceTheory.abi_decoder_coherent_layout_transport >>
     goal_assum (drule_at Any) >> simp[]) >>
  `calldata_encodes env fname (MAP SND args) vals s.vs_call_ctx.cc_calldata /\
   LENGTH s.vs_call_ctx.cc_calldata < dimword (:256)` by simp[] >>
  `j < LENGTH (MAP SND args)` by simp[] >>
  drule_at (Pat `LIST_REL (abi_decoder_coherent _ _ _) _ _`)
    registration_calldata_index_ready >>
  disch_then (drule_at (Pat `LIST_REL value_has_type _ _`)) >>
  disch_then (drule_at (Pat `calldata_encodes _ _ _ _ _`)) >>
  disch_then (qspecl_then [`j`,
    `SUM (MAP abi_member_head_size (TAKE j (MAP (vyper_to_abi_type env) (MAP SND args))))`]
    mp_tac) >>
  (impl_tac >- simp[]) >> strip_tac >>
  `abi_decoder_header ce1 env (SND (EL j args)) (EL j tvs)` by
    metis_tac[LIST_REL_EL_EQN, EL_MAP,
      abiDecoderCoherenceTheory.abi_decoder_coherent_header] >>
  qexistsl_tac [`is_word_type (SND (EL j args))`,
    `is_abi_dynamic ce0.ce_struct_fields (SND (EL j args))`,
    `abi_embedded_static_size ce0.ce_struct_fields (SND (EL j args))`,
    `av`, `delta`, `srcpos`] >>
  gvs[abiDecoderCoherenceTheory.abi_decoder_header_def, EL_MAP,
    MAP_TAKE, MAP_MAP_o, combinTheory.o_DEF] >>
  conj_tac >-
    (Cases_on `EL j args` >> simp[build_positional_arg_def] >>
     gvs[GSYM exprLoweringTheory.type_to_abi_dec_info_layout_cong]) >>
  strip_tac >> conj_tac
  >- metis_tac[entryDecodeStaticPropsTheory.word_type_dec_sizes] >>
  metis_tac[ctorArgDecodeTheory.ctor_arg_word_descriptor]
QED

Theorem registration_frontier_alloca_room:
  alloca_frontier_inv ctx fn site s /\
  unit_alloca_budget ctx < dimword (:256) ==> alloca_room ctx fn s
Proof
  `alloca_lit_size = alloca_size` by
    (simp[FUN_EQ_THM, exprLoweringPropsTheory.alloca_lit_size_def,
      vyperCompilerTheory.alloca_size_def]) >>
  strip_tac >>
  gvs[allocaFrontierBoundTheory.call_targets_card,
    exprLoweringPropsTheory.alloca_room_def,
    allocaFrontierBoundTheory.alloca_frontier_inv_def,
    exprLoweringPropsTheory.pending_alloca_size_def,
    allocaBudgetPropsTheory.remaining_alloca_budget_def,
    exprLoweringPropsTheory.unit_alloca_frame_def] >> decide_tac
QED

Theorem registration_no_dalloca_fmp_room:
  ~ctx_has_dalloca ctx /\
  lookup_function fn.fn_name ctx.ctx_functions = SOME fn ==> fmp_room ctx fn s
Proof
  strip_tac >> drule venomInstTheory.lookup_function_MEM >>
  gvs[ptrDisciplineTheory.ctx_has_dalloca_def,
    exprLoweringPropsTheory.fmp_room_def, EXISTS_MEM] >> metis_tac[]
QED

Theorem registration_owned_locals_endpoint_resources:
  lower_vyper_runtime_unit tops rpolicy = SOME unit /\
  supported_program tops /\ source_typing_ok tops am tx /\
  valid_vyper_call tops tx vs.vs_call_ctx.cc_calldata ret /\
  initial_venom_state_rel tops am tx vs /\
  lookup_function NONE tx.function_name External tops = SOME (mut,F,args,[],ret,fbody) /\
  bind_arguments (type_env tops) args tx.args = SOME env /\
  lookup_function "__entry" unit.cu_context.ctx_functions = SOME efn /\
  set_external_package_target target
    (package_external_fn tops ut nk (mut,F,rr,tx.function_name,args,[],ret,fbody)) =
    (lbl,cenv0,pos_args,mincd,pay,nr',key,ut',iv,fbody',rt) /\
  compile_register_positional_args cenv0 pos_args 4 st = (cenv,sa) /\
  fn_has_code st sa efn /\ fn_inst_ids_distinct efn /\
  vars_pc_only (vs with <|vs_prev_bb := NONE; vs_current_bb := elbl; vs_inst_idx := 0|>) s1 /\
  fresh_vars_wrt st s1 /\ ~s1.vs_halted /\
  s1.vs_current_bb = st.cs_current_bb /\ s1.vs_inst_idx = LENGTH st.cs_current_insts /\
  ~ctx_has_dalloca unit.cu_context ==>
  ?tvs s0 G0 tn0.
    LIST_REL (\ty tv. evaluate_type (type_env tops) ty = SOME tv) (MAP SND args) tvs /\
    local_ptrs_rel efn cenv [env] s0 /\
    (!j. j < LENGTH args ==> ?aid q p n inst.
      MEM inst (fn_insts efn) /\ inst.inst_opcode = ALLOCA /\
      inst.inst_outputs = [q] /\ inst.inst_id = aid /\
      aid < sa.cs_next_id /\ FLOOKUP s0.vs_allocas aid = SOME (p,n) /\
      FLOOKUP cenv.ce_vars (FST (EL j args)) = SOME (PtrVar (Var q) n) /\
      lookup_var q s0 = SOME (n2w p) /\ n = type_memory_size (EL j tvs) /\
      ptr_covers G0 tn0 q s0 n /\ val_wf (EL j tvs) (EL j tx.args) /\
      val_footprint (EL j tvs) (EL j tx.args) <= n /\
      (!mem. mem_agree_outside tn0.t_mem s0.vs_memory mem ==>
        val_in_memory (EL j tvs) (EL j tx.args) p mem)) /\
    cenv = cenv0 with ce_vars := cenv.ce_vars /\
    (!k. ~MEM k (MAP FST args) ==> FLOOKUP cenv.ce_vars k = NONE) /\
    alloca_inv s0 /\ alloca_frontier_inv unit.cu_context efn site s0 /\ allocas_from 0 s0 /\
    fresh_vars_wrt sa s0 /\ ~s0.vs_halted /\
    s0.vs_current_bb = sa.cs_current_bb /\ s0.vs_inst_idx = LENGTH sa.cs_current_insts /\
    tn0.t_stor = tn1.t_stor /\ tn0.t_trans = tn1.t_trans /\ tn0.t_imm = tn1.t_imm /\
    s0.vs_call_ctx = s1.vs_call_ctx /\ s0.vs_accounts = s1.vs_accounts /\
    s0.vs_transient = s1.vs_transient /\ s0.vs_logs = s1.vs_logs /\
    s0.vs_outcomes = s1.vs_outcomes /\ s0.vs_requests = s1.vs_requests /\
    s0.vs_pending_deletions = s1.vs_pending_deletions /\ s0.vs_tx_ctx = s1.vs_tx_ctx /\
    s0.vs_block_ctx = s1.vs_block_ctx /\ s0.vs_fmp = s1.vs_fmp /\
    s0.vs_gas_readings = s1.vs_gas_readings /\
    s0.vs_data_section = s1.vs_data_section /\
    (!inst w b n. MEM inst (fn_insts efn) /\ inst.inst_opcode = ALLOCA /\
      inst.inst_operands = [Lit w] /\
      FLOOKUP s0.vs_allocas inst.inst_id = SOME (b,n) ==> n = w2n w) /\
    (!D. (!fuel. ptr_safe_run D 0 fuel unit.cu_context efn [] G0 tn0 s0) ==>
      !fuel. ptr_safe_run D 0 fuel unit.cu_context efn [] G1 tn1 s1)
Proof
  strip_tac >> drule_all registration_owned_entry_inputs >>
  disch_then (qspec_then `site` strip_assume_tac) >>
  drule_at (Pat `LIST_REL (abi_decoder_coherent _ _ _) _ _`)
    registration_owned_source_ready >>
  disch_then (drule_at (Pat `calldata_encodes _ _ _ _ _`)) >>
  simp[] >> disch_tac >>
  drule_at (Pat `fresh_vars_wrt _ _`)
    (registration_owned_suffix_invariant_resources |> Q.SPEC
      `\aid q n. ?inst. MEM inst (fn_insts efn) /\ inst.inst_opcode = ALLOCA /\
        inst.inst_outputs = [q] /\ inst.inst_id = aid`) >>
  disch_then (qspec_then `efn` mp_tac) >>
  disch_then (drule_at (Pat `fn_has_code _ _ _`)) >>
  disch_then (drule_at (Pat `ALL_DISTINCT _`)) >>
  disch_then (qspecl_then [`cenv0`, `tvs`, `tx.args`, `type_env tops`] mp_tac) >>
  disch_then (drule_at (Pat `alloca_frontier_inv _ _ _ _`)) >>
  disch_then (drule_at (Pat `allocas_from _ _`)) >>
  disch_then (qspecl_then [`cenv0.ce_struct_fields`, `vs.vs_call_ctx`, `[]`,
    `0`, `cenv0`] mp_tac) >>
  disch_then (qspecl_then [`G1`, `tn1`, `cenv`] mp_tac) >>
  impl_tac >- (conj_tac >- (rpt gen_tac >> strip_tac >>
    drule_all registration_singleton_owner_instruction >>
    strip_tac >> simp_tac (srw_ss()) [] >>
    qexists_tac `mk_inst st2.cs_next_id ALLOCA [Lit (n2w n)] [q]` >>
    simp[venomInstTheory.mk_inst_def]) >>
    simp[var_location_memory_size_def] >>
    conj_tac >- (rpt strip_tac >>
      qpat_x_assum `!i. i < LENGTH args ==> ?off. _`
        (qspec_then `j` mp_tac) >> simp[] >>
      strip_tac >> goal_assum (drule_at Any) >>
      simp[var_location_memory_size_def]) >>
    conj_tac >- metis_tac[] >>
    first_assum ACCEPT_TAC) >>
  disch_then (qx_choosel_then [`s0`, `G0`, `tn0`] strip_assume_tac) >>
  qexistsl_tac [`tvs`, `s0`, `G0`, `tn0`] >>
  simp_tac (srw_ss()) [] >>
  conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac >- suspend "endpoint_locals" >>
  conj_tac >- (rpt strip_tac >>
    qpat_x_assum `!j. j < LENGTH args ==> ?aid q p n. _`
      (qspec_then `j` mp_tac) >> simp[] >> metis_tac[]) >>
  conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac >- suspend "endpoint_domain" >>
  qpat_x_assum `cenv = cenv0 with ce_vars := cenv.ce_vars` kall_tac >>
  gvs[] >> first_assum ACCEPT_TAC
QED

Resume registration_owned_locals_endpoint_resources[endpoint_locals]:
  rewrite_tac[local_ptrs_rel_def] >> conj_tac
  >- (rpt gen_tac >> strip_tac >>
    `FLOOKUP env name = SOME entry` by gvs[vyperStateTheory.lookup_scopes_def, AllCaseEqs()] >>
    drule_all vyperTypeBindArgumentsTheory.bind_arguments_scope_lookup >>
    strip_tac >>
    `?j. j < LENGTH args /\ EL j args = (name,typ)` by metis_tac[MEM_EL] >>
    drule_all bind_arguments_lookup_index >> strip_tac >>
    qpat_assum `LIST_REL (\ty tv. evaluate_type _ ty = SOME tv) _ _`
      (mp_tac o SRULE [LIST_REL_EL_EQN]) >>
    strip_tac >>
    `evaluate_type (type_env tops) (SND (EL j args)) = SOME (EL j tvs)` by
      metis_tac[EL_MAP] >>
    qpat_x_assum `!j. j < LENGTH args ==> ?aid q p n. _`
      (qspec_then `j` mp_tac) >> simp[] >> strip_tac >>
    qpat_x_assum `cenv = cenv0 with ce_vars := cenv.ce_vars` kall_tac >>
    gvs[] >>
    `p' + type_memory_size (EL j tvs) <= s0.vs_alloca_next` by
      metis_tac[venomMemDefsTheory.alloca_inv_def,
        venomMemDefsTheory.alloca_next_valid_def] >>
    `s0.vs_alloca_next < dimword (:256)` by
      (qpat_x_assum `alloca_frontier_inv _ _ _ s0` mp_tac >>
       simp[allocaFrontierBoundTheory.alloca_frontier_inv_def] >> decide_tac) >>
    `p' < dimword (:256)` by decide_tac >>
    simp[] >> conj_tac >- metis_tac[local_backed_def] >>
    irule memoryValueEncodingTheory.val_in_memory_memory_value_rel >>
    conj_tac
    >- (qpat_x_assum `LIST_REL value_has_type tvs tx.args`
          (mp_tac o SRULE [LIST_REL_EL_EQN]) >> simp[]) >>
    first_x_assum irule >> simp[mem_agree_outside_def]) >>
  `cenv0.ce_vars = (build_compile_env tops External mut tx.function_name args ret fbody ut).ce_vars /\
   cenv0.ce_imm_alloca = NONE` by
    (qpat_x_assum `set_external_package_target _ _ = _` mp_tac >>
     simp[package_external_fn_def] >>
     simp[set_external_package_target_def] >> strip_tac >>
     gvs[update_cenv_nonreentrant_def] >>
     rw[update_cenv_ret_abi_def, intCallCalleeTheory.build_compile_env_imm_alloca]) >>
  `local_ptrs_reserved cenv sa` by
    (qspecl_then [`tops`, `External`, `mut`, `tx.function_name`, `args`,
       `ret`, `fbody`, `ut`] strip_assume_tac build_compile_env_vars >>
     drule entryLocalsTheory.compile_register_positional_args_reserved >>
     impl_tac >- gvs[build_positional_args_FST] >> simp[]) >>
  `!name b sz. local_region cenv [env] s0 name b sz ==>
    ?q inst. FLOOKUP cenv.ce_vars name = SOME (PtrVar (Var q) sz) /\
      MEM inst (fn_insts efn) /\ inst.inst_outputs = [q] /\
      FLOOKUP s0.vs_allocas inst.inst_id = SOME (b,sz)` by
    (rpt gen_tac >> simp[local_region_def] >> strip_tac >>
     `FLOOKUP env name = SOME entry` by
       gvs[vyperStateTheory.lookup_scopes_def, AllCaseEqs()] >>
     drule_all vyperTypeBindArgumentsTheory.bind_arguments_scope_lookup >> strip_tac >>
     `?j. j < LENGTH args /\ EL j args = (name,typ)` by metis_tac[MEM_EL] >>
     qpat_x_assum `!j. j < LENGTH args ==> ?aid q p n. _`
       (qspec_then `j` mp_tac) >> simp[] >> strip_tac >>
     qpat_x_assum `cenv = cenv0 with ce_vars := cenv.ce_vars` kall_tac >>
     gvs[] >>
     `p' + type_memory_size (EL j tvs) <= s0.vs_alloca_next` by
       metis_tac[venomMemDefsTheory.alloca_inv_def,
         venomMemDefsTheory.alloca_next_valid_def] >>
     `s0.vs_alloca_next < dimword (:256)` by
       (qpat_x_assum `alloca_frontier_inv _ _ _ s0` mp_tac >>
        simp[allocaFrontierBoundTheory.alloca_frontier_inv_def] >> decide_tac) >>
     `p' < dimword (:256)` by decide_tac >> simp[] >> metis_tac[]) >>
  rpt gen_tac >> strip_tac >>
  qpat_assum `!name b sz. local_region _ _ _ _ _ _ ==> _`
    (qspecl_then [`n1`, `b1`, `sz1`] mp_tac) >>
  (impl_tac >- first_assum ACCEPT_TAC) >> strip_tac >>
  qpat_assum `!name b sz. local_region _ _ _ _ _ _ ==> _`
    (qspec_then `n2` mp_tac) >>
  disch_then (qspecl_then [`b2`, `sz2`] mp_tac) >>
  (impl_tac >- first_assum ACCEPT_TAC) >> strip_tac >>
  `q <> q'` by metis_tac[local_ptrs_reserved_def] >>
  `inst.inst_id <> inst'.inst_id` by
    (strip_tac >> `inst = inst'` by
       metis_tac[localPtrsPropsTheory.fn_inst_ids_distinct_inj] >> gvs[]) >>
  gvs[venomMemDefsTheory.alloca_inv_def,
      venomMemDefsTheory.allocas_non_overlapping_def] >>
  metis_tac[regions_disjoint_def]
QED

Resume registration_owned_locals_endpoint_resources[endpoint_domain]:
  drule compile_register_positional_args_cenv >> strip_tac >>
  rpt strip_tac >>
  qpat_x_assum `!n. ~MEM n (MAP FST pos_args) ==> _`
    (qspec_then `k` mp_tac) >>
  simp[build_positional_args_FST]
QED

Finalise registration_owned_locals_endpoint_resources

Theorem registration_owned_locals_endpoint:
  lower_vyper_runtime_unit tops rpolicy = SOME unit /\
  supported_program tops /\ source_typing_ok tops am tx /\
  valid_vyper_call tops tx vs.vs_call_ctx.cc_calldata ret /\
  initial_venom_state_rel tops am tx vs /\
  lookup_function NONE tx.function_name External tops = SOME (mut,F,args,[],ret,fbody) /\
  bind_arguments (type_env tops) args tx.args = SOME env /\
  lookup_function "__entry" unit.cu_context.ctx_functions = SOME efn /\
  set_external_package_target target
    (package_external_fn tops ut nk (mut,F,rr,tx.function_name,args,[],ret,fbody)) =
    (lbl,cenv0,pos_args,mincd,pay,nr',key,ut',iv,fbody',rt) /\
  compile_register_positional_args cenv0 pos_args 4 st = (cenv,sa) /\
  fn_has_code st sa efn /\ fn_inst_ids_distinct efn /\
  vars_pc_only (vs with <|vs_prev_bb := NONE; vs_current_bb := elbl; vs_inst_idx := 0|>) s1 /\
  fresh_vars_wrt st s1 /\ ~s1.vs_halted /\
  s1.vs_current_bb = st.cs_current_bb /\ s1.vs_inst_idx = LENGTH st.cs_current_insts /\
  ~ctx_has_dalloca unit.cu_context ==>
  ?tvs s0 G0 tn0.
    LIST_REL (\ty tv. evaluate_type (type_env tops) ty = SOME tv) (MAP SND args) tvs /\
    local_ptrs_rel efn cenv [env] s0 /\
    (!j. j < LENGTH args ==> ?aid q p n inst.
      MEM inst (fn_insts efn) /\ inst.inst_opcode = ALLOCA /\
      inst.inst_outputs = [q] /\ inst.inst_id = aid /\
      aid < sa.cs_next_id /\ FLOOKUP s0.vs_allocas aid = SOME (p,n) /\
      FLOOKUP cenv.ce_vars (FST (EL j args)) = SOME (PtrVar (Var q) n) /\
      lookup_var q s0 = SOME (n2w p) /\ n = type_memory_size (EL j tvs) /\
      ptr_covers G0 tn0 q s0 n /\ val_wf (EL j tvs) (EL j tx.args) /\
      val_footprint (EL j tvs) (EL j tx.args) <= n /\
      (!mem. mem_agree_outside tn0.t_mem s0.vs_memory mem ==>
        val_in_memory (EL j tvs) (EL j tx.args) p mem)) /\
    cenv = cenv0 with ce_vars := cenv.ce_vars /\
    (!k. ~MEM k (MAP FST args) ==> FLOOKUP cenv.ce_vars k = NONE) /\
    alloca_inv s0 /\ alloca_frontier_inv unit.cu_context efn site s0 /\ allocas_from 0 s0 /\
    fresh_vars_wrt sa s0 /\ ~s0.vs_halted /\
    s0.vs_current_bb = sa.cs_current_bb /\ s0.vs_inst_idx = LENGTH sa.cs_current_insts /\
    tn0.t_stor = tn1.t_stor /\ tn0.t_trans = tn1.t_trans /\ tn0.t_imm = tn1.t_imm /\
    s0.vs_call_ctx = s1.vs_call_ctx /\ s0.vs_accounts = s1.vs_accounts /\
    s0.vs_transient = s1.vs_transient /\ s0.vs_logs = s1.vs_logs /\
    s0.vs_outcomes = s1.vs_outcomes /\ s0.vs_requests = s1.vs_requests /\
    s0.vs_pending_deletions = s1.vs_pending_deletions /\ s0.vs_tx_ctx = s1.vs_tx_ctx /\
    s0.vs_block_ctx = s1.vs_block_ctx /\ s0.vs_fmp = s1.vs_fmp /\
    s0.vs_gas_readings = s1.vs_gas_readings /\
    (!D. (!fuel. ptr_safe_run D 0 fuel unit.cu_context efn [] G0 tn0 s0) ==>
      !fuel. ptr_safe_run D 0 fuel unit.cu_context efn [] G1 tn1 s1)
Proof
  strip_tac >> drule_all registration_owned_locals_endpoint_resources >>
  disch_then (qspecl_then [`tn1`, `site`, `G1`] strip_assume_tac) >>
  qexistsl_tac [`tvs`, `s0`, `G0`, `tn0`] >> simp[]
QED

Theorem registration_charge_margin:
  !total pending reserve budget:num.
    total + pending + reserve <= budget /\
    budget + 2 ** 65 < dimword (:256) ==>
    total + pending + reserve + 2 ** 65 < dimword (:256)
Proof
  rpt strip_tac >> decide_tac
QED

(* This numerical obstruction is not an accepted-program counterexample. *)
Theorem registration_budget_margin_probe[local]:
  dimword (:256) - 32 + 32 * 0 < dimword (:256) /\
  ~(dimword (:256) - 32 + 2 ** 65 < dimword (:256))
Proof
  simp[wordsTheory.dimword_def]
QED

Theorem registration_indexed_locals_ghost:
  bind_arguments tenv args vals = SOME env /\
  ALL_DISTINCT (MAP FST args) /\
  LIST_REL (\ty tv. evaluate_type tenv ty = SOME tv) (MAP SND args) tvs /\
  es.scopes = [env] /\
  (!j. j < LENGTH args ==> ?q p n.
    FLOOKUP cenv.ce_vars (FST (EL j args)) = SOME (PtrVar (Var q) n) /\
    lookup_var q s = SOME (n2w p) /\ p < dimword (:256) /\
    ptr_covers G tn q s n /\
    (!mem. mem_agree_outside tn.t_mem s.vs_memory mem ==>
      val_in_memory (EL j tvs) (EL j vals) p mem)) /\
  (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==>
    op_taint tn (Var x) = {}) /\
  tn.t_stor = {} /\ tn.t_trans = {} /\ tn.t_imm = {} ==>
  ghost_inv NONE cenv cx es G tn s
Proof
  strip_tac >>
  simp[bodyPtrDefsTheory.ghost_inv_def, bodyPtrDefsTheory.return_buf_ptr_def,
       bodyPtrDefsTheory.stor_taint_ok_def] >>
  rpt gen_tac >> strip_tac >>
  `FLOOKUP env name = SOME entry` by
    gvs[vyperStateTheory.lookup_scopes_def, AllCaseEqs()] >>
  drule_all vyperTypeBindArgumentsTheory.bind_arguments_scope_lookup >> strip_tac >>
  `?j. j < LENGTH args /\ EL j args = (name,typ)` by metis_tac[MEM_EL] >>
  drule_all bind_arguments_lookup_index >> strip_tac >>
  qpat_assum `LIST_REL (\ty tv. evaluate_type _ ty = SOME tv) _ _`
    (mp_tac o SRULE [LIST_REL_EL_EQN]) >> strip_tac >>
  `evaluate_type tenv (SND (EL j args)) = SOME (EL j tvs)` by
    metis_tac[EL_MAP] >>
  qpat_x_assum `!j. j < LENGTH args ==> ?q p n. _`
    (qspec_then `j` mp_tac) >> simp[] >> strip_tac >>
  gvs[]
QED

(* Storage and transient metadata observe only their own location classes. *)
Theorem module_location_relations_cong:
  !c1 c2 cx.
    c1.ce_module = c2.ce_module /\
    (!key slot. (FLOOKUP c1.ce_module_vars key = SOME (StorageLoc slot) <=>
      FLOOKUP c2.ce_module_vars key = SOME (StorageLoc slot))) /\
    (!key slot. (FLOOKUP c1.ce_module_vars key = SOME (TransientLoc slot) <=>
      FLOOKUP c2.ce_module_vars key = SOME (TransientLoc slot))) ==>
    (storage_vars_rel c1 cx <=> storage_vars_rel c2 cx) /\
    (transient_vars_rel c1 cx <=> transient_vars_rel c2 cx)
Proof
  rpt strip_tac >> simp[storage_vars_rel_def, transient_vars_rel_def]
QED

Theorem registration_actual_endpoint_relations:
  lower_vyper_runtime_unit tops rpolicy = SOME unit /\
  supported_program tops /\ source_typing_ok tops am tx /\
  source_storage_ok tops am tx /\ source_deployment_rel tops am tx /\
  valid_vyper_call tops tx vs.vs_call_ctx.cc_calldata ret /\
  initial_venom_state_rel tops am tx vs /\ call_outcomes_ok am tx vs.vs_outcomes /\
  lookup_function NONE tx.function_name External tops = SOME (mut,F,args,[],ret,fbody) /\
  bind_arguments (type_env tops) args tx.args = SOME env /\
  send_call_value mut (initial_evaluation_context am.sources am.layouts tx NONE)
    (initial_state am [env] with <|outcomes := SOME vs.vs_outcomes; requests := []|>) =
    (INL (),es0) /\
  lookup_function "__entry" unit.cu_context.ctx_functions = SOME efn /\
  set_external_package_target rpolicy.rpol_target
    (package_external_fn tops T (K global_nonreentrant_slot)
      (mut,F,lookup_raw_return_or_F (NONE:num option) tx.function_name External tops,
       tx.function_name,args,[],ret,fbody)) =
    (lbl,cenv0,pos_args,mincd,pay,F,key,ut',iv,fbody,rt) /\
  compile_register_positional_args cenv0 pos_args 4 st = (cenv,sa) /\
  vars_pc_only (vs with <|vs_prev_bb := NONE; vs_current_bb := elbl; vs_inst_idx := 0|>) s1 /\
  ~ctx_has_dalloca unit.cu_context /\
  LIST_REL (\ty tv. evaluate_type (type_env tops) ty = SOME tv) (MAP SND args) tvs /\
  local_ptrs_rel efn cenv [env] s0 /\
  (!j. j < LENGTH args ==> ?aid q p n.
    FLOOKUP s0.vs_allocas aid = SOME (p,n) /\
    FLOOKUP cenv.ce_vars (FST (EL j args)) = SOME (PtrVar (Var q) n) /\
    lookup_var q s0 = SOME (n2w p) /\ ptr_covers G0 tn0 q s0 n /\
    (!mem. mem_agree_outside tn0.t_mem s0.vs_memory mem ==>
      val_in_memory (EL j tvs) (EL j tx.args) p mem)) /\
  cenv = cenv0 with ce_vars := cenv.ce_vars /\
  alloca_inv s0 /\ alloca_frontier_inv unit.cu_context efn site s0 /\
  tn0.t_stor = {} /\ tn0.t_trans = {} /\ tn0.t_imm = {} /\
  s0.vs_call_ctx = s1.vs_call_ctx /\ s0.vs_accounts = s1.vs_accounts /\
  s0.vs_transient = s1.vs_transient /\ s0.vs_logs = s1.vs_logs /\
  s0.vs_outcomes = s1.vs_outcomes /\ s0.vs_requests = s1.vs_requests /\
  s0.vs_pending_deletions = s1.vs_pending_deletions /\ s0.vs_tx_ctx = s1.vs_tx_ctx /\
  s0.vs_block_ctx = s1.vs_block_ctx /\ s0.vs_data_section = s1.vs_data_section /\
  (!inst w b n. MEM inst (fn_insts efn) /\ inst.inst_opcode = ALLOCA /\
    inst.inst_operands = [Lit w] /\
    FLOOKUP s0.vs_allocas inst.inst_id = SOME (b,n) ==> n = w2n w) ==>
  stmt_state_rel unit.cu_context efn cenv
    (initial_evaluation_context am.sources am.layouts tx NONE) es0 s0 /\
  ghost_inv NONE cenv (initial_evaluation_context am.sources am.layouts tx NONE)
    es0 G0 tn0 s0
Proof
  strip_tac >>
  `ALL_DISTINCT (MAP FST args)` by
    (drule_all registration_source_parameter_inputs >> simp[]) >>
  drule send_call_value_accounts >> strip_tac >>
  `es0.scopes = [env]` by simp[initial_state_def] >>
  `unit_alloca_budget unit.cu_context < dimword (:256)` by
    (drule_all registration_initial_ptr_resources >>
     disch_then (qspec_then `site` strip_assume_tac) >> simp[]) >>
  conj_tac >- suspend "actual_stmt" >>
  irule registration_indexed_locals_ghost >>
  conj_tac >- suspend "actual_return_pc" >> simp[] >>
  qexistsl_tac [`args`, `type_env tops`, `tvs`, `tx.args`] >> simp[] >>
  suspend "actual_ghost_locals"
QED

Resume registration_actual_endpoint_relations[actual_ghost_locals]:
  rpt strip_tac >>
  qpat_x_assum `!j. j < LENGTH args ==> ?aid q p n. _`
    (qspec_then `j` mp_tac) >> simp[] >> strip_tac >>
  qexistsl_tac [`q`, `p`, `n`] >> simp[] >>
  `p + n <= s0.vs_alloca_next` by
    metis_tac[venomMemDefsTheory.alloca_inv_def,
      venomMemDefsTheory.alloca_next_valid_def] >>
  qpat_x_assum `alloca_frontier_inv _ _ _ s0` mp_tac >>
  simp[allocaFrontierBoundTheory.alloca_frontier_inv_def] >> decide_tac
QED

Resume registration_actual_endpoint_relations[actual_return_pc]:
  `cenv.ce_return_pc = cenv0.ce_return_pc` by
    (qpat_assum `cenv = cenv0 with ce_vars := cenv.ce_vars`
      (fn th => pure_once_rewrite_tac[th]) >> simp[]) >>
  `cenv0.ce_return_pc = NONE` by
    (qpat_x_assum `set_external_package_target _ _ = _` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >>
     simp[package_external_fn_def, set_external_package_target_def] >> strip_tac >>
     gvs[update_cenv_nonreentrant_def] >>
     rw[update_cenv_ret_abi_def, build_compile_env_def] >>
     rpt (pairarg_tac >> gvs[])) >> simp[]
QED

Resume registration_actual_endpoint_relations[actual_stmt]:
  `cenv0.ce_module = NONE /\ ~cenv0.ce_is_ctor /\
   cenv0.ce_imm_alloca = NONE /\
   cenv0.ce_module_vars = add_immutable_locations
     (get_struct_fields (make_struct_fields_map tops)) tops 0
     (add_module_var_locations tops FEMPTY)` by
    (qpat_x_assum `set_external_package_target _ _ = _` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >>
     simp[package_external_fn_def, set_external_package_target_def] >> strip_tac >>
     gvs[update_cenv_nonreentrant_def] >>
     rw[update_cenv_ret_abi_def, build_compile_env_def] >>
     rpt (pairarg_tac >> gvs[])) >>
  `cenv.ce_module = NONE /\ ~cenv.ce_is_ctor /\
   cenv.ce_imm_alloca = NONE /\ cenv.ce_module_vars = cenv0.ce_module_vars` by
    (qpat_assum `cenv = cenv0 with ce_vars := cenv.ce_vars`
      (fn th => pure_once_rewrite_tac[th]) >> simp[]) >>
  `alloca_room unit.cu_context efn s0` by
    (drule_all registration_frontier_alloca_room >> simp[]) >>
  `fmp_room unit.cu_context efn s0` by
    (irule registration_no_dalloca_fmp_room >> simp[] >>
     drule vyperCompilerTheory.lookup_function_result_name >> simp[]) >>
  simp[stmt_state_rel_def, immutable_alloca_sep_def, immutable_decl_sep_def,
       immutable_base_zero_def] >>
  conj_tac >- suspend "actual_state" >> first_assum ACCEPT_TAC
QED

Resume registration_actual_endpoint_relations[actual_state]:
  `storage_vars_rel cenv (initial_evaluation_context am.sources am.layouts tx NONE) /\
   transient_vars_rel cenv (initial_evaluation_context am.sources am.layouts tx NONE)` by
    suspend "actual_module_locations" >>
  `immutable_section_layout cenv tops` by
    (qspecl_then [`tops`, `External`, `mut`, `tx.function_name`, `args`, `ret`,
       `fbody`, `F`] mp_tac
       immutableLocationPropsTheory.immutable_build_compile_env_layout >>
     qpat_x_assum `cenv.ce_module_vars = cenv0.ce_module_vars` mp_tac >>
     qpat_x_assum `cenv0.ce_module_vars = _` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >>
     simp[immutableRelationTheory.immutable_section_layout_def,
       build_compile_env_def] >> rpt (pairarg_tac >> gvs[])) >>
  `immutables_rel cenv
    (initial_evaluation_context am.sources am.layouts tx NONE).txn.target
    cenv.ce_module cenv.ce_is_ctor es0 s0` by suspend "actual_immutables" >>
  qpat_x_assum `vars_pc_only _ s1` mp_tac >>
  simp[vars_pc_only_def, venom_state_component_equality] >> strip_tac >>
  gvs[initial_venom_state_rel_def, venom_env_rel_def, state_rel_def,
      initial_state_def, initial_evaluation_context_def] >>
  `s0.vs_call_ctx.cc_address = tx.target` by fs[call_ctx_rel_def] >>
  simp[storage_rel_def, transient_rel_def, contract_storage_def,
       contract_transient_def, logs_rel_def, accounts_rel_def]
QED

Resume registration_actual_endpoint_relations[actual_immutables]:
  simp[] >> irule immutableSectionRelTheory.immutables_section_rel_runtime_fallback >>
  qexistsl_tac [`vs.vs_data_section`, `tops`] >> simp[] >>
  qpat_x_assum `vars_pc_only _ s1` mp_tac >>
  simp[vars_pc_only_def, venom_state_component_equality] >> strip_tac >>
  gvs[initial_venom_state_rel_def, initial_state_def, e2eDefsTheory.account_immutables_def,
      initial_evaluation_context_def]
QED

Resume registration_actual_endpoint_relations[actual_module_locations]:
  `supported_declaration_headers tops` by fs[supported_program_def] >>
  drule source_typing_ok_vtype_keys_distinct >> strip_tac >>
  `storage_vars_rel
     (cenv with ce_module_vars := add_module_var_locations tops FEMPTY)
     (initial_evaluation_context am.sources am.layouts tx NONE) /\
   transient_vars_rel
     (cenv with ce_module_vars := add_module_var_locations tops FEMPTY)
     (initial_evaluation_context am.sources am.layouts tx NONE)` by
    (irule entry_storage_vars_rel >> simp[initial_evaluation_context_def] >>
     qexistsl_tac [`am`, `tops`, `tx`] >> simp[]) >>
  `(!key slot.
     (FLOOKUP (add_immutable_locations
       (get_struct_fields (make_struct_fields_map tops)) tops 0
       (add_module_var_locations tops FEMPTY)) key = SOME (StorageLoc slot) <=>
      FLOOKUP (add_module_var_locations tops FEMPTY) key = SOME (StorageLoc slot))) /\
   (!key slot.
     (FLOOKUP (add_immutable_locations
       (get_struct_fields (make_struct_fields_map tops)) tops 0
       (add_module_var_locations tops FEMPTY)) key = SOME (TransientLoc slot) <=>
      FLOOKUP (add_module_var_locations tops FEMPTY) key = SOME (TransientLoc slot)))` by
    (conj_tac >> rpt gen_tac >> eq_tac
     >- (strip_tac >> drule add_immutable_locations_FLOOKUP >> simp[])
     >- (strip_tac >> suspend "actual_insert")
     >- (strip_tac >> drule add_immutable_locations_FLOOKUP >> simp[]) >>
     strip_tac >> suspend "actual_insert") >>
  mp_tac (module_location_relations_cong |> Q.SPECL
    [`cenv`, `cenv with ce_module_vars := add_module_var_locations tops FEMPTY`,
     `initial_evaluation_context am.sources am.layouts tx NONE`]) >>
  simp[]
QED

Resume registration_actual_endpoint_relations[actual_insert]:
  markerLib.RESUME_TAC >> rpt strip_tac >>
  rename1 `FLOOKUP (add_module_var_locations tops FEMPTY) ky = SOME _` >>
  `!vis name ty sl.
    MEM (VariableDecl vis Immutable name ty sl) tops ==> (NONE,name) <> ky` by
    (rpt gen_tac >> strip_tac >> strip_tac >> gvs[] >>
     drule_then (qspecl_then
       [`FEMPTY`, `VariableDecl vis Immutable name ty sl`, `name`] mp_tac)
       add_module_var_locations_mem >>
     simp[vyperTypeContractTheory.toplevel_vtype_keys_toplevel_def] >>
     Cases_on `sl` >> simp[add_module_var_locations_def]) >>
  drule add_immutable_locations_lookup_unchanged >> simp[]
QED

Finalise registration_actual_endpoint_relations

Theorem registration_positional_args_ptr_no_dalloca:
  !tops rpolicy unit am tx ret vs mut args fbody env es0 efn elbl lbl cenv0
   pos_args min_cds is_payable nkey ut' iv rt st cenv sa s1 G1 tn1.
    lower_vyper_runtime_unit tops rpolicy = SOME unit /\
    supported_program tops /\ source_typing_ok tops am tx /\
    source_storage_ok tops am tx /\ source_deployment_rel tops am tx /\
    valid_vyper_call tops tx vs.vs_call_ctx.cc_calldata ret /\
    initial_venom_state_rel tops am tx vs /\ call_outcomes_ok am tx vs.vs_outcomes /\
    lookup_function NONE tx.function_name External tops =
      SOME (mut, F, args, [], ret, fbody) /\
    bind_arguments (type_env tops) args tx.args = SOME env /\
    send_call_value mut
      (initial_evaluation_context am.sources am.layouts tx NONE)
      (initial_state am [env] with
         <| outcomes := SOME vs.vs_outcomes; requests := [] |>) = (INL (), es0) /\
    lookup_function "__entry" unit.cu_context.ctx_functions = SOME efn /\
    fn_entry_label efn = SOME elbl /\
    set_external_package_target rpolicy.rpol_target
      (package_external_fn tops T (K global_nonreentrant_slot)
         (mut, F, lookup_raw_return_or_F (NONE : num option)
                     tx.function_name External tops,
          tx.function_name, args, [], ret, fbody)) =
      (lbl, cenv0, pos_args, min_cds, is_payable, F, nkey, ut', iv, fbody, rt) /\
    compile_register_positional_args cenv0 pos_args 4 st = (cenv, sa) /\
    fn_has_code st sa efn /\ fn_inst_ids_distinct efn /\
    vars_pc_only
      (vs with <| vs_prev_bb := NONE; vs_current_bb := elbl;
                  vs_inst_idx := 0 |>) s1 /\
    fresh_vars_wrt st s1 /\ ~s1.vs_halted /\
    s1.vs_current_bb = st.cs_current_bb /\
    s1.vs_inst_idx = LENGTH st.cs_current_insts /\
    tn1.t_mem = {} /\ tn1.t_stor = {} /\ tn1.t_trans = {} /\ tn1.t_imm = {} /\
    ~ctx_has_dalloca unit.cu_context ==>
    ?s0 G0 tn0.
      stmt_state_rel unit.cu_context efn cenv
        (initial_evaluation_context am.sources am.layouts tx NONE) es0 s0 /\
      ghost_inv NONE cenv
        (initial_evaluation_context am.sources am.layouts tx NONE) es0 G0 tn0 s0 /\
      ~s0.vs_halted /\ s0.vs_current_bb = sa.cs_current_bb /\
      s0.vs_inst_idx = LENGTH sa.cs_current_insts /\
      s0.vs_gas_readings = s1.vs_gas_readings /\
      !D. (!fuel. ptr_safe_run D 0 fuel unit.cu_context efn [] G0 tn0 s0) ==>
          !fuel. ptr_safe_run D 0 fuel unit.cu_context efn [] G1 tn1 s1
Proof
  rpt gen_tac >> strip_tac >>
  drule_all registration_owned_locals_endpoint_resources >>
  disch_then (qspecl_then [`tn1`, `ARB:instruction`, `G1`] strip_assume_tac) >>
  qexistsl_tac [`s0`, `G0`, `tn0`] >>
  `stmt_state_rel unit.cu_context efn cenv
     (initial_evaluation_context am.sources am.layouts tx NONE) es0 s0 /\
   ghost_inv NONE cenv
     (initial_evaluation_context am.sources am.layouts tx NONE) es0 G0 tn0 s0` by
    (`!j. j < LENGTH args ==> ?aid q p n.
       FLOOKUP s0.vs_allocas aid = SOME (p,n) /\
       FLOOKUP cenv.ce_vars (FST (EL j args)) = SOME (PtrVar (Var q) n) /\
       lookup_var q s0 = SOME (n2w p) /\ ptr_covers G0 tn0 q s0 n /\
       (!mem. mem_agree_outside tn0.t_mem s0.vs_memory mem ==>
         val_in_memory (EL j tvs) (EL j tx.args) p mem)` by
       (rpt strip_tac >>
        qpat_x_assum `!j. j < LENGTH args ==> ?aid q p n inst. _`
          (qspec_then `j` mp_tac) >> simp[] >> strip_tac >>
        qexistsl_tac [`inst.inst_id`, `q`, `p`, `type_memory_size (EL j tvs)`] >> simp[]) >>
     `tn0.t_stor = {} /\ tn0.t_trans = {} /\ tn0.t_imm = {}` by simp[] >>
     drule_all registration_actual_endpoint_relations >> simp[]) >> simp[]
QED

(* Registration seam, proved at the shared owned endpoint:
   it owns the caller side of the decoder contract.
   Hints (not binding):
   - Per argument, the decode is the is_prim word path (ADD, CALLDATALOAD,
     clamp, MSTORE), the dynamic path (head offset load, ADD 4, then
     compile_abi_decode_to_buf) or the static path (ADD, then
     compile_abi_decode_to_buf); for the latter two, entryPtrSeamDecoder's
     calldata_scratch_decoder_ptr is the contract, at lower = 0.
   - Its inputs (abi_scratch_decoder_input, abi_decoder_budget) come from
     valid_vyper_call's calldata_encodes and bind_arguments; the ordinary
     static-only precedent is entryStateRel's external_body_entry_state_rel
     with entryArgPtrs' register_positional_args_local_ptrs, and the
     memory-sourced builtin precedent is abiBuiltinValidCaller.
   - Earlier parameters stay robust: each later decode writes only its own
     buffer and its scratch slots and leaves taint and provenance of older
     variables alone (the contract's frame conjuncts).
   - A natural split, if one run cannot close it: one registration step
     (one parameter) against an invariant over the decoded prefix, then
     the induction over pos_args. *)
Theorem register_positional_args_ptr:
  !tops rpolicy unit am tx ret vs mut args fbody env es0 efn elbl lbl cenv0
   pos_args min_cds is_payable nkey ut' iv rt st cenv sa s1 G1 tn1.
    lower_vyper_runtime_unit tops rpolicy = SOME unit /\
    supported_program tops /\
    source_typing_ok tops am tx /\
    source_storage_ok tops am tx /\
    source_deployment_rel tops am tx /\
    valid_vyper_call tops tx vs.vs_call_ctx.cc_calldata ret /\
    initial_venom_state_rel tops am tx vs /\
    call_outcomes_ok am tx vs.vs_outcomes /\
    lookup_function NONE tx.function_name External tops =
      SOME (mut, F, args, [], ret, fbody) /\
    bind_arguments (type_env tops) args tx.args = SOME env /\
    send_call_value mut
      (initial_evaluation_context am.sources am.layouts tx NONE)
      (initial_state am [env] with
         <| outcomes := SOME vs.vs_outcomes; requests := [] |>) =
      (INL (), es0) /\
    lookup_function "__entry" unit.cu_context.ctx_functions = SOME efn /\
    fn_entry_label efn = SOME elbl /\
    set_external_package_target rpolicy.rpol_target
      (package_external_fn tops T (K global_nonreentrant_slot)
         (mut, F, lookup_raw_return_or_F (NONE : num option)
                     tx.function_name External tops,
          tx.function_name, args, [], ret, fbody)) =
      (lbl, cenv0, pos_args, min_cds, is_payable, F, nkey, ut', iv, fbody,
       rt) /\
    compile_register_positional_args cenv0 pos_args 4 st = (cenv, sa) /\
    fn_has_code st sa efn /\ fn_inst_ids_distinct efn /\
    vars_pc_only
      (vs with <| vs_prev_bb := NONE; vs_current_bb := elbl;
                  vs_inst_idx := 0 |>) s1 /\
    fresh_vars_wrt st s1 /\ ~s1.vs_halted /\
    s1.vs_current_bb = st.cs_current_bb /\
    s1.vs_inst_idx = LENGTH st.cs_current_insts /\
    tn1.t_mem = {} /\ tn1.t_stor = {} /\ tn1.t_trans = {} /\
    tn1.t_imm = {} ==>
    ?s0 G0 tn0.
      stmt_state_rel unit.cu_context efn cenv
        (initial_evaluation_context am.sources am.layouts tx NONE) es0 s0 /\
      ghost_inv NONE cenv
        (initial_evaluation_context am.sources am.layouts tx NONE) es0
        G0 tn0 s0 /\
      ~s0.vs_halted /\ s0.vs_current_bb = sa.cs_current_bb /\
      s0.vs_inst_idx = LENGTH sa.cs_current_insts /\
      s0.vs_gas_readings = s1.vs_gas_readings /\
      !D. (!fuel. ptr_safe_run D 0 fuel unit.cu_context efn [] G0 tn0 s0) ==>
          !fuel. ptr_safe_run D 0 fuel unit.cu_context efn [] G1 tn1 s1
Proof
  rpt gen_tac >> strip_tac >>
  `~ctx_has_dalloca unit.cu_context` by
    (drule_all registration_supported_no_dalloca >> simp[]) >>
  drule_all registration_positional_args_ptr_no_dalloca >> simp[]
QED
