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
  entryStateRel entryArgPtrs entryLocals
  entryDecodePlanProps entryDecodeProps bodySimEntry actualRegistrationCode
  vyperCompiler moduleLoweringProps exprLoweringProps vyperInterpreter
  vyperContext venomExecSemantics venomState compileEnv supportedProgram
  fragExec venomInst ptrDiscipline ptrSafeRun vyperLoweringCorrect
  loweringRuntimeCorrect bodyPtrDefs moduleLowering venomWf
  list rich_list selectorDispatch byte contractABI vyperABIRoundtrip
  valueEncoding entryDispatchProps ctorDeployInitcode abiCallerBuiltinInput compileVyper
  ctorDeployMemoryFrontier

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
       immutable_alloca_sep_def, local_ptrs_rel_def, local_region_def,
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

(* Existence of an entry ghost is separate from transporting an actual
   ghost along execution.  Empty taint makes ordinary local values robust. *)
Theorem local_ptrs_entry_ghost:
  local_ptrs_rel fn ce es.scopes s ==>
  ghost_inv NONE ce cx es
    (FUN_FMAP (\p. (0,s.vs_alloca_next)) (FDOM s.vs_vars)) entry_taint s
Proof
  strip_tac >>
  simp[ghost_inv_def, return_buf_ptr_def, stor_taint_ok_def,
       entry_taint_def, op_taint_def] >>
  rpt gen_tac >> strip_tac >>
  fs[local_ptrs_rel_def] >>
  first_x_assum drule_all >> strip_tac >>
  conj_tac
  >- (simp[ptr_covers_def, op_taint_def, entry_taint_def,
           finite_mapTheory.FLOOKUP_FUN_FMAP, lookup_var_def] >>
      gvs[lookup_var_def, finite_mapTheory.FLOOKUP_DEF]) >>
  gvs[lookup_var_def] >>
  drule calldataTypedRobustPtrTheory.clean_footprint_val_in_memory_robust >>
  disch_then drule >>
  disch_then (qspec_then `{}` mp_tac) >> simp[]
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
  simp[lower_vyper_runtime_unit_def] >>
  pairarg_tac >> simp[AllCaseEqs()] >>
  metis_tac[run_lowering_context_ok, run_lowering_entry]
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
       ?head b delta c.
         emit_op ADD [Lit 4w; Lit (n2w (off-4))] a = (head,b) /\
         emit_op CALLDATALOAD [head] b = (delta,c) /\
         emit_op ADD [Lit 4w; delta] c = (src,first)
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
  ?buf a src first.
    compile_alloc_buffer n st = (buf,a) /\
    ce' = ce with ce_vars updated_by
      (\m. m |+ (name,PtrVar buf.buf_operand n)) /\
    compile_getelemptr_abi (Lit 4w) dyn h CALLDATALOAD (Lit 0w) (Lit 0w)
      a = (src,first) /\
    compile_abi_decode_to_buf buf.buf_operand src CALLDATALOAD
      (Lit 0w) (Lit 0w) di first = ((),last)
Proof
  strip_tac >> drule_all registration_aggregate_prepare_phases >>
  strip_tac >> qexistsl_tac [`buf`, `a`, `src`, `first`] >> simp[] >>
  Cases_on `dyn` >>
  gvs[abiEncoderTheory.compile_getelemptr_abi_def,
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
    (drule_all decoderCalldataShellTheory.calldata_alloca_invariants_fields >>
     simp[]) >>
  `u.t_stor = tn.t_stor /\ u.t_trans = tn.t_trans /\ u.t_imm = tn.t_imm` by
    simp[step_taint_def, store_taint_def, adopt_reset_def, imm_taint_def, mk_inst_def] >>
  qpat_x_assum `H = step_prov _ _ _ _` kall_tac >>
  qpat_x_assum `u = step_taint _ _ _ _` kall_tac >>
  gvs[lookup_var_def, fresh_vars_wrt_def, allocas_from_def] >>
  simp[step_taint_def, store_taint_def, adopt_reset_def, imm_taint_def, mk_inst_def] >>
  gvs[]
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
  strip_tac >> drule_all registration_aggregate_phases >> strip_tac >>
  `cs_extends st a /\ cs_extends a first /\ cs_extends first last` by
    metis_tac[abiDecoderAppendTheory.cs_appends_abi_alloc_buffer,
      abiDecoderAppendTheory.cs_appends_abi_member_pointer,
      abiDecoderAppendTheory.cs_appends_abi_decode_mutual,
      fragExecTheory.cs_appends_def] >>
  `fn_has_code st a fn /\ fn_has_code a first fn /\ fn_has_code first last fn` by
    metis_tac[fragExecTheory.fn_has_code_split, compileEnvTheory.cs_extends_trans] >>
  `!entry. FLOOKUP s.vs_allocas st.cs_next_id = SOME entry ==>
    ?p. entry = (p,type_memory_size tv) /\ p+type_memory_size tv < dimword (:256)` by
    (rpt strip_tac >> first_x_assum drule >> simp[]) >>
  `ALL_DISTINCT (MAP (\i. i.inst_id) (fn_insts fn))` by
    gvs[fn_inst_ids_distinct_def, venomInstTheory.fn_insts_def,
        allocaFrontierBoundTheory.fn_insts_blocks_inst_ids] >>
  drule_all registration_argument_prepare_forward_robust_ptr >>
  disch_then (qspecl_then [`tn`, `PG`, `G`] strip_assume_tac) >>
  rename1 `lookup_var q ready = SOME (n2w p)` >>
  drule_all registration_preparation_forward_slots >> strip_tac >>
  `st.cs_next_id < first.cs_next_id` by
    ( `emit_op ALLOCA [Lit (n2w (type_memory_size tv))] st = (buf.buf_operand,a)` by
        (qpat_x_assum `compile_alloc_buffer _ _ = _` mp_tac >>
         simp[contextTheory.compile_alloc_buffer_def, comp_bind_def, comp_return_def] >>
         pairarg_tac >> simp[] >> strip_tac >> gvs[]) >>
      drule emitHelperPropsTheory.emitted_insts_emit_op >> strip_tac >>
      fs[cs_extends_def]) >>
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
       drule >> simp[])) >>
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
     metis_tac[optionTheory.NOT_NONE_SOME]) >>
  `t.vs_call_ctx = s.vs_call_ctx` by
    (qpat_x_assum `abi_decode_footprint_frame _ ready t`
       (strip_assume_tac o REWRITE_RULE [abiDecoderFrameTheory.abi_decode_footprint_frame_def]) >>
     metis_tac[]) >>
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

Resume registration_aggregate_singleton_ptr_framed[old_local]:
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

Finalise registration_aggregate_singleton_ptr_framed

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
  strip_tac >>
  `compile_register_positional_args ce
    [(name,F,dyn,sz,type_to_abi_dec_info sf ce ty)] (4+h) st = (ce',last)` by
    (Cases_on `prim` >> gvs[registration_primitive_as_aggregate]) >>
  drule_all registration_aggregate_singleton_ptr_framed >>
  simp[]
QED

(* SEAM (cheated; proved by its own alan run).  This is the largest seam:
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
      (package_external_fn tops F (assign_nkeys tops 0)
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
  cheat
QED
