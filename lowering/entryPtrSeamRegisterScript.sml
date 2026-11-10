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
