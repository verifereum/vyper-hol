(* Dispatch NONE does not require the successful-call storage or GAS premises. *)
Theory entryCreateReject
Ancestors
  entryCreateNativeCut requestCutNativeAbortVisit dftGasFromListTraceDefs
  e2eCorrectness vyperLoweringCorrect vyperCompiler e2eDefs
  venomRunBounded venomExecSemantics venomState venomInst venomWf
  lowerDloadDefs o1PassContract contextCodegenRel
  vfmConstants words list arithmetic

(* A reached primitive decoding error is propagated even through INVOKE. *)
Theorem reject_trace_primitive_error[local]:
  (!p d fuel C f head s.
    !key g i t e. MEM (key,g,i,t) (trace_step p d fuel C f head s) /\
      i.inst_opcode <> INVOKE /\ step_inst_base i t = Error e ==>
      step_inst fuel C head s = Error e) /\
  (!p d fuel C f bb s.
    !key g i t e. MEM (key,g,i,t) (trace_block p d fuel C f bb s) /\
      i.inst_opcode <> INVOKE /\ step_inst_base i t = Error e ==>
      exec_block fuel C bb s = Error e) /\
  (!p d fuel C f s.
    !key g i t e. MEM (key,g,i,t) (trace_blocks p d fuel C f s) /\
      i.inst_opcode <> INVOKE /\ step_inst_base i t = Error e ==>
      run_blocks fuel C f s = Error e)
Proof
  ho_match_mp_tac trace_defs_ind >> rpt conj_tac
  >- (rpt gen_tac >> strip_tac >> rpt gen_tac >>
      reverse (Cases_on `head.inst_opcode = INVOKE`) >- simp[trace_step_noninvoke] >>
      Cases_on `decode_invoke head` >- simp[Once trace_defs] >>
      rename1 `decode_invoke head = SOME pair` >> PairCases_on `pair` >>
      Cases_on `lookup_function pair0 C.ctx_functions` >- simp[Once trace_defs] >>
      rename1 `lookup_function _ _ = SOME callee` >>
      Cases_on `eval_operands pair1 s` >- simp[Once trace_defs] >>
      rename1 `eval_operands _ _ = SOME args` >>
      Cases_on `setup_callee callee args s` >- simp[Once trace_defs] >>
      simp[Once trace_defs] >> strip_tac >>
      `?cs. setup_callee callee args s = SOME cs /\ run_blocks fuel C callee cs = Error e`
        by metis_tac[] >> simp[step_inst_def])
  >- (rpt gen_tac >> strip_tac >> rpt gen_tac >>
      Cases_on `get_instruction bb s.vs_inst_idx` >- simp[Once trace_defs] >>
      rename1 `get_instruction bb s.vs_inst_idx = SOME head` >>
      once_rewrite_tac[cj 2 trace_defs, exec_block_def] >> simp[MEM_APPEND] >>
      strip_tac
      >- gvs[step_inst_non_invoke]
      >- (`step_inst fuel C head s = Error e` by metis_tac[] >> simp[]) >>
      Cases_on `step_inst fuel C head s` >> gvs[] >>
      Cases_on `is_terminator head.inst_opcode` >> gvs[] >> metis_tac[]) >>
  rpt gen_tac >> strip_tac >> rpt gen_tac >>
  namedCases_on `fuel` ["", "small"] >- simp[] >>
  Cases_on `lookup_block s.vs_current_bb f.fn_blocks` >- simp[Once trace_defs] >>
  rename1 `lookup_block _ _ = SOME bb` >>
  Cases_on `eval_phis s bb.bb_instructions` >>
  once_rewrite_tac[cj 3 trace_defs, run_blocks_def] >> simp[MEM_APPEND] >>
  strip_tac
  >- (rename1 `eval_phis _ _ = OK phi` >>
      `exec_block small C bb (phi with vs_inst_idx := phi_prefix_length bb.bb_instructions) = Error e`
        by metis_tac[] >> simp[]) >>
  qmatch_asmsub_abbrev_tac `exec_block small C bb en` >>
  Cases_on `exec_block small C bb en` >> gvs[] >>
  rename1 `exec_block _ _ _ _ = OK after` >> Cases_on `after.vs_halted` >> gvs[] >>
  metis_tac[]
QED

Theorem reject_context_primitive_error[local]:
  MEM (key,f,i,t) (trace_context fuel C s) /\
  i.inst_opcode <> INVOKE /\ step_inst_base i t = Error e ==>
  run_context fuel C s = Error e
Proof
  Cases_on `C.ctx_entry` >- simp[trace_context_def] >>
  rename1 `C.ctx_entry = SOME nm` >>
  Cases_on `lookup_function nm C.ctx_functions` >- simp[trace_context_def] >>
  rename1 `lookup_function _ _ = SOME entry` >>
  Cases_on `fn_entry_label entry` >>
  simp[trace_context_def, trace_function_def, run_context_def, run_function_def] >>
  metis_tac[cj 3 reject_trace_primitive_error]
QED

Theorem oversized_create_stops[local]:
  ~inst_create_size_ok i s ==>
  i.inst_opcode <> INVOKE /\
  ((?err. step_inst_base i s = Error err) \/
   step_inst_base i s = Abort ExHalt_abort (halt_state (set_returndata [] s)))
Proof
  rw[inst_create_size_ok_def] >>
  `2 * max_code_size < w2n sz_w` by decide_tac >>
  simp[Once step_inst_base_def] >> simp[Once step_inst_base_def] >>
  rpt (BasicProvers.TOP_CASE_TAC >> gvs[exec_create_abort_iff, Once exec_create_def])
QED

Theorem reject_raw_create_size:
  !tops rpolicy unit am tx vs vi fmp.
    lower_vyper_runtime_unit tops rpolicy = SOME unit /\
    supported_program tops /\ source_typing_ok tops am tx /\
    source_deployment_rel tops am tx /\
    calldata_dispatch tops vs.vs_call_ctx.cc_calldata = NONE /\
    initial_venom_state_rel tops am tx vs /\
    (ctx_has_dalloca unit.cu_context ==>
      w2n fmp < 2 ** 254 /\
      unit_alloca_budget unit.cu_context +
        32 * ctx_dload_count unit.cu_context <= w2n fmp) /\
    code_layout_valid vs /\ raw_variant fmp vi vs ==>
    !fn inst s. raw_reachable vi unit.cu_context fn inst s ==>
      inst_create_size_ok inst s
Proof
  rpt gen_tac >> strip_tac >>
  drule_all raw_variant_revert_facts_fmp >> strip_tac >>
  drule lower_vyper_runtime_unit_context_entry >> strip_tac >>
  `EVERY wf_function unit.cu_context.ctx_functions` by
    fs[lowering_context_ok_def, ptr_ok_check_def, EVERY_MEM] >>
  rpt gen_tac >> strip_tac >>
  rename1 `raw_reachable vi unit.cu_context hit inst st` >>
  `!err. run_context fuel unit.cu_context vi <> Error err` by simp[] >>
  drule_all reached_on_selected_prefix >> strip_tac >>
  `MEM ((p,d,inst.inst_id),hit,inst,st) (trace_context fuel unit.cu_context vi)` by simp[] >>
  CCONTR_TAC >> drule oversized_create_stops >> strip_tac
  >- (drule_all reject_context_primitive_error >> simp[]) >>
  drule_all native_trace_context_primitive_abort >> simp[]
QED
