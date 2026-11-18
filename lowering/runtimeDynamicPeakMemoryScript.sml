(* Cumulative dynamic allocation over the raw recorder path. *)
Theory runtimeDynamicPeakMemory
Ancestors
  loweringCallBudgetBounds loweringCallBudgetHistory loweringBudgetDallocaWindows
  loweringBudgetRecorderOutcomes loweringRuntimeBudgetShape
  fmpLowerSequenceExec dallocaBounds contextCodegenRel venomInst
  vfmExecution vfmExecutionProp vfmCalldataBound vfmBuffer vfmTypes vfmConstants
  venomLayout venomState dallocaCalldata rawCallCalldataPeakMemory
  exprSimRawCallCalldata exprLoweringProps builtinSystem emitHelper fragExec
  compileVyper vyperCompiler vyperLoweringCorrect o1PassContract
  contextRawReachable ctxLookupAgreeHelpers venomExecProofs ptrDiscipline unitTransformDefs
  stepWriteFootprintBase
  compileEnv arithmetic list rich_list words finite_map

Theorem calldata_copy_zero_memory_expansion:
  es.contexts = (c, rb) :: rest ==>
  vfmExecution$copy_to_memory gas offset 0 0 (SOME get_call_data) es =
    consume_gas gas es
Proof
  simp[copy_to_memory_def, memory_expansion_info_def, consume_gas_def,
       get_call_data_def, get_current_context_def, set_current_context_def,
       vfmExecutionTheory.bind_def, vfmExecutionTheory.return_def,
       vfmExecutionTheory.assert_def, vfmExecutionTheory.ignore_bind_def,
       vfmExecutionTheory.expand_memory_def, vfmExecutionTheory.write_memory_def,
       word_size_def] >>
  strip_tac >> IF_CASES_TAC >> simp[]
QED

Theorem raw_reachable_at_active_inst[local]:
  raw_reachable vs0 ctx fn i0 s /\ active_inst fn i s ==>
  raw_reachable vs0 ctx fn i s
Proof
  once_rewrite_tac[raw_reachable_cases] >> strip_tac >>
  metis_tac[]
QED

Theorem raw_reachable_frag_reachable[local]:
  !ctx func s0 fn i s.
    frag_reachable ctx func s0 fn i s ==>
    !vs0 i0. raw_reachable vs0 ctx func i0 s0 ==>
      raw_reachable vs0 ctx fn i s
Proof
  ho_match_mp_tac frag_reachable_ind >>
  rpt conj_tac >> rpt gen_tac >> strip_tac >> rpt gen_tac >> strip_tac >>
  metis_tac[raw_reachable_at_active_inst, raw_reachable_rules]
QED

Theorem runtime_body_peak_memory_no_wrap:
  raw_reachable vs0 unit.cu_context func i0 s0 /\
  (!fn i s.
    raw_reachable vs0 unit.cu_context fn i s ==>
    s.vs_initial_fmp = fmp /\
    w2n s.vs_initial_fmp <= w2n s.vs_fmp /\
    fmp_frontier_rel cp_fmp (w2n fmp)
      (cp_fmp + (w2n s.vs_fmp - w2n fmp)) s.vs_fmp /\
    (i.inst_opcode = DALLOCA ==>
     w2n s.vs_fmp <= w2n fmp + 2 ** 64 * 2 ** 64 /\
     !sz_op sz.
       i.inst_operands = [sz_op] /\ eval_operand sz_op s = SOME sz ==>
       w2n s.vs_fmp + venomLayout$ceil32 (w2n sz) < dimword (:256))) ==>
  !fn inst s. frag_reachable unit.cu_context func s0 fn inst s ==>
    dalloca_no_wrap inst s
Proof
  rpt gen_tac >> strip_tac >> rpt gen_tac >> strip_tac >>
  drule_all raw_reachable_frag_reachable >> strip_tac >>
  qpat_x_assum `!fn i s. raw_reachable _ _ _ _ _ ==> _`
    (qspecl_then [`fn`, `inst`, `s`] mp_tac) >>
  simp[dalloca_no_wrap_def] >> rpt strip_tac >> res_tac
QED

(* Evaluated operands at the reached call use the very same length and
   pointer as the copy, with no intervening compiler-emitted instruction. *)
Theorem raw_call_msg_data_allocation_window:
  compile_msg_data_to_memory sa = ((data_ptr,data_len),sb) /\
  compile_raw_call_finish addr data_ptr data_len gas value call_ty n rev ov out sb =
    (result,sc) /\
  fn_has_code sa sc fn ==>
  ?bb call.
    lookup_block sa.cs_current_bb fn.fn_blocks = SOME bb /\
    isPREFIX (sa.cs_current_insts ++ emitted_insts sa sb ++ [call])
      bb.bb_instructions /\
    ((call.inst_opcode = CALL /\
      call.inst_operands = [gas;addr;value;data_ptr;data_len;out;Lit (n2w n)]) \/
     (MEM call.inst_opcode [STATICCALL;DELEGATECALL] /\
      call.inst_operands = [gas;addr;data_ptr;data_len;out;Lit (n2w n)]))
Proof
  strip_tac >>
  drule raw_call_finish_prefix >>
  disch_then (qx_choose_then `success` (qx_choose_then `after_call` strip_assume_tac)) >>
  `same_blocks sa sb /\ isPREFIX sa.cs_current_insts sb.cs_current_insts` by
    (qpat_x_assum `compile_msg_data_to_memory _ = _` mp_tac >>
     simp[compile_msg_data_to_memory_def, contextTheory.compile_alloc_dynamic_def,
          emit_op_def, emit_void_def, compileEnvTheory.comp_bind_def,
          compileEnvTheory.comp_ignore_bind_def, compileEnvTheory.comp_return_def,
          compileEnvTheory.fresh_var_def, compileEnvTheory.fresh_id_def,
          compileEnvTheory.emit_def, same_blocks_def, rich_listTheory.IS_PREFIX_APPEND] >>
     strip_tac >> gvs[] >> simp[IS_PREFIX_APPEND]) >>
  `sb.cs_current_insts = sa.cs_current_insts ++ emitted_insts sa sb` by
    fs[rich_listTheory.IS_PREFIX_APPEND, emitted_insts_def,
       rich_listTheory.DROP_LENGTH_APPEND] >>
  Cases_on `call_ty` >> gvs[] >>
  qpat_assum `emit_op _ _ _ = _` (strip_assume_tac o MATCH_MP emit_op_extends) >>
  qpat_assum `emit_op _ _ _ = _` (strip_assume_tac o MATCH_MP emitted_insts_emit_op_local) >>
  `cs_extends sa after_call` by
    (irule cs_extends_same_block >> fs[same_blocks_def, IS_PREFIX_APPEND] >>
     metis_tac[APPEND_ASSOC]) >>
  `fn_has_code after_call sc fn` by metis_tac[fn_has_code_split] >>
  qspecl_then [`after_call`, `sc`, `fn`] mp_tac fn_has_code_start >>
  simp[] >> strip_tac >> fs[same_blocks_def] >>
  rename1 `lookup_block _ fn.fn_blocks = SOME call_bb` >>
  qexists_tac `call_bb` >>
  qpat_assum `emitted_insts sb after_call = [_]`
    (fn th => exists_tac (hd (fst (listSyntax.dest_list (rhs (concl th)))))) >>
  gvs[mk_inst_def]
QED

Theorem raw_call_msg_data_site_peak_memory:
  compile_msg_data_to_memory sa = ((data_ptr,data_len),sb) /\
  LENGTH s.vs_call_ctx.cc_calldata < 2 ** 64 /\
  fmp_room ctx fn s /\ ctx_has_dalloca ctx /\
  w2n s.vs_fmp <= w2n s.vs_initial_fmp + 2 ** 64 * 2 ** 64 /\
  fmp_frontier_rel cp_fmp (w2n s.vs_initial_fmp) lo s.vs_fmp ==>
  ?pre t.
    run_inst_seq (TAKE 1 (emitted_insts sa sb)) s = OK pre /\
    eval_operand data_len pre =
      SOME (n2w (LENGTH s.vs_call_ctx.cc_calldata)) /\
    pre.vs_fmp = s.vs_fmp /\
    run_inst_seq (emitted_insts sa sb) s = OK t /\
    eval_operand data_ptr t = SOME pre.vs_fmp /\
    eval_operand data_len t = eval_operand data_len pre /\
    venomLayout$ceil32 (LENGTH s.vs_call_ctx.cc_calldata) <= 2 ** 64 /\
    w2n pre.vs_fmp + venomLayout$ceil32 (LENGTH s.vs_call_ctx.cc_calldata) <
      dimword (:256) /\
    lo + venomLayout$ceil32 (LENGTH s.vs_call_ctx.cc_calldata) < dimword (:256) /\
    fmp_room ctx fn t /\
    fmp_frontier_rel cp_fmp (w2n s.vs_initial_fmp)
      (lo + venomLayout$ceil32 (LENGTH s.vs_call_ctx.cc_calldata)) t.vs_fmp /\
    (!es c rb rest gas offset.
      es.contexts = (c, rb) :: rest /\
      s.vs_call_ctx.cc_calldata = buffer_to_list c.msgParams.data ==>
      (s.vs_call_ctx.cc_calldata = [] ==>
        copy_to_memory gas offset 0 0 (SOME get_call_data) es =
          consume_gas gas es) /\
      (s.vs_call_ctx.cc_calldata <> [] /\ wf_state es /\ calldata_bounded es /\
       2 ** 64 <= offset + LENGTH s.vs_call_ctx.cc_calldata ==>
        c.msgParams.gasLimit - c.gasUsed <
        memory_expansion_cost (buffer_length c.memory)
          (word_size (offset + LENGTH s.vs_call_ctx.cc_calldata) * 32)))
Proof
  strip_tac >>
  drule_all calldata_memory_prefix >> disch_then (qx_choose_then `pre` strip_assume_tac) >>
  `LENGTH s.vs_call_ctx.cc_calldata < dimword (:256)` by
    (fs[dimword_def, venomMemPropsTheory.dimindex_256] >> decide_tac) >>
  drule_all calldata_memory_run >> disch_then (qx_choose_then `t` strip_assume_tac) >>
  qexistsl_tac [`pre`, `t`] >>
  imp_res_tac dalloca_calldata_size_bound >>
  simp[] >>
  qspecl_then [`ctx`, `fn`, `cp_fmp`, `s.vs_initial_fmp`, `lo`, `0`,
    `ARB`, `ARB`, `ARB`, `ARB`, `s`] mp_tac raw_call_msg_data_peak_memory_oog_bridge >>
  disch_then (mp_tac o CONJUNCT2) >> simp[] >> strip_tac >> gvs[] >>
  qpat_x_assum `t = _`
    (fn th => MAP_EVERY (assume_tac o SIMP_RULE (srw_ss()) [] o
      (fn field => AP_TERM field th))
      [``\(v:venom_state). v.vs_allocas``,
       ``\(v:venom_state). v.vs_alloca_next``,
       ``\(v:venom_state). v.vs_initial_fmp``]) >>
  `fmp_room ctx fn t` by
    (irule fmp_room_fields >>
     qexists_tac `(write_memory_with_expansion (w2n s.vs_fmp)
       s.vs_call_ctx.cc_calldata s) with vs_fmp :=
       s.vs_fmp + n2w (venomLayout$ceil32 (LENGTH s.vs_call_ctx.cc_calldata))` >>
     fs[write_memory_with_expansion_def]) >>
  asm_rewrite_tac[] >> rpt gen_tac >> strip_tac >> conj_tac
  >- metis_tac[calldata_copy_zero_memory_expansion] >>
  strip_tac >>
  qspecl_then [`ctx`, `fn`, `cp_fmp`, `s.vs_initial_fmp`, `lo`,
    `offset + LENGTH s.vs_call_ctx.cc_calldata`, `es`, `c`, `rb`, `rest`, `s`]
    mp_tac raw_call_msg_data_peak_memory_oog_bridge >>
  simp[]
QED

Theorem runtime_raw_fmp_opcode_guards[local]:
  lower_vyper_runtime_unit source_tops rpolicy = SOME unit /\
  MEM fn unit.cu_context.ctx_functions /\ MEM i (fn_insts fn) ==>
  i.inst_opcode <> SETFMP /\ i.inst_opcode <> DRET
Proof
  strip_tac >>
  drule lower_vyper_runtime_unit_context_entry >> strip_tac >>
  `fn_ptr_ok_check (ctx_ptr_param_list unit.cu_context) fn` by
    (fs[lowering_context_ok_def, ptr_ok_check_def, EVERY_MEM] >> metis_tac[]) >>
  pop_assum mp_tac >>
  simp[fn_ptr_ok_check_def] >>
  rpt (BasicProvers.TOP_CASE_TAC >> simp[]) >>
  simp[EVERY_MEM] >> strip_tac >>
  qpat_x_assum `!inst. MEM inst (fn_insts fn) ==> _` drule >>
  simp[inst_ptr_ok_check_def]
QED

Theorem runtime_raw_started_state[local]:
  lower_vyper_runtime_unit source_tops rpolicy = SOME unit /\
  initial_venom_state_rel source_tops am tx vs /\
  raw_variant fmp vs0 vs /\
  raw_reachable vs0 unit.cu_context fn i s ==>
  ?entry lbl entered root h marks q.
    lookup_function "__entry" unit.cu_context.ctx_functions = SOME entry /\
    fn_entry_label entry = SOME lbl /\
    enters_block entry
      (vs0 with <| vs_prev_bb := NONE; vs_current_bb := lbl; vs_inst_idx := 0 |>)
      entered /\
    root = <| bp_stack := []; bp_params := []; bp_prov := FEMPTY;
              bp_taint := entry_taint; bp_fn := entry; bp_state := entered |> /\
    lower_budget_path F (D,lo,explicit,unit.cu_context) root h marks q /\
    entered.vs_initial_fmp = fmp /\ entered.vs_fmp = fmp /\
    entered.vs_outcomes = vs0.vs_outcomes /\
    entered.vs_call_ctx = vs0.vs_call_ctx /\
    q.bp_fn = fn /\ q.bp_state = s /\ active_inst fn i s
Proof
  strip_tac >>
  fs[raw_variant_def] >>
  drule_all lower_budget_raw_variant_entry >> strip_tac >>
  `vs0.vs_initial_fmp = fmp /\ vs0.vs_fmp = fmp /\ ~vs0.vs_halted` by
    fs[initial_venom_state_rel_def] >>
  drule lower_vyper_runtime_unit_context_entry >> strip_tac >>
  qspecl_then [`vs0`, `unit.cu_context`, `fn`, `i`, `s`, `D`, `lo`, `explicit`]
    mp_tac lower_budget_raw_history >> simp[] >> strip_tac >>
  gvs[] >>
  qpat_assum `enters_block _ _ _`
    (strip_assume_tac o REWRITE_RULE [enters_block_def]) >>
  drule eval_phis_only_updates_vs_vars >> strip_tac >>
  qpat_x_assum `s_phi = _`
    (fn th => MAP_EVERY (assume_tac o SIMP_RULE (srw_ss()) [] o
      (fn field => AP_TERM field th))
      [``\(v:venom_state). v.vs_initial_fmp``, ``\(v:venom_state). v.vs_fmp``,
       ``\(v:venom_state). v.vs_outcomes``, ``\(v:venom_state). v.vs_call_ctx``]) >>
  qexistsl_tac [`entered`, `h`, `marks`, `q`] >> fs[]
QED

(* A recorder prefix can include one larger, unpaired reservation at its
   end. The current-site condition excludes one immediately before another
   DALLOCA, so only completed, outcome-charged allocations contribute there. *)
Theorem lower_budget_path_peak_memory:
  lower_budget_path F (D,lo,explicit,ctx) root h marks q /\
  root.bp_stack = [] /\
  root.bp_state.vs_fmp = root.bp_state.vs_initial_fmp /\
  w2n root.bp_state.vs_initial_fmp < 2 ** 254 /\
  cp_fmp <= w2n root.bp_state.vs_initial_fmp /\
  LENGTH root.bp_state.vs_call_ctx.cc_calldata < 2 ** 64 /\
  LENGTH root.bp_state.vs_outcomes < 2 ** 64 /\
  lower_history_pairs h pair /\ lower_history_current h pair q /\
  (!a. a < LENGTH h /\ lower_event_allocates (EL a h) ==>
    ?fn ai pre op sz post.
      lower_alloc_record h a fn ai pre op sz post) /\
  MEM root.bp_fn ctx.ctx_functions /\
  (!fn i. MEM fn ctx.ctx_functions /\ MEM i (fn_insts fn) ==>
    i.inst_opcode <> SETFMP /\ i.inst_opcode <> DRET) ==>
  q.bp_state.vs_initial_fmp = root.bp_state.vs_initial_fmp /\
  w2n q.bp_state.vs_initial_fmp <= w2n q.bp_state.vs_fmp /\
  fmp_frontier_rel cp_fmp (w2n root.bp_state.vs_initial_fmp)
    (cp_fmp + (w2n q.bp_state.vs_fmp - w2n root.bp_state.vs_initial_fmp))
    q.bp_state.vs_fmp /\
  (!i. active_inst q.bp_fn i q.bp_state /\ i.inst_opcode = DALLOCA ==>
    w2n q.bp_state.vs_fmp <=
      w2n root.bp_state.vs_initial_fmp + 2 ** 64 * 2 ** 64 /\
    !op sz. i.inst_operands = [op] /\ eval_operand op q.bp_state = SOME sz ==>
      w2n q.bp_state.vs_fmp + venomLayout$ceil32 (w2n sz) < dimword (:256))
Proof
  strip_tac >>
  drule lower_budget_path_count_le_outcomes >> strip_tac >>
  `lower_history_count h <= 2 ** 64` by decide_tac >>
  qspecl_then [`F`, `D`, `lo`, `explicit`, `ctx`, `root`, `h`, `marks`, `q`]
    mp_tac lower_budget_path_fmp_guards >>
  (impl_tac >- asm_rewrite_tac[EVERY_DEF]) >> strip_tac >>
  `?charge. !a. a < LENGTH h /\ lower_event_allocates (EL a h) ==>
    ?fn ai pre op sz post.
      lower_alloc_record h a fn ai pre op sz post /\
      charge a = contractABI$ceil32 (w2n sz)` by
    (simp[GSYM SKOLEM_THM, RIGHT_EXISTS_IMP_THM] >> metis_tac[]) >>
  drule_all lower_budget_history_allocation_charge_bound >> strip_tac >>
  `w2n root.bp_state.vs_initial_fmp +
     SUM (MAP charge (FILTER (\a. lower_event_allocates (EL a h))
       (GENLIST I (LENGTH h)))) < dimword (:256)` by metis_tac[] >>
  drule lower_budget_path_fmp_envelope >>
  disch_then (qspec_then `charge` mp_tac) >>
  (impl_tac >- (asm_rewrite_tac[] >> metis_tac[])) >> strip_tac >>
  simp[fmp_frontier_rel_def] >> rpt strip_tac
  >- (`lower_history_count h * 2 ** 64 <= 2 ** 64 * 2 ** 64` by simp[] >>
      qpat_x_assum `!i. active_inst _ _ _ /\ _ ==> _`
        (qspec_then `i` mp_tac) >> simp[] >> strip_tac >> fs[] >> decide_tac) >>
  qspecl_then [`F`, `D`, `lo`, `explicit`, `ctx`, `root`, `h`, `marks`, `q`,
    `pair`] mp_tac lower_budget_history_fmp_nowrap >>
  (impl_tac >- (asm_rewrite_tac[] >> metis_tac[])) >>
  simp[contractABITheory.ceil32_def, fmpAlignmentTheory.ceil32_div_mul, MULT_COMM] >>
  disch_then (qspecl_then [`i`, `op`, `sz`] mp_tac) >> asm_rewrite_tac[]
QED

(* The compiler site proof supplies these three recorder facts at the raw
   prefix. Neither the invocation projection nor the arithmetic uses a
   memory-checked gas path. *)
Theorem lower_vyper_runtime_unit_dynamic_peak_memory_from_history:
  lower_vyper_runtime_unit source_tops rpolicy = SOME unit /\
  initial_venom_state_rel source_tops am tx vs /\ raw_variant fmp vs0 vs /\
  cp_fmp <= w2n fmp /\ w2n fmp < 2 ** 254 /\
  LENGTH vs0.vs_outcomes < 2 ** 64 /\
  LENGTH vs0.vs_call_ctx.cc_calldata < 2 ** 64 /\
  (!entry lbl entered root h marks q.
    lookup_function "__entry" unit.cu_context.ctx_functions = SOME entry /\
    fn_entry_label entry = SOME lbl /\
    enters_block entry
      (vs0 with <| vs_prev_bb := NONE; vs_current_bb := lbl; vs_inst_idx := 0 |>)
      entered /\
    root = <| bp_stack := []; bp_params := []; bp_prov := FEMPTY;
              bp_taint := entry_taint; bp_fn := entry; bp_state := entered |> /\
    lower_budget_path F (D,cp_fmp,explicit,unit.cu_context) root h marks q ==>
    ?pair. lower_history_pairs h pair /\ lower_history_current h pair q /\
      (!a. a < LENGTH h /\ lower_event_allocates (EL a h) ==>
        ?fn ai pre op sz post. lower_alloc_record h a fn ai pre op sz post)) ==>
  !fn i s.
    raw_reachable vs0 unit.cu_context fn i s ==>
    s.vs_initial_fmp = fmp /\
    w2n s.vs_initial_fmp <= w2n s.vs_fmp /\
    fmp_frontier_rel cp_fmp (w2n fmp)
      (cp_fmp + (w2n s.vs_fmp - w2n fmp)) s.vs_fmp /\
    (i.inst_opcode = DALLOCA ==>
     w2n s.vs_fmp <= w2n fmp + 2 ** 64 * 2 ** 64 /\
     !sz_op sz.
       i.inst_operands = [sz_op] /\ eval_operand sz_op s = SOME sz ==>
       w2n s.vs_fmp + venomLayout$ceil32 (w2n sz) < dimword (:256))
Proof
  strip_tac >> rpt gen_tac >> strip_tac >>
  mp_tac (Q.INST [`lo` |-> `cp_fmp`] runtime_raw_started_state) >>
  (impl_tac >- asm_rewrite_tac[]) >> strip_tac >>
  qpat_x_assum `!entry lbl entered root h marks q. _`
    (qspecl_then [`entry`, `lbl`, `entered`, `root`, `h`, `marks`, `q`] mp_tac) >>
  (impl_tac >- asm_rewrite_tac[]) >> strip_tac >>
  `MEM entry unit.cu_context.ctx_functions` by metis_tac[lookup_function_MEM] >>
  `!fn i. MEM fn unit.cu_context.ctx_functions /\ MEM i (fn_insts fn) ==>
    i.inst_opcode <> SETFMP /\ i.inst_opcode <> DRET` by
    metis_tac[runtime_raw_fmp_opcode_guards] >>
  mp_tac (Q.INST [`ctx` |-> `unit.cu_context`, `lo` |-> `cp_fmp`]
    lower_budget_path_peak_memory) >>
  (impl_tac >- (fs[] >> first_assum ACCEPT_TAC)) >> simp[] >> strip_tac >>
  qpat_x_assum `!i. active_inst _ i _ /\ _ ==> _`
    (qspec_then `i` mp_tac) >> simp[]
QED

Theorem lower_vyper_runtime_unit_dynamic_peak_memory_raw_call:
  lower_vyper_runtime_unit source_tops rpolicy = SOME unit /\
  initial_venom_state_rel source_tops am tx vs /\ raw_variant fmp vs0 vs /\
  cp_fmp <= w2n fmp /\ w2n fmp < 2 ** 254 /\
  LENGTH vs0.vs_outcomes < 2 ** 64 /\
  LENGTH vs0.vs_call_ctx.cc_calldata < 2 ** 64 /\
  (!fn i s. MEM fn unit.cu_context.ctx_functions /\ active_inst fn i s /\
      i.inst_opcode = DALLOCA ==> raw_call_dalloca_window fn i s) ==>
  !fn i s. raw_reachable vs0 unit.cu_context fn i s ==>
    s.vs_initial_fmp = fmp /\
    w2n s.vs_initial_fmp <= w2n s.vs_fmp /\
    fmp_frontier_rel cp_fmp (w2n fmp)
      (cp_fmp + (w2n s.vs_fmp - w2n fmp)) s.vs_fmp /\
    (i.inst_opcode = DALLOCA ==>
     w2n s.vs_fmp <= w2n fmp + 2 ** 64 * 2 ** 64 /\
     !sz_op sz.
       i.inst_operands = [sz_op] /\ eval_operand sz_op s = SOME sz ==>
       w2n s.vs_fmp + venomLayout$ceil32 (w2n sz) < dimword (:256))
Proof
  strip_tac >>
  mp_tac lower_vyper_runtime_unit_dynamic_peak_memory_from_history >>
  impl_tac >- (
    asm_rewrite_tac[] >> rpt strip_tac >>
    qpat_x_assum `root = _` SUBST_ALL_TAC >>
    drule lower_vyper_runtime_unit_context_entry >> strip_tac >>
    `MEM entry unit.cu_context.ctx_functions` by metis_tac[lookup_function_MEM] >>
    `!fn. MEM fn unit.cu_context.ctx_functions ==> ALL_DISTINCT (fn_labels fn)` by
      fs[lowering_context_ok_def, EVERY_MEM] >>
    `entered.vs_call_ctx = vs0.vs_call_ctx` by
      (qpat_x_assum `enters_block _ _ _` mp_tac >>
       simp[enters_block_def] >> strip_tac >>
       drule eval_phis_only_updates_vs_vars >>
       disch_then (mp_tac o AP_TERM ``\(v:venom_state). v.vs_call_ctx``) >>
       simp[]) >>
    mp_tac (Q.INST [`root` |-> `<| bp_stack := []; bp_params := [];
      bp_prov := FEMPTY; bp_taint := entry_taint; bp_fn := entry;
      bp_state := entered |>`, `ctx` |-> `unit.cu_context`, `lo` |-> `cp_fmp`,
      `start` |-> `vs0 with <|vs_prev_bb := NONE; vs_current_bb := lbl;
                            vs_inst_idx := 0|>`]
      lower_budget_raw_call_history_certificate) >>
    fs[])
  >> simp[]
QED
