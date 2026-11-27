(* Cumulative dynamic allocation over the raw recorder path. *)
Theory runtimeDynamicPeakMemory
Ancestors
  loweringCallBudgetBounds loweringCallBudgetHistory loweringBudgetDallocaWindows
  loweringBudgetRecorderOutcomes loweringRuntimeBudgetShape
  fmpLowerSequenceExec contextCodegenRel venomInst venomLayout venomState
  compileVyper vyperCompiler vyperLoweringCorrect o1PassContract
  contextRawReachable ctxLookupAgreeHelpers venomExecProofs ptrDiscipline unitTransformDefs
  stepWriteFootprintBase dallocaBounds
  compileEnv arithmetic list rich_list words finite_map

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

Theorem raw_fmp_opcode_guards[local]:
  lowering_context_ok ctx /\ MEM fn ctx.ctx_functions /\ MEM i (fn_insts fn) ==>
  i.inst_opcode <> SETFMP /\ i.inst_opcode <> DRET
Proof
  strip_tac >>
  `fn_ptr_ok_check (ctx_ptr_param_list ctx) fn` by
    (fs[lowering_context_ok_def, ptr_ok_check_def, EVERY_MEM] >> metis_tac[]) >>
  pop_assum mp_tac >>
  simp[fn_ptr_ok_check_def] >>
  rpt (BasicProvers.TOP_CASE_TAC >> simp[]) >>
  simp[EVERY_MEM] >> strip_tac >>
  qpat_x_assum `!inst. MEM inst (fn_insts fn) ==> _` drule >>
  simp[inst_ptr_ok_check_def]
QED

Theorem raw_started_state[local]:
  ~vs0.vs_halted /\ vs0.vs_initial_fmp = fmp /\ vs0.vs_fmp = fmp /\
  raw_reachable vs0 ctx fn i s ==>
  ?entry name lbl entered root h marks q.
    ctx.ctx_entry = SOME name /\
    lookup_function name ctx.ctx_functions = SOME entry /\
    fn_entry_label entry = SOME lbl /\
    enters_block entry
      (vs0 with <| vs_prev_bb := NONE; vs_current_bb := lbl; vs_inst_idx := 0 |>)
      entered /\
    root = <| bp_stack := []; bp_params := []; bp_prov := FEMPTY;
              bp_taint := entry_taint; bp_fn := entry; bp_state := entered |> /\
    lower_budget_path F (D,lo,explicit,ctx) root h marks q /\
    entered.vs_initial_fmp = fmp /\ entered.vs_fmp = fmp /\
    entered.vs_outcomes = vs0.vs_outcomes /\
    entered.vs_call_ctx = vs0.vs_call_ctx /\
    q.bp_fn = fn /\ q.bp_state = s /\ active_inst fn i s
Proof
  strip_tac >>
  qspecl_then [`vs0`, `ctx`, `fn`, `i`, `s`, `D`, `lo`, `explicit`]
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
  qexistsl_tac [`entered`, `h`, `marks`, `q`] >> fs[] >>
  metis_tac[]
QED

Theorem raw_reachable_dalloca_headroom_from_peak:
  ~vs0.vs_halted /\ vs0.vs_fmp = vs0.vs_initial_fmp /\
  w2n vs0.vs_initial_fmp < 2 ** 254 /\
  LENGTH vs0.vs_call_ctx.cc_calldata < 2 ** 64 /\
  raw_reachable vs0 ctx fn i s /\
  (i.inst_opcode = DALLOCA ==>
    w2n s.vs_fmp <= w2n vs0.vs_initial_fmp + 2 ** 64 * 2 ** 64) ==>
  dalloca_fmp_headroom i s
Proof
  simp[dalloca_fmp_headroom_def] >> strip_tac >> strip_tac >>
  `s.vs_call_ctx = vs0.vs_call_ctx` by
    (mp_tac (Q.INST [`fmp` |-> `vs0.vs_initial_fmp`] raw_started_state) >>
     (impl_tac >- simp[]) >> strip_tac >>
     drule lower_budget_path_charge_facts >> simp[]) >>
  `venomLayout$ceil32 (LENGTH s.vs_call_ctx.cc_calldata) <= 2 ** 64` by
    (irule dalloca_calldata_size_bound >> simp[]) >>
  qspecl_then [`w2n vs0.vs_initial_fmp`, `2 ** 64`] mp_tac dalloca_split_budget >>
  (impl_tac >- simp[]) >>
  gvs[MAX_DEF] >> IF_CASES_TAC >> gvs[] >> decide_tac
QED

Theorem lower_budget_path_completed_peak:
  lower_budget_path F (D,lo,explicit,ctx) root h marks q /\
  root.bp_stack = [] /\
  root.bp_state.vs_fmp = root.bp_state.vs_initial_fmp /\
  w2n root.bp_state.vs_initial_fmp < 2 ** 254 /\
  LENGTH root.bp_state.vs_call_ctx.cc_calldata < 2 ** 64 /\
  LENGTH root.bp_state.vs_outcomes < 2 ** 64 /\
  lower_history_pairs h pair /\
  (!a. a < LENGTH h /\ lower_event_allocates (EL a h) ==> pair a < LENGTH h) /\
  (!a. a < LENGTH h /\ lower_event_allocates (EL a h) ==>
    ?fn ai pre op sz post. lower_alloc_record h a fn ai pre op sz post) /\
  MEM root.bp_fn ctx.ctx_functions /\
  (!fn i. MEM fn ctx.ctx_functions /\ MEM i (fn_insts fn) ==>
    i.inst_opcode <> SETFMP /\ i.inst_opcode <> DRET) ==>
  w2n q.bp_state.vs_fmp <= w2n root.bp_state.vs_initial_fmp + 2 ** 64 * 2 ** 64
Proof
  strip_tac >>
  drule lower_budget_path_count_le_outcomes >> strip_tac >>
  `lower_history_count h <= 2 ** 64` by decide_tac >>
  qspecl_then [`F`, `D`, `lo`, `explicit`, `ctx`, `root`, `h`, `marks`, `q`]
    mp_tac lower_budget_path_fmp_guards >>
  impl_tac >- asm_rewrite_tac[EVERY_DEF] >> strip_tac >>
  `?charge. !a. a < LENGTH h /\ lower_event_allocates (EL a h) ==>
    ?fn ai pre op sz post.
      lower_alloc_record h a fn ai pre op sz post /\
      charge a = venomLayout$ceil32 (w2n sz)` by
    (simp[GSYM SKOLEM_THM, RIGHT_EXISTS_IMP_THM] >> metis_tac[]) >>
  qabbrev_tac `allocs = FILTER (\a. lower_event_allocates (EL a h))
    (GENLIST I (LENGTH h))` >>
  `LENGTH allocs <= lower_history_count h` by
    (drule lower_budget_paired_alloc_count >>
     `FILTER (\a. lower_event_allocates (EL a h) /\ pair a < LENGTH h)
        (GENLIST I (LENGTH h)) = allocs` by
       (rw[FILTER_EQ, MEM_GENLIST, Abbr `allocs`] >> metis_tac[]) >>
     simp[]) >>
  `SUM (MAP charge allocs) <= LENGTH allocs * 2 ** 64` by
    (once_rewrite_tac[MULT_COMM] >>
     rewrite_tac[GSYM combinatoricsTheory.SUM_MAP_K] >>
     irule combinatoricsTheory.SUM_MAP_LE >>
     simp[EVERY_MEM, Abbr `allocs`, MEM_FILTER, MEM_GENLIST] >>
     qx_gen_tac `a` >> strip_tac >>
     `pair a < LENGTH h` by (first_x_assum (qspec_then `a` mp_tac) >> simp[]) >>
     qpat_x_assum `!a. _ ==> ?fn ai pre op sz post. _`
       (qspec_then `a` mp_tac) >> simp[] >> strip_tac >>
     drule_all lower_budget_completed_allocation_charge_bound >> simp[]) >>
  `SUM (MAP charge allocs) <= 2 ** 64 * 2 ** 64` by
    (`LENGTH allocs <= 2 ** 64` by decide_tac >>
     `LENGTH allocs * 2 ** 64 <= 2 ** 64 * 2 ** 64` by simp[] >> decide_tac) >>
  `w2n root.bp_state.vs_initial_fmp + SUM (MAP charge allocs) < dimword (:256)` by
    (fs[wordsTheory.dimword_def, dimindex_256] >> decide_tac) >>
  drule lower_budget_path_fmp_envelope >>
  disch_then (qspec_then `charge` mp_tac) >>
  (impl_tac >- (fs[Abbr `allocs`] >> metis_tac[])) >>
  strip_tac >> fs[Abbr `allocs`] >> decide_tac
QED

Theorem raw_dalloca_headroom_from_history:
  lowering_context_ok ctx /\ ~vs0.vs_halted /\
  vs0.vs_fmp = vs0.vs_initial_fmp /\ w2n vs0.vs_initial_fmp < 2 ** 254 /\
  LENGTH vs0.vs_outcomes < 2 ** 64 /\
  LENGTH vs0.vs_call_ctx.cc_calldata < 2 ** 64 /\
  (!entry name lbl entered root h marks q i.
    ctx.ctx_entry = SOME name /\
    lookup_function name ctx.ctx_functions = SOME entry /\
    fn_entry_label entry = SOME lbl /\
    enters_block entry
      (vs0 with <|vs_prev_bb := NONE; vs_current_bb := lbl; vs_inst_idx := 0|>)
      entered /\
    root = <|bp_stack := []; bp_params := []; bp_prov := FEMPTY;
             bp_taint := entry_taint; bp_fn := entry; bp_state := entered|> /\
    lower_budget_path F (D,lo,explicit,ctx) root h marks q /\
    i.inst_opcode = DALLOCA /\ active_inst q.bp_fn i q.bp_state ==>
    ?pair. lower_history_pairs h pair /\
      (!a. a < LENGTH h /\ lower_event_allocates (EL a h) ==> pair a < LENGTH h) /\
      (!a. a < LENGTH h /\ lower_event_allocates (EL a h) ==>
        ?fn ai pre op sz post. lower_alloc_record h a fn ai pre op sz post)) ==>
  !fn i s. raw_reachable vs0 ctx fn i s ==> dalloca_fmp_headroom i s
Proof
  strip_tac >> rpt gen_tac >> strip_tac >>
  match_mp_tac (Q.INST [`ctx` |-> `ctx`, `fn` |-> `fn`, `vs0` |-> `vs0`]
    raw_reachable_dalloca_headroom_from_peak) >> simp[] >> strip_tac >>
  mp_tac (Q.INST [`fmp` |-> `vs0.vs_initial_fmp`, `lo` |-> `lo`]
    raw_started_state) >> impl_tac >- simp[] >> strip_tac >>
  qpat_x_assum `!entry name lbl entered root h marks q i. _`
    (qspecl_then [`entry`, `name`, `lbl`, `entered`, `root`, `h`, `marks`, `q`, `i`]
      mp_tac) >> simp[] >> strip_tac >>
  `MEM entry ctx.ctx_functions` by metis_tac[lookup_function_MEM] >>
  `!fn i. MEM fn ctx.ctx_functions /\ MEM i (fn_insts fn) ==>
    i.inst_opcode <> SETFMP /\ i.inst_opcode <> DRET` by
    metis_tac[raw_fmp_opcode_guards] >>
  mp_tac (Q.INST [`ctx` |-> `ctx`, `lo` |-> `lo`]
    lower_budget_path_completed_peak) >>
  impl_tac >- (fs[] >> metis_tac[]) >> simp[]
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
      charge a = venomLayout$ceil32 (w2n sz)` by
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
Theorem raw_dynamic_peak_memory_from_history:
  lowering_context_ok ctx /\
  ~vs0.vs_halted /\ vs0.vs_initial_fmp = fmp /\ vs0.vs_fmp = fmp /\
  cp_fmp <= w2n fmp /\ w2n fmp < 2 ** 254 /\
  LENGTH vs0.vs_outcomes < 2 ** 64 /\
  LENGTH vs0.vs_call_ctx.cc_calldata < 2 ** 64 /\
  (!entry name lbl entered root h marks q.
    ctx.ctx_entry = SOME name /\
    lookup_function name ctx.ctx_functions = SOME entry /\
    fn_entry_label entry = SOME lbl /\
    enters_block entry
      (vs0 with <| vs_prev_bb := NONE; vs_current_bb := lbl; vs_inst_idx := 0 |>)
      entered /\
    root = <| bp_stack := []; bp_params := []; bp_prov := FEMPTY;
              bp_taint := entry_taint; bp_fn := entry; bp_state := entered |> /\
    lower_budget_path F (D,cp_fmp,explicit,ctx) root h marks q ==>
    ?pair. lower_history_pairs h pair /\ lower_history_current h pair q /\
      (!a. a < LENGTH h /\ lower_event_allocates (EL a h) ==>
        ?fn ai pre op sz post. lower_alloc_record h a fn ai pre op sz post)) ==>
  !fn i s.
    raw_reachable vs0 ctx fn i s ==>
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
  mp_tac (Q.INST [`lo` |-> `cp_fmp`] raw_started_state) >>
  (impl_tac >- asm_rewrite_tac[]) >> strip_tac >>
  qpat_x_assum `!entry name lbl entered root h marks q. _`
    (qspecl_then [`entry`, `name`, `lbl`, `entered`, `root`, `h`, `marks`, `q`] mp_tac) >>
  (impl_tac >- asm_rewrite_tac[]) >> strip_tac >>
  `MEM entry ctx.ctx_functions` by metis_tac[lookup_function_MEM] >>
  `!fn i. MEM fn ctx.ctx_functions /\ MEM i (fn_insts fn) ==>
    i.inst_opcode <> SETFMP /\ i.inst_opcode <> DRET` by
    metis_tac[raw_fmp_opcode_guards] >>
  mp_tac (Q.INST [`ctx` |-> `ctx`, `lo` |-> `cp_fmp`]
    lower_budget_path_peak_memory) >>
  (impl_tac >- (fs[] >> first_assum ACCEPT_TAC)) >> simp[] >> strip_tac >>
  qpat_x_assum `!i. active_inst _ i _ /\ _ ==> _`
    (qspec_then `i` mp_tac) >> simp[]
QED
