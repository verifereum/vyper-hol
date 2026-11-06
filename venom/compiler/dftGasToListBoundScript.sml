Theory dftGasToListBound
Ancestors
  dftGasToListTrace dftGasOracleDefs venomExecSemantics venomInst venomState
  list arithmetic pred_set execEquivParamBase

Definition function_block_bound_def:
  function_block_bound k fn <=>
    !bb. MEM bb fn.fn_blocks ==> LENGTH bb.bb_instructions <= k
End

Definition context_block_bound_def:
  context_block_bound k ctx <=>
    !fn. MEM fn ctx.ctx_functions ==> function_block_bound k fn
End

Theorem member_measure_le_sum:
  !xs (f:'a -> num) x. MEM x xs ==> f x <= SUM (MAP f xs)
Proof
  Induct >> simp[] >> rpt strip_tac >> gvs[] >>
  first_x_assum drule >> disch_then (qspec_then `f` mp_tac) >> decide_tac
QED

Theorem context_block_bound_exists:
  !ctx. ?k. context_block_bound k ctx
Proof
  gen_tac >> qexists `SUM (MAP (\fn. SUM (MAP (\bb. LENGTH bb.bb_instructions)
                                  fn.fn_blocks)) ctx.ctx_functions)` >>
  rw[context_block_bound_def, function_block_bound_def] >>
  qspecl_then [`fn.fn_blocks`, `\bb. LENGTH bb.bb_instructions`]
    (drule_then assume_tac) member_measure_le_sum >>
  qspecl_then [`ctx.ctx_functions`,
    `\fn. SUM (MAP (\bb. LENGTH bb.bb_instructions) fn.fn_blocks)`]
    (drule_then assume_tac) member_measure_le_sum >>
  gvs[] >> decide_tac
QED

Theorem context_block_bound_lookup:
  context_block_bound k ctx /\
  lookup_function nm ctx.ctx_functions = SOME fn ==>
  function_block_bound k fn
Proof
  rw[context_block_bound_def] >> drule lookup_function_MEM >> metis_tac[]
QED

Theorem function_block_bound_lookup:
  function_block_bound k fn /\ lookup_block lbl fn.fn_blocks = SOME bb ==>
  LENGTH bb.bb_instructions <= k
Proof
  rw[function_block_bound_def, lookup_block_def] >>
  drule FIND_MEM >> metis_tac[]
QED

Definition shallow_count_def:
  shallow_count B ts =
    LENGTH (FILTER (\e. FST (SND e) <= B) (trace_events ts))
End

Theorem shallow_count_append:
  shallow_count B (xs ++ ys) = shallow_count B xs + shallow_count B ys
Proof
  simp[shallow_count_def, trace_events_append, FILTER_APPEND_DISTRIB]
QED

Theorem shallow_count_items[simp]:
  shallow_count B [] = 0 /\
  shallow_count B (TraceGas (p,d,i)::ts) =
    (if d <= B then 1 else 0) + shallow_count B ts /\
  shallow_count B (TraceVisit p d fn inst s::ts) = shallow_count B ts
Proof
  simp[shallow_count_def, trace_events_def] >>
  Cases_on `d <= B` >> simp[]
QED

Definition shallow_budget_def:
  (shallow_budget (k:num) 0 = (0:num)) /\
  (shallow_budget k (SUC n) =
     k * (1 + shallow_budget k n) + shallow_budget k n)
End


Theorem trace_shallow_bound:
  (!orc p d fuel ctx inst s.
    !k B. context_block_bound k ctx ==>
      shallow_count B (trace_step orc p d fuel ctx inst s) <=
      if d <= B then 1 + shallow_budget k (B-d) else 0) /\
  (!orc p d fuel ctx fn bb s.
    !k B. context_block_bound k ctx ==>
      shallow_count B (trace_block orc p d fuel ctx fn bb s) <=
      (LENGTH bb.bb_instructions - s.vs_inst_idx) *
      (if d <= B then 1 + shallow_budget k (B-d) else 0)) /\
  (!orc p d fuel ctx fn s.
    !k B. context_block_bound k ctx /\ function_block_bound k fn ==>
      shallow_count B (trace_blocks orc p d fuel ctx fn s) <=
      shallow_budget k (B-d))
Proof
  ho_match_mp_tac oracle_trace_defs_ind >> rpt conj_tac
  >- suspend "step"
  >- suspend "block"
  >> suspend "blocks"
QED

Resume trace_shallow_bound[step]:
  rpt gen_tac >> strip_tac >> rpt gen_tac >> strip_tac >>
  Cases_on `inst.inst_opcode = GAS`
  >- (simp[trace_step_eq] >> Cases_on `d <= B` >> simp[]) >>
  Cases_on `inst.inst_opcode = INVOKE`
  >- (Cases_on `decode_invoke inst`
      >- simp[trace_step_eq] >>
      rename1 `decode_invoke inst = SOME pair` >> PairCases_on `pair` >>
      Cases_on `lookup_function pair0 ctx.ctx_functions`
      >- simp[trace_step_eq] >>
      Cases_on `eval_operands pair1 s`
      >- simp[trace_step_eq] >>
      rename1 `lookup_function pair0 ctx.ctx_functions = SOME callee` >>
      rename1 `eval_operands pair1 s = SOME args` >>
      Cases_on `setup_callee callee args s`
      >- simp[trace_step_eq] >>
      gvs[] >> drule_all context_block_bound_lookup >> strip_tac >>
      first_x_assum drule_all >>
      disch_then (qspec_then `B` mp_tac) >>
      simp[trace_step_eq] >>
      Cases_on `d <= B`
      >- simp[] >>
      `B-d = 0` by decide_tac >> simp[shallow_budget_def]) >>
  simp[trace_step_eq]
QED

Resume trace_shallow_bound[block]:
  rpt gen_tac >> strip_tac >> rpt gen_tac >> strip_tac >>
  Cases_on `get_instruction bb s.vs_inst_idx`
  >- simp[Once trace_block_eq] >>
  rename1 `get_instruction bb s.vs_inst_idx = SOME inst` >> gvs[] >>
  qpat_x_assum `!k B. _` (qspecl_then [`k`,`B`] mp_tac) >>
  simp[] >> strip_tac >>
  `s.vs_inst_idx < LENGTH bb.bb_instructions`
    by gvs[get_instruction_def] >>
  `LENGTH bb.bb_instructions - s.vs_inst_idx =
     SUC (LENGTH bb.bb_instructions - SUC s.vs_inst_idx)` by decide_tac >>
  simp[Once trace_block_eq, shallow_count_append] >>
  Cases_on `ev_step orc p d fuel ctx inst s`
  >- (Cases_on `is_terminator inst.inst_opcode`
      >- (simp[MULT_CLAUSES] >> decide_tac) >>
      gvs[] >> first_x_assum drule_all >>
      disch_then (qspec_then `B` mp_tac) >>
      simp[MULT_CLAUSES] >> decide_tac) >>
  simp[MULT_CLAUSES] >> decide_tac
QED

Resume trace_shallow_bound[blocks]:
  rpt gen_tac >> strip_tac >> rpt gen_tac >> strip_tac >>
  namedCases_on `fuel` ["", "small"]
  >- simp[trace_blocks_zero] >>
  Cases_on `lookup_block s.vs_current_bb fn.fn_blocks`
  >- simp[Once trace_blocks_eq] >>
  rename1 `lookup_block s.vs_current_bb fn.fn_blocks = SOME bb` >>
  drule_all function_block_bound_lookup >> strip_tac >>
  qspecl_then [`s`, `bb.bb_instructions`] strip_assume_tac
    eval_phis_ok_or_error_defs
  >- (gvs[] >>
      qpat_x_assum `!k B. _` (qspecl_then [`k`,`B`] mp_tac) >>
      simp[] >> strip_tac >>
      simp[Once trace_blocks_eq, shallow_count_append] >>
      rename1 `eval_phis s bb.bb_instructions = OK s_phi` >>
      qmatch_goalsub_abbrev_tac `ev_block orc p (SUC d) small ctx bb entry` >>
      qmatch_asmsub_abbrev_tac `_ <= positions * cap` >>
      `positions <= k` by (simp[Abbr `positions`] >> decide_tac) >>
      `positions * cap <= k * cap` by simp[LE_MULT_RCANCEL] >>
      `shallow_count B (trace_block orc p (SUC d) small ctx fn bb entry) <=
         k * cap` by decide_tac >>
      qmatch_goalsub_abbrev_tac `shallow_count B continuation + _ <= _` >>
      `shallow_count B continuation <= shallow_budget k (B-SUC d)` by
        (simp[Abbr `continuation`] >>
         Cases_on `ev_block orc p (SUC d) small ctx bb entry`
         >- (rename1 `ev_block orc p (SUC d) small ctx bb entry = OK result` >>
             Cases_on `result.vs_halted` >> gvs[] >>
             first_x_assum drule_all >>
             disch_then (qspec_then `B` mp_tac) >> simp[]) >> simp[]) >>
      Cases_on `SUC d <= B`
      >- (`B-d = SUC (B-SUC d)` by decide_tac >>
          gvs[Abbr `cap`, shallow_budget_def] >> decide_tac) >>
      `B-d = 0 /\ B-SUC d = 0` by decide_tac >>
      gvs[Abbr `cap`, shallow_budget_def]) >>
  simp[Once trace_blocks_eq]
QED

Finalise trace_shallow_bound

Theorem context_shallow_bound:
  context_block_bound k ctx ==>
  shallow_count B (trace_context orc fuel ctx s) <= shallow_budget k B
Proof
  strip_tac >> Cases_on `ctx.ctx_entry`
  >- simp[trace_context_def] >>
  rename1 `ctx.ctx_entry = SOME nm` >>
  Cases_on `lookup_function nm ctx.ctx_functions`
  >- simp[trace_context_def] >>
  rename1 `lookup_function nm ctx.ctx_functions = SOME fn` >>
  drule_all context_block_bound_lookup >> strip_tac >>
  Cases_on `fn_entry_label fn`
  >- simp[trace_context_def, trace_function_def] >>
  simp[trace_context_def, trace_function_def] >>
  irule (SRULE [] (Q.SPECL [`orc`,`[]`,`0`] (cj 3 trace_shallow_bound))) >>
  simp[]
QED

Theorem finite_event_depth_bound:
  !support:gas_event set. FINITE support ==>
  ?B. !e. e IN support ==> FST (SND e) <= B
Proof
  ho_match_mp_tac FINITE_INDUCT >> conj_tac
  >- simp[] >>
  rpt strip_tac >>
  rename1 `!e. e IN event_set ==> FST (SND e) <= depth_limit` >>
  rename1 `new_event NOTIN event_set` >>
  qexists `MAX (FST (SND new_event)) depth_limit` >>
  rw[MAX_DEF] >> simp[]
QED

Theorem nonzero_count_le_shallow:
  !es:gas_event list.
  (!e. MEM e es /\ (orc:gas_event -> bytes32) e <> 0w ==> FST (SND e) <= B) ==>
  LENGTH (FILTER (\e. orc e <> 0w) es) <=
  LENGTH (FILTER (\e. FST (SND e) <= B) es)
Proof
  Induct >> simp[] >> rpt strip_tac >>
  `!e. MEM e es /\ orc e <> 0w ==> FST (SND e) <= B` by metis_tac[] >>
  first_x_assum drule >>
  Cases_on `orc h = 0w` >> Cases_on `FST (SND h) <= B` >>
  gvs[]
QED

Theorem context_nonzero_count_bounded:
  FINITE {e | orc e <> 0w} ==>
  ?N. !fuel. LENGTH (FILTER (\e. orc e <> 0w)
                (trace_events (trace_context orc fuel ctx s))) <= N
Proof
  strip_tac >> drule finite_event_depth_bound >> simp[] >>
  disch_then (qx_choose_then `B` assume_tac) >>
  qspec_then `ctx` (qx_choose_then `k` assume_tac)
    context_block_bound_exists >>
  qexists `shallow_budget k B` >> gen_tac >>
  irule LESS_EQ_TRANS >>
  qexists `shallow_count B (trace_context orc fuel ctx s)` >>
  reverse conj_tac >- (irule context_shallow_bound >> simp[]) >>
  simp[shallow_count_def] >> irule nonzero_count_le_shallow >> simp[]
QED
