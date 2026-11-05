Theory makeSsaCurrentCompletedReinsertion
Ancestors makeSsaCurrentCompletedOrdinary makeSsaCurrentReinsertedReady
  makeSsaCurrentRuntimeTransport makeSsaCurrentSemanticHistory
  makeSsaCurrentExecutionHistory makeSsaCurrentRetainedNonclobber
  makeSsaCurrentCleanupRuntime venomExecSemantics venomExecProps venomWf
  venomState venomInst stateFrame finite_map list rich_list

Theorem current_eval_phis_maximal_append:
  !pre tail. EVERY (\inst. inst.inst_opcode = PHI) pre /\
    (tail = [] \/ (HD tail).inst_opcode <> PHI) ==>
    eval_phis incoming (pre ++ tail) = eval_phis incoming pre
Proof
  Induct >- (Cases >> simp[eval_phis_def]) >>
  rpt strip_tac >> gvs[eval_phis_def]
QED

Theorem current_actual_interval_nonclobber:
  lookup_block h fn.fn_blocks = SOME out /\ out.bb_instructions = pre ++ tail /\
  ALL_DISTINCT (FLAT (MAP (\inst. inst.inst_outputs) out.bb_instructions)) /\
  MEM src (FLAT (MAP (\inst. inst.inst_outputs) pre)) /\
  current_actual_prefix fn C loc start phases next result before /\
  (!phase. MEM phase phases ==> phase = CurrentControl \/
    ?i inst. phase = CurrentOrdinary h i inst /\ LENGTH pre <= i /\ i < c) ==>
  lookup_var src before = lookup_var src start
Proof
  strip_tac >>
  drule current_actual_prefix_occurs >> strip_tac >>
  drule current_actual_prefix_history >>
  disch_then (qspec_then `0` strip_assume_tac) >>
  irule current_semantic_history_output_no_write >>
  goal_assum $ drule_at Any >> rpt strip_tac >>
  `phase = CurrentControl \/
    ?i inst. phase = CurrentOrdinary h i inst /\ LENGTH pre <= i /\ i < c` by metis_tac[]
  >- gvs[current_phase_outputs_def] >>
  gvs[current_phase_outputs_def] >>
  `current_phase_occurs fn (CurrentOrdinary h i inst)` by metis_tac[EVERY_MEM] >>
  gvs[current_phase_occurs_def] >>
  gvs[get_instruction_def, AllCaseEqs()] >>
  fs[ALL_DISTINCT_APPEND, EL_APPEND_EQN] >>
  `i - LENGTH pre < LENGTH tail` by decide_tac >>
  `MEM src (FLAT (MAP (\inst. inst.inst_outputs) tail))` by
    (simp[NoAsms, MEM_FLAT, MEM_MAP] >>
     qexists `(EL (i-LENGTH pre) tail).inst_outputs` >>
     reverse conj_tac >- first_assum ACCEPT_TAC >>
     qexists `EL (i-LENGTH pre) tail` >> simp[EL_MEM]) >>
  metis_tac[]
QED

Theorem current_actual_retained_copy_ready:
  lookup_block h fn.fn_blocks = SOME out /\ out.bb_instructions = pre ++ tail /\
  EVERY (\inst. inst.inst_opcode = PHI) pre /\
  (tail = [] \/ (HD tail).inst_opcode <> PHI) /\
  ALL_DISTINCT (FLAT (MAP (\inst. inst.inst_outputs) out.bb_instructions)) /\
  r < LENGTH pre /\ LENGTH pre <= c /\ c < LENGTH out.bb_instructions /\
  eval_one_phi incoming (EL r pre) = SOME (src,value) /\
  eval_phis incoming out.bb_instructions = OK post /\
  (EL c out.bb_instructions).inst_opcode = ASSIGN /\
  (EL c out.bb_instructions).inst_operands = [Var src] /\
  (EL c out.bb_instructions).inst_outputs = [dst] /\
  current_actual_prefix fn C (CurrentBody fuel out)
    (post with vs_inst_idx := LENGTH pre) phases
    (SOME (CurrentBody fuel out)) (OK before) before /\
  before.vs_current_bb = h /\ before.vs_inst_idx = c /\
  (!phase. MEM phase phases ==> phase = CurrentControl \/
    ?i inst. phase = CurrentOrdinary h i inst /\ LENGTH pre <= i /\ i < c) ==>
  lookup_var src before = SOME value /\
  ?after. step_inst_base (EL c out.bb_instructions) before = OK after /\
    lookup_var dst after = SOME value /\
    execution_frame after = execution_frame before /\
    after.vs_current_bb = before.vs_current_bb /\ after.vs_prev_bb = before.vs_prev_bb
Proof
  strip_tac >>
  `(EL r pre).inst_outputs = [src]` by metis_tac[makeSsaCurrentReinsertedReadyTheory.current_eval_one_phi_output] >>
  `MEM src (FLAT (MAP (\inst. inst.inst_outputs) pre))` by
    (simp[MEM_FLAT, MEM_MAP] >> metis_tac[EL_MEM, MEM]) >>
  `ALL_DISTINCT (FLAT (MAP (\inst. inst.inst_outputs) pre))` by
    gvs[ALL_DISTINCT_APPEND] >>
  `eval_phis incoming pre = OK post` by
    (metis_tac[current_eval_phis_maximal_append]) >>
  `lookup_var src post = SOME value` by metis_tac[current_phi_batch_selected_value] >>
  `lookup_var src before = lookup_var src (post with vs_inst_idx := LENGTH pre)` by
    (irule current_actual_interval_nonclobber >> goal_assum $ drule_at Any >> metis_tac[]) >>
  `lookup_var src before = SOME value` by fs[lookup_var_def] >>
  simp[] >> qexists `update_var dst value before` >>
  drule_all current_cleanup_assign_step >> disch_then (qspec_then `before` mp_tac) >>
  simp[lookup_var_def, update_var_def, FLOOKUP_UPDATE]
QED

Theorem current_actual_retained_copy_continue:
  lookup_block h fn.fn_blocks = SOME out /\ out.bb_instructions = pre ++ tail /\
  EVERY (\inst. inst.inst_opcode = PHI) pre /\
  (tail = [] \/ (HD tail).inst_opcode <> PHI) /\
  ALL_DISTINCT (FLAT (MAP (\inst. inst.inst_outputs) out.bb_instructions)) /\
  r < LENGTH pre /\ LENGTH pre <= c /\ c < LENGTH out.bb_instructions /\
  eval_one_phi incoming (EL r pre) = SOME (src,value) /\
  eval_phis incoming out.bb_instructions = OK post /\
  (EL c out.bb_instructions).inst_opcode = ASSIGN /\
  (EL c out.bb_instructions).inst_operands = [Var src] /\
  (EL c out.bb_instructions).inst_outputs = [dst] /\ inst_wf (EL c out.bb_instructions) /\
  current_actual_prefix fn C (CurrentBody fuel out)
    (post with vs_inst_idx := LENGTH pre) phases
    (SOME (CurrentBody fuel out)) (OK before) before /\
  before.vs_current_bb = h /\ before.vs_inst_idx = c /\
  (!phase. MEM phase phases ==> phase = CurrentControl \/
    ?i inst. phase = CurrentOrdinary h i inst /\ LENGTH pre <= i /\ i < c) ==>
  lookup_var src before = SOME value /\
  ?after. step_inst_base (EL c out.bb_instructions) before = OK after /\
    lookup_var dst after = SOME value /\ execution_frame after = execution_frame before /\
    after.vs_current_bb = h /\ after.vs_prev_bb = before.vs_prev_bb /\
    current_actual_prefix fn C (CurrentBody fuel out)
      (post with vs_inst_idx := LENGTH pre)
      (phases ++ [CurrentOrdinary h c (EL c out.bb_instructions); CurrentControl])
      (SOME (CurrentBody fuel out))
      (OK (after with vs_inst_idx := SUC c)) (after with vs_inst_idx := SUC c)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all current_actual_retained_copy_ready >> strip_tac >>
  conj_tac >- first_assum ACCEPT_TAC >>
  qexists `after` >>
  conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac >- metis_tac[] >>
  conj_tac >- first_assum ACCEPT_TAC >>
  `get_instruction out before.vs_inst_idx = SOME (EL c out.bb_instructions)` by
    gvs[get_instruction_def] >>
  `~is_terminator (EL c out.bb_instructions).inst_opcode` by simp[is_terminator_def] >>
  `(EL c out.bb_instructions).inst_opcode <> PHI /\
   (EL c out.bb_instructions).inst_opcode <> INVOKE` by simp[] >>
  metis_tac[current_completed_ordinary_continue]
QED

Theorem current_certificate_reinserted_actual_continue:
  current_structural_certificate s fn fn' s' A H events /\
  wf_function fn /\ fn_inst_wf fn /\ fn_defs_reach_uses fn /\
  all_reachable fn /\ first_block_no_preds fn /\ entry_block fn = SOME eb /\
  fn_phi_outputs_single_def fn /\ blocks_have_leading_phi fn.fn_blocks /\
  ir_supply_covers_fn s fn /\ ir_supply_inst_ok s /\
  lookup_block h fn.fn_blocks = SOME old /\ i < LENGTH old.bb_instructions /\
  (EL i old.bb_instructions).inst_opcode = PHI /\
  (EL i old.bb_instructions).inst_outputs = [v] /\ current_actual_inserted fn v h /\
  fn_phis_non_degenerate fn /\ old.bb_instructions = phis ++ tail /\
  EVERY (\p. p.inst_opcode = PHI) phis /\
  (tail = [] \/ (HD tail).inst_opcode <> PHI) /\ i < LENGTH phis ==>
  ?out src r c batch.
    lookup_block h fn'.fn_blocks = SOME out /\
    current_token_name H (CurrentOriginal h i 0) = SOME src /\ src <> v /\
    r < batch /\ batch <= c /\ c < LENGTH out.bb_instructions /\
    (EL r out.bb_instructions).inst_opcode = PHI /\
    (EL r out.bb_instructions).inst_outputs = [src] /\
    (EL c out.bb_instructions).inst_opcode = ASSIGN /\
    (EL c out.bb_instructions).inst_operands = [Var src] /\
    (EL c out.bb_instructions).inst_outputs = [v] /\
    EVERY (\p. p.inst_opcode = PHI) (TAKE batch out.bb_instructions) /\
    (DROP batch out.bb_instructions = [] \/
     (HD (DROP batch out.bb_instructions)).inst_opcode <> PHI) /\
    (!C fuel incoming post phases before value.
      eval_one_phi incoming (EL r out.bb_instructions) = SOME (src,value) /\
      eval_phis incoming out.bb_instructions = OK post /\
      current_actual_prefix fn' C (CurrentBody fuel out)
        (post with vs_inst_idx := batch) phases
        (SOME (CurrentBody fuel out)) (OK before) before /\
      before.vs_current_bb = h /\ before.vs_inst_idx = c /\
      (!phase. MEM phase phases ==> phase = CurrentControl \/
        ?j inst. phase = CurrentOrdinary h j inst /\ batch <= j /\ j < c) ==>
      lookup_var src before = SOME value /\
      ?after. step_inst_base (EL c out.bb_instructions) before = OK after /\
        lookup_var v after = SOME value /\ execution_frame after = execution_frame before /\
        after.vs_current_bb = h /\ after.vs_prev_bb = before.vs_prev_bb /\
        current_actual_prefix fn' C (CurrentBody fuel out)
          (post with vs_inst_idx := batch)
          (phases ++ [CurrentOrdinary h c (EL c out.bb_instructions); CurrentControl])
          (SOME (CurrentBody fuel out))
          (OK (after with vs_inst_idx := SUC c)) (after with vs_inst_idx := SUC c))
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all current_certificate_reinserted_next_ready >>
  disch_then (qx_choose_then `out` (qx_choose_then `src`
    (qx_choose_then `r` (qx_choose_then `c` (qx_choose_then `batch`
      (map_every assume_tac o CONJUNCTS)))))) >>
  qpat_x_assum `!copies rest incoming post before value. _` kall_tac >>
  `ALL_DISTINCT (FLAT (MAP (\j. j.inst_outputs) out.bb_instructions))` by
    (irule current_certificate_block_outputs_distinct >> metis_tac[]) >>
  `inst_wf (EL c out.bb_instructions)` by simp[inst_wf_def] >>
  `LENGTH (TAKE batch out.bb_instructions) = batch` by simp[] >>
  qexistsl_tac [`out`, `src`, `r`, `c`, `batch`] >>
  rpt (conj_tac >- first_assum ACCEPT_TAC) >>
  rpt gen_tac >> strip_tac >>
  `eval_one_phi incoming (EL r (TAKE batch out.bb_instructions)) = SOME (src,value)` by
    simp[EL_TAKE] >>
  `out.bb_instructions = TAKE batch out.bb_instructions ++ DROP batch out.bb_instructions` by
    simp[TAKE_DROP] >>
  mp_tac (Q.INST [`pre` |-> `TAKE batch out.bb_instructions`,
    `tail` |-> `DROP batch out.bb_instructions`, `fn` |-> `fn'`, `dst` |-> `v`]
    current_actual_retained_copy_continue) >>
  qpat_assum `LENGTH (TAKE _ _) = _` (fn th => pure_rewrite_tac[th]) >>
  disch_then irule >> rpt conj_tac >> first_assum ACCEPT_TAC
QED
