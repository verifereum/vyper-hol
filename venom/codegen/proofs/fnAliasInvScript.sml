(*
 * The cross-block DFG alias invariant of the block induction behind
 * venomToAsmProps$gen_fn_frame_simulation.
 *
 * gen_fn_frame_simulation assumes that every operand on the planner's
 * stack or in its spill map has the value of its ASSIGN-chain root
 * (normalize_operand), read through the frame view.  The planner's
 * alias-only reorder steps rely on it.  The induction must re-establish
 * it at the successor block, whose lineage state carries the stack and
 * spill map the current block's code leaves (fnPlanLineage).
 *
 * TOP-LEVEL:
 *   lineage_alias_successor — CHEATED: one block preserves the invariant
 *)

Theory fnAliasInv
Ancestors
  fnPlanLineage frameRel codegenRel unitShapeDefs stackPlanGen stackPlanTypes
  venomExecSemantics venomState livenessDefs dfgDefs cfgDefs
  fnAliasInvOrdering fnAliasInvAvailability dfgAnalysisProps allocaRemapSSA
  venomInst venomInstProps venomWf venomExecProps venomExecProofs list rich_list stackModel
  stackPlanOps reorderSim sorting genericInputReady cleanOpsSim
  fnFrameBoundaryEntryParams joinSpillWitness frameViewFacts instSimHelpers
  livenessConvergenceProofs livenessBlockProofs codegenReadyCompute fnPlanPrefix
  simplifyCfgFixupStatic genBlockSim

(* Actual planner cuts.  The historical label is deliberately independent of
   any semantic predecessor.  Instruction indices count non-PARAM instructions,
   exactly as generate_block_insts_plan does. *)
Datatype:
  alias_plan_cut =
    AliasPlanEntry string plan_state
  | AliasPlanPrepared string basic_block plan_state
  | AliasPlanInst string basic_block num plan_state
End

Inductive alias_plan_event:
[~override:]
  alias_plan_event lv dfg cfg fn ps0
    (AliasPlanEntry lbl ps)
    (AliasPlanEntry lbl
      (ps with <| ps_cleanup_height := ch; ps_cleanup_promised := promised |>))
[~prepare:]
  lookup_block lbl fn.fn_blocks = SOME bb /\
  (if bb = HD fn.fn_blocks then prepare_params_plan lv fn ps
   else ([], ps)) = (ops, ps1) ==>
  alias_plan_event lv dfg cfg fn ps0
    (AliasPlanEntry lbl ps) (AliasPlanPrepared lbl bb ps1)
[~clean:]
  (if LENGTH (cfg_preds_of cfg bb.bb_label) = 1
   then clean_stack_plan lv cfg fn bb ps else ([], ps)) = (ops, ps1) ==>
  alias_plan_event lv dfg cfg fn ps0
    (AliasPlanPrepared lbl bb ps) (AliasPlanInst lbl bb 0 ps1)
[~instruction:]
  DROP i (non_param_insts bb) = inst::rest /\
  generate_inst_plan lv dfg cfg fn inst
    (if rest = [] then live_vars_at lv bb.bb_label (LENGTH bb.bb_instructions)
     else live_vars_at lv bb.bb_label
       (i + LENGTH (get_params bb.bb_instructions) + 1))
    (bb_is_halting bb)
    (case rest of [] => F | next::_ => is_terminator next.inst_opcode)
    bb.bb_label ps = SOME (ops, ps1) ==>
  alias_plan_event lv dfg cfg fn ps0
    (AliasPlanInst lbl bb i ps) (AliasPlanInst lbl bb (i+1) ps1)
[~edge:]
  lookup_block lbl fn.fn_blocks = SOME bb /\
  dfs_block_state lv dfg cfg fn ps0 lbl ps_dfs /\
  generate_block_plan lv dfg cfg fn bb ps_dfs = SOME (ops, ps_dfs_after) /\
  generate_block_plan lv dfg cfg fn bb
    (ps with <| ps_cleanup_height := ch; ps_cleanup_promised := promised |>) =
      SOME (ops, ps_after) /\
  MEM succ (cfg_succs_of cfg lbl) /\
  dfs_block_state lv dfg cfg fn ps0 succ ps_succ ==>
  alias_plan_event lv dfg cfg fn ps0
    (AliasPlanInst lbl bb (LENGTH (non_param_insts bb)) ps_after)
    (AliasPlanEntry succ
      (ps_succ with <| ps_stack := ps_after.ps_stack;
                      ps_spilled := ps_after.ps_spilled |>))
End

(* The list contains destination cuts, not the starting cut. *)
Definition alias_cut_history_def:
  (alias_cut_history R start [] finish <=> finish = start) /\
  (alias_cut_history R start (cut::cuts) finish <=>
     R start cut /\ alias_cut_history R cut cuts finish)
End

Theorem alias_cut_history_append:
  !xs start mid ys finish.
    alias_cut_history R start xs mid /\
    alias_cut_history R mid ys finish ==>
    alias_cut_history R start (xs ++ ys) finish
Proof
  Induct_on `xs` >> simp[alias_cut_history_def] >> metis_tac[]
QED

Theorem alias_cut_history_first_failure:
  !cuts start finish.
    alias_cut_history R start cuts finish /\ Good start /\ ~Good finish ==>
    ?before input bad after.
      cuts = before ++ bad::after /\
      alias_cut_history R start before input /\
      EVERY Good before /\ Good input /\ R input bad /\ ~Good bad /\
      alias_cut_history R bad after finish
Proof
  Induct_on `cuts` >> simp[alias_cut_history_def] >>
  rpt gen_tac >> strip_tac >> Cases_on `Good h`
  >- (first_x_assum drule_all >> strip_tac >>
      qexistsl_tac [`h::before`, `input`, `bad`, `after`] >>
      simp[alias_cut_history_def]) >>
  qexistsl_tac [`[]`, `start`, `h`, `cuts`] >>
  simp[alias_cut_history_def]
QED

Theorem alias_plan_instruction_history:
  !insts i ps ops ps_end.
    generate_block_insts_plan lv dfg cfg fn bb.bb_label (bb_is_halting bb)
      (LENGTH (get_params bb.bb_instructions)) (LENGTH bb.bb_instructions)
      i insts ps = SOME (ops, ps_end) /\
    DROP i (non_param_insts bb) = insts ==>
    ?cuts. alias_cut_history (alias_plan_event lv dfg cfg fn ps0)
      (AliasPlanInst lbl bb i ps) cuts
      (AliasPlanInst lbl bb (i + LENGTH insts) ps_end)
Proof
  Induct_on `insts`
  >- (simp[generate_block_insts_plan_def] >> rpt strip_tac >>
      qexists_tac `[]` >> simp[alias_cut_history_def]) >>
  rpt gen_tac >> strip_tac >>
  gvs[Once generate_block_insts_plan_def, LET_THM, AllCaseEqs()] >>
  `DROP (i+1) (non_param_insts bb) = insts` by
    (`DROP 1 (DROP i (non_param_insts bb)) = insts` by simp[] >>
     qpat_x_assum `DROP 1 (DROP i _) = _` mp_tac >>
     pure_rewrite_tac[DROP_DROP_T] >> simp[Once arithmeticTheory.ADD_COMM]) >>
  first_x_assum drule_all >> strip_tac >>
  qexists_tac `AliasPlanInst lbl bb (i+1) ps' :: cuts` >>
  simp[alias_cut_history_def, arithmeticTheory.ADD_CLAUSES] >>
  reverse conj_tac >-
    (`SUC (i + LENGTH insts) = i + 1 + LENGTH insts` by simp[] >>
     pop_assum SUBST1_TAC >> first_assum ACCEPT_TAC) >>
  irule alias_plan_event_instruction >>
  qexistsl_tac [`h`, `step_ops`, `insts`] >>
  pure_rewrite_tac[GSYM arithmeticTheory.ADD_ASSOC] >>
  conj_tac >> first_assum ACCEPT_TAC
QED

Theorem alias_plan_block_history:
  lookup_block lbl fn.fn_blocks = SOME bb /\
  generate_block_plan lv dfg cfg fn bb ps = SOME (ops, ps_after) ==>
  ?cuts. alias_cut_history (alias_plan_event lv dfg cfg fn ps0)
    (AliasPlanEntry lbl ps) cuts
    (AliasPlanInst lbl bb (LENGTH (non_param_insts bb)) ps_after)
Proof
  strip_tac >>
  qpat_x_assum `generate_block_plan _ _ _ _ _ _ = _` mp_tac >>
  simp[generate_block_plan_def, LET_THM] >>
  pairarg_tac >> simp[] >> pairarg_tac >> simp[] >>
  simp[AllCaseEqs()] >> rpt strip_tac >> gvs[] >>
  drule alias_plan_instruction_history >> simp[] >>
  disch_then (qspecl_then [`ps0`, `lbl`] strip_assume_tac) >>
  qexists_tac `AliasPlanPrepared lbl bb ps1 :: AliasPlanInst lbl bb 0 ps2 :: cuts` >>
  simp[alias_cut_history_def] >> conj_tac
  >- (irule alias_plan_event_prepare >> metis_tac[]) >>
  irule alias_plan_event_clean >> metis_tac[]
QED

(* Unlike the flat event projection, this certificate retains the operation
   fragments and recursively correlates every cut with its block origin. *)
Inductive alias_instruction_segment:
[~nil:]
  DROP i (non_param_insts bb) = [] ==>
  alias_instruction_segment lv dfg cfg fn lbl bb i [] ps [] ps []
[~cons:]
  DROP i (non_param_insts bb) = inst::rest /\
  generate_inst_plan lv dfg cfg fn inst
    (if rest = [] then live_vars_at lv bb.bb_label (LENGTH bb.bb_instructions)
     else live_vars_at lv bb.bb_label
       (i + LENGTH (get_params bb.bb_instructions) + 1))
    (bb_is_halting bb)
    (case rest of [] => F | next::_ => is_terminator next.inst_opcode)
    bb.bb_label ps = SOME (step_ops, ps1) /\
  alias_instruction_segment lv dfg cfg fn lbl bb (i+1) rest
    ps1 rest_ops ps_end cuts ==>
  alias_instruction_segment lv dfg cfg fn lbl bb i (inst::rest)
    ps (step_ops ++ rest_ops) ps_end (AliasPlanInst lbl bb (i+1) ps1 :: cuts)
End

Definition alias_block_segment_def:
  alias_block_segment lv dfg cfg fn lbl bb ps ops ps_after cuts <=>
    lookup_block lbl fn.fn_blocks = SOME bb /\
    ?param_ops ps1 clean_ops ps2 inst_ops inst_cuts.
      (if bb = HD fn.fn_blocks then prepare_params_plan lv fn ps
       else ([], ps)) = (param_ops, ps1) /\
      (if LENGTH (cfg_preds_of cfg bb.bb_label) = 1
       then clean_stack_plan lv cfg fn bb ps1 else ([], ps1)) = (clean_ops, ps2) /\
      alias_instruction_segment lv dfg cfg fn lbl bb 0 (non_param_insts bb)
        ps2 inst_ops ps_after inst_cuts /\
      ops = [SOLabel bb.bb_label] ++ param_ops ++ clean_ops ++ inst_ops /\
      cuts = AliasPlanPrepared lbl bb ps1 :: AliasPlanInst lbl bb 0 ps2 :: inst_cuts
End

Theorem alias_instruction_segment_exists:
  !insts i ps ops ps_end.
    generate_block_insts_plan lv dfg cfg fn bb.bb_label (bb_is_halting bb)
      (LENGTH (get_params bb.bb_instructions)) (LENGTH bb.bb_instructions)
      i insts ps = SOME (ops, ps_end) /\
    DROP i (non_param_insts bb) = insts ==>
    ?cuts. alias_instruction_segment lv dfg cfg fn lbl bb i insts ps ops ps_end cuts
Proof
  Induct_on `insts`
  >- (simp[generate_block_insts_plan_def] >> rpt strip_tac >>
      qexists_tac `[]` >> irule alias_instruction_segment_nil >> simp[]) >>
  rpt gen_tac >> strip_tac >>
  gvs[Once generate_block_insts_plan_def, LET_THM, AllCaseEqs()] >>
  `DROP (i+1) (non_param_insts bb) = insts` by
    (`DROP 1 (DROP i (non_param_insts bb)) = insts` by simp[] >>
     qpat_x_assum `DROP 1 (DROP i _) = _` mp_tac >>
     pure_rewrite_tac[DROP_DROP_T] >> simp[Once arithmeticTheory.ADD_COMM]) >>
  first_x_assum drule_all >> strip_tac >>
  qexists_tac `AliasPlanInst lbl bb (i+1) ps' :: cuts` >>
  irule alias_instruction_segment_cons >>
  pure_rewrite_tac[GSYM arithmeticTheory.ADD_ASSOC] >>
  rpt (first_assum (irule_at Any))
QED

Theorem alias_instruction_segment_history:
  !i insts ps ops ps_end cuts.
    alias_instruction_segment lv dfg cfg fn lbl bb i insts ps ops ps_end cuts ==>
    !ps0. alias_cut_history (alias_plan_event lv dfg cfg fn ps0)
      (AliasPlanInst lbl bb i ps) cuts
      (AliasPlanInst lbl bb (i + LENGTH insts) ps_end)
Proof
  ho_match_mp_tac alias_instruction_segment_ind >> conj_tac
  >- simp[alias_cut_history_def] >>
  rpt strip_tac >> rename1 `DROP i _ = inst::rest` >>
  simp[alias_cut_history_def] >> conj_tac
  >- (irule alias_plan_event_instruction >> metis_tac[]) >>
  `i + SUC (LENGTH rest) = i+1+LENGTH rest` by simp[] >>
  pop_assum SUBST1_TAC >> simp[]
QED

Theorem alias_block_segment_exists:
  lookup_block lbl fn.fn_blocks = SOME bb /\
  generate_block_plan lv dfg cfg fn bb ps = SOME (ops, ps_after) ==>
  ?cuts. alias_block_segment lv dfg cfg fn lbl bb ps ops ps_after cuts
Proof
  strip_tac >>
  qpat_x_assum `generate_block_plan _ _ _ _ _ _ = _` mp_tac >>
  simp[generate_block_plan_def, LET_THM] >>
  pairarg_tac >> simp[] >> pairarg_tac >> simp[] >>
  simp[AllCaseEqs()] >> rpt strip_tac >> gvs[] >>
  drule alias_instruction_segment_exists >> simp[] >>
  disch_then (qspec_then `lbl` strip_assume_tac) >>
  qexists_tac `AliasPlanPrepared lbl bb ps1 :: AliasPlanInst lbl bb 0 ps2 :: cuts` >>
  simp[alias_block_segment_def] >> rpt (first_assum (irule_at Any))
QED

Theorem alias_block_segment_history:
  alias_block_segment lv dfg cfg fn lbl bb ps ops ps_after cuts ==>
  !ps0. alias_cut_history (alias_plan_event lv dfg cfg fn ps0)
    (AliasPlanEntry lbl ps) cuts
    (AliasPlanInst lbl bb (LENGTH (non_param_insts bb)) ps_after)
Proof
  simp[alias_block_segment_def] >> rpt strip_tac >>
  drule alias_instruction_segment_history >> simp[] >> strip_tac >>
  simp[alias_cut_history_def] >> conj_tac
  >- (irule alias_plan_event_prepare >> metis_tac[]) >>
  irule alias_plan_event_clean >> metis_tac[]
QED

Theorem alias_plan_history_extend_block:
  alias_cut_history (alias_plan_event lv dfg cfg fn ps0)
    start prefix (AliasPlanEntry lbl ps) /\
  lookup_block lbl fn.fn_blocks = SOME bb /\
  generate_block_plan lv dfg cfg fn bb
    (ps with <| ps_cleanup_height := ch; ps_cleanup_promised := promised |>) =
      SOME (ops, ps_after) ==>
  ?block_cuts. alias_cut_history (alias_plan_event lv dfg cfg fn ps0)
    start (prefix ++ block_cuts)
    (AliasPlanInst lbl bb (LENGTH (non_param_insts bb)) ps_after)
Proof
  strip_tac >> drule_all alias_plan_block_history >>
  disch_then (qspec_then `ps0` strip_assume_tac) >>
  qexists_tac `AliasPlanEntry lbl
    (ps with <| ps_cleanup_height := ch; ps_cleanup_promised := promised |>) :: cuts` >>
  irule alias_cut_history_append >> first_assum (irule_at Any) >>
  simp[alias_cut_history_def, alias_plan_event_override]
QED

Inductive alias_lineage_segments:
[~entry:]
  fn_entry_label fn = SOME lbl ==>
  alias_lineage_segments lv dfg cfg fn ps0 lbl ps0 []
[~step:]
  alias_lineage_segments lv dfg cfg fn ps0 lbl ps cuts /\
  lookup_block lbl fn.fn_blocks = SOME bb /\
  dfs_block_state lv dfg cfg fn ps0 lbl ps_dfs /\
  generate_block_plan lv dfg cfg fn bb ps_dfs = SOME (ops, ps_dfs_after) /\
  generate_block_plan lv dfg cfg fn bb
    (ps with <| ps_cleanup_height := ch; ps_cleanup_promised := promised |>) =
      SOME (ops, ps_after) /\
  alias_block_segment lv dfg cfg fn lbl bb
    (ps with <| ps_cleanup_height := ch; ps_cleanup_promised := promised |>)
    ops ps_after block_cuts /\
  MEM succ (cfg_succs_of cfg lbl) /\
  dfs_block_state lv dfg cfg fn ps0 succ ps_succ ==>
  alias_lineage_segments lv dfg cfg fn ps0 succ
    (ps_succ with <| ps_stack := ps_after.ps_stack;
                    ps_spilled := ps_after.ps_spilled |>)
    (cuts ++ AliasPlanEntry lbl
       (ps with <| ps_cleanup_height := ch; ps_cleanup_promised := promised |>) ::
     block_cuts ++ [AliasPlanEntry succ
       (ps_succ with <| ps_stack := ps_after.ps_stack;
                       ps_spilled := ps_after.ps_spilled |>)])
End

Theorem alias_lineage_segments_exists:
  !lbl ps. lineage_state lv dfg cfg fn ps0 lbl ps ==>
    ?cuts. alias_lineage_segments lv dfg cfg fn ps0 lbl ps cuts
Proof
  ho_match_mp_tac lineage_state_ind >> conj_tac
  >- (rpt strip_tac >> qexists_tac `[]` >>
      irule alias_lineage_segments_entry >> simp[]) >>
  rpt strip_tac >> rename1 `MEM succ (cfg_succs_of cfg lbl)` >>
  drule_all alias_block_segment_exists >> strip_tac >>
  qexists_tac `cuts ++ AliasPlanEntry lbl
    (ps with <| ps_cleanup_height := ch; ps_cleanup_promised := promised |>) ::
    cuts' ++ [AliasPlanEntry succ
      (ps_succ with <| ps_stack := ps_after.ps_stack;
                      ps_spilled := ps_after.ps_spilled |>)]` >>
  irule alias_lineage_segments_step >> simp[] >>
  qexistsl_tac [`ps_dfs`, `ps_dfs_after`] >> simp[]
QED

Theorem alias_lineage_segments_history:
  !lbl ps cuts. alias_lineage_segments lv dfg cfg fn ps0 lbl ps cuts ==>
  ?entry. fn_entry_label fn = SOME entry /\
    alias_cut_history (alias_plan_event lv dfg cfg fn ps0)
      (AliasPlanEntry entry ps0) cuts (AliasPlanEntry lbl ps)
Proof
  ho_match_mp_tac alias_lineage_segments_ind >> conj_tac
  >- (rpt strip_tac >> qexists_tac `lbl` >> simp[alias_cut_history_def]) >>
  rpt strip_tac >> rename1 `MEM succ (cfg_succs_of cfg lbl)` >>
  drule alias_block_segment_history >>
  disch_then (qspec_then `ps0` assume_tac) >>
  qexists_tac `entry` >> simp[] >>
  irule alias_cut_history_append >>
  qexists_tac `AliasPlanInst lbl bb (LENGTH (non_param_insts bb)) ps_after` >>
  conj_tac
  >- (simp[alias_cut_history_def] >> irule alias_plan_event_edge >> metis_tac[]) >>
  irule alias_cut_history_append >> first_assum (irule_at Any) >>
  simp[alias_cut_history_def, alias_plan_event_override]
QED

Theorem alias_lineage_segments_extend_block:
  alias_lineage_segments lv dfg cfg fn ps0 lbl ps cuts /\
  lookup_block lbl fn.fn_blocks = SOME bb /\
  generate_block_plan lv dfg cfg fn bb
    (ps with <| ps_cleanup_height := ch; ps_cleanup_promised := promised |>) =
      SOME (ops, ps_after) ==>
  ?entry block_cuts.
    fn_entry_label fn = SOME entry /\
    alias_block_segment lv dfg cfg fn lbl bb
      (ps with <| ps_cleanup_height := ch; ps_cleanup_promised := promised |>)
      ops ps_after block_cuts /\
    alias_cut_history (alias_plan_event lv dfg cfg fn ps0)
      (AliasPlanEntry entry ps0)
      (cuts ++ AliasPlanEntry lbl
        (ps with <| ps_cleanup_height := ch; ps_cleanup_promised := promised |>) :: block_cuts)
      (AliasPlanInst lbl bb (LENGTH (non_param_insts bb)) ps_after)
Proof
  strip_tac >> drule alias_lineage_segments_history >> strip_tac >>
  drule_all alias_block_segment_exists >> strip_tac >>
  drule alias_block_segment_history >>
  disch_then (qspec_then `ps0` assume_tac) >>
  qexistsl_tac [`entry`, `cuts'`] >> simp[] >>
  irule alias_cut_history_append >> first_assum (irule_at Any) >>
  simp[alias_cut_history_def, alias_plan_event_override]
QED

Theorem alias_lineage_history:
  !lbl ps. lineage_state lv dfg cfg fn ps0 lbl ps ==>
  ?entry cuts. fn_entry_label fn = SOME entry /\
    alias_cut_history (alias_plan_event lv dfg cfg fn ps0)
      (AliasPlanEntry entry ps0) cuts (AliasPlanEntry lbl ps)
Proof
  ho_match_mp_tac lineage_state_ind >> conj_tac
  >- (rpt strip_tac >> qexistsl_tac [`lbl`, `[]`] >>
      simp[alias_cut_history_def]) >>
  rpt strip_tac >> rename1 `MEM succ (cfg_succs_of cfg lbl)` >>
  drule_all alias_plan_block_history >>
  disch_then (qspec_then `ps0` strip_assume_tac) >>
  qexists_tac `entry` >> simp[] >>
  irule_at Any alias_cut_history_append >>
  first_assum (irule_at Any) >>
  qexists_tac `AliasPlanEntry lbl
    (ps with <| ps_cleanup_height := ch; ps_cleanup_promised := promised |>) ::
    cuts' ++ [AliasPlanEntry succ
      (ps_succ with <| ps_stack := ps_after.ps_stack;
                      ps_spilled := ps_after.ps_spilled |>)]` >>
  simp[alias_cut_history_def, alias_plan_event_override] >>
  irule alias_cut_history_append >>
  first_assum (irule_at Any) >>
  simp[alias_cut_history_def] >>
  irule alias_plan_event_edge >> metis_tac[]
QED

Theorem alias_single_successor_liveout:
  wf_function fn /\ cfg_reachable_of (cfg_analyze fn) pred /\
  lookup_block pred fn.fn_blocks = SOME pb /\
  lookup_block lbl fn.fn_blocks = SOME bb /\
  cfg_succs_of (cfg_analyze fn) pred = [lbl] ==>
  set (live_vars_at (liveness_analyze fn) pred (LENGTH pb.bb_instructions)) =
  set (input_vars_from pred bb.bb_instructions
    (live_vars_at (liveness_analyze fn) lbl 0))
Proof
  strip_tac >> drule_all liveness_recompute_convergence >>
  simp[same_vars_set, liveness_instrs_def, liveness_out_def,
       liveness_edge_transfer_def, live_vars_at_def, liveness_analyze_def,
       livenessTransferProofsTheory.list_union_set]
QED

Theorem alias_lineage_reachable:
  wf_function fn /\
  lineage_state liveness dfg (cfg_analyze fn) fn ps0 lbl ps ==>
  cfg_reachable_of (cfg_analyze fn) lbl
Proof
  strip_tac >>
  `?eb. entry_block fn = SOME eb` by
    (gvs[wf_function_def, fn_has_entry_def, entry_block_def, NULL_EQ]) >>
  `!l p. lineage_state liveness dfg (cfg_analyze fn) fn ps0 l p ==>
     cfg_path (cfg_analyze fn) eb.bb_label l` suffices_by
    metis_tac[cfgAnalysisPropsTheory.cfg_analyze_semantic_reachability] >>
  ho_match_mp_tac lineage_state_ind >> conj_tac
  >- (rpt strip_tac >> gvs[fn_entry_label_def, cfg_path_def]) >>
  rpt strip_tac >> fs[cfg_path_def] >>
  once_rewrite_tac[relationTheory.RTC_CASES2] >>
  disj2_tac >> qexists_tac `l` >> simp[]
QED

(* A final successful JMP checks its target suffix; block finalization leaves
   that checked state unchanged.  No coverage assumption on entry is needed. *)
Theorem alias_jmp_plan_join_reached:
  inst.inst_opcode = JMP /\
  generate_inst_plan liveness dfg cfg fn inst live halting next_term lbl ps =
    SOME (ops, ps') ==>
  join_reached liveness fn lbl inst ps'
Proof
  strip_tac >>
  gvs[generate_inst_plan_def, is_param_opcode_def, AllCaseEqs()]
QED

Theorem alias_join_reached_length:
  join_reached liveness fn lbl inst qs /\
  join_target_ops liveness fn lbl inst = SOME targets ==>
  LENGTH targets <= LENGTH qs.ps_stack
Proof
  strip_tac >> fs[join_reached_def] >>
  qpat_x_assum `_ ++ _ = _` (mp_tac o AP_TERM ``LENGTH:operand list -> num``) >>
  simp[]
QED

Theorem alias_block_insts_final_jmp_join_reached:
  !prefix i ps ops ps'.
  inst.inst_opcode = JMP /\
  generate_block_insts_plan liveness dfg cfg fn lbl halting np blen i
    (prefix ++ [inst]) ps = SOME (ops, ps') ==>
  join_reached liveness fn lbl inst ps'
Proof
  Induct >> simp[Once generate_block_insts_plan_def] >>
  rpt gen_tac >> simp[AllCaseEqs()] >> strip_tac
  >- (gvs[generate_block_insts_plan_def] >>
      drule_all alias_jmp_plan_join_reached >> simp[]) >>
  gvs[] >> first_x_assum drule >> simp[]
QED

Theorem alias_block_plan_final_jmp_inputs:
  generate_block_plan liveness dfg cfg fn bb ps = SOME (ops, ps') /\
  non_param_insts bb = prefix ++ [inst] /\
  inst.inst_opcode = JMP /\ inst.inst_operands = [Label target] /\
  lookup_block target fn.fn_blocks = SOME target_bb /\
  MEM v (input_vars_from bb.bb_label target_bb.bb_instructions
    (live_vars_at liveness target 0)) ==>
  MEM (Var v) ps'.ps_stack
Proof
  simp[generate_block_plan_def] >> pairarg_tac >> simp[] >>
  pairarg_tac >> simp[AllCaseEqs()] >> strip_tac >> gvs[] >>
  drule_all alias_block_insts_final_jmp_join_reached >>
  simp[join_reached_def, join_target_ops_def] >> strip_tac >>
  qpat_x_assum `_ ++ _ = _` (fn th => once_rewrite_tac[GSYM th]) >>
  simp[MEM_MAP]
QED

Theorem alias_ready_entry_no_preds:
  codegen_ready_fn fn /\ fn_entry_label fn = SOME lbl ==>
  cfg_preds_of (cfg_analyze fn) lbl = []
Proof
  simp[codegen_ready_fn_def, block_entries_ready_def, fn_entry_label_def] >>
  Cases_on `entry_block fn` >> simp[] >> rpt strip_tac >> gvs[NULL_EQ]
QED

Theorem alias_ready_join_predecessor_jmp:
  codegen_ready_fn fn /\ lookup_block lbl fn.fn_blocks = SOME bb /\
  1 < LENGTH (cfg_preds_of (cfg_analyze fn) lbl) /\
  MEM pred (cfg_preds_of (cfg_analyze fn) lbl) /\
  lookup_block pred fn.fn_blocks = SOME pb ==>
  ~NULL pb.bb_instructions /\ (LAST pb.bb_instructions).inst_opcode = JMP
Proof
  strip_tac >>
  `MEM bb fn.fn_blocks /\ bb.bb_label = lbl` by
    metis_tac[lookup_block_MEM, lookup_block_label] >>
  gvs[codegen_ready_fn_def, block_entries_ready_def, EVERY_MEM] >>
  qpat_x_assum `!b. MEM b fn.fn_blocks ==> _ \/ _`
    (qspec_then `bb` mp_tac) >> simp[] >>
  disch_then assume_tac >> first_x_assum drule >> simp[]
QED

Theorem alias_ready_jmp_edge_operands:
  codegen_ready_fn fn /\ lookup_block pred fn.fn_blocks = SOME pb /\
  ~NULL pb.bb_instructions /\ (LAST pb.bb_instructions).inst_opcode = JMP /\
  MEM lbl (cfg_succs_of (cfg_analyze fn) pred) ==>
  (LAST pb.bb_instructions).inst_operands = [Label lbl]
Proof
  strip_tac >>
  `MEM pb fn.fn_blocks /\ pb.bb_label = pred` by
    metis_tac[lookup_block_MEM, lookup_block_label] >>
  `wf_function fn /\ fn_inst_wf fn` by gvs[codegen_ready_fn_def] >>
  `inst_wf (LAST pb.bb_instructions)` by
    metis_tac[fn_inst_wf_def, LAST_MEM, NULL_EQ] >>
  gvs[inst_wf_def] >>
  drule_all cfgAnalysisPropsTheory.cfg_analyze_preserves_bb_succs >>
  strip_tac >> gvs[] >> Cases_on `pb.bb_instructions` >>
  gvs[bb_succs_def, get_successors_def, get_label_def, is_terminator_def,
      NULL_EQ]
QED

Theorem alias_ready_jmp_single_successor:
  codegen_ready_fn fn /\ lookup_block pred fn.fn_blocks = SOME pb /\
  ~NULL pb.bb_instructions /\ (LAST pb.bb_instructions).inst_opcode = JMP /\
  MEM lbl (cfg_succs_of (cfg_analyze fn) pred) ==>
  cfg_succs_of (cfg_analyze fn) pred = [lbl]
Proof
  strip_tac >> drule_all alias_ready_jmp_edge_operands >> strip_tac >>
  `MEM pb fn.fn_blocks /\ pb.bb_label = pred` by
    metis_tac[lookup_block_MEM, lookup_block_label] >>
  `wf_function fn` by fs[codegen_ready_fn_def] >>
  drule_all cfgAnalysisPropsTheory.cfg_analyze_preserves_bb_succs >>
  strip_tac >> simp[] >>
  Cases_on `pb.bb_instructions` >>
  gvs[bb_succs_def, get_successors_def, get_label_def, is_terminator_def, NULL_EQ] >>
  EVAL_TAC
QED

Theorem alias_lineage_join_historical_coverage:
  liveness = liveness_analyze fn /\ dfg = dfg_build_function fn /\
  cfg = cfg_analyze fn /\ codegen_ready_fn fn /\
  lineage_state liveness dfg cfg fn
    (init_cleanup_plan_state ch growth spill_base lbl_ctr) lbl ps /\
  lookup_block lbl fn.fn_blocks = SOME bb /\
  1 < LENGTH (cfg_preds_of cfg lbl) ==>
  ?pred. lineage_entry liveness dfg cfg fn
           (init_cleanup_plan_state ch growth spill_base lbl_ctr) pred lbl ps /\
         MEM pred (cfg_preds_of cfg lbl) /\
         (!v. MEM v (input_vars_from pred bb.bb_instructions
                        (live_vars_at liveness lbl 0)) ==>
              MEM (Var v) ps.ps_stack)
Proof
  strip_tac >>
  qpat_x_assum `lineage_state _ _ _ _ _ _ _` mp_tac >>
  simp[Once lineage_state_cases] >> strip_tac
  >- (gvs[] >> drule_all alias_ready_entry_no_preds >>
      disch_then assume_tac >> gvs[]) >>
  gvs[] >> qexists_tac `lbl'` >> conj_tac
  >- (simp[lineage_entry_def] >> metis_tac[]) >>
  conj_asm1_tac
  >- metis_tac[cfgAnalysisPropsTheory.cfg_edge_symmetry_uncond] >>
  drule_all alias_ready_join_predecessor_jmp >> strip_tac >>
  drule_all alias_ready_jmp_edge_operands >> strip_tac >>
  `bb'.bb_label = lbl'` by metis_tac[lookup_block_label] >>
  `?prefix. non_param_insts bb' = prefix ++ [LAST bb'.bb_instructions]` by
    (qexists_tac `FILTER (\i. ~is_param_opcode i.inst_opcode)
                     (FRONT bb'.bb_instructions)` >>
     `bb'.bb_instructions = FRONT bb'.bb_instructions ++
                              [LAST bb'.bb_instructions]` by
       metis_tac[APPEND_FRONT_LAST, NULL_EQ] >>
     simp[non_param_insts_def] >>
     pop_assum (fn th => CONV_TAC (LHS_CONV (ONCE_REWRITE_CONV [th]))) >>
     simp[FILTER_APPEND, is_param_opcode_def]) >>
  rpt strip_tac >> irule alias_block_plan_final_jmp_inputs >>
  goal_assum (drule_at Any) >> simp[] >>
  goal_assum (drule_at Any) >> simp[] >>
  goal_assum (drule_at Any) >> simp[]
QED

(* Forward inversion requires non-use, not a circular non-definition premise. *)
Theorem alias_live_no_use_step:
  wf_function fn /\ MEM lbl (cfg_analyze fn).cfg_dfs_pre /\
  lookup_block lbl fn.fn_blocks = SOME bb /\
  i < LENGTH bb.bb_instructions /\
  MEM v (live_vars_at (liveness_analyze fn) lbl i) /\
  ~MEM v (inst_uses (EL i bb.bb_instructions)) ==>
  MEM v (live_vars_at (liveness_analyze fn) lbl (SUC i)) /\
  ~MEM v (inst_defs (EL i bb.bb_instructions))
Proof
  strip_tac >>
  qspecl_then [`fn`, `lbl`, `bb`, `i`] mp_tac
    livenessAnalysisPropsTheory.live_vars_at_transfer >>
  simp[] >> strip_tac >>
  gvs[liveness_transfer_def, livenessTransferProofsTheory.live_update_mem]
QED

Theorem alias_live_no_use_range:
  !j fn lbl bb i v.
  wf_function fn /\ MEM lbl (cfg_analyze fn).cfg_dfs_pre /\
  lookup_block lbl fn.fn_blocks = SOME bb /\
  i <= j /\ j <= LENGTH bb.bb_instructions /\
  MEM v (live_vars_at (liveness_analyze fn) lbl i) /\
  (!k. i <= k /\ k < j ==> ~MEM v (inst_uses (EL k bb.bb_instructions))) ==>
  MEM v (live_vars_at (liveness_analyze fn) lbl j)
Proof
  Induct >- (rpt strip_tac >> gvs[]) >>
  rpt strip_tac >> Cases_on `i = SUC j` >- gvs[] >>
  `i <= j /\ j < LENGTH bb.bb_instructions` by decide_tac >>
  `MEM v (live_vars_at (liveness_analyze fn) lbl j)` by
    (first_x_assum irule >> goal_assum (drule_at Any) >> simp[] >>
     qexists_tac `i` >> simp[] >> rpt strip_tac >>
     first_x_assum irule >> decide_tac) >>
  `~MEM v (inst_uses (EL j bb.bb_instructions))` by
    (first_x_assum irule >> simp[]) >>
  drule_all alias_live_no_use_step >> simp[]
QED

Theorem alias_live_no_use_range_not_def:
  wf_function fn /\ MEM lbl (cfg_analyze fn).cfg_dfs_pre /\
  lookup_block lbl fn.fn_blocks = SOME bb /\
  i <= j /\ j <= LENGTH bb.bb_instructions /\
  MEM v (live_vars_at (liveness_analyze fn) lbl i) /\
  (!n. i <= n /\ n < j ==> ~MEM v (inst_uses (EL n bb.bb_instructions))) /\
  i <= k /\ k < j ==>
  ~MEM v (inst_defs (EL k bb.bb_instructions))
Proof
  strip_tac >>
  `k < LENGTH bb.bb_instructions` by decide_tac >>
  `MEM v (live_vars_at (liveness_analyze fn) lbl k)` by
    (irule alias_live_no_use_range >> goal_assum (drule_at Any) >>
     simp[] >> metis_tac[arithmeticTheory.LESS_TRANS]) >>
  `~MEM v (inst_uses (EL k bb.bb_instructions))` by
    (first_x_assum irule >> simp[]) >>
  drule_all alias_live_no_use_step >> simp[]
QED

Theorem alias_collect_phis_prefix:
  !xs. ?rest. xs = collect_phis xs ++ rest
Proof
  Induct >- simp[collect_phis_def] >>
  gen_tac >> Cases_on `h.inst_opcode = PHI` >>
  simp[collect_phis_def] >> metis_tac[]
QED

Theorem alias_phi_map_absent_prefix_no_use:
  FLOOKUP (FST (build_phi_maps pred (collect_phis bb.bb_instructions))) v = NONE /\
  (!phi. MEM phi (collect_phis bb.bb_instructions) ==>
    phi_well_formed phi.inst_operands) ==>
  !k. k < LENGTH (collect_phis bb.bb_instructions) ==>
    ~MEM v (inst_uses (EL k bb.bb_instructions))
Proof
  strip_tac >>
  `!phi. MEM phi (collect_phis bb.bb_instructions) ==>
    ~MEM v (inst_uses phi)` by
    metis_tac[alias_build_phi_maps_absent_uses] >>
  rpt strip_tac >>
  qspec_then `bb.bb_instructions` strip_assume_tac alias_collect_phis_prefix >>
  `EL k bb.bb_instructions = EL k (collect_phis bb.bb_instructions)` by
    metis_tac[EL_APPEND1] >>
  metis_tac[MEM_EL]
QED

Theorem alias_phi_map_absent_postprefix_live:
  wf_function fn /\ MEM lbl (cfg_analyze fn).cfg_dfs_pre /\
  lookup_block lbl fn.fn_blocks = SOME bb /\
  MEM v (live_vars_at (liveness_analyze fn) lbl 0) /\
  FLOOKUP (FST (build_phi_maps pred (collect_phis bb.bb_instructions))) v = NONE /\
  (!phi. MEM phi (collect_phis bb.bb_instructions) ==>
    phi_well_formed phi.inst_operands) ==>
  MEM v (live_vars_at (liveness_analyze fn) lbl
    (LENGTH (collect_phis bb.bb_instructions)))
Proof
  strip_tac >> irule alias_live_no_use_range >>
  simp[] >> qexists_tac `0` >> simp[] >>
  conj_tac
  >- metis_tac[alias_phi_map_absent_prefix_no_use] >>
  qspec_then `bb.bb_instructions` strip_assume_tac alias_collect_phis_prefix >>
  pop_assum (mp_tac o AP_TERM ``LENGTH:instruction list -> num``) >> simp[]
QED

Theorem alias_phi_map_absent_not_output:
  wf_function fn /\ MEM lbl (cfg_analyze fn).cfg_dfs_pre /\
  lookup_block lbl fn.fn_blocks = SOME bb /\
  MEM v (live_vars_at (liveness_analyze fn) lbl 0) /\
  FLOOKUP (FST (build_phi_maps pred (collect_phis bb.bb_instructions))) v = NONE /\
  (!p. MEM p (collect_phis bb.bb_instructions) ==>
    phi_well_formed p.inst_operands) /\
  MEM phi (collect_phis bb.bb_instructions) ==>
  ~MEM v (inst_defs phi)
Proof
  strip_tac >>
  qpat_x_assum `MEM phi _` (strip_assume_tac o REWRITE_RULE [MEM_EL]) >>
  rename1 `n < LENGTH (collect_phis bb.bb_instructions)` >>
  qspec_then `bb.bb_instructions` strip_assume_tac alias_collect_phis_prefix >>
  `EL n bb.bb_instructions = phi` by metis_tac[EL_APPEND1] >>
  qpat_x_assum `EL n bb.bb_instructions = phi`
    (fn th => once_rewrite_tac[GSYM th]) >>
  irule alias_live_no_use_range_not_def >>
  goal_assum (drule_at Any) >>
  qexistsl_tac [`fn`, `0`, `lbl`] >> simp[] >>
  conj_tac
  >- metis_tac[alias_phi_map_absent_prefix_no_use] >>
  qpat_x_assum `bb.bb_instructions = _ ++ _`
    (mp_tac o AP_TERM ``LENGTH:instruction list -> num``) >> simp[]
QED

Theorem alias_phi_ready_ordinary_input:
  phi_block_ready liveness bb /\
  MEM v (live_vars_at liveness bb.bb_label 0) /\
  MEM v (live_vars_at liveness bb.bb_label
    (LENGTH (collect_phis bb.bb_instructions))) ==>
  MEM v (input_vars_from pred bb.bb_instructions
    (live_vars_at liveness bb.bb_label 0))
Proof
  strip_tac >> irule alias_input_vars_ordinary_intro >>
  gvs[phi_block_ready_def, EVERY_MEM] >> metis_tac[]
QED

Theorem alias_path_last_visit:
  !path fn d. is_fn_path fn path /\ MEM d path ==>
  ?pre tail. path = pre ++ d::tail /\ ~MEM d tail /\
    is_fn_path fn (d::tail) /\ LAST (d::tail) = LAST path
Proof
  Induct >- simp[] >> rpt gen_tac >> strip_tac >>
  Cases_on `MEM d path`
  >- (`is_fn_path fn path` by
        (Cases_on `path` >> gvs[is_fn_path_def]) >>
      `LAST (h::path) = LAST path` by
        (Cases_on `path` >> gvs[LAST_DEF]) >>
      first_x_assum drule >> disch_then drule >>
      strip_tac >> qexistsl_tac [`h::pre`, `tail`] >>
      metis_tac[APPEND]) >>
  `h = d` by gvs[] >>
  qexistsl_tac [`[]`, `path`] >> gvs[]
QED

Theorem alias_available_definition_visit:
  wf_function fn /\ ssa_form fn /\
  lookup_block d fn.fn_blocks = SOME db /\ j < LENGTH db.bb_instructions /\
  MEM v (inst_defs (EL j db.bb_instructions)) /\
  alias_path_available fn p n v /\ is_fn_path fn path /\ path <> [] /\
  (?entry. fn_entry_label fn = SOME entry /\ HD path = entry) /\ LAST path = p ==>
  MEM d path
Proof
  strip_tac >>
  qpat_x_assum `alias_path_available _ _ _ _` mp_tac >>
  rewrite_tac[alias_path_available_def] >>
  disch_then (qspec_then `path` mp_tac) >>
  impl_tac >- metis_tac[] >> strip_tac
  >- (`?i. i < LENGTH bb.bb_instructions /\ EL i bb.bb_instructions = inst` by
        metis_tac[MEM_EL] >>
      `d = EL k path` by metis_tac[alias_ssa_definition_position] >>
      `k < LENGTH path` by decide_tac >>
      qpat_x_assum `d = EL k path` SUBST1_TAC >>
      irule EL_MEM >> simp[]) >>
  `d = p` by metis_tac[alias_ssa_definition_position] >>
  gvs[] >> simp[LAST_EL] >> irule EL_MEM >> Cases_on `path` >> gvs[]
QED

Theorem alias_path_snoc_invert:
  !path fn l. is_fn_path fn (path ++ [l]) /\ path <> [] ==>
    is_fn_path fn path /\ fn_cfg_edge fn (LAST path) l
Proof
  Induct >> simp[] >> rpt gen_tac >> Cases_on `path`
  >- simp[is_fn_path_def] >>
  simp[is_fn_path_def] >> strip_tac >>
  first_x_assum (qspecl_then [`fn`,`l`] mp_tac) >>
  simp[] >> strip_tac >> gvs[is_fn_path_def]
QED

Theorem alias_ready_phi_nonlocal_source:
  codegen_ready_fn fn /\ fn_reachable fn lbl /\
  lookup_block lbl fn.fn_blocks = SOME bb /\
  k < LENGTH (collect_phis bb.bb_instructions) ==>
  ?v. MEM v (inst_uses (EL k (collect_phis bb.bb_instructions))) /\
    (?edge. MEM (edge,v)
      (phi_pairs (EL k (collect_phis bb.bb_instructions)).inst_operands)) /\
    (!j. j < LENGTH bb.bb_instructions ==>
      ~MEM v (inst_defs (EL j bb.bb_instructions)))
Proof
  strip_tac >>
  `wf_function fn /\ ssa_form fn /\ def_dominates_uses fn` by
    gvs[codegen_ready_fn_def] >>
  `bb.bb_label = lbl /\ MEM bb fn.fn_blocks` by
    metis_tac[lookup_block_label, lookup_block_MEM] >>
  `MEM (EL k (collect_phis bb.bb_instructions)) bb.bb_instructions /\
   (EL k (collect_phis bb.bb_instructions)).inst_opcode = PHI` by
    metis_tac[EL_MEM, livenessProofsTheory.collect_phis_mem] >>
  drule alias_reachable_first_visit >> strip_tac >>
  `?pre. path = pre ++ [lbl]` by
    metis_tac[SNOC_CASES, SNOC_APPEND, LAST_SNOC] >>
  gvs[] >>
  Cases_on `pre = []`
  >- (gvs[codegen_ready_fn_def, block_entries_ready_def,
          fn_entry_label_def, NULL_EQ, AllCaseEqs()] >>
      `MEM bb' fn.fn_blocks` by
        (Cases_on `fn.fn_blocks` >> gvs[entry_block_def]) >>
      `lookup_block bb'.bb_label fn.fn_blocks = SOME bb'` by
        (irule MEM_lookup_block >> gvs[wf_function_def, fn_labels_def]) >>
      gvs[]) >>
  drule_all alias_path_snoc_invert >> strip_tac >>
  `~MEM bb.bb_label pre` by
    (simp[MEM_EL] >> rpt strip_tac >>
     first_x_assum (qspec_then `n` mp_tac) >> simp[EL_APPEND_EQN]) >>
  `phi_edge_uses_wf fn bb (EL k (collect_phis bb.bb_instructions))` by
    metis_tac[def_dominates_uses_def] >>
  `?v. MEM (LAST pre,v)
     (phi_pairs (EL k (collect_phis bb.bb_instructions)).inst_operands)` by
    (gvs[phi_edge_uses_wf_def] >> PairCases_on `p` >> gvs[] >>
     metis_tac[]) >>
  drule_all alias_phi_edge_available >> strip_tac >>
  qexists_tac `v` >> conj_tac
  >- (simp[inst_uses_def] >> irule alias_phi_pairs_subset_uses >>
      simp[MEM_MAP] >> goal_assum (drule_at Any) >> simp[]) >>
  conj_tac >- metis_tac[] >>
  rpt strip_tac >>
  `MEM bb.bb_label pre` by
    (irule alias_available_definition_visit >>
     simp[] >> qexistsl_tac [`bb`, `fn`] >> simp[] >>
     goal_assum (drule_at Any) >>
     goal_assum (drule_at Any) >> simp[] >>
     Cases_on `pre` >> gvs[] >> metis_tac[]) >> gvs[]
QED

Theorem alias_definition_excludes_other_block:
  wf_function fn /\ ssa_form fn /\
  lookup_block d fn.fn_blocks = SOME db /\ j < LENGTH db.bb_instructions /\
  MEM v (inst_defs (EL j db.bb_instructions)) /\
  lookup_block l fn.fn_blocks = SOME bb /\ l <> d /\ k < LENGTH bb.bb_instructions ==>
  ~MEM v (inst_defs (EL k bb.bb_instructions))
Proof
  metis_tac[alias_ssa_definition_position]
QED

Theorem alias_definition_excludes_other_index:
  wf_function fn /\ ssa_form fn /\
  lookup_block d fn.fn_blocks = SOME db /\ j < LENGTH db.bb_instructions /\
  MEM v (inst_defs (EL j db.bb_instructions)) /\ k <> j /\ k < LENGTH db.bb_instructions ==>
  ~MEM v (inst_defs (EL k db.bb_instructions))
Proof
  metis_tac[alias_ssa_definition_position]
QED

Theorem alias_def_available_definition_suffix:
  wf_function fn /\ ssa_form fn /\
  lookup_block d fn.fn_blocks = SOME db /\ j < LENGTH db.bb_instructions /\
  MEM v (inst_defs (EL j db.bb_instructions)) /\
  lookup_block p fn.fn_blocks = SOME pb /\
  def_available_at fn pb use_opt v /\
  is_fn_path fn path /\ path <> [] /\
  (?entry. fn_entry_label fn = SOME entry /\ HD path = entry) /\ LAST path = p ==>
  ?pre tail.
    path = pre ++ d::tail /\ ~MEM d tail /\
    is_fn_path fn (d::tail) /\ LAST (d::tail) = p /\
    (!l bb k. MEM l tail /\ lookup_block l fn.fn_blocks = SOME bb /\
      k < LENGTH bb.bb_instructions ==>
      ~MEM v (inst_defs (EL k bb.bb_instructions))) /\
    (d = p ==> case use_opt of NONE => T | SOME ui =>
      ?k. j < k /\ k < LENGTH pb.bb_instructions /\
          EL k pb.bb_instructions = ui)
Proof
  strip_tac >>
  `pb.bb_label = p` by metis_tac[lookup_block_label] >>
  qpat_x_assum `def_available_at _ _ _ _`
    (strip_assume_tac o REWRITE_RULE [def_available_at_def]) >>
  `lookup_block def_bb.bb_label fn.fn_blocks = SOME def_bb` by
    (irule MEM_lookup_block >> gvs[wf_function_def, fn_labels_def]) >>
  `?di. di < LENGTH def_bb.bb_instructions /\
    EL di def_bb.bb_instructions = def_inst` by metis_tac[MEM_EL] >>
  `d = def_bb.bb_label /\ j = di` by
    metis_tac[alias_ssa_definition_position, inst_defs_def] >>
  `def_bb = db` by metis_tac[optionTheory.SOME_11] >>
  `MEM d path` by metis_tac[fn_dominates_def] >>
  drule_all alias_path_last_visit >> strip_tac >>
  qexistsl_tac [`pre`, `tail`] >> simp[] >> conj_tac
  >- (rpt gen_tac >> strip_tac >>
      `l <> d` by metis_tac[] >>
      metis_tac[alias_definition_excludes_other_block]) >>
  strip_tac >> `db = pb` by metis_tac[optionTheory.SOME_11] >>
  Cases_on `use_opt` >> gvs[] >>
  `i < LENGTH db.bb_instructions` by decide_tac >>
  `i = di` by metis_tac[alias_ssa_definition_position] >>
  metis_tac[]
QED

Theorem alias_offset_reachable_use_witness:
  codegen_ready_fn fn /\ MEM oi (fn_insts fn) /\
  oi.inst_opcode = OFFSET /\ MEM v oi.inst_outputs ==>
  ?ub ui endpoint use_opt path.
    MEM ub fn.fn_blocks /\ MEM ui ub.bb_instructions /\
    MEM (Var v) ui.inst_operands /\
    lookup_block endpoint.bb_label fn.fn_blocks = SOME endpoint /\
    def_available_at fn endpoint use_opt v /\
    is_fn_path fn path /\ path <> [] /\
    (?entry. fn_entry_label fn = SOME entry /\ HD path = entry) /\
    LAST path = endpoint.bb_label /\
    ((ui.inst_opcode <> PHI /\ endpoint = ub /\ use_opt = SOME ui) \/
     (ui.inst_opcode = PHI /\ use_opt = NONE /\
      MEM (endpoint.bb_label,v) (phi_pairs ui.inst_operands) /\
      fn_cfg_edge fn endpoint.bb_label ub.bb_label))
Proof
  strip_tac >>
  `wf_function fn /\ def_dominates_uses fn /\ offset_outputs_used fn` by
    gvs[codegen_ready_fn_def] >>
  `?ui. MEM ui (fn_insts fn) /\ MEM (Var v) ui.inst_operands` by
    (gvs[offset_outputs_used_def, EVERY_MEM, EXISTS_MEM] >> metis_tac[]) >>
  `?ub. MEM ub fn.fn_blocks /\ MEM ui ub.bb_instructions` by
    (gvs[fn_insts_def, removeUnusedSsaProofsTheory.fn_insts_blocks_flat,
         MEM_FLAT, MEM_MAP] >> metis_tac[]) >>
  `?endpoint use_opt.
    MEM endpoint fn.fn_blocks /\ def_available_at fn endpoint use_opt v /\
    ((ui.inst_opcode <> PHI /\ endpoint = ub /\ use_opt = SOME ui) \/
     (ui.inst_opcode = PHI /\ use_opt = NONE /\
      MEM (endpoint.bb_label,v) (phi_pairs ui.inst_operands) /\
      fn_cfg_edge fn endpoint.bb_label ub.bb_label))` by
    (Cases_on `ui.inst_opcode = PHI`
     >- (`phi_edge_uses_wf fn ub ui` by metis_tac[def_dominates_uses_def] >>
         `?pred. MEM (pred,v) (phi_pairs ui.inst_operands)` by
           metis_tac[phi_well_formed_var_pair, phi_edge_uses_wf_def] >>
         gvs[phi_edge_uses_wf_def] >> metis_tac[]) >>
     qexistsl_tac [`ub`, `SOME ui`] >> simp[] >>
     metis_tac[def_dominates_uses_def]) >>
  `lookup_block endpoint.bb_label fn.fn_blocks = SOME endpoint` by
    (irule MEM_lookup_block >> gvs[wf_function_def, fn_labels_def]) >>
  `fn_reachable fn endpoint.bb_label` by
    gvs[def_available_at_def, fn_dominates_def] >>
  drule alias_reachable_first_visit >> strip_tac >>
  qexistsl_tac [`ub`, `ui`, `endpoint`, `use_opt`, `path`] >> simp[]
QED

Theorem alias_phi_ready_postprefix_input:
  wf_function fn /\ MEM lbl (cfg_analyze fn).cfg_dfs_pre /\
  lookup_block lbl fn.fn_blocks = SOME bb /\
  phi_block_ready (liveness_analyze fn) bb /\
  MEM v (live_vars_at (liveness_analyze fn) lbl
    (LENGTH (collect_phis bb.bb_instructions))) /\
  (!k. k < LENGTH (collect_phis bb.bb_instructions) ==>
    ~MEM v (inst_defs (EL k bb.bb_instructions))) ==>
  MEM v (input_vars_from pred bb.bb_instructions
    (live_vars_at (liveness_analyze fn) lbl 0))
Proof
  strip_tac >>
  `bb.bb_label = lbl` by metis_tac[lookup_block_label] >>
  `LENGTH (collect_phis bb.bb_instructions) <= LENGTH bb.bb_instructions` by
    (qspec_then `bb.bb_instructions` strip_assume_tac alias_collect_phis_prefix >>
     pop_assum (mp_tac o AP_TERM ``LENGTH:instruction list -> num``) >> simp[]) >>
  `MEM v (live_vars_at (liveness_analyze fn) lbl 0)` by
    (qspecl_then [`fn`, `lbl`, `bb`, `0`] mp_tac
       livenessAnalysisPropsTheory.live_vars_at_propagate_range >>
     simp[] >> disch_then irule >>
     qexists_tac `LENGTH (collect_phis bb.bb_instructions)` >> simp[]) >>
  metis_tac[alias_phi_ready_ordinary_input]
QED

Theorem alias_selected_input_liveout:
  wf_function fn /\ cfg_reachable_of (cfg_analyze fn) pred /\
  MEM lbl (cfg_succs_of (cfg_analyze fn) pred) /\
  lookup_block pred fn.fn_blocks = SOME pb /\
  lookup_block lbl fn.fn_blocks = SOME bb /\
  MEM v (input_vars_from pred bb.bb_instructions
    (live_vars_at (liveness_analyze fn) lbl 0)) ==>
  MEM v (live_vars_at (liveness_analyze fn) pred (LENGTH pb.bb_instructions))
Proof
  strip_tac >> drule_all liveness_recompute_edge_subset >>
  gvs[liveness_edge_transfer_def, live_vars_at_def, liveness_analyze_def,
      liveness_instrs_def, pred_setTheory.SUBSET_DEF]
QED

Theorem alias_fn_edge_succs:
  wf_function fn /\ fn_cfg_edge fn a b ==>
  MEM b (cfg_succs_of (cfg_analyze fn) a)
Proof
  rw[fn_cfg_edge_def] >>
  irule cfgAnalysisPropsTheory.bb_succs_in_cfg_succs >> gvs[wf_function_def]
QED

Theorem alias_path_liveout_backward:
  !tail fn d db endbb v.
  wf_function fn /\ is_fn_path fn (d::tail) /\
  (!l. MEM l (d::tail) ==> ?bb. lookup_block l fn.fn_blocks = SOME bb /\
    MEM l (cfg_analyze fn).cfg_dfs_pre /\ phi_block_ready (liveness_analyze fn) bb) /\
  (!l bb k. MEM l tail /\ lookup_block l fn.fn_blocks = SOME bb /\
    k < LENGTH bb.bb_instructions ==> ~MEM v (inst_defs (EL k bb.bb_instructions))) /\
  lookup_block d fn.fn_blocks = SOME db /\
  lookup_block (LAST (d::tail)) fn.fn_blocks = SOME endbb /\
  MEM v (live_vars_at (liveness_analyze fn) (LAST (d::tail)) (LENGTH endbb.bb_instructions)) ==>
  MEM v (live_vars_at (liveness_analyze fn) d (LENGTH db.bb_instructions))
Proof
  Induct >- (rpt strip_tac >> gvs[]) >> rpt strip_tac >>
  `?hb. lookup_block h fn.fn_blocks = SOME hb /\
    MEM h (cfg_analyze fn).cfg_dfs_pre /\ phi_block_ready (liveness_analyze fn) hb` by
    metis_tac[MEM] >>
  `MEM v (live_vars_at (liveness_analyze fn) h (LENGTH hb.bb_instructions))` by
    (first_x_assum irule >> simp[] >>
     gvs[is_fn_path_def, LAST_DEF] >> metis_tac[MEM]) >>
  `LENGTH (collect_phis hb.bb_instructions) <= LENGTH hb.bb_instructions` by
    (qspec_then `hb.bb_instructions` strip_assume_tac alias_collect_phis_prefix >>
     pop_assum (mp_tac o AP_TERM ``LENGTH:instruction list -> num``) >> simp[]) >>
  `MEM v (live_vars_at (liveness_analyze fn) h
      (LENGTH (collect_phis hb.bb_instructions)))` by
    (qspecl_then [`fn`, `h`, `hb`, `LENGTH (collect_phis hb.bb_instructions)`]
       mp_tac livenessAnalysisPropsTheory.live_vars_at_propagate_range >>
     simp[] >> disch_then irule >>
     qexists_tac `LENGTH hb.bb_instructions` >> simp[] >> metis_tac[MEM]) >>
  `MEM v (input_vars_from d hb.bb_instructions
      (live_vars_at (liveness_analyze fn) h 0))` by
    (irule alias_phi_ready_postprefix_input >> simp[] >>
     rpt strip_tac >>
     `k < LENGTH hb.bb_instructions` by decide_tac >> metis_tac[MEM]) >>
  `fn_cfg_edge fn d h` by gvs[is_fn_path_def] >>
  `MEM h (cfg_succs_of (cfg_analyze fn) d)` by
    metis_tac[alias_fn_edge_succs] >>
  `MEM d (cfg_analyze fn).cfg_dfs_pre` by metis_tac[MEM] >>
  `cfg_reachable_of (cfg_analyze fn) d` by
    (drule cfgAnalysisPropsTheory.cfg_analyze_reachable_sets >>
     simp[pred_setTheory.EXTENSION] >> metis_tac[]) >>
  metis_tac[alias_selected_input_liveout]
QED

Theorem alias_path_cut_liveout_backward:
  !tail fn d db endbb v j.
  wf_function fn /\ tail <> [] /\ is_fn_path fn (d::tail) /\
  (!l. MEM l (d::tail) ==> ?bb. lookup_block l fn.fn_blocks = SOME bb /\
    MEM l (cfg_analyze fn).cfg_dfs_pre /\ phi_block_ready (liveness_analyze fn) bb) /\
  (!l bb k. MEM l tail /\ lookup_block l fn.fn_blocks = SOME bb /\
    k < LENGTH bb.bb_instructions ==> ~MEM v (inst_defs (EL k bb.bb_instructions))) /\
  lookup_block d fn.fn_blocks = SOME db /\
  lookup_block (LAST (d::tail)) fn.fn_blocks = SOME endbb /\
  LENGTH (collect_phis endbb.bb_instructions) <= j /\ j <= LENGTH endbb.bb_instructions /\
  MEM v (live_vars_at (liveness_analyze fn) (LAST (d::tail)) j) ==>
  MEM v (live_vars_at (liveness_analyze fn) d (LENGTH db.bb_instructions))
Proof
  Induct >- simp[] >> rpt strip_tac >>
  `?hb. lookup_block h fn.fn_blocks = SOME hb /\
    MEM h (cfg_analyze fn).cfg_dfs_pre /\ phi_block_ready (liveness_analyze fn) hb` by
    metis_tac[MEM] >>
  `LENGTH (collect_phis hb.bb_instructions) <= LENGTH hb.bb_instructions` by
    (qspec_then `hb.bb_instructions` strip_assume_tac alias_collect_phis_prefix >>
     pop_assum (mp_tac o AP_TERM ``LENGTH:instruction list -> num``) >> simp[]) >>
  `MEM v (live_vars_at (liveness_analyze fn) h
      (LENGTH (collect_phis hb.bb_instructions)))` by
    (Cases_on `tail = []`
     >- (gvs[] >>
         qspecl_then [`fn`, `h`, `endbb`, `LENGTH (collect_phis endbb.bb_instructions)`]
           mp_tac livenessAnalysisPropsTheory.live_vars_at_propagate_range >>
         simp[] >> disch_then irule >> qexists_tac `j` >> simp[] >>
         metis_tac[MEM]) >>
     `MEM v (live_vars_at (liveness_analyze fn) h (LENGTH hb.bb_instructions))` by
       (first_x_assum irule >> simp[] >>
        gvs[is_fn_path_def, LAST_DEF] >> metis_tac[MEM]) >>
     qspecl_then [`fn`, `h`, `hb`, `LENGTH (collect_phis hb.bb_instructions)`]
       mp_tac livenessAnalysisPropsTheory.live_vars_at_propagate_range >>
     simp[] >> disch_then irule >>
     qexists_tac `LENGTH hb.bb_instructions` >> simp[] >> metis_tac[MEM]) >>
  `MEM v (input_vars_from d hb.bb_instructions
      (live_vars_at (liveness_analyze fn) h 0))` by
    (irule alias_phi_ready_postprefix_input >> simp[] >> rpt strip_tac >>
     `k < LENGTH hb.bb_instructions` by decide_tac >> metis_tac[MEM]) >>
  `fn_cfg_edge fn d h` by gvs[is_fn_path_def] >>
  `MEM h (cfg_succs_of (cfg_analyze fn) d)` by metis_tac[alias_fn_edge_succs] >>
  `MEM d (cfg_analyze fn).cfg_dfs_pre` by metis_tac[MEM] >>
  `cfg_reachable_of (cfg_analyze fn) d` by
    (drule cfgAnalysisPropsTheory.cfg_analyze_reachable_sets >>
     simp[pred_setTheory.EXTENSION] >> metis_tac[]) >>
  metis_tac[alias_selected_input_liveout]
QED

Theorem alias_ready_entry_path_member:
  codegen_ready_fn fn /\
  fn_entry_label fn = SOME entry /\ is_fn_path fn path /\ path <> [] /\
  HD path = entry /\ MEM l path ==>
  ?bb. lookup_block l fn.fn_blocks = SOME bb /\
    MEM l (cfg_analyze fn).cfg_dfs_pre /\ phi_block_ready (liveness_analyze fn) bb
Proof
  strip_tac >> `wf_function fn` by gvs[codegen_ready_fn_def] >>
  drule_all is_fn_path_prefix >> strip_tac >>
  `fn_reachable fn l` by
    (simp[fn_reachable_def] >>
     qspec_then `fn` (qspec_then `pre ++ [l]` mp_tac) is_fn_path_rtc >> simp[]) >>
  `cfg_reachable_of (cfg_analyze fn) l` by metis_tac[fn_reachable_cfg_analyze] >>
  `MEM l (cfg_analyze fn).cfg_dfs_pre` by
    (drule cfgAnalysisPropsTheory.cfg_analyze_reachable_sets >>
     simp[pred_setTheory.EXTENSION] >> metis_tac[]) >>
  `?bb. MEM bb fn.fn_blocks /\ bb.bb_label = l` by
    (drule cfgAnalysisPropsTheory.cfg_analyze_reachable_in_labels >>
     simp[fn_labels_def, MEM_MAP] >> metis_tac[]) >>
  qexists_tac `bb` >> simp[] >> conj_tac
  >- (irule MEM_lookup_block >> gvs[wf_function_def, fn_labels_def]) >>
  `phi_operands_ready fn` by gvs[codegen_ready_fn_def] >>
  gvs[phi_operands_ready_def, EVERY_MEM] >>
  `collect_phis bb.bb_instructions = []` by metis_tac[NULL_EQ] >>
  simp[phi_block_ready_def, phi_uses_disjoint_def]
QED

Theorem alias_ready_selected_source_not_phi_output:
  codegen_ready_fn fn /\ cfg_reachable_of (cfg_analyze fn) pred /\
  MEM lbl (cfg_succs_of (cfg_analyze fn) pred) /\
  lookup_block pred fn.fn_blocks = SOME pb /\
  lookup_block lbl fn.fn_blocks = SOME bb /\
  MEM v (input_vars_from pred bb.bb_instructions
    (live_vars_at (liveness_analyze fn) lbl 0)) /\
  MEM source (collect_phis bb.bb_instructions) /\
  MEM (pred,v) (phi_pairs source.inst_operands) /\
  MEM phi (collect_phis bb.bb_instructions) ==> ~MEM v (inst_defs phi)
Proof
  strip_tac >>
  `wf_function fn /\ ssa_form fn /\ def_dominates_uses fn` by
    gvs[codegen_ready_fn_def] >>
  `MEM bb fn.fn_blocks /\ bb.bb_label = lbl` by
    metis_tac[lookup_block_MEM, lookup_block_label] >>
  `MEM source bb.bb_instructions /\ source.inst_opcode = PHI` by
    metis_tac[livenessTransferProofsTheory.collect_phis_mem] >>
  `alias_path_available fn pred (LENGTH pb.bb_instructions) v` by
    (drule_all alias_phi_edge_available >> strip_tac >> gvs[]) >>
  `?j. j < LENGTH (collect_phis bb.bb_instructions) /\
       EL j bb.bb_instructions = phi` by
    (qspec_then `bb.bb_instructions` strip_assume_tac alias_collect_phis_prefix >>
     metis_tac[MEM_EL, EL_APPEND1]) >>
  `fn_reachable fn pred` by metis_tac[fn_reachable_cfg_analyze] >>
  `?entry path. fn_entry_label fn = SOME entry /\ is_fn_path fn path /\
       path <> [] /\ HD path = entry /\ LAST path = pred` by
    (qpat_x_assum `fn_reachable fn pred` mp_tac >>
     simp[fn_reachable_def] >> metis_tac[rtc_to_fn_path]) >>
  strip_tac >>
  `j < LENGTH bb.bb_instructions` by
    (qspec_then `bb.bb_instructions` strip_assume_tac alias_collect_phis_prefix >>
     pop_assum (mp_tac o AP_TERM ``LENGTH:instruction list -> num``) >> simp[]) >>
  `MEM lbl path` by
    (irule alias_available_definition_visit >> simp[] >>
     goal_assum (drule_at Any) >> metis_tac[]) >>
  drule_all alias_path_last_visit >> strip_tac >>
  `!l. MEM l (lbl::tail) ==> ?b. lookup_block l fn.fn_blocks = SOME b /\
      MEM l (cfg_analyze fn).cfg_dfs_pre /\ phi_block_ready (liveness_analyze fn) b` by
    (rpt strip_tac >> irule alias_ready_entry_path_member >>
     goal_assum (drule_at Any) >> metis_tac[MEM_APPEND]) >>
  `!l b k. MEM l tail /\ lookup_block l fn.fn_blocks = SOME b /\
      k < LENGTH b.bb_instructions ==> ~MEM v (inst_defs (EL k b.bb_instructions))` by
    (rpt gen_tac >> strip_tac >> irule alias_definition_excludes_other_block >>
     goal_assum (drule_at Any) >> metis_tac[]) >>
  `MEM v (live_vars_at (liveness_analyze fn) pred (LENGTH pb.bb_instructions))` by
    metis_tac[alias_selected_input_liveout] >>
  `MEM v (live_vars_at (liveness_analyze fn) lbl (LENGTH bb.bb_instructions))` by
    (irule alias_path_liveout_backward >> simp[] >>
     goal_assum (drule_at Any) >> qexists_tac `pb` >>
     metis_tac[MEM]) >>
  `MEM lbl (cfg_analyze fn).cfg_dfs_pre /\
   phi_block_ready (liveness_analyze fn) bb` by
    (qpat_x_assum `!l. MEM l (lbl::tail) ==> _`
       (qspec_then `lbl` mp_tac) >> simp[] >> strip_tac >>
     metis_tac[optionTheory.SOME_11]) >>
  `LENGTH (collect_phis bb.bb_instructions) <= LENGTH bb.bb_instructions` by
    (qspec_then `bb.bb_instructions` strip_assume_tac alias_collect_phis_prefix >>
     pop_assum (mp_tac o AP_TERM ``LENGTH:instruction list -> num``) >> simp[]) >>
  `MEM v (live_vars_at (liveness_analyze fn) lbl
      (LENGTH (collect_phis bb.bb_instructions)))` by
    (qspecl_then [`fn`, `lbl`, `bb`, `LENGTH (collect_phis bb.bb_instructions)`]
       mp_tac livenessAnalysisPropsTheory.live_vars_at_propagate_range >>
     simp[] >> disch_then irule >> qexists_tac `LENGTH bb.bb_instructions` >>
     simp[] >> rpt gen_tac >> strip_tac >>
     irule alias_definition_excludes_other_index >>
     goal_assum (drule_at Any) >>
     `k <> j` by decide_tac >> metis_tac[]) >>
  `MEM v (inst_uses source)` by
    (simp[inst_uses_def] >> irule alias_phi_pairs_subset_uses >>
     simp[MEM_MAP] >> qexists_tac `(pred,v)` >> simp[]) >>
  qpat_x_assum `phi_block_ready _ bb` mp_tac >>
  simp[phi_block_ready_def, EVERY_MEM] >> metis_tac[]
QED

Theorem alias_ready_input_not_phi_output:
  codegen_ready_fn fn /\ cfg_reachable_of (cfg_analyze fn) pred /\
  MEM lbl (cfg_succs_of (cfg_analyze fn) pred) /\
  lookup_block pred fn.fn_blocks = SOME pb /\
  lookup_block lbl fn.fn_blocks = SOME bb /\
  MEM v (input_vars_from pred bb.bb_instructions
    (live_vars_at (liveness_analyze fn) lbl 0)) /\
  MEM phi (collect_phis bb.bb_instructions) ==> ~MEM v (inst_defs phi)
Proof
  strip_tac >>
  drule alias_input_vars_from_partition >> strip_tac
  >- (`wf_function fn /\ def_dominates_uses fn` by gvs[codegen_ready_fn_def] >>
      `MEM bb fn.fn_blocks /\ bb.bb_label = lbl /\
       MEM pb fn.fn_blocks /\ pb.bb_label = pred` by
        metis_tac[lookup_block_MEM, lookup_block_label] >>
      `fn_cfg_edge fn pred lbl` by
        (drule_all cfgAnalysisPropsTheory.cfg_analyze_preserves_bb_succs >>
         strip_tac >> gvs[fn_cfg_edge_def] >> metis_tac[]) >>
      `fn_reachable fn pred` by metis_tac[fn_reachable_cfg_analyze] >>
      `fn_reachable fn lbl` by metis_tac[fn_reachable_step] >>
      `MEM lbl (cfg_analyze fn).cfg_dfs_pre` by
        (drule cfgAnalysisPropsTheory.cfg_analyze_reachable_sets >>
         simp[pred_setTheory.EXTENSION] >> metis_tac[fn_reachable_cfg_analyze]) >>
      `!p. MEM p (collect_phis bb.bb_instructions) ==>
          phi_well_formed p.inst_operands` by
        (rpt strip_tac >>
         drule livenessTransferProofsTheory.collect_phis_mem >> strip_tac >>
         metis_tac[def_dominates_uses_def, phi_edge_uses_wf_def]) >>
      metis_tac[alias_phi_map_absent_not_output]) >>
  metis_tac[alias_ready_selected_source_not_phi_output]
QED

Theorem alias_input_fold_trigger:
  !base acc placed.
  FLOOKUP op_map v = SOME i /\ FLOOKUP matching i = SOME x /\
  (MEM i placed ==> MEM x acc) /\ (MEM x acc \/ MEM v base) ==>
  MEM x (FST (FOLDL (\(acc,placed) w.
    case FLOOKUP op_map w of
      NONE => (acc ++ [w], placed)
    | SOME j => if MEM j placed then (acc,placed)
        else case FLOOKUP matching j of
          NONE => (acc,placed)
        | SOME y => (acc ++ [y],j::placed)) (acc,placed) base))
Proof
  Induct >> simp[] >> rpt gen_tac >> disch_tac >>
  Cases_on `FLOOKUP op_map h` >> simp[]
  >- (first_x_assum irule >> gvs[] >> metis_tac[]) >>
  rename1 `_ = SOME j` >> Cases_on `MEM j placed` >> simp[]
  >- (first_x_assum irule >> gvs[] >> metis_tac[]) >>
  Cases_on `FLOOKUP matching j` >> simp[] >>
  first_x_assum irule >> gvs[] >> metis_tac[optionTheory.SOME_11]
QED

Theorem alias_input_vars_trigger_intro:
  !pred instrs v i base x.
  FLOOKUP (FST (build_phi_maps pred (collect_phis instrs))) v = SOME i /\
  MEM v base /\
  FLOOKUP (SND (build_phi_maps pred (collect_phis instrs))) i = SOME x ==>
  MEM x (input_vars_from pred instrs base)
Proof
  rpt strip_tac >> simp[input_vars_from_def] >>
  Cases_on `NULL (collect_phis instrs)`
  >- gvs[NULL_EQ, build_phi_maps_def] >>
  Cases_on `build_phi_maps pred (collect_phis instrs)` >> gvs[] >>
  simp[Once pairTheory.UNCURRY] >> irule alias_input_fold_trigger >>
  simp[] >> metis_tac[]
QED

Theorem alias_phi_pair_fold_lookup:
  !pairs m v j.
  FLOOKUP (FOLDL (\m (l,w). m |+ (w,j)) m pairs) v =
    if MEM v (MAP SND pairs) then SOME j else FLOOKUP m v
Proof
  Induct >> simp[] >> gen_tac >> PairCases_on `h` >>
  simp[finite_mapTheory.FLOOKUP_UPDATE] >> rpt gen_tac >>
  Cases_on `h1 = v` >> simp[] >> metis_tac[]
QED

Theorem alias_phi_maps_fold_op_lookup:
  !indexed op_map matching pred v k.
  (!j phi. MEM (j,phi) indexed /\
      MEM v (MAP SND (phi_pairs phi.inst_operands)) ==> j = k) ==>
  FLOOKUP (FST (FOLDL (\(op_map,matching) (j,phi).
    (FOLDL (\m (l,w). m |+ (w,j)) op_map (phi_pairs phi.inst_operands),
     case FIND (\(l,w). l = pred) (phi_pairs phi.inst_operands) of
       NONE => matching | SOME (l,w) => matching |+ (j,w)))
    (op_map,matching) indexed)) v =
  if EXISTS (\(j,phi). MEM v (MAP SND (phi_pairs phi.inst_operands))) indexed
  then SOME k else FLOOKUP op_map v
Proof
  Induct >> simp[] >> gen_tac >> PairCases_on `h` >> rpt gen_tac >> strip_tac >>
  `!j phi. MEM (j,phi) indexed /\
      MEM v (MAP SND (phi_pairs phi.inst_operands)) ==> j = k` by
    metis_tac[] >>
  simp[Once FOLDL] >>
  last_x_assum drule >> disch_then (fn th => rewrite_tac[th]) >>
  simp[alias_phi_pair_fold_lookup] >>
  Cases_on `MEM v (MAP SND (phi_pairs h1.inst_operands))` >> simp[] >>
  metis_tac[]
QED

Theorem alias_phi_uses_disjoint_index:
  !phis i j v. phi_uses_disjoint phis /\ i < LENGTH phis /\
    j < LENGTH phis /\ MEM v (inst_uses (EL i phis)) /\
    MEM v (inst_uses (EL j phis)) ==> i = j
Proof
  Induct >- simp[] >> rpt gen_tac >> strip_tac >>
  gvs[phi_uses_disjoint_def, EVERY_MEM] >>
  Cases_on `i` >> Cases_on `j` >> gvs[] >> metis_tac[EL_MEM]
QED

Theorem alias_build_phi_maps_op_index:
  phi_uses_disjoint phis /\ k < LENGTH phis /\
  MEM (edge,v) (phi_pairs (EL k phis).inst_operands) ==>
  FLOOKUP (FST (build_phi_maps pred phis)) v = SOME k
Proof
  strip_tac >> simp[build_phi_maps_def] >>
  `!j phi. MEM (j,phi) (MAPi (\i phi. (i,phi)) phis) /\
      MEM v (MAP SND (phi_pairs phi.inst_operands)) ==> j = k` by
    (simp[indexedListsTheory.MEM_MAPi] >> rpt strip_tac >> gvs[] >>
     irule alias_phi_uses_disjoint_index >>
     goal_assum (drule_at Any) >> simp[] >>
     qexists_tac `v` >> conj_tac
     >- (simp[inst_uses_def] >> irule alias_phi_pairs_subset_uses >> simp[]) >>
     simp[inst_uses_def] >> irule alias_phi_pairs_subset_uses >>
     simp[MEM_MAP] >> goal_assum (drule_at Any) >> simp[]) >>
  drule alias_phi_maps_fold_op_lookup >>
  disch_then (fn th => rewrite_tac[th]) >>
  simp[EXISTS_MEM, indexedListsTheory.MEM_MAPi] >>
  `?i. i < LENGTH phis /\ MEM v (MAP SND (phi_pairs (EL i phis).inst_operands))` by
    (qexists_tac `k` >> simp[MEM_MAP] >>
     goal_assum (drule_at Any) >> simp[]) >>
  qexists_tac `(i, EL i phis)` >> simp[] >> metis_tac[]
QED

Theorem alias_phi_maps_fold_matching_lookup:
  !indexed op_map matching pred k x.
  (!phi. MEM (k,phi) indexed ==>
    FIND (\(l,w). l = pred) (phi_pairs phi.inst_operands) = SOME (pred,x)) ==>
  FLOOKUP (SND (FOLDL (\(op_map,matching) (j,phi).
    (FOLDL (\m (l,w). m |+ (w,j)) op_map (phi_pairs phi.inst_operands),
     case FIND (\(l,w). l = pred) (phi_pairs phi.inst_operands) of
       NONE => matching | SOME (l,w) => matching |+ (j,w)))
    (op_map,matching) indexed)) k =
  if MEM k (MAP FST indexed) then SOME x else FLOOKUP matching k
Proof
  Induct >> simp[] >> gen_tac >> PairCases_on `h` >>
  rpt gen_tac >> strip_tac >>
  `!phi. MEM (k,phi) indexed ==>
    FIND (\(l,w). l = pred) (phi_pairs phi.inst_operands) = SOME (pred,x)` by
    metis_tac[] >>
  simp[Once FOLDL] >>
  last_x_assum drule >> disch_then (fn th => rewrite_tac[th]) >>
  Cases_on `h0 = k` >> gvs[]
  >- (Cases_on `MEM k (MAP FST indexed)` >> simp[finite_mapTheory.FLOOKUP_UPDATE]) >>
  Cases_on `FIND (\(l,w). l = pred) (phi_pairs h1.inst_operands)` >> simp[] >>
  PairCases_on `x'` >> simp[finite_mapTheory.FLOOKUP_UPDATE] >>
  Cases_on `MEM k (MAP FST indexed)` >> simp[]
QED

Theorem alias_phi_pair_find:
  !pairs pred x. ALL_DISTINCT (MAP FST pairs) /\ MEM (pred,x) pairs ==>
    FIND (\(l,w). l = pred) pairs = SOME (pred,x)
Proof
  Induct >> simp[] >> gen_tac >> PairCases_on `h` >>
  rpt gen_tac >> strip_tac >> gvs[] >>
  Cases_on `h0 = pred` >> gvs[FIND_thm, MEM_MAP] >> metis_tac[]
QED

Theorem alias_build_phi_maps_matching_index:
  k < LENGTH phis /\
  ALL_DISTINCT (MAP FST (phi_pairs (EL k phis).inst_operands)) /\
  MEM (pred,x) (phi_pairs (EL k phis).inst_operands) ==>
  FLOOKUP (SND (build_phi_maps pred phis)) k = SOME x
Proof
  strip_tac >> simp[build_phi_maps_def] >>
  `!phi. MEM (k,phi) (MAPi (\i phi. (i,phi)) phis) ==>
    FIND (\(l,w). l = pred) (phi_pairs phi.inst_operands) = SOME (pred,x)` by
    (simp[indexedListsTheory.MEM_MAPi] >> rpt strip_tac >> gvs[] >>
     irule alias_phi_pair_find >> simp[]) >>
  drule alias_phi_maps_fold_matching_lookup >>
  disch_then (fn th => rewrite_tac[th]) >>
  `MEM k (MAP FST (MAPi (\i phi. (i,phi)) phis))` by
    (simp[MEM_MAP, indexedListsTheory.MEM_MAPi] >>
     qexists_tac `(k, EL k phis)` >> simp[]) >> simp[]
QED

Theorem alias_ready_phi_input_member:
  codegen_ready_fn fn /\ fn_reachable fn lbl /\
  lookup_block lbl fn.fn_blocks = SOME bb /\
  k < LENGTH (collect_phis bb.bb_instructions) /\
  MEM (pred,x)
    (phi_pairs (EL k (collect_phis bb.bb_instructions)).inst_operands) ==>
  MEM x (input_vars_from pred bb.bb_instructions
    (live_vars_at (liveness_analyze fn) lbl 0))
Proof
  strip_tac >>
  drule_all alias_ready_phi_nonlocal_source >> strip_tac >>
  `wf_function fn` by gvs[codegen_ready_fn_def] >>
  `MEM lbl (cfg_analyze fn).cfg_dfs_pre` by
    (`cfg_reachable_of (cfg_analyze fn) lbl` by
       metis_tac[fn_reachable_cfg_analyze] >>
     drule cfgAnalysisPropsTheory.cfg_analyze_reachable_sets >>
     simp[pred_setTheory.EXTENSION] >> metis_tac[]) >>
  `?tail. bb.bb_instructions = collect_phis bb.bb_instructions ++ tail` by
    metis_tac[alias_collect_phis_prefix] >>
  `k < LENGTH bb.bb_instructions /\
   EL k (collect_phis bb.bb_instructions) = EL k bb.bb_instructions` by
    (conj_tac
     >- (qpat_assum `bb.bb_instructions = _`
           (mp_tac o AP_TERM ``LENGTH:instruction list -> num``) >> simp[]) >>
     qpat_assum `bb.bb_instructions = _`
       (fn th => CONV_TAC (RHS_CONV (RAND_CONV (REWR_CONV th)))) >>
     simp[EL_APPEND_EQN]) >>
  `MEM v (live_vars_at (liveness_analyze fn) lbl k)` by
    (drule livenessAnalysisPropsTheory.live_vars_at_uses >> simp[] >>
     disch_then irule >> goal_assum (drule_at Any) >> simp[] >> metis_tac[]) >>
  `MEM v (live_vars_at (liveness_analyze fn) lbl 0)` by
    (drule livenessAnalysisPropsTheory.live_vars_at_propagate_range >> simp[] >>
     disch_then irule >> goal_assum (drule_at Any) >> simp[] >>
     qexists_tac `k` >> simp[]) >>
  `phi_uses_disjoint (collect_phis bb.bb_instructions)` by
    (gvs[codegen_ready_fn_def, phi_operands_ready_def, phi_block_ready_def,
         EVERY_MEM, NULL_EQ, phi_uses_disjoint_def] >>
     metis_tac[lookup_block_MEM, phi_uses_disjoint_def]) >>
  `ALL_DISTINCT (MAP FST
    (phi_pairs (EL k (collect_phis bb.bb_instructions)).inst_operands))` by
    (`phi_edge_uses_wf fn bb (EL k (collect_phis bb.bb_instructions))` by
       (gvs[codegen_ready_fn_def, def_dominates_uses_def] >>
        metis_tac[lookup_block_MEM, livenessProofsTheory.collect_phis_mem, EL_MEM]) >>
     gvs[phi_edge_uses_wf_def]) >>
  irule alias_input_vars_trigger_intro >>
  goal_assum (drule_at Any) >> qexists_tac `k` >> conj_tac
  >- (irule alias_build_phi_maps_matching_index >> simp[]) >>
  irule alias_build_phi_maps_op_index >> metis_tac[]
QED

Theorem alias_collect_phis_index:
  !insts k. k < LENGTH insts /\
    (!i. i <= k ==> (EL i insts).inst_opcode = PHI) ==>
    k < LENGTH (collect_phis insts) /\
    EL k (collect_phis insts) = EL k insts
Proof
  Induct >- simp[] >> rpt gen_tac >> strip_tac >>
  `h.inst_opcode = PHI` by
    (first_x_assum (qspec_then `0` mp_tac) >> simp[]) >>
  Cases_on `k` >> gvs[collect_phis_def] >>
  first_x_assum irule >> simp[] >> rpt strip_tac >>
  first_x_assum (qspec_then `SUC i` mp_tac) >> simp[]
QED

Theorem alias_offset_output_live_after:
  codegen_ready_fn fn /\
  lookup_block d fn.fn_blocks = SOME db /\
  j < LENGTH db.bb_instructions /\
  (EL j db.bb_instructions).inst_opcode = OFFSET /\
  MEM v (EL j db.bb_instructions).inst_outputs ==>
  MEM v (live_vars_at (liveness_analyze fn) d (SUC j))
Proof
  strip_tac >>
  `wf_function fn /\ ssa_form fn` by gvs[codegen_ready_fn_def] >>
  `MEM v (inst_defs (EL j db.bb_instructions))` by simp[inst_defs_def] >>
  `MEM (EL j db.bb_instructions) (fn_insts fn)` by
    (simp[fn_insts_def, removeUnusedSsaProofsTheory.fn_insts_blocks_flat,
          MEM_FLAT, MEM_MAP] >>
     metis_tac[lookup_block_MEM, EL_MEM]) >>
  drule_all alias_offset_reachable_use_witness >>
  disch_then (qx_choose_then `ub` (qx_choose_then `ui`
    (qx_choose_then `endpoint` (qx_choose_then `use_opt`
      (qx_choose_then `path` strip_assume_tac))))) >>
  `?pre tail.
    path = pre ++ d::tail /\ ~MEM d tail /\
    is_fn_path fn (d::tail) /\ LAST (d::tail) = endpoint.bb_label /\
    (!l bb k. MEM l tail /\ lookup_block l fn.fn_blocks = SOME bb /\
      k < LENGTH bb.bb_instructions ==> ~MEM v (inst_defs (EL k bb.bb_instructions))) /\
    (d = endpoint.bb_label ==> case use_opt of NONE => T | SOME ui =>
      ?k. j < k /\ k < LENGTH endpoint.bb_instructions /\
          EL k endpoint.bb_instructions = ui)` by
    (irule alias_def_available_definition_suffix >>
     goal_assum (drule_at Any) >> simp[] >>
     goal_assum (drule_at Any) >> simp[] >> metis_tac[]) >>
  `!l. MEM l (d::tail) ==> ?bb. lookup_block l fn.fn_blocks = SOME bb /\
      MEM l (cfg_analyze fn).cfg_dfs_pre /\ phi_block_ready (liveness_analyze fn) bb` by
    (rpt strip_tac >> irule alias_ready_entry_path_member >>
     goal_assum (drule_at Any) >> metis_tac[MEM_APPEND]) >>
  `!k. SUC j <= k /\ k < LENGTH db.bb_instructions ==>
    ~MEM v (inst_defs (EL k db.bb_instructions))` by
    (rpt gen_tac >> strip_tac >> `k <> j` by decide_tac >>
     metis_tac[alias_definition_excludes_other_index]) >>
  `MEM d (cfg_analyze fn).cfg_dfs_pre` by metis_tac[MEM, optionTheory.SOME_11] >>
  `(?k. SUC j <= k /\ k <= LENGTH db.bb_instructions /\
       MEM v (live_vars_at (liveness_analyze fn) d k))` suffices_by
    (strip_tac >> drule livenessAnalysisPropsTheory.live_vars_at_propagate_range >>
     simp[] >> disch_then irule >> simp[] >> qexists_tac `k` >>
     simp[] >> rpt strip_tac >> first_x_assum irule >> decide_tac) >>
  FIRST [qpat_assum `use_opt = SOME _` (K (suspend "ordinary")),
         qpat_assum `use_opt = NONE` (K (suspend "phi"))]
QED

Resume alias_offset_output_live_after[ordinary]:
  gvs[] >>
  `MEM endpoint.bb_label (cfg_analyze fn).cfg_dfs_pre` by
    metis_tac[MEM, MEM_LAST] >>
  `?k. k < LENGTH endpoint.bb_instructions /\ EL k endpoint.bb_instructions = ui` by
    metis_tac[MEM_EL] >>
  `LENGTH (collect_phis endpoint.bb_instructions) <= k` by
    (spose_not_then assume_tac >>
     `k < LENGTH (collect_phis endpoint.bb_instructions)` by decide_tac >>
     qspec_then `endpoint.bb_instructions` strip_assume_tac alias_collect_phis_prefix >>
     `EL k (collect_phis endpoint.bb_instructions) = ui` by metis_tac[EL_APPEND1] >>
     metis_tac[livenessTransferProofsTheory.collect_phis_mem, EL_MEM]) >>
  `MEM v (live_vars_at (liveness_analyze fn) endpoint.bb_label k)` by
    (drule livenessAnalysisPropsTheory.live_vars_at_uses >> simp[] >>
     disch_then irule >> goal_assum (drule_at Any) >>
     simp[inst_uses_def, passSharedDefsTheory.MEM_operand_vars_eq_Var]) >>
  Cases_on `tail = []`
  >- (gvs[] >> qexists_tac `k'` >> simp[] >>
      drule livenessAnalysisPropsTheory.live_vars_at_uses >> simp[] >>
      disch_then irule >> goal_assum (drule_at Any) >>
      simp[inst_uses_def, passSharedDefsTheory.MEM_operand_vars_eq_Var]) >>
  qexists_tac `LENGTH db.bb_instructions` >> simp[] >>
  irule alias_path_cut_liveout_backward >>
  goal_assum (drule_at Any) >> simp[] >>
  goal_assum (drule_at Any) >> simp[] >>
  qexists_tac `k` >> simp[] >> metis_tac[]
QED

Resume alias_offset_output_live_after[phi]:
  `fn_reachable fn endpoint.bb_label` by
    gvs[def_available_at_def, fn_dominates_def] >>
  `fn_reachable fn ub.bb_label` by metis_tac[fn_reachable_step] >>
  `lookup_block ub.bb_label fn.fn_blocks = SOME ub` by
    (irule MEM_lookup_block >> gvs[wf_function_def, fn_labels_def]) >>
  `bb_well_formed ub` by metis_tac[wf_function_def] >>
  `?m. m < LENGTH ub.bb_instructions /\ EL m ub.bb_instructions = ui` by
    metis_tac[MEM_EL] >>
  `!i. i <= m ==> (EL i ub.bb_instructions).inst_opcode = PHI` by
    (rpt strip_tac >> Cases_on `i = m` >- gvs[] >>
     `i < m` by decide_tac >> gvs[bb_well_formed_def] >> metis_tac[]) >>
  drule_all alias_collect_phis_index >> strip_tac >>
  `MEM v (input_vars_from endpoint.bb_label ub.bb_instructions
    (live_vars_at (liveness_analyze fn) ub.bb_label 0))` by
    (irule alias_ready_phi_input_member >> goal_assum (drule_at Any) >>
     simp[] >> qexists_tac `m` >> simp[]) >>
  `cfg_reachable_of (cfg_analyze fn) endpoint.bb_label` by
    metis_tac[fn_reachable_cfg_analyze] >>
  `MEM ub.bb_label (cfg_succs_of (cfg_analyze fn) endpoint.bb_label)` by
    metis_tac[alias_fn_edge_succs] >>
  `MEM v (live_vars_at (liveness_analyze fn) endpoint.bb_label
    (LENGTH endpoint.bb_instructions))` by
    metis_tac[alias_selected_input_liveout] >>
  qexists_tac `LENGTH db.bb_instructions` >> simp[] >>
  irule alias_path_liveout_backward >>
  goal_assum (drule_at Any) >> simp[] >>
  goal_assum (drule_at Any) >> simp[]
QED

Finalise alias_offset_output_live_after

Theorem alias_lineage_join_ordinary_coverage:
  liveness = liveness_analyze fn /\ dfg = dfg_build_function fn /\
  cfg = cfg_analyze fn /\ codegen_ready_fn fn /\
  lineage_state liveness dfg cfg fn
    (init_cleanup_plan_state ch growth spill_base lbl_ctr) lbl ps /\
  lookup_block lbl fn.fn_blocks = SOME bb /\
  1 < LENGTH (cfg_preds_of cfg lbl) /\
  MEM v (live_vars_at liveness lbl 0) /\
  MEM v (live_vars_at liveness lbl
    (LENGTH (collect_phis bb.bb_instructions))) ==>
  MEM (Var v) ps.ps_stack
Proof
  strip_tac >>
  drule_all alias_lineage_join_historical_coverage >> strip_tac >>
  `MEM bb fn.fn_blocks /\ bb.bb_label = lbl` by
    metis_tac[lookup_block_MEM, lookup_block_label] >>
  first_x_assum irule >>
  Cases_on `NULL (collect_phis bb.bb_instructions)`
  >- gvs[input_vars_from_def] >>
  `phi_block_ready (liveness_analyze fn) bb` by
    (gvs[codegen_ready_fn_def, phi_operands_ready_def, EVERY_MEM] >>
     metis_tac[]) >>
  metis_tac[alias_phi_ready_ordinary_input]
QED

Theorem alias_do_swap_stack:
  dist < LENGTH ps.ps_stack ==>
  (SND (do_swap dist ps)).ps_stack = stack_swap dist ps.ps_stack
Proof
  strip_tac >> Cases_on `dist = 0`
  >- (gvs[do_swap_def, stack_swap_def, LUPDATE_SAME]) >>
  Cases_on `dist <= 16` >- simp[do_swap_def] >>
  simp[do_swap_def] >> pairarg_tac >> simp[] >>
  simp[top_n_def, GSYM LASTN_def, LASTN_DROP] >>
  irule LIST_EQ >>
  simp[stack_swap_def, LENGTH_LUPDATE] >>
  rpt strip_tac >>
  simp[EL_APPEND_EQN, EL_MAP, EL_GENLIST, EL_LUPDATE, EL_DROP] >>
  Cases_on `x = LENGTH ps.ps_stack - (dist + 1)`
  >- (gvs[] >> simp[]) >>
  Cases_on `x = LENGTH ps.ps_stack - 1`
  >- (gvs[] >> simp[HD_DROP]) >>
  Cases_on `x < LENGTH ps.ps_stack - (dist + 1)` >>
  simp[EL_TAKE]
QED

Theorem alias_select_spill_candidate_large:
  16 < target_len ==>
  select_spill_candidate stk forbidden target_dist target_len = NONE
Proof
  strip_tac >>
  Cases_on `select_spill_candidate stk forbidden target_dist target_len`
  >- simp[] >>
  drule planWfTheory.select_spill_candidate_below_target >>
  gvs[select_spill_candidate_def] >>
  imp_res_tac FIND_SOME_MEM >> gvs[MEM_GENLIST, arithmeticTheory.MIN_DEF]
QED

Theorem alias_reduce_depth_plan_large:
  16 < target_len ==>
  reduce_depth_plan fuel target_ops target_op f target_len ps = ([],ps)
Proof
  strip_tac >> Cases_on `fuel` >>
  simp[reduce_depth_plan_def, alias_select_spill_candidate_large] >>
  Cases_on `stack_get_unfixed_depth target_op f target_len ps.ps_stack` >> simp[]
QED

Theorem alias_reorder_one_large_step:
  16 < LENGTH pending /\ idx < LENGTH pending /\
  LENGTH pending <= LENGTH ps.ps_stack /\
  stack_get_unfixed_depth op (LENGTH pending - (idx + 1))
    (LENGTH pending) ps.ps_stack = SOME d /\
  reorder_one dfg pending idx op ps = (ops,qs) ==>
  LENGTH qs.ps_stack = LENGTH ps.ps_stack /\
  qs.ps_spilled = ps.ps_spilled /\
  (!at. LIST_ELEM_COUNT at qs.ps_stack = LIST_ELEM_COUNT at ps.ps_stack) /\
  stack_peek (LENGTH pending - (idx + 1)) qs.ps_stack = op /\
  (!i. i < idx ==> stack_peek (LENGTH pending - 1 - i) qs.ps_stack =
                   stack_peek (LENGTH pending - 1 - i) ps.ps_stack)
Proof
  strip_tac >>
  drule_then strip_assume_tac stack_get_unfixed_depth_props >>
  qpat_x_assum `reorder_one _ _ _ _ _ = _` mp_tac >>
  simp[reorder_one_def, alias_reduce_depth_plan_large] >>
  Cases_on `d = LENGTH pending - (idx + 1)`
  >- (gvs[] >> simp[]) >>
  `LENGTH pending - (idx + 1) < LENGTH ps.ps_stack` by decide_tac >>
  simp[] >>
  Cases_on `operand_equiv dfg op (stack_peek (LENGTH pending - (idx + 1)) ps.ps_stack)`
  >- (simp[] >> disch_then strip_assume_tac >> gnvs[] >>
      conj_tac >- simp[stack_poke_def, LENGTH_LUPDATE] >>
      conj_tac
      >- (gen_tac >> irule doSwapSimTheory.stack_poke_exchange_multiplicity >> simp[]) >>
      simp[stack_peek_def, stack_poke_def, EL_LUPDATE] >>
      rpt strip_tac >> rpt IF_CASES_TAC >> gvs[]) >>
  pairarg_tac >> simp[] >> pairarg_tac >> simp[] >>
  disch_then strip_assume_tac >> gnvs[] >>
  rename1 `do_swap (LENGTH pending - (idx + 1)) ps3 = (swap2_ops,qs)` >>
  `LENGTH ps3.ps_stack = LENGTH ps.ps_stack /\
   ps3.ps_spilled = ps.ps_spilled` by
    (drule planWfTheory.do_swap_length >>
     qspec_then `d` (qspec_then `ps` mp_tac) do_swap_spilled_unchanged >> simp[]) >>
  `LENGTH qs.ps_stack = LENGTH ps.ps_stack /\
   qs.ps_spilled = ps.ps_spilled` by
    (qspec_then `LENGTH pending - (idx + 1)`
       (qspec_then `ps3` mp_tac) planWfTheory.do_swap_length >>
     qspec_then `LENGTH pending - (idx + 1)`
       (qspec_then `ps3` mp_tac) do_swap_spilled_unchanged >> simp[]) >>
  simp[] >> conj_tac
  >- (gen_tac >>
      qspec_then `d` (qspec_then `ps` mp_tac) doSwapSimTheory.do_swap_multiplicity >>
      qspec_then `LENGTH pending - (idx + 1)`
        (qspec_then `ps3` mp_tac) doSwapSimTheory.do_swap_multiplicity >> simp[]) >>
  `ps3.ps_stack = stack_swap d ps.ps_stack` by
    (drule alias_do_swap_stack >> simp[]) >>
  `LENGTH pending - (idx + 1) < LENGTH ps3.ps_stack` by simp[] >>
  `qs.ps_stack = stack_swap (LENGTH pending - (idx + 1)) ps3.ps_stack` by
    metis_tac[alias_do_swap_stack, pairTheory.SND] >>
  simp[stack_peek_def, stack_swap_def, EL_LUPDATE] >>
  rpt strip_tac >> rpt IF_CASES_TAC >> gvs[]
QED

Theorem alias_plan_steps_large_materialised:
  !rest done pending dfg ps ops qs.
  pending = done ++ rest /\ 16 < LENGTH pending /\
  LENGTH pending <= LENGTH ps.ps_stack /\
  (!at. LIST_ELEM_COUNT at pending <= LIST_ELEM_COUNT at ps.ps_stack) /\
  (!i. i < LENGTH done ==>
    stack_peek (LENGTH pending - 1 - i) ps.ps_stack = EL i pending) /\
  plan_steps (\(idx,op) ps. reorder_one dfg pending idx op ps)
    (MAPi (\i op. (LENGTH done + i,op)) rest) ps = (ops,qs) ==>
  LENGTH qs.ps_stack = LENGTH ps.ps_stack /\
  qs.ps_spilled = ps.ps_spilled /\
  (!at. LIST_ELEM_COUNT at qs.ps_stack = LIST_ELEM_COUNT at ps.ps_stack) /\
  (!i. i < LENGTH pending ==>
    stack_peek (LENGTH pending - 1 - i) qs.ps_stack = EL i pending)
Proof
  Induct_on `rest`
  >- (simp[foldlSimTheory.plan_steps_def] >> rpt strip_tac >> gvs[]) >>
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `plan_steps _ _ _ = _` mp_tac >>
  simp[indexedListsTheory.MAPi_def, combinTheory.o_DEF, arithmeticTheory.ADD_CLAUSES] >>
  strip_tac >> drule plan_steps_cons_result >> strip_tac >> gvs[] >>
  rule_assum_tac (PURE_REWRITE_RULE [GSYM APPEND_ASSOC, APPEND]) >>
  `LENGTH done < LENGTH (done ++ h::rest)` by simp[] >>
  `EL (LENGTH done) (done ++ h::rest) = h` by simp[EL_APPEND_EQN] >>
  `?d. stack_get_unfixed_depth h
    (LENGTH (done ++ h::rest) - (LENGTH done + 1))
    (LENGTH (done ++ h::rest)) ps.ps_stack = SOME d` by
    (qspecl_then [`done ++ h::rest`, `LENGTH done`, `ps`]
       mp_tac materialised_pending_next_on_stack_window >>
       `SUC (LENGTH done + LENGTH rest) - (LENGTH done + 1) = LENGTH rest` by decide_tac >>
       simp[arithmeticTheory.ADD_CLAUSES]) >>
  drule_at (Pat `reorder_one _ _ _ _ _ = _`) alias_reorder_one_large_step >>
  simp[] >> disch_then strip_assume_tac >>
  first_x_assum (qspec_then `done ++ [h]` mp_tac) >>
  pure_rewrite_tac[GSYM APPEND_ASSOC, APPEND, LENGTH_APPEND, LENGTH] >>
  disch_then (qspecl_then [`dfg`, `ps1`, `rest_ops`, `qs`] mp_tac) >>
  simp[arithmeticTheory.ADD_CLAUSES] >>
  impl_tac
  >- (rpt strip_tac >> Cases_on `i = LENGTH done`
      >- (`SUC (LENGTH done + LENGTH rest) - (i + 1) = LENGTH rest` by decide_tac >>
          simp[]) >>
      `i < LENGTH done` by decide_tac >>
      `SUC (LENGTH done + LENGTH rest) - (i + 1) = LENGTH done + LENGTH rest - i` by decide_tac >>
      first_x_assum (qspec_then `i` mp_tac) >>
      simp[arithmeticTheory.ADD_CLAUSES]) >>
  disch_then strip_assume_tac >> rpt strip_tac >>
  `SUC (LENGTH done + LENGTH rest) - (i + 1) = LENGTH done + LENGTH rest - i` by decide_tac >>
  first_x_assum (qspec_then `i` mp_tac) >> simp[]
QED

Theorem alias_reorder_plan_large_materialised:
  16 < LENGTH pending /\ LENGTH pending <= LENGTH ps.ps_stack /\
  (!at. LIST_ELEM_COUNT at pending <= LIST_ELEM_COUNT at ps.ps_stack) /\
  reorder_plan dfg pending ps = (ops,qs) ==>
  LENGTH qs.ps_stack = LENGTH ps.ps_stack /\
  qs.ps_spilled = ps.ps_spilled /\
  (!at. LIST_ELEM_COUNT at qs.ps_stack = LIST_ELEM_COUNT at ps.ps_stack) /\
  qs.ps_stack = TAKE (LENGTH qs.ps_stack - LENGTH pending) qs.ps_stack ++ pending
Proof
  strip_tac >>
  `LENGTH qs.ps_stack = LENGTH ps.ps_stack /\
   qs.ps_spilled = ps.ps_spilled /\
   (!at. LIST_ELEM_COUNT at qs.ps_stack = LIST_ELEM_COUNT at ps.ps_stack) /\
   (!i. i < LENGTH pending ==>
     stack_peek (LENGTH pending - 1 - i) qs.ps_stack = EL i pending)` by
    (irule alias_plan_steps_large_materialised >> simp[] >>
     qexistsl_tac [`dfg`, `[]`, `ops`, `pending`] >>
     simp[GSYM reorder_plan_eq_plan_steps]) >>
  `qs.ps_stack = stack_pop (LENGTH pending) qs.ps_stack ++ pending` by
    (irule fixed_suffix_decompose >> simp[]) >>
  conj_tac >- simp[] >> conj_tac >- simp[] >> conj_tac >- simp[] >>
  qpat_x_assum `qs.ps_stack = stack_pop _ _ ++ _` mp_tac >>
  simp[stack_pop_def]
QED

Theorem alias_emit_reorder_consumed_window:
  emit_input_plan opc inputs nl ps = (iops,prepared) /\
  (!op. MEM op inputs /\ is_var_operand op ==>
    MEM op ps.ps_stack \/ op IN FDOM ps.ps_spilled) /\
  PERM inputs selected /\
  reorder_plan dfg selected prepared = (rops,arranged) ==>
  LENGTH selected <= LENGTH prepared.ps_stack /\
  arranged.ps_stack = stack_pop (LENGTH selected) arranged.ps_stack ++ selected
Proof
  `!xs : operand list. !ys.
     (!x. LIST_ELEM_COUNT x xs <= LIST_ELEM_COUNT x ys) ==>
     LENGTH xs <= LENGTH ys` by
    (Induct >> simp[] >> rpt gen_tac >> strip_tac >>
     `MEM h ys` by
       (simp[GSYM LIST_ELEM_COUNT_MEM] >>
        first_x_assum (qspec_then `h` mp_tac) >>
        simp[LIST_ELEM_COUNT_THM]) >>
     qpat_x_assum `MEM h ys` (strip_assume_tac o REWRITE_RULE [MEM_SPLIT]) >>
     gvs[] >>
     first_x_assum (qspec_then `l1 ++ l2` mp_tac) >>
     impl_tac >-
       (gen_tac >> first_x_assum (qspec_then `x` mp_tac) >>
        simp[elem_count_append, LIST_ELEM_COUNT_THM] >>
        Cases_on `h = x` >> simp[LIST_ELEM_COUNT_THM] ) >>
     simp[]) >>
  rpt strip_tac >>
  drule_all emit_input_plan_materialised >> strip_tac >>
  drule perm_operand_counts >> strip_tac >>
  `LENGTH selected = LENGTH inputs` by metis_tac[PERM_LENGTH] >>
  `!x. LIST_ELEM_COUNT x selected <= LIST_ELEM_COUNT x prepared.ps_stack` by
    metis_tac[] >>
  `LENGTH selected <= LENGTH prepared.ps_stack` by metis_tac[] >>
  Cases_on `LENGTH selected <= 16`
  >- (match_mp_tac fixed_suffix_decompose >> conj_tac
      >- (irule reorder_plan_materialised_length_floor >>
          simp[] >> qexistsl [`dfg`, `rops`, `prepared`] >> simp[]) >>
      rpt strip_tac >> irule reorder_plan_materialised_order >>
      simp[] >> qexistsl [`dfg`, `rops`, `prepared`] >> simp[]) >>
  `16 < LENGTH selected` by decide_tac >>
  drule_all alias_reorder_plan_large_materialised >> strip_tac >>
  qpat_x_assum `arranged.ps_stack = _` mp_tac >> simp[stack_pop_def]
QED


Theorem normalize_operand_non_assign_output:
  !fn inst x visited.
    ssa_form fn /\ MEM inst (fn_insts fn) /\ MEM x inst.inst_outputs /\
    inst.inst_opcode <> ASSIGN ==>
    normalize_operand (dfg_build_function fn) visited (Var x) = Var x
Proof
  rpt strip_tac >> Cases_on `MEM x visited` >> simp[Once normalize_operand_def] >>
  Cases_on `dfg_get_def (dfg_build_function fn) x` >>
  gvs[dfg_get_def_def] >>
  rename1 `FLOOKUP (dfg_build_function fn).dfg_defs x = SOME def` >>
  `dfg_get_def (dfg_build_function fn) x = SOME def` by simp[dfg_get_def_def] >>
  drule dfg_build_function_correct >> strip_tac >>
  `def = inst` by
    (irule ssa_unique_output >> conj_tac >- (qexists_tac `fn` >> simp[]) >>
     qexists_tac `x` >> simp[]) >>
  gvs[] >> simp[Once normalize_operand_def]
QED

(* Value-level copy boundary: neither operand needs a physical planner slot.
   Normalization transport and root noninterference are separate premises. *)
Theorem alias_assign_value_boundary:
  ssa_form fn /\ MEM inst (fn_insts fn) /\
  inst.inst_opcode = ASSIGN /\ inst.inst_operands = [src] /\
  inst.inst_outputs = [x] /\ step_inst fuel ctx inst s = OK s' /\
  (!l. FLOOKUP s.vs_labels l = OPTION_MAP n2w (FLOOKUP lo l)) /\
  normalize_operand dfg [] (Var x) = normalize_operand dfg [] src /\
  operand_val (frame_view fn ra s) lo src =
    operand_val (frame_view fn ra s) lo (normalize_operand dfg [] src) /\
  operand_val (frame_view fn ra s') lo (normalize_operand dfg [] src) =
    operand_val (frame_view fn ra s) lo (normalize_operand dfg [] src) ==>
  operand_val (frame_view fn ra s') lo (Var x) =
    operand_val (frame_view fn ra s') lo (normalize_operand dfg [] (Var x))
Proof
  strip_tac >>
  `step_inst_base inst s = OK s'` by
    (qpat_x_assum `step_inst fuel ctx inst s = OK s'` mp_tac >>
     simp[Once step_inst_def]) >>
  `?v. eval_operand src s = SOME v /\ s' = update_var x v s` by
    (qpat_x_assum `step_inst_base inst s = OK s'` mp_tac >>
     simp[Once step_inst_base_def, AllCaseEqs()] >> metis_tac[]) >>
  `MEM x inst.inst_outputs` by simp[] >>
  `eval_operand src (frame_view fn ra s) =
    SOME (if retpc_var fn x then ra else v)` by
    (drule_all assign_eval_frame_view >>
     disch_then (qspecl_then [`ra`, `s.vs_memory`] mp_tac) >>
     Cases_on `src` >>
     simp[frame_view_def, eval_operand_def, lookup_var_def]) >>
  `operand_val (frame_view fn ra s) lo src =
    SOME (if retpc_var fn x then ra else v)` by
    (Cases_on `src` >> gvs[operand_val_def, eval_operand_def,
      lookup_var_def, frame_view_def]) >>
  gvs[frame_view_update_var, operand_val_update_var_eq]
QED

Theorem alias_phi_output_value_boundary:
  ssa_form fn /\ MEM inst (fn_insts fn) /\
  inst.inst_opcode = PHI /\ MEM x inst.inst_outputs ==>
  operand_val (frame_view fn ra s) lo (Var x) =
    operand_val (frame_view fn ra s) lo
      (normalize_operand (dfg_build_function fn) [] (Var x))
Proof
  strip_tac >>
  `normalize_operand (dfg_build_function fn) [] (Var x) = Var x` by
    (irule normalize_operand_non_assign_output >> simp[] >>
     qexists_tac `inst` >> simp[]) >> simp[]
QED

Theorem alias_step_survivor_value:
  step_inst fuel ctx inst s = OK s' /\
  (!x. at = Var x ==> ~MEM x inst.inst_outputs) /\
  (!x. normalize_operand dfg [] at = Var x ==> ~MEM x inst.inst_outputs) /\
  operand_val (frame_view fn ra s) lo at =
    operand_val (frame_view fn ra s) lo (normalize_operand dfg [] at) ==>
  operand_val (frame_view fn ra s') lo at =
    operand_val (frame_view fn ra s') lo (normalize_operand dfg [] at)
Proof
  strip_tac >>
  `!x. ~MEM x inst.inst_outputs ==>
    FLOOKUP s'.vs_vars x = FLOOKUP s.vs_vars x` by
    (Cases_on `is_terminator inst.inst_opcode` >>
     metis_tac[step_preserves_non_output_vars, step_terminator_preserves_vars,
               lookup_var_def]) >>
  Cases_on `normalize_operand dfg [] at` >> Cases_on `at` >>
  gvs[operand_val_def, frame_view_vars_lookup]
QED

Theorem alias_phis_survivor_value:
  eval_phis s instructions = OK s' /\
  (!x inst. at = Var x /\ MEM inst instructions /\ inst.inst_opcode = PHI ==>
    ~MEM x inst.inst_outputs) /\
  (!x inst. normalize_operand dfg [] at = Var x /\
    MEM inst instructions /\ inst.inst_opcode = PHI ==> ~MEM x inst.inst_outputs) /\
  operand_val (frame_view fn ra s) lo at =
    operand_val (frame_view fn ra s) lo (normalize_operand dfg [] at) ==>
  operand_val (frame_view fn ra s') lo at =
    operand_val (frame_view fn ra s') lo (normalize_operand dfg [] at)
Proof
  strip_tac >>
  `!x. (!inst. MEM inst instructions /\ inst.inst_opcode = PHI ==>
    ~MEM x inst.inst_outputs) ==>
    FLOOKUP s'.vs_vars x = FLOOKUP s.vs_vars x` by
      metis_tac[eval_phis_flookup_not_phi_output] >>
  Cases_on `normalize_operand dfg [] at` >> Cases_on `at` >>
  gvs[operand_val_def, frame_view_vars_lookup] >> metis_tac[]
QED

(* Certificates describe actual state boundaries; existence is a separate static
   obligation. PHI transitions are atomic. No value equality is a constructor. *)
Inductive alias_certificate:
  (!fn dfg lo ps states n at.
    n < LENGTH states /\ normalize_operand dfg [] at = at ==>
    alias_certificate fn dfg lo ps states n at) /\
  (!fn dfg lo ps states at.
    0 < LENGTH states /\ (MEM at ps.ps_stack \/ at IN FDOM ps.ps_spilled) ==>
    alias_certificate fn dfg lo ps states 0 at) /\
  (!fn dfg lo ps states n at fuel ctx inst.
    alias_certificate fn dfg lo ps states n at /\ SUC n < LENGTH states /\
    step_inst fuel ctx inst (EL n states) = OK (EL (SUC n) states) /\
    (!x. at = Var x ==> ~MEM x inst.inst_outputs) /\
    (!x. normalize_operand dfg [] at = Var x ==> ~MEM x inst.inst_outputs) ==>
    alias_certificate fn dfg lo ps states (SUC n) at) /\
  (!fn dfg lo ps states n at instructions.
    alias_certificate fn dfg lo ps states n at /\ SUC n < LENGTH states /\
    eval_phis (EL n states) instructions = OK (EL (SUC n) states) /\
    (!x inst. at = Var x /\ MEM inst instructions /\ inst.inst_opcode = PHI ==>
      ~MEM x inst.inst_outputs) /\
    (!x inst. normalize_operand dfg [] at = Var x /\
      MEM inst instructions /\ inst.inst_opcode = PHI ==> ~MEM x inst.inst_outputs) ==>
    alias_certificate fn dfg lo ps states (SUC n) at) /\
  (!fn dfg lo ps states n src x fuel ctx inst.
    alias_certificate fn dfg lo ps states n src /\ SUC n < LENGTH states /\
    ssa_form fn /\ MEM inst (fn_insts fn) /\
    inst.inst_opcode = ASSIGN /\ inst.inst_operands = [src] /\
    inst.inst_outputs = [x] /\
    step_inst fuel ctx inst (EL n states) = OK (EL (SUC n) states) /\
    (!l. FLOOKUP (EL n states).vs_labels l = OPTION_MAP n2w (FLOOKUP lo l)) /\
    normalize_operand dfg [] (Var x) = normalize_operand dfg [] src /\
    (!y. normalize_operand dfg [] src = Var y ==> ~MEM y inst.inst_outputs) ==>
    alias_certificate fn dfg lo ps states (SUC n) (Var x)) /\
  (!fn dfg lo ps states n at i.
    alias_certificate fn dfg lo ps states n at /\ SUC n < LENGTH states /\
    EL (SUC n) states = (EL n states with vs_inst_idx := i) ==>
    alias_certificate fn dfg lo ps states (SUC n) at)
End

Theorem alias_certificate_admin_transport:
  alias_certificate fn dfg lo ps states n at /\ SUC n < LENGTH states /\
  EL (SUC n) states = (EL n states with vs_inst_idx := i) ==>
  alias_certificate fn dfg lo ps states (SUC n) at
Proof
  metis_tac[alias_certificate_rules]
QED

Theorem alias_certificate_sound:
  !fn dfg lo ps states n at.
    alias_certificate fn dfg lo ps states n at ==>
    !ra. (!op. MEM op ps.ps_stack \/ op IN FDOM ps.ps_spilled ==>
      operand_val (frame_view fn ra (EL 0 states)) lo op =
      operand_val (frame_view fn ra (EL 0 states)) lo (normalize_operand dfg [] op)) ==>
    operand_val (frame_view fn ra (EL n states)) lo at =
    operand_val (frame_view fn ra (EL n states)) lo (normalize_operand dfg [] at)
Proof
  ho_match_mp_tac alias_certificate_ind >> rpt strip_tac
  >- simp[]
  >- metis_tac[]
  >- metis_tac[]
  >- (irule alias_step_survivor_value >> metis_tac[])
  >- (irule alias_phis_survivor_value >> metis_tac[])
  >- (`!y. ~MEM y inst.inst_outputs ==>
        FLOOKUP (EL (SUC n) states).vs_vars y = FLOOKUP (EL n states).vs_vars y` by
      (Cases_on `is_terminator inst.inst_opcode` >>
       metis_tac[step_preserves_non_output_vars, step_terminator_preserves_vars,
                 lookup_var_def]) >>
  `operand_val (frame_view fn ra (EL (SUC n) states)) lo (normalize_operand dfg [] at) =
   operand_val (frame_view fn ra (EL n states)) lo (normalize_operand dfg [] at)` by
    (Cases_on `normalize_operand dfg [] at` >>
     gvs[operand_val_def, frame_view_vars_lookup] >> metis_tac[]) >>
  irule alias_assign_value_boundary >> metis_tac[]) >>
  first_x_assum (qspec_then `ra` mp_tac) >>
  (impl_tac >- metis_tac[]) >>
  Cases_on `normalize_operand dfg [] at` >> gvs[] >>
  Cases_on `at` >> gvs[operand_val_def, frame_view_def]
QED

Theorem alias_certificate_endpoint:
  EL 0 states = vs /\ EL n states = vs' /\
  (!at. MEM at qs.ps_stack \/ at IN FDOM qs.ps_spilled ==>
    alias_certificate fn dfg lo ps states n at) /\
  (!at. MEM at ps.ps_stack \/ at IN FDOM ps.ps_spilled ==>
    operand_val (frame_view fn ra vs) lo at =
    operand_val (frame_view fn ra vs) lo (normalize_operand dfg [] at)) ==>
  !at. MEM at qs.ps_stack \/ at IN FDOM qs.ps_spilled ==>
    operand_val (frame_view fn ra vs') lo at =
    operand_val (frame_view fn ra vs') lo (normalize_operand dfg [] at)
Proof
  metis_tac[alias_certificate_sound]
QED

(* Universal interface tests: a root write blocks the survival constructor,
   but a subsequent ASSIGN may repair the destination from a reflexive source,
   without needing any certificate for the destination at the preceding cut. *)
Theorem alias_certificate_root_write_blocks_survival:
  normalize_operand dfg [] at = Var x /\ MEM x inst.inst_outputs ==>
  ~(!y. normalize_operand dfg [] at = Var y ==> ~MEM y inst.inst_outputs)
Proof
  metis_tac[]
QED

Theorem alias_certificate_self_root_repair:
  SUC n < LENGTH states /\ ssa_form fn /\ MEM inst (fn_insts fn) /\
  inst.inst_opcode = ASSIGN /\ inst.inst_operands = [src] /\
  inst.inst_outputs = [x] /\
  step_inst fuel ctx inst (EL n states) = OK (EL (SUC n) states) /\
  (!l. FLOOKUP (EL n states).vs_labels l = OPTION_MAP n2w (FLOOKUP lo l)) /\
  normalize_operand dfg [] src = src /\ normalize_operand dfg [] (Var x) = src /\
  (!y. src = Var y ==> ~MEM y inst.inst_outputs) ==>
  alias_certificate fn dfg lo ps states (SUC n) (Var x)
Proof
  strip_tac >>
  `alias_certificate fn dfg lo ps states n src` by
    (irule (cj 1 alias_certificate_rules) >> simp[] >> decide_tac) >>
  irule (cj 5 alias_certificate_rules) >> metis_tac[]
QED

(* Certificate producer ledger:
   - Entry constructor needs actual stack/spill ownership at cut zero, not
     just liveness or selected-edge membership.
   - Reflexive constructor needs a checked normalization equation (non-ASSIGN
     outputs have normalize_operand_non_assign_output).
   - Each survivor needs exclusion of BOTH the operand and its root from the
     actual ordinary outputs or the entire atomic PHI batch.
   - ASSIGN needs a source certificate at the preceding cut, actual execution,
     labels, SSA/membership, normalization transport and syntactic root stability.
   - Administrative cuts change only vs_inst_idx, covering PHI-prefix resets
     and ordinary-step increments. The observation fact already exists as
     fnBlockStepHelpers$operand_val_frame_view_inst_idx; the soundness case
     computes this boundary directly to avoid that higher-level dependency.
   The states list fixes common cut identities; execution facts are supplied by
   constructors, not inferred from list indices. No assertion here produces
   these certificates from run_block, planner heldness, or lineage. In particular
   loop root writes require deletion or later repair, not SSA alone. *)

(* Pointwise demand interface ledger (C1.21.2.3).
   Both survivor boundaries quantify over arbitrary operands and arbitrary dfg;
   neither assumes liveness nor physical ownership, so dead retained names are
   covered too. Label operands use lo, not vs_labels: no label preservation
   premise is needed for these survivor statements. Terminator and ordinary
   execution cases are both discharged by their exported preservation lemmas.

   Consumers still need STATIC producers, not additional transport lemmas:
   - New ASSIGN output: alias_assign_value_boundary consumes actual source
     equality, normalization transport and root-read stability, plus SSA,
     membership and the runtime label-map premise. None follows from mere
     successful planning or an absent physical source.
   - Other outputs: normalize_operand_non_assign_output gives reflexive
     equality; alias_phi_output_value_boundary already specializes this to PHI.
   - PHI survivors: alias_phis_survivor_value excludes both the demanded name
     and its variable root from ALL physical PHI outputs in the batch. These
     exclusions still need production under the target assumptions.
   - Ordinary survivors: alias_step_survivor_value requires the two output
     exclusions. This includes dead retained aliases; the earlier live-only
     root exclusion is not a producer for that case.
   - Backward traces still need initial equality coverage and final-held demand
     inclusion from actual lineage. Neither prev=NONE nor static JMP planning
     establishes runtime predecessor agreement or missing initial equality.
*)

(* Semantic-prefix interface probe (C1.20.1).

   Candidate ordinary-prefix assertion, written here rather than installed as a
   new global predicate until its entry producer has been validated:

     !x. MEM x (live_vars_at (liveness_analyze fn) bb.bb_label i) ==>
       operand_val (frame_view fn ra s) lo (Var x) =
       operand_val (frame_view fn ra s) lo
         (normalize_operand (dfg_build_function fn) [] (Var x)).

   The index is the NEXT instruction, s.vs_inst_idx = i. The initial state is
   s_phi with vs_inst_idx := phi_prefix_length bb.bb_instructions, where
   eval_phis entry bb.bb_instructions = OK s_phi. The actual recursion is
   exec_block (not block_step): at a nonterminator it calls itself on
   s' with vs_inst_idx := SUC i after step_inst fuel ctx inst s = OK s'.
   Induct on LENGTH bb.bb_instructions - i, keeping fuel fixed. Terminators
   stop recursion. Require lookup_block bb.bb_label fn.fn_blocks = SOME bb,
   fn_reachable fn bb.bb_label, wf_function fn, ssa_form fn and
   def_dominates_uses fn throughout. This is a proposal, NOT a proved theorem
   or a claim that the frozen target already supplies its base case.

   Premise ledger:

   * Entry: the frozen ownership and equality premises supply equality only
     for input_vars_from pred instructions (live_vars_at ... label 0), when
     entry.vs_prev_bb = SOME pred. To initialize the assertion after PHIs,
     each live non-PHI output x needs entry equality of x AND preservation
     of its normalized root through the entire PHI batch. The necessary
     implication from this entry demand to input_vars_from is UNVALIDATED:
     input_vars_from uses op_map over all PHI sources and a placed-index
     deduplication; it is not simply union of the selected sources and the
     ordinary survivors. Source collisions must be checked, not assumed away.

   * Parallel PHIs: a PHI output is a self root by
     alias_phi_output_value_boundary, independent of its selected value or
     physical location. A survivor x instead needs both x and any variable
     root r excluded from PHI outputs. eval_phis_flookup_not_phi_output and
     eval_phis_only_updates_vs_vars then preserve the two framed reads;
     literal/label roots need only unchanged labels. Producing the root
     exclusion from SSA/dominance at this batch boundary is UNVALIDATED.
     eval_phis reads EVERY source in entry, not in partially updated states.

   * Skipped physical PHI: E0072 already supplies this case. Runtime PHI
     equality is reflexive at its self root even if planning skips it. A
     later ASSIGN consumes semantic source equality, not source heldness,
     through alias_assign_value_boundary above. No new fixture is needed.

   * Ordinary survivor: backward live transfer supplies liveness at i if x
     is live at SUC i and is not an output. The proved
     alias_live_after_root_not_defined excludes its variable root from this
     instruction's definitions. step_preserves_non_output_vars (for
     nonterminators) and step_terminator_preserves_vars preserve reads.
     step_inst_preserves_labels_always preserves label-root reads.

   * New ASSIGN output: alias_assign_value_boundary separates source equality,
     normalization transport, and root-value preservation. Source liveness
     at i supplies the first from the prefix assertion. For a variable source,
     alias_live_root_not_defined supplies root exclusion at i. Literal and
     label sources use their immediate reads and unchanged labels. Transport
     across normalize_operand's visited list needs an acyclicity/rank result:
     normalize_operand_codegen_assign in fnFrameStepsRevertForward provides
     precisely this interface under codegen_ready_fn, but importing that
     theory (or relocating its rank infrastructure) is NOT validated here.
     Do not replace the cycle obligation with a syntactic one-step rewrite.

   * Other new outputs: normalize_operand_non_assign_output is reflexive;
     no semantic source equality is required. INVOKE belongs here, but old
     survivors still require step_preserves_non_output_vars, whose step_inst
     statement includes INVOKE, rather than an assumption that callee execution
     preserves the caller environment without merge_callee_state/bind_outputs.

   * Frame/retpc: perform the proof on operand_val (frame_view ...), never
     silently substitute raw vs_vars equality for framed equality. The checked
     ASSIGN boundary uses assign_eval_frame_view and frame_view_update_var,
     including the retpc-dependent destination value; labels use the frozen
     label-map premise, propagated by step_inst_preserves_labels_always.

   * prev = NONE: successful eval_phis forces an empty PHI prefix (otherwise
     eval_one_phi fails). It DOES NOT supply ordinary live-input equality:
     the frozen selected-input premise is vacuous. A separate lineage/entry
     argument or a weaker backward-demand interface is needed for this base
     case. This gap is not a counterexample to lineage_alias_successor.

   Even a proved live-prefix assertion would not cover final retained dead
   aliases: those remain the separate retained-name obligation in the PLAN.
*)

(* Actual single steps followed by normalize_operand, including literal roots. *)
Definition alias_assign_step_def:
  alias_assign_step dfg at src <=>
    ?v inst. at = Var v /\ FLOOKUP dfg.dfg_defs v = SOME inst /\
      inst.inst_opcode = ASSIGN /\ inst.inst_operands = [src]
End

Theorem alias_assign_source_available:
  wf_function fn /\ ssa_form fn /\ def_dominates_uses fn /\
  alias_assign_step (dfg_build_function fn) (Var x) (Var y) /\
  alias_path_available fn l i x ==>
  alias_path_available fn l i y
Proof
  strip_tac >>
  `?assign. dfg_get_def (dfg_build_function fn) x = SOME assign /\
      assign.inst_opcode = ASSIGN /\ assign.inst_operands = [Var y]` by
    gvs[alias_assign_step_def, dfg_get_def_def] >>
  drule dfg_build_function_correct >> strip_tac >>
  `!bb j. MEM bb fn.fn_blocks /\ j < LENGTH bb.bb_instructions /\
       MEM x (inst_defs (EL j bb.bb_instructions)) ==>
       alias_path_available fn bb.bb_label j y` by
    (rpt strip_tac >>
     `EL j bb.bb_instructions = assign` by
       (irule ssa_unique_output >> conj_tac
        >- (qexists_tac `fn` >>
            gvs[fn_insts_def, MEM_fn_insts_blocks_iff] >> metis_tac[EL_MEM]) >>
        qexists_tac `x` >> gvs[inst_defs_def]) >>
     irule alias_ordinary_use_available >>
     simp[inst_uses_def, operand_vars_def, operand_var_def]) >>
  rewrite_tac[alias_path_available_def] >> rpt strip_tac >>
  qpat_x_assum `alias_path_available fn l i x` mp_tac >>
  rewrite_tac[alias_path_available_def] >>
  disch_then (qspec_then `path` mp_tac) >>
  impl_tac >- simp[] >> strip_tac
  >- (`?j. j < LENGTH bb.bb_instructions /\
           EL j bb.bb_instructions = inst` by metis_tac[MEM_EL] >>
      `alias_path_available fn bb.bb_label j y` by
        metis_tac[lookup_block_MEM] >>
      `!p n. is_fn_path fn p ==> is_fn_path fn (TAKE n p)` by
        (Induct >- simp[is_fn_path_def] >>
         qx_gen_tac `head` >> Cases >- simp[is_fn_path_def] >>
         Cases_on `p` >> simp[is_fn_path_def] >>
         Cases_on `n'` >> simp[is_fn_path_def] >> strip_tac >>
         qpat_x_assum `!n. is_fn_path fn (h::t) ==> _`
           (qspec_then `SUC n` mp_tac) >> simp[]) >>
      qpat_x_assum `alias_path_available fn bb.bb_label j y` mp_tac >>
      rewrite_tac[alias_path_available_def] >>
      disch_then (qspec_then `TAKE (SUC k) path` mp_tac) >>
      impl_tac >- (simp[LENGTH_TAKE, HD_TAKE, LAST_EL, EL_TAKE] >>
                    metis_tac[lookup_block_label]) >>
      simp[LENGTH_TAKE, EL_TAKE] >> strip_tac >> disj1_tac
      >- (gvs[EL_TAKE] >> qexistsl_tac [`k'`,`bb'`,`inst'`] >> simp[] >> decide_tac) >>
      `bb.bb_label = EL k path` by metis_tac[lookup_block_label] >>
      gvs[] >> qexistsl_tac [`k`,`bb`,`EL j' bb.bb_instructions`] >>
      simp[EL_MEM]) >>
  `alias_path_available fn bb.bb_label j y` by
    metis_tac[lookup_block_MEM] >>
  qpat_x_assum `alias_path_available fn bb.bb_label j y` mp_tac >>
  rewrite_tac[alias_path_available_def] >>
  disch_then (qspec_then `path` mp_tac) >>
  impl_tac >- metis_tac[lookup_block_label] >>
  strip_tac >- metis_tac[] >>
  `bb.bb_label = l` by metis_tac[lookup_block_label] >> gvs[] >>
  disj2_tac >> qexists_tac `j'` >> simp[]
QED

Theorem normalize_operand_closed_visited_cong:
  !dfg visited at P other.
    P at /\
    (!a b. P a /\ alias_assign_step dfg a b ==> P b) /\
    (!v. P (Var v) ==> (MEM v visited <=> MEM v other)) ==>
    normalize_operand dfg visited at = normalize_operand dfg other at
Proof
  recInduct normalize_operand_ind >> rpt strip_tac
  >- (Cases_on `MEM v visited` >>
      `MEM v visited <=> MEM v other` by metis_tac[] >>
      CONV_TAC (BINOP_CONV (ONCE_REWRITE_CONV [normalize_operand_def])) >>
      gvs[] >>
      Cases_on `FLOOKUP dfg.dfg_defs v` >> gvs[] >>
      rename1 `FLOOKUP dfg.dfg_defs v = SOME inst` >>
      Cases_on `inst.inst_opcode = ASSIGN` >> simp[] >>
      Cases_on `inst.inst_operands` >> simp[] >>
      rename1 `inst.inst_operands = src::rest` >>
      Cases_on `rest` >> simp[] >>
      `alias_assign_step dfg (Var v) src` by
        (simp[alias_assign_step_def] >> metis_tac[]) >>
      `P src` by metis_tac[] >>
      first_x_assum irule >> simp[] >>
      qexists_tac `P` >> simp[] >> metis_tac[]) >>
  CONV_TAC (BINOP_CONV (ONCE_REWRITE_CONV [normalize_operand_def])) >> simp[]
QED

Theorem normalize_operand_assign_chain:
  !dfg visited at.
    normalize_operand dfg visited at <> at ==>
    TC (alias_assign_step dfg) at (normalize_operand dfg visited at)
Proof
  recInduct normalize_operand_ind >>
  rpt strip_tac >>
  gvs[Once normalize_operand_def, AllCaseEqs()] >>
  Cases_on `FLOOKUP dfg.dfg_defs v` >> gvs[] >>
  rename1 `FLOOKUP dfg.dfg_defs v = SOME inst` >>
  Cases_on `inst.inst_operands` >> gvs[] >>
  rename1 `inst.inst_operands = src::rest` >>
  Cases_on `rest` >> gvs[] >>
  gvs[Once normalize_operand_def] >>
  `alias_assign_step dfg (Var v) src` by
    (simp[alias_assign_step_def] >> metis_tac[]) >>
  Cases_on `normalize_operand dfg (v::visited) src = src`
  >- metis_tac[relationTheory.TC_SUBSET] >>
  metis_tac[relationTheory.TC_RULES]
QED

Theorem alias_normalize_available:
  !dfg visited at.
    dfg = dfg_build_function fn /\ wf_function fn /\ ssa_form fn /\
    def_dominates_uses fn /\
    (!v. at = Var v ==> alias_path_available fn l i v) /\
    normalize_operand dfg visited at = Var r ==>
    alias_path_available fn l i r
Proof
  recInduct normalize_operand_ind >> rpt strip_tac >>
  gvs[Once normalize_operand_def, AllCaseEqs()] >>
  first_x_assum irule >> rpt strip_tac >> gvs[] >>
  irule alias_assign_source_available >>
  simp[alias_assign_step_def] >> metis_tac[]
QED

Theorem alias_path_available_index_mono:
  alias_path_available fn l i x /\ i <= j ==>
  alias_path_available fn l j x
Proof
  simp[alias_path_available_def] >> rpt strip_tac >>
  first_x_assum drule >> simp[] >> strip_tac
  >- metis_tac[] >>
  disj2_tac >> qexistsl_tac [`bb`, `j'`] >> simp[] >> decide_tac
QED

Theorem alias_available_suffix_not_output:
  wf_function fn /\ ssa_form fn /\ fn_reachable fn l /\
  lookup_block l fn.fn_blocks = SOME bb /\
  alias_path_available fn l i x /\ i <= j /\
  j < LENGTH bb.bb_instructions ==>
  ~MEM x (EL j bb.bb_instructions).inst_outputs
Proof
  strip_tac >>
  `alias_path_available fn l j x` by
    metis_tac[alias_path_available_index_mono] >>
  metis_tac[alias_definition_not_available, inst_defs_def]
QED

Theorem alias_local_assign_normalize:
  wf_function fn /\ ssa_form fn /\ def_dominates_uses fn /\
  fn_reachable fn lbl /\ lookup_block lbl fn.fn_blocks = SOME bb /\
  i < LENGTH bb.bb_instructions /\
  (EL i bb.bb_instructions).inst_opcode = ASSIGN /\
  (EL i bb.bb_instructions).inst_outputs = [x] /\
  (EL i bb.bb_instructions).inst_operands = [op] ==>
  normalize_operand (dfg_build_function fn) [] (Var x) =
  normalize_operand (dfg_build_function fn) [] op
Proof
  strip_tac >>
  `MEM (EL i bb.bb_instructions) (fn_insts fn)` by
    (simp[fn_insts_def, MEM_fn_insts_blocks_iff] >>
     qexists_tac `bb` >> simp[EL_MEM] >> metis_tac[lookup_block_MEM]) >>
  `MEM x (EL i bb.bb_instructions).inst_outputs` by simp[] >>
  `dfg_get_def (dfg_build_function fn) x = SOME (EL i bb.bb_instructions)` by
    (drule_all dfg_build_function_defs_complete >> strip_tac >>
     drule dfg_build_function_correct >> strip_tac >>
     `inst' = EL i bb.bb_instructions` by
       (irule ssa_unique_output >> metis_tac[]) >> gvs[]) >>
  `~alias_path_available fn lbl i x` by
    (strip_tac >>
     `i <= i` by simp[] >>
     metis_tac[alias_available_suffix_not_output]) >>
  CONV_TAC (LAND_CONV (ONCE_REWRITE_CONV [normalize_operand_def])) >>
  gvs[dfg_get_def_def] >>
  irule normalize_operand_closed_visited_cong >>
  qexists_tac `\a. !v. a = Var v ==> alias_path_available fn lbl i v` >>
  simp[] >> conj_tac
  >- (rpt strip_tac >>
      `lbl = bb.bb_label` by metis_tac[lookup_block_label] >> gvs[] >>
      irule alias_ordinary_use_available >>
      simp[inst_uses_def, operand_vars_def, operand_var_def] >>
      metis_tac[lookup_block_MEM]) >>
  rpt strip_tac >> gvs[] >>
  Cases_on `a` >> gvs[alias_assign_step_def] >>
  irule alias_assign_source_available >>
  simp[alias_assign_step_def] >> metis_tac[]
QED

Theorem alias_available_root_suffix_not_output:
  wf_function fn /\ ssa_form fn /\ def_dominates_uses fn /\
  fn_reachable fn l /\ lookup_block l fn.fn_blocks = SOME bb /\
  (!x. at = Var x ==> alias_path_available fn l i x) /\
  normalize_operand (dfg_build_function fn) [] at = Var r /\
  i <= j /\ j < LENGTH bb.bb_instructions ==>
  ~MEM r (EL j bb.bb_instructions).inst_outputs
Proof
  strip_tac >>
  `alias_path_available fn l i r` by
    (irule alias_normalize_available >> simp[] >> metis_tac[]) >>
  metis_tac[alias_available_suffix_not_output]
QED

Theorem alias_ordinary_use_root_suffix_not_output:
  wf_function fn /\ ssa_form fn /\ def_dominates_uses fn /\
  fn_reachable fn lbl /\ lookup_block lbl fn.fn_blocks = SOME bb /\
  i < LENGTH bb.bb_instructions /\
  (EL i bb.bb_instructions).inst_opcode <> PHI /\
  (!v. at = Var v ==> MEM v (inst_uses (EL i bb.bb_instructions))) /\
  normalize_operand (dfg_build_function fn) [] at = Var r /\
  i <= j /\ j < LENGTH bb.bb_instructions ==>
  ~MEM r (EL j bb.bb_instructions).inst_outputs
Proof
  strip_tac >>
  `MEM bb fn.fn_blocks /\ bb.bb_label = lbl` by
    metis_tac[lookup_block_MEM, lookup_block_label] >>
  `!v. at = Var v ==> alias_path_available fn lbl i v` by
    (rpt strip_tac >>
     `MEM v (inst_uses (EL i bb.bb_instructions))` by metis_tac[] >>
     drule_all alias_ordinary_use_available >> simp[]) >>
  irule alias_available_root_suffix_not_output >>
  goal_assum (drule_at Any) >> simp[] >> metis_tac[]
QED

Theorem alias_assign_source_root_suffix_not_output:
  wf_function fn /\ ssa_form fn /\ def_dominates_uses fn /\
  fn_reachable fn lbl /\ lookup_block lbl fn.fn_blocks = SOME bb /\
  i < LENGTH bb.bb_instructions /\
  (EL i bb.bb_instructions).inst_opcode = ASSIGN /\
  (EL i bb.bb_instructions).inst_operands = [at] /\
  normalize_operand (dfg_build_function fn) [] at = Var r /\
  i <= j /\ j < LENGTH bb.bb_instructions ==>
  ~MEM r (EL j bb.bb_instructions).inst_outputs
Proof
  strip_tac >> irule alias_ordinary_use_root_suffix_not_output >>
  goal_assum (drule_at Any) >> simp[] >>
  qexistsl_tac [`at`, `fn`, `i`, `lbl`] >>
  simp[inst_uses_def, operand_vars_def] >>
  rpt strip_tac >> gvs[operand_vars_def, operand_var_def]
QED

Theorem alias_available_entry_not_output:
  wf_function fn /\ ssa_form fn /\ fn_reachable fn l /\
  lookup_block l fn.fn_blocks = SOME bb /\
  alias_path_available fn l 0 x /\ MEM inst bb.bb_instructions ==>
  ~MEM x inst.inst_outputs
Proof
  strip_tac >>
  `?j. j < LENGTH bb.bb_instructions /\ inst = EL j bb.bb_instructions` by
    metis_tac[MEM_EL] >>
  gvs[] >> irule alias_available_suffix_not_output >> simp[] >>
  qexistsl_tac [`fn`, `0`, `l`] >> simp[]
QED

Theorem alias_available_root_entry_not_output:
  wf_function fn /\ ssa_form fn /\ def_dominates_uses fn /\
  fn_reachable fn l /\ lookup_block l fn.fn_blocks = SOME bb /\
  (!x. at = Var x ==> alias_path_available fn l 0 x) /\
  normalize_operand (dfg_build_function fn) [] at = Var r /\
  MEM inst bb.bb_instructions ==>
  ~MEM r inst.inst_outputs
Proof
  strip_tac >>
  `alias_path_available fn l 0 r` by
    (irule alias_normalize_available >> simp[] >> metis_tac[]) >>
  metis_tac[alias_available_entry_not_output]
QED

Theorem alias_live_root_not_defined:
  wf_function fn /\ ssa_form fn /\ def_dominates_uses fn /\
  fn_reachable fn l /\ lookup_block l fn.fn_blocks = SOME bb /\
  i < LENGTH bb.bb_instructions /\
  LENGTH (collect_phis bb.bb_instructions) <= i /\
  MEM x (live_vars_at (liveness_analyze fn) l i) /\
  normalize_operand (dfg_build_function fn) [] (Var x) = Var r ==>
  ~MEM r (inst_defs (EL i bb.bb_instructions))
Proof
  strip_tac >>
  `alias_path_available fn l i x` by
    metis_tac[alias_live_available_after_phis] >>
  `alias_path_available fn l i r` by
    (irule alias_normalize_available >> simp[] >>
     qexistsl_tac [`Var x`,`[]`] >> simp[]) >>
  metis_tac[alias_definition_not_available]
QED

Theorem alias_live_after_root_not_defined:
  wf_function fn /\ ssa_form fn /\ def_dominates_uses fn /\
  fn_reachable fn l /\ lookup_block l fn.fn_blocks = SOME bb /\
  i < LENGTH bb.bb_instructions /\
  LENGTH (collect_phis bb.bb_instructions) <= SUC i /\
  MEM x (live_vars_at (liveness_analyze fn) l (SUC i)) /\
  ~MEM x (inst_defs (EL i bb.bb_instructions)) /\
  normalize_operand (dfg_build_function fn) [] (Var x) = Var r ==>
  ~MEM r (inst_defs (EL i bb.bb_instructions))
Proof
  strip_tac >>
  `alias_path_available fn l (SUC i) x` by
    metis_tac[alias_live_available_after_phis] >>
  `alias_path_available fn l i x` by
    metis_tac[alias_available_nondef_backward] >>
  `alias_path_available fn l i r` by
    (irule alias_normalize_available >> simp[] >>
     qexistsl_tac [`Var x`,`[]`] >> simp[]) >>
  metis_tac[alias_definition_not_available]
QED

(* Inventory boundaries do not depend on cleanup metadata or allocator fields. *)
Theorem alias_stack_find_singleton:
  !xs p v. FILTER p xs = [v] ==>
    ?d. stack_find p xs = SOME d /\ d < LENGTH xs /\ EL d xs = v /\
        (!j. j < LENGTH xs /\ p (EL j xs) ==> j = d)
Proof
  Induct >> simp[stack_find_def] >> rpt gen_tac >>
  Cases_on `p h` >> simp[stack_find_def]
  >- (strip_tac >> gvs[] >>
      rpt strip_tac >> Cases_on `j` >> gvs[] >>
      gvs[FILTER_EQ_NIL, EVERY_EL]) >>
  strip_tac >> first_x_assum drule >> strip_tac >>
  qexists_tac `SUC d` >> simp[arithmeticTheory.ADD1, EL_CONS] >>
  rpt strip_tac >> Cases_on `j` >> gvs[] >> metis_tac[]
QED

Theorem alias_phi_singleton_poke:
  FILTER (\at. MEM at inputs) stk = [v] /\ ~MEM ret inputs ==>
  ?d. stack_get_phi_depth inputs stk = SOME d /\
      stack_peek d stk = v /\
      (!at. MEM at inputs ==> ~MEM at (stack_poke d ret stk))
Proof
  strip_tac >>
  `FILTER (\at. MEM at inputs) (REVERSE stk) = [v]` by
    simp[FILTER_REVERSE] >>
  drule alias_stack_find_singleton >> strip_tac >>
  qexists_tac `d` >> simp[stack_get_phi_depth_def] >> conj_tac
  >- (gvs[LENGTH_REVERSE] >>
      qspecl_then [`d`,`stk`] mp_tac EL_REVERSE >> simp[stack_peek_def, arithmeticTheory.PRE_SUB1]) >>
  rpt strip_tac >>
  `?j. j < LENGTH (stack_poke d ret stk) /\
       EL j (stack_poke d ret stk) = at` by metis_tac[MEM_EL] >>
  gvs[stack_poke_def, LENGTH_LUPDATE, EL_LUPDATE] >>
  Cases_on `j = LENGTH stk - 1 - d` >> gvs[] >>
  `LENGTH stk - 1 - j = d` by
    (first_x_assum irule >>
     simp[EL_REVERSE, GSYM arithmeticTheory.ADD1]) >>
  decide_tac
QED

Definition plan_holds_def:
  plan_holds ps at <=> MEM at ps.ps_stack \/ at IN FDOM ps.ps_spilled
End

Theorem do_spill_tos_plan_holds:
  do_spill_tos ps = (ops,ps') /\ plan_holds ps at ==>
  plan_holds ps' at
Proof
  simp[do_spill_tos_def] >> pairarg_tac >> gvs[] >>
  qspec_then `ps.ps_stack` strip_assume_tac SNOC_CASES >>
  gvs[plan_holds_def, stack_pop_def, stack_peek_def,
      LENGTH_SNOC, TAKE_SNOC, EL_SNOC, EL_LENGTH_SNOC, MEM_SNOC] >>
  rpt strip_tac >> gvs[]
QED

Theorem stack_swap_mem_iff:
  dist < LENGTH (stk : operand list) ==>
  (MEM at (stack_swap dist stk) <=> MEM at stk)
Proof
  strip_tac >>
  `0 < LENGTH stk` by decide_tac >>
  qspecl_then [`stk`, `0`, `dist`, `at`] mp_tac
    doSwapSimTheory.stack_poke_exchange_multiplicity >>
  simp[stack_poke_def, stack_peek_def, stack_swap_def,
       GSYM LIST_ELEM_COUNT_MEM]
QED

Theorem stack_swap_mem_unbounded:
  MEM at (stk : operand list) ==> MEM at (stack_swap dist stk)
Proof
  strip_tac >>
  `0 < LENGTH stk` by (Cases_on `stk` >> gvs[]) >>
  `MIN dist (LENGTH stk - 1) < LENGTH stk` by simp[arithmeticTheory.MIN_DEF] >>
  `stack_swap dist stk = stack_swap (MIN dist (LENGTH stk - 1)) stk` by
    (simp[stack_swap_def, arithmeticTheory.MIN_DEF] >> IF_CASES_TAC >> simp[] >>
     `LENGTH stk - (dist + 1) = 0` by decide_tac >> simp[]) >>
  metis_tac[stack_swap_mem_iff]
QED

Theorem swap_desired_index_mem:
  2 <= chunk /\ j < chunk ==>
  MEM j ([chunk - 1] ++ GENLIST (\i. i + 1) (chunk - 2) ++ [0])
Proof
  strip_tac >> simp[MEM_GENLIST] >>
  Cases_on `j = 0` >- simp[] >>
  Cases_on `j = chunk - 1` >- simp[] >>
  gvs[] >> qexists_tac `j - 1` >> decide_tac
QED

Theorem top_n_stack_decomposition:
  TAKE (LENGTH stk - n) stk ++ top_n n stk = stk
Proof
  Cases_on `n <= LENGTH stk`
  >- (simp[top_n_def, GSYM LASTN_def] >>
      metis_tac[BUTLASTN_TAKE, APPEND_BUTLASTN_LASTN]) >>
  simp[top_n_def, TAKE_LENGTH_TOO_LONG]
QED

Theorem swap_desired_values_mem:
  2 <= chunk /\ LENGTH items <= chunk /\ MEM at items ==>
  MEM at (MAP (\idx. EL idx items)
    ([chunk - 1] ++ GENLIST (\i. i + 1) (chunk - 2) ++ [0]))
Proof
  strip_tac >>
  qpat_x_assum `MEM at items` (strip_assume_tac o REWRITE_RULE [MEM_EL]) >>
  pure_rewrite_tac[MEM_MAP] >> qexists_tac `n` >>
  conj_tac >- simp[] >> irule swap_desired_index_mem >> decide_tac
QED

Theorem do_swap_plan_holds:
  do_swap dist ps = (ops,ps') /\ plan_holds ps at ==> plan_holds ps' at
Proof
  Cases_on `dist = 0`
  >- (simp[do_swap_def] >> strip_tac >> gvs[]) >>
  Cases_on `dist <= 16`
  >- (simp[do_swap_def] >> strip_tac >> gvs[plan_holds_def] >>
      metis_tac[stack_swap_mem_unbounded]) >>
  simp[do_swap_def] >> pairarg_tac >> simp[] >> strip_tac >> gvs[] >>
  gvs[plan_holds_def] >>
  `MEM at (TAKE (LENGTH ps.ps_stack - (dist + 1)) ps.ps_stack) \/
   MEM at (top_n (dist + 1) ps.ps_stack)` by
    metis_tac[top_n_stack_decomposition, MEM_APPEND] >>
  simp[] >>
  `MEM at (MAP (\idx. EL idx (top_n (dist + 1) ps.ps_stack))
     ([dist] ++ GENLIST (\i. i + 1) (dist - 1) ++ [0]))` by
    (drule_at (Pat `MEM _ _`) swap_desired_values_mem >>
     disch_then (qspec_then `dist + 1` mp_tac) >>
     simp[top_n_def, LENGTH_TAKE_EQ]) >>
  gvs[]
QED

Theorem do_spill_at_plan_holds:
  dist < LENGTH ps.ps_stack /\ do_spill_at dist ps = (ops,ps') /\
  plan_holds ps at ==> plan_holds ps' at
Proof
  Cases_on `dist = 0`
  >- (simp[do_spill_at_def] >> metis_tac[do_spill_tos_plan_holds]) >>
  simp[do_spill_at_def] >> pairarg_tac >> simp[] >> strip_tac >> gvs[] >>
  `plan_holds (ps with ps_stack := stack_swap dist ps.ps_stack) at` by
    gvs[plan_holds_def, stack_swap_mem_iff] >>
  drule_all do_spill_tos_plan_holds >> simp[]
QED

Theorem do_restore_plan_holds:
  do_restore op ps = (ops,ps') /\ plan_holds ps at ==>
  plan_holds ps' at
Proof
  Cases_on `FLOOKUP ps.ps_spilled op` >>
  simp[do_restore_def, plan_holds_def, stack_push_def] >>
  rpt strip_tac >> gvs[MEM_SNOC]
QED

Theorem restore_spilled_plan_holds:
  !pending ps ops ps' at.
    restore_spilled_plan pending ps = (ops,ps') /\ plan_holds ps at ==>
    plan_holds ps' at
Proof
  Induct >> simp[restore_spilled_plan_def] >>
  rpt gen_tac >> pairarg_tac >> gvs[] >>
  Cases_on `restore_spilled_plan pending ps1` >> simp[] >>
  strip_tac >> gvs[] >>
  drule_all do_restore_plan_holds >> strip_tac >>
  first_x_assum (qspec_then `ps1` mp_tac) >>
  disch_then irule >> simp[]
QED

Theorem reduce_depth_plan_holds:
  !fuel target_ops target_op f target_len ps ops ps' at.
    reduce_depth_plan fuel target_ops target_op f target_len ps = (ops,ps') /\
    plan_holds ps at ==> plan_holds ps' at
Proof
  Induct >> simp[reduce_depth_plan_def] >> rpt gen_tac >>
  Cases_on `f + 1 < target_len` >> simp[]
  >- (strip_tac >> gvs[]) >>
  Cases_on `stack_get_unfixed_depth target_op f target_len ps.ps_stack` >> simp[]
  >- (strip_tac >> gvs[]) >>
  rename1 `stack_get_unfixed_depth _ _ _ _ = SOME dist` >>
  Cases_on `dist <= 16` >> simp[]
  >- (strip_tac >> gvs[]) >>
  Cases_on `select_spill_candidate ps.ps_stack target_ops dist target_len` >> simp[]
  >- (strip_tac >> gvs[]) >>
  rename1 `select_spill_candidate _ _ _ _ = SOME cand` >>
  Cases_on `do_spill_at cand ps` >> simp[] >>
  rename1 `do_spill_at _ _ = (sops,ps1)` >>
  Cases_on `reduce_depth_plan fuel target_ops target_op f target_len ps1` >>
  simp[] >> strip_tac >> gvs[] >>
  `1 <= LENGTH ps.ps_stack` by
    (drule stack_get_unfixed_depth_bound >> simp[]) >>
  `cand < LENGTH ps.ps_stack` by
    metis_tac[planWfTheory.select_spill_candidate_bound] >>
  drule_all do_spill_at_plan_holds >> strip_tac >>
  first_x_assum (qspecl_then [`target_ops`, `target_op`, `f`, `target_len`, `ps1`]
    mp_tac) >> simp[]
QED

Theorem stack_poke_exchange_mem:
  d < LENGTH (stk : operand list) /\ e < LENGTH stk ==>
  (MEM at (stack_poke e (stack_peek d stk)
    (stack_poke d (stack_peek e stk) stk)) <=> MEM at stk)
Proof
  strip_tac >>
  qspecl_then [`stk`, `d`, `e`, `at`] mp_tac
    doSwapSimTheory.stack_poke_exchange_multiplicity >>
  simp[GSYM LIST_ELEM_COUNT_MEM]
QED

Theorem reorder_one_plan_holds:
  reorder_one dfg pending idx op ps = (ops,ps') /\ plan_holds ps at ==>
  plan_holds ps' at
Proof
  simp[reorder_one_def] >> pairarg_tac >>
  `plan_holds ps at ==> plan_holds ps1 at` by
    (qpat_x_assum `_ = (restore_ops,ps1)` mp_tac >>
     Cases_on `stack_get_unfixed_depth op (LENGTH pending - (idx + 1))
       (LENGTH pending) ps.ps_stack` >> simp[]
     >- (Cases_on `FLOOKUP ps.ps_spilled op` >> simp[] >>
         metis_tac[do_restore_plan_holds]) >>
     strip_tac >> gvs[]) >>
  Cases_on `stack_get_unfixed_depth op (LENGTH pending - (idx + 1))
    (LENGTH pending) ps1.ps_stack` >> simp[]
  >- (strip_tac >> gvs[]) >>
  pairarg_tac >>
  `plan_holds ps1 at ==> plan_holds ps2 at` by
    (qpat_x_assum `_ = (reduce_ops,ps2)` mp_tac >>
     IF_CASES_TAC >> simp[]
     >- metis_tac[reduce_depth_plan_holds] >> strip_tac >> gvs[]) >>
  Cases_on `stack_get_unfixed_depth op (LENGTH pending - (idx + 1))
    (LENGTH pending) ps2.ps_stack` >> simp[]
  >- (strip_tac >> gvs[]) >>
  rename1 `stack_get_unfixed_depth _ _ _ _ = SOME d` >>
  Cases_on `d = LENGTH pending - (idx + 1)` >> simp[]
  >- (strip_tac >> gvs[]) >>
  Cases_on `LENGTH pending - (idx + 1) < LENGTH ps2.ps_stack` >> simp[]
  >- (IF_CASES_TAC >> simp[]
      >- (strip_tac >> gvs[] >>
          drule stack_get_unfixed_depth_props >> strip_tac >>
          gvs[plan_holds_def, stack_poke_exchange_mem]) >>
      pairarg_tac >> gvs[] >> pairarg_tac >> simp[] >> strip_tac >> gvs[] >>
      dxrule_all do_swap_plan_holds >> strip_tac >>
      drule_all do_swap_plan_holds >> simp[]) >>
  pairarg_tac >> gvs[] >> pairarg_tac >> simp[] >> strip_tac >> gvs[] >>
  dxrule_all do_swap_plan_holds >> strip_tac >>
  drule_all do_swap_plan_holds >> simp[]
QED

Theorem reorder_plan_holds:
  reorder_plan dfg pending ps = (ops,ps') /\ plan_holds ps at ==>
  plan_holds ps' at
Proof
  `!steps acc ps ops ps'.
    FOLDL (\(acc,st) (idx,op).
      (\(sops,st'). (acc ++ sops,st'))
        (reorder_one dfg pending idx op st)) (acc,ps) steps = (ops,ps') /\
    plan_holds ps at ==> plan_holds ps' at` by
    (Induct >- (simp[] >> rpt strip_tac >> gvs[]) >>
     simp[] >> rpt gen_tac >> PairCases_on `h` >>
     Cases_on `reorder_one dfg pending h0 h1 ps` >> simp[] >>
     strip_tac >> drule_all reorder_one_plan_holds >> strip_tac >>
     first_x_assum (qspecl_then [`acc ++ q`, `r`, `ops`, `ps'`] mp_tac) >>
     simp[]) >>
  simp[reorder_plan_def] >> strip_tac >>
  first_x_assum drule_all >> simp[]
QED

Theorem stack_pop_retains_noninputs:
  n <= LENGTH stk /\
  (!i. i < n ==> MEM (stack_peek i stk) pending) /\
  ~MEM at pending /\ MEM at stk ==>
  MEM at (stack_pop n stk)
Proof
  strip_tac >>
  qpat_x_assum `MEM at stk` (strip_assume_tac o REWRITE_RULE [MEM_EL]) >>
  rename1 `j < LENGTH stk` >>
  Cases_on `j < LENGTH stk - n`
  >- (simp[stack_pop_def, MEM_EL] >> qexists_tac `j` >>
      simp[LENGTH_TAKE_EQ, EL_TAKE]) >>
  `LENGTH stk - 1 - j < n` by decide_tac >>
  `stack_peek (LENGTH stk - 1 - j) stk = at` by
    (simp[stack_peek_def] >>
     `LENGTH stk - (LENGTH stk - 1 - j + 1) = j` by decide_tac >> simp[]) >>
  metis_tac[]
QED

Theorem reorder_consume_retains_noninputs:
  LENGTH pending <= 16 /\ LENGTH pending <= LENGTH ps.ps_stack /\
  (!x. MEM x pending ==>
    LIST_ELEM_COUNT x pending <= LIST_ELEM_COUNT x ps.ps_stack) /\
  reorder_plan dfg pending ps = (ops,ps') /\
  plan_holds ps at /\ ~MEM at pending ==>
  plan_holds (ps' with ps_stack := stack_pop (LENGTH pending) ps'.ps_stack) at
Proof
  strip_tac >>
  drule_all reorder_plan_holds >> strip_tac >>
  drule_all reorder_plan_materialised_length_floor >> strip_tac >>
  drule_at (Pat `reorder_plan _ _ _ = _`) reorder_plan_materialised_order >>
  simp[] >> disch_tac >>
  `!d. d < LENGTH pending ==> MEM (stack_peek d ps'.ps_stack) pending` by
    (rpt strip_tac >>
     first_x_assum (qspec_then `LENGTH pending - 1 - d` mp_tac) >>
     `LENGTH pending - 1 - d < LENGTH pending` by decide_tac >>
     `LENGTH pending - 1 - (LENGTH pending - 1 - d) = d` by decide_tac >>
     simp[] >> strip_tac >> simp[MEM_EL] >>
     qexists_tac `LENGTH pending - (d + 1)` >> simp[]) >>
  gvs[plan_holds_def] >> disj1_tac >> irule stack_pop_retains_noninputs >>
  goal_assum (drule_at Any) >> simp[] >> qexists_tac `pending` >> simp[]
QED

Definition alias_var_mass_def:
  alias_var_mass x ps =
    LIST_ELEM_COUNT (Var x) ps.ps_stack +
    (if Var x IN FDOM ps.ps_spilled then 1 else 0)
End

Theorem alias_var_mass_positive:
  0 < alias_var_mass x ps <=> plan_holds ps (Var x)
Proof
  simp[alias_var_mass_def, plan_holds_def, GSYM LIST_ELEM_COUNT_MEM] >>
  Cases_on `Var x IN FDOM ps.ps_spilled` >> simp[]
QED

Theorem emit_one_input_plan_holds:
  plan_holds ps at ==> plan_holds (SND (emit_one_input opc nl op ps)) at
Proof
  mp_tac (Q.SPECL [`opc`, `nl`, `op`, `ps`] emit_one_input_inventory_mono_aux) >>
  disch_then (qspec_then `at` mp_tac) >>
  simp[plan_holds_def, GSYM LIST_ELEM_COUNT_MEM] >>
  rpt IF_CASES_TAC >> simp[] >> decide_tac
QED

Theorem emit_input_plan_holds:
  !operands opc nl ps at.
    plan_holds ps at ==> plan_holds (SND (emit_input_plan opc operands nl ps)) at
Proof
  Induct >> simp[emit_input_plan_def] >> rpt gen_tac >>
  Cases_on `emit_one_input opc (operand_vars operands ++ nl) h ps` >> simp[] >>
  Cases_on `emit_input_plan opc operands nl r` >> simp[] >> strip_tac >>
  `plan_holds r at` by
    (drule emit_one_input_plan_holds >>
     disch_then (qspecl_then [`opc`, `h`, `operand_vars operands ++ nl`] mp_tac) >>
     simp[]) >>
  first_x_assum (qspecl_then [`opc`, `nl`, `r`, `at`] mp_tac) >> simp[]
QED

Theorem emit_input_plan_live_surplus:
  !operands opc nl ps x.
    MEM x nl /\ plan_holds ps (Var x) ==>
    alias_var_mass x ps + LIST_ELEM_COUNT (Var x) operands <=
    alias_var_mass x (SND (emit_input_plan opc operands nl ps))
Proof
  Induct >> simp[emit_input_plan_def, LIST_ELEM_COUNT_THM] >> rpt gen_tac >>
  Cases_on `emit_one_input opc (operand_vars operands ++ nl) h ps` >> simp[] >>
  Cases_on `emit_input_plan opc operands nl r` >> simp[] >> strip_tac >>
  `plan_holds r (Var x)` by
    (drule emit_one_input_plan_holds >>
     disch_then (qspecl_then [`opc`, `h`, `operand_vars operands ++ nl`] mp_tac) >>
     simp[]) >>
  first_x_assum (qspecl_then [`opc`, `nl`, `r`, `x`] mp_tac) >>
  simp[] >> strip_tac >>
  Cases_on `Var x = h`
  >- (gvs[] >>
      mp_tac (Q.SPECL [`opc`, `operand_vars operands ++ nl`, `Var x`, `ps`]
        emit_one_input_inventory_inc) >>
      simp[is_var_operand_def, GSYM plan_holds_def, GSYM alias_var_mass_def,
           LIST_ELEM_COUNT_THM] >>
      decide_tac) >>
  mp_tac (Q.SPECL [`opc`, `operand_vars operands ++ nl`, `h`, `ps`]
    emit_one_input_inventory_mono_aux) >>
  disch_then (qspec_then `Var x` mp_tac) >>
  simp[GSYM alias_var_mass_def, LIST_ELEM_COUNT_THM] >> decide_tac
QED

Theorem alias_emit_reorder_consume_live:
  emit_input_plan opc inputs nl ps = (iops,prepared) /\
  (!op. MEM op inputs /\ is_var_operand op ==> plan_holds ps op) /\
  PERM inputs selected /\
  reorder_plan dfg selected prepared = (rops,arranged) /\
  MEM x nl /\ plan_holds ps (Var x) ==>
  plan_holds
    (arranged with ps_stack := stack_pop (LENGTH selected) arranged.ps_stack)
    (Var x)
Proof
  strip_tac >>
  `!op. MEM op inputs /\ is_var_operand op ==>
    MEM op ps.ps_stack \/ op IN FDOM ps.ps_spilled` by
    gvs[plan_holds_def] >>
  drule_all alias_emit_reorder_consumed_window >> strip_tac >>
  drule_all emit_input_plan_materialised >> disch_tac >>
  drule perm_operand_counts >> strip_tac >>
  `LENGTH selected = LENGTH inputs` by metis_tac[PERM_LENGTH] >>
  `!op. LIST_ELEM_COUNT op selected <=
    LIST_ELEM_COUNT op prepared.ps_stack` by metis_tac[] >>
  `!op. MEM op selected ==>
    LIST_ELEM_COUNT op selected <= LIST_ELEM_COUNT op prepared.ps_stack` by
    simp[] >>
  reverse (Cases_on `LENGTH inputs <= 16`)
  >- (`16 < LENGTH selected` by decide_tac >>
      drule_all alias_reorder_plan_large_materialised >> strip_tac >>
      mp_tac (Q.SPECL [`inputs`, `opc`, `nl`, `ps`, `x`]
        emit_input_plan_live_surplus) >> simp[] >>
      `0 < alias_var_mass x ps` by simp[alias_var_mass_positive] >>
      qpat_x_assum `arranged.ps_stack = stack_pop _ _ ++ _`
        (mp_tac o Q.AP_TERM `LIST_ELEM_COUNT (Var x)`) >>
      simp[elem_count_append, plan_holds_def, GSYM LIST_ELEM_COUNT_MEM,
           alias_var_mass_def] >>
      rpt IF_CASES_TAC >> gvs[alias_var_mass_def] >> decide_tac) >>
  Cases_on `MEM (Var x) selected`
  >- (`LENGTH selected <= 16` by simp[] >>
      drule_all reorder_plan_materialised_counts >>
      strip_tac >>
      `MEM (Var x) inputs` by metis_tac[PERM_MEM_EQ] >>
      drule emit_input_plan_vars_not_spilled >>
      disch_then (qspec_then `Var x` mp_tac) >>
      simp[is_var_operand_def] >> strip_tac >>
      mp_tac (Q.SPECL [`inputs`, `opc`, `nl`, `ps`, `x`]
        emit_input_plan_live_surplus) >>
      simp[alias_var_mass_def] >>
      `0 < alias_var_mass x ps` by simp[alias_var_mass_positive] >>
      qpat_x_assum `arranged.ps_stack = _` (mp_tac o
        Q.AP_TERM `LIST_ELEM_COUNT (Var x)`) >>
      simp[elem_count_append, plan_holds_def, GSYM LIST_ELEM_COUNT_MEM] >>
      gvs[alias_var_mass_def] >> rpt IF_CASES_TAC >> gvs[] >> decide_tac) >>
  `plan_holds prepared (Var x)` by
    (drule emit_input_plan_holds >>
     disch_then (qspecl_then [`inputs`, `opc`, `nl`] mp_tac) >> simp[]) >>
  irule reorder_consume_retains_noninputs >> simp[] >>
  qexistsl [`dfg`, `rops`, `prepared`] >> simp[]
QED

Definition alias_var_budget_def:
  alias_var_budget pending ps <=>
    !x. alias_var_mass x ps <= SUC (LIST_ELEM_COUNT (Var x) pending)
End

Theorem alias_var_mass_fields:
  ps.ps_stack = qs.ps_stack /\ FDOM ps.ps_spilled = FDOM qs.ps_spilled ==>
  alias_var_mass x ps = alias_var_mass x qs
Proof
  simp[alias_var_mass_def]
QED

Theorem alias_var_budget_empty:
  alias_var_budget [] ps <=>
  !x. LIST_ELEM_COUNT (Var x) ps.ps_stack +
    (if Var x IN FDOM ps.ps_spilled then 1 else 0) <= 1
Proof
  simp[alias_var_budget_def, alias_var_mass_def, LIST_ELEM_COUNT_THM]
QED

Theorem alias_var_mass_push:
  alias_var_mass x (ps with ps_stack := stack_push op ps.ps_stack) =
  alias_var_mass x ps + (if op = Var x then 1 else 0)
Proof
  simp[alias_var_mass_def, stack_push_def, SNOC_APPEND, elem_count_append,
       LIST_ELEM_COUNT_THM] >>
  Cases_on `op = Var x` >> simp[LIST_ELEM_COUNT_THM]
QED

Theorem alias_var_mass_restore:
  alias_var_mass x (SND (do_restore op ps)) = alias_var_mass x ps
Proof
  Cases_on `FLOOKUP ps.ps_spilled op` >>
  simp[do_restore_def, alias_var_mass_def, stack_push_def,
       SNOC_APPEND, elem_count_append, LIST_ELEM_COUNT_THM, finite_mapTheory.FDOM_DOMSUB] >>
  Cases_on `op = Var x` >>
  gvs[finite_mapTheory.flookup_thm, LIST_ELEM_COUNT_THM]
QED

Theorem alias_var_mass_spill_tos:
  !ps x. ps.ps_stack <> [] ==>
  alias_var_mass x (SND (do_spill_tos ps)) <= alias_var_mass x ps
Proof
  rpt gen_tac >> strip_tac >>
  `?a stk. ps.ps_stack = SNOC a stk` by metis_tac[SNOC_CASES] >>
  simp[do_spill_tos_def, alias_var_mass_def] >>
  pairarg_tac >> gvs[] >>
  simp[stack_pop_def, stack_peek_def, SNOC_APPEND, TAKE_APPEND,
       EL_APPEND_EQN, elem_count_append, LIST_ELEM_COUNT_THM] >>
  Cases_on `a = Var x` >> simp[LIST_ELEM_COUNT_THM] >>
  Cases_on `Var x IN FDOM ps.ps_spilled` >> simp[]
QED

Theorem alias_var_mass_spill:
  d < LENGTH ps.ps_stack ==>
  alias_var_mass x (SND (do_spill_at d ps)) <= alias_var_mass x ps
Proof
  strip_tac >> Cases_on `d = 0`
  >- (simp[do_spill_at_def] >> irule alias_var_mass_spill_tos >>
      strip_tac >> gvs[]) >>
  `LIST_ELEM_COUNT (Var x) (stack_swap d ps.ps_stack) =
   LIST_ELEM_COUNT (Var x) ps.ps_stack` by
    (mp_tac (Q.SPECL [`ps.ps_stack`, `0`, `d`, `Var x`]
       doSwapSimTheory.stack_poke_exchange_multiplicity) >>
     simp[stack_poke_def, stack_peek_def, stack_swap_def]) >>
  `stack_swap d ps.ps_stack <> []` by
    (strip_tac >> gvs[stack_swap_def]) >>
  qspecl_then [`ps with ps_stack := stack_swap d ps.ps_stack`, `x`] mp_tac
    alias_var_mass_spill_tos >>
  simp[do_spill_at_def, alias_var_mass_def] >>
  pairarg_tac >> gvs[]
QED

Theorem alias_var_mass_dup:
  d < LENGTH ps.ps_stack ==>
  alias_var_mass x (SND (do_dup d ps)) = alias_var_mass x ps +
    (if stack_peek d ps.ps_stack = Var x then 1 else 0)
Proof
  strip_tac >>
  drule_then assume_tac doSwapSimTheory.do_dup_stack_exact >>
  Cases_on `d <= 15` >>
  simp[alias_var_mass_def, do_dup_def, LET_THM] >>
  rpt (pairarg_tac >> gvs[]) >>
  gvs[alias_var_mass_def, stack_dup_def, elem_count_append] >>
  Cases_on `stack_peek d ps.ps_stack = Var x` >>
  simp[LIST_ELEM_COUNT_THM]
QED

Theorem alias_var_mass_swap:
  d < LENGTH ps.ps_stack ==>
  alias_var_mass x (SND (do_swap d ps)) = alias_var_mass x ps
Proof
  strip_tac >> drule_then (qspec_then `Var x` assume_tac)
    doSwapSimTheory.do_swap_multiplicity >>
  simp[alias_var_mass_def, do_swap_spilled_unchanged]
QED

Theorem alias_do_swap_deep_length:
  16 < d ==>
  LENGTH (SND (do_swap d ps)).ps_stack = MAX (LENGTH ps.ps_stack) (d + 1)
Proof
  strip_tac >> simp[do_swap_def] >> pairarg_tac >> simp[] >>
  simp[listTheory.LENGTH_TAKE, arithmeticTheory.MAX_DEF] >>
  IF_CASES_TAC >> decide_tac
QED

Theorem alias_do_swap_oversized_stack:
  16 < d /\ LENGTH ps.ps_stack <= d ==>
  (SND (do_swap d ps)).ps_stack =
    MAP (\idx. EL idx ps.ps_stack)
      ([d] ++ GENLIST (\i. i + 1) (d - 1) ++ [0])
Proof
  strip_tac >> simp[do_swap_def] >> pairarg_tac >> simp[] >>
  `LENGTH ps.ps_stack - (d + 1) = 0` by decide_tac >>
  `TAKE (d + 1) (REVERSE ps.ps_stack) = REVERSE ps.ps_stack` by
    (irule TAKE_LENGTH_TOO_LONG >> simp[] >> decide_tac) >>
  simp[top_n_def]
QED

(* In the oversized branch the second exchange indexes the entire desired
   window, including indices beyond the first exchange's actual stack.
   These EL terms remain symbolic: no value is chosen for them here. *)
Theorem alias_oversized_exchange_stack:
  e < LENGTH ps.ps_stack /\ 16 < d /\ LENGTH ps.ps_stack <= d ==>
  (SND (do_swap d (SND (do_swap e ps)))).ps_stack =
    MAP (\idx. EL idx (stack_swap e ps.ps_stack))
      ([d] ++ GENLIST (\i. i + 1) (d - 1) ++ [0])
Proof
  strip_tac >>
  `LENGTH (SND (do_swap e ps)).ps_stack = LENGTH ps.ps_stack` by
    simp[alias_do_swap_stack, planWfTheory.stack_swap_length] >>
  simp[alias_do_swap_oversized_stack, alias_do_swap_stack]
QED

Theorem alias_oversized_exchange_head:
  e < LENGTH ps.ps_stack /\ 16 < d /\ LENGTH ps.ps_stack <= d ==>
  HD (SND (do_swap d (SND (do_swap e ps)))).ps_stack =
    EL d (stack_swap e ps.ps_stack)
Proof
  simp[alias_oversized_exchange_stack]
QED

Theorem alias_oversized_exchange_new_origin:
  e < LENGTH ps.ps_stack /\ 16 < d /\ LENGTH ps.ps_stack <= d /\
  MEM at (SND (do_swap d (SND (do_swap e ps)))).ps_stack /\
  ~MEM at ps.ps_stack ==>
  ?i. LENGTH ps.ps_stack <= i /\ i <= d /\
      at = EL i (stack_swap e ps.ps_stack)
Proof
  strip_tac >>
  qpat_x_assum `MEM at _` mp_tac >>
  asm_simp_tac bool_ss [alias_oversized_exchange_stack] >>
  pure_rewrite_tac[MEM_MAP] >> strip_tac >>
  `~(y < LENGTH ps.ps_stack)` by
    (strip_tac >>
     `MEM (EL y (stack_swap e ps.ps_stack)) (stack_swap e ps.ps_stack)` by
       (irule EL_MEM >> simp[]) >>
     gvs[stack_swap_mem_iff]) >>
  qexists_tac `y` >> gvs[MEM_GENLIST] >> decide_tac
QED

Theorem alias_oversized_exchange_join_window:
  e < LENGTH ps.ps_stack /\ 16 < d /\ LENGTH ps.ps_stack <= d /\
  d < LENGTH targets /\
  stack_pop (LENGTH targets)
      (SND (do_swap d (SND (do_swap e ps)))).ps_stack ++ targets =
      (SND (do_swap d (SND (do_swap e ps)))).ps_stack ==>
  targets = (SND (do_swap d (SND (do_swap e ps)))).ps_stack
Proof
  strip_tac >>
  `LENGTH (SND (do_swap d (SND (do_swap e ps)))).ps_stack = d + 1` by
    (simp[alias_oversized_exchange_stack] >> decide_tac) >>
  `stack_pop (LENGTH targets)
      (SND (do_swap d (SND (do_swap e ps)))).ps_stack = []` by
    simp[stack_pop_def] >>
  gvs[]
QED

Theorem alias_restore_spilled_domain:
  !targets ps.
  FDOM (SND (restore_spilled_plan targets ps)).ps_spilled =
    FDOM ps.ps_spilled DIFF set targets
Proof
  Induct >- simp[restore_spilled_plan_def] >> rpt gen_tac >>
  Cases_on `h IN FDOM ps.ps_spilled` >>
  simp[Once restore_spilled_plan_def, do_restore_def, finite_mapTheory.FLOOKUP_DEF] >>
  pairarg_tac >> gvs[] >>
  qpat_x_assum `restore_spilled_plan _ _ = _`
    (mp_tac o AP_TERM ``\p:stack_op list # plan_state. FDOM (SND p).ps_spilled``) >>
  simp[finite_mapTheory.FDOM_DOMSUB] >> disch_then (SUBST1_TAC o SYM) >>
  simp[pred_setTheory.EXTENSION] >> metis_tac[]
QED

Theorem alias_var_mass_restore_spilled:
  !ops ps x.
  alias_var_mass x (SND (restore_spilled_plan ops ps)) = alias_var_mass x ps
Proof
  Induct >> simp[restore_spilled_plan_def] >> rpt gen_tac >>
  pairarg_tac >> simp[] >> pairarg_tac >> simp[] >>
  first_x_assum (qspecl_then [`ps1`, `x`] mp_tac) >>
  mp_tac (Q.INST [`op` |-> `h`] alias_var_mass_restore) >> gvs[]
QED

Theorem alias_select_spill_candidate_not_target:
  select_spill_candidate stk targets d n = SOME cand /\ cand < LENGTH stk ==>
  ~MEM (stack_peek cand stk) targets
Proof
  rpt strip_tac >> gvs[select_spill_candidate_def, LET_THM] >>
  drule FIND_SOME_MEM >> simp[]
QED

Theorem alias_spill_at_domain:
  d < LENGTH ps.ps_stack ==>
  FDOM (SND (do_spill_at d ps)).ps_spilled =
    stack_peek d ps.ps_stack INSERT FDOM ps.ps_spilled
Proof
  strip_tac >> Cases_on `d = 0`
  >- (simp[do_spill_at_def, do_spill_tos_def] >> pairarg_tac >> simp[]) >>
  simp[do_spill_at_def, do_spill_tos_def] >> pairarg_tac >>
  Cases_on `alloc_spill_slot ps.ps_alloc` >> gvs[] >>
  simp[stack_peek_def, stack_swap_def, EL_LUPDATE] >>
  `LENGTH ps.ps_stack - 1 < LENGTH ps.ps_stack` by decide_tac >>
  simp[] >> decide_tac
QED

Theorem alias_restore_spilled_target_exclusion:
  set targets INTER FDOM (SND (restore_spilled_plan targets ps)).ps_spilled = {}
Proof
  simp[alias_restore_spilled_domain] >> SET_TAC[]
QED

Theorem alias_reduce_depth_target_exclusion:
  !fuel targets op f n ps.
  set targets INTER FDOM ps.ps_spilled = {} ==>
  set targets INTER FDOM (SND (reduce_depth_plan fuel targets op f n ps)).ps_spilled = {}
Proof
  Induct >> simp[Once reduce_depth_plan_def] >> rpt gen_tac >> strip_tac >>
  IF_CASES_TAC >> simp[] >>
  Cases_on `stack_get_unfixed_depth op f n ps.ps_stack` >> simp[] >>
  IF_CASES_TAC >> simp[] >>
  Cases_on `select_spill_candidate ps.ps_stack targets x n` >> simp[] >>
  pairarg_tac >> simp[] >> pairarg_tac >> simp[] >>
  drule_then assume_tac stack_get_unfixed_depth_bound >>
  `1 <= LENGTH ps.ps_stack` by decide_tac >>
  drule_all_then strip_assume_tac planWfTheory.select_spill_candidate_bound >>
  drule_all_then assume_tac alias_select_spill_candidate_not_target >>
  `set targets INTER FDOM ps'.ps_spilled = {}` by
    (qpat_assum `x' < LENGTH ps.ps_stack`
       (mp_then Any mp_tac alias_spill_at_domain) >> simp[] >>
     disch_then SUBST1_TAC >>
     gvs[pred_setTheory.EXTENSION] >> metis_tac[]) >>
  first_x_assum drule >>
  disch_then (qspecl_then [`op`, `f`, `n`] mp_tac) >> simp[]
QED

Theorem alias_reorder_one_target_exclusion:
  MEM op targets /\ set targets INTER FDOM ps.ps_spilled = {} ==>
  set targets INTER FDOM (SND (reorder_one dfg targets idx op ps)).ps_spilled = {}
Proof
  strip_tac >>
  `FLOOKUP ps.ps_spilled op = NONE` by
    (gvs[pred_setTheory.EXTENSION, finite_mapTheory.FLOOKUP_DEF] >> metis_tac[]) >>
  simp[reorder_one_def, LET_THM] >>
  pairarg_tac >> simp[] >>
  `ps1 = ps` by
    (Cases_on `stack_get_unfixed_depth op (LENGTH targets - (idx + 1))
      (LENGTH targets) ps.ps_stack` >> gvs[]) >> gvs[] >>
  Cases_on `stack_get_unfixed_depth op (LENGTH targets - (idx + 1))
      (LENGTH targets) ps.ps_stack` >> simp[] >>
  pairarg_tac >> simp[] >>
  `set targets INTER FDOM ps2.ps_spilled = {}` by
    (Cases_on `x > 16` >> gvs[] >>
     drule alias_reduce_depth_target_exclusion >>
     disch_then (qspecl_then [`LENGTH ps.ps_stack`, `op`,
       `LENGTH targets - (idx + 1)`, `LENGTH targets`] mp_tac) >> simp[]) >>
  Cases_on `stack_get_unfixed_depth op (LENGTH targets - (idx + 1))
      (LENGTH targets) ps2.ps_stack` >> simp[] >>
  rpt IF_CASES_TAC >> simp[] >>
  pairarg_tac >> simp[] >> pairarg_tac >> simp[] >>
  metis_tac[do_swap_spilled_unchanged, pairTheory.SND]
QED

Theorem alias_reorder_fold_target_exclusion:
  !steps ops ps.
  EVERY (\p. MEM (SND p) targets) steps /\
  set targets INTER FDOM ps.ps_spilled = {} ==>
  set targets INTER FDOM (SND (FOLDL
    (\(ops, ps) (idx, op).
      (\(step_ops, ps'). (ops ++ step_ops, ps'))
        (reorder_one dfg targets idx op ps)) (ops, ps) steps)).ps_spilled = {}
Proof
  Induct >> simp[] >> rpt gen_tac >> strip_tac >>
  PairCases_on `h` >> gvs[] >> pairarg_tac >> simp[] >>
  `set targets INTER FDOM ps'.ps_spilled = {}` by
    (drule_all alias_reorder_one_target_exclusion >>
     disch_then (qspecl_then [`h0`, `dfg`] mp_tac) >> simp[]) >>
  first_x_assum irule >> simp[]
QED

Theorem alias_reorder_plan_target_exclusion:
  set targets INTER FDOM ps.ps_spilled = {} ==>
  set targets INTER FDOM (SND (reorder_plan dfg targets ps)).ps_spilled = {}
Proof
  strip_tac >> simp[reorder_plan_def] >>
  irule alias_reorder_fold_target_exclusion >> simp[] >>
  simp[EVERY_MEM, indexedListsTheory.MEM_MAPi, pairTheory.FORALL_PROD] >>
  metis_tac[MEM_EL]
QED

Theorem alias_do_swap_length_ceiling:
  !ps n d. LENGTH ps.ps_stack <= n /\ d < n ==>
  LENGTH (SND (do_swap d ps)).ps_stack <= n
Proof
  rpt strip_tac >> Cases_on `16 < d`
  >- (simp[alias_do_swap_deep_length, arithmeticTheory.MAX_DEF] >>
      IF_CASES_TAC >> decide_tac) >>
  `d <= 16` by decide_tac >>
  Cases_on `d = 0` >> simp[do_swap_def, planWfTheory.stack_swap_length]
QED

Theorem alias_reduce_depth_short:
  LENGTH ps.ps_stack <= n ==>
  reduce_depth_plan fuel targets op f n ps = ([],ps)
Proof
  strip_tac >> Cases_on `fuel` >> simp[Once reduce_depth_plan_def] >>
  IF_CASES_TAC >> simp[] >>
  Cases_on `stack_get_unfixed_depth op f n ps.ps_stack` >> simp[] >>
  IF_CASES_TAC >> simp[] >>
  Cases_on `select_spill_candidate ps.ps_stack targets x n` >> simp[] >>
  drule_then assume_tac stack_get_unfixed_depth_bound >>
  `1 <= LENGTH ps.ps_stack` by decide_tac >>
  drule_all_then strip_assume_tac planWfTheory.select_spill_candidate_bound >>
  drule_then assume_tac planWfTheory.select_spill_candidate_below_target >>
  `F` by decide_tac
QED

Theorem alias_reorder_one_short:
  MEM op targets /\ idx < LENGTH targets /\
  LENGTH ps.ps_stack <= LENGTH targets /\
  set targets INTER FDOM ps.ps_spilled = {} ==>
  LENGTH (SND (reorder_one dfg targets idx op ps)).ps_stack <= LENGTH targets /\
  (SND (reorder_one dfg targets idx op ps)).ps_spilled = ps.ps_spilled
Proof
  strip_tac >>
  `FLOOKUP ps.ps_spilled op = NONE` by
    (gvs[pred_setTheory.EXTENSION, finite_mapTheory.FLOOKUP_DEF] >> metis_tac[]) >>
  simp[reorder_one_def, LET_THM] >> pairarg_tac >> simp[] >>
  `ps1 = ps` by
    (Cases_on `stack_get_unfixed_depth op (LENGTH targets - (idx + 1))
      (LENGTH targets) ps.ps_stack` >> gvs[]) >> gvs[] >>
  Cases_on `stack_get_unfixed_depth op (LENGTH targets - (idx + 1))
      (LENGTH targets) ps.ps_stack` >> simp[] >>
  pairarg_tac >> simp[] >>
  `ps2 = ps` by
    (Cases_on `x > 16` >> gvs[alias_reduce_depth_short]) >> gvs[] >>
  Cases_on `x = LENGTH targets - (idx + 1)` >> simp[] >>
  Cases_on `LENGTH targets - (idx + 1) < LENGTH ps.ps_stack` >> simp[]
  >- (Cases_on `operand_equiv dfg op
       (stack_peek (LENGTH targets - (idx + 1)) ps.ps_stack)` >>
      simp[stack_poke_def, LENGTH_LUPDATE] >> suspend "exchange") >>
  suspend "exchange"
QED

Resume alias_reorder_one_short[exchange]:
  markerLib.RESUME_TAC >> rpt disch_tac >>
  drule_then assume_tac stack_get_unfixed_depth_bound >>
  pairarg_tac >> simp[] >> pairarg_tac >> simp[] >>
  `LENGTH ps3.ps_stack <= LENGTH targets` by
    (qspecl_then [`ps`, `LENGTH targets`, `x`] mp_tac
       alias_do_swap_length_ceiling >> gvs[] >> decide_tac) >>
  `LENGTH ps4.ps_stack <= LENGTH targets` by
    (qspecl_then [`ps3`, `LENGTH targets`, `LENGTH targets - (idx + 1)`]
       mp_tac alias_do_swap_length_ceiling >> gvs[] >> decide_tac) >>
  simp[] >> qspecl_then [`x`, `ps`] mp_tac do_swap_spilled_unchanged >>
  qspecl_then [`LENGTH targets - (idx + 1)`, `ps3`] mp_tac
    do_swap_spilled_unchanged >> simp[]
QED

Finalise alias_reorder_one_short

Theorem alias_reorder_fold_short:
  !steps ops ps.
  EVERY (\p. FST p < LENGTH targets /\ MEM (SND p) targets) steps /\
  LENGTH ps.ps_stack <= LENGTH targets /\
  set targets INTER FDOM ps.ps_spilled = {} ==>
  LENGTH (SND (FOLDL
    (\(ops, ps) (idx, op).
      (\(step_ops, ps'). (ops ++ step_ops, ps'))
        (reorder_one dfg targets idx op ps)) (ops, ps) steps)).ps_stack <= LENGTH targets /\
  (SND (FOLDL
    (\(ops, ps) (idx, op).
      (\(step_ops, ps'). (ops ++ step_ops, ps'))
        (reorder_one dfg targets idx op ps)) (ops, ps) steps)).ps_spilled = ps.ps_spilled
Proof
  Induct >> simp[] >> rpt gen_tac >> strip_tac >>
  PairCases_on `h` >> gvs[] >> pairarg_tac >> simp[] >>
  `LENGTH ps'.ps_stack <= LENGTH targets /\ ps'.ps_spilled = ps.ps_spilled` by
    (drule_all alias_reorder_one_short >>
     disch_then (qspec_then `dfg` mp_tac) >> simp[]) >>
  first_x_assum (qspecl_then [`ops ++ step_ops`, `ps'`] mp_tac) >> simp[]
QED

Theorem alias_reorder_plan_short:
  LENGTH ps.ps_stack <= LENGTH targets /\
  set targets INTER FDOM ps.ps_spilled = {} ==>
  LENGTH (SND (reorder_plan dfg targets ps)).ps_stack <= LENGTH targets /\
  (SND (reorder_plan dfg targets ps)).ps_spilled = ps.ps_spilled
Proof
  strip_tac >> simp[reorder_plan_def] >>
  irule alias_reorder_fold_short >> simp[] >>
  simp[EVERY_MEM, indexedListsTheory.MEM_MAPi, pairTheory.FORALL_PROD] >>
  metis_tac[MEM_EL]
QED

Theorem alias_var_mass_reduce_depth:
  !fuel targets op f n ps x.
  alias_var_mass x (SND (reduce_depth_plan fuel targets op f n ps)) <=
  alias_var_mass x ps
Proof
  Induct >> simp[Once reduce_depth_plan_def] >> rpt gen_tac >>
  IF_CASES_TAC >> simp[] >>
  Cases_on `stack_get_unfixed_depth op f n ps.ps_stack` >> simp[] >>
  IF_CASES_TAC >> simp[] >>
  Cases_on `select_spill_candidate ps.ps_stack targets x' n` >> simp[] >>
  pairarg_tac >> simp[] >> pairarg_tac >> simp[] >>
  drule_then assume_tac stack_get_unfixed_depth_bound >>
  `1 <= LENGTH ps.ps_stack` by decide_tac >>
  drule_all_then strip_assume_tac planWfTheory.select_spill_candidate_bound >>
  drule_then (qspec_then `x` mp_tac) (GEN_ALL alias_var_mass_spill) >>
  first_x_assum (qspecl_then [`targets`, `op`, `f`, `n`, `ps'`, `x`] mp_tac) >>
  gvs[] >> decide_tac
QED

Theorem alias_reduce_depth_length_floor:
  !fuel targets op f n ps.
  n <= LENGTH ps.ps_stack ==>
  n <= LENGTH (SND (reduce_depth_plan fuel targets op f n ps)).ps_stack
Proof
  Induct >> simp[Once reduce_depth_plan_def] >> rpt gen_tac >> strip_tac >>
  IF_CASES_TAC >> simp[] >>
  Cases_on `stack_get_unfixed_depth op f n ps.ps_stack` >> simp[] >>
  IF_CASES_TAC >> simp[] >>
  Cases_on `select_spill_candidate ps.ps_stack targets x n` >> simp[] >>
  pairarg_tac >> simp[] >> pairarg_tac >> simp[] >>
  drule_then assume_tac stack_get_unfixed_depth_bound >>
  `1 <= LENGTH ps.ps_stack` by decide_tac >>
  drule_all_then strip_assume_tac planWfTheory.select_spill_candidate_bound >>
  drule_then assume_tac planWfTheory.select_spill_candidate_below_target >>
  `LENGTH ps'.ps_stack = LENGTH ps.ps_stack - 1` by
    (Cases_on `x' = 0` >>
     gvs[do_spill_at_def, do_spill_tos_def, LET_THM,
         stack_swap_def, stack_pop_def] >>
     rpt (pairarg_tac >> gvs[]) >> simp[LENGTH_LUPDATE, LENGTH_TAKE_EQ]) >>
  first_x_assum (qspecl_then [`targets`, `op`, `f`, `n`, `ps'`] mp_tac) >>
  simp[] >> decide_tac
QED

Theorem alias_reorder_one_bounds:
  LENGTH targets <= LENGTH ps.ps_stack ==>
  LENGTH targets <= LENGTH (SND (reorder_one dfg targets idx op ps)).ps_stack /\
  alias_var_mass x (SND (reorder_one dfg targets idx op ps)) <= alias_var_mass x ps
Proof
  strip_tac >> simp[reorder_one_def, LET_THM] >>
  pairarg_tac >> simp[] >>
  `LENGTH targets <= LENGTH ps1.ps_stack /\
   alias_var_mass x ps1 = alias_var_mass x ps` by
    (Cases_on `stack_get_unfixed_depth op (LENGTH targets - (idx + 1))
                   (LENGTH targets) ps.ps_stack` >> gvs[] >>
     Cases_on `FLOOKUP ps.ps_spilled op` >> gvs[] >>
     mp_tac alias_var_mass_restore >>
     qspecl_then [`op`, `ps`] mp_tac planWfTheory.do_restore_length >> gvs[] >> decide_tac) >>
  Cases_on `stack_get_unfixed_depth op (LENGTH targets - (idx + 1))
                   (LENGTH targets) ps1.ps_stack` >> simp[] >>
  pairarg_tac >> simp[] >>
  `LENGTH targets <= LENGTH ps2.ps_stack /\
   alias_var_mass x ps2 <= alias_var_mass x ps1` by
    (Cases_on `x' > 16` >> gvs[] >>
     qspecl_then [`LENGTH ps1.ps_stack`, `targets`, `op`,
       `LENGTH targets - (idx + 1)`, `LENGTH targets`, `ps1`]
       mp_tac alias_reduce_depth_length_floor >>
     qspecl_then [`LENGTH ps1.ps_stack`, `targets`, `op`,
       `LENGTH targets - (idx + 1)`, `LENGTH targets`, `ps1`, `x`]
       mp_tac alias_var_mass_reduce_depth >> gvs[]) >>
  Cases_on `stack_get_unfixed_depth op (LENGTH targets - (idx + 1))
                   (LENGTH targets) ps2.ps_stack` >> simp[] >>
  suspend "exchange"
QED

Resume alias_reorder_one_bounds[exchange]:
  drule_then strip_assume_tac stack_get_unfixed_depth_props >>
  `LENGTH targets - (idx + 1) < LENGTH ps2.ps_stack` by decide_tac >>
  Cases_on `x'' = LENGTH targets - (idx + 1)` >> simp[] >>
  Cases_on `operand_equiv dfg op
    (stack_peek (LENGTH targets - (idx + 1)) ps2.ps_stack)` >> simp[]
  >- (qspecl_then [`ps2.ps_stack`, `x''`, `LENGTH targets - (idx + 1)`, `Var x`]
        mp_tac doSwapSimTheory.stack_poke_exchange_multiplicity >>
      simp[] >> strip_tac >>
      gvs[alias_var_mass_def, stack_poke_def, LENGTH_LUPDATE]) >>
  pairarg_tac >> simp[] >> pairarg_tac >> simp[] >>
  `LENGTH ps3.ps_stack = LENGTH ps2.ps_stack /\
   alias_var_mass x ps3 = alias_var_mass x ps2` by
    (qspecl_then [`x''`, `ps2`] mp_tac planWfTheory.do_swap_length >>
     mp_tac (Q.INST [`d` |-> `x''`, `ps` |-> `ps2`] alias_var_mass_swap) >>
     gvs[]) >>
  qspecl_then [`LENGTH targets - (idx + 1)`, `ps3`]
    mp_tac planWfTheory.do_swap_length >>
  mp_tac (Q.INST [`d` |-> `LENGTH (targets : operand list) - (idx + 1)`, `ps` |-> `ps3`]
    alias_var_mass_swap) >> gvs[] >> decide_tac
QED

Finalise alias_reorder_one_bounds

Theorem alias_reorder_one_length_floor:
  LENGTH targets <= LENGTH ps.ps_stack ==>
  LENGTH targets <= LENGTH (SND (reorder_one dfg targets idx op ps)).ps_stack
Proof
  metis_tac[alias_reorder_one_bounds]
QED

Theorem alias_var_mass_reorder_one:
  LENGTH targets <= LENGTH ps.ps_stack ==>
  alias_var_mass x (SND (reorder_one dfg targets idx op ps)) <= alias_var_mass x ps
Proof
  metis_tac[alias_reorder_one_bounds]
QED

Theorem alias_reorder_fold_bounds:
  !steps ops ps.
  LENGTH targets <= LENGTH ps.ps_stack ==>
  LENGTH targets <= LENGTH (SND (FOLDL
    (\(ops, ps) (idx, op).
      (\(step_ops, ps'). (ops ++ step_ops, ps'))
        (reorder_one dfg targets idx op ps)) (ops, ps) steps)).ps_stack /\
  alias_var_mass x (SND (FOLDL
    (\(ops, ps) (idx, op).
      (\(step_ops, ps'). (ops ++ step_ops, ps'))
        (reorder_one dfg targets idx op ps)) (ops, ps) steps)) <= alias_var_mass x ps
Proof
  Induct >> simp[] >> rpt gen_tac >> strip_tac >>
  PairCases_on `h` >> simp[] >> pairarg_tac >> simp[] >>
  `LENGTH targets <= LENGTH ps'.ps_stack /\
   alias_var_mass x ps' <= alias_var_mass x ps` by
    (mp_tac (Q.INST [`idx` |-> `h0`, `op` |-> `h1`] alias_reorder_one_bounds) >>
     gvs[]) >>
  first_x_assum (qspecl_then [`ops ++ step_ops`, `ps'`] mp_tac) >>
  simp[] >> decide_tac
QED

Theorem alias_reorder_plan_length_floor:
  LENGTH targets <= LENGTH ps.ps_stack ==>
  LENGTH targets <= LENGTH (SND (reorder_plan dfg targets ps)).ps_stack
Proof
  strip_tac >> simp[reorder_plan_def] >>
  metis_tac[alias_reorder_fold_bounds]
QED

Theorem alias_var_mass_reorder_plan:
  LENGTH targets <= LENGTH ps.ps_stack ==>
  alias_var_mass x (SND (reorder_plan dfg targets ps)) <= alias_var_mass x ps
Proof
  strip_tac >> simp[reorder_plan_def] >>
  metis_tac[alias_reorder_fold_bounds]
QED

Theorem alias_reorder_one_upper_support:
  LENGTH targets <= LENGTH ps.ps_stack /\
  reorder_one dfg targets idx op ps = (ops,qs) /\ plan_holds qs (Var x) ==>
  plan_holds ps (Var x)
Proof
  strip_tac >> drule alias_var_mass_reorder_one >>
  disch_then (qspecl_then [`x`, `op`, `idx`, `dfg`] mp_tac) >>
  gvs[GSYM alias_var_mass_positive]
QED

Theorem alias_reorder_one_long_support:
  MEM op targets /\ LENGTH targets <= LENGTH ps.ps_stack /\
  set targets INTER FDOM ps.ps_spilled = {} /\
  reorder_one dfg targets idx op ps = (ops,qs) /\ plan_holds qs at ==>
  plan_holds ps at
Proof
  strip_tac >>
  `FLOOKUP ps.ps_spilled op = NONE` by
    (gvs[pred_setTheory.EXTENSION, finite_mapTheory.FLOOKUP_DEF] >> metis_tac[]) >>
  qpat_x_assum `reorder_one _ _ _ _ _ = _` mp_tac >>
  simp[reorder_one_def, LET_THM] >> pairarg_tac >> simp[] >>
  `ps1 = ps` by
    (Cases_on `stack_get_unfixed_depth op (LENGTH targets - (idx + 1))
      (LENGTH targets) ps.ps_stack` >> gvs[]) >> gvs[] >>
  Cases_on `stack_get_unfixed_depth op (LENGTH targets - (idx + 1))
      (LENGTH targets) ps.ps_stack` >> simp[] >>
  pairarg_tac >> simp[] >>
  `LENGTH targets <= LENGTH ps2.ps_stack /\
   (plan_holds ps2 at ==> plan_holds ps at)` by
    (Cases_on `x > 16` >> gvs[] >> conj_tac
     >- (drule alias_reduce_depth_length_floor >>
         disch_then (qspecl_then [`LENGTH ps.ps_stack`, `targets`, `op`,
           `LENGTH targets - (idx + 1)`] mp_tac) >> simp[]) >>
     strip_tac >> drule reduce_depth_plan_inventory_subset >>
     simp[GSYM plan_holds_def]) >>
  Cases_on `stack_get_unfixed_depth op (LENGTH targets - (idx + 1))
      (LENGTH targets) ps2.ps_stack` >> simp[] >>
  qpat_assum `stack_get_unfixed_depth _ _ _ ps2.ps_stack = SOME _`
    (mp_then Any assume_tac stack_get_unfixed_depth_bound) >>
  qpat_assum `stack_get_unfixed_depth _ _ _ ps2.ps_stack = SOME _`
    (mp_then Any assume_tac stack_get_unfixed_depth_peek) >>
  `LENGTH targets - (idx + 1) < LENGTH ps2.ps_stack` by decide_tac >>
  Cases_on `x' = LENGTH targets - (idx + 1)` >> simp[] >>
  Cases_on `operand_equiv dfg op (stack_peek (LENGTH targets - (idx + 1)) ps2.ps_stack)` >> simp[]
  >- (strip_tac >> gvs[plan_holds_def, stack_poke_exchange_mem] >> metis_tac[]) >>
  pairarg_tac >> simp[] >> pairarg_tac >> simp[] >> strip_tac >> gvs[] >>
  `LENGTH ps3.ps_stack = LENGTH ps2.ps_stack` by
    (qspecl_then [`x'`, `ps2`] mp_tac planWfTheory.do_swap_length >> simp[]) >>
  `LENGTH targets - (idx + 1) < LENGTH ps3.ps_stack` by decide_tac >>
  qpat_assum `do_swap _ ps3 = _`
    (mp_then Any mp_tac do_swap_inventory_subset) >> simp[] >>
  disch_then (qspec_then `at` mp_tac) >>
  qpat_assum `do_swap _ ps2 = _`
    (mp_then Any mp_tac do_swap_inventory_subset) >> simp[] >>
  disch_then (qspec_then `at` mp_tac) >>
  gvs[plan_holds_def] >> metis_tac[]
QED

Theorem alias_reorder_fold_long_support:
  !steps ops ps.
  EVERY (\p. MEM (SND p) targets) steps /\
  LENGTH targets <= LENGTH ps.ps_stack /\
  set targets INTER FDOM ps.ps_spilled = {} ==>
  plan_holds (SND (FOLDL
    (\(ops, ps) (idx, op).
      (\(step_ops, ps'). (ops ++ step_ops, ps'))
        (reorder_one dfg targets idx op ps)) (ops, ps) steps)) at ==>
  plan_holds ps at
Proof
  Induct >> simp[] >> rpt gen_tac >> strip_tac >>
  PairCases_on `h` >> gvs[] >> pairarg_tac >> simp[] >>
  `LENGTH targets <= LENGTH ps'.ps_stack` by
    (drule alias_reorder_one_length_floor >>
     disch_then (qspecl_then [`h1`, `h0`, `dfg`] mp_tac) >> simp[]) >>
  `set targets INTER FDOM ps'.ps_spilled = {}` by
    (drule_all alias_reorder_one_target_exclusion >>
     disch_then (qspecl_then [`h0`, `dfg`] mp_tac) >> simp[]) >>
  strip_tac >>
  `plan_holds ps' at` by
    (first_x_assum irule >> simp[] >> goal_assum (drule_at Any)) >>
  drule_all alias_reorder_one_long_support >> simp[]
QED

Theorem alias_reorder_plan_long_support:
  LENGTH targets <= LENGTH ps.ps_stack /\
  set targets INTER FDOM ps.ps_spilled = {} ==>
  plan_holds (SND (reorder_plan dfg targets ps)) at ==> plan_holds ps at
Proof
  strip_tac >> simp[reorder_plan_def] >> strip_tac >>
  irule alias_reorder_fold_long_support >>
  goal_assum (drule_at Any) >> simp[] >>
  simp[EVERY_MEM, indexedListsTheory.MEM_MAPi, pairTheory.FORALL_PROD] >>
  metis_tac[MEM_EL]
QED

Theorem alias_reorder_plan_upper_support:
  LENGTH targets <= LENGTH ps.ps_stack /\
  reorder_plan dfg targets ps = (ops,qs) /\ plan_holds qs (Var x) ==>
  plan_holds ps (Var x)
Proof
  strip_tac >> drule alias_var_mass_reorder_plan >>
  disch_then (qspecl_then [`x`, `dfg`] mp_tac) >>
  gvs[GSYM alias_var_mass_positive]
QED

Theorem alias_var_budget_reorder_plan:
  LENGTH targets <= LENGTH ps.ps_stack /\ alias_var_budget pending ps ==>
  alias_var_budget pending (SND (reorder_plan dfg targets ps))
Proof
  rw[alias_var_budget_def] >>
  drule_then (qspecl_then [`x`, `dfg`] assume_tac)
    (GEN_ALL alias_var_mass_reorder_plan) >>
  first_x_assum (qspec_then `x` mp_tac) >> decide_tac
QED

Theorem alias_var_mass_pop:
  alias_var_mass x (ps with ps_stack := stack_pop n ps.ps_stack) +
  LIST_ELEM_COUNT (Var x) (top_n n ps.ps_stack) = alias_var_mass x ps
Proof
  `TAKE (LENGTH ps.ps_stack - n) ps.ps_stack ++ top_n n ps.ps_stack =
   ps.ps_stack` by
    (Cases_on `n <= LENGTH ps.ps_stack`
     >- simp[top_n_def, GSYM rich_listTheory.LASTN_def,
             rich_listTheory.LASTN_DROP, TAKE_DROP] >>
     `LENGTH ps.ps_stack <= n` by decide_tac >>
     simp[top_n_def, TAKE_LENGTH_TOO_LONG]) >>
  pop_assum (mp_tac o AP_TERM ``LIST_ELEM_COUNT (Var x)``) >>
  simp[elem_count_append, alias_var_mass_def, stack_pop_def] >> decide_tac
QED

Theorem alias_reorder_residual_mass:
  set targets INTER FDOM ps.ps_spilled = {} ==>
  alias_var_mass x ((SND (reorder_plan dfg targets ps)) with ps_stack :=
    stack_pop (LENGTH targets) (SND (reorder_plan dfg targets ps)).ps_stack) <=
  alias_var_mass x ps
Proof
  strip_tac >> Cases_on `LENGTH targets <= LENGTH ps.ps_stack`
  >- (drule_then (qspecl_then [`x`, `dfg`] assume_tac)
        (GEN_ALL alias_var_mass_reorder_plan) >>
      mp_tac (Q.INST [`ps` |-> `SND (reorder_plan dfg targets ps)`,
        `n` |-> `LENGTH (targets : operand list)`] alias_var_mass_pop) >> decide_tac) >>
  `LENGTH ps.ps_stack <= LENGTH targets` by decide_tac >>
  drule_all alias_reorder_plan_short >>
  disch_then (qspec_then `dfg` strip_assume_tac) >>
  `LENGTH (SND (reorder_plan dfg targets ps)).ps_stack - LENGTH targets = 0`
    by decide_tac >>
  simp[alias_var_mass_def, stack_pop_def, LIST_ELEM_COUNT_THM]
QED

Theorem alias_reorder_residual_support:
  set targets INTER FDOM ps.ps_spilled = {} ==>
  plan_holds ((SND (reorder_plan dfg targets ps)) with ps_stack :=
    stack_pop (LENGTH targets) (SND (reorder_plan dfg targets ps)).ps_stack) at ==>
  plan_holds ps at
Proof
  strip_tac >> Cases_on `LENGTH targets <= LENGTH ps.ps_stack`
  >- (strip_tac >>
      `plan_holds (SND (reorder_plan dfg targets ps)) at` by
        (gvs[plan_holds_def, stack_pop_def] >> metis_tac[MEM_TAKE]) >>
      drule_all alias_reorder_plan_long_support >> simp[]) >>
  `LENGTH ps.ps_stack <= LENGTH targets` by decide_tac >>
  drule_all alias_reorder_plan_short >>
  disch_then (qspec_then `dfg` strip_assume_tac) >>
  `LENGTH (SND (reorder_plan dfg targets ps)).ps_stack - LENGTH targets = 0`
    by decide_tac >>
  simp[plan_holds_def, stack_pop_def]
QED

Theorem alias_reorder_success_mass:
  set targets INTER FDOM ps.ps_spilled = {} /\
  qs = SND (reorder_plan dfg targets ps) /\
  stack_pop (LENGTH targets) qs.ps_stack ++ targets = qs.ps_stack ==>
  alias_var_mass x qs <= MAX (alias_var_mass x ps) (LIST_ELEM_COUNT (Var x) targets)
Proof
  strip_tac >> Cases_on `LENGTH targets <= LENGTH ps.ps_stack`
  >- (drule_then (qspecl_then [`x`, `dfg`] assume_tac)
        (GEN_ALL alias_var_mass_reorder_plan) >> gvs[] >>
      simp[arithmeticTheory.MAX_DEF] >> IF_CASES_TAC >> decide_tac) >>
  `LENGTH ps.ps_stack <= LENGTH targets` by decide_tac >>
  drule_all alias_reorder_plan_short >>
  disch_then (qspec_then `dfg` strip_assume_tac) >>
  `stack_pop (LENGTH targets) qs.ps_stack = []` by
    (gvs[stack_pop_def] >>
     `LENGTH (SND (reorder_plan dfg targets ps)).ps_stack - LENGTH targets = 0`
       by decide_tac >> simp[]) >>
  `qs.ps_stack = targets` by gvs[] >>
  drule_then (qspec_then `dfg` assume_tac) alias_reorder_plan_target_exclusion >>
  Cases_on `MEM (Var x) targets`
  >- (`~(Var x IN FDOM qs.ps_spilled)` by
        (gvs[pred_setTheory.EXTENSION] >> metis_tac[]) >>
      simp[alias_var_mass_def, arithmeticTheory.MAX_DEF] >>
      IF_CASES_TAC >> decide_tac) >>
  `LIST_ELEM_COUNT (Var x) targets = 0` by
    (gvs[GSYM LIST_ELEM_COUNT_MEM] >> decide_tac) >>
  gvs[alias_var_mass_def] >> decide_tac
QED

Theorem alias_restored_reorder_success_mass:
  prepared = SND (restore_spilled_plan targets ps) /\
  qs = SND (reorder_plan dfg targets prepared) /\
  stack_pop (LENGTH targets) qs.ps_stack ++ targets = qs.ps_stack ==>
  alias_var_mass x qs <= MAX (alias_var_mass x ps) (LIST_ELEM_COUNT (Var x) targets)
Proof
  strip_tac >>
  `set targets INTER FDOM prepared.ps_spilled = {}` by
    simp[alias_restore_spilled_target_exclusion] >>
  drule_all alias_reorder_success_mass >>
  disch_then (qspec_then `x` mp_tac) >>
  simp[alias_var_mass_restore_spilled]
QED

Theorem alias_restored_reorder_success_unique:
  prepared = SND (restore_spilled_plan targets ps) /\
  qs = SND (reorder_plan dfg targets prepared) /\
  stack_pop (LENGTH targets) qs.ps_stack ++ targets = qs.ps_stack /\
  alias_var_mass x ps <= 1 /\ LIST_ELEM_COUNT (Var x) targets <= 1 ==>
  alias_var_mass x qs <= 1
Proof
  strip_tac >> drule_all alias_restored_reorder_success_mass >>
  disch_then (qspec_then `x` mp_tac) >>
  simp[arithmeticTheory.MAX_DEF] >> IF_CASES_TAC >> decide_tac
QED

Theorem alias_var_budget_pop_window:
  alias_var_budget (pending ++ consumed) ps /\
  (!x. LIST_ELEM_COUNT (Var x) consumed <=
       LIST_ELEM_COUNT (Var x) (top_n n ps.ps_stack)) ==>
  alias_var_budget pending (ps with ps_stack := stack_pop n ps.ps_stack)
Proof
  rw[alias_var_budget_def] >>
  first_x_assum (qspec_then `x` assume_tac) >>
  first_x_assum (qspec_then `x` mp_tac) >>
  mp_tac alias_var_mass_pop >> simp[elem_count_append] >> decide_tac
QED

Theorem alias_var_budget_reorder_pop:
  qs = SND (reorder_plan dfg targets ps) /\
  LENGTH targets <= LENGTH ps.ps_stack /\
  alias_var_budget (pending ++ consumed) ps /\
  (!x. LIST_ELEM_COUNT (Var x) consumed <=
       LIST_ELEM_COUNT (Var x) (top_n n qs.ps_stack)) ==>
  alias_var_budget pending (qs with ps_stack := stack_pop n qs.ps_stack)
Proof
  strip_tac >> irule alias_var_budget_pop_window >>
  qexists_tac `consumed` >> simp[] >>
  metis_tac[alias_var_budget_reorder_plan]
QED

Theorem alias_var_mass_emit_one:
  !opc live op ps x.
  alias_var_mass x (SND (emit_one_input opc live op ps)) <=
  alias_var_mass x ps + (if op = Var x then 1 else 0)
Proof
  rpt gen_tac >> Cases_on `op` >>
  simp[emit_one_input_def, is_var_operand_def, alias_var_mass_push]
  >~ [`SOPushLabel l`] >-
    (Cases_on `opc = INVOKE` >> simp[alias_var_mass_push]) >>
  pairarg_tac >> simp[] >>
  `alias_var_mass x ps1 = alias_var_mass x ps` by
    (Cases_on `IS_SOME (FLOOKUP ps.ps_spilled (Var s))` >>
     gvs[] >> metis_tac[alias_var_mass_restore, pairTheory.SND]) >>
  IF_CASES_TAC >> simp[] >>
  Cases_on `stack_get_depth (Var s) ps1.ps_stack` >> simp[] >>
  drule_then strip_assume_tac stack_get_depth_props >>
  pairarg_tac >> simp[] >>
  drule_then (qspec_then `x` mp_tac) (GEN_ALL alias_var_mass_dup) >>
  gvs[]
QED

Theorem alias_var_mass_emit_inputs:
  !inputs opc live ps x.
  alias_var_mass x (SND (emit_input_plan opc inputs live ps)) <=
  alias_var_mass x ps + LIST_ELEM_COUNT (Var x) inputs
Proof
  Induct >> simp[emit_input_plan_def, LIST_ELEM_COUNT_THM] >>
  rpt gen_tac >> pairarg_tac >> simp[] >> pairarg_tac >> simp[] >>
  first_x_assum (qspecl_then [`opc`, `live`, `ps1`, `x`] mp_tac) >>
  qspecl_then [`opc`, `operand_vars inputs ++ live`, `h`, `ps`, `x`]
    mp_tac alias_var_mass_emit_one >>
  gvs[] >> Cases_on `h = Var x` >> simp[LIST_ELEM_COUNT_THM] >> decide_tac
QED

Theorem alias_var_mass_emit_inputs_dead:
  !inputs opc live ps x. ~MEM x live ==>
  alias_var_mass x (SND (emit_input_plan opc inputs live ps)) +
    (if MEM (Var x) inputs then 1 else 0) <=
  alias_var_mass x ps + LIST_ELEM_COUNT (Var x) inputs
Proof
  `!ops v. MEM v (dfgDefs$operand_vars ops) <=> MEM (Var v) ops` by
    (Induct >> simp[dfgDefsTheory.operand_vars_def] >>
     rpt gen_tac >> Cases_on `h` >>
     simp[dfgDefsTheory.operand_vars_def, dfgDefsTheory.operand_var_def]) >>
  Induct >> simp[emit_input_plan_def, LIST_ELEM_COUNT_THM] >>
  rpt gen_tac >> strip_tac >> pairarg_tac >> simp[] >>
  pairarg_tac >> simp[] >>
  first_x_assum (qspecl_then [`opc`, `live`, `ps1`, `x`] mp_tac) >>
  simp[] >> strip_tac >>
  Cases_on `h = Var x`
  >- (gvs[] >> Cases_on `MEM (Var x) inputs`
      >- (qspecl_then [`opc`, `operand_vars inputs ++ live`, `Var x`, `ps`, `x`]
            mp_tac alias_var_mass_emit_one >>
          gvs[LIST_ELEM_COUNT_THM] >> decide_tac) >>
      `~MEM x (operand_vars inputs ++ live)` by
        simp[passSharedDefsTheory.MEM_operand_vars_eq_Var] >>
      qpat_x_assum `emit_one_input _ _ _ _ = _` mp_tac >>
      simp[emit_one_input_def, is_var_operand_def] >>
      pairarg_tac >> simp[] >> strip_tac >> gvs[] >>
      `alias_var_mass x ps1 = alias_var_mass x ps` by
        (Cases_on `IS_SOME (FLOOKUP ps.ps_spilled (Var x))` >>
         gvs[] >> metis_tac[alias_var_mass_restore, pairTheory.SND]) >>
      simp[LIST_ELEM_COUNT_THM] >> decide_tac) >>
  qspecl_then [`opc`, `operand_vars inputs ++ live`, `h`, `ps`, `x`]
    mp_tac alias_var_mass_emit_one >>
  simp[LIST_ELEM_COUNT_THM] >>
  Cases_on `MEM (Var x) inputs` >> gvs[] >> decide_tac
QED

Theorem alias_emit_reorder_pop_var_support:
  alias_var_mass x ps <= 1 /\
  (plan_holds ps (Var x) ==> MEM x live \/ MEM (Var x) inputs) /\
  (!op. MEM op inputs /\ is_var_operand op ==> plan_holds ps op) /\
  emit_input_plan opc inputs live ps = (iops,mid) /\
  PERM targets inputs /\ LENGTH inputs <= 16 /\
  reorder_plan dfg targets mid = (rops,qs) ==>
  plan_holds (qs with ps_stack := stack_pop (LENGTH inputs) qs.ps_stack)
         (Var x) ==> MEM x live
Proof
  rpt strip_tac >> spose_not_then assume_tac >>
  `PERM inputs targets` by metis_tac[PERM_SYM] >>
  `!op. MEM op inputs /\ is_var_operand op ==>
     MEM op ps.ps_stack \/ op IN FDOM ps.ps_spilled` by
    metis_tac[plan_holds_def] >>
  drule_all alias_emit_reorder_consumed_window >> strip_tac >>
  `LENGTH targets = LENGTH inputs` by metis_tac[PERM_LENGTH] >>
  `alias_var_mass x qs <= alias_var_mass x mid` by
    (mp_tac (Q.INST [`targets` |-> `targets`, `ps` |-> `mid`,
                    `dfg` |-> `dfg`, `x` |-> `x`] alias_var_mass_reorder_plan) >>
     simp[]) >>
  qspecl_then [`inputs`, `opc`, `live`, `ps`, `x`] mp_tac
    alias_var_mass_emit_inputs_dead >> simp[] >> strip_tac >>
  `alias_var_mass x qs =
   alias_var_mass x (qs with ps_stack := stack_pop (LENGTH inputs) qs.ps_stack) +
   LIST_ELEM_COUNT (Var x) inputs` by
    (drule perm_operand_counts >> strip_tac >>
     qpat_x_assum `qs.ps_stack = _`
       (mp_tac o AP_TERM ``LIST_ELEM_COUNT (Var x)``) >>
     simp[alias_var_mass_def, elem_count_append] >> decide_tac) >>
  `0 < alias_var_mass x
     (qs with ps_stack := stack_pop (LENGTH inputs) qs.ps_stack)` by
    (gvs[plan_holds_def, alias_var_mass_def, GSYM LIST_ELEM_COUNT_MEM] >>
     decide_tac) >>
  Cases_on `MEM (Var x) inputs`
  >- (gvs[] >> decide_tac) >>
  `~plan_holds ps (Var x)` by metis_tac[] >>
  `alias_var_mass x ps = 0` by
    gvs[plan_holds_def, alias_var_mass_def, GSYM LIST_ELEM_COUNT_MEM] >>
  gvs[GSYM LIST_ELEM_COUNT_MEM] >> decide_tac
QED

Theorem alias_emit_reorder_pop_support:
  alias_var_budget [] ps /\
  (!x. plan_holds ps (Var x) ==> MEM x live \/ MEM (Var x) inputs) /\
  (!op. MEM op inputs /\ is_var_operand op ==> plan_holds ps op) /\
  emit_input_plan opc inputs live ps = (iops,mid) /\
  PERM targets inputs /\ LENGTH inputs <= 16 /\
  reorder_plan dfg targets mid = (rops,qs) ==>
  !x. plan_holds (qs with ps_stack := stack_pop (LENGTH inputs) qs.ps_stack)
         (Var x) ==> MEM x live
Proof
  simp[alias_var_budget_def, LIST_ELEM_COUNT_THM] >> rpt strip_tac >>
  irule alias_emit_reorder_pop_var_support >> metis_tac[]
QED

Theorem alias_var_budget_emit_inputs:
  alias_var_budget pending ps ==>
  alias_var_budget (pending ++ inputs) (SND (emit_input_plan opc inputs live ps))
Proof
  simp[alias_var_budget_def, elem_count_append] >> strip_tac >> gen_tac >>
  first_x_assum (qspec_then `x` mp_tac) >>
  qspecl_then [`inputs`, `opc`, `live`, `ps`, `x`] mp_tac
    alias_var_mass_emit_inputs >> decide_tac
QED

Theorem alias_popmany_singleton_inventory:
  plan_holds (SND (popmany_plan [v] ps)) at ==> plan_holds ps at
Proof
  Cases_on `stack_get_depth v ps.ps_stack` >>
  simp[popmany_plan_def, is_contiguous_top_def, popmany_individual_def,
       QSORT_DEF, PARTITION_DEF, PART_DEF] >>
  drule stack_get_depth_props >> strip_tac >>
  Cases_on `x = 0`
  >- (gvs[plan_holds_def, stack_pop_def] >> metis_tac[MEM_TAKE]) >>
  Cases_on `x = 1` >> gvs[] >> pairarg_tac >> simp[] >>
  `!a. MEM a ps'.ps_stack \/ a IN FDOM ps'.ps_spilled ==>
       MEM a ps.ps_stack \/ a IN FDOM ps.ps_spilled` by
    metis_tac[do_swap_inventory_subset] >>
  simp[plan_holds_def, stack_pop_def] >> metis_tac[MEM_TAKE]
QED

Theorem alias_phi_singleton_consumed:
  inputs = FILTER is_var_operand inst.inst_operands /\
  ret = Var (HD inst.inst_outputs) /\
  FILTER (\at. MEM at inputs) ps.ps_stack = [Var v] /\
  MEM (Var v) inputs /\ ~MEM v next_liveness /\ ~MEM ret inputs /\
  (!at. MEM at inputs ==> at NOTIN FDOM ps.ps_spilled) ==>
  !at. MEM at inputs ==>
    ~plan_holds (SND (generate_phi_plan inst next_liveness is_halting ps)) at
Proof
  strip_tac >>
  `?d. stack_get_phi_depth inputs ps.ps_stack = SOME d /\
       stack_peek d ps.ps_stack = Var v /\
       (!at. MEM at inputs ==> ~MEM at (stack_poke d ret ps.ps_stack))` by
    metis_tac[alias_phi_singleton_poke] >>
  `!at. MEM at inputs ==>
      ~plan_holds (ps with ps_stack := stack_poke d ret ps.ps_stack) at` by
    (simp[plan_holds_def] >> metis_tac[]) >>
  gvs[] >> simp[generate_phi_plan_def, operand_to_string_def] >>
  IF_CASES_TAC
  >- (pairarg_tac >> simp[] >> rpt strip_tac >>
      metis_tac[alias_popmany_singleton_inventory, pairTheory.SND]) >>
  simp[]
QED
(* Generic projection for spill release; unlike the specialized stack
   theorem in fnFrameBoundaryGenRet this also describes arbitrary deletion
   batches, without importing the frame-simulation dependency chain. *)
Theorem alias_release_fold_fields:
  !xs ps.
    (FOLDL (\ps' (op,off).
       ps' with <| ps_spilled := ps'.ps_spilled \\ op;
                   ps_alloc := free_spill_slot off ps'.ps_alloc |>) ps xs).ps_stack = ps.ps_stack /\
    (!at. at IN FDOM (FOLDL (\ps' (op,off).
       ps' with <| ps_spilled := ps'.ps_spilled \\ op;
                   ps_alloc := free_spill_slot off ps'.ps_alloc |>) ps xs).ps_spilled <=>
      at IN FDOM ps.ps_spilled /\ ~MEM at (MAP FST xs))
Proof
  Induct >> simp[] >> rpt gen_tac >> PairCases_on `h` >> simp[] >>
  metis_tac[]
QED

Theorem alias_release_dead_spills_domain:
  at IN FDOM (release_dead_spills live ps).ps_spilled <=>
    at IN FDOM ps.ps_spilled /\ (?v. at = Var v /\ MEM v live)
Proof
  Cases_on `at` >>
  simp[release_dead_spills_def, alias_release_fold_fields, MEM_MAP, MEM_FILTER,
       pairTheory.FORALL_PROD, alistTheory.MEM_pair_fmap_to_alist_FLOOKUP] >>
  metis_tac[finite_mapTheory.flookup_thm]
QED

Theorem alias_regular_spill_support:
  !at. at IN FDOM (SND (generate_regular_inst_plan liveness dfg cfg fn inst
    live halting next_term lbl ps)).ps_spilled ==>
    ?v. at = Var v /\ MEM v live
Proof
  simp[generate_regular_inst_plan_def] >>
  qmatch_goalsub_abbrev_tac `generate_emit_ops inst topics` >>
  ntac 4 (pairarg_tac >> simp[]) >>
  Cases_on `inst.inst_outputs = []`
  >- simp[alias_release_dead_spills_domain] >>
  ntac 2 (pairarg_tac >> simp[]) >>
  simp[alias_release_dead_spills_domain]
QED

Theorem alias_regular_dispatch_spill_support:
  inst.inst_opcode <> PHI /\ inst.inst_opcode <> OFFSET /\
  ~is_param_opcode inst.inst_opcode /\ inst.inst_opcode <> NOP /\
  generate_inst_plan liveness dfg cfg fn inst live halting next_term lbl ps =
    SOME (ops,qs) ==>
  !at. at IN FDOM qs.ps_spilled ==> ?v. at = Var v /\ MEM v live
Proof
  strip_tac >>
  qpat_x_assum `generate_inst_plan _ _ _ _ _ _ _ _ _ _ = _` mp_tac >>
  simp[generate_inst_plan_def, AllCaseEqs()] >>
  rpt strip_tac >> gvs[] >>
  metis_tac[alias_regular_spill_support, pairTheory.SND]
QED

Theorem alias_block_insts_final_regular_spill_support:
  !prefix i ps ops qs.
  inst.inst_opcode <> PHI /\ inst.inst_opcode <> OFFSET /\
  ~is_param_opcode inst.inst_opcode /\ inst.inst_opcode <> NOP /\
  generate_block_insts_plan liveness dfg cfg fn lbl halting np blen i
    (prefix ++ [inst]) ps = SOME (ops,qs) ==>
  !at. at IN FDOM qs.ps_spilled ==>
    ?v. at = Var v /\ MEM v (live_vars_at liveness lbl blen)
Proof
  Induct
  >- (simp[generate_block_insts_plan_def, AllCaseEqs()] >>
      metis_tac[alias_regular_dispatch_spill_support]) >>
  simp[Once generate_block_insts_plan_def] >>
  rpt gen_tac >> simp[AllCaseEqs()] >> strip_tac >>
  gvs[] >> first_x_assum drule >> simp[]
QED

Theorem alias_terminator_regular_dispatch:
  is_terminator opc ==>
  opc <> PHI /\ opc <> OFFSET /\ ~is_param_opcode opc /\ opc <> NOP
Proof
  Cases_on `opc` >> simp[is_terminator_def, is_param_opcode_def]
QED

Theorem alias_control_plan_spill_support:
  MEM inst.inst_opcode [JMP; JNZ; DJMP] /\
  generate_inst_plan liveness dfg cfg fn inst live halting next_term lbl ps =
    SOME (ops,qs) ==>
  !at. at IN FDOM qs.ps_spilled ==> ?v. at = Var v /\ MEM v live
Proof
  simp[MEM] >> strip_tac >>
  rpt strip_tac >> irule alias_regular_dispatch_spill_support >>
  goal_assum (drule_at (Pat `generate_inst_plan _ _ _ _ _ _ _ _ _ _ = _`)) >>
  simp[is_param_opcode_def]
QED

Theorem alias_block_insts_final_control_spill_support:
  !prefix i ps ops qs.
  MEM inst.inst_opcode [JMP; JNZ; DJMP] /\
  generate_block_insts_plan liveness dfg cfg fn lbl halting np blen i
    (prefix ++ [inst]) ps = SOME (ops,qs) ==>
  !at. at IN FDOM qs.ps_spilled ==>
    ?v. at = Var v /\ MEM v (live_vars_at liveness lbl blen)
Proof
  rpt gen_tac >> simp[MEM] >> strip_tac >>
  rpt strip_tac >> irule alias_block_insts_final_regular_spill_support >>
  goal_assum (drule_at (Pat `generate_block_insts_plan _ _ _ _ _ _ _ _ _ _ _ = _`)) >>
  simp[is_param_opcode_def]
QED

Theorem alias_block_plan_final_spill_support:
  bb_well_formed bb /\
  generate_block_plan liveness dfg cfg fn bb ps = SOME (ops,qs) ==>
  !at. at IN FDOM qs.ps_spilled ==>
    ?v. at = Var v /\
      MEM v (live_vars_at liveness bb.bb_label (LENGTH bb.bb_instructions))
Proof
  strip_tac >>
  `bb.bb_instructions <> [] /\
   is_terminator (LAST bb.bb_instructions).inst_opcode` by
    gvs[bb_well_formed_def] >>
  drule alias_terminator_regular_dispatch >> strip_tac >>
  `?prefix. non_param_insts bb = prefix ++ [LAST bb.bb_instructions]` by
    (`?front. bb.bb_instructions = front ++ [LAST bb.bb_instructions]` by
       metis_tac[APPEND_FRONT_LAST] >>
     simp[non_param_insts_def] >>
     qpat_x_assum `bb.bb_instructions = _` (fn th => once_rewrite_tac[th]) >>
     simp[FILTER_APPEND]) >>
  qpat_x_assum `generate_block_plan _ _ _ _ _ _ = _` mp_tac >>
  simp[generate_block_plan_def] >> pairarg_tac >> simp[] >>
  pairarg_tac >> simp[AllCaseEqs()] >> strip_tac >> gvs[] >>
  metis_tac[alias_block_insts_final_regular_spill_support]
QED

Theorem alias_block_plan_final_control_spill_support:
  ~NULL bb.bb_instructions /\
  MEM (LAST bb.bb_instructions).inst_opcode [JMP; JNZ; DJMP] /\
  generate_block_plan liveness dfg cfg fn bb ps = SOME (ops,qs) ==>
  !at. at IN FDOM qs.ps_spilled ==>
    ?v. at = Var v /\
      MEM v (live_vars_at liveness bb.bb_label (LENGTH bb.bb_instructions))
Proof
  strip_tac >>
  `?prefix. non_param_insts bb = prefix ++ [LAST bb.bb_instructions]` by
    (`?front. bb.bb_instructions = front ++ [LAST bb.bb_instructions]` by
       metis_tac[APPEND_FRONT_LAST, NULL_EQ] >>
     simp[non_param_insts_def] >>
     qpat_x_assum `bb.bb_instructions = _` (fn th => once_rewrite_tac[th]) >>
     gvs[MEM, FILTER_APPEND, is_param_opcode_def]) >>
  qpat_x_assum `generate_block_plan _ _ _ _ _ _ = _` mp_tac >>
  simp[generate_block_plan_def] >> pairarg_tac >> simp[] >>
  pairarg_tac >> simp[AllCaseEqs()] >> strip_tac >> gvs[] >>
  metis_tac[alias_block_insts_final_control_spill_support, MEM]
QED

Theorem alias_lineage_historical_spill_support:
  wf_function fn /\
  lineage_entry liveness dfg cfg fn ps0 pred lbl ps ==>
  ?pb. lookup_block pred fn.fn_blocks = SOME pb /\
    (!at. at IN FDOM ps.ps_spilled ==> ?v. at = Var v /\
      MEM v (live_vars_at liveness pred (LENGTH pb.bb_instructions)))
Proof
  strip_tac >> gvs[lineage_entry_def] >>
  rename1 `lookup_block pred fn.fn_blocks = SOME pb` >>
  `pb.bb_label = pred /\ MEM pb fn.fn_blocks` by
    metis_tac[lookup_block_label, lookup_block_MEM] >>
  `bb_well_formed pb` by metis_tac[wf_function_def] >>
  metis_tac[alias_block_plan_final_spill_support]
QED

Theorem alias_lineage_join_selected_spill_support:
  liveness = liveness_analyze fn /\ cfg = cfg_analyze fn /\
  codegen_ready_fn fn /\
  lineage_entry liveness dfg cfg fn ps0 pred lbl ps /\
  lookup_block lbl fn.fn_blocks = SOME bb /\
  1 < LENGTH (cfg_preds_of cfg lbl) ==>
  !at. at IN FDOM ps.ps_spilled ==> ?v. at = Var v /\
    MEM v (input_vars_from pred bb.bb_instructions (live_vars_at liveness lbl 0))
Proof
  strip_tac >> gvs[] >>
  `wf_function fn` by fs[codegen_ready_fn_def] >>
  drule_all alias_lineage_historical_spill_support >> strip_tac >>
  `cfg_reachable_of (cfg_analyze fn) pred /\
   MEM lbl (cfg_succs_of (cfg_analyze fn) pred)` by
    (gvs[lineage_entry_def] >> metis_tac[alias_lineage_reachable]) >>
  `MEM pred (cfg_preds_of (cfg_analyze fn) lbl)` by
    metis_tac[cfgAnalysisPropsTheory.cfg_edge_symmetry_uncond] >>
  drule_all alias_ready_join_predecessor_jmp >> strip_tac >>
  drule_all alias_ready_jmp_single_successor >> strip_tac >>
  drule_all alias_single_successor_liveout >> strip_tac >>
  fs[pred_setTheory.EXTENSION] >> metis_tac[]
QED

Theorem release_dead_spills_plan_holds:
  MEM x live /\ plan_holds ps (Var x) ==>
  plan_holds (release_dead_spills live ps) (Var x)
Proof
  simp[plan_holds_def, release_dead_spills_def, alias_release_fold_fields,
       alias_release_dead_spills_domain]
QED

Theorem optimistic_swap_plan_holds:
  optimistic_swap_plan dfg inst live next_term ps = (ops,qs) /\
  plan_holds ps at ==> plan_holds qs at
Proof
  simp[optimistic_swap_plan_def] >>
  rpt IF_CASES_TAC >> simp[] >>
  Cases_on `stack_get_depth (Var (LAST live)) ps.ps_stack` >> simp[] >>
  metis_tac[do_swap_plan_holds]
QED

Theorem alias_var_mass_release_dead_spills:
  alias_var_mass x (release_dead_spills live ps) <= alias_var_mass x ps
Proof
  `(release_dead_spills live ps).ps_stack = ps.ps_stack` by
    simp[release_dead_spills_def, alias_release_fold_fields] >>
  simp[alias_var_mass_def, alias_release_dead_spills_domain] >>
  Cases_on `Var x IN FDOM ps.ps_spilled` >> simp[] >>
  Cases_on `MEM x live` >> simp[]
QED

Theorem alias_emit_ops_inventory:
  (SND (generate_emit_ops inst topics ps)).ps_stack = ps.ps_stack /\
  (SND (generate_emit_ops inst topics ps)).ps_spilled = ps.ps_spilled
Proof
  rw[generate_emit_ops_def] >>
  Cases_on `venom_to_evm_name inst.inst_opcode` >> simp[] >>
  rpt (IF_CASES_TAC >> simp[]) >>
  gvs[asmIRTheory.venom_to_evm_name_def, fresh_label_def]
  >~ [`FILTER is_label_operand inst.inst_operands`] >- suspend "jnz"
  >~ [`FILTER is_label_operand inst.inst_operands`] >- suspend "jnz"
  >~ [`HD inst.inst_operands`] >- suspend "invoke"
  >~ [`HD inst.inst_operands`] >- suspend "invoke"
  >> suspend "jmp"
QED

Resume alias_emit_ops_inventory[jnz]:
  markerLib.RESUME_TAC >>
  Cases_on `FILTER is_label_operand inst.inst_operands` >> simp[] >>
  rename1 `h::t` >> Cases_on `h` >> simp[] >>
  Cases_on `t` >> simp[] >> rename1 `h::t` >>
  Cases_on `h` >> simp[] >> Cases_on `t` >> simp[]
QED

Resume alias_emit_ops_inventory[invoke]:
  markerLib.RESUME_TAC >>
  Cases_on `HD inst.inst_operands` >> simp[]
QED

Resume alias_emit_ops_inventory[jmp]:
  markerLib.RESUME_TAC >>
  Cases_on `inst.inst_operands` >> simp[] >>
  rename1 `h::t` >> Cases_on `h` >> simp[] >> Cases_on `t` >> simp[]
QED

Finalise alias_emit_ops_inventory

Theorem alias_var_mass_emit_ops:
  alias_var_mass x (SND (generate_emit_ops inst topics ps)) = alias_var_mass x ps
Proof
  simp[alias_var_mass_def, alias_emit_ops_inventory]
QED

Theorem pop_foldl_body_plan_holds:
  at <> v /\ plan_holds ps at ==>
  plan_holds (SND (pop_foldl_body (ops,ps) v)) at
Proof
  strip_tac >> Cases_on `stack_get_depth v ps.ps_stack`
  >- simp[pop_foldl_body_def] >>
  drule_then strip_assume_tac stack_get_depth_props >>
  simp[pop_foldl_body_def] >> IF_CASES_TAC >> simp[]
  >- (gvs[plan_holds_def] >> disj1_tac >>
      irule stack_pop_retains_noninputs >> simp[] >>
      qexists_tac `[stack_peek 0 ps.ps_stack]` >> simp[]) >>
  pairarg_tac >> simp[] >>
  `plan_holds ps1 at` by metis_tac[do_swap_plan_holds] >>
  `ps1.ps_stack = stack_swap x ps.ps_stack` by
    metis_tac[doSwapSimTheory.do_swap_stack_result, pairTheory.SND] >>
  `0 < LENGTH ps1.ps_stack /\ stack_peek 0 ps1.ps_stack = v` by
    (simp[stack_swap_def, stack_peek_def, EL_LUPDATE] >>
     gvs[stack_peek_def]) >>
  gvs[plan_holds_def] >> disj1_tac >>
  irule stack_pop_retains_noninputs >> simp[] >>
  qexists_tac `[stack_peek x ps.ps_stack]` >> simp[]
QED

Theorem pop_fold_plan_holds:
  !dead ops ps. ~MEM at dead /\ plan_holds ps at ==>
  plan_holds (SND (FOLDL pop_foldl_body (ops,ps) dead)) at
Proof
  Induct >> simp[] >> rpt gen_tac >> strip_tac >>
  Cases_on `pop_foldl_body (ops,ps) h` >> simp[] >>
  first_x_assum irule >> simp[] >>
  mp_tac (Q.INST [`v` |-> `h`] pop_foldl_body_plan_holds) >> simp[]
QED

Theorem popmany_individual_plan_holds:
  !dead ps at. ~MEM at dead /\ plan_holds ps at ==>
  plan_holds (SND (popmany_individual dead ps)) at
Proof
  rpt gen_tac >> simp[popmany_individual_eq_foldl] >> strip_tac >>
  irule pop_fold_plan_holds >> simp[QSORT_MEM]
QED

Theorem popmany_plan_plan_holds:
  ~MEM at to_pop /\ plan_holds ps at ==>
  plan_holds (SND (popmany_plan to_pop ps)) at
Proof
  strip_tac >> Cases_on `to_pop` >- simp[popmany_plan_def] >>
  simp[Once popmany_plan_def] >>
  reverse IF_CASES_TAC >- metis_tac[popmany_individual_plan_holds] >>
  reverse IF_CASES_TAC >- metis_tac[popmany_individual_plan_holds] >>
  `LENGTH (h::t) < LENGTH ps.ps_stack` by
    (irule contiguous_top_stack_bound >> simp[]) >>
  `!d. 1 <= d /\ d <= LENGTH (h::t) ==>
       MEM (stack_peek d ps.ps_stack) (h::t)` by
    (rpt strip_tac >>
     `MEM d (GENLIST SUC (LENGTH (h::t)))` by
       (simp[MEM_GENLIST] >> qexists_tac `d - 1` >> simp[] >> fs[] >> decide_tac) >>
     `MEM d (MAP THE (MAP (\v. stack_get_depth v ps.ps_stack) (h::t)))` by
       (fs[is_contiguous_top_def] >>
        qpat_x_assum `QSORT _ _ = _` (mp_tac o Q.AP_TERM `MEM d`) >>
        BETA_TAC >> pure_rewrite_tac[QSORT_MEM, MEM] >> metis_tac[]) >>
     qpat_x_assum `MEM d (MAP THE _)`
       (strip_assume_tac o REWRITE_RULE [MEM_MAP]) >>
     rule_assum_tac (CONV_RULE (DEPTH_CONV BETA_CONV)) >>
     rename1 `y = stack_get_depth v ps.ps_stack` >>
     `IS_SOME (stack_get_depth v ps.ps_stack)` by
       (fs[EVERY_MEM, MEM_MAP] >> metis_tac[]) >>
     Cases_on `stack_get_depth v ps.ps_stack` >> gvs[] >>
     drule_then strip_assume_tac stack_get_depth_props >> gvs[]) >>
  pairarg_tac >> simp[] >>
  `plan_holds ps' at` by metis_tac[do_swap_plan_holds] >>
  `ps'.ps_stack = stack_swap (SUC (LENGTH t)) ps.ps_stack` by
    (mp_tac (Q.SPECL [`SUC (LENGTH (t:operand list))`, `ps`]
       doSwapSimTheory.do_swap_stack_result) >> fs[]) >>
  gvs[plan_holds_def] >> disj1_tac >>
  irule stack_pop_retains_noninputs >> simp[] >>
  qexists_tac `h::t` >> simp[] >>
  rpt strip_tac >>
  (simp[stack_peek_def, stack_swap_def, EL_LUPDATE] >>
   IF_CASES_TAC
   >- (first_x_assum (qspec_then `SUC (LENGTH t)` mp_tac) >>
       simp[stack_peek_def]) >>
   `1 <= i` by (Cases_on `i` >> fs[]) >>
   first_x_assum (qspec_then `i` mp_tac) >> simp[stack_peek_def])
QED

Theorem alias_var_mass_pop_foldl_body:
  alias_var_mass x (SND (pop_foldl_body (ops,ps) v)) <= alias_var_mass x ps
Proof
  simp[pop_foldl_body_def] >>
  Cases_on `stack_get_depth v ps.ps_stack` >> simp[] >>
  drule_then strip_assume_tac stack_get_depth_props >>
  IF_CASES_TAC >> simp[]
  >- (mp_tac (Q.INST [`n` |-> `1`] alias_var_mass_pop) >> decide_tac) >>
  pairarg_tac >> simp[] >>
  `alias_var_mass x ps1 = alias_var_mass x ps` by
    metis_tac[alias_var_mass_swap, pairTheory.SND] >>
  mp_tac (Q.INST [`n` |-> `1`, `ps` |-> `ps1`] alias_var_mass_pop) >>
  decide_tac
QED

Theorem alias_var_mass_pop_fold:
  !xs ops ps.
    alias_var_mass x (SND (FOLDL pop_foldl_body (ops,ps) xs)) <= alias_var_mass x ps
Proof
  Induct >> simp[] >> rpt gen_tac >>
  Cases_on `pop_foldl_body (ops,ps) h` >> simp[] >>
  first_x_assum (qspecl_then [`q`, `r`] mp_tac) >>
  mp_tac (Q.INST [`v` |-> `h`] alias_var_mass_pop_foldl_body) >>
  simp[] >> decide_tac
QED

Theorem alias_var_mass_popmany_individual:
  alias_var_mass x (SND (popmany_individual to_pop ps)) <= alias_var_mass x ps
Proof
  simp[popmany_individual_eq_foldl, alias_var_mass_pop_fold]
QED

Theorem alias_var_mass_popmany:
  alias_var_mass x (SND (popmany_plan to_pop ps)) <= alias_var_mass x ps
Proof
  Cases_on `to_pop` >- simp[popmany_plan_def] >>
  simp[popmany_plan_def] >>
  IF_CASES_TAC >> simp[alias_var_mass_popmany_individual] >>
  IF_CASES_TAC >> simp[alias_var_mass_popmany_individual] >>
  `LENGTH (h::t) < LENGTH ps.ps_stack` by
    (irule contiguous_top_stack_bound >> simp[]) >>
  fs[] >>
  pairarg_tac >> simp[] >>
  `alias_var_mass x ps' = alias_var_mass x ps` by
    metis_tac[alias_var_mass_swap, pairTheory.SND] >>
  mp_tac (Q.INST [`n` |-> `SUC (LENGTH (t:operand list))`, `ps` |-> `ps'`] alias_var_mass_pop) >>
  decide_tac
QED

(* A one-slot rename needs no multiplicity bound on its source. *)
Theorem alias_count_lupdate_bound:
  !xs n a b.
    LIST_ELEM_COUNT a (LUPDATE b n xs) <=
    LIST_ELEM_COUNT a xs + (if a = b then 1 else 0)
Proof
  Induct >- simp[LUPDATE_def, LIST_ELEM_COUNT_THM] >> Cases_on `n`
  >- (rpt gen_tac >> Cases_on `a = h` >> Cases_on `a = b` >>
      gvs[LUPDATE_def, LIST_ELEM_COUNT_THM]) >>
  rpt gen_tac >>
  first_x_assum (qspecl_then [`n'`, `a`, `b`] mp_tac) >>
  simp[LUPDATE_def, LIST_ELEM_COUNT_THM] >>
  Cases_on `a = h` >> Cases_on `a = b` >>
  gvs[LIST_ELEM_COUNT_THM] >> decide_tac
QED

Theorem alias_count_lupdate_decreases:
  !xs n a b. n < LENGTH xs /\ EL n xs = a /\ a <> b ==>
    LIST_ELEM_COUNT a (LUPDATE b n xs) < LIST_ELEM_COUNT a xs
Proof
  Induct >- simp[] >> Cases_on `n`
  >- (rpt gen_tac >> simp[LUPDATE_def, LIST_ELEM_COUNT_THM]) >>
  rpt gen_tac >> simp[LUPDATE_def, LIST_ELEM_COUNT_THM] >> strip_tac >>
  first_x_assum drule >> disch_then drule >>
  disch_then (qspec_then `b` mp_tac) >> simp[] >>
  Cases_on `a = h` >> simp[LIST_ELEM_COUNT_THM]
QED

Theorem alias_phi_dead_selected_mass_decreases:
  stack_get_phi_depth (FILTER is_var_operand inst.inst_operands) ps.ps_stack = SOME d /\
  stack_peek d ps.ps_stack = Var a /\
  ~MEM a live /\ a <> HD inst.inst_outputs ==>
  alias_var_mass a (SND (generate_phi_plan inst live halting ps)) < alias_var_mass a ps
Proof
  strip_tac >>
  `d < LENGTH ps.ps_stack` by
    (gvs[stack_get_phi_depth_def] >> drule planWfTheory.stack_find_bound >> simp[]) >>
  `alias_var_mass a
    (ps with ps_stack := stack_poke d (Var (HD inst.inst_outputs)) ps.ps_stack) <
    alias_var_mass a ps` by
    (qspecl_then [`ps.ps_stack`, `LENGTH ps.ps_stack - 1 - d`,
       `Var a`, `Var (HD inst.inst_outputs)`] mp_tac alias_count_lupdate_decreases >>
     gvs[alias_var_mass_def, stack_poke_def, stack_peek_def]) >>
  simp[generate_phi_plan_def, operand_to_string_def] >>
  IF_CASES_TAC
  >- (pairarg_tac >> simp[] >>
      metis_tac[alias_var_mass_popmany, pairTheory.SND, arithmeticTheory.LESS_EQ_LESS_TRANS]) >>
  simp[]
QED

(* Unlike alias_phi_singleton_consumed, this one-name boundary needs no
   singleton filter over the entire input set and permits unrelated spills. *)
Theorem alias_phi_dead_selected_consumed:
  stack_get_phi_depth (FILTER is_var_operand inst.inst_operands) ps.ps_stack = SOME d /\
  stack_peek d ps.ps_stack = Var a /\
  ~MEM a live /\ a <> HD inst.inst_outputs /\ alias_var_mass a ps <= 1 ==>
  ~plan_holds (SND (generate_phi_plan inst live halting ps)) (Var a)
Proof
  strip_tac >> drule_all alias_phi_dead_selected_mass_decreases >>
  disch_then (qspec_then `halting` mp_tac) >>
  gvs[GSYM alias_var_mass_positive]
QED

(* C1.32 premise-production audit (conditional boundary, not a producer).
   At a PHI-prefix cut, let a denote the variable in the selected slot.
   1. alias_lineage_join_phi_prefix_total_slots supplies SOME d, and
      alias_phi_depth_selected supplies membership in the filtered operands.
      It does NOT identify this slot with the historical predecessor's
      selected input: residual prefix operands may also match.  That extra
      identification remains an obligation when a is fixed in advance.
   2. Deadness ~MEM a live is a branch condition of generate_phi_plan, not
      a consequence of historical edge membership.  The live branch uses
      do_dup and retains the source.  At a root-writing PHI it still needs
      a liveness/root-availability argument or a later repair argument.
   3. For an actual historical selected source, output difference follows
      from alias_ready_selected_source_not_phi_output and the singleton
      outputs in alias_ready_phi_single_output.  For a nonreflexive demand
      with normalize(a)=Var r and output r, it follows from a<>r directly.
      Neither fact identifies the slot in item 1.
   4. No current lineage result supplies alias_var_mass a cut <= 1.
      alias_lineage_join_historical_coverage and the prefix-slots theorem
      are lower bounds only.  join_reached_def constrains a suffix, not
      the residual prefix; alias_lineage_join_selected_spill_support permits
      selected sources in spills.  alias_phi_prefix_singleton_mass itself
      requires a starting budget and fresh outputs.  An earlier live PHI
      retains its source (generate_phi_plan_def); it supplies no uniqueness.

   Symbolic residual case: a stack prefix u ++ [Var a] followed by a
   selected top [Var a], with arbitrary spill map sp.  Poking the selected
   top to Var r (a<>r) leaves u ++ [Var a; Var r] and the SAME sp.  If the
   output is kept, the residual mass is count(Var a,u)+1 plus the spill
   indicator.  The suffix condition alone cannot exclude this shape.
   This is not a claim that the shape is reachable from lineage.

   Even complete deletion at this cut is not endpoint deletion: later
   alias_phi_prefix_upper_support allows reintroduction as an output,
   and regular planning may emit an input.  The unresolved producer is
   lineage plus endpoint demand implies deletion of ALL residual copies
   or executed repair, across the remaining planner/execution suffix.
   The strict-decrease theorem above does not supply that implication. *)
Theorem alias_phi_mass_bound:
  !inst live halting ps x.
  alias_var_mass x (SND (generate_phi_plan inst live halting ps)) <=
  alias_var_mass x ps + (if x = HD inst.inst_outputs then 1 else 0)
Proof
  rpt gen_tac >>
  Cases_on `stack_get_phi_depth (FILTER is_var_operand inst.inst_operands) ps.ps_stack`
  >- simp[generate_phi_plan_def] >>
  rename1 `_ = SOME d` >>
  `d < LENGTH ps.ps_stack` by
    (gvs[stack_get_phi_depth_def] >> drule planWfTheory.stack_find_bound >> simp[]) >>
  simp[generate_phi_plan_def] >>
  Cases_on `MEM (operand_to_string (stack_peek d ps.ps_stack)) live` >> simp[]
  >- (Cases_on `do_dup d ps` >> simp[] >>
      `r.ps_stack = ps.ps_stack ++ [stack_peek d ps.ps_stack]` by
        metis_tac[doSwapSimTheory.do_dup_stack_exact, pairTheory.SND] >>
      `r.ps_spilled = ps.ps_spilled` by
        (Cases_on `d <= 15` >>
         gvs[do_dup_def] >> rpt (pairarg_tac >> gvs[])) >>
      `alias_var_mass x
        (r with ps_stack := stack_poke 0 (Var (HD inst.inst_outputs)) r.ps_stack) =
       alias_var_mass x ps + (if x = HD inst.inst_outputs then 1 else 0)` by
        (simp[alias_var_mass_def, stack_poke_def, LUPDATE_APPEND2,
              elem_count_append, LIST_ELEM_COUNT_THM] >>
         Cases_on `x = HD inst.inst_outputs` >> simp[LIST_ELEM_COUNT_THM]) >>
      IF_CASES_TAC
      >- (pairarg_tac >> simp[] >>
          metis_tac[alias_var_mass_popmany, pairTheory.SND]) >>
      gvs[]) >>
  `alias_var_mass x (ps with ps_stack := stack_poke d (Var (HD inst.inst_outputs)) ps.ps_stack) <=
   alias_var_mass x ps + (if x = HD inst.inst_outputs then 1 else 0)` by
    (qspecl_then [`ps.ps_stack`, `LENGTH ps.ps_stack - 1 - d`,
       `Var x`, `Var (HD inst.inst_outputs)`] mp_tac alias_count_lupdate_bound >>
     simp[alias_var_mass_def, stack_poke_def] >>
     rpt IF_CASES_TAC >> simp[] >> decide_tac) >>
  IF_CASES_TAC
  >- (pairarg_tac >> simp[] >>
      metis_tac[alias_var_mass_popmany, pairTheory.SND, arithmeticTheory.LESS_EQ_TRANS]) >>
  simp[]
QED

Theorem alias_phi_preserves_fresh_singleton:
  alias_var_mass x ps <= 1 /\
  (x = HD inst.inst_outputs ==> alias_var_mass x ps = 0) ==>
  alias_var_mass x (SND (generate_phi_plan inst live halting ps)) <= 1
Proof
  strip_tac >>
  qspecl_then [`inst`, `live`, `halting`, `ps`, `x`] mp_tac alias_phi_mass_bound >>
  Cases_on `x = HD inst.inst_outputs` >> gvs[]
QED

Theorem alias_phi_upper_support:
  plan_holds (SND (generate_phi_plan inst live halting ps)) (Var x) ==>
  plan_holds ps (Var x) \/ x = HD inst.inst_outputs
Proof
  strip_tac >> Cases_on `x = HD inst.inst_outputs` >> simp[] >>
  qspecl_then [`inst`, `live`, `halting`, `ps`, `x`] mp_tac alias_phi_mass_bound >>
  gvs[GSYM alias_var_mass_positive] >> decide_tac
QED

Theorem alias_phi_prefix_upper_support:
  !steps ps x.
  plan_holds (FOLDL (\s p. SND (generate_phi_plan (FST p) (SND p) halting s)) ps steps) (Var x) ==>
  plan_holds ps (Var x) \/ MEM x (MAP (\p. HD (FST p).inst_outputs) steps)
Proof
  Induct >- simp[] >> rpt gen_tac >> simp[FOLDL] >>
  strip_tac >> first_x_assum drule >>
  metis_tac[alias_phi_upper_support]
QED

Theorem alias_phi_prefix_singleton_mass:
  !steps ps.
  EVERY (\p. LENGTH (FST p).inst_outputs = 1) steps /\
  ALL_DISTINCT (MAP (\p. HD (FST p).inst_outputs) steps) /\
  (!x. MEM x (MAP (\p. HD (FST p).inst_outputs) steps) ==> alias_var_mass x ps = 0) /\
  (!x. alias_var_mass x ps <= 1) ==>
  !x. alias_var_mass x
    (FOLDL (\s p. SND (generate_phi_plan (FST p) (SND p) halting s)) ps steps) <= 1
Proof
  Induct >- simp[] >> rpt gen_tac >> simp[FOLDL] >> strip_tac >>
  first_x_assum irule >> simp[] >>
  conj_tac
  >- (gen_tac >> irule alias_phi_preserves_fresh_singleton >> metis_tac[]) >>
  rpt strip_tac >>
  qspecl_then [`FST h`, `SND h`, `halting`, `ps`, `x`] mp_tac alias_phi_mass_bound >>
  `x <> HD (FST h).inst_outputs /\ alias_var_mass x ps = 0` by metis_tac[] >>
  simp[]
QED

Theorem alias_popmany_upper_support:
  popmany_plan to_pop ps = (ops,qs) /\ plan_holds qs (Var x) ==>
  plan_holds ps (Var x)
Proof
  strip_tac >> mp_tac alias_var_mass_popmany >>
  gvs[GSYM alias_var_mass_positive]
QED

Theorem alias_mark_dead_stack_upper_support:
  MEM (Var x) (mark_dead_stack retained stk) <=>
    MEM (Var x) stk /\ ~MEM (Var x) retained
Proof
  simp[mark_dead_stack_def, MEM_MAP] >> eq_tac
  >- (rpt strip_tac >> Cases_on `MEM op retained` >> gvs[dead_stack_marker_def]) >>
  strip_tac >> qexists_tac `Var x` >> simp[]
QED

Theorem alias_clean_stack_upper_support:
  clean_stack_plan live cfg fn bb ps = (ops,qs) /\ plan_holds qs (Var x) ==>
  plan_holds ps (Var x)
Proof
  Cases_on `cfg_preds_of cfg bb.bb_label`
  >- (simp[clean_stack_plan_def] >> rpt strip_tac >> gvs[]) >>
  rename1 `cfg_preds_of cfg bb.bb_label = pred::rest` >>
  Cases_on `rest`
  >- (simp[clean_stack_plan_def] >> IF_CASES_TAC
      >- (rpt strip_tac >> gvs[]) >>
      Cases_on `lookup_block pred fn.fn_blocks`
      >- (simp[] >> rpt strip_tac >> gvs[]) >>
      simp[] >>
      qmatch_goalsub_abbrev_tac `if guard then _ else _` >>
      qmatch_goalsub_abbrev_tac `if ok then _ else _` >>
      qmatch_goalsub_abbrev_tac `mark_dead_stack retained` >>
      qmatch_goalsub_abbrev_tac `popmany_plan cleanup ps` >>
      qmatch_goalsub_abbrev_tac `popmany_plan other ps` >>
      POP_ASSUM_LIST (K ALL_TAC) >>
      IF_CASES_TAC
      >- (simp[plan_holds_def, MEM_MAP, dead_stack_marker_def] >>
          rpt strip_tac >> gvs[MEM_MAP]) >>
      IF_CASES_TAC
      >- (pairarg_tac >> simp[] >> rpt strip_tac >> gvs[] >>
          drule alias_popmany_upper_support >> disch_then irule >>
          gvs[plan_holds_def] >> metis_tac[alias_mark_dead_stack_upper_support]) >>
      simp[] >> metis_tac[alias_popmany_upper_support]) >>
  simp[clean_stack_plan_def] >> rpt strip_tac >> gvs[]
QED

Theorem alias_clean_stack_spilled:
  clean_stack_plan live cfg fn bb ps = (ops,qs) ==>
  qs.ps_spilled = ps.ps_spilled
Proof
  `!items ops ps. (SND (FOLDL pop_foldl_body (ops,ps) items)).ps_spilled =
      ps.ps_spilled` by
    (Induct >> simp[] >> rpt gen_tac >>
     Cases_on `stack_get_depth h ps.ps_stack` >> simp[pop_foldl_body_def] >>
     IF_CASES_TAC >> simp[] >> pairarg_tac >> simp[] >>
     metis_tac[do_swap_spilled_unchanged, pairTheory.SND]) >>
  `!items ps. (SND (popmany_plan items ps)).ps_spilled = ps.ps_spilled` by
    (Cases >> simp[popmany_plan_def] >> rpt gen_tac >>
     rpt IF_CASES_TAC >> simp[popmany_individual_eq_foldl] >>
     pairarg_tac >> simp[] >>
     metis_tac[do_swap_spilled_unchanged, pairTheory.SND]) >>
  pop_assum (fn th =>
    (Cases_on `cfg_preds_of cfg bb.bb_label`
     >- (simp[clean_stack_plan_def] >> strip_tac >> gvs[]) >>
     rename1 `cfg_preds_of cfg bb.bb_label = pred::rest` >>
     Cases_on `rest`
     >- (simp[clean_stack_plan_def] >> IF_CASES_TAC
         >- (strip_tac >> gvs[]) >>
         Cases_on `lookup_block pred fn.fn_blocks`
         >- (simp[] >> strip_tac >> gvs[]) >>
         simp[] >> IF_CASES_TAC
         >- (strip_tac >> gvs[]) >>
         IF_CASES_TAC
         >- (pairarg_tac >> simp[] >> strip_tac >> gvs[] >>
             metis_tac[th, pairTheory.SND]) >>
         metis_tac[th, pairTheory.SND]) >>
     simp[clean_stack_plan_def] >> strip_tac >> gvs[]))
QED

Theorem alias_clean_stack_bypass:
  (!pred. cfg_preds_of cfg bb.bb_label = [pred] ==>
    LENGTH (cfg_succs_of cfg pred) <= 1 \/ lookup_block pred fn.fn_blocks = NONE) ==>
  clean_stack_plan live cfg fn bb ps = ([],ps)
Proof
  strip_tac >> Cases_on `cfg_preds_of cfg bb.bb_label`
  >- simp[clean_stack_plan_def] >>
  rename1 `cfg_preds_of cfg bb.bb_label = pred::rest` >> Cases_on `rest`
  >- (first_x_assum (qspec_then `pred` mp_tac) >> simp[clean_stack_plan_def] >>
      strip_tac >> simp[]) >>
  simp[clean_stack_plan_def]
QED

Theorem alias_clean_stack_survival:
  cfg_preds_of cfg bb.bb_label = [pred] /\
  1 < LENGTH (cfg_succs_of cfg pred) /\ lookup_block pred fn.fn_blocks = SOME pred_bb /\
  inputs = input_vars_from pred bb.bb_instructions (live_vars_at live bb.bb_label 0) /\
  layout = live_vars_at live pred (LENGTH pred_bb.bb_instructions) /\
  to_pop = FILTER (\v. ~MEM v inputs) layout /\
  physical = FILTER (\op. IS_SOME (stack_get_depth op ps.ps_stack)) (MAP Var to_pop) /\
  retained = FILTER (\op. below_all_live op inputs ps.ps_stack) physical /\
  cleanup = FILTER (\op. ~MEM op retained) physical /\
  ok = (ps.ps_cleanup_promised \/
    cleanup_elision_safe ps.ps_cleanup_height ps.ps_cleanup_growth cfg fn bb
      (LENGTH ps.ps_stack - LENGTH cleanup)) ==>
  (MEM (Var x) (SND (clean_stack_plan live cfg fn bb ps)).ps_stack <=>
    if NULL inputs /\ ok then F
    else if ok then
      MEM (Var x) (SND (popmany_plan cleanup ps)).ps_stack /\ ~MEM (Var x) retained
    else MEM (Var x) (SND (popmany_plan (MAP Var to_pop) ps)).ps_stack)
Proof
  rpt strip_tac >> gvs[] >> simp[clean_stack_plan_def] >>
  qmatch_goalsub_abbrev_tac `if guard then _ else _` >>
  qmatch_goalsub_abbrev_tac `if enabled then _ else _` >>
  IF_CASES_TAC
  >- simp[MEM_MAP, dead_stack_marker_def] >>
  IF_CASES_TAC
  >- (pairarg_tac >> gvs[alias_mark_dead_stack_upper_support,
                        Abbr `enabled`, Abbr `guard`]) >>
  gvs[Abbr `enabled`, Abbr `guard`]
QED

Theorem alias_unique_take_absent:
  LIST_ELEM_COUNT at stk <= 1 /\ i < LENGTH stk /\ k <= i /\ EL i stk = at ==>
  ~MEM at (TAKE k stk)
Proof
  strip_tac >>
  `MEM at (DROP k stk)` by
    (simp[MEM_EL] >> qexists_tac `i - k` >>
     simp[EL_DROP] >> `k + (i - k) = i` by decide_tac >> simp[]) >>
  `LIST_ELEM_COUNT at (TAKE k stk) + LIST_ELEM_COUNT at (DROP k stk) <= 1` by
    metis_tac[TAKE_DROP, elem_count_append] >>
  fs[GSYM LIST_ELEM_COUNT_MEM] >> decide_tac
QED

Theorem alias_pop_foldl_body_deletes:
  LIST_ELEM_COUNT at ps.ps_stack <= 1 ==>
  ~MEM at (SND (pop_foldl_body (ops,ps) at)).ps_stack
Proof
  strip_tac >> Cases_on `stack_get_depth at ps.ps_stack`
  >- (simp[pop_foldl_body_def] >>
      fs[stack_get_depth_NONE] >> strip_tac >> fs[MEM_EL] >>
      first_x_assum (qspec_then `LENGTH ps.ps_stack - 1 - n` mp_tac) >>
      simp[stack_peek_def] >>
      `LENGTH ps.ps_stack - 1 - (LENGTH ps.ps_stack - 1 - n) = n` by decide_tac >>
      simp[]) >>
  drule_then strip_assume_tac stack_get_depth_props >>
  simp[pop_foldl_body_def] >> IF_CASES_TAC >> simp[]
  >- (simp[stack_pop_def] >> irule alias_unique_take_absent >> simp[] >>
      qexists_tac `LENGTH ps.ps_stack - 1` >>
      gvs[stack_peek_def]) >>
  pairarg_tac >> simp[] >>
  `ps1.ps_stack = stack_swap x ps.ps_stack` by
    metis_tac[doSwapSimTheory.do_swap_stack_result, pairTheory.SND] >>
  `LIST_ELEM_COUNT at ps1.ps_stack <= 1` by
    metis_tac[doSwapSimTheory.do_swap_multiplicity, pairTheory.SND] >>
  gvs[] >> simp[stack_pop_def] >> irule alias_unique_take_absent >> simp[] >>
  qexists_tac `LENGTH ps.ps_stack - 1` >>
  simp[] >> simp[stack_swap_def, EL_LUPDATE, stack_peek_def] >>
  gvs[stack_peek_def]
QED

Theorem alias_pop_foldl_body_count:
  LIST_ELEM_COUNT at (SND (pop_foldl_body (ops,ps) v)).ps_stack <=
  LIST_ELEM_COUNT at ps.ps_stack
Proof
  `!stk:operand list. !n. LIST_ELEM_COUNT at (stack_pop n stk) <= LIST_ELEM_COUNT at stk` by
    (simp[stack_pop_def] >> rpt gen_tac >>
     `LIST_ELEM_COUNT at (TAKE (LENGTH stk - n) stk) +
      LIST_ELEM_COUNT at (DROP (LENGTH stk - n) stk) = LIST_ELEM_COUNT at stk` by
       metis_tac[elem_count_append, TAKE_DROP] >> decide_tac) >>
  Cases_on `stack_get_depth v ps.ps_stack` >> simp[pop_foldl_body_def] >>
  drule_then strip_assume_tac stack_get_depth_props >>
  IF_CASES_TAC >> simp[] >> pairarg_tac >> simp[] >>
  `LIST_ELEM_COUNT at ps1.ps_stack = LIST_ELEM_COUNT at ps.ps_stack` by
    metis_tac[doSwapSimTheory.do_swap_multiplicity, pairTheory.SND] >>
  metis_tac[]
QED

Theorem alias_pop_fold_count:
  !xs ops ps. LIST_ELEM_COUNT at (SND (FOLDL pop_foldl_body (ops,ps) xs)).ps_stack <=
    LIST_ELEM_COUNT at ps.ps_stack
Proof
  Induct >> simp[] >> rpt gen_tac >>
  Cases_on `pop_foldl_body (ops,ps) h` >> simp[] >>
  first_x_assum (qspecl_then [`q`, `r`] mp_tac) >>
  mp_tac (Q.INST [`v` |-> `h`] alias_pop_foldl_body_count) >> simp[] >> decide_tac
QED

Theorem alias_pop_fold_deletes:
  !xs ops ps. MEM at xs /\ LIST_ELEM_COUNT at ps.ps_stack <= 1 ==>
    ~MEM at (SND (FOLDL pop_foldl_body (ops,ps) xs)).ps_stack
Proof
  Induct >> simp[] >> rpt gen_tac >> disch_tac >>
  Cases_on `pop_foldl_body (ops,ps) h` >> simp[] >>
  `LIST_ELEM_COUNT at ps.ps_stack <= 1` by metis_tac[] >>
  `LIST_ELEM_COUNT at r.ps_stack <= LIST_ELEM_COUNT at ps.ps_stack` by
    metis_tac[alias_pop_foldl_body_count, pairTheory.SND] >>
  Cases_on `at = h`
  >- (`~MEM at r.ps_stack` by metis_tac[alias_pop_foldl_body_deletes, pairTheory.SND] >>
      mp_tac (Q.SPECL [`xs`, `q`, `r`] alias_pop_fold_count) >>
      gvs[GSYM LIST_ELEM_COUNT_MEM] >> decide_tac) >>
  first_x_assum irule >> gvs[] >> decide_tac
QED

Theorem alias_popmany_individual_deletes:
  MEM at to_pop /\ LIST_ELEM_COUNT at ps.ps_stack <= 1 ==>
  ~MEM at (SND (popmany_individual to_pop ps)).ps_stack
Proof
  simp[popmany_individual_eq_foldl] >> strip_tac >>
  irule alias_pop_fold_deletes >> simp[QSORT_MEM]
QED

Theorem alias_popmany_contiguous_depth:
  MEM at to_pop /\
  EVERY IS_SOME (MAP (\v. stack_get_depth v stk) to_pop) /\
  is_contiguous_top (MAP THE (MAP (\v. stack_get_depth v stk) to_pop)) ==>
  ?d. stack_get_depth at stk = SOME d /\ 1 <= d /\ d <= LENGTH to_pop
Proof
  strip_tac >>
  `IS_SOME (stack_get_depth at stk)` by (fs[EVERY_MEM, MEM_MAP] >> metis_tac[]) >>
  Cases_on `stack_get_depth at stk` >> fs[] >>
  `MEM x (MAP THE (MAP (\v. stack_get_depth v stk) to_pop))` by
    (simp[MEM_MAP] >> qexists_tac `SOME x` >> simp[] >>
     qexists_tac `at` >> simp[]) >>
  fs[is_contiguous_top_def] >>
  `MEM x (GENLIST SUC (LENGTH to_pop))` by metis_tac[QSORT_MEM] >>
  fs[MEM_GENLIST] >> decide_tac
QED

Theorem alias_popmany_plan_deletes:
  MEM at to_pop /\ LIST_ELEM_COUNT at ps.ps_stack <= 1 ==>
  ~MEM at (SND (popmany_plan to_pop ps)).ps_stack
Proof
  disch_tac >> Cases_on `to_pop` >- fs[] >>
  `MEM at (h::t) /\ LIST_ELEM_COUNT at ps.ps_stack <= 1` by metis_tac[] >>
  qpat_x_assum `MEM _ _ /\ _` kall_tac >>
  simp[Once popmany_plan_def] >>
  reverse IF_CASES_TAC
  >- metis_tac[alias_popmany_individual_deletes] >>
  reverse IF_CASES_TAC
  >- metis_tac[alias_popmany_individual_deletes] >>
  `LENGTH (h::t) < LENGTH ps.ps_stack` by
    (irule contiguous_top_stack_bound >> simp[]) >>
  `?d. stack_get_depth at ps.ps_stack = SOME d /\ 1 <= d /\ d <= LENGTH (h::t)` by
    (irule alias_popmany_contiguous_depth >> simp[]) >>
  drule_then strip_assume_tac stack_get_depth_props >>
  pairarg_tac >> simp[] >>
  `ps'.ps_stack = stack_swap (SUC (LENGTH t)) ps.ps_stack` by
    (mp_tac (Q.SPECL [`SUC (LENGTH (t:operand list))`, `ps`] doSwapSimTheory.do_swap_stack_result) >>
     fs[]) >>
  `LIST_ELEM_COUNT at ps'.ps_stack <= 1` by
    (mp_tac (Q.SPECL [`SUC (LENGTH (t:operand list))`, `ps`]
       doSwapSimTheory.do_swap_multiplicity) >> simp[] >>
     impl_tac >- fs[] >> disch_then (qspec_then `at` mp_tac) >> simp[]) >>
  suspend "positions"
QED

Resume alias_popmany_plan_deletes[positions]:
  markerLib.RESUME_TAC >>
  simp[stack_pop_def] >> irule alias_unique_take_absent >>
  conj_tac >- gvs[] >>
  qexists_tac `if d = SUC (LENGTH t) then LENGTH ps.ps_stack - 1
              else LENGTH ps.ps_stack - 1 - d` >>
  simp[] >>
  `LENGTH ps'.ps_stack = LENGTH ps.ps_stack` by simp[] >>
  `EL (if d = SUC (LENGTH t) then LENGTH ps.ps_stack - 1
       else LENGTH ps.ps_stack - 1 - d) ps'.ps_stack = at` by
    (Cases_on `d = SUC (LENGTH t)` >>
     `LENGTH ps.ps_stack - 1 - SUC (LENGTH t) <> LENGTH ps.ps_stack - 1` by
       (fs[] >> decide_tac) >>
     simp[stack_swap_def, EL_LUPDATE] >>
     gvs[stack_peek_def] >>
     `LENGTH ps.ps_stack - 1 - d <> LENGTH ps.ps_stack - 1` by decide_tac >>
     `LENGTH ps.ps_stack - 1 - d <> LENGTH ps.ps_stack - 1 - SUC (LENGTH t)` by
       (fs[] >> decide_tac) >> simp[]) >>
  gvs[] >> decide_tac
QED

Finalise alias_popmany_plan_deletes

Theorem alias_popmany_stack_count:
  LIST_ELEM_COUNT at (SND (popmany_plan to_pop ps)).ps_stack <=
    LIST_ELEM_COUNT at ps.ps_stack
Proof
  Cases_on `to_pop` >- simp[popmany_plan_def] >>
  simp[Once popmany_plan_def] >>
  reverse IF_CASES_TAC
  >- simp[popmany_individual_eq_foldl, alias_pop_fold_count] >>
  reverse IF_CASES_TAC
  >- simp[popmany_individual_eq_foldl, alias_pop_fold_count] >>
  `LENGTH (h::t) < LENGTH ps.ps_stack` by
    (irule contiguous_top_stack_bound >> simp[]) >>
  pairarg_tac >> simp[] >>
  `LIST_ELEM_COUNT at ps'.ps_stack = LIST_ELEM_COUNT at ps.ps_stack` by
    (mp_tac (Q.SPECL [`SUC (LENGTH (t:operand list))`, `ps`]
       doSwapSimTheory.do_swap_multiplicity) >> fs[]) >>
  simp[stack_pop_def] >>
  metis_tac[elem_count_append, TAKE_DROP, arithmeticTheory.LESS_EQ_ADD]
QED

Theorem alias_clean_stack_edge_deletes:
  cfg_preds_of cfg bb.bb_label = [pred] /\
  1 < LENGTH (cfg_succs_of cfg pred) /\
  lookup_block pred fn.fn_blocks = SOME pb /\
  MEM v (live_vars_at live pred (LENGTH pb.bb_instructions)) /\
  ~MEM v (input_vars_from pred bb.bb_instructions (live_vars_at live bb.bb_label 0)) /\
  LIST_ELEM_COUNT (Var v) ps.ps_stack <= 1 ==>
  ~MEM (Var v) (SND (clean_stack_plan live cfg fn bb ps)).ps_stack
Proof
  strip_tac >> simp[clean_stack_plan_def] >>
  qmatch_goalsub_abbrev_tac `if guard then _ else _` >>
  qmatch_goalsub_abbrev_tac `if ok then _ else _` >>
  qmatch_goalsub_abbrev_tac `mark_dead_stack retained` >>
  qmatch_goalsub_abbrev_tac `popmany_plan cleanup ps` >>
  IF_CASES_TAC
  >- simp[MEM_MAP, dead_stack_marker_def] >>
  IF_CASES_TAC
  >- (pairarg_tac >> simp[alias_mark_dead_stack_upper_support] >>
      Cases_on `MEM (Var v) retained` >> simp[] >>
      Cases_on `MEM (Var v) ps.ps_stack`
      >- (`MEM (Var v) cleanup` by
            (`IS_SOME (stack_get_depth (Var v) ps.ps_stack)` by
               (Cases_on `stack_get_depth (Var v) ps.ps_stack` >> simp[] >>
                qpat_x_assum `MEM (Var v) ps.ps_stack` mp_tac >>
                qpat_x_assum `stack_get_depth _ _ = NONE` mp_tac >>
                POP_ASSUM_LIST (K ALL_TAC) >>
                simp[stack_get_depth_NONE, MEM_EL] >> rpt strip_tac >>
                first_x_assum (qspec_then `LENGTH ps.ps_stack - 1 - n` mp_tac) >>
                simp[stack_peek_def] >>
                `LENGTH ps.ps_stack - 1 - n < LENGTH ps.ps_stack /\
                 LENGTH ps.ps_stack - 1 - (LENGTH ps.ps_stack - 1 - n) = n` by decide_tac >>
                simp[]) >>
             simp[Abbr `cleanup`, MEM_FILTER, MEM_MAP]) >>
          metis_tac[alias_popmany_plan_deletes, pairTheory.SND]) >>
      mp_tac (Q.INST [`at` |-> `Var v`, `to_pop` |-> `cleanup`] alias_popmany_stack_count) >>
      gvs[GSYM LIST_ELEM_COUNT_MEM]) >>
  `MEM (Var v) (MAP Var (FILTER
     (\v. ~MEM v (input_vars_from pred bb.bb_instructions
       (live_vars_at live bb.bb_label 0)))
     (live_vars_at live pred (LENGTH pb.bb_instructions))))` by
    simp[MEM_MAP, MEM_FILTER] >>
  metis_tac[alias_popmany_plan_deletes]
QED

Theorem alias_clean_stack_stack_support:
  MEM (Var x) (SND (clean_stack_plan live cfg fn bb ps)).ps_stack ==>
  MEM (Var x) ps.ps_stack
Proof
  Cases_on `cfg_preds_of cfg bb.bb_label`
  >- simp[clean_stack_plan_def] >>
  rename1 `cfg_preds_of cfg bb.bb_label = pred::rest` >>
  Cases_on `rest`
  >- (simp[clean_stack_plan_def] >> IF_CASES_TAC
      >- simp[] >>
      Cases_on `lookup_block pred fn.fn_blocks`
      >- simp[] >> simp[] >>
      qmatch_goalsub_abbrev_tac `if guard then _ else _` >>
      qmatch_goalsub_abbrev_tac `if ok then _ else _` >>
      qmatch_goalsub_abbrev_tac `mark_dead_stack retained` >>
      qmatch_goalsub_abbrev_tac `popmany_plan cleanup ps` >>
      qmatch_goalsub_abbrev_tac `popmany_plan other ps` >>
      POP_ASSUM_LIST (K ALL_TAC) >>
      IF_CASES_TAC
      >- (simp[MEM_MAP, dead_stack_marker_def] >> metis_tac[]) >>
      IF_CASES_TAC
      >- (pairarg_tac >> simp[alias_mark_dead_stack_upper_support] >>
          mp_tac (Q.INST [`at` |-> `Var x`, `to_pop` |-> `other`]
            alias_popmany_stack_count) >>
          gvs[GSYM LIST_ELEM_COUNT_MEM] >> decide_tac) >>
      qmatch_goalsub_abbrev_tac `popmany_plan removed ps` >>
      mp_tac (Q.INST [`at` |-> `Var x`, `to_pop` |-> `removed`]
        alias_popmany_stack_count) >>
      simp[GSYM LIST_ELEM_COUNT_MEM] >> decide_tac) >>
  simp[clean_stack_plan_def]
QED

Theorem alias_clean_stack_edge_support:
  cfg_preds_of cfg bb.bb_label = [pred] /\
  1 < LENGTH (cfg_succs_of cfg pred) /\
  lookup_block pred fn.fn_blocks = SOME pb /\
  (!x. MEM (Var x) ps.ps_stack ==>
    MEM x (live_vars_at live pred (LENGTH pb.bb_instructions))) /\
  (!x. LIST_ELEM_COUNT (Var x) ps.ps_stack <= 1) ==>
  !x. MEM (Var x) (SND (clean_stack_plan live cfg fn bb ps)).ps_stack ==>
  MEM x (input_vars_from pred bb.bb_instructions (live_vars_at live bb.bb_label 0))
Proof
  rpt strip_tac >>
  `MEM (Var x) ps.ps_stack` by metis_tac[alias_clean_stack_stack_support] >>
  spose_not_then assume_tac >>
  `MEM x (live_vars_at live pred (LENGTH pb.bb_instructions))` by metis_tac[] >>
  `LIST_ELEM_COUNT (Var x) ps.ps_stack <= 1` by simp[] >>
  drule_all alias_clean_stack_edge_deletes >> simp[]
QED

Theorem alias_clean_stack_edge_inventory:
  cfg_preds_of cfg bb.bb_label = [pred] /\
  1 < LENGTH (cfg_succs_of cfg pred) /\
  lookup_block pred fn.fn_blocks = SOME pb /\
  MEM v (live_vars_at live pred (LENGTH pb.bb_instructions)) /\
  ~MEM v (input_vars_from pred bb.bb_instructions (live_vars_at live bb.bb_label 0)) /\
  LIST_ELEM_COUNT (Var v) ps.ps_stack <= 1 ==>
  (plan_holds (SND (clean_stack_plan live cfg fn bb ps)) (Var v) <=>
   Var v IN FDOM ps.ps_spilled)
Proof
  strip_tac >> drule_all alias_clean_stack_edge_deletes >> strip_tac >>
  Cases_on `clean_stack_plan live cfg fn bb ps` >>
  drule alias_clean_stack_spilled >> simp[plan_holds_def]
QED

Theorem alias_pop_fold_mass_zero:
  !xs ops ps. MEM (Var x) xs /\ alias_var_mass x ps <= 1 /\
    Var x NOTIN FDOM ps.ps_spilled ==>
    alias_var_mass x (SND (FOLDL pop_foldl_body (ops,ps) xs)) = 0
Proof
  Induct >> simp[] >> rpt gen_tac >> disch_tac >>
  Cases_on `pop_foldl_body (ops,ps) h` >> simp[] >>
  `alias_var_mass x ps <= 1 /\ Var x NOTIN FDOM ps.ps_spilled` by metis_tac[] >>
  `alias_var_mass x r <= alias_var_mass x ps` by
    metis_tac[alias_var_mass_pop_foldl_body, pairTheory.SND] >>
  `Var x NOTIN FDOM r.ps_spilled` by
    (qpat_x_assum `pop_foldl_body _ _ = _` mp_tac >>
     Cases_on `stack_get_depth h ps.ps_stack`
     >- (simp[pop_foldl_body_def] >> strip_tac >> gvs[]) >>
     simp[pop_foldl_body_def] >> IF_CASES_TAC >> simp[]
     >- (strip_tac >> gvs[]) >>
     pairarg_tac >> simp[] >>
     strip_tac >> gvs[] >>
     metis_tac[do_swap_spilled_unchanged, pairTheory.SND]) >>
  Cases_on `Var x = h`
  >- (`LIST_ELEM_COUNT (Var x) ps.ps_stack <= 1` by
        fs[alias_var_mass_def] >>
      `~MEM (Var x) r.ps_stack` by
        metis_tac[alias_pop_foldl_body_deletes, pairTheory.SND] >>
      `alias_var_mass x r = 0` by
        (gvs[alias_var_mass_def, GSYM LIST_ELEM_COUNT_MEM]) >>
      mp_tac (Q.SPECL [`xs`, `q`, `r`] alias_var_mass_pop_fold) >> simp[]) >>
  first_x_assum irule >> gvs[] >> decide_tac
QED

Theorem alias_popmany_plan_mass_zero:
  MEM (Var x) to_pop /\ alias_var_mass x ps <= 1 /\
    Var x NOTIN FDOM ps.ps_spilled ==>
  alias_var_mass x (SND (popmany_plan to_pop ps)) = 0
Proof
  disch_tac >>
  `MEM (Var x) to_pop /\ alias_var_mass x ps <= 1 /\
   Var x NOTIN FDOM ps.ps_spilled` by metis_tac[] >>
  qpat_x_assum `MEM _ _ /\ _` kall_tac >>
  `LIST_ELEM_COUNT (Var x) ps.ps_stack <= 1` by fs[alias_var_mass_def] >>
  `~MEM (Var x) (SND (popmany_plan to_pop ps)).ps_stack` by
    metis_tac[alias_popmany_plan_deletes] >>
  Cases_on `to_pop` >- fs[] >>
  simp[Once popmany_plan_def] >>
  reverse IF_CASES_TAC
  >- (simp[popmany_individual_eq_foldl] >> irule alias_pop_fold_mass_zero >>
      simp[QSORT_MEM]) >>
  reverse IF_CASES_TAC
  >- (simp[popmany_individual_eq_foldl] >> irule alias_pop_fold_mass_zero >>
      simp[QSORT_MEM]) >>
  pairarg_tac >> simp[] >>
  `ps'.ps_spilled = ps.ps_spilled` by
    metis_tac[do_swap_spilled_unchanged, pairTheory.SND] >>
  qpat_x_assum `~MEM _ (SND _).ps_stack` mp_tac >>
  simp[Once popmany_plan_def] >> simp[] >>
  simp[alias_var_mass_def, GSYM LIST_ELEM_COUNT_MEM]
QED

Theorem alias_var_mass_optimistic_swap:
  alias_var_mass x (SND (optimistic_swap_plan dfg inst live next_term ps)) <=
  alias_var_mass x ps
Proof
  simp[optimistic_swap_plan_def] >>
  rpt (IF_CASES_TAC >> simp[]) >>
  Cases_on `stack_get_depth (Var (LAST live)) ps.ps_stack` >> simp[] >>
  drule_then strip_assume_tac stack_get_depth_props >>
  simp[alias_var_mass_swap]
QED

Theorem alias_var_mass_outputs:
  !outs ps.
    alias_var_mass x (FOLDL (\ps' out.
      ps' with ps_stack := stack_push (Var out) ps'.ps_stack) ps outs) =
    alias_var_mass x ps + LIST_ELEM_COUNT x outs
Proof
  Induct >> simp[LIST_ELEM_COUNT_THM] >>
  rpt gen_tac >> simp[alias_var_mass_push] >>
  Cases_on `h = x` >> gvs[LIST_ELEM_COUNT_DEF] >> decide_tac
QED

Theorem alias_var_mass_zero:
  alias_var_mass x ps = 0 <=> ~plan_holds ps (Var x)
Proof
  simp[alias_var_mass_def, plan_holds_def, GSYM LIST_ELEM_COUNT_MEM] >>
  Cases_on `Var x IN FDOM ps.ps_spilled` >> simp[]
QED

Theorem alias_emit_reorder_pop_mass:
  emit_input_plan opc inputs live ps = (iops,mid) /\
  (!op. MEM op inputs /\ is_var_operand op ==> plan_holds ps op) /\
  PERM targets inputs /\ LENGTH inputs <= 16 /\
  reorder_plan dfg targets mid = (rops,qs) ==>
  alias_var_mass x (qs with ps_stack := stack_pop (LENGTH inputs) qs.ps_stack) <=
  alias_var_mass x ps
Proof
  strip_tac >>
  `PERM inputs targets` by metis_tac[PERM_SYM] >>
  `!op. MEM op inputs /\ is_var_operand op ==>
     MEM op ps.ps_stack \/ op IN FDOM ps.ps_spilled` by
    metis_tac[plan_holds_def] >>
  drule_all alias_emit_reorder_consumed_window >> strip_tac >>
  `LENGTH targets = LENGTH inputs` by metis_tac[PERM_LENGTH] >>
  `alias_var_mass x qs <= alias_var_mass x mid` by
    (mp_tac (Q.INST [`targets` |-> `targets`, `ps` |-> `mid`,
                    `dfg` |-> `dfg`, `x` |-> `x`] alias_var_mass_reorder_plan) >>
     simp[]) >>
  `alias_var_mass x qs =
   alias_var_mass x (qs with ps_stack := stack_pop (LENGTH inputs) qs.ps_stack) +
   LIST_ELEM_COUNT (Var x) inputs` by
    (drule perm_operand_counts >> strip_tac >>
     qpat_x_assum `qs.ps_stack = _`
       (mp_tac o AP_TERM ``LIST_ELEM_COUNT (Var x)``) >>
     simp[alias_var_mass_def, elem_count_append] >> decide_tac) >>
  qspecl_then [`inputs`, `opc`, `live`, `ps`, `x`] mp_tac
    alias_var_mass_emit_inputs >> simp[] >> decide_tac
QED

Theorem alias_regular_postprocess_holds:
  generate_emit_ops inst topics
    (FOLDL (\s out. s with ps_stack := stack_push (Var out) s.ps_stack)
      consumed inst.inst_outputs) = (eops,emitted) /\
  (if inst.inst_outputs <> [] /\ (~is_halting \/ LENGTH inst.inst_outputs > 1)
   then popmany_plan (MAP Var (FILTER (\out. ~MEM out live) inst.inst_outputs)) emitted
   else ([],emitted)) = (pops,post) /\
  MEM x live /\ (plan_holds consumed (Var x) \/ MEM x inst.inst_outputs) ==>
  plan_holds post (Var x)
Proof
  strip_tac >>
  `plan_holds emitted (Var x)` by
    (qpat_x_assum `generate_emit_ops _ _ _ = _`
       (mp_tac o AP_TERM ``\p:stack_op list # plan_state. alias_var_mass x (SND p)``) >>
     simp[alias_var_mass_emit_ops, alias_var_mass_outputs] >>
     strip_tac >> spose_not_then assume_tac >>
     `alias_var_mass x emitted = 0` by metis_tac[alias_var_mass_zero] >>
     `alias_var_mass x consumed <> 0 \/ LIST_ELEM_COUNT x inst.inst_outputs > 0` by
       metis_tac[alias_var_mass_zero, LIST_ELEM_COUNT_MEM] >> decide_tac) >>
  qpat_x_assum `(if _ then _ else _) = _` mp_tac >>
  IF_CASES_TAC >> simp[] >> strip_tac >> gvs[] >>
  (mp_tac (Q.INST [`at` |-> `Var x`, `ps` |-> `emitted`,
     `to_pop` |-> `MAP Var (FILTER (\out. ~MEM out live) inst.inst_outputs)`]
     popmany_plan_plan_holds) >> simp[MEM_MAP, MEM_FILTER])
QED

Theorem alias_regular_plan_stages:
  inst.inst_opcode <> JMP /\
  generate_regular_inst_plan liveness dfg cfg fn inst live is_halting next_term lbl ps = (ops,qs) ==>
  ?iops mid targets rops reordered topics eops emitted pops post.
    emit_input_plan inst.inst_opcode (compute_operands inst) live ps = (iops,mid) /\
    PERM targets (compute_operands inst) /\
    reorder_plan dfg targets mid = (rops,reordered) /\
    generate_emit_ops inst topics
      (FOLDL (\s out. s with ps_stack := stack_push (Var out) s.ps_stack)
        (reordered with ps_stack := stack_pop (LENGTH (compute_operands inst)) reordered.ps_stack)
        inst.inst_outputs) = (eops,emitted) /\
    (if inst.inst_outputs <> [] /\ (~is_halting \/ LENGTH inst.inst_outputs > 1)
     then popmany_plan (MAP Var (FILTER (\out. ~MEM out live) inst.inst_outputs)) emitted
     else ([],emitted)) = (pops,post) /\
    (!x. alias_var_mass x qs <= alias_var_mass x post) /\
    (!x. MEM x live /\ plan_holds post (Var x) ==> plan_holds qs (Var x))
Proof
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `generate_regular_inst_plan _ _ _ _ _ _ _ _ _ _ = _` mp_tac >>
  simp[generate_regular_inst_plan_def] >>
  pairarg_tac >> simp[] >>
  qmatch_goalsub_abbrev_tac `generate_emit_ops inst topics` >>
  pairarg_tac >> simp[] >>
  `?targets. PERM targets (compute_operands inst) /\
     reorder_plan dfg targets ps1 = (reorder_ops,ps4)` by
    (qpat_x_assum `(if _ then _ else _) = _` mp_tac >>
     IF_CASES_TAC >> simp[]
     >- (pairarg_tac >> simp[] >> pairarg_tac >> simp[] >>
         IF_CASES_TAC >> simp[] >> strip_tac >> gvs[]
         >- metis_tac[PERM_REFL] >>
         `2 <= LENGTH (compute_operands inst)` by decide_tac >>
         drule last_two_reorder_perm >> metis_tac[PERM_SYM]) >>
     metis_tac[PERM_REFL]) >>
  qpat_x_assum `(if _ then _ else _) = _` kall_tac >>
  pairarg_tac >> simp[] >>
  IF_CASES_TAC >> simp[]
  >- (strip_tac >> gvs[] >>
      qexistsl_tac [`targets`, `reorder_ops`, `ps4`, `topics`, `emit_ops`, `ps7`] >>
      simp[] >> conj_tac
      >- (gen_tac >> mp_tac (Q.INST [`ps` |-> `ps7`]
            alias_var_mass_release_dead_spills) >> simp[]) >>
      metis_tac[release_dead_spills_plan_holds]) >>
  pairarg_tac >> simp[] >> pairarg_tac >> simp[] >>
  `!x. alias_var_mass x ps9 <= alias_var_mass x ps8` by
    (gen_tac >> qpat_x_assum `(if _ then _ else _) = (_,ps9)` mp_tac >>
     IF_CASES_TAC >> simp[] >> strip_tac >> gvs[] >>
     metis_tac[alias_var_mass_optimistic_swap, pairTheory.SND]) >>
  `!at. plan_holds ps8 at ==> plan_holds ps9 at` by
    (gen_tac >> qpat_x_assum `(if _ then _ else _) = (_,ps9)` mp_tac >>
     IF_CASES_TAC >> simp[] >> strip_tac >> gvs[] >>
     metis_tac[optimistic_swap_plan_holds, pairTheory.SND]) >>
  strip_tac >> gvs[] >>
  qexistsl_tac [`targets`, `reorder_ops`, `ps4`, `topics`, `emit_ops`, `ps7`, `pop_ops`, `ps8`] >>
  simp[] >> conj_tac
  >- (gen_tac >>
      mp_tac (Q.INST [`ps` |-> `ps9`] alias_var_mass_release_dead_spills) >>
      first_x_assum (qspec_then `x` mp_tac) >> decide_tac) >>
  metis_tac[release_dead_spills_plan_holds]
QED

Theorem alias_regular_plan_forward_stages:
  inst.inst_opcode <> JMP /\
  generate_regular_inst_plan liveness dfg cfg fn inst live is_halting next_term lbl ps = (ops,qs) ==>
  ?iops mid selected rops reordered.
    emit_input_plan inst.inst_opcode (compute_operands inst) live ps = (iops,mid) /\
    PERM selected (compute_operands inst) /\
    reorder_plan dfg selected mid = (rops,reordered) /\
    (!x. MEM x live /\
      (plan_holds (reordered with ps_stack :=
         stack_pop (LENGTH (compute_operands inst)) reordered.ps_stack) (Var x) \/
       MEM x inst.inst_outputs) ==> plan_holds qs (Var x))
Proof
  strip_tac >> drule_all alias_regular_plan_stages >> strip_tac >>
  qexistsl_tac [`iops`, `mid`, `targets`, `rops`, `reordered`] >> simp[] >>
  rpt strip_tac >>
  `plan_holds post (Var x)` by
    (drule_at (Pos hd) alias_regular_postprocess_holds >>
     disch_then drule >> simp[]) >>
  metis_tac[]
QED

Theorem alias_regular_plan_holds_live:
  inst.inst_opcode <> JMP /\
  (!op. MEM op (compute_operands inst) /\ is_var_operand op ==> plan_holds ps op) /\
  generate_regular_inst_plan liveness dfg cfg fn inst live is_halting next_term lbl ps = (ops,qs) /\
  MEM x live /\ (plan_holds ps (Var x) \/ MEM x inst.inst_outputs) ==>
  plan_holds qs (Var x)
Proof
  strip_tac >> (drule_all alias_regular_plan_forward_stages >> strip_tac >>
  reverse (Cases_on `plan_holds ps (Var x)`)
  >- metis_tac[] >>
  `PERM (compute_operands inst) selected` by metis_tac[PERM_SYM] >>
  `LENGTH selected = LENGTH (compute_operands inst)` by metis_tac[PERM_LENGTH] >>
  `plan_holds (reordered with ps_stack :=
     stack_pop (LENGTH selected) reordered.ps_stack) (Var x)` by
    metis_tac[alias_emit_reorder_consume_live] >>
  metis_tac[])
QED

Theorem alias_entry_live_param_output:
  codegen_ready_fn fn /\
  MEM x (live_vars_at (liveness_analyze fn)
    (HD fn.fn_blocks).bb_label
    (LENGTH (get_params (HD fn.fn_blocks).bb_instructions))) ==>
  MEM x (MAP (\inst. HD inst.inst_outputs)
    (get_params (HD fn.fn_blocks).bb_instructions))
Proof
  strip_tac >>
  `fn.fn_blocks <> []` by
    (gvs[codegen_ready_fn_def, callLayoutDefsTheory.canonical_param_prefix_def] >>
     Cases_on `fn.fn_blocks` >> gvs[]) >>
  Cases_on `fn.fn_blocks` >> gvs[] >>
  rename1 `fn.fn_blocks = entry::rest` >>
  `lookup_block entry.bb_label fn.fn_blocks = SOME entry` by
    simp[lookup_block_def, FIND_thm] >>
  `collect_phis entry.bb_instructions = []` by
    (gvs[codegen_ready_fn_def, block_entries_ready_def, entry_block_def, NULL_EQ]) >>
  `alias_path_available fn entry.bb_label
    (LENGTH (get_params entry.bb_instructions)) x` by
    (irule alias_live_available_after_phis >> simp[] >>
     gvs[codegen_ready_fn_def]) >>
  qpat_x_assum `alias_path_available _ _ _ _` mp_tac >>
  simp[alias_path_available_def] >>
  disch_then (qspec_then `[entry.bb_label]` mp_tac) >>
  simp[is_fn_path_def, fn_entry_label_def, entry_block_def] >>
  strip_tac >> gvs[] >>
  qspec_then `entry.bb_instructions` strip_assume_tac get_params_suffix >>
  `MEM (EL j entry.bb_instructions) (get_params entry.bb_instructions)` by
    (irule (iffRL MEM_EL) >> qexists_tac `j` >> simp[] >>
     qpat_x_assum `entry.bb_instructions = _ ++ _`
       (fn th => CONV_TAC (LHS_CONV (RAND_CONV (REWR_CONV th)))) >>
     simp[EL_APPEND1]) >>
  `param_insts_from 0 (get_params entry.bb_instructions)` by
    (drule canonical_get_params_layout >> simp[]) >>
  drule param_insts_flat_outputs >> disch_then (SUBST1_TAC o SYM) >>
  simp[MEM_FLAT, MEM_MAP] >>
  metis_tac[inst_defs_def]
QED

Theorem alias_prepare_params_holds_output:
  MEM x (MAP (\inst. HD inst.inst_outputs)
    (get_params (HD fn.fn_blocks).bb_instructions)) /\
  MEM x (live_vars_at liveness (HD fn.fn_blocks).bb_label
    (LENGTH (get_params (HD fn.fn_blocks).bb_instructions))) ==>
  plan_holds (SND (prepare_params_plan liveness fn ps)) (Var x)
Proof
  strip_tac >>
  simp[prepare_params_plan_def, parameter_stack_fold] >>
  IF_CASES_TAC >- gvs[] >>
  pairarg_tac >> simp[] >> pairarg_tac >> simp[] >>
  irule optimistic_swap_plan_holds >> goal_assum (drule_at Any) >>
  qpat_x_assum `popmany_plan _ _ = _` mp_tac >>
  qmatch_goalsub_abbrev_tac `popmany_plan dead_names prepared_state` >>
  `~MEM (Var x) dead_names /\ plan_holds prepared_state (Var x)` by
    (simp[Abbr `dead_names`, Abbr `prepared_state`, MEM_FILTER,
          operand_to_string_def, plan_holds_def, MEM_MAP] >>
     gvs[MEM_MAP] >> metis_tac[]) >>
  drule popmany_plan_plan_holds >>
  metis_tac[pairTheory.SND]
QED

Theorem alias_prepare_params_entry_demand:
  codegen_ready_fn fn /\
  MEM x (live_vars_at (liveness_analyze fn) (HD fn.fn_blocks).bb_label
    (LENGTH (get_params (HD fn.fn_blocks).bb_instructions))) ==>
  plan_holds (SND (prepare_params_plan (liveness_analyze fn) fn ps)) (Var x)
Proof
  metis_tac[alias_prepare_params_holds_output, alias_entry_live_param_output]
QED

Theorem alias_prepare_params_mass_bound:
  alias_var_mass x (SND (prepare_params_plan live fn ps)) <=
  alias_var_mass x ps + LIST_ELEM_COUNT x
    (MAP (\inst. HD inst.inst_outputs)
      (get_params (HD fn.fn_blocks).bb_instructions))
Proof
  simp[prepare_params_plan_def, parameter_stack_fold] >>
  IF_CASES_TAC >- simp[] >>
  pairarg_tac >> simp[] >> pairarg_tac >> simp[] >>
  `alias_var_mass x ps''' <= alias_var_mass x ps''` by
    metis_tac[alias_var_mass_optimistic_swap, pairTheory.SND] >>
  qpat_x_assum `popmany_plan _ _ = _` mp_tac >>
  qmatch_goalsub_abbrev_tac `popmany_plan to_delete prepared` >>
  strip_tac >>
  `alias_var_mass x ps'' <= alias_var_mass x prepared` by
    metis_tac[alias_var_mass_popmany, pairTheory.SND] >>
  gvs[Abbr `prepared`, alias_var_mass_def, elem_count_append,
      LIST_ELEM_COUNT_DEF, FILTER_APPEND, FILTER_MAP, GSYM MAP_FILTER,
      MAP_MAP_o, combinTheory.o_DEF] >>
  metis_tac[arithmeticTheory.LESS_EQ_TRANS]
QED

Theorem alias_prepare_params_parameter_provenance:
  ps.ps_stack = [] /\ ps.ps_spilled = FEMPTY /\
  plan_holds (SND (prepare_params_plan live fn ps)) (Var x) ==>
  MEM x (MAP (\inst. HD inst.inst_outputs)
    (get_params (HD fn.fn_blocks).bb_instructions))
Proof
  strip_tac >> spose_not_then assume_tac >>
  mp_tac (Q.INST [`live` |-> `live`] alias_prepare_params_mass_bound) >>
  gvs[alias_var_mass_def, LIST_ELEM_COUNT_THM,
      GSYM LIST_ELEM_COUNT_MEM, plan_holds_def] >>
  Cases_on `Var x IN FDOM (SND (prepare_params_plan live fn ps)).ps_spilled` >>
  gvs[] >> decide_tac
QED

Theorem stack_poke_retains_other:
  MEM at stk /\ stack_peek d stk <> at ==>
  MEM at (stack_poke d ret stk)
Proof
  simp[MEM_EL, stack_peek_def, stack_poke_def, EL_LUPDATE] >>
  metis_tac[]
QED

Theorem alias_popmany_singleton_retains_stack:
  at <> v /\ MEM at ps.ps_stack ==>
  MEM at (SND (popmany_plan [v] ps)).ps_stack
Proof
  strip_tac >> Cases_on `stack_get_depth v ps.ps_stack` >>
  simp[popmany_plan_def, is_contiguous_top_def, popmany_individual_def,
       QSORT_DEF, PARTITION_DEF, PART_DEF] >>
  drule stack_get_depth_props >> strip_tac >>
  Cases_on `x = 0` >> gvs[]
  >- (irule stack_pop_retains_noninputs >> simp[] >>
      qexists_tac `[stack_peek 0 ps.ps_stack]` >> simp[]) >>
  Cases_on `x = 1` >> simp[] >> pairarg_tac >> simp[] >>
  `ps'.ps_stack = stack_swap x ps.ps_stack` by
    metis_tac[doSwapSimTheory.do_swap_stack_result, pairTheory.SND] >>
  irule stack_pop_retains_noninputs >> simp[stack_swap_mem_unbounded] >>
  qexists_tac `[stack_peek x ps.ps_stack]` >>
  simp[stack_swap_def, stack_peek_def, EL_LUPDATE]
QED

Theorem alias_stack_find_selected:
  !stk d. stack_find p stk = SOME d ==> p (EL d stk)
Proof
  Induct >> simp[stack_find_def] >> gen_tac >>
  Cases_on `p h` >> simp[] >>
  Cases_on `stack_find p stk` >> simp[] >>
  gvs[EL_CONS, GSYM arithmeticTheory.ADD1]
QED

Theorem alias_stack_find_exists:
  !stk. (?d. stack_find p stk = SOME d) <=> EXISTS p stk
Proof
  Induct >> simp[stack_find_def] >>
  Cases_on `p h` >> simp[] >>
  Cases_on `stack_find p stk` >> gvs[]
QED

Theorem alias_phi_depth_selected:
  stack_get_phi_depth inputs stk = SOME d ==>
  MEM (stack_peek d stk) inputs
Proof
  strip_tac >>
  `d < LENGTH stk` by
    (gvs[stack_get_phi_depth_def] >> drule planWfTheory.stack_find_bound >> simp[]) >>
  gvs[stack_get_phi_depth_def] >> drule alias_stack_find_selected >>
  simp[EL_REVERSE, stack_peek_def, arithmeticTheory.PRE_SUB1]
QED

Theorem alias_ready_phi_source_dead_cuts:
  codegen_ready_fn fn /\ fn_reachable fn lbl /\
  lookup_block lbl fn.fn_blocks = SOME bb /\
  k < LENGTH (collect_phis bb.bb_instructions) /\
  MEM x (inst_uses (EL k (collect_phis bb.bb_instructions))) /\
  k < j /\ j <= LENGTH (collect_phis bb.bb_instructions) ==>
  ~MEM x (live_vars_at (liveness_analyze fn) lbl j)
Proof
  strip_tac >>
  `MEM bb fn.fn_blocks /\ collect_phis bb.bb_instructions <> []` by
    (conj_tac >- metis_tac[lookup_block_MEM] >> strip_tac >> gvs[]) >>
  `~EVERY (\b. NULL (collect_phis b.bb_instructions)) fn.fn_blocks` by
    (simp[EVERY_MEM, NULL_EQ, EXISTS_MEM] >> metis_tac[]) >>
  `bb.bb_label = lbl` by metis_tac[lookup_block_label] >>
  `MEM (EL k (collect_phis bb.bb_instructions))
     (collect_phis bb.bb_instructions)` by simp[EL_MEM] >>
  `wf_function fn /\ phi_block_ready (liveness_analyze fn) bb` by
    (fs[codegen_ready_fn_def, phi_operands_ready_def, EVERY_MEM, EXISTS_MEM] >>
     metis_tac[]) >>
  `phi_uses_disjoint (collect_phis bb.bb_instructions) /\
   ~MEM x (live_vars_at (liveness_analyze fn) lbl
     (LENGTH (collect_phis bb.bb_instructions)))` by
    (fs[phi_block_ready_def, EVERY_MEM] >> metis_tac[]) >>
  `cfg_reachable_of (cfg_analyze fn) lbl` by
    metis_tac[fn_reachable_cfg_analyze] >>
  `MEM lbl (cfg_analyze fn).cfg_dfs_pre` by
    (drule cfgAnalysisPropsTheory.cfg_analyze_reachable_sets >>
     simp[pred_setTheory.EXTENSION] >> metis_tac[]) >>
  qspec_then `bb.bb_instructions` strip_assume_tac alias_collect_phis_prefix >>
  strip_tac >>
  `MEM x (live_vars_at (liveness_analyze fn) lbl
     (LENGTH (collect_phis bb.bb_instructions)))` suffices_by simp[] >>
  irule alias_live_no_use_range >> goal_assum (drule_at Any) >>
  simp[] >> qexists_tac `j` >> simp[] >> conj_tac
  >- (qx_gen_tac `n` >> strip_tac >> strip_tac >>
      `EL n bb.bb_instructions = EL n (collect_phis bb.bb_instructions)` by
        metis_tac[EL_APPEND1] >>
      `k = n` by metis_tac[alias_phi_uses_disjoint_index] >>
      decide_tac) >>
  metis_tac[LENGTH_APPEND, arithmeticTheory.LESS_EQ_ADD]
QED

Theorem alias_ready_phi_selected_dead:
  codegen_ready_fn fn /\ fn_reachable fn lbl /\
  lookup_block lbl fn.fn_blocks = SOME bb /\
  k < LENGTH (collect_phis bb.bb_instructions) /\
  stack_get_phi_depth
    (FILTER is_var_operand (EL k (collect_phis bb.bb_instructions)).inst_operands)
    ps.ps_stack = SOME d /\ stack_peek d ps.ps_stack = Var x ==>
  ~MEM x (live_vars_at (liveness_analyze fn) lbl (SUC k))
Proof
  strip_tac >>
  `MEM (Var x) (EL k (collect_phis bb.bb_instructions)).inst_operands` by
    (drule alias_phi_depth_selected >> simp[MEM_FILTER]) >>
  `MEM x (inst_uses (EL k (collect_phis bb.bb_instructions)))` by
    simp[inst_uses_def, passSharedDefsTheory.MEM_operand_vars_eq_Var] >>
  irule alias_ready_phi_source_dead_cuts >>
  goal_assum (drule_at Any) >> simp[] >> qexists_tac `k` >> simp[]
QED

Theorem alias_ready_phi_selected_mass_decreases:
  codegen_ready_fn fn /\ fn_reachable fn lbl /\
  lookup_block lbl fn.fn_blocks = SOME bb /\
  k < LENGTH (collect_phis bb.bb_instructions) /\
  stack_get_phi_depth
    (FILTER is_var_operand (EL k (collect_phis bb.bb_instructions)).inst_operands)
    ps.ps_stack = SOME d /\ stack_peek d ps.ps_stack = Var x /\
  x <> HD (EL k (collect_phis bb.bb_instructions)).inst_outputs ==>
  alias_var_mass x (SND (generate_phi_plan
    (EL k (collect_phis bb.bb_instructions))
    (live_vars_at (liveness_analyze fn) lbl (SUC k)) halting ps)) <
  alias_var_mass x ps
Proof
  strip_tac >>
  `~MEM x (live_vars_at (liveness_analyze fn) lbl (SUC k))` by
    (drule_all alias_ready_phi_selected_dead >> simp[]) >>
  irule alias_phi_dead_selected_mass_decreases >>
  goal_assum (drule_at Any) >> simp[]
QED

Theorem alias_phi_plan_retains_stack:
  ~MEM (Var x) (FILTER is_var_operand inst.inst_operands) /\
  ~MEM x inst.inst_outputs /\ MEM (Var x) ps.ps_stack /\
  inst.inst_outputs = [out] ==>
  MEM (Var x) (SND (generate_phi_plan inst live halting ps)).ps_stack
Proof
  strip_tac >> Cases_on `stack_get_phi_depth
    (FILTER is_var_operand inst.inst_operands) ps.ps_stack`
  >- simp[generate_phi_plan_def] >>
  rename1 `_ = SOME d` >>
  `d < LENGTH ps.ps_stack` by
    (gvs[stack_get_phi_depth_def] >> drule planWfTheory.stack_find_bound >> simp[]) >>
  `stack_peek d ps.ps_stack <> Var x` by
    metis_tac[alias_phi_depth_selected] >>
  simp[generate_phi_plan_def] >>
  Cases_on `MEM (operand_to_string (stack_peek d ps.ps_stack)) live` >> simp[]
  >- (Cases_on `do_dup d ps` >> simp[] >>
      `r.ps_stack = ps.ps_stack ++ [stack_peek d ps.ps_stack]` by
        metis_tac[doSwapSimTheory.do_dup_stack_exact, pairTheory.SND] >>
      `MEM (Var x) (stack_poke 0 (Var out) r.ps_stack)` by
        gvs[stack_poke_def, LUPDATE_APPEND2] >>
      IF_CASES_TAC
      >- (pairarg_tac >> simp[] >>
          `x <> out` by gvs[] >>
          qpat_x_assum `popmany_plan _ _ = _` (mp_tac o Q.AP_TERM `SND`) >>
          simp[] >> disch_then (SUBST1_TAC o SYM) >>
          irule alias_popmany_singleton_retains_stack >> gvs[]) >>
      gvs[]) >>
  `MEM (Var x) (stack_poke d (Var out) ps.ps_stack)` by
    metis_tac[stack_poke_retains_other] >>
  IF_CASES_TAC
  >- (pairarg_tac >> simp[] >> `x <> out` by gvs[] >>
      qpat_x_assum `popmany_plan _ _ = _` (mp_tac o Q.AP_TERM `SND`) >>
          simp[] >> disch_then (SUBST1_TAC o SYM) >>
          irule alias_popmany_singleton_retains_stack >> gvs[]) >>
  gvs[]
QED

Theorem alias_phi_prefix_retains_stack:
  !steps ps.
  EVERY (\p. (?out. (FST p).inst_outputs = [out]) /\
    ~MEM (Var x) (FILTER is_var_operand (FST p).inst_operands) /\
    ~MEM x (FST p).inst_outputs) steps /\ MEM (Var x) ps.ps_stack ==>
  MEM (Var x) (FOLDL (\s p.
    SND (generate_phi_plan (FST p) (SND p) halting s)) ps steps).ps_stack
Proof
  Induct >> simp[] >> rpt gen_tac >> strip_tac >>
  first_x_assum irule >> simp[] >>
  irule alias_phi_plan_retains_stack >> metis_tac[]
QED

Theorem alias_phi_prefix_next_slot:
  EVERY (\p. (?out. (FST p).inst_outputs = [out]) /\
    ~MEM (Var x) (FILTER is_var_operand (FST p).inst_operands) /\
    ~MEM x (FST p).inst_outputs) steps /\ MEM (Var x) ps.ps_stack /\
  MEM (Var x) (FILTER is_var_operand next.inst_operands) ==>
  ?d. stack_get_phi_depth (FILTER is_var_operand next.inst_operands)
    (FOLDL (\s p. SND (generate_phi_plan (FST p) (SND p) halting s))
      ps steps).ps_stack = SOME d
Proof
  strip_tac >> drule_all alias_phi_prefix_retains_stack >>
  simp[stack_get_phi_depth_def, alias_stack_find_exists, EXISTS_MEM] >>
  metis_tac[MEM_REVERSE]
QED

Theorem alias_ready_phi_single_output:
  codegen_ready_fn fn /\ lookup_block lbl fn.fn_blocks = SOME bb /\
  MEM phi (collect_phis bb.bb_instructions) ==>
  ?out. phi.inst_outputs = [out]
Proof
  strip_tac >>
  `MEM bb fn.fn_blocks /\ MEM phi bb.bb_instructions /\ phi.inst_opcode = PHI` by
    metis_tac[lookup_block_MEM, livenessProofsTheory.collect_phis_mem] >>
  `inst_wf phi` by
    (gvs[codegen_ready_fn_def, fn_inst_wf_def, EVERY_MEM] >> metis_tac[]) >>
  `LENGTH phi.inst_outputs = 1` by gvs[inst_wf_def] >>
  Cases_on `phi.inst_outputs` >> gvs[] >> Cases_on `t` >> gvs[]
QED

Theorem alias_ready_phi_prefix_retention:
  codegen_ready_fn fn /\ cfg_reachable_of (cfg_analyze fn) pred /\
  MEM lbl (cfg_succs_of (cfg_analyze fn) pred) /\
  lookup_block pred fn.fn_blocks = SOME pb /\
  lookup_block lbl fn.fn_blocks = SOME bb /\
  MEM x (input_vars_from pred bb.bb_instructions
    (live_vars_at (liveness_analyze fn) lbl 0)) /\
  k < LENGTH (collect_phis bb.bb_instructions) /\
  MEM (pred,x) (phi_pairs (EL k (collect_phis bb.bb_instructions)).inst_operands) ==>
  EVERY (\p. (?out. (FST p).inst_outputs = [out]) /\
    ~MEM (Var x) (FILTER is_var_operand (FST p).inst_operands) /\
    ~MEM x (FST p).inst_outputs)
    (MAP (\j. (EL j (collect_phis bb.bb_instructions), lives j)) (COUNT_LIST k))
Proof
  strip_tac >>
  `phi_uses_disjoint (collect_phis bb.bb_instructions)` by
    (gvs[codegen_ready_fn_def, phi_operands_ready_def, phi_block_ready_def,
         EVERY_MEM, NULL_EQ, phi_uses_disjoint_def] >>
     metis_tac[lookup_block_MEM, phi_uses_disjoint_def]) >>
  `MEM x (inst_uses (EL k (collect_phis bb.bb_instructions)))` by
    (simp[inst_uses_def] >> irule alias_phi_pairs_subset_uses >>
     simp[MEM_MAP] >> qexists_tac `(pred,x)` >> simp[]) >>
  simp[EVERY_MAP, EVERY_MEM, MEM_COUNT_LIST] >> rpt strip_tac
  >- (irule alias_ready_phi_single_output >> metis_tac[EL_MEM, arithmeticTheory.LESS_TRANS])
  >- (gvs[MEM_FILTER, inst_uses_def, passSharedDefsTheory.MEM_operand_vars_eq_Var] >>
      `j < LENGTH (collect_phis bb.bb_instructions)` by decide_tac >>
      `j = k` by metis_tac[alias_phi_uses_disjoint_index, inst_uses_def,
                          passSharedDefsTheory.MEM_operand_vars_eq_Var] >> decide_tac) >>
  `MEM (EL j (collect_phis bb.bb_instructions))
       (collect_phis bb.bb_instructions)` by (simp[EL_MEM] >> decide_tac) >>
  metis_tac[alias_ready_input_not_phi_output, inst_defs_def]
QED

Theorem alias_lineage_join_phi_prefix_slots:
  liveness = liveness_analyze fn /\ dfg = dfg_build_function fn /\
  cfg = cfg_analyze fn /\ codegen_ready_fn fn /\
  lineage_state liveness dfg cfg fn
    (init_cleanup_plan_state ch growth spill_base lbl_ctr) lbl ps /\
  lookup_block lbl fn.fn_blocks = SOME bb /\
  1 < LENGTH (cfg_preds_of cfg lbl) ==>
  ?pred. lineage_entry liveness dfg cfg fn
    (init_cleanup_plan_state ch growth spill_base lbl_ctr) pred lbl ps /\
    MEM pred (cfg_preds_of cfg lbl) /\
    (!k x lives halting.
      k < LENGTH (collect_phis bb.bb_instructions) /\
      MEM (pred,x) (phi_pairs (EL k (collect_phis bb.bb_instructions)).inst_operands) ==>
      MEM (Var x) (FOLDL (\s p.
        SND (generate_phi_plan (FST p) (SND p) halting s)) ps
        (MAP (\j. (EL j (collect_phis bb.bb_instructions), lives j))
          (COUNT_LIST k))).ps_stack /\
      (?d. stack_get_phi_depth
        (FILTER is_var_operand (EL k (collect_phis bb.bb_instructions)).inst_operands)
        (FOLDL (\s p. SND (generate_phi_plan (FST p) (SND p) halting s)) ps
          (MAP (\j. (EL j (collect_phis bb.bb_instructions), lives j))
            (COUNT_LIST k))).ps_stack = SOME d))
Proof
  strip_tac >> drule_all alias_lineage_join_historical_coverage >>
  disch_then (qx_choose_then `pred` strip_assume_tac) >>
  qexists_tac `pred` >> simp[] >>
  `wf_function fn` by gvs[codegen_ready_fn_def] >>
  `cfg_reachable_of (cfg_analyze fn) lbl` by
    metis_tac[alias_lineage_reachable] >>
  `fn_reachable fn lbl` by metis_tac[fn_reachable_cfg_analyze] >>
  `?pb. cfg_reachable_of (cfg_analyze fn) pred /\
    lookup_block pred fn.fn_blocks = SOME pb /\
    MEM lbl (cfg_succs_of (cfg_analyze fn) pred)` by
    (qpat_x_assum `lineage_entry _ _ _ _ _ _ _ _` mp_tac >>
     simp[lineage_entry_def] >> rpt strip_tac >>
     metis_tac[alias_lineage_reachable]) >>
  rpt gen_tac >> strip_tac >>
  `MEM x (input_vars_from pred bb.bb_instructions
    (live_vars_at (liveness_analyze fn) lbl 0))` by
    metis_tac[alias_ready_phi_input_member] >>
  `MEM (Var x) ps.ps_stack` by metis_tac[] >>
  `EVERY (\p. (?out. (FST p).inst_outputs = [out]) /\
    ~MEM (Var x) (FILTER is_var_operand (FST p).inst_operands) /\
    ~MEM x (FST p).inst_outputs)
    (MAP (\j. (EL j (collect_phis bb.bb_instructions), lives j)) (COUNT_LIST k))` by
    (irule alias_ready_phi_prefix_retention >> metis_tac[]) >>
  conj_tac
  >- (irule alias_phi_prefix_retains_stack >> simp[]) >>
  irule alias_phi_prefix_next_slot >> simp[] >>
  qexists_tac `x` >> simp[MEM_FILTER, is_var_operand_def] >>
  `MEM x (inst_uses (EL k (collect_phis bb.bb_instructions)))` by
    (simp[inst_uses_def] >> irule alias_phi_pairs_subset_uses >>
     simp[MEM_MAP] >> qexists_tac `(pred,x)` >> simp[]) >>
  gvs[inst_uses_def, passSharedDefsTheory.MEM_operand_vars_eq_Var]
QED

Theorem alias_lineage_join_phi_prefix_total_slots:
  liveness = liveness_analyze fn /\ dfg = dfg_build_function fn /\
  cfg = cfg_analyze fn /\ codegen_ready_fn fn /\
  lineage_state liveness dfg cfg fn
    (init_cleanup_plan_state ch growth spill_base lbl_ctr) lbl ps /\
  lookup_block lbl fn.fn_blocks = SOME bb /\
  1 < LENGTH (cfg_preds_of cfg lbl) ==>
  !k lives halting. k < LENGTH (collect_phis bb.bb_instructions) ==>
  ?d. stack_get_phi_depth
    (FILTER is_var_operand (EL k (collect_phis bb.bb_instructions)).inst_operands)
    (FOLDL (\s p. SND (generate_phi_plan (FST p) (SND p) halting s)) ps
      (MAP (\j. (EL j (collect_phis bb.bb_instructions), lives j))
        (COUNT_LIST k))).ps_stack = SOME d
Proof
  strip_tac >> drule_all alias_lineage_join_phi_prefix_slots >>
  disch_then (qx_choose_then `pred` strip_assume_tac) >>
  rpt gen_tac >> strip_tac >>
  `wf_function fn /\ def_dominates_uses fn` by gvs[codegen_ready_fn_def] >>
  `?pb. lookup_block pred fn.fn_blocks = SOME pb /\
    MEM lbl (cfg_succs_of (cfg_analyze fn) pred)` by
    (qpat_x_assum `lineage_entry _ _ _ _ _ _ _ _` mp_tac >>
     simp[lineage_entry_def] >> metis_tac[]) >>
  `fn_cfg_edge fn pred lbl` by
    (`MEM pb fn.fn_blocks /\ pb.bb_label = pred` by
       metis_tac[lookup_block_MEM, lookup_block_label] >>
     drule_all cfgAnalysisPropsTheory.cfg_analyze_preserves_bb_succs >>
     strip_tac >> gvs[fn_cfg_edge_def] >> metis_tac[]) >>
  `MEM bb fn.fn_blocks /\ bb.bb_label = lbl /\
    MEM (EL k (collect_phis bb.bb_instructions)) bb.bb_instructions /\
    (EL k (collect_phis bb.bb_instructions)).inst_opcode = PHI` by
    metis_tac[lookup_block_MEM, lookup_block_label,
              livenessProofsTheory.collect_phis_mem, EL_MEM] >>
  `phi_edge_uses_wf fn bb (EL k (collect_phis bb.bb_instructions))` by
    metis_tac[def_dominates_uses_def] >>
  `?x. MEM (pred,x)
    (phi_pairs (EL k (collect_phis bb.bb_instructions)).inst_operands)` by
    (gvs[phi_edge_uses_wf_def] >> PairCases_on `p` >> gvs[] >> metis_tac[]) >>
  metis_tac[]
QED

Theorem alias_phi_plan_holds_live:
  MEM x live /\ plan_holds ps (Var x) ==>
  plan_holds (SND (generate_phi_plan inst live halting ps)) (Var x)
Proof
  strip_tac >> Cases_on `stack_get_phi_depth
    (FILTER is_var_operand inst.inst_operands) ps.ps_stack`
  >- simp[generate_phi_plan_def] >>
  rename1 `_ = SOME d` >>
  `d < LENGTH ps.ps_stack` by
    (gvs[stack_get_phi_depth_def] >> drule planWfTheory.stack_find_bound >> simp[]) >>
  simp[generate_phi_plan_def] >>
  Cases_on `MEM (operand_to_string (stack_peek d ps.ps_stack)) live` >> simp[]
  >- (Cases_on `do_dup d ps` >> simp[] >>
      `r.ps_stack = ps.ps_stack ++ [stack_peek d ps.ps_stack]` by
        metis_tac[doSwapSimTheory.do_dup_stack_exact, pairTheory.SND] >>
      `r.ps_spilled = ps.ps_spilled` by
        (Cases_on `d <= 15` >>
         gvs[do_dup_def] >> rpt (pairarg_tac >> gvs[])) >>
      `plan_holds (r with ps_stack := stack_poke 0 (Var (HD inst.inst_outputs)) r.ps_stack) (Var x)` by
        gvs[plan_holds_def, stack_poke_def, LUPDATE_APPEND2] >>
      IF_CASES_TAC
      >- (pairarg_tac >> simp[] >>
          `~MEM (Var x) [Var (HD inst.inst_outputs)]` by
            (simp[] >> metis_tac[]) >>
          metis_tac[popmany_plan_plan_holds, pairTheory.SND]) >>
      gvs[]) >>
  `stack_peek d ps.ps_stack <> Var x` by
    (strip_tac >> gvs[operand_to_string_def]) >>
  `plan_holds (ps with ps_stack := stack_poke d (Var (HD inst.inst_outputs)) ps.ps_stack) (Var x)` by
    (gvs[plan_holds_def] >> metis_tac[stack_poke_retains_other]) >>
  IF_CASES_TAC
  >- (pairarg_tac >> simp[] >>
      `~MEM (Var x) [Var (HD inst.inst_outputs)]` by
            (simp[] >> metis_tac[]) >>
      metis_tac[popmany_plan_plan_holds, pairTheory.SND]) >>
  gvs[]
QED

Theorem alias_phi_plan_holds_output:
  inst.inst_outputs = [out] /\ MEM out live /\
  stack_get_phi_depth (FILTER is_var_operand inst.inst_operands) ps.ps_stack = SOME d ==>
  plan_holds (SND (generate_phi_plan inst live halting ps)) (Var out)
Proof
  strip_tac >>
  `d < LENGTH ps.ps_stack` by
    (gvs[stack_get_phi_depth_def] >> drule planWfTheory.stack_find_bound >> simp[]) >>
  simp[generate_phi_plan_def] >>
  Cases_on `MEM (operand_to_string (stack_peek d ps.ps_stack)) live` >> simp[]
  >- (Cases_on `do_dup d ps` >> simp[] >>
      `r.ps_stack = ps.ps_stack ++ [stack_peek d ps.ps_stack]` by
        metis_tac[doSwapSimTheory.do_dup_stack_exact, pairTheory.SND] >>
      simp[plan_holds_def, stack_poke_def, LUPDATE_APPEND2]) >>
  simp[plan_holds_def, stack_poke_def] >>
  disj1_tac >> irule (iffRL MEM_EL) >>
  qexists_tac `LENGTH ps.ps_stack - 1 - d` >> simp[EL_LUPDATE]
QED

Theorem alias_phi_fold_holds_live:
  !steps ps. plan_holds ps (Var x) /\
    EVERY (\p. MEM x (SND p)) steps ==>
  plan_holds (FOLDL (\s p.
    SND (generate_phi_plan (FST p) (SND p) halting s)) ps steps) (Var x)
Proof
  Induct >> simp[] >> rpt gen_tac >> strip_tac >>
  first_x_assum irule >> simp[] >>
  irule alias_phi_plan_holds_live >> simp[]
QED

Theorem alias_phi_indexed_fold_holds_output:
  !n ps j. j < n /\ (insts j).inst_outputs = [x] /\
  (?d. stack_get_phi_depth (FILTER is_var_operand (insts j).inst_operands)
    (FOLDL (\s p. SND (generate_phi_plan (FST p) (SND p) halting s)) ps
      (MAP (\i. (insts i,lives i)) (COUNT_LIST j))).ps_stack = SOME d) /\
  (!i. j <= i /\ i < n ==> MEM x (lives i)) ==>
  plan_holds (FOLDL (\s p.
    SND (generate_phi_plan (FST p) (SND p) halting s)) ps
    (MAP (\i. (insts i,lives i)) (COUNT_LIST n))) (Var x)
Proof
  Induct >- simp[] >> rpt gen_tac >> strip_tac >>
  simp[COUNT_LIST_SNOC, MAP_SNOC, FOLDL_SNOC] >>
  Cases_on `j = n`
  >- (gvs[] >> irule alias_phi_plan_holds_output >> simp[] >>
      first_x_assum (qspec_then `j` mp_tac) >> simp[]) >>
  irule alias_phi_plan_holds_live >> conj_tac
  >- (first_x_assum irule >> simp[] >> decide_tac) >>
  first_x_assum irule >> qexists_tac `j` >> simp[]
QED

Theorem alias_lineage_join_phi_fold_lower_coverage:
  liveness = liveness_analyze fn /\ dfg = dfg_build_function fn /\
  cfg = cfg_analyze fn /\ codegen_ready_fn fn /\
  lineage_state liveness dfg cfg fn
    (init_cleanup_plan_state ch growth spill_base lbl_ctr) lbl ps /\
  lookup_block lbl fn.fn_blocks = SOME bb /\
  1 < LENGTH (cfg_preds_of cfg lbl) /\
  n <= LENGTH (collect_phis bb.bb_instructions) /\
  ((plan_holds ps (Var x) /\ (!i. i < n ==> MEM x (lives i))) \/
   (?j. j < n /\ (EL j (collect_phis bb.bb_instructions)).inst_outputs = [x] /\
     (!i. j <= i /\ i < n ==> MEM x (lives i)))) ==>
  plan_holds (FOLDL (\s p.
    SND (generate_phi_plan (FST p) (SND p) halting s)) ps
    (MAP (\i. (EL i (collect_phis bb.bb_instructions), lives i))
      (COUNT_LIST n))) (Var x)
Proof
  strip_tac
  >- (irule alias_phi_fold_holds_live >>
      simp[EVERY_MAP, EVERY_MEM, MEM_COUNT_LIST]) >>
  ho_match_mp_tac alias_phi_indexed_fold_holds_output >>
  qexists_tac `j` >> simp[] >>
  irule alias_lineage_join_phi_prefix_total_slots >>
  metis_tac[arithmeticTheory.LESS_LESS_EQ_TRANS]
QED

Theorem alias_jmp_plan_holds_live:
  inst.inst_opcode = JMP /\ inst.inst_operands = [Label target] /\
  inst.inst_outputs = [] /\
  generate_regular_inst_plan liveness dfg cfg fn inst live is_halting next_term lbl ps = (ops,qs) /\
  MEM x live /\ plan_holds ps (Var x) ==> plan_holds qs (Var x)
Proof
  strip_tac >>
  qpat_x_assum `generate_regular_inst_plan _ _ _ _ _ _ _ _ _ _ = _` mp_tac >>
  simp[generate_regular_inst_plan_def, compute_operands_def,
       asmIRTheory.get_non_label_operands_def, is_label_operand_def, emit_input_plan_def,
       planWfTheory.reorder_plan_nil, stack_pop_def] >>
  Cases_on `join_target_ops liveness fn lbl inst` >> simp[]
  >- (pairarg_tac >> simp[] >> strip_tac >> gvs[] >>
      irule release_dead_spills_plan_holds >> simp[] >>
      gvs[plan_holds_def] >>
      metis_tac[alias_emit_ops_inventory, pairTheory.SND]) >>
  pairarg_tac >> simp[] >> pairarg_tac >> simp[] >>
  qpat_x_assum `(\(restore_ops,ps1'). _) _ = _` mp_tac >>
  pairarg_tac >> simp[] >> pairarg_tac >> simp[] >> strip_tac >> gvs[] >>
  `plan_holds ps1' (Var x)` by metis_tac[restore_spilled_plan_holds] >>
  `plan_holds ps2 (Var x)` by metis_tac[reorder_plan_holds] >>
  strip_tac >> gvs[] >> irule release_dead_spills_plan_holds >> simp[] >>
  gvs[plan_holds_def] >> metis_tac[alias_emit_ops_inventory, pairTheory.SND]
QED

Theorem alias_probe_large_regular_arity:
  inst_wf (mk_inst 0 INVOKE (Label "callee" :: REPLICATE 17 (Lit 0w)) []) /\
  ~codegen_ready_inst (mk_inst 0 INVOKE (Label "callee" :: REPLICATE 17 (Lit 0w)) []) /\
  LENGTH (compute_operands (mk_inst 0 INVOKE (Label "callee" :: REPLICATE 17 (Lit 0w)) [])) = 17 /\
  inst_wf (mk_inst 1 LOG (Lit (17w:256 word) :: REPLICATE 19 (Lit 0w)) []) /\
  ~codegen_ready_inst (mk_inst 1 LOG (Lit (17w:256 word) :: REPLICATE 19 (Lit 0w)) []) /\
  LENGTH (compute_operands (mk_inst 1 LOG (Lit (17w:256 word) :: REPLICATE 19 (Lit 0w)) [])) = 19
Proof
  EVAL_TAC >> simp[wordsTheory.w2n_n2w, wordsTheory.dimword_def]
QED

Theorem alias_regular_plan_var_support:
  inst.inst_opcode <> JMP /\ alias_var_mass x ps <= 1 /\
  (plan_holds ps (Var x) ==> MEM x live \/ MEM (Var x) (compute_operands inst)) /\
  (!op. MEM op (compute_operands inst) /\ is_var_operand op ==> plan_holds ps op) /\
  LENGTH (compute_operands inst) <= 16 /\
  generate_regular_inst_plan liveness dfg cfg fn inst live is_halting next_term lbl ps = (ops,qs) ==>
  plan_holds qs (Var x) ==> MEM x live \/ MEM x inst.inst_outputs
Proof
  strip_tac >> drule_all alias_regular_plan_stages >> strip_tac >>
  `plan_holds (reordered with ps_stack := stack_pop (LENGTH (compute_operands inst)) reordered.ps_stack)
     (Var x) ==> MEM x live` by
    (strip_tac >> drule_all alias_emit_reorder_pop_var_support >> simp[]) >>
  strip_tac >> spose_not_then assume_tac >>
  `alias_var_mass x (reordered with ps_stack := stack_pop (LENGTH (compute_operands inst)) reordered.ps_stack) = 0` by
    metis_tac[alias_var_mass_zero] >>
  `alias_var_mass x emitted = 0` by
    (qpat_x_assum `generate_emit_ops _ _ _ = _`
       (mp_tac o AP_TERM ``\p:stack_op list # plan_state. alias_var_mass x (SND p)``) >>
     simp[alias_var_mass_emit_ops, alias_var_mass_outputs] >>
     `LIST_ELEM_COUNT x inst.inst_outputs = 0` by
       (fs[GSYM LIST_ELEM_COUNT_MEM] >> decide_tac) >> simp[]) >>
  `alias_var_mass x post <= alias_var_mass x emitted` by
    (qpat_x_assum `(if _ then _ else _) = _` mp_tac >>
     IF_CASES_TAC >> simp[] >> strip_tac >> gvs[] >>
     mp_tac (Q.INST [`ps` |-> `emitted`, `to_pop` |-> `MAP Var (FILTER (\out. ~MEM out live) inst.inst_outputs)`] alias_var_mass_popmany) >>
     simp[]) >>
  qpat_x_assum `!x. alias_var_mass x qs <= _` (qspec_then `x` mp_tac) >>
  `alias_var_mass x qs <> 0` by metis_tac[alias_var_mass_zero] >> decide_tac
QED

Theorem alias_regular_plan_support:
  inst.inst_opcode <> JMP /\ alias_var_budget [] ps /\
  (!x. plan_holds ps (Var x) ==> MEM x live \/ MEM (Var x) (compute_operands inst)) /\
  (!op. MEM op (compute_operands inst) /\ is_var_operand op ==> plan_holds ps op) /\
  LENGTH (compute_operands inst) <= 16 /\
  generate_regular_inst_plan liveness dfg cfg fn inst live is_halting next_term lbl ps = (ops,qs) ==>
  !x. plan_holds qs (Var x) ==> MEM x live \/ MEM x inst.inst_outputs
Proof
  rpt strip_tac >> irule alias_regular_plan_var_support >>
  fs[alias_var_budget_def, LIST_ELEM_COUNT_THM] >> metis_tac[]
QED

Definition alias_distinct_probe_fn_def:
  alias_distinct_probe_fn = mk_raw_function "distinct_probe"
    [<| bb_label := "entry"; bb_instructions :=
       [mk_inst 0 CALLDATASIZE [] ["r"];
        mk_inst 1 JMP [Label "use"] []] |>;
     <| bb_label := "use"; bb_instructions :=
       [mk_inst 2 ADD [Var "r"; Var "r"] ["z"];
        mk_inst 3 STOP [] []] |>]
End

Theorem alias_distinct_probe:
  codegen_ready_fn alias_distinct_probe_fn /\
  lookup_block "use" alias_distinct_probe_fn.fn_blocks =
    SOME (EL 1 alias_distinct_probe_fn.fn_blocks) /\
  ~ALL_DISTINCT (input_vars_from "entry"
    (EL 1 alias_distinct_probe_fn.fn_blocks).bb_instructions
    (live_vars_at (liveness_analyze alias_distinct_probe_fn) "use" 0))
Proof
  EVAL_TAC
QED

(* The ready repeated-use edge reaches restoration with only one copy.
   Restoration cannot supply the target multiplicity; the block plan fails. *)
Definition alias_distinct_probe_prefix_def:
  alias_distinct_probe_prefix = SND (generate_regular_inst_plan
    (liveness_analyze alias_distinct_probe_fn)
    (dfg_build_function alias_distinct_probe_fn)
    (cfg_analyze alias_distinct_probe_fn) alias_distinct_probe_fn
    (mk_inst 0 CALLDATASIZE [] ["r"]) ["r"; "r"] F T "entry"
    (init_cleanup_plan_state NONE [] 0 0))
End

Theorem alias_distinct_probe_prefix_eq:
  alias_distinct_probe_prefix =
    (init_cleanup_plan_state NONE [] 0 0) with ps_stack := [Var "r"]
Proof
  EVAL_TAC >> simp[listTheory.SET_TO_LIST_EMPTY]
QED

Theorem alias_distinct_probe_restore_boundary:
  join_target_ops (liveness_analyze alias_distinct_probe_fn)
    alias_distinct_probe_fn "entry" (mk_inst 1 JMP [Label "use"] []) =
      SOME [Var "r"; Var "r"] /\
  alias_distinct_probe_prefix.ps_stack = [Var "r"] /\
  restore_spilled_plan [Var "r"; Var "r"] alias_distinct_probe_prefix =
    ([], alias_distinct_probe_prefix) /\
  ~(LENGTH [Var "r"; Var "r"] <=
    LENGTH (SND (restore_spilled_plan [Var "r"; Var "r"]
      alias_distinct_probe_prefix)).ps_stack)
Proof
  rewrite_tac[alias_distinct_probe_prefix_eq] >> EVAL_TAC
QED

Theorem alias_distinct_probe_planning:
  prepare_params_plan (liveness_analyze alias_distinct_probe_fn)
    alias_distinct_probe_fn (init_cleanup_plan_state NONE [] 0 0) =
    ([], init_cleanup_plan_state NONE [] 0 0) /\
  cfg_preds_of (cfg_analyze alias_distinct_probe_fn) "entry" = [] /\
  live_vars_at (liveness_analyze alias_distinct_probe_fn) "entry" 1 = ["r"; "r"] /\
  generate_block_plan (liveness_analyze alias_distinct_probe_fn)
    (dfg_build_function alias_distinct_probe_fn)
    (cfg_analyze alias_distinct_probe_fn) alias_distinct_probe_fn
    (EL 0 alias_distinct_probe_fn.fn_blocks)
    (init_cleanup_plan_state NONE [] 0 0) = NONE
Proof
  conj_tac >- EVAL_TAC >>
  conj_tac >- EVAL_TAC >>
  conj_tac >- EVAL_TAC >>
  EVAL_TAC >> rewrite_tac[listTheory.SET_TO_LIST_EMPTY] >> EVAL_TAC >>
  rewrite_tac[listTheory.SET_TO_LIST_EMPTY] >> EVAL_TAC
QED

Theorem alias_wf_jmp_shape:
  inst_wf inst /\ inst.inst_opcode = JMP ==>
  inst.inst_outputs = [] /\ compute_operands inst = []
Proof
  strip_tac >> gvs[inst_wf_def] >>
  simp[compute_operands_def, asmIRTheory.get_non_label_operands_def, get_label_def]
QED

Theorem alias_ready_jmp_shape:
  codegen_ready_fn fn /\ lookup_block pred fn.fn_blocks = SOME pb /\
  ~NULL pb.bb_instructions /\ (LAST pb.bb_instructions).inst_opcode = JMP ==>
  (LAST pb.bb_instructions).inst_outputs = [] /\
  compute_operands (LAST pb.bb_instructions) = []
Proof
  strip_tac >> irule alias_wf_jmp_shape >> simp[] >>
  `MEM pb fn.fn_blocks` by metis_tac[lookup_block_MEM] >>
  `fn_inst_wf fn` by fs[codegen_ready_fn_def] >>
  metis_tac[fn_inst_wf_def, LAST_MEM, NULL_EQ]
QED

Theorem alias_jmp_plan_var_mass:
  inst.inst_opcode = JMP /\ inst.inst_outputs = [] /\ compute_operands inst = [] /\
  (!targets. join_target_ops liveness fn lbl inst = SOME targets ==>
     LENGTH targets <= LENGTH (SND (restore_spilled_plan targets ps)).ps_stack) /\
  generate_regular_inst_plan liveness dfg cfg fn inst live is_halting next_term lbl ps = (ops,qs)
  ==> alias_var_mass x qs <= alias_var_mass x ps
Proof
  strip_tac >>
  qpat_x_assum `generate_regular_inst_plan _ _ _ _ _ _ _ _ _ _ = _` mp_tac >>
  simp[generate_regular_inst_plan_def, emit_input_plan_def,
       stack_pop_def] >>
  Cases_on `join_target_ops liveness fn lbl inst`
  >- (simp[] >> pairarg_tac >> simp[] >> strip_tac >> gvs[] >>
      metis_tac[alias_var_mass_release_dead_spills, alias_var_mass_emit_ops, pairTheory.SND]) >>
  simp[] >> pairarg_tac >> simp[] >> pairarg_tac >> simp[] >>
  pairarg_tac >> simp[] >> pairarg_tac >> simp[] >> strip_tac >> gvs[] >>
  Cases_on `reorder_plan dfg x' ps1'` >> gvs[] >>
  `alias_var_mass x ps1' = alias_var_mass x ps` by
    metis_tac[alias_var_mass_restore_spilled, pairTheory.SND] >>
  `alias_var_mass x ps2 <= alias_var_mass x ps1'` by
    metis_tac[alias_var_mass_reorder_plan, pairTheory.SND] >>
  metis_tac[alias_var_mass_release_dead_spills, alias_var_mass_emit_ops, pairTheory.SND,
            arithmeticTheory.LESS_EQ_TRANS]
QED

Theorem alias_regular_plan_var_mass:
  inst.inst_opcode <> JMP /\
  (!op. MEM op (compute_operands inst) /\ is_var_operand op ==> plan_holds ps op) /\
  LENGTH (compute_operands inst) <= 16 /\
  generate_regular_inst_plan liveness dfg cfg fn inst live is_halting next_term lbl ps = (ops,qs) ==>
  alias_var_mass x qs <= alias_var_mass x ps + LIST_ELEM_COUNT x inst.inst_outputs
Proof
  strip_tac >> drule_all alias_regular_plan_stages >> strip_tac >>
  `alias_var_mass x (reordered with ps_stack := stack_pop (LENGTH (compute_operands inst)) reordered.ps_stack)
    <= alias_var_mass x ps` by
    (drule_all alias_emit_reorder_pop_mass >> simp[]) >>
  `alias_var_mass x emitted <= alias_var_mass x ps + LIST_ELEM_COUNT x inst.inst_outputs` by
    (qpat_x_assum `generate_emit_ops _ _ _ = _`
       (mp_tac o AP_TERM ``\p:stack_op list # plan_state. alias_var_mass x (SND p)``) >>
     simp[alias_var_mass_emit_ops, alias_var_mass_outputs]) >>
  `alias_var_mass x post <= alias_var_mass x emitted` by
    (qpat_x_assum `(if _ then _ else _) = _` mp_tac >>
     IF_CASES_TAC >> simp[] >> strip_tac >> gvs[] >>
     metis_tac[alias_var_mass_popmany, pairTheory.SND]) >>
  qpat_x_assum `!x. alias_var_mass x qs <= _` (qspec_then `x` mp_tac) >> decide_tac
QED

Theorem alias_regular_plan_var_budget:
  inst.inst_opcode <> JMP /\ alias_var_mass x ps <= 1 /\
  (!op. MEM op (compute_operands inst) /\ is_var_operand op ==> plan_holds ps op) /\
  LENGTH (compute_operands inst) <= 16 /\
  LIST_ELEM_COUNT x inst.inst_outputs <= 1 /\
  (MEM x inst.inst_outputs ==> ~plan_holds ps (Var x)) /\
  generate_regular_inst_plan liveness dfg cfg fn inst live is_halting next_term lbl ps = (ops,qs) ==>
  alias_var_mass x qs <= 1
Proof
  strip_tac >> drule_all alias_regular_plan_var_mass >>
  disch_then (qspec_then `x` mp_tac) >>
  Cases_on `MEM x inst.inst_outputs`
  >- (`alias_var_mass x ps = 0` by metis_tac[alias_var_mass_zero] >> simp[]) >>
  `LIST_ELEM_COUNT x inst.inst_outputs = 0` by
    (fs[GSYM LIST_ELEM_COUNT_MEM] >> decide_tac) >> simp[]
QED

Theorem alias_distinct_output_count:
  !xs:string list. !x. ALL_DISTINCT xs ==> LIST_ELEM_COUNT x xs <= 1
Proof
  Induct >> simp[LIST_ELEM_COUNT_THM] >> rpt strip_tac >>
  Cases_on `h = x` >> gvs[LIST_ELEM_COUNT_THM]
  >- (fs[GSYM LIST_ELEM_COUNT_MEM] >> decide_tac) >>
  first_x_assum (qspec_then `x` mp_tac) >> simp[]
QED

Theorem alias_ready_parameter_names_distinct:
  codegen_ready_fn fn ==>
  ALL_DISTINCT (MAP (\inst. HD inst.inst_outputs)
    (get_params (HD fn.fn_blocks).bb_instructions))
Proof
  strip_tac >>
  `param_insts_from 0 (get_params (HD fn.fn_blocks).bb_instructions)` by
    (drule canonical_get_params_layout >> simp[]) >>
  drule param_insts_flat_outputs >> disch_then (SUBST1_TAC o SYM) >>
  qspec_then `(HD fn.fn_blocks).bb_instructions` strip_assume_tac get_params_suffix >>
  `ssa_form fn` by gvs[codegen_ready_fn_def] >>
  Cases_on `fn.fn_blocks`
  >- gvs[codegen_ready_fn_def, callLayoutDefsTheory.canonical_param_prefix_def] >>
  gvs[ssa_form_def, fn_insts_def, fn_insts_blocks_def, MAP_APPEND, FLAT_APPEND] >>
  qpat_x_assum `ALL_DISTINCT _` mp_tac >>
  qpat_x_assum `h.bb_instructions = _` (fn th =>
    CONV_TAC (LAND_CONV (ONCE_REWRITE_CONV [th]))) >>
  simp[MAP_APPEND, FLAT_APPEND, ALL_DISTINCT_APPEND]
QED

Theorem alias_prepare_params_entry_budget:
  codegen_ready_fn fn /\ ps.ps_stack = [] /\ ps.ps_spilled = FEMPTY ==>
  alias_var_budget [] (SND (prepare_params_plan (liveness_analyze fn) fn ps))
Proof
  strip_tac >> simp[alias_var_budget_def] >> gen_tac >>
  drule alias_ready_parameter_names_distinct >> strip_tac >>
  drule alias_distinct_output_count >> disch_then (qspec_then `x` mp_tac) >>
  mp_tac (Q.INST [`live` |-> `liveness_analyze fn`]
    alias_prepare_params_mass_bound) >>
  simp[alias_var_mass_def, LIST_ELEM_COUNT_THM] >>
  metis_tac[arithmeticTheory.LESS_EQ_TRANS]
QED

Theorem alias_regular_plan_budget:
  inst.inst_opcode <> JMP /\ alias_var_budget [] ps /\
  (!x. plan_holds ps (Var x) ==> MEM x live \/ MEM (Var x) (compute_operands inst)) /\
  (!op. MEM op (compute_operands inst) /\ is_var_operand op ==> plan_holds ps op) /\
  LENGTH (compute_operands inst) <= 16 /\
  ALL_DISTINCT inst.inst_outputs /\
  (!x. MEM x inst.inst_outputs ==>
    ~plan_holds ps (Var x) /\ ~MEM (Var x) (compute_operands inst)) /\
  generate_regular_inst_plan liveness dfg cfg fn inst live is_halting next_term lbl ps = (ops,qs) ==>
  alias_var_budget [] qs
Proof
  strip_tac >> simp[alias_var_budget_def, LIST_ELEM_COUNT_THM] >> gen_tac >>
  irule alias_regular_plan_var_budget >>
  fs[alias_var_budget_def, LIST_ELEM_COUNT_THM] >>
  metis_tac[alias_distinct_output_count]
QED

Theorem alias_regular_plan_var_live_support:
  inst.inst_opcode <> JMP /\ alias_var_mass x ps <= 1 /\
  (plan_holds ps (Var x) ==> MEM x live \/ MEM (Var x) (compute_operands inst)) /\
  (!op. MEM op (compute_operands inst) /\ is_var_operand op ==> plan_holds ps op) /\
  LENGTH (compute_operands inst) <= 16 /\
  LIST_ELEM_COUNT x inst.inst_outputs <= 1 /\
  (MEM x inst.inst_outputs ==> ~plan_holds ps (Var x)) /\
  (~is_halting \/ LENGTH inst.inst_outputs > 1) /\
  generate_regular_inst_plan liveness dfg cfg fn inst live is_halting next_term lbl ps = (ops,qs) ==>
  plan_holds qs (Var x) ==> MEM x live
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  strip_tac >> spose_not_then assume_tac >>
  `MEM x inst.inst_outputs` by
    (drule_all alias_regular_plan_var_support >> simp[]) >>
  `alias_var_mass x ps = 0` by metis_tac[alias_var_mass_zero] >>
  drule_all alias_regular_plan_stages >> strip_tac >>
  `alias_var_mass x (reordered with ps_stack := stack_pop (LENGTH (compute_operands inst)) reordered.ps_stack) = 0` by
    (drule_all alias_emit_reorder_pop_mass >>
     disch_then (qspec_then `x` mp_tac) >> simp[]) >>
  qmatch_asmsub_abbrev_tac `alias_var_mass x residual = 0` >>
  `alias_var_mass x emitted <= 1` by
    (qpat_assum `generate_emit_ops _ _ _ = _`
       (mp_tac o AP_TERM ``\p:stack_op list # plan_state. alias_var_mass x (SND p)``) >>
     simp[alias_var_mass_emit_ops, alias_var_mass_outputs]) >>
  `Var x NOTIN FDOM emitted.ps_spilled` by
    (`!outs p. (FOLDL (\s out. s with ps_stack := stack_push (Var out) s.ps_stack)
       p outs).ps_spilled = p.ps_spilled` by (Induct >> simp[]) >>
     `Var x NOTIN FDOM residual.ps_spilled` by
       (qpat_x_assum `alias_var_mass x residual = 0` mp_tac >>
        simp[alias_var_mass_def] >> IF_CASES_TAC >> simp[]) >>
     qpat_assum `generate_emit_ops _ _ _ = _`
       (mp_tac o AP_TERM ``\p:stack_op list # plan_state. (SND p).ps_spilled``) >>
     simp[alias_emit_ops_inventory] >> metis_tac[]) >>
  `inst.inst_outputs <> []` by (strip_tac >> fs[]) >>
  qpat_x_assum `(if _ then _ else _) = _` mp_tac >> simp[] >> strip_tac >>
  `alias_var_mass x post = 0` by
    (`MEM (Var x) (MAP Var (FILTER (\out. ~MEM out live) inst.inst_outputs))` by
       simp[MEM_MAP, MEM_FILTER] >>
     drule_all alias_popmany_plan_mass_zero >> simp[]) >>
  qpat_x_assum `!x. alias_var_mass x qs <= _` (qspec_then `x` mp_tac) >>
  `alias_var_mass x qs <> 0` by metis_tac[alias_var_mass_zero] >> decide_tac
QED

Theorem alias_regular_plan_var_residual:
  inst.inst_opcode <> JMP /\ alias_var_mass x ps <= 1 /\
  (!op. MEM op (compute_operands inst) /\ is_var_operand op ==> plan_holds ps op) /\
  LENGTH (compute_operands inst) <= 16 /\
  LIST_ELEM_COUNT x inst.inst_outputs <= 1 /\
  (MEM x inst.inst_outputs ==> ~plan_holds ps (Var x)) /\
  (~is_halting \/ LENGTH inst.inst_outputs > 1) /\
  generate_regular_inst_plan liveness dfg cfg fn inst live is_halting next_term lbl ps = (ops,qs) /\
  plan_holds qs (Var x) ==>
  MEM x live \/ (plan_holds ps (Var x) /\ ~MEM (Var x) (compute_operands inst))
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >> spose_not_then assume_tac >>
  `plan_holds ps (Var x) ==> MEM x live \/ MEM (Var x) (compute_operands inst)` by
    metis_tac[] >>
  drule_all alias_regular_plan_var_live_support >> metis_tac[]
QED

Theorem alias_regular_plan_var_residual_or_halting:
  inst.inst_opcode <> JMP /\ alias_var_mass x ps <= 1 /\
  (!op. MEM op (compute_operands inst) /\ is_var_operand op ==> plan_holds ps op) /\
  LENGTH (compute_operands inst) <= 16 /\
  LIST_ELEM_COUNT x inst.inst_outputs <= 1 /\
  (MEM x inst.inst_outputs ==> ~plan_holds ps (Var x)) /\
  generate_regular_inst_plan liveness dfg cfg fn inst live is_halting next_term lbl ps = (ops,qs) /\
  plan_holds qs (Var x) ==>
  MEM x live \/ (plan_holds ps (Var x) /\ ~MEM (Var x) (compute_operands inst)) \/
  (is_halting /\ LENGTH inst.inst_outputs = 1 /\ MEM x inst.inst_outputs)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  Cases_on `~is_halting \/ LENGTH inst.inst_outputs > 1`
  >- (drule_all alias_regular_plan_var_residual >> metis_tac[]) >>
  Cases_on `MEM x live` >- simp[] >>
  Cases_on `plan_holds ps (Var x) /\ ~MEM (Var x) (compute_operands inst)`
  >- simp[] >>
  `plan_holds ps (Var x) ==> MEM x live \/ MEM (Var x) (compute_operands inst)` by
    metis_tac[] >>
  `MEM x inst.inst_outputs` by metis_tac[alias_regular_plan_var_support] >>
  Cases_on `inst.inst_outputs` >> gvs[arithmeticTheory.GREATER_DEF] >>
  Cases_on `t` >> gvs[]
QED

Theorem alias_regular_plan_live_support:
  inst.inst_opcode <> JMP /\ alias_var_budget [] ps /\
  (!x. plan_holds ps (Var x) ==> MEM x live \/ MEM (Var x) (compute_operands inst)) /\
  (!op. MEM op (compute_operands inst) /\ is_var_operand op ==> plan_holds ps op) /\
  LENGTH (compute_operands inst) <= 16 /\
  ALL_DISTINCT inst.inst_outputs /\
  (!x. MEM x inst.inst_outputs ==>
    ~plan_holds ps (Var x) /\ ~MEM (Var x) (compute_operands inst)) /\
  (~is_halting \/ 1 < LENGTH inst.inst_outputs) /\
  generate_regular_inst_plan liveness dfg cfg fn inst live is_halting next_term lbl ps = (ops,qs) ==>
  !x. plan_holds qs (Var x) ==> MEM x live
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >> rpt strip_tac >>
  `alias_var_mass x ps <= 1` by fs[alias_var_budget_def, LIST_ELEM_COUNT_THM] >>
  `LIST_ELEM_COUNT x inst.inst_outputs <= 1` by metis_tac[alias_distinct_output_count] >>
  `MEM x inst.inst_outputs ==> ~plan_holds ps (Var x)` by simp[] >>
  `plan_holds ps (Var x) ==> MEM x live \/ MEM (Var x) (compute_operands inst)` by simp[] >>
  drule_all (SRULE [arithmeticTheory.GREATER_DEF] alias_regular_plan_var_live_support) >> simp[]
QED

(* Bounded OFFSET inventory-interface probes: syntactic use versus demand. *)
Definition alias_offset_unreachable_fn_def:
  alias_offset_unreachable_fn = mk_raw_function "offset_unreachable"
    [<| bb_label := "entry"; bb_instructions :=
         [mk_inst 0 OFFSET [Lit 0w; Label "entry"] ["v"];
          mk_inst 1 STOP [] []] |>;
     <| bb_label := "unused"; bb_instructions :=
         [mk_inst 2 ASSERT [Var "v"] [];
          mk_inst 3 STOP [] []] |>]
End

Theorem alias_offset_unreachable_probe:
  offset_outputs_used alias_offset_unreachable_fn /\
  ~MEM "v" (live_vars_at (liveness_analyze alias_offset_unreachable_fn) "entry" 1) /\
  ~def_dominates_uses alias_offset_unreachable_fn /\
  ~codegen_ready_fn alias_offset_unreachable_fn
Proof
  EVAL_TAC
QED

Theorem alias_offset_unreachable_readiness_clauses:
  canonical_param_prefix alias_offset_unreachable_fn /\
  wf_function alias_offset_unreachable_fn /\
  fn_inst_wf alias_offset_unreachable_fn /\
  ssa_form alias_offset_unreachable_fn /\
  single_use_form alias_offset_unreachable_fn /\
  cfg_is_normalized (cfg_analyze alias_offset_unreachable_fn) alias_offset_unreachable_fn /\
  block_entries_ready (cfg_analyze alias_offset_unreachable_fn) alias_offset_unreachable_fn /\
  phi_operands_ready alias_offset_unreachable_fn /\
  EVERY (\bb. EVERY codegen_ready_inst bb.bb_instructions) alias_offset_unreachable_fn.fn_blocks /\
  phis_at_joins (cfg_analyze alias_offset_unreachable_fn) alias_offset_unreachable_fn
Proof
  EVAL_TAC
QED

Definition alias_offset_branch_fn_def:
  alias_offset_branch_fn = mk_raw_function "offset_branch"
    [<| bb_label := "entry"; bb_instructions :=
         [mk_inst 0 CALLDATASIZE [] ["cond"];
          mk_inst 1 OFFSET [Lit 0w; Label "use"] ["v"];
          mk_inst 2 JNZ [Var "cond"; Label "use"; Label "skip"] []] |>;
     <| bb_label := "use"; bb_instructions :=
         [mk_inst 3 ASSERT [Var "v"] [];
          mk_inst 4 STOP [] []] |>;
     <| bb_label := "skip"; bb_instructions :=
         [mk_inst 5 STOP [] []] |>]
End

Theorem alias_offset_branch_ready:
  codegen_ready_fn alias_offset_branch_fn
Proof
  EVAL_TAC
QED

Theorem alias_offset_branch_liveness:
  MEM "v" (live_vars_at (liveness_analyze alias_offset_branch_fn) "entry" 2) /\
  MEM "v" (live_vars_at (liveness_analyze alias_offset_branch_fn) "entry" 3) /\
  MEM "v" (input_vars_from "entry"
    (EL 1 alias_offset_branch_fn.fn_blocks).bb_instructions
    (live_vars_at (liveness_analyze alias_offset_branch_fn) "use" 0)) /\
  ~MEM "v" (input_vars_from "entry"
    (EL 2 alias_offset_branch_fn.fn_blocks).bb_instructions
    (live_vars_at (liveness_analyze alias_offset_branch_fn) "skip" 0))
Proof
  EVAL_TAC
QED

(* PHI freshness probes at historical incoming edges, not arbitrary stacks. *)
Definition alias_phi_self_fn_def:
  alias_phi_self_fn = mk_raw_function "phi_self"
    [<| bb_label := "entry"; bb_instructions :=
         [mk_inst 0 CALLDATASIZE [] ["a"];
          mk_inst 1 JMP [Label "header"] []] |>;
     <| bb_label := "header"; bb_instructions :=
         [mk_inst 2 PHI [Label "entry"; Var "a"; Label "back"; Var "p"] ["p"];
          mk_inst 3 JMP [Label "back"] []] |>;
     <| bb_label := "back"; bb_instructions :=
         [mk_inst 4 JMP [Label "header"] []] |>]
End

Theorem alias_phi_self_demand:
  phi_uses_disjoint (collect_phis (EL 1 alias_phi_self_fn.fn_blocks).bb_instructions) /\
  input_vars_from "back" (EL 1 alias_phi_self_fn.fn_blocks).bb_instructions
    (live_vars_at (liveness_analyze alias_phi_self_fn) "header" 0) = ["p"] /\
  MEM "p" (live_vars_at (liveness_analyze alias_phi_self_fn) "header" 1) /\
  ~phi_block_ready (liveness_analyze alias_phi_self_fn) (EL 1 alias_phi_self_fn.fn_blocks) /\
  ~codegen_ready_fn alias_phi_self_fn
Proof
  EVAL_TAC
QED

Definition alias_phi_cross_fn_def:
  alias_phi_cross_fn = mk_raw_function "phi_cross"
    [<| bb_label := "entry"; bb_instructions :=
         [mk_inst 0 CALLDATASIZE [] ["a"];
          mk_inst 1 CALLDATASIZE [] ["b"];
          mk_inst 2 JMP [Label "header"] []] |>;
     <| bb_label := "header"; bb_instructions :=
         [mk_inst 3 PHI [Label "entry"; Var "a"; Label "back"; Var "q"] ["p"];
          mk_inst 4 PHI [Label "entry"; Var "b"; Label "back"; Var "p"] ["q"];
          mk_inst 5 JMP [Label "back"] []] |>;
     <| bb_label := "back"; bb_instructions :=
         [mk_inst 6 JMP [Label "header"] []] |>]
End

Theorem alias_phi_cross_demand:
  phi_uses_disjoint (collect_phis (EL 1 alias_phi_cross_fn.fn_blocks).bb_instructions) /\
  MEM "p" (input_vars_from "back" (EL 1 alias_phi_cross_fn.fn_blocks).bb_instructions
    (live_vars_at (liveness_analyze alias_phi_cross_fn) "header" 0)) /\
  MEM "q" (input_vars_from "back" (EL 1 alias_phi_cross_fn.fn_blocks).bb_instructions
    (live_vars_at (liveness_analyze alias_phi_cross_fn) "header" 0)) /\
  MEM "p" (live_vars_at (liveness_analyze alias_phi_cross_fn) "header" 2) /\
  MEM "q" (live_vars_at (liveness_analyze alias_phi_cross_fn) "header" 2) /\
  ~phi_block_ready (liveness_analyze alias_phi_cross_fn) (EL 1 alias_phi_cross_fn.fn_blocks) /\
  ~codegen_ready_fn alias_phi_cross_fn
Proof
  EVAL_TAC
QED

Theorem alias_phi_loop_readiness_clauses:
  EVERY (\fn.
    canonical_param_prefix fn /\ wf_function fn /\ fn_inst_wf fn /\
    ssa_form fn /\ def_dominates_uses fn /\ single_use_form fn /\
    cfg_is_normalized (cfg_analyze fn) fn /\
    block_entries_ready (cfg_analyze fn) fn /\
    EVERY (\bb. EVERY codegen_ready_inst bb.bb_instructions) fn.fn_blocks /\
    offset_outputs_used fn /\ phis_at_joins (cfg_analyze fn) fn /\
    ~phi_operands_ready fn /\
    cfg_preds_of (cfg_analyze fn) "entry" = [] /\
    cfg_succs_of (cfg_analyze fn) "entry" = ["header"] /\
    cfg_succs_of (cfg_analyze fn) "header" = ["back"] /\
    cfg_succs_of (cfg_analyze fn) "back" = ["header"])
    [alias_phi_self_fn; alias_phi_cross_fn]
Proof
  EVAL_TAC
QED

Definition alias_phi_fresh_fn_def:
  alias_phi_fresh_fn = mk_raw_function "phi_fresh"
    [<| bb_label := "entry"; bb_instructions :=
         [mk_inst 0 CALLDATASIZE [] ["a"];
          mk_inst 1 CALLDATASIZE [] ["b"];
          mk_inst 2 CALLDATASIZE [] ["cond"];
          mk_inst 3 JNZ [Var "cond"; Label "left"; Label "right"] []] |>;
     <| bb_label := "left"; bb_instructions := [mk_inst 4 JMP [Label "join"] []] |>;
     <| bb_label := "right"; bb_instructions := [mk_inst 5 JMP [Label "join"] []] |>;
     <| bb_label := "join"; bb_instructions :=
         [mk_inst 6 PHI [Label "left"; Var "a"; Label "right"; Var "b"] ["p"];
          mk_inst 7 ASSERT [Var "p"] [];
          mk_inst 8 STOP [] []] |>]
End

Theorem alias_phi_fresh_control:
  codegen_ready_fn alias_phi_fresh_fn /\
  phi_uses_disjoint (collect_phis (EL 3 alias_phi_fresh_fn.fn_blocks).bb_instructions) /\
  phi_block_ready (liveness_analyze alias_phi_fresh_fn) (EL 3 alias_phi_fresh_fn.fn_blocks) /\
  live_vars_at (liveness_analyze alias_phi_fresh_fn) "join" 1 = ["p"] /\
  input_vars_from "left" (EL 3 alias_phi_fresh_fn.fn_blocks).bb_instructions
    (live_vars_at (liveness_analyze alias_phi_fresh_fn) "join" 0) = ["a"] /\
  input_vars_from "right" (EL 3 alias_phi_fresh_fn.fn_blocks).bb_instructions
    (live_vars_at (liveness_analyze alias_phi_fresh_fn) "join" 0) = ["b"]
Proof
  EVAL_TAC
QED

(* Two-PHI loop checks the actual lower input trigger, on both entry and
   loop-carried edges, independently of the conditional stack interface. *)
Definition alias_phi_trigger_fn_def:
  alias_phi_trigger_fn = mk_raw_function "phi_trigger"
    [<| bb_label := "entry"; bb_instructions :=
         [mk_inst 0 CALLDATASIZE [] ["a"];
          mk_inst 1 CALLDATASIZE [] ["b"];
          mk_inst 2 JMP [Label "header"] []] |>;
     <| bb_label := "header"; bb_instructions :=
         [mk_inst 3 PHI [Label "entry"; Var "a"; Label "back"; Var "n"] ["p"];
          mk_inst 4 PHI [Label "entry"; Var "b"; Label "back"; Var "m"] ["q"];
          mk_inst 5 ASSERT [Var "p"] [];
          mk_inst 6 ASSERT [Var "q"] [];
          mk_inst 7 JMP [Label "back"] []] |>;
     <| bb_label := "back"; bb_instructions :=
         [mk_inst 8 ASSIGN [Lit 1w] ["n"];
          mk_inst 9 ASSIGN [Lit 2w] ["m"];
          mk_inst 10 JMP [Label "header"] []] |>]
End

Theorem alias_phi_trigger_ready_probe:
  codegen_ready_fn alias_phi_trigger_fn /\
  cfg_reachable_of (cfg_analyze alias_phi_trigger_fn) "entry" /\
  cfg_reachable_of (cfg_analyze alias_phi_trigger_fn) "back" /\
  MEM "header" (cfg_succs_of (cfg_analyze alias_phi_trigger_fn) "entry") /\
  MEM "header" (cfg_succs_of (cfg_analyze alias_phi_trigger_fn) "back")
Proof
  EVAL_TAC
QED

Theorem alias_phi_trigger_input_probe:
  EVERY (\pred. EVERY (\phi. ?x.
    MEM (pred,x) (phi_pairs phi.inst_operands) /\
    MEM x (input_vars_from pred
      (EL 1 alias_phi_trigger_fn.fn_blocks).bb_instructions
      (live_vars_at (liveness_analyze alias_phi_trigger_fn) "header" 0)))
    (collect_phis (EL 1 alias_phi_trigger_fn.fn_blocks).bb_instructions))
    ["entry"; "back"] /\
  EVERY (\x. MEM x
    (live_vars_at (liveness_analyze alias_phi_trigger_fn) "header" 0))
    ["a"; "b"; "n"; "m"] /\
  EVERY (\phi. EVERY (\x. ~MEM x phi.inst_outputs) ["a"; "b"; "n"; "m"])
    (collect_phis (EL 1 alias_phi_trigger_fn.fn_blocks).bb_instructions)
Proof
  EVAL_TAC >> simp[]
QED

Definition alias_collision_fn_def:
  alias_collision_fn = mk_raw_function "collision"
    [<| bb_label := "E"; bb_instructions :=
       [mk_inst 0 ASSIGN [Lit 7w] ["x"];
        mk_inst 1 ASSIGN [Lit 9w] ["y"];
        mk_inst 2 CALLDATASIZE [] ["c"];
        mk_inst 3 JNZ [Var "c"; Label "A"; Label "B"] []] |>;
     <| bb_label := "A"; bb_instructions := [mk_inst 4 JMP [Label "J"] []] |>;
     <| bb_label := "B"; bb_instructions := [mk_inst 5 JMP [Label "J"] []] |>;
     <| bb_label := "J"; bb_instructions :=
       [mk_inst 6 PHI [Label "A"; Var "x"; Label "B"; Var "y"] ["p"];
        mk_inst 7 ASSIGN [Var "x"] ["q"];
        mk_inst 8 JMP [Label "K"] []] |>;
     <| bb_label := "K"; bb_instructions :=
       [mk_inst 9 MSTORE [Lit 0w; Var "p"] [];
        mk_inst 10 MSTORE [Lit 32w; Var "q"] [];
        mk_inst 11 STOP [] []] |>]
End

Theorem alias_collision_normalize:
  normalize_operand (dfg_build_function alias_collision_fn) [] (Var "x") = Lit 7w
Proof
  EVAL_TAC
QED

Theorem alias_collision_ready_probe:
  ~codegen_ready_fn alias_collision_fn
Proof
  simp[codegen_ready_fn_def] >> EVAL_TAC
QED

Theorem alias_collision_phi_obstruction:
  ~phi_operands_ready alias_collision_fn
Proof
  EVAL_TAC
QED

Definition alias_none_fn_def:
  alias_none_fn = mk_raw_function "none_probe"
    [<| bb_label := "E"; bb_instructions :=
       [mk_inst 0 ASSIGN [Lit 7w] ["x"];
        mk_inst 1 ASSIGN [Lit 9w] ["y"];
        mk_inst 2 CALLDATASIZE [] ["c"];
        mk_inst 3 JNZ [Var "c"; Label "A"; Label "B"] []] |>;
     <| bb_label := "A"; bb_instructions := [mk_inst 4 JMP [Label "J"] []] |>;
     <| bb_label := "B"; bb_instructions := [mk_inst 5 JMP [Label "J"] []] |>;
     <| bb_label := "J"; bb_instructions :=
       [mk_inst 7 ASSIGN [Var "x"] ["q"];
        mk_inst 8 JMP [Label "K"] []] |>;
     <| bb_label := "K"; bb_instructions :=
       [mk_inst 10 MSTORE [Lit 32w; Var "q"] [];
        mk_inst 11 STOP [] []] |>]
End

Theorem alias_none_ready:
  codegen_ready_fn alias_none_fn /\
  normalize_operand (dfg_build_function alias_none_fn) [] (Var "x") = Lit 7w
Proof
  EVAL_TAC
QED


Theorem alias_input_vars_no_phis:
  collect_phis instrs = [] ==>
  input_vars_from pred instrs live = live
Proof
  simp[input_vars_from_def]
QED

Theorem alias_entry_demand_collision_probe:
  input_vars_from "b"
    [mk_inst 10 PHI [Label "a"; Var "x"; Label "b"; Var "y"] ["p"];
     mk_inst 11 ASSIGN [Var "x"] ["q"]] ["x"; "y"] = ["y"] /\
  ~MEM "x" (input_vars_from "b"
    [mk_inst 10 PHI [Label "a"; Var "x"; Label "b"; Var "y"] ["p"];
     mk_inst 11 ASSIGN [Var "x"] ["q"]] ["x"; "y"]) /\
  MEM "x" (inst_uses (mk_inst 11 ASSIGN [Var "x"] ["q"]))
Proof
  EVAL_TAC
QED

(* Entry-demand producer audit (C1.20.3).
   alias_entry_demand_collision_probe checks a genuine omission from the
   selected-input list, NOT an omission from a reachable planner state.
   Thus membership of x in ordinary uses does not justify invoking the
   frozen selected-input ownership premise. In this example that premise
   gives heldness/equality of y only. If x is already held, the separate
   frozen equality premise DOES give its entry alias equality.

   Existing interfaces do not supply that missing antecedent:
   - alias_input_vars_from_partition is elimination from membership in
     input_vars_from, not introduction of ordinary survivors.
   - alias_build_phi_maps_absent_uses requires the source-map lookup to be
     NONE (plus well-formed PHIs). Here x has a SOME lookup, so this theorem
     cannot remove the collision.
   - alias_phi_plan_holds_live requires MEM x live AND plan_holds ps (Var x).
     It preserves existing heldness; it cannot establish entry heldness.
   - alias_phi_plan_holds_output requires a singleton output, output liveness
     AND a successful stack_get_phi_depth. It does not produce x in this
     example, where x is an input, not the PHI output p.
   generate_phi_plan itself returns ps unchanged if stack_get_phi_depth is
   NONE. Otherwise it renames a found stack source, duplicating it first
   when that source is live afterwards; spills are not searched as sources.
   Consequently it preserves an already-held ordinary survivor but supplies
   no independent entry-heldness producer for an omitted survivor.

   Required unresolved implication: for every ordinary survivor actually
   needed by the eventual semantic proof but omitted by input_vars_from,
   derive plan_holds ps (Var x) from the frozen lineage/block-plan premises,
   or prove that this survivor need not be demanded to establish any final
   held alias. No unconditional physical PHI demand is implied by this audit.

   NONE audit: lineage_state's entry/step constructors mention planner
   states, CFG and DFS plans only; neither mentions a runtime state or
   vs_prev_bb. lineage_entry names a static predecessor but the frozen
   theorem assumes lineage_state, not its correspondence to vs_prev_bb.
   Therefore prev=NONE must not be identified with function entry. With no
   PHIs alias_input_vars_no_phis computes input_vars_from as identity, but
   the frozen selected-input ownership premise is still vacuous when prev
   is NONE. The same missing heldness-or-unneeded-demand implication must
   cover that case. This audit supplies no target counterexample and does
   not validate the proposed universal live-prefix base case.
*)

Definition alias_probe_phis_def:
  alias_probe_phis =
    [mk_inst 10 PHI [Label "left"; Var "a"; Label "right"; Var "b"] ["p"];
     mk_inst 11 PHI [Label "left"; Var "c"; Label "right"; Var "d"] ["q"]]
End

Theorem alias_probe_phi_static_edges:
  phi_uses_disjoint alias_probe_phis /\
  input_vars_from "left" alias_probe_phis ["a"; "b"; "c"; "d"; "r"] = ["a"; "c"; "r"] /\
  input_vars_from "right" alias_probe_phis ["a"; "b"; "c"; "d"; "r"] = ["b"; "d"; "r"]
Proof
  EVAL_TAC
QED

Theorem alias_probe_phi_prefix_ownership:
  (SND (generate_phi_plan (HD alias_probe_phis) ["c"; "d"; "r"] F
    ((init_plan_state 0) with ps_stack := [Var "r"; Var "a"; Var "c"]))).ps_stack =
    [Var "r"; Var "c"] /\
  FILTER (\at. MEM at [Var "c"; Var "d"])
    (SND (generate_phi_plan (HD alias_probe_phis) ["c"; "d"; "r"] F
      ((init_plan_state 0) with ps_stack := [Var "r"; Var "a"; Var "c"]))).ps_stack =
    [Var "c"] /\
  (SND (generate_phi_plan (EL 1 alias_probe_phis) ["q"; "r"] F
    (SND (generate_phi_plan (HD alias_probe_phis) ["c"; "d"; "r"] F
      ((init_plan_state 0) with ps_stack := [Var "r"; Var "a"; Var "c"]))))).ps_stack =
    [Var "r"; Var "q"] /\
  (SND (generate_phi_plan (HD alias_probe_phis) ["c"; "d"; "r"] F
    ((init_plan_state 0) with ps_stack := [Var "r"; Var "a"; Var "c"]))).ps_spilled = FEMPTY
Proof
  EVAL_TAC
QED

Theorem alias_probe_phi_prefix_live_and_spilled:
  (SND (generate_phi_plan (EL 1 alias_probe_phis) ["p"; "q"; "r"] F
    (SND (generate_phi_plan (HD alias_probe_phis) ["p"; "c"; "r"] F
      ((init_plan_state 0) with ps_stack := [Var "r"; Var "a"; Var "c"]))))).ps_stack =
    [Var "r"; Var "p"; Var "q"] /\
  (SND (generate_phi_plan (EL 1 alias_probe_phis) ["p"; "q"; "r"] F
    (SND (generate_phi_plan (HD alias_probe_phis) ["p"; "c"; "r"] F
      ((init_plan_state 0) with <| ps_stack := [Var "r"; Var "a"];
        ps_spilled := FEMPTY |+ (Var "c",0) |>))))).ps_stack =
    [Var "r"; Var "p"]
Proof
  EVAL_TAC
QED

(* Input disjointness alone supplies neither output freshness nor static
   edge choice. In loops SSA alone also permits an output on a backedge.
   A proposed freshness proof must additionally use phi_block_ready's
   dead-after-prefix condition and a liveness witness from the backedge;
   that proof remains an obligation, not a consequence of these fixtures. *)
Theorem alias_probe_phi_disjoint_not_fresh:
  phi_uses_disjoint
    [mk_inst 10 PHI [Label "left"; Var "a"; Label "right"; Var "b"] ["c"];
     mk_inst 11 PHI [Label "left"; Var "c"; Label "right"; Var "d"] ["q"]] /\
  MEM (Var "c") (FILTER is_var_operand
    (mk_inst 11 PHI [Label "left"; Var "c"; Label "right"; Var "d"] ["q"]).inst_operands)
Proof
  EVAL_TAC
QED

(* Proposed remaining-PHI preservation interface: disjoint selected input
   lists A,B, FILTER A stack = [Var a], FILTER B stack = [Var b], no
   incoming spill keys, a dead at this step, output not in A or B and not
   already held. After the step FILTER B stack = [Var b], no B spills,
   and no A held (the latter is alias_phi_singleton_consumed).
   Output freshness needs its own codegen_ready/SSA/liveness boundary.
   Poke preserves the B filter, but optional pop can move the B slot;
   preserve a FILTER singleton, not its absolute depth. The computation
   above exercises that movement with a carried residual r. *)


Theorem plan_holds_cleanup_update[simp]:
  plan_holds
    (ps with <| ps_cleanup_height := h; ps_cleanup_promised := promised |>) at
  <=> plan_holds ps at
Proof
  simp[plan_holds_def]
QED

Theorem plan_holds_inventory_update[simp]:
  plan_holds (ps with <| ps_stack := stk; ps_spilled := spilled |>) at
  <=> MEM at stk \/ at IN FDOM spilled
Proof
  simp[plan_holds_def]
QED

Theorem plan_holds_init_cleanup[simp]:
  ~plan_holds (init_cleanup_plan_state ch growth spill_base lbl_ctr) at
Proof
  simp[plan_holds_def, init_cleanup_plan_state_def, init_plan_state_def]
QED

(* A successful PHI plan does not, by itself, establish demand coverage. *)
Theorem generate_phi_plan_absent_slot:
  stack_get_phi_depth (FILTER is_var_operand inst.inst_operands) ps.ps_stack =
    NONE ==>
  generate_phi_plan inst next_liveness is_halting ps = ([], ps)
Proof
  simp[generate_phi_plan_def]
QED

(* OFFSET bypasses dead-output filtering. Such names must not be confused
   with nontrivial ASSIGN aliases by a static support invariant. *)
Theorem generate_offset_plan_holds_output:
  inst.inst_operands = [Lit n; Label lbl] /\ inst.inst_outputs = [out] ==>
  plan_holds (SND (generate_offset_plan inst ps)) (Var out)
Proof
  simp[generate_offset_plan_def, plan_holds_def, stackModelTheory.stack_push_def]
QED

(* Reachable JNZ spill/PHI diagnostic. Root names are deliberately distinct. *)
Definition alias_spill_probe_names_def:
  alias_spill_probe_names =
    ["x0"; "x1"; "x2"; "x3"; "x4"; "x5"; "x6"; "x7"; "x8"; "x9";
     "x10"; "x11"; "x12"; "x13"; "x14"; "x15"; "x16"; "x17"; "x18"; "x19"]
End

Definition alias_spill_probe_fn_def:
  alias_spill_probe_fn = mk_raw_function "alias_spill_probe"
    [<| bb_label := "E"; bb_instructions :=
      MAPi (\i v. mk_inst i CALLDATASIZE [] [v]) alias_spill_probe_names ++
      [mk_inst 20 ADD [Var "x0"; Var "x1"] ["c"];
       mk_inst 21 JNZ [Var "c"; Label "S"; Label "P"] []] |>;
     <| bb_label := "P"; bb_instructions :=
      [mk_inst 22 PHI [Label "E"; Var "x18"] ["p"];
       mk_inst 23 ASSIGN [Var "p"] ["q"]] ++
      MAPi (\i v. mk_inst (24+i) MSTORE [Lit (n2w (32*i)); Var v] [])
        ("q" :: FILTER (\v. v <> "x18") (TL (TL alias_spill_probe_names))) ++
      [mk_inst 43 STOP [] []] |>;
     <| bb_label := "S"; bb_instructions := [mk_inst 44 STOP [] []] |>]
End

Definition alias_spill_probe_live_def:
  alias_spill_probe_live = liveness_analyze alias_spill_probe_fn
End

Theorem alias_spill_probe_rejected:
  ~phis_at_joins (cfg_analyze alias_spill_probe_fn) alias_spill_probe_fn /\
  ~codegen_ready_fn alias_spill_probe_fn
Proof
  EVAL_TAC
QED

Definition alias_spill_probe_entry_result_def:
  alias_spill_probe_entry_result = generate_block_plan
    alias_spill_probe_live (dfg_build_function alias_spill_probe_fn)
    (cfg_analyze alias_spill_probe_fn) alias_spill_probe_fn
    (HD alias_spill_probe_fn.fn_blocks) (init_cleanup_plan_state NONE [] 0 0)
End

val () = computeLib.upd_compset
  (computeLib.add_thms [alistTheory.fmap_to_alist_FEMPTY]);

Theorem alias_spill_probe_edge_demand:
  cfg_succs_of (cfg_analyze alias_spill_probe_fn) "E" = ["P"; "S"] /\
  cfg_preds_of (cfg_analyze alias_spill_probe_fn) "P" = ["E"] /\
  MEM "x18" (live_vars_at alias_spill_probe_live "E" 22) /\
  MEM "x18" (input_vars_from "E"
    (EL 1 alias_spill_probe_fn.fn_blocks).bb_instructions
    (live_vars_at alias_spill_probe_live "P" 0))
Proof
  EVAL_TAC
QED

Theorem alias_spill_probe_selected_phi:
  MEM (mk_inst 22 PHI [Label "E"; Var "x18"] ["p"])
    (collect_phis (EL 1 alias_spill_probe_fn.fn_blocks).bb_instructions) /\
  MEM ("E", "x18") (phi_pairs [Label "E"; Var "x18"])
Proof
  EVAL_TAC
QED

(* Keep release opaque until its concrete live-key premise can be checked. *)
fun alias_release_conv tm =
  let
    val (_, args) = strip_comb tm
    val th = SPECL args jp_release_live
    val hyp = fst (dest_imp (concl th))
    val hth = EQT_ELIM
      ((SIMP_CONV (srw_ss())
          [finite_mapTheory.FDOM_FUPDATE, finite_mapTheory.FDOM_FEMPTY,
           boolTheory.DISJ_IMP_THM, boolTheory.FORALL_AND_THM] THENC EVAL) hyp)
  in MP th hth end;
val alias_rel_c = ``stackPlanOps$release_dead_spills``;
val () =
  let
    val rules = List.concat (List.concat (map
      (fn (_,xs) => map (fn clauses.RRules ths => ths
                          | clauses.Conversion _ => []) xs)
      (computeLib.listItems (computeLib.the_compset ()))))
    val callers = List.filter (fn th =>
      let val (_,body) = strip_forall (concl th)
          val (_,r) = boolSyntax.dest_eq body
      in can (find_term (aconv alias_rel_c)) r end
      handle HOL_ERR _ => false) rules
  in
    computeLib.del_funs [stackPlanOpsTheory.release_dead_spills_def];
    computeLib.add_convs [(alias_rel_c,2,alias_release_conv)];
    computeLib.add_funs callers
  end;

Definition alias_none_e_def:
  alias_none_e = THE (generate_block_plan (liveness_analyze alias_none_fn)
    (dfg_build_function alias_none_fn) (cfg_analyze alias_none_fn) alias_none_fn
    (HD alias_none_fn.fn_blocks) (init_cleanup_plan_state NONE [] 0 0))
End

Definition alias_none_a_def:
  alias_none_a = THE (generate_block_plan (liveness_analyze alias_none_fn)
    (dfg_build_function alias_none_fn) (cfg_analyze alias_none_fn) alias_none_fn
    (EL 2 alias_none_fn.fn_blocks) (SND alias_none_e))
End

Theorem alias_none_e_plan:
  generate_block_plan (liveness_analyze alias_none_fn)
    (dfg_build_function alias_none_fn) (cfg_analyze alias_none_fn) alias_none_fn
    (HD alias_none_fn.fn_blocks) (init_cleanup_plan_state NONE [] 0 0) =
    SOME alias_none_e
Proof
  EVAL_TAC
QED

Theorem alias_none_a_plan:
  generate_block_plan (liveness_analyze alias_none_fn)
    (dfg_build_function alias_none_fn) (cfg_analyze alias_none_fn) alias_none_fn
    (EL 2 alias_none_fn.fn_blocks) (SND alias_none_e) = SOME alias_none_a
Proof
  EVAL_TAC
QED

Theorem alias_none_inventory_probe:
  plan_holds (SND alias_none_a) (Var "x")
Proof
  EVAL_TAC
QED

Theorem alias_none_cfg_edges:
  cfg_succs_of (cfg_analyze alias_none_fn) "E" = ["B"; "A"] /\
  cfg_succs_of (cfg_analyze alias_none_fn) "B" = ["J"]
Proof
  EVAL_TAC
QED

Theorem alias_none_dfs_a:
  dfs_aux_call (liveness_analyze alias_none_fn)
    (dfg_build_function alias_none_fn) (cfg_analyze alias_none_fn) alias_none_fn
    (init_cleanup_plan_state NONE [] 0 0) ["B"] ["E"] (SND alias_none_e)
Proof
  `SND alias_none_e = (SND alias_none_e) with
    <|ps_stack := (SND alias_none_e).ps_stack;
      ps_spilled := (SND alias_none_e).ps_spilled|>` by simp[] >>
  pop_assum SUBST1_TAC >> irule dfs_aux_call_branch >>
  qexists_tac `["A"]` >>
  rewrite_tac[GSYM (cj 1 alias_none_cfg_edges)] >>
  irule dfs_aux_call_succs >> simp[] >>
  qexistsl_tac [`HD alias_none_fn.fn_blocks`, `FST alias_none_e`,
    `init_cleanup_plan_state NONE [] 0 0`, `[]`] >>
  simp[alias_none_e_plan] >> conj_tac >- EVAL_TAC >>
  irule dfs_aux_call_entry >> EVAL_TAC
QED

Theorem alias_none_dfs_j:
  dfs_aux_call (liveness_analyze alias_none_fn)
    (dfg_build_function alias_none_fn) (cfg_analyze alias_none_fn) alias_none_fn
    (init_cleanup_plan_state NONE [] 0 0) ["J"] ["B"; "E"] (SND alias_none_a)
Proof
  `SND alias_none_a = (SND alias_none_a) with
    <|ps_stack := (SND alias_none_a).ps_stack;
      ps_spilled := (SND alias_none_a).ps_spilled|>` by simp[] >>
  pop_assum SUBST1_TAC >> irule dfs_aux_call_branch >>
  qexists_tac `[]` >>
  rewrite_tac[GSYM (cj 2 alias_none_cfg_edges)] >>
  irule dfs_aux_call_succs >> simp[] >>
  qexistsl_tac [`EL 2 alias_none_fn.fn_blocks`, `FST alias_none_a`,
    `SND alias_none_e`, `[]`] >>
  simp[alias_none_a_plan, alias_none_dfs_a] >> EVAL_TAC
QED

Theorem alias_none_dfs_states:
  dfs_block_state (liveness_analyze alias_none_fn)
    (dfg_build_function alias_none_fn) (cfg_analyze alias_none_fn) alias_none_fn
    (init_cleanup_plan_state NONE [] 0 0) "E" (init_cleanup_plan_state NONE [] 0 0) /\
  dfs_block_state (liveness_analyze alias_none_fn)
    (dfg_build_function alias_none_fn) (cfg_analyze alias_none_fn) alias_none_fn
    (init_cleanup_plan_state NONE [] 0 0) "B" (SND alias_none_e) /\
  dfs_block_state (liveness_analyze alias_none_fn)
    (dfg_build_function alias_none_fn) (cfg_analyze alias_none_fn) alias_none_fn
    (init_cleanup_plan_state NONE [] 0 0) "J" (SND alias_none_a)
Proof
  rewrite_tac[dfs_block_state_def] >> conj_tac
  >- (qexistsl_tac [`[]`,`[]`] >> simp[] >> irule dfs_aux_call_entry >> EVAL_TAC) >>
  conj_tac
  >- (qexistsl_tac [`[]`,`["E"]`] >> simp[alias_none_dfs_a]) >>
  qexistsl_tac [`[]`,`["B"; "E"]`] >> simp[alias_none_dfs_j]
QED

Theorem alias_none_lineage_b:
  lineage_state (liveness_analyze alias_none_fn)
    (dfg_build_function alias_none_fn) (cfg_analyze alias_none_fn) alias_none_fn
    (init_cleanup_plan_state NONE [] 0 0) "B" (SND alias_none_e)
Proof
  `SND alias_none_e = (SND alias_none_e) with
    <|ps_stack := (SND alias_none_e).ps_stack;
      ps_spilled := (SND alias_none_e).ps_spilled|>` by simp[] >>
  pop_assum SUBST1_TAC >> irule lineage_state_step >>
  simp[alias_none_dfs_states] >>
  qexistsl_tac [`HD alias_none_fn.fn_blocks`, `FST alias_none_e`, `NONE`, `"E"`, `F`,
    `init_cleanup_plan_state NONE [] 0 0`, `init_cleanup_plan_state NONE [] 0 0`,
    `SND alias_none_e`] >>
  simp[alias_none_dfs_states, alias_none_e_plan, alias_none_cfg_edges] >>
  conj_tac >- EVAL_TAC >>
  reverse conj_tac
  >- (irule lineage_state_entry >> EVAL_TAC) >>
  `init_cleanup_plan_state NONE [] 0 0 with
    <|ps_cleanup_height := NONE; ps_cleanup_promised := F|> =
    init_cleanup_plan_state NONE [] 0 0` by
      simp[init_cleanup_plan_state_def] >>
  simp[alias_none_e_plan]
QED

Theorem alias_none_lineage_j:
  lineage_state (liveness_analyze alias_none_fn)
    (dfg_build_function alias_none_fn) (cfg_analyze alias_none_fn) alias_none_fn
    (init_cleanup_plan_state NONE [] 0 0) "J" (SND alias_none_a)
Proof
  `SND alias_none_a = (SND alias_none_a) with
    <|ps_stack := (SND alias_none_a).ps_stack;
      ps_spilled := (SND alias_none_a).ps_spilled|>` by simp[] >>
  pop_assum SUBST1_TAC >> irule lineage_state_step >>
  simp[alias_none_dfs_states] >>
  qexistsl_tac [`EL 2 alias_none_fn.fn_blocks`, `FST alias_none_a`, `NONE`, `"B"`, `F`,
    `SND alias_none_e`, `SND alias_none_e`, `SND alias_none_a`] >>
  simp[alias_none_dfs_states, alias_none_a_plan, alias_none_cfg_edges,
       alias_none_lineage_b] >> EVAL_TAC
QED

Theorem alias_none_selected_input:
  input_vars_from "B" (EL 3 alias_none_fn.fn_blocks).bb_instructions
    (live_vars_at (liveness_analyze alias_none_fn) "J" 0) = ["x"] /\
  LENGTH (cfg_preds_of (cfg_analyze alias_none_fn) "J") = 2
Proof
  EVAL_TAC
QED

Definition alias_none_regular_def:
  alias_none_regular = generate_regular_inst_plan (liveness_analyze alias_none_fn)
    (dfg_build_function alias_none_fn) (cfg_analyze alias_none_fn) alias_none_fn
    (mk_inst 7 ASSIGN [Var "x"] ["q"])
    (live_vars_at (liveness_analyze alias_none_fn) "J" 1) F T "J" (SND alias_none_a)
End

Theorem alias_none_regular_inventory:
  plan_holds (SND alias_none_a) (Var "x") /\
  plan_holds (SND alias_none_regular) (Var "q")
Proof
  EVAL_TAC
QED

Definition alias_none_j_result_def:
  alias_none_j_result = generate_block_plan (liveness_analyze alias_none_fn)
    (dfg_build_function alias_none_fn) (cfg_analyze alias_none_fn) alias_none_fn
    (EL 3 alias_none_fn.fn_blocks) (SND alias_none_a)
End

Theorem alias_none_final_inventory:
  IS_SOME alias_none_j_result /\
  plan_holds (SND (THE alias_none_j_result)) (Var "q")
Proof
  EVAL_TAC
QED

Theorem alias_spill_probe_entry_fields:
  IS_SOME alias_spill_probe_entry_result /\
  ~MEM (Var "x18") (SND (THE alias_spill_probe_entry_result)).ps_stack /\
  Var "x18" IN FDOM (SND (THE alias_spill_probe_entry_result)).ps_spilled
Proof
  rpt conj_tac >>
  rewrite_tac[alias_spill_probe_entry_result_def] >>
  CONV_TAC (ONCE_DEPTH_CONV (fn tm =>
    if same_const (fst (strip_comb tm)) ``dfg_build_function`` then EVAL tm else NO_CONV tm)) >>
  CONV_TAC (ONCE_DEPTH_CONV (fn tm =>
    if same_const (fst (strip_comb tm)) ``cfg_analyze`` then EVAL tm else NO_CONV tm)) >>
  CONV_TAC (ONCE_DEPTH_CONV (fn tm =>
    if same_const tm ``alias_spill_probe_live`` then EVAL tm else NO_CONV tm)) >>
  simp[finite_mapTheory.FUNION_FUPDATE_1, finite_mapTheory.FUPDATE_LIST_THM] >>
  EVAL_TAC
QED

Definition alias_spill_probe_after_def:
  alias_spill_probe_after = SND (THE alias_spill_probe_entry_result)
End

Theorem alias_spill_probe_entry_plan:
  generate_block_plan alias_spill_probe_live
    (dfg_build_function alias_spill_probe_fn) (cfg_analyze alias_spill_probe_fn)
    alias_spill_probe_fn (HD alias_spill_probe_fn.fn_blocks)
    (init_cleanup_plan_state NONE [] 0 0) =
    SOME (FST (THE alias_spill_probe_entry_result), alias_spill_probe_after)
Proof
  rewrite_tac[GSYM alias_spill_probe_entry_result_def, alias_spill_probe_after_def] >>
  mp_tac alias_spill_probe_entry_fields >>
  Cases_on `alias_spill_probe_entry_result` >> simp[]
QED

Theorem alias_spill_probe_first_edge:
  dfs_block_state alias_spill_probe_live (dfg_build_function alias_spill_probe_fn)
    (cfg_analyze alias_spill_probe_fn) alias_spill_probe_fn
    (init_cleanup_plan_state NONE [] 0 0) "P" alias_spill_probe_after
Proof
  simp[dfs_block_state_def] >>
  qexistsl_tac [`[]`, `["E"]`] >> simp[] >>
  `alias_spill_probe_after = alias_spill_probe_after with
    <|ps_stack := alias_spill_probe_after.ps_stack;
      ps_spilled := alias_spill_probe_after.ps_spilled|>` by simp[] >>
  pop_assum SUBST1_TAC >>
  irule dfs_aux_call_branch >>
  qexists_tac `["S"]` >>
  rewrite_tac[GSYM (cj 1 alias_spill_probe_edge_demand)] >>
  irule dfs_aux_call_succs >>
  simp[] >>
  qexistsl_tac [`HD alias_spill_probe_fn.fn_blocks`,
    `FST (THE alias_spill_probe_entry_result)`,
    `init_cleanup_plan_state NONE [] 0 0`, `[]`] >>
  simp[alias_spill_probe_entry_plan] >>
  conj_tac >- EVAL_TAC >>
  irule dfs_aux_call_entry >> EVAL_TAC
QED

Theorem alias_spill_probe_lineage:
  lineage_state alias_spill_probe_live (dfg_build_function alias_spill_probe_fn)
    (cfg_analyze alias_spill_probe_fn) alias_spill_probe_fn
    (init_cleanup_plan_state NONE [] 0 0) "P" alias_spill_probe_after
Proof
  `alias_spill_probe_after = alias_spill_probe_after with
    <|ps_stack := alias_spill_probe_after.ps_stack;
      ps_spilled := alias_spill_probe_after.ps_spilled|>` by simp[] >>
  pop_assum SUBST1_TAC >>
  irule lineage_state_step >>
  conj_tac >- ACCEPT_TAC alias_spill_probe_first_edge >>
  qexistsl_tac [`HD alias_spill_probe_fn.fn_blocks`,
    `FST (THE alias_spill_probe_entry_result)`, `NONE`, `"E"`, `F`,
    `init_cleanup_plan_state NONE [] 0 0`,
    `init_cleanup_plan_state NONE [] 0 0`, `alias_spill_probe_after`] >>
  `init_cleanup_plan_state NONE [] 0 0 with
    <|ps_cleanup_height := NONE; ps_cleanup_promised := F|> =
    init_cleanup_plan_state NONE [] 0 0` by EVAL_TAC >>
  simp[alias_spill_probe_entry_plan, alias_spill_probe_edge_demand] >>
  conj_tac >- EVAL_TAC >>
  conj_tac
  >- (simp[dfs_block_state_def] >> qexistsl_tac [`[]`, `[]`] >>
      simp[] >> irule dfs_aux_call_entry >> EVAL_TAC) >>
  irule lineage_state_entry >> EVAL_TAC
QED

Definition alias_spill_probe_clean_def:
  alias_spill_probe_clean = SND (clean_stack_plan alias_spill_probe_live
    (cfg_analyze alias_spill_probe_fn) alias_spill_probe_fn
    (EL 1 alias_spill_probe_fn.fn_blocks) alias_spill_probe_after)
End

Theorem alias_spill_probe_clean_and_phi:
  alias_spill_probe_clean = alias_spill_probe_after /\
  generate_phi_plan (mk_inst 22 PHI [Label "E"; Var "x18"] ["p"])
    (live_vars_at alias_spill_probe_live "P" 1) T alias_spill_probe_clean =
    ([], alias_spill_probe_clean) /\
  ~plan_holds alias_spill_probe_clean (Var "p")
Proof
  `alias_spill_probe_clean = alias_spill_probe_after` by
    (rewrite_tac[alias_spill_probe_clean_def] >>
     CONV_TAC (DEPTH_CONV (fn tm =>
       if same_const tm ``alias_spill_probe_after`` then EVAL tm else NO_CONV tm)) >>
     EVAL_TAC) >>
  simp[] >> conj_tac
  >- (CONV_TAC (ONCE_DEPTH_CONV (fn tm =>
        if same_const (fst (strip_comb tm)) ``live_vars_at`` then EVAL tm else NO_CONV tm)) >>
      EVAL_TAC) >>
  EVAL_TAC
QED

Definition alias_spill_probe_assign_def:
  alias_spill_probe_assign = generate_regular_inst_plan alias_spill_probe_live
    (dfg_build_function alias_spill_probe_fn) (cfg_analyze alias_spill_probe_fn)
    alias_spill_probe_fn (mk_inst 23 ASSIGN [Var "p"] ["q"])
    (live_vars_at alias_spill_probe_live "P" 2) T F "P" alias_spill_probe_clean
End

Theorem alias_spill_probe_assign_fields:
  plan_holds (SND alias_spill_probe_assign) (Var "q") /\
  normalize_operand (dfg_build_function alias_spill_probe_fn) [] (Var "q") = Var "p"
Proof
  EVAL_TAC >> simp[release_dead_spills_def, alias_release_fold_fields]
QED

(* Absent-source end-to-end audit (C1.21.2.1): reuse E0072, not a
   duplicate fixture. alias_spill_probe_clean_and_phi proves that Var p is
   absent from BOTH stack and spill domain (by plan_holds_def). The checked
   alias_spill_probe_assign_fields nevertheless proves that full
   generate_regular_inst_plan retains Var q. Its arguments are explicitly
   alias_spill_probe_live, the built DFG and analyzed CFG of
   alias_spill_probe_fn, instruction 23 ASSIGN p -> q, analyzed next-live
   index 2, first-instruction flag T, halting flag F, label P, and the
   concrete alias_spill_probe_clean state. This is the full planner call,
   not just its consume/push fragment: it includes input emission, reorder
   and optimistic-swap handling. The successful call is not an availability
   certificate. The regular planner pushes outputs after consuming operands;
   missing physical input does not prevent that construction.

   The fixture has a checked static lineage entry (alias_spill_probe_lineage)
   and checked cleanup/PHI behavior, but no general instruction-prefix
   lineage predicate. Here p is a PHI self-root: runtime PHI definition can
   supply its semantic equality without physical heldness. Therefore this
   example does NOT show an alias failure or a frozen-target counterexample.

   Exact residual producer required for the joint proof: whenever full
   regular planning retains an ASSIGN output whose source was not held,
   under the frozen block-entry/lineage/run premises derive semantic framed
   alias equality of that source at the actual runtime instruction prefix
   (or a sufficient backwards trace to initially held equality or a locally
   executed self-root). The producer must cover nontrivial ASSIGN sources,
   not merely this PHI example, and must track intervening root writes.
   Conditional inventory/phi-heldness lemmas require source heldness and
   cannot establish this residual implication. Static lineage constructors
   alone do not relate the runtime predecessor to a chosen static edge.
*)
val () = computeLib.add_funs [stackPlanOpsTheory.release_dead_spills_def];

(* Small computation fixture: an actual DFG, not an assumed equivalence. *)
Definition alias_probe_fn_def:
  alias_probe_fn = mk_raw_function "alias_probe"
    [<| bb_label := "entry"; bb_instructions :=
      [mk_inst 0 PARAM [] ["r"];
       mk_inst 1 ASSIGN [Var "r"] ["a"];
       mk_inst 2 STOP [] []] |>]
End

(* Demand diagnostics use analyzed liveness of this actual function. *)
Definition alias_demand_probe_fn_def:
  alias_demand_probe_fn = mk_raw_function "demand_probe"
    [<| bb_label := "entry"; bb_instructions :=
      [mk_inst 0 PARAM [] ["r"];
       mk_inst 1 PARAM [] ["k"];
       mk_inst 2 ADD [Var "r"; Var "r"] ["z"];
       mk_inst 3 ADD [Var "z"; Var "k"] ["result"];
       mk_inst 4 STOP [] []] |>]
End

Theorem alias_demand_probe_entry_preparation:
  ~plan_holds (init_cleanup_plan_state NONE [] 0 0) (Var "r") /\
  ~plan_holds (init_cleanup_plan_state NONE [] 0 0) (Var "k") /\
  MEM "r" (live_vars_at (liveness_analyze alias_demand_probe_fn) "entry" 2) /\
  MEM "k" (live_vars_at (liveness_analyze alias_demand_probe_fn) "entry" 2) /\
  (!x. MEM x ["r"; "k"] ==>
    plan_holds (SND (prepare_params_plan (liveness_analyze alias_demand_probe_fn)
      alias_demand_probe_fn (init_cleanup_plan_state NONE [] 0 0))) (Var x))
Proof
  EVAL_TAC >> simp[] >> metis_tac[]
QED

Theorem alias_demand_probe_regular_distinct_live:
  MEM "k" (live_vars_at (liveness_analyze alias_demand_probe_fn) "entry" 3) /\
  (!x. MEM x ["z"; "k"] ==>
    plan_holds (SND (generate_regular_inst_plan
      (liveness_analyze alias_demand_probe_fn) (dfg_build_function alias_demand_probe_fn)
      (cfg_analyze alias_demand_probe_fn) alias_demand_probe_fn
      (mk_inst 2 ADD [Var "r"; Var "r"] ["z"])
      (live_vars_at (liveness_analyze alias_demand_probe_fn) "entry" 3)
      T F "entry" ((init_plan_state 0) with ps_stack := [Var "k"; Var "r"]))) (Var x)) /\
  (!x. MEM x ["z"; "k"] ==>
    plan_holds (SND (generate_regular_inst_plan
      (liveness_analyze alias_demand_probe_fn) (dfg_build_function alias_demand_probe_fn)
      (cfg_analyze alias_demand_probe_fn) alias_demand_probe_fn
      (mk_inst 2 ADD [Var "r"; Var "r"] ["z"])
      (live_vars_at (liveness_analyze alias_demand_probe_fn) "entry" 3)
      T F "entry" ((init_plan_state 0) with <| ps_stack := [Var "r"];
        ps_spilled := FEMPTY |+ (Var "k",0) |>))) (Var x))
Proof
  EVAL_TAC >> simp[] >> metis_tac[]
QED

(* The published path predicate permits inter-block exits before the terminator.
   This witnesses only an interface limitation, not analyzed liveness. *)
Definition alias_path_probe_fn_def:
  alias_path_probe_fn = mk_raw_function "path_probe"
    [<| bb_label := "A"; bb_instructions :=
       [mk_inst 0 PARAM [] ["r"];
        mk_inst 1 ASSIGN [Var "r"] ["a"];
        mk_inst 2 JMP [Label "B"] []] |>;
     <| bb_label := "B"; bb_instructions :=
       [mk_inst 3 ADD [Var "a"; Lit 1w] ["b"];
        mk_inst 4 STOP [] []] |>]
End

Theorem alias_path_probe_early_exit:
  cfg_exec_path (cfg_analyze alias_path_probe_fn) [("A",0);("B",0)] /\
  used_before_defined alias_path_probe_fn.fn_blocks "a" [("A",0);("B",0)] /\
  normalize_operand (dfg_build_function alias_path_probe_fn) [] (Var "a") =
    Var "r" /\
  ~MEM "a" (live_vars_at (liveness_analyze alias_path_probe_fn) "A" 0)
Proof
  EVAL_TAC >> qexists_tac `1` >> simp[] >> EVAL_TAC
QED

Theorem alias_probe_normalize:
  normalize_operand (dfg_build_function alias_probe_fn) [] (Var "a") = Var "r"
Proof
  EVAL_TAC
QED

Theorem alias_probe_phi_slots:
  (SND (generate_phi_plan
    (mk_inst 3 PHI [Label "left"; Var "a"; Label "right"; Var "b"] ["p"])
    ["p"] F ((init_plan_state 0) with ps_stack := [Var "a"; Var "b"]))).ps_stack =
    [Var "a"; Var "p"] /\
  (SND (generate_phi_plan
    (mk_inst 3 PHI [Label "left"; Var "a"; Label "right"; Var "b"] ["p"])
    ["p"] F ((init_plan_state 0) with ps_stack := [Var "a"]))).ps_stack =
    [Var "p"]
Proof
  EVAL_TAC
QED

Theorem alias_probe_phi_live_and_dead:
  (SND (generate_phi_plan
    (mk_inst 3 PHI [Label "left"; Var "a"; Label "right"; Var "b"] ["p"])
    ["a"; "p"] F ((init_plan_state 0) with ps_stack := [Var "a"]))).ps_stack =
    [Var "a"; Var "p"] /\
  (SND (generate_phi_plan
    (mk_inst 3 PHI [Label "left"; Var "a"; Label "right"; Var "b"] ["p"])
    [] F ((init_plan_state 0) with ps_stack := [Var "a"]))).ps_stack = [] /\
  (SND (generate_phi_plan
    (mk_inst 3 PHI [Label "left"; Var "a"; Label "right"; Var "b"] ["p"])
    [] F ((init_plan_state 0) with ps_stack := [Var "a"; Var "a"]))).ps_stack =
    [Var "a"]
Proof
  EVAL_TAC
QED

Theorem alias_probe_regular_consumption:
  (SND (generate_regular_inst_plan ARB (dfg_build_function alias_probe_fn)
    ARB alias_probe_fn (mk_inst 4 ISZERO [Var "a"] ["z"])
    [] F F "entry" ((init_plan_state 0) with ps_stack := [Var "a"]))).ps_stack = [] /\
  (SND (generate_regular_inst_plan ARB (dfg_build_function alias_probe_fn)
    ARB alias_probe_fn (mk_inst 4 ISZERO [Var "a"] ["z"])
    [] F F "entry" ((init_plan_state 0) with ps_stack := [Var "a"; Var "a"]))).ps_stack =
    [Var "a"]
Proof
  EVAL_TAC >> simp[]
QED

(* Boundary fixtures distinguish transient duplicates from retained ownership. *)
Theorem alias_probe_assign_ownership:
  (SND (generate_regular_inst_plan ARB (dfg_build_function alias_probe_fn)
    ARB alias_probe_fn (mk_inst 4 ASSIGN [Var "a"] ["z"])
    ["a"; "z"] F T "entry" ((init_plan_state 0) with ps_stack := [Var "a"]))).ps_stack =
    [Var "a"; Var "z"] /\
  (SND (generate_regular_inst_plan ARB (dfg_build_function alias_probe_fn)
    ARB alias_probe_fn (mk_inst 4 ASSIGN [Var "a"] ["z"])
    ["z"] F T "entry" ((init_plan_state 0) with ps_stack := [Var "a"]))).ps_stack =
    [Var "z"] /\
  (SND (generate_regular_inst_plan ARB (dfg_build_function alias_probe_fn)
    ARB alias_probe_fn (mk_inst 4 ASSIGN [Var "a"] ["z"])
    ["a"] F T "entry" ((init_plan_state 0) with ps_stack := [Var "a"]))).ps_stack =
    [Var "a"] /\
  (SND (generate_regular_inst_plan ARB (dfg_build_function alias_probe_fn)
    ARB alias_probe_fn (mk_inst 4 ASSIGN [Var "a"] ["z"])
    [] F T "entry" ((init_plan_state 0) with ps_stack := [Var "a"]))).ps_stack = []
Proof
  EVAL_TAC >> simp[]
QED

Theorem alias_probe_repeated_operands:
  (SND (emit_input_plan ADD [Var "a"; Var "a"] []
    ((init_plan_state 0) with ps_stack := [Var "a"]))).ps_stack =
    [Var "a"; Var "a"] /\
  (SND (generate_regular_inst_plan ARB (dfg_build_function alias_probe_fn)
    ARB alias_probe_fn (mk_inst 4 ADD [Var "a"; Var "a"] ["z"])
    [] F T "entry" ((init_plan_state 0) with ps_stack := [Var "a"]))).ps_stack = [] /\
  (SND (generate_regular_inst_plan ARB (dfg_build_function alias_probe_fn)
    ARB alias_probe_fn (mk_inst 4 ADD [Var "a"; Var "a"] ["z"])
    ["a"] F T "entry" ((init_plan_state 0) with ps_stack := [Var "a"]))).ps_stack =
    [Var "a"]
Proof
  EVAL_TAC >> simp[]
QED

Theorem alias_probe_live_then_dead:
  (SND (generate_regular_inst_plan ARB (dfg_build_function alias_probe_fn)
    ARB alias_probe_fn (mk_inst 5 ISZERO [Var "a"] ["q"])
    ["z"] F T "entry"
    (SND (generate_regular_inst_plan ARB (dfg_build_function alias_probe_fn)
      ARB alias_probe_fn (mk_inst 4 ASSIGN [Var "a"] ["z"])
      ["a"; "z"] F T "entry"
      ((init_plan_state 0) with ps_stack := [Var "a"]))))).ps_stack = [Var "z"]
Proof
  EVAL_TAC >> simp[] >> EVAL_TAC >> simp[]
QED

Theorem alias_probe_spill_restore_ownership:
  (SND (emit_input_plan ADD [Var "a"; Var "a"] []
    ((init_plan_state 0) with ps_spilled := FEMPTY |+ (Var "a",0)))).ps_stack =
    [Var "a"; Var "a"] /\
  (SND (emit_input_plan ADD [Var "a"; Var "a"] []
    ((init_plan_state 0) with ps_spilled := FEMPTY |+ (Var "a",0)))).ps_spilled = FEMPTY /\
  (SND (emit_one_input ADD ["a"] (Var "a")
    ((init_plan_state 0) with ps_stack := Var "a" :: REPLICATE 16 (Lit 0w)))).ps_stack =
    (Var "a" :: REPLICATE 16 (Lit 0w)) ++ [Var "a"] /\
  (SND (emit_one_input ADD ["a"] (Var "a")
    ((init_plan_state 0) with ps_stack := Var "a" :: REPLICATE 16 (Lit 0w)))).ps_spilled = FEMPTY
Proof
  EVAL_TAC >> simp[]
QED

(* Candidate interface (not yet a reachable-state invariant):
   At ordinary boundaries each variable has at most one owner, either one
   stack occurrence or a spill key. Constants/markers may repeat freely.
   Inputs actually read must be covered. Emission needs the transient bound
     count x stack <= count x pending + 1
   and, for spilled x, count x stack <= count x pending; these are the
   occurrence clauses of reorderSim.residual_budget_wf. Its slot/allocator
   clauses are extra obligations, not consequences of coverage.
   emit_input_plan_pending_inventory gives a LOWER bound from coverage;
   emit_input_plan_inventory_accumulation is also a LOWER bound and cannot
   establish the desired upper bound. reorder_one_pending_inventory_wf
   preserves that lower bound only assuming residual_budget_wf and pending
   length <= 16. Thus none of these three is a uniqueness theorem.
   Missing transfer: covered demand + per-variable one-owner + fresh outputs
   + valid spill allocation must yield one-owner after reorder/pop/output,
   with dead nontrivial aliases absent except for untouched branch residuals.
   Support for those residuals is edge/cleanup dependent, not plain liveness.
   OFFSET introduces a fresh root even when dead; PARAM introduces no planner
   operand at dispatch. Halting may retain a dead single output. Restrict live
   support to nontrivial aliases at nonhalting boundaries, not all held names.
   These tests validate the local candidate only, not the lineage induction. *)
Theorem alias_probe_halting_retention:
  (SND (generate_regular_inst_plan ARB (dfg_build_function alias_probe_fn)
    ARB alias_probe_fn (mk_inst 4 ASSIGN [Var "a"] ["z"])
    [] T T "entry" ((init_plan_state 0) with ps_stack := [Var "a"]))).ps_stack =
    [Var "z"]
Proof
  EVAL_TAC >> simp[]
QED

Definition alias_probe_clean_def:
  alias_probe_clean inputs stk height promised =
    clean_stack_plan
      <| ds_inst := FEMPTY |++ [(("pred",0),["a"; "b"]); (("edge",0),inputs)];
         ds_boundary := FEMPTY |>
      (ARB with <| cfg_preds := FEMPTY |+ ("edge",["pred"]);
                   cfg_succs := FEMPTY |+ ("pred",["edge"; "other"]) |>)
      (mk_raw_function "clean_probe"
        [<| bb_label := "pred"; bb_instructions := [] |>])
      <| bb_label := "edge"; bb_instructions := [] |>
      ((init_plan_state 0) with <| ps_stack := stk;
        ps_cleanup_height := height; ps_cleanup_promised := promised |> )
End

Theorem alias_probe_clean_slots:
  (SND (alias_probe_clean ["b"] [Var "a"; Var "b"] NONE T)).ps_stack =
    [dead_stack_marker; Var "b"] /\
  (SND (alias_probe_clean ["b"] [Var "a"; Var "b"] NONE F)).ps_stack =
    [Var "b"] /\
  (SND (alias_probe_clean ["a"; "b"] [Var "a"; Var "b"] NONE T)).ps_stack =
    [Var "a"; Var "b"] /\
  (SND (alias_probe_clean [] [Var "a"; Var "b"] NONE T)).ps_stack =
    [dead_stack_marker; dead_stack_marker] /\
  (SND (alias_probe_clean ["a"] [Var "a"; Var "b"] NONE T)).ps_stack =
    [Var "a"]
Proof
  EVAL_TAC
QED

Theorem alias_probe_jmp_residual:
  (SND (reorder_plan (dfg_build_function alias_probe_fn) [Var "b"]
    ((init_plan_state 0) with ps_stack := [Var "a"; Var "b"]))).ps_stack =
    [Var "a"; Var "b"] /\
  (SND (reorder_plan (dfg_build_function alias_probe_fn) [Var "r"; Var "a"]
    ((init_plan_state 0) with ps_stack := [Var "a"; Var "r"]))).ps_stack =
    [Var "r"; Var "a"]
Proof
  EVAL_TAC
QED

Theorem alias_probe_spilled_phi:
  (SND (generate_phi_plan
    (mk_inst 3 PHI [Label "left"; Var "a"; Label "right"; Var "b"] ["p"])
    ["p"] F ((init_plan_state 0) with ps_spilled := FEMPTY |+ (Var "a",0))))
      .ps_spilled = FEMPTY |+ (Var "a",0) /\
  (release_dead_spills []
    ((init_plan_state 0) with ps_spilled := FEMPTY |+ (Var "a",0))).ps_spilled = FEMPTY
Proof
  EVAL_TAC >> simp[]
QED

Definition alias_probe_loop_fn_def:
  alias_probe_loop_fn = mk_raw_function "loop_probe"
    [<| bb_label := "entry"; bb_instructions :=
         [mk_inst 0 JMP [Label "header"] []] |>;
     <| bb_label := "header"; bb_instructions :=
         [mk_inst 1 CALLDATASIZE [] ["r"];
          mk_inst 2 JMP [Label "body"] []] |>;
     <| bb_label := "body"; bb_instructions :=
         [mk_inst 3 ASSIGN [Var "r"] ["a"];
          mk_inst 4 ISZERO [Var "a"] ["z"];
          mk_inst 5 JNZ [Var "z"; Label "header"; Label "exit"] []] |>;
     <| bb_label := "exit"; bb_instructions := [mk_inst 6 STOP [] []] |>]
End

Theorem alias_probe_loop_liveness:
  ~MEM "a" (live_vars_at (liveness_analyze alias_probe_loop_fn) "header" 0) /\
  MEM "a" (live_vars_at (liveness_analyze alias_probe_loop_fn) "body" 1) /\
  ~MEM "a" (live_vars_at (liveness_analyze alias_probe_loop_fn) "body" 2) /\
  normalize_operand (dfg_build_function alias_probe_loop_fn) [] (Var "a") = Var "r"
Proof
  EVAL_TAC >> simp[]
QED

(* Initialized loop probe with the root written by a header PHI. *)
Definition alias_phi_loop_fn_def:
  alias_phi_loop_fn = mk_raw_function "phi_loop_probe"
    [<| bb_label := "entry"; bb_instructions :=
         [mk_inst 0 CALLDATASIZE [] ["e"];
          mk_inst 1 JMP [Label "header"] []] |>;
     <| bb_label := "header"; bb_instructions :=
         [mk_inst 2 PHI [Label "entry"; Var "e"; Label "backedge"; Var "q"] ["r"];
          mk_inst 3 JMP [Label "body"] []] |>;
     <| bb_label := "body"; bb_instructions :=
         [mk_inst 4 ASSIGN [Var "r"] ["a"];
          mk_inst 5 ISZERO [Var "a"] ["z"];
          mk_inst 6 CALLDATASIZE [] ["q"];
          mk_inst 7 JNZ [Var "z"; Label "backedge"; Label "exit"] []] |>;
     <| bb_label := "exit"; bb_instructions := [mk_inst 8 STOP [] []] |>;
     <| bb_label := "backedge"; bb_instructions := [mk_inst 9 JMP [Label "header"] []] |>]
End

Theorem alias_phi_loop_ready:
  codegen_ready_fn alias_phi_loop_fn /\
  normalize_operand (dfg_build_function alias_phi_loop_fn) [] (Var "a") = Var "r"
Proof
  conj_tac >- EVAL_TAC >> EVAL_TAC
QED

Definition alias_phi_loop_plan_def:
  alias_phi_loop_plan n ps = generate_block_plan
    (liveness_analyze alias_phi_loop_fn) (dfg_build_function alias_phi_loop_fn)
    (cfg_analyze alias_phi_loop_fn) alias_phi_loop_fn (EL n alias_phi_loop_fn.fn_blocks) ps
End

Definition alias_phi_loop_entry_def:
  alias_phi_loop_entry = THE (alias_phi_loop_plan 0 (init_cleanup_plan_state NONE [] 0 0))
End

Definition alias_phi_loop_header_def:
  alias_phi_loop_header = THE (alias_phi_loop_plan 1 (SND alias_phi_loop_entry))
End

Definition alias_phi_loop_body_def:
  alias_phi_loop_body = THE (alias_phi_loop_plan 2 (SND alias_phi_loop_header))
End

Theorem alias_phi_loop_plans_success:
  IS_SOME (alias_phi_loop_plan 0 (init_cleanup_plan_state NONE [] 0 0)) /\
  IS_SOME (alias_phi_loop_plan 1 (SND alias_phi_loop_entry)) /\
  IS_SOME (alias_phi_loop_plan 2 (SND alias_phi_loop_header)) /\
  IS_SOME (alias_phi_loop_plan 1 ((SND alias_phi_loop_entry) with
    <|ps_stack := (SND alias_phi_loop_body).ps_stack;
      ps_spilled := (SND alias_phi_loop_body).ps_spilled|>))
Proof
  conj_tac >- EVAL_TAC >>
  conj_tac >- EVAL_TAC >>
  conj_tac >- EVAL_TAC >> EVAL_TAC
QED

Theorem alias_phi_loop_endpoint_stacks:
  (SND alias_phi_loop_entry).ps_stack = [Var "e"] /\
  (SND alias_phi_loop_header).ps_stack = [Var "r"] /\
  (SND alias_phi_loop_body).ps_stack = [Var "q"]
Proof
  conj_tac >- EVAL_TAC >> conj_tac >- EVAL_TAC >> EVAL_TAC
QED

Definition alias_phi_loop_backedge_def:
  alias_phi_loop_backedge = THE (alias_phi_loop_plan 4 (SND alias_phi_loop_body))
End

Definition alias_phi_loop_reentry_def:
  alias_phi_loop_reentry = (SND alias_phi_loop_entry) with
    <|ps_stack := (SND alias_phi_loop_backedge).ps_stack;
      ps_spilled := (SND alias_phi_loop_backedge).ps_spilled|>
End

Definition alias_phi_loop_phi_cut_def:
  alias_phi_loop_phi_cut = SND (generate_phi_plan
    (HD (EL 1 alias_phi_loop_fn.fn_blocks).bb_instructions)
    (live_vars_at (liveness_analyze alias_phi_loop_fn) "header" 1) F
    alias_phi_loop_reentry)
End

Theorem alias_phi_loop_plans:
  alias_phi_loop_plan 0 (init_cleanup_plan_state NONE [] 0 0) = SOME alias_phi_loop_entry /\
  alias_phi_loop_plan 1 (SND alias_phi_loop_entry) = SOME alias_phi_loop_header /\
  alias_phi_loop_plan 2 (SND alias_phi_loop_header) = SOME alias_phi_loop_body
Proof
  mp_tac alias_phi_loop_plans_success >>
  Cases_on `alias_phi_loop_plan 0 (init_cleanup_plan_state NONE [] 0 0)` >>
  Cases_on `alias_phi_loop_plan 1 (SND alias_phi_loop_entry)` >>
  Cases_on `alias_phi_loop_plan 2 (SND alias_phi_loop_header)` >>
  simp[alias_phi_loop_entry_def, alias_phi_loop_header_def, alias_phi_loop_body_def]
QED

Theorem alias_phi_loop_backedge_success:
  IS_SOME (alias_phi_loop_plan 4 (SND alias_phi_loop_body))
Proof
  EVAL_TAC
QED

Theorem alias_phi_loop_backedge_plan:
  alias_phi_loop_plan 4 (SND alias_phi_loop_body) = SOME alias_phi_loop_backedge
Proof
  mp_tac alias_phi_loop_backedge_success >>
  Cases_on `alias_phi_loop_plan 4 (SND alias_phi_loop_body)` >>
  simp[alias_phi_loop_backedge_def]
QED

Theorem alias_phi_loop_reentry_fields:
  (SND alias_phi_loop_backedge).ps_stack = [Var "q"] /\
  alias_phi_loop_reentry.ps_stack = [Var "q"] /\
  alias_phi_loop_reentry.ps_spilled = FEMPTY /\
  alias_phi_loop_phi_cut.ps_stack = [Var "r"] /\
  alias_phi_loop_phi_cut.ps_spilled = FEMPTY /\
  IS_SOME (alias_phi_loop_plan 1 alias_phi_loop_reentry) /\
  FST (THE (alias_phi_loop_plan 1 alias_phi_loop_reentry)) = FST alias_phi_loop_header /\
  (SND (THE (alias_phi_loop_plan 1 alias_phi_loop_reentry))).ps_stack = [Var "r"]
Proof
  conj_tac >- EVAL_TAC >>
  conj_tac >- EVAL_TAC >>
  conj_tac >- EVAL_TAC >>
  conj_tac >- EVAL_TAC >>
  conj_tac >- EVAL_TAC >>
  conj_tac >- EVAL_TAC >>
  conj_tac >- EVAL_TAC >> EVAL_TAC
QED

Theorem alias_phi_loop_alias_deleted:
  ~plan_holds (SND alias_phi_loop_body) (Var "a") /\
  ~plan_holds (SND alias_phi_loop_backedge) (Var "a") /\
  ~plan_holds alias_phi_loop_reentry (Var "a") /\
  ~plan_holds alias_phi_loop_phi_cut (Var "a")
Proof
  conj_tac >- (EVAL_TAC >> simp[]) >>
  conj_tac >- (EVAL_TAC >> simp[]) >>
  conj_tac >- (EVAL_TAC >> simp[]) >> EVAL_TAC >> simp[]
QED

Theorem alias_phi_loop_dfs_header:
  dfs_aux_call (liveness_analyze alias_phi_loop_fn)
    (dfg_build_function alias_phi_loop_fn) (cfg_analyze alias_phi_loop_fn) alias_phi_loop_fn
    (init_cleanup_plan_state NONE [] 0 0) ["header"] ["entry"] (SND alias_phi_loop_entry)
Proof
  `SND alias_phi_loop_entry = (SND alias_phi_loop_entry) with
    <|ps_stack := (SND alias_phi_loop_entry).ps_stack;
      ps_spilled := (SND alias_phi_loop_entry).ps_spilled|>` by simp[] >>
  pop_assum SUBST1_TAC >> irule dfs_aux_call_branch >> qexists_tac `[]` >>
  `cfg_succs_of (cfg_analyze alias_phi_loop_fn) "entry" = ["header"]` by EVAL_TAC >>
  pop_assum (fn th => rewrite_tac[GSYM th]) >>
  irule dfs_aux_call_succs >> simp[] >>
  qexistsl_tac [`EL 0 alias_phi_loop_fn.fn_blocks`, `FST alias_phi_loop_entry`,
    `init_cleanup_plan_state NONE [] 0 0`, `[]`] >>
  simp[GSYM alias_phi_loop_plan_def, alias_phi_loop_plans] >>
  conj_tac >- EVAL_TAC >> irule dfs_aux_call_entry >> EVAL_TAC
QED

Theorem alias_phi_loop_dfs_body:
  dfs_aux_call (liveness_analyze alias_phi_loop_fn)
    (dfg_build_function alias_phi_loop_fn) (cfg_analyze alias_phi_loop_fn) alias_phi_loop_fn
    (init_cleanup_plan_state NONE [] 0 0) ["body"] ["header"; "entry"] (SND alias_phi_loop_header)
Proof
  `SND alias_phi_loop_header = (SND alias_phi_loop_header) with
    <|ps_stack := (SND alias_phi_loop_header).ps_stack;
      ps_spilled := (SND alias_phi_loop_header).ps_spilled|>` by simp[] >>
  pop_assum SUBST1_TAC >> irule dfs_aux_call_branch >> qexists_tac `[]` >>
  `cfg_succs_of (cfg_analyze alias_phi_loop_fn) "header" = ["body"]` by EVAL_TAC >>
  pop_assum (fn th => rewrite_tac[GSYM th]) >>
  irule dfs_aux_call_succs >> simp[] >>
  qexistsl_tac [`EL 1 alias_phi_loop_fn.fn_blocks`, `FST alias_phi_loop_header`,
    `SND alias_phi_loop_entry`, `[]`] >>
  simp[GSYM alias_phi_loop_plan_def, alias_phi_loop_plans, alias_phi_loop_dfs_header] >> EVAL_TAC
QED

Theorem alias_phi_loop_exit_dfs_result:
  generate_fn_plan_aux (liveness_analyze alias_phi_loop_fn)
    (dfg_build_function alias_phi_loop_fn) (cfg_analyze alias_phi_loop_fn) alias_phi_loop_fn
    ["exit"] ["body"; "header"; "entry"] (SND alias_phi_loop_body) =
    SOME ([SOLabel "exit"; SOPop 1; SOEmit "STOP"],
      ["exit"; "body"; "header"; "entry"], init_cleanup_plan_state NONE [] 0 0)
Proof
  EVAL_TAC
QED

Theorem alias_phi_loop_dfs_backedge:
  dfs_aux_call (liveness_analyze alias_phi_loop_fn)
    (dfg_build_function alias_phi_loop_fn) (cfg_analyze alias_phi_loop_fn) alias_phi_loop_fn
    (init_cleanup_plan_state NONE [] 0 0) ["backedge"]
    ["exit"; "body"; "header"; "entry"] (SND alias_phi_loop_body)
Proof
  `SND alias_phi_loop_body = (SND alias_phi_loop_body) with
    <|ps_stack := (SND alias_phi_loop_body).ps_stack;
      ps_spilled := (SND alias_phi_loop_body).ps_spilled|>` by simp[] >>
  pop_assum SUBST1_TAC >> irule dfs_aux_call_branch >> qexists_tac `[]` >>
  `SND alias_phi_loop_body = (SND alias_phi_loop_body) with
    <|ps_alloc := (init_cleanup_plan_state NONE [] 0 0).ps_alloc with
        sa_free_slots := (SND alias_phi_loop_body).ps_alloc.sa_free_slots;
      ps_label_counter := (init_cleanup_plan_state NONE [] 0 0).ps_label_counter|>` by EVAL_TAC >>
  pop_assum SUBST1_TAC >> irule dfs_aux_call_sibling >>
  qexistsl_tac [`[SOLabel "exit"; SOPop 1; SOEmit "STOP"]`,
    `"exit"`, `["body"; "header"; "entry"]`] >>
  simp[alias_phi_loop_exit_dfs_result] >>
  `cfg_succs_of (cfg_analyze alias_phi_loop_fn) "body" = ["exit"; "backedge"]` by EVAL_TAC >>
  pop_assum (fn th => rewrite_tac[GSYM th]) >>
  irule dfs_aux_call_succs >> simp[] >>
  qexistsl_tac [`EL 2 alias_phi_loop_fn.fn_blocks`, `FST alias_phi_loop_body`,
    `SND alias_phi_loop_header`, `[]`] >>
  simp[GSYM alias_phi_loop_plan_def, alias_phi_loop_plans, alias_phi_loop_dfs_body] >> EVAL_TAC
QED

Theorem alias_phi_loop_dfs_states:
  dfs_block_state (liveness_analyze alias_phi_loop_fn)
    (dfg_build_function alias_phi_loop_fn) (cfg_analyze alias_phi_loop_fn) alias_phi_loop_fn
    (init_cleanup_plan_state NONE [] 0 0) "entry" (init_cleanup_plan_state NONE [] 0 0) /\
  dfs_block_state (liveness_analyze alias_phi_loop_fn)
    (dfg_build_function alias_phi_loop_fn) (cfg_analyze alias_phi_loop_fn) alias_phi_loop_fn
    (init_cleanup_plan_state NONE [] 0 0) "header" (SND alias_phi_loop_entry) /\
  dfs_block_state (liveness_analyze alias_phi_loop_fn)
    (dfg_build_function alias_phi_loop_fn) (cfg_analyze alias_phi_loop_fn) alias_phi_loop_fn
    (init_cleanup_plan_state NONE [] 0 0) "body" (SND alias_phi_loop_header) /\
  dfs_block_state (liveness_analyze alias_phi_loop_fn)
    (dfg_build_function alias_phi_loop_fn) (cfg_analyze alias_phi_loop_fn) alias_phi_loop_fn
    (init_cleanup_plan_state NONE [] 0 0) "backedge" (SND alias_phi_loop_body)
Proof
  rewrite_tac[dfs_block_state_def] >> conj_tac
  >- (qexistsl_tac [`[]`, `[]`] >> simp[] >> irule dfs_aux_call_entry >> EVAL_TAC) >>
  conj_tac >- (qexistsl_tac [`[]`, `["entry"]`] >> simp[alias_phi_loop_dfs_header]) >>
  conj_tac >- (qexistsl_tac [`[]`, `["header"; "entry"]`] >> simp[alias_phi_loop_dfs_body]) >>
  qexistsl_tac [`[]`, `["exit"; "body"; "header"; "entry"]`] >> simp[alias_phi_loop_dfs_backedge]
QED

Theorem alias_phi_loop_lineage_header:
  lineage_state (liveness_analyze alias_phi_loop_fn)
    (dfg_build_function alias_phi_loop_fn) (cfg_analyze alias_phi_loop_fn) alias_phi_loop_fn
    (init_cleanup_plan_state NONE [] 0 0) "header" (SND alias_phi_loop_entry)
Proof
  `SND alias_phi_loop_entry = (SND alias_phi_loop_entry) with
    <|ps_stack := (SND alias_phi_loop_entry).ps_stack;
      ps_spilled := (SND alias_phi_loop_entry).ps_spilled|>` by simp[] >>
  pop_assum SUBST1_TAC >> irule lineage_state_step >> simp[alias_phi_loop_dfs_states] >>
  qexistsl_tac [`EL 0 alias_phi_loop_fn.fn_blocks`, `FST alias_phi_loop_entry`, `NONE`,
    `"entry"`, `F`, `init_cleanup_plan_state NONE [] 0 0`,
    `init_cleanup_plan_state NONE [] 0 0`, `SND alias_phi_loop_entry`] >>
  simp[GSYM alias_phi_loop_plan_def, alias_phi_loop_plans, alias_phi_loop_dfs_states] >>
  conj_tac >- EVAL_TAC >> conj_tac >- EVAL_TAC >>
  conj_tac >- EVAL_TAC >> irule lineage_state_entry >> EVAL_TAC
QED

Theorem alias_phi_loop_lineage_body:
  lineage_state (liveness_analyze alias_phi_loop_fn)
    (dfg_build_function alias_phi_loop_fn) (cfg_analyze alias_phi_loop_fn) alias_phi_loop_fn
    (init_cleanup_plan_state NONE [] 0 0) "body" (SND alias_phi_loop_header)
Proof
  `SND alias_phi_loop_header = (SND alias_phi_loop_header) with
    <|ps_stack := (SND alias_phi_loop_header).ps_stack;
      ps_spilled := (SND alias_phi_loop_header).ps_spilled|>` by simp[] >>
  pop_assum SUBST1_TAC >> irule lineage_state_step >> simp[alias_phi_loop_dfs_states] >>
  qexistsl_tac [`EL 1 alias_phi_loop_fn.fn_blocks`, `FST alias_phi_loop_header`, `NONE`,
    `"header"`, `F`, `SND alias_phi_loop_entry`, `SND alias_phi_loop_entry`,
    `SND alias_phi_loop_header`] >>
  simp[GSYM alias_phi_loop_plan_def, alias_phi_loop_plans, alias_phi_loop_dfs_states,
       alias_phi_loop_lineage_header] >>
  conj_tac >- EVAL_TAC >> conj_tac >- EVAL_TAC >> EVAL_TAC
QED

Theorem alias_phi_loop_lineage_backedge:
  lineage_state (liveness_analyze alias_phi_loop_fn)
    (dfg_build_function alias_phi_loop_fn) (cfg_analyze alias_phi_loop_fn) alias_phi_loop_fn
    (init_cleanup_plan_state NONE [] 0 0) "backedge" (SND alias_phi_loop_body)
Proof
  `SND alias_phi_loop_body = (SND alias_phi_loop_body) with
    <|ps_stack := (SND alias_phi_loop_body).ps_stack;
      ps_spilled := (SND alias_phi_loop_body).ps_spilled|>` by simp[] >>
  pop_assum SUBST1_TAC >> irule lineage_state_step >> simp[alias_phi_loop_dfs_states] >>
  qexistsl_tac [`EL 2 alias_phi_loop_fn.fn_blocks`, `FST alias_phi_loop_body`, `NONE`,
    `"body"`, `F`, `SND alias_phi_loop_header`, `SND alias_phi_loop_header`,
    `SND alias_phi_loop_body`] >>
  simp[GSYM alias_phi_loop_plan_def, alias_phi_loop_plans, alias_phi_loop_dfs_states,
       alias_phi_loop_lineage_body] >>
  conj_tac >- EVAL_TAC >> conj_tac >- EVAL_TAC >> EVAL_TAC
QED

Theorem alias_phi_loop_lineage_reentry:
  lineage_entry (liveness_analyze alias_phi_loop_fn)
    (dfg_build_function alias_phi_loop_fn) (cfg_analyze alias_phi_loop_fn) alias_phi_loop_fn
    (init_cleanup_plan_state NONE [] 0 0) "backedge" "header" alias_phi_loop_reentry
Proof
  simp[lineage_entry_def] >>
  qexistsl_tac [`SND alias_phi_loop_body`, `EL 4 alias_phi_loop_fn.fn_blocks`,
    `SND alias_phi_loop_body`, `FST alias_phi_loop_backedge`, `SND alias_phi_loop_backedge`,
    `NONE`, `F`, `SND alias_phi_loop_backedge`, `SND alias_phi_loop_entry`] >>
  simp[GSYM alias_phi_loop_plan_def, alias_phi_loop_backedge_plan, alias_phi_loop_dfs_states,
       alias_phi_loop_lineage_backedge, alias_phi_loop_reentry_def] >>
  conj_tac >- EVAL_TAC >> conj_tac >- EVAL_TAC >> EVAL_TAC
QED

(* Without dominance, liveness alone admits a stale alias at a root write. *)
Definition alias_probe_bad_loop_fn_def:
  alias_probe_bad_loop_fn = mk_raw_function "bad_loop_probe"
    [<| bb_label := "entry"; bb_instructions :=
         [mk_inst 0 JMP [Label "header"] []] |>;
     <| bb_label := "header"; bb_instructions :=
         [mk_inst 1 CALLDATASIZE [] ["r"];
          mk_inst 2 ISZERO [Var "a"] ["z"];
          mk_inst 3 JMP [Label "body"] []] |>;
     <| bb_label := "body"; bb_instructions :=
         [mk_inst 4 ASSIGN [Var "r"] ["a"];
          mk_inst 5 JMP [Label "header"] []] |>]
End

Theorem alias_probe_bad_loop_liveness:
  MEM "a" (live_vars_at (liveness_analyze alias_probe_bad_loop_fn) "header" 0) /\
  normalize_operand (dfg_build_function alias_probe_bad_loop_fn) [] (Var "a") = Var "r"
Proof
  EVAL_TAC >> simp[]
QED

(* Joint-cut probe: both incoming PHI identities are defined before the split. *)
Definition alias_retired_fn_def:
  alias_retired_fn = mk_raw_function "retired_phi"
    [<| bb_label := "entry"; bb_instructions :=
         [mk_inst 0 CALLDATASIZE [] ["a"];
          mk_inst 1 CALLDATASIZE [] ["b"];
          mk_inst 2 CALLDATASIZE [] ["c"];
          mk_inst 3 JNZ [Var "c"; Label "right"; Label "left"] []] |>;
     <| bb_label := "left"; bb_instructions :=
         [mk_inst 11 CALLDATASIZE [] ["tmp"]; mk_inst 4 JMP [Label "join"] []] |>;
     <| bb_label := "right"; bb_instructions := [mk_inst 5 JMP [Label "join"] []] |>;
     <| bb_label := "join"; bb_instructions :=
         [mk_inst 6 PHI [Label "left"; Var "a"; Label "right"; Var "b"] ["p"];
          mk_inst 7 ADD [Var "p"; Lit 1w] ["w"];
          mk_inst 8 JNZ [Var "w"; Label "yes"; Label "no"] []] |>;
     <| bb_label := "yes"; bb_instructions := [mk_inst 9 STOP [] []] |>;
     <| bb_label := "no"; bb_instructions := [mk_inst 10 STOP [] []] |>]
End

Theorem alias_retired_ready:
  codegen_ready_fn alias_retired_fn
Proof
  EVAL_TAC
QED

Definition alias_retired_plan_def:
  alias_retired_plan n ps = generate_block_plan (liveness_analyze alias_retired_fn)
    (dfg_build_function alias_retired_fn) (cfg_analyze alias_retired_fn)
    alias_retired_fn (EL n alias_retired_fn.fn_blocks) ps
End

Definition alias_retired_entry_def:
  alias_retired_entry = THE (alias_retired_plan 0 (init_cleanup_plan_state NONE [] 0 0))
End

Definition alias_retired_left_def:
  alias_retired_left = THE (alias_retired_plan 1 (SND alias_retired_entry))
End

Theorem alias_retired_trace_probe:
  IS_SOME (alias_retired_plan 0 (init_cleanup_plan_state NONE [] 0 0)) /\
  IS_SOME (alias_retired_plan 1 (SND alias_retired_entry)) /\
  (SND alias_retired_left).ps_stack = [Var "a"]
Proof
  EVAL_TAC
QED

Theorem alias_retired_plans:
  alias_retired_plan 0 (init_cleanup_plan_state NONE [] 0 0) = SOME alias_retired_entry /\
  alias_retired_plan 1 (SND alias_retired_entry) = SOME alias_retired_left
Proof
  mp_tac alias_retired_trace_probe >>
  Cases_on `alias_retired_plan 0 (init_cleanup_plan_state NONE [] 0 0)` >>
  Cases_on `alias_retired_plan 1 (SND alias_retired_entry)` >>
  simp[alias_retired_entry_def, alias_retired_left_def]
QED

Theorem alias_retired_dfs_left:
  dfs_aux_call (liveness_analyze alias_retired_fn)
    (dfg_build_function alias_retired_fn) (cfg_analyze alias_retired_fn) alias_retired_fn
    (init_cleanup_plan_state NONE [] 0 0) ["left"] ["entry"] (SND alias_retired_entry)
Proof
  `SND alias_retired_entry = (SND alias_retired_entry) with
    <|ps_stack := (SND alias_retired_entry).ps_stack;
      ps_spilled := (SND alias_retired_entry).ps_spilled|>` by simp[] >>
  pop_assum SUBST1_TAC >> irule dfs_aux_call_branch >> qexists_tac `["right"]` >>
  `cfg_succs_of (cfg_analyze alias_retired_fn) "entry" = ["left"; "right"]` by EVAL_TAC >>
  pop_assum (fn th => rewrite_tac[GSYM th]) >>
  irule dfs_aux_call_succs >> simp[] >>
  qexistsl_tac [`EL 0 alias_retired_fn.fn_blocks`, `FST alias_retired_entry`,
    `init_cleanup_plan_state NONE [] 0 0`, `[]`] >>
  simp[GSYM alias_retired_plan_def, alias_retired_plans] >>
  conj_tac >- EVAL_TAC >> irule dfs_aux_call_entry >> EVAL_TAC
QED

Theorem alias_retired_dfs_join:
  dfs_block_state (liveness_analyze alias_retired_fn)
    (dfg_build_function alias_retired_fn) (cfg_analyze alias_retired_fn) alias_retired_fn
    (init_cleanup_plan_state NONE [] 0 0) "join" (SND alias_retired_left)
Proof
  simp[dfs_block_state_def] >> qexistsl_tac [`[]`, `["left"; "entry"]`] >> simp[] >>
  `SND alias_retired_left = (SND alias_retired_left) with
    <|ps_stack := (SND alias_retired_left).ps_stack;
      ps_spilled := (SND alias_retired_left).ps_spilled|>` by simp[] >>
  pop_assum SUBST1_TAC >> irule dfs_aux_call_branch >> qexists_tac `[]` >>
  `cfg_succs_of (cfg_analyze alias_retired_fn) "left" = ["join"]` by EVAL_TAC >>
  pop_assum (fn th => rewrite_tac[GSYM th]) >>
  irule dfs_aux_call_succs >> simp[] >>
  qexistsl_tac [`EL 1 alias_retired_fn.fn_blocks`, `FST alias_retired_left`,
    `SND alias_retired_entry`, `[]`] >>
  simp[GSYM alias_retired_plan_def, alias_retired_plans, alias_retired_dfs_left] >> EVAL_TAC
QED

(* Initialized diamond JMP producer stages. *)
Definition alias_retired_left_mid_def:
  alias_retired_left_mid = SND (generate_regular_inst_plan
    (liveness_analyze alias_retired_fn) (dfg_build_function alias_retired_fn)
    (cfg_analyze alias_retired_fn) alias_retired_fn
    (HD (EL 1 alias_retired_fn.fn_blocks).bb_instructions)
    (live_vars_at (liveness_analyze alias_retired_fn) "left" 1)
    F T "left" (SND (clean_stack_plan (liveness_analyze alias_retired_fn)
      (cfg_analyze alias_retired_fn) alias_retired_fn
      (EL 1 alias_retired_fn.fn_blocks) (SND alias_retired_entry))))
End

Definition alias_retired_right_def:
  alias_retired_right = THE (alias_retired_plan 2 (SND alias_retired_entry))
End

Theorem alias_retired_jmp_targets:
  join_target_ops (liveness_analyze alias_retired_fn) alias_retired_fn "left"
    (EL 1 (EL 1 alias_retired_fn.fn_blocks).bb_instructions) = SOME [Var "a"] /\
  join_target_ops (liveness_analyze alias_retired_fn) alias_retired_fn "right"
    (HD (EL 2 alias_retired_fn.fn_blocks).bb_instructions) = SOME [Var "b"]
Proof
  conj_tac >- EVAL_TAC >> EVAL_TAC
QED

Definition alias_retired_right_mid_def:
  alias_retired_right_mid = SND (clean_stack_plan
    (liveness_analyze alias_retired_fn) (cfg_analyze alias_retired_fn)
    alias_retired_fn (EL 2 alias_retired_fn.fn_blocks) (SND alias_retired_entry))
End

Theorem alias_retired_jmp_restoration:
  alias_retired_left_mid.ps_stack = [Var "a"] /\
  restore_spilled_plan [Var "a"] alias_retired_left_mid = ([], alias_retired_left_mid) /\
  restore_spilled_plan [Var "b"] alias_retired_right_mid = ([], alias_retired_right_mid)
Proof
  conj_tac >- EVAL_TAC >>
  conj_tac >- EVAL_TAC >> EVAL_TAC
QED

Theorem alias_retired_jmp_reorder_calls:
  stack_get_unfixed_depth (Var "a") 0 1 alias_retired_left_mid.ps_stack = SOME 0 /\
  stack_get_unfixed_depth (Var "b") 0 1 alias_retired_right_mid.ps_stack = SOME 0 /\
  0 < LENGTH alias_retired_left_mid.ps_stack /\
  0 < LENGTH alias_retired_right_mid.ps_stack /\
  IS_SOME (alias_retired_plan 2 (SND alias_retired_entry))
Proof
  conj_tac >- EVAL_TAC >>
  conj_tac >- EVAL_TAC >>
  conj_tac >- EVAL_TAC >>
  conj_tac >- EVAL_TAC >> EVAL_TAC
QED

Theorem alias_retired_right_jmp_stages:
  alias_retired_right_mid.ps_stack = [Var "b"] /\
  reorder_plan (dfg_build_function alias_retired_fn) [Var "b"] alias_retired_right_mid =
    ([], alias_retired_right_mid) /\
  reorder_plan (dfg_build_function alias_retired_fn) [Var "a"] alias_retired_left_mid =
    ([], alias_retired_left_mid) /\
  (SND alias_retired_right).ps_stack = [Var "b"]
Proof
  conj_tac >- EVAL_TAC >>
  conj_tac >- EVAL_TAC >>
  conj_tac >- EVAL_TAC >> EVAL_TAC
QED

Definition alias_retired_left_tree_def:
  alias_retired_left_tree = THE (generate_fn_plan_aux
    (liveness_analyze alias_retired_fn) (dfg_build_function alias_retired_fn)
    (cfg_analyze alias_retired_fn) alias_retired_fn
    ["left"] ["entry"] (SND alias_retired_entry))
End

Theorem alias_retired_left_tree_success:
  IS_SOME (generate_fn_plan_aux
    (liveness_analyze alias_retired_fn) (dfg_build_function alias_retired_fn)
    (cfg_analyze alias_retired_fn) alias_retired_fn
    ["left"] ["entry"] (SND alias_retired_entry))
Proof
  EVAL_TAC
QED

Theorem alias_retired_left_tree_result:
  generate_fn_plan_aux
    (liveness_analyze alias_retired_fn) (dfg_build_function alias_retired_fn)
    (cfg_analyze alias_retired_fn) alias_retired_fn
    ["left"] ["entry"] (SND alias_retired_entry) = SOME alias_retired_left_tree
Proof
  mp_tac alias_retired_left_tree_success >>
  Cases_on `generate_fn_plan_aux
    (liveness_analyze alias_retired_fn) (dfg_build_function alias_retired_fn)
    (cfg_analyze alias_retired_fn) alias_retired_fn
    ["left"] ["entry"] (SND alias_retired_entry)` >>
  simp[alias_retired_left_tree_def]
QED

Theorem alias_retired_left_tree_alloc:
  (SND (SND alias_retired_left_tree)).ps_alloc =
    (init_cleanup_plan_state NONE [] 0 0).ps_alloc
Proof
  EVAL_TAC
QED

Theorem alias_retired_left_tree_counter:
  (SND (SND alias_retired_left_tree)).ps_label_counter = 0
Proof
  EVAL_TAC
QED

Theorem alias_retired_left_tree_fields:
  FST (SND alias_retired_left_tree) = ["yes"; "no"; "join"; "left"; "entry"] /\
  SND alias_retired_entry = (SND alias_retired_entry) with
    <|ps_alloc := (SND (SND alias_retired_left_tree)).ps_alloc with
        sa_free_slots := (SND alias_retired_entry).ps_alloc.sa_free_slots;
      ps_label_counter := (SND (SND alias_retired_left_tree)).ps_label_counter|>
Proof
  conj_tac >- EVAL_TAC >>
  rewrite_tac[alias_retired_left_tree_alloc, alias_retired_left_tree_counter] >>
  EVAL_TAC
QED

Theorem alias_retired_dfs_right:
  dfs_aux_call (liveness_analyze alias_retired_fn)
    (dfg_build_function alias_retired_fn) (cfg_analyze alias_retired_fn) alias_retired_fn
    (init_cleanup_plan_state NONE [] 0 0) ["right"]
    ["yes"; "no"; "join"; "left"; "entry"] (SND alias_retired_entry)
Proof
  `SND alias_retired_entry = (SND alias_retired_entry) with
    <|ps_stack := (SND alias_retired_entry).ps_stack;
      ps_spilled := (SND alias_retired_entry).ps_spilled|>` by simp[] >>
  pop_assum SUBST1_TAC >> irule dfs_aux_call_branch >> qexists_tac `[]` >>
  once_rewrite_tac[cj 2 alias_retired_left_tree_fields] >>
  irule dfs_aux_call_sibling >>
  qexistsl_tac [`FST alias_retired_left_tree`, `"left"`, `["entry"]`] >>
  simp[GSYM (cj 1 alias_retired_left_tree_fields), alias_retired_left_tree_result] >>
  `cfg_succs_of (cfg_analyze alias_retired_fn) "entry" = ["left"; "right"]` by EVAL_TAC >>
  pop_assum (fn th => rewrite_tac[GSYM th]) >>
  irule dfs_aux_call_succs >> simp[] >>
  qexistsl_tac [`EL 0 alias_retired_fn.fn_blocks`, `FST alias_retired_entry`,
    `init_cleanup_plan_state NONE [] 0 0`, `[]`] >>
  simp[GSYM alias_retired_plan_def, alias_retired_plans] >>
  conj_tac >- EVAL_TAC >> irule dfs_aux_call_entry >> EVAL_TAC
QED

Theorem alias_retired_dfs_edge_states:
  dfs_block_state (liveness_analyze alias_retired_fn)
    (dfg_build_function alias_retired_fn) (cfg_analyze alias_retired_fn) alias_retired_fn
    (init_cleanup_plan_state NONE [] 0 0) "entry" (init_cleanup_plan_state NONE [] 0 0) /\
  dfs_block_state (liveness_analyze alias_retired_fn)
    (dfg_build_function alias_retired_fn) (cfg_analyze alias_retired_fn) alias_retired_fn
    (init_cleanup_plan_state NONE [] 0 0) "left" (SND alias_retired_entry) /\
  dfs_block_state (liveness_analyze alias_retired_fn)
    (dfg_build_function alias_retired_fn) (cfg_analyze alias_retired_fn) alias_retired_fn
    (init_cleanup_plan_state NONE [] 0 0) "right" (SND alias_retired_entry)
Proof
  rewrite_tac[dfs_block_state_def] >> conj_tac
  >- (qexistsl_tac [`[]`, `[]`] >> simp[] >> irule dfs_aux_call_entry >> EVAL_TAC) >>
  conj_tac
  >- (qexistsl_tac [`[]`, `["entry"]`] >> simp[alias_retired_dfs_left]) >>
  qexistsl_tac [`[]`, `["yes"; "no"; "join"; "left"; "entry"]`] >>
  simp[alias_retired_dfs_right]
QED

Theorem alias_retired_lineage_edges:
  !lbl. MEM lbl ["left"; "right"] ==>
  lineage_entry (liveness_analyze alias_retired_fn)
    (dfg_build_function alias_retired_fn) (cfg_analyze alias_retired_fn) alias_retired_fn
    (init_cleanup_plan_state NONE [] 0 0) "entry" lbl (SND alias_retired_entry)
Proof
  rpt strip_tac >>
  `dfs_block_state (liveness_analyze alias_retired_fn)
    (dfg_build_function alias_retired_fn) (cfg_analyze alias_retired_fn) alias_retired_fn
    (init_cleanup_plan_state NONE [] 0 0) lbl (SND alias_retired_entry)` by
    (gvs[] >> simp[alias_retired_dfs_edge_states]) >>
  simp[lineage_entry_def] >>
  qexistsl_tac [`init_cleanup_plan_state NONE [] 0 0`, `EL 0 alias_retired_fn.fn_blocks`,
    `init_cleanup_plan_state NONE [] 0 0`, `FST alias_retired_entry`, `SND alias_retired_entry`,
    `NONE`, `F`, `SND alias_retired_entry`, `SND alias_retired_entry`] >>
  simp[GSYM alias_retired_plan_def, alias_retired_plans, alias_retired_dfs_edge_states,
       init_cleanup_plan_state_def] >>
  conj_tac >- (irule lineage_state_entry >> EVAL_TAC) >>
  conj_tac >- EVAL_TAC >>
  `cfg_succs_of (cfg_analyze alias_retired_fn) "entry" = ["left"; "right"]` by EVAL_TAC >>
  simp[GSYM init_cleanup_plan_state_def, alias_retired_plans] >> gvs[]
QED

Theorem alias_retired_right_plan:
  alias_retired_plan 2 (SND alias_retired_entry) = SOME alias_retired_right
Proof
  mp_tac (cj 5 alias_retired_jmp_reorder_calls) >>
  Cases_on `alias_retired_plan 2 (SND alias_retired_entry)` >>
  simp[alias_retired_right_def]
QED

Theorem alias_retired_lineage_join_left:
  lineage_entry (liveness_analyze alias_retired_fn)
    (dfg_build_function alias_retired_fn) (cfg_analyze alias_retired_fn) alias_retired_fn
    (init_cleanup_plan_state NONE [] 0 0) "left" "join" (SND alias_retired_left)
Proof
  simp[lineage_entry_def] >>
  qexistsl_tac [`SND alias_retired_entry`, `EL 1 alias_retired_fn.fn_blocks`,
    `SND alias_retired_entry`, `FST alias_retired_left`, `SND alias_retired_left`,
    `NONE`, `F`, `SND alias_retired_left`, `SND alias_retired_left`] >>
  simp[GSYM alias_retired_plan_def, alias_retired_plans, alias_retired_dfs_edge_states,
       alias_retired_dfs_join] >>
  conj_tac >- (irule lineage_entry_lineage_state >> qexists_tac `"entry"` >>
    irule alias_retired_lineage_edges >> simp[]) >>
  conj_tac >- EVAL_TAC >> conj_tac >- EVAL_TAC >> EVAL_TAC
QED

Theorem alias_retired_lineage_join_right:
  lineage_entry (liveness_analyze alias_retired_fn)
    (dfg_build_function alias_retired_fn) (cfg_analyze alias_retired_fn) alias_retired_fn
    (init_cleanup_plan_state NONE [] 0 0) "right" "join"
    ((SND alias_retired_left) with <|ps_stack := (SND alias_retired_right).ps_stack;
                                  ps_spilled := (SND alias_retired_right).ps_spilled|>)
Proof
  simp[lineage_entry_def] >>
  qexistsl_tac [`SND alias_retired_entry`, `EL 2 alias_retired_fn.fn_blocks`,
    `SND alias_retired_entry`, `FST alias_retired_right`, `SND alias_retired_right`,
    `NONE`, `F`, `SND alias_retired_right`, `SND alias_retired_left`] >>
  simp[GSYM alias_retired_plan_def, alias_retired_right_plan, alias_retired_dfs_edge_states,
       alias_retired_dfs_join] >>
  conj_tac >- (irule lineage_entry_lineage_state >> qexists_tac `"entry"` >>
    irule alias_retired_lineage_edges >> simp[]) >>
  conj_tac >- EVAL_TAC >> conj_tac >- EVAL_TAC >> EVAL_TAC
QED

(* This concrete cleanup override still emits the DFS block operations. *)
Theorem alias_retired_promised_replay:
  IS_SOME (alias_retired_plan 1 ((SND alias_retired_entry) with
    <|ps_cleanup_height := SOME 2; ps_cleanup_promised := T|>)) /\
  FST (THE (alias_retired_plan 1 ((SND alias_retired_entry) with
    <|ps_cleanup_height := SOME 2; ps_cleanup_promised := T|>))) =
    FST alias_retired_left
Proof
  conj_tac >- EVAL_TAC >> EVAL_TAC
QED

Definition alias_retired_shared_fn_def:
  alias_retired_shared_fn = alias_retired_fn with fn_blocks :=
    LUPDATE ((EL 0 alias_retired_fn.fn_blocks) with bb_instructions :=
      LUPDATE (mk_inst 1 ASSIGN [Var "a"] ["b"])
        1 (EL 0 alias_retired_fn.fn_blocks).bb_instructions)
      0 alias_retired_fn.fn_blocks
End

Theorem alias_retired_shared_ready:
  codegen_ready_fn alias_retired_shared_fn /\
  normalize_operand (dfg_build_function alias_retired_shared_fn) [] (Var "b") = Var "a"
Proof
  conj_tac >- EVAL_TAC >> EVAL_TAC
QED

Definition alias_retired_shared_plan_def:
  alias_retired_shared_plan n ps = generate_block_plan
    (liveness_analyze alias_retired_shared_fn) (dfg_build_function alias_retired_shared_fn)
    (cfg_analyze alias_retired_shared_fn) alias_retired_shared_fn
    (EL n alias_retired_shared_fn.fn_blocks) ps
End

Definition alias_retired_shared_entry_def:
  alias_retired_shared_entry = THE (alias_retired_shared_plan 0
    (init_cleanup_plan_state NONE [] 0 0))
End

Theorem alias_retired_shared_plans:
  IS_SOME (alias_retired_shared_plan 0 (init_cleanup_plan_state NONE [] 0 0)) /\
  IS_SOME (alias_retired_shared_plan 1 (SND alias_retired_shared_entry)) /\
  IS_SOME (alias_retired_shared_plan 2 (SND alias_retired_shared_entry)) /\
  (SND (THE (alias_retired_shared_plan 1 (SND alias_retired_shared_entry)))).ps_stack = [Var "a"] /\
  (SND (THE (alias_retired_shared_plan 2 (SND alias_retired_shared_entry)))).ps_stack = [Var "b"]
Proof
  conj_tac >- EVAL_TAC >>
  conj_tac >- EVAL_TAC >>
  conj_tac >- EVAL_TAC >>
  conj_tac >- EVAL_TAC >> EVAL_TAC
QED

Definition alias_retired_phi_state_def:
  alias_retired_phi_state = SND (generate_phi_plan
    (EL 0 (EL 3 alias_retired_fn.fn_blocks).bb_instructions)
    (live_vars_at (liveness_analyze alias_retired_fn) "join" 1) F
    (SND alias_retired_left))
End

Definition alias_retired_add_state_def:
  alias_retired_add_state = SND (generate_regular_inst_plan
    (liveness_analyze alias_retired_fn) (dfg_build_function alias_retired_fn)
    (cfg_analyze alias_retired_fn) alias_retired_fn
    (EL 1 (EL 3 alias_retired_fn.fn_blocks).bb_instructions)
    (live_vars_at (liveness_analyze alias_retired_fn) "join" 2) F T "join"
    alias_retired_phi_state)
End

Theorem alias_retired_join_cut_fields:
  (SND alias_retired_entry).ps_stack = [Var "a"; Var "b"] /\
  (SND alias_retired_left).ps_stack = [Var "a"] /\
  alias_retired_phi_state.ps_stack = [Var "p"] /\
  alias_retired_add_state.ps_stack = [Var "w"] /\
  IS_SOME (alias_retired_plan 3 (SND alias_retired_left)) /\
  EVERY (\ps. ps.ps_spilled = FEMPTY)
    [SND alias_retired_entry; SND alias_retired_left;
     alias_retired_phi_state; alias_retired_add_state]
Proof
  conj_tac >- EVAL_TAC >>
  conj_tac >- simp[alias_retired_trace_probe] >>
  conj_tac >- EVAL_TAC >>
  conj_tac >- EVAL_TAC >>
  conj_tac >- EVAL_TAC >>
  EVAL_TAC
QED

(* C2.24 whole-phase closure ledger (not a global invariant theorem).
   Initialization: alias_prepare_params_holds_output supplies parameter coverage;
   alias_entry_live_param_output connects entry demand to parameters. Still need
   compatible initial mass and provenance for the whole DFS inventory.
   Cleanup: alias_clean_stack_upper_support introduces no variable identities;
   it is not a proof that every retained identity is live. Need preservation of
   the lower-demand and mass predicates at the same cleanup cut.
   PHIs: alias_lineage_join_phi_prefix_total_slots and
   alias_lineage_join_phi_fold_lower_coverage close historical lower coverage.
   alias_phi_prefix_upper_support permits old names plus prefix outputs;
   alias_phi_prefix_singleton_mass needs output freshness. No theorem here
   supplies freshness for all old exception names along a DFS path.
   Regular non-JMP: alias_regular_plan_var_mass and
   alias_regular_plan_var_budget propagate mass given operand coverage, arity,
   distinct outputs and absent outputs. Readiness supplies arity/distinctness,
   not coverage or absent outputs. alias_regular_plan_holds_live propagates
   covered demand; it does not establish the initial coverage at every cut.
   alias_regular_plan_var_support additionally needs, for the tracked x,
     plan_holds ps (Var x) ==> MEM x live \/ MEM (Var x) (compute_operands inst).
   The branch cut below falsifies this premise despite coverage, mass and
   freshness. The halting and OFFSET joint cuts below give separate exceptions.
   Final JMP: alias_jmp_plan_holds_live handles covered live names;
   alias_lineage_join_historical_coverage and historical_spill_support describe
   the reached join. They are not an all-path inventory producer.
   Successor: DFS/lineage transfer copies stack/spills, so needs an edge rule
   reclassifying exception provenance and re-establishing demanded coverage.
   No such coupled producer has been established by these finite probes.

   Minimal necessary envelope revision: besides live/current operands, allow
   inactive branch alternatives BEFORE the PHI (with path/edge and defining
   instruction provenance), not just retired PHI sources; retain actual OFFSET
   definitions and earlier singleton outputs of halting blocks. Carry these
   tags until a proved deletion boundary, not merely until the next cut.
   Sufficiency is UNPROVED: at each output y still need
     MEM y inst.inst_outputs ==> ~plan_holds ps (Var y)
   for every tag class. SSA alone does not rule out a previous loop iteration;
   a path/dominance argument is still required. No global induction is released.
   This refutes the proposed inventory envelope, not lineage_alias_successor. *)
Theorem alias_retired_branch_cut:
  (!op. MEM op (compute_operands
      (HD (EL 1 alias_retired_fn.fn_blocks).bb_instructions)) /\
      is_var_operand op ==> plan_holds (SND alias_retired_entry) op) /\
  (!x. alias_var_mass x (SND alias_retired_entry) <= 1) /\
  EVERY (\out. ~plan_holds (SND alias_retired_entry) (Var out))
    (HD (EL 1 alias_retired_fn.fn_blocks).bb_instructions).inst_outputs /\
  plan_holds (SND alias_retired_entry) (Var "b") /\
  ~MEM "b" (live_vars_at (liveness_analyze alias_retired_fn) "left" 1) /\
  ~MEM (Var "b") (compute_operands
    (HD (EL 1 alias_retired_fn.fn_blocks).bb_instructions)) /\
  MEM (Var "b") (EL 0 (EL 3 alias_retired_fn.fn_blocks).bb_instructions).inst_operands
Proof
  conj_tac >- (EVAL_TAC >> simp[]) >>
  conj_tac >- (EVAL_TAC >> gen_tac >> rpt IF_CASES_TAC >> gvs[]) >>
  conj_tac >- EVAL_TAC >>
  conj_tac >- EVAL_TAC >>
  conj_tac >- EVAL_TAC >>
  conj_tac >- EVAL_TAC >> EVAL_TAC
QED

Theorem alias_retired_join_regular_cuts:
  EVERY (\(i,ps).
    (!op. MEM op (compute_operands (EL i (EL 3 alias_retired_fn.fn_blocks).bb_instructions)) /\
       is_var_operand op ==> plan_holds ps op) /\
    (!x. alias_var_mass x ps <= 1) /\
    EVERY (\out. ~plan_holds ps (Var out))
      (EL i (EL 3 alias_retired_fn.fn_blocks).bb_instructions).inst_outputs /\
    (!x. plan_holds ps (Var x) ==>
      MEM x (live_vars_at (liveness_analyze alias_retired_fn) "join" (SUC i)) \/
      MEM (Var x) (compute_operands (EL i (EL 3 alias_retired_fn.fn_blocks).bb_instructions))))
    [(1,alias_retired_phi_state); (2,alias_retired_add_state)]
Proof
  EVAL_TAC >> rpt strip_tac >> gvs[is_var_operand_def] >>
  IF_CASES_TAC >> simp[]
QED

Definition alias_halting_cut_fn_def:
  alias_halting_cut_fn = mk_raw_function "halting_cut"
    [<| bb_label := "entry"; bb_instructions :=
         [mk_inst 0 CALLDATASIZE [] ["dead"];
          mk_inst 1 CALLDATASIZE [] ["b"];
          mk_inst 2 ISZERO [Var "b"] ["z"];
          mk_inst 3 STOP [] []] |>]
End

Definition alias_halting_cut_state_def:
  alias_halting_cut_state i = SND (THE (generate_block_insts_plan
    (liveness_analyze alias_halting_cut_fn) (dfg_build_function alias_halting_cut_fn)
    (cfg_analyze alias_halting_cut_fn) alias_halting_cut_fn "entry" T 0 4 0
    (TAKE i (HD alias_halting_cut_fn.fn_blocks).bb_instructions)
    (init_cleanup_plan_state NONE [] 0 0)))
End

Theorem alias_halting_cut_probe:
  codegen_ready_fn alias_halting_cut_fn /\
  IS_SOME (generate_block_plan (liveness_analyze alias_halting_cut_fn)
    (dfg_build_function alias_halting_cut_fn) (cfg_analyze alias_halting_cut_fn)
    alias_halting_cut_fn (HD alias_halting_cut_fn.fn_blocks)
    (init_cleanup_plan_state NONE [] 0 0)) /\
  (alias_halting_cut_state 1).ps_stack = [Var "dead"] /\
  (alias_halting_cut_state 2).ps_stack = [Var "dead"; Var "b"] /\
  (alias_halting_cut_state 3).ps_stack = [Var "dead"; Var "z"] /\
  ~MEM "dead" (live_vars_at (liveness_analyze alias_halting_cut_fn) "entry" 2) /\
  ~MEM (Var "dead") (compute_operands
    (EL 1 (HD alias_halting_cut_fn.fn_blocks).bb_instructions))
Proof
  EVAL_TAC
QED

Theorem alias_halting_joint_cuts:
  EVERY (\i.
    (!op. MEM op (compute_operands (EL i (HD alias_halting_cut_fn.fn_blocks).bb_instructions)) /\
       is_var_operand op ==> plan_holds (alias_halting_cut_state i) op) /\
    (!x. alias_var_mass x (alias_halting_cut_state i) <= 1) /\
    EVERY (\out. ~plan_holds (alias_halting_cut_state i) (Var out))
      (EL i (HD alias_halting_cut_fn.fn_blocks).bb_instructions).inst_outputs /\
    (!x. plan_holds (alias_halting_cut_state i) (Var x) ==>
      MEM x (live_vars_at (liveness_analyze alias_halting_cut_fn) "entry" (SUC i)) \/
      MEM (Var x) (compute_operands (EL i (HD alias_halting_cut_fn.fn_blocks).bb_instructions)) \/
      MEM x (FLAT (MAP (\inst. inst.inst_outputs)
        (TAKE i (HD alias_halting_cut_fn.fn_blocks).bb_instructions))))) (COUNT_LIST 4)
Proof
  EVAL_TAC >> rpt strip_tac >> gvs[is_var_operand_def] >>
  rpt IF_CASES_TAC >> simp[]
QED

Theorem alias_halting_dfs_entry:
  dfs_block_state (liveness_analyze alias_halting_cut_fn)
    (dfg_build_function alias_halting_cut_fn) (cfg_analyze alias_halting_cut_fn)
    alias_halting_cut_fn (init_cleanup_plan_state NONE [] 0 0) "entry"
    (init_cleanup_plan_state NONE [] 0 0)
Proof
  simp[dfs_block_state_def] >> qexistsl_tac [`[]`, `[]`] >> simp[] >>
  irule dfs_aux_call_entry >> EVAL_TAC
QED

Definition alias_offset_cut_state_def:
  alias_offset_cut_state i = SND (THE (generate_block_insts_plan
    (liveness_analyze alias_offset_branch_fn) (dfg_build_function alias_offset_branch_fn)
    (cfg_analyze alias_offset_branch_fn) alias_offset_branch_fn "entry" F 0 3 0
    (TAKE i (HD alias_offset_branch_fn.fn_blocks).bb_instructions)
    (init_cleanup_plan_state NONE [] 0 0)))
End

Theorem alias_offset_cut_trace:
  IS_SOME (generate_block_plan (liveness_analyze alias_offset_branch_fn)
    (dfg_build_function alias_offset_branch_fn) (cfg_analyze alias_offset_branch_fn)
    alias_offset_branch_fn (HD alias_offset_branch_fn.fn_blocks)
    (init_cleanup_plan_state NONE [] 0 0)) /\
  (alias_offset_cut_state 3).ps_stack = [Var "v"] /\
  (alias_offset_cut_state 3).ps_spilled = FEMPTY /\
  ~MEM "v" (live_vars_at (liveness_analyze alias_offset_branch_fn) "skip" 0) /\
  IS_SOME (generate_block_plan (liveness_analyze alias_offset_branch_fn)
    (dfg_build_function alias_offset_branch_fn) (cfg_analyze alias_offset_branch_fn)
    alias_offset_branch_fn (EL 2 alias_offset_branch_fn.fn_blocks) (alias_offset_cut_state 3))
Proof
  EVAL_TAC
QED

Theorem alias_offset_joint_entry_cuts:
  EVERY (\i.
    (!op. MEM op (compute_operands (EL i (HD alias_offset_branch_fn.fn_blocks).bb_instructions)) /\
       is_var_operand op ==> plan_holds (alias_offset_cut_state i) op) /\
    (!x. alias_var_mass x (alias_offset_cut_state i) <= 1) /\
    EVERY (\out. ~plan_holds (alias_offset_cut_state i) (Var out))
      (EL i (HD alias_offset_branch_fn.fn_blocks).bb_instructions).inst_outputs /\
    (!x. plan_holds (alias_offset_cut_state i) (Var x) ==>
      MEM x (live_vars_at (liveness_analyze alias_offset_branch_fn) "entry" (SUC i)) \/
      MEM (Var x) (compute_operands (EL i (HD alias_offset_branch_fn.fn_blocks).bb_instructions))))
    (COUNT_LIST 3)
Proof
  EVAL_TAC >> rpt strip_tac >> gvs[is_var_operand_def] >>
  rpt IF_CASES_TAC >> simp[]
QED

Theorem alias_offset_joint_skip_cut:
  (!op. MEM op (compute_operands (HD (EL 2 alias_offset_branch_fn.fn_blocks).bb_instructions)) /\
     is_var_operand op ==> plan_holds (alias_offset_cut_state 3) op) /\
  (!x. alias_var_mass x (alias_offset_cut_state 3) <= 1) /\
  EVERY (\out. ~plan_holds (alias_offset_cut_state 3) (Var out))
    (HD (EL 2 alias_offset_branch_fn.fn_blocks).bb_instructions).inst_outputs /\
  (!x. plan_holds (alias_offset_cut_state 3) (Var x) ==>
    MEM x (live_vars_at (liveness_analyze alias_offset_branch_fn) "skip" 1) \/
    ((EL 1 (HD alias_offset_branch_fn.fn_blocks).bb_instructions).inst_opcode = OFFSET /\
     MEM x (EL 1 (HD alias_offset_branch_fn.fn_blocks).bb_instructions).inst_outputs))
Proof
  EVAL_TAC >> rpt strip_tac >> gvs[is_var_operand_def] >>
  rpt IF_CASES_TAC >> simp[]
QED

Theorem alias_offset_dfs_skip:
  dfs_block_state (liveness_analyze alias_offset_branch_fn)
    (dfg_build_function alias_offset_branch_fn) (cfg_analyze alias_offset_branch_fn)
    alias_offset_branch_fn (init_cleanup_plan_state NONE [] 0 0) "skip" (alias_offset_cut_state 3)
Proof
  simp[dfs_block_state_def] >> qexistsl_tac [`[]`, `["entry"]`] >> simp[] >>
  `alias_offset_cut_state 3 = (alias_offset_cut_state 3) with
    <|ps_stack := (alias_offset_cut_state 3).ps_stack;
      ps_spilled := (alias_offset_cut_state 3).ps_spilled|>` by simp[] >>
  pop_assum SUBST1_TAC >> irule dfs_aux_call_branch >> qexists_tac `["use"]` >>
  `cfg_succs_of (cfg_analyze alias_offset_branch_fn) "entry" = ["skip"; "use"]` by EVAL_TAC >>
  pop_assum (fn th => rewrite_tac[GSYM th]) >>
  irule dfs_aux_call_succs >> simp[] >>
  qexistsl_tac [`HD alias_offset_branch_fn.fn_blocks`,
    `FST (THE (generate_block_plan (liveness_analyze alias_offset_branch_fn)
      (dfg_build_function alias_offset_branch_fn) (cfg_analyze alias_offset_branch_fn)
      alias_offset_branch_fn (HD alias_offset_branch_fn.fn_blocks)
      (init_cleanup_plan_state NONE [] 0 0)))`,
    `init_cleanup_plan_state NONE [] 0 0`, `[]`] >>
  conj_tac >- EVAL_TAC >>
  conj_tac >- EVAL_TAC >> irule dfs_aux_call_entry >> EVAL_TAC
QED

(* Restricted-ownership probe requested by C1.21.2.6.5. *)
Definition alias_diamond_fn_def:
  alias_diamond_fn = mk_raw_function "alias_diamond"
    [<| bb_label := "entry"; bb_instructions :=
         [mk_inst 0 CALLDATASIZE [] ["seed"];
          mk_inst 1 JMP [Label "header"] []] |>;
     <| bb_label := "header"; bb_instructions :=
         [mk_inst 2 PHI [Label "entry"; Var "seed"; Label "backedge"; Var "z"] ["t"];
          mk_inst 3 CALLDATASIZE [] ["r"];
          mk_inst 4 ADD [Var "t"; Var "r"] ["c"];
          mk_inst 5 JNZ [Var "c"; Label "left"; Label "right"] []] |>;
     <| bb_label := "left"; bb_instructions :=
         [mk_inst 6 ASSIGN [Var "r"] ["u"];
          mk_inst 7 ASSIGN [Var "c"] ["u2"];
          mk_inst 8 JMP [Label "join"] []] |>;
     <| bb_label := "right"; bb_instructions :=
         [mk_inst 9 ASSIGN [Var "r"] ["v"];
          mk_inst 10 ASSIGN [Var "c"] ["v2"];
          mk_inst 11 JMP [Label "join"] []] |>;
     <| bb_label := "join"; bb_instructions :=
         [mk_inst 12 PHI [Label "left"; Var "u"; Label "right"; Var "v"] ["p"];
          mk_inst 13 PHI [Label "left"; Var "u2"; Label "right"; Var "v2"] ["q"];
          mk_inst 14 ADD [Var "p"; Var "q"] ["w"];
          mk_inst 15 ISZERO [Var "w"] ["z"];
          mk_inst 16 JNZ [Var "z"; Label "backedge"; Label "exit"] []] |>;
     <| bb_label := "exit"; bb_instructions := [mk_inst 17 STOP [] []] |>;
     <| bb_label := "backedge"; bb_instructions :=
         [mk_inst 18 JMP [Label "header"] []] |>]
End

Theorem alias_diamond_entries_ready:
  block_entries_ready (cfg_analyze alias_diamond_fn) alias_diamond_fn
Proof
  EVAL_TAC
QED

Theorem alias_diamond_ready:
  codegen_ready_fn alias_diamond_fn
Proof
  EVAL_TAC
QED

Theorem alias_diamond_no_retpc:
  !x. ~retpc_var alias_diamond_fn x
Proof
  simp[retpc_var_def] >> irule copy_phi_var_no_seed >>
  EVAL_TAC >> rpt strip_tac >> gvs[]
QED

Theorem alias_diamond_no_return:
  !inst. MEM inst (fn_insts alias_diamond_fn) ==>
    ~MEM inst.inst_opcode [RET; RETFMP; DRET]
Proof
  EVAL_TAC >> rpt strip_tac >> gvs[]
QED

Theorem alias_diamond_shapes:
  retpc_shape_ok alias_diamond_fn /\ opaque_use_ok alias_diamond_fn
Proof
  simp[retpc_shape_ok_def, opaque_use_ok_def, alias_diamond_no_retpc] >>
  conj_tac
  >- (rpt strip_tac >> drule reachable_fn_insts_nonphi >> simp[] >>
      strip_tac >> drule alias_diamond_no_return >> simp[]) >>
  metis_tac[reachable_retpc_var, alias_diamond_no_retpc]
QED

Definition alias_diamond_plan_def:
  alias_diamond_plan n ps =
    generate_block_plan (liveness_analyze alias_diamond_fn)
      (dfg_build_function alias_diamond_fn) (cfg_analyze alias_diamond_fn)
      alias_diamond_fn (EL n alias_diamond_fn.fn_blocks) ps
End

Definition alias_diamond_e_def:
  alias_diamond_e = THE (alias_diamond_plan 0 (init_cleanup_plan_state NONE [] 0 0))
End

Theorem alias_diamond_e_fields:
  IS_SOME (alias_diamond_plan 0 (init_cleanup_plan_state NONE [] 0 0)) /\
  (SND alias_diamond_e).ps_stack = [Var "seed"] /\
  (SND alias_diamond_e).ps_spilled = FEMPTY
Proof
  EVAL_TAC
QED

Theorem alias_diamond_e_state:
  SND alias_diamond_e =
    (init_cleanup_plan_state NONE [] 0 0 with ps_stack := [Var "seed"])
Proof
  EVAL_TAC
QED

Definition alias_diamond_h_def:
  alias_diamond_h = THE (alias_diamond_plan 1 (SND alias_diamond_e))
End

Theorem alias_diamond_h_fields:
  IS_SOME (alias_diamond_plan 1 (SND alias_diamond_e)) /\
  (SND alias_diamond_h).ps_stack = [Var "r"; Var "c"] /\
  (SND alias_diamond_h).ps_spilled = FEMPTY
Proof
  rewrite_tac[alias_diamond_h_def, alias_diamond_e_state] >>
  rpt conj_tac >> EVAL_TAC
QED

Theorem alias_diamond_h_state:
  SND alias_diamond_h =
    (init_cleanup_plan_state NONE [] 0 0 with ps_stack := [Var "r"; Var "c"])
Proof
  rewrite_tac[alias_diamond_h_def, alias_diamond_e_state] >> EVAL_TAC
QED

Definition alias_diamond_l_def:
  alias_diamond_l = THE (alias_diamond_plan 2 (SND alias_diamond_h))
End

Definition alias_diamond_r_def:
  alias_diamond_r = THE (alias_diamond_plan 3 (SND alias_diamond_h))
End

Theorem alias_diamond_branches:
  IS_SOME (alias_diamond_plan 2 (SND alias_diamond_h)) /\
  IS_SOME (alias_diamond_plan 3 (SND alias_diamond_h)) /\
  (SND alias_diamond_l).ps_stack = [Var "u2"; Var "u"] /\
  (SND alias_diamond_r).ps_stack = [Var "v2"; Var "v"] /\
  (SND alias_diamond_l).ps_spilled = FEMPTY /\
  (SND alias_diamond_r).ps_spilled = FEMPTY
Proof
  rewrite_tac[alias_diamond_l_def, alias_diamond_r_def, alias_diamond_h_state] >>
  rpt conj_tac >> EVAL_TAC
QED

Theorem alias_diamond_branch_states:
  SND alias_diamond_l =
    (init_cleanup_plan_state NONE [] 0 0 with ps_stack := [Var "u2"; Var "u"]) /\
  SND alias_diamond_r =
    (init_cleanup_plan_state NONE [] 0 0 with ps_stack := [Var "v2"; Var "v"])
Proof
  rewrite_tac[alias_diamond_l_def, alias_diamond_r_def, alias_diamond_h_state] >>
  conj_tac >> EVAL_TAC
QED

Definition alias_diamond_jl_def:
  alias_diamond_jl = THE (alias_diamond_plan 4 (SND alias_diamond_l))
End

Definition alias_diamond_jr_def:
  alias_diamond_jr = THE (alias_diamond_plan 4 (SND alias_diamond_r))
End

Theorem alias_wl_iterate_empty:
  wl_iterate c p d [] s = ([],s)
Proof
  rewrite_tac[worklistDefsTheory.wl_iterate_def] >>
  once_rewrite_tac[WhileTheory.WHILE] >> simp[]
QED

Theorem alias_wl_iterate_step:
  wl_step c p d (x::xs,s) = (ys,t) ==>
  wl_iterate c p d (x::xs) s = wl_iterate c p d ys t
Proof
  strip_tac >> rewrite_tac[worklistDefsTheory.wl_iterate_def] >>
  CONV_TAC (LAND_CONV (ONCE_REWRITE_CONV [WhileTheory.WHILE])) >> simp[]
QED

Theorem alias_diamond_liveness_certificate:
  liveness_analyze alias_diamond_fn =
    <| ds_inst :=
        (FEMPTY |++ [(("right",0),["c";"r"]); (("right",1),["v";"c"]);
          (("right",2),["v2";"v"]); (("right",3),["v2";"v"])]) ⊌
        (FEMPTY |++ [(("left",0),["c";"r"]); (("left",1),["u";"c"]);
          (("left",2),["u2";"u"]); (("left",3),["u2";"u"])]) ⊌
        (FEMPTY |++ [(("join",0),["u2";"v2";"u";"v"]);
          (("join",1),["p";"u2";"v2"]); (("join",2),["q";"p"]);
          (("join",3),["w"]); (("join",4),["z"]); (("join",5),["z"])]) ⊌
        (FEMPTY |++ [(("backedge",0),["z"]); (("backedge",1),["z"])]) ⊌
        (FEMPTY |++ [(("entry",0),[]); (("entry",1),["seed"]); (("entry",2),["seed"])]) ⊌
        (FEMPTY |++ [(("header",0),["seed";"z"]); (("header",1),["t"]);
          (("header",2),["r";"t"]); (("header",3),["c";"r"]);
          (("header",4),["c";"r"])]) ⊌
        (FEMPTY |++ [(("exit",0),[]); (("exit",1),[])]);
       ds_boundary := FEMPTY |++ [("right",["c";"r"]); ("left",["c";"r"]);
         ("join",["u2";"v2";"u";"v"]); ("backedge",["z"]);
         ("entry",[]); ("header",["seed";"z"]); ("exit",[])] |>
Proof
  rewrite_tac[liveness_analyze_def, liveness_recompute_def, LET_THM,
    worklistDefsTheory.wl_iterate_def] >>
  CONV_TAC (LAND_CONV (computeLib.RESTR_EVAL_CONV [``While$WHILE``])) >>
  CONV_TAC (LAND_CONV (ONCE_DEPTH_CONV (REWR_CONV WhileTheory.WHILE))) >>
  CONV_TAC (LAND_CONV (computeLib.RESTR_EVAL_CONV [``While$WHILE``])) >>
  CONV_TAC (LAND_CONV (ONCE_DEPTH_CONV (REWR_CONV WhileTheory.WHILE))) >>
  CONV_TAC (LAND_CONV (computeLib.RESTR_EVAL_CONV [``While$WHILE``])) >>
  CONV_TAC (LAND_CONV (ONCE_DEPTH_CONV (REWR_CONV WhileTheory.WHILE))) >>
  CONV_TAC (LAND_CONV (computeLib.RESTR_EVAL_CONV [``While$WHILE``])) >>
  CONV_TAC (LAND_CONV (ONCE_DEPTH_CONV (REWR_CONV WhileTheory.WHILE))) >>
  CONV_TAC (LAND_CONV (computeLib.RESTR_EVAL_CONV [``While$WHILE``])) >>
  CONV_TAC (LAND_CONV (ONCE_DEPTH_CONV (REWR_CONV WhileTheory.WHILE))) >>
  CONV_TAC (LAND_CONV (computeLib.RESTR_EVAL_CONV [``While$WHILE``])) >>
  CONV_TAC (LAND_CONV (ONCE_DEPTH_CONV (REWR_CONV WhileTheory.WHILE))) >>
  CONV_TAC (LAND_CONV (computeLib.RESTR_EVAL_CONV [``While$WHILE``])) >>
  CONV_TAC (LAND_CONV (ONCE_DEPTH_CONV (REWR_CONV WhileTheory.WHILE))) >>
  CONV_TAC (LAND_CONV (computeLib.RESTR_EVAL_CONV [``While$WHILE``])) >>
  CONV_TAC (LAND_CONV (ONCE_DEPTH_CONV (REWR_CONV WhileTheory.WHILE))) >>
  CONV_TAC (LAND_CONV (computeLib.RESTR_EVAL_CONV [``While$WHILE``])) >>
  CONV_TAC (LAND_CONV (ONCE_DEPTH_CONV (REWR_CONV WhileTheory.WHILE))) >>
  CONV_TAC (LAND_CONV (computeLib.RESTR_EVAL_CONV [``While$WHILE``])) >>
  CONV_TAC (LAND_CONV (ONCE_DEPTH_CONV (REWR_CONV WhileTheory.WHILE))) >>
  CONV_TAC (LAND_CONV (computeLib.RESTR_EVAL_CONV [``While$WHILE``])) >>
  CONV_TAC (LAND_CONV (ONCE_DEPTH_CONV (REWR_CONV WhileTheory.WHILE))) >>
  CONV_TAC (LAND_CONV (computeLib.RESTR_EVAL_CONV [``While$WHILE``])) >>
  CONV_TAC (LAND_CONV (ONCE_DEPTH_CONV (REWR_CONV WhileTheory.WHILE))) >>
  CONV_TAC (LAND_CONV (computeLib.RESTR_EVAL_CONV [``While$WHILE``])) >>
  CONV_TAC (LAND_CONV (ONCE_DEPTH_CONV (REWR_CONV WhileTheory.WHILE))) >>
  CONV_TAC (LAND_CONV (computeLib.RESTR_EVAL_CONV [``While$WHILE``])) >>
  CONV_TAC (LAND_CONV (ONCE_DEPTH_CONV (REWR_CONV WhileTheory.WHILE))) >>
  CONV_TAC (LAND_CONV (computeLib.RESTR_EVAL_CONV [``While$WHILE``])) >>
  CONV_TAC (LAND_CONV (ONCE_DEPTH_CONV (REWR_CONV WhileTheory.WHILE))) >>
  CONV_TAC (LAND_CONV (computeLib.RESTR_EVAL_CONV [``While$WHILE``])) >>
  CONV_TAC (LAND_CONV (ONCE_DEPTH_CONV (REWR_CONV WhileTheory.WHILE))) >>
  CONV_TAC (LAND_CONV (computeLib.RESTR_EVAL_CONV [``While$WHILE``])) >>
  CONV_TAC (LAND_CONV (ONCE_DEPTH_CONV (REWR_CONV WhileTheory.WHILE))) >>
  CONV_TAC (LAND_CONV (computeLib.RESTR_EVAL_CONV [``While$WHILE``])) >>
  CONV_TAC (LAND_CONV (ONCE_DEPTH_CONV (REWR_CONV WhileTheory.WHILE))) >>
  CONV_TAC (LAND_CONV (computeLib.RESTR_EVAL_CONV [``While$WHILE``])) >>
  simp[finite_mapTheory.FUNION_FUPDATE_1, finite_mapTheory.FUPDATE_LIST_THM,
    dfAnalyzeDefsTheory.df_state_component_equality, finite_mapTheory.fmap_eq_flookup,
    finite_mapTheory.FLOOKUP_UPDATE, finite_mapTheory.FLOOKUP_FUNION] >>
  conj_tac >> gen_tac >>
  ntac 4 (IF_CASES_TAC >> gvs[]) >>
  ntac 4 (IF_CASES_TAC >> gvs[]) >>
  ntac 4 (IF_CASES_TAC >> gvs[]) >>
  ntac 4 (IF_CASES_TAC >> gvs[]) >>
  ntac 4 (IF_CASES_TAC >> gvs[]) >>
  ntac 4 (IF_CASES_TAC >> gvs[]) >>
  ntac 4 (IF_CASES_TAC >> gvs[])
QED

Theorem alias_diamond_joins:
  IS_SOME (alias_diamond_plan 4 (SND alias_diamond_l)) /\
  IS_SOME (alias_diamond_plan 4 (SND alias_diamond_r)) /\
  FST alias_diamond_jl = FST alias_diamond_jr /\
  (SND alias_diamond_jl).ps_stack = [Var "z"] /\
  (SND alias_diamond_jr).ps_stack = [Var "z"] /\
  (SND alias_diamond_jl).ps_spilled = FEMPTY /\
  (SND alias_diamond_jr).ps_spilled = FEMPTY
Proof
  rewrite_tac[alias_diamond_jl_def, alias_diamond_jr_def, alias_diamond_branch_states] >>
  rpt conj_tac >>
  simp[alias_diamond_plan_def, alias_diamond_liveness_certificate,
    finite_mapTheory.FUPDATE_LIST_THM, finite_mapTheory.FUNION_FUPDATE_1] >>
  CONV_TAC (ONCE_DEPTH_CONV (fn tm =>
    if same_const (fst (strip_comb tm)) ``dfg_build_function`` andalso is_comb tm
    then CHANGED_CONV EVAL tm else NO_CONV tm)) >>
  CONV_TAC (ONCE_DEPTH_CONV (fn tm =>
    if same_const (fst (strip_comb tm)) ``cfg_analyze`` andalso is_comb tm
    then CHANGED_CONV EVAL tm else NO_CONV tm)) >>
  EVAL_TAC
QED

Theorem alias_diamond_join_state:
  SND alias_diamond_jl =
    (init_cleanup_plan_state NONE [] 0 0 with ps_stack := [Var "z"]) /\
  SND alias_diamond_jr =
    (init_cleanup_plan_state NONE [] 0 0 with ps_stack := [Var "z"])
Proof
  rewrite_tac[alias_diamond_jl_def, alias_diamond_jr_def, alias_diamond_branch_states] >>
  conj_tac >> EVAL_TAC
QED

Definition alias_diamond_back_def:
  alias_diamond_back = THE (alias_diamond_plan 6 (SND alias_diamond_jl))
End

Theorem alias_diamond_back_fields:
  IS_SOME (alias_diamond_plan 6 (SND alias_diamond_jl)) /\
  (SND alias_diamond_back).ps_stack = [Var "z"] /\
  (SND alias_diamond_back).ps_spilled = FEMPTY
Proof
  rewrite_tac[alias_diamond_back_def, alias_diamond_join_state] >> EVAL_TAC
QED

Theorem alias_diamond_edges:
  cfg_succs_of (cfg_analyze alias_diamond_fn) "entry" = ["header"] /\
  cfg_succs_of (cfg_analyze alias_diamond_fn) "header" = ["right"; "left"] /\
  cfg_succs_of (cfg_analyze alias_diamond_fn) "right" = ["join"] /\
  cfg_succs_of (cfg_analyze alias_diamond_fn) "join" = ["exit"; "backedge"] /\
  cfg_succs_of (cfg_analyze alias_diamond_fn) "backedge" = ["header"]
Proof
  EVAL_TAC
QED

Theorem alias_diamond_plans:
  alias_diamond_plan 0 (init_cleanup_plan_state NONE [] 0 0) = SOME alias_diamond_e /\
  alias_diamond_plan 1 (SND alias_diamond_e) = SOME alias_diamond_h /\
  alias_diamond_plan 3 (SND alias_diamond_h) = SOME alias_diamond_r /\
  alias_diamond_plan 4 (SND alias_diamond_r) = SOME alias_diamond_jr
Proof
  rpt conj_tac
  >- (mp_tac alias_diamond_e_fields >>
      Cases_on `alias_diamond_plan 0 (init_cleanup_plan_state NONE [] 0 0)` >>
      simp[alias_diamond_e_def])
  >- (mp_tac alias_diamond_h_fields >>
      Cases_on `alias_diamond_plan 1 (SND alias_diamond_e)` >>
      simp[alias_diamond_h_def])
  >- (mp_tac alias_diamond_branches >>
      Cases_on `alias_diamond_plan 3 (SND alias_diamond_h)` >>
      simp[alias_diamond_r_def]) >>
  mp_tac alias_diamond_joins >>
  Cases_on `alias_diamond_plan 4 (SND alias_diamond_r)` >>
  simp[alias_diamond_jr_def]
QED

Theorem alias_diamond_dfs_h:
  dfs_aux_call (liveness_analyze alias_diamond_fn)
    (dfg_build_function alias_diamond_fn) (cfg_analyze alias_diamond_fn) alias_diamond_fn
    (init_cleanup_plan_state NONE [] 0 0) ["header"] ["entry"] (SND alias_diamond_e)
Proof
  `SND alias_diamond_e = (SND alias_diamond_e) with
    <|ps_stack := (SND alias_diamond_e).ps_stack;
      ps_spilled := (SND alias_diamond_e).ps_spilled|>` by simp[] >>
  pop_assum SUBST1_TAC >> irule dfs_aux_call_branch >> qexists_tac `[]` >>
  rewrite_tac[GSYM (cj 1 alias_diamond_edges)] >>
  irule dfs_aux_call_succs >> simp[] >>
  qexistsl_tac [`EL 0 alias_diamond_fn.fn_blocks`, `FST alias_diamond_e`,
    `init_cleanup_plan_state NONE [] 0 0`, `[]`] >>
  simp[GSYM alias_diamond_plan_def, alias_diamond_plans] >>
  conj_tac >- EVAL_TAC >> irule dfs_aux_call_entry >> EVAL_TAC
QED

Theorem alias_diamond_dfs_r:
  dfs_aux_call (liveness_analyze alias_diamond_fn)
    (dfg_build_function alias_diamond_fn) (cfg_analyze alias_diamond_fn) alias_diamond_fn
    (init_cleanup_plan_state NONE [] 0 0) ["right"] ["header"; "entry"] (SND alias_diamond_h)
Proof
  `SND alias_diamond_h = (SND alias_diamond_h) with
    <|ps_stack := (SND alias_diamond_h).ps_stack;
      ps_spilled := (SND alias_diamond_h).ps_spilled|>` by simp[] >>
  pop_assum SUBST1_TAC >> irule dfs_aux_call_branch >> qexists_tac `["left"]` >>
  rewrite_tac[GSYM (cj 2 alias_diamond_edges)] >>
  irule dfs_aux_call_succs >> simp[] >>
  qexistsl_tac [`EL 1 alias_diamond_fn.fn_blocks`, `FST alias_diamond_h`,
    `SND alias_diamond_e`, `[]`] >>
  simp[GSYM alias_diamond_plan_def, alias_diamond_plans, alias_diamond_dfs_h] >> EVAL_TAC
QED

Theorem alias_diamond_dfs_j:
  dfs_aux_call (liveness_analyze alias_diamond_fn)
    (dfg_build_function alias_diamond_fn) (cfg_analyze alias_diamond_fn) alias_diamond_fn
    (init_cleanup_plan_state NONE [] 0 0) ["join"] ["right"; "header"; "entry"] (SND alias_diamond_r)
Proof
  `SND alias_diamond_r = (SND alias_diamond_r) with
    <|ps_stack := (SND alias_diamond_r).ps_stack;
      ps_spilled := (SND alias_diamond_r).ps_spilled|>` by simp[] >>
  pop_assum SUBST1_TAC >> irule dfs_aux_call_branch >> qexists_tac `[]` >>
  rewrite_tac[GSYM (cj 3 alias_diamond_edges)] >>
  irule dfs_aux_call_succs >> simp[] >>
  qexistsl_tac [`EL 3 alias_diamond_fn.fn_blocks`, `FST alias_diamond_r`,
    `SND alias_diamond_h`, `[]`] >>
  simp[GSYM alias_diamond_plan_def, alias_diamond_plans, alias_diamond_dfs_r] >> EVAL_TAC
QED

Theorem alias_diamond_exit_dfs_result:
  generate_fn_plan_aux (liveness_analyze alias_diamond_fn)
    (dfg_build_function alias_diamond_fn) (cfg_analyze alias_diamond_fn) alias_diamond_fn
    ["exit"] ["join"; "right"; "header"; "entry"] (SND alias_diamond_jr) =
    SOME ([SOLabel "exit"; SOPop 1; SOEmit "STOP"],
      ["exit"; "join"; "right"; "header"; "entry"], init_cleanup_plan_state NONE [] 0 0)
Proof
  rewrite_tac[alias_diamond_jr_def, alias_diamond_branch_states] >> EVAL_TAC
QED

Theorem alias_diamond_dfs_back:
  dfs_aux_call (liveness_analyze alias_diamond_fn)
    (dfg_build_function alias_diamond_fn) (cfg_analyze alias_diamond_fn) alias_diamond_fn
    (init_cleanup_plan_state NONE [] 0 0) ["backedge"]
    ["exit"; "join"; "right"; "header"; "entry"] (SND alias_diamond_jr)
Proof
  `SND alias_diamond_jr = (SND alias_diamond_jr) with
    <|ps_stack := (SND alias_diamond_jr).ps_stack;
      ps_spilled := (SND alias_diamond_jr).ps_spilled|>` by simp[] >>
  pop_assum SUBST1_TAC >> irule dfs_aux_call_branch >> qexists_tac `[]` >>
  `SND alias_diamond_jr = (SND alias_diamond_jr) with
    <|ps_alloc := (init_cleanup_plan_state NONE [] 0 0).ps_alloc with
        sa_free_slots := (SND alias_diamond_jr).ps_alloc.sa_free_slots;
      ps_label_counter := (init_cleanup_plan_state NONE [] 0 0).ps_label_counter|>` by
    (rewrite_tac[alias_diamond_jr_def, alias_diamond_branch_states] >> EVAL_TAC) >>
  pop_assum SUBST1_TAC >> irule dfs_aux_call_sibling >>
  qexistsl_tac [`[SOLabel "exit"; SOPop 1; SOEmit "STOP"]`,
    `"exit"`, `["join"; "right"; "header"; "entry"]`] >>
  simp[alias_diamond_exit_dfs_result] >>
  rewrite_tac[GSYM (cj 4 alias_diamond_edges)] >>
  irule dfs_aux_call_succs >> simp[] >>
  qexistsl_tac [`EL 4 alias_diamond_fn.fn_blocks`, `FST alias_diamond_jr`,
    `SND alias_diamond_r`, `[]`] >>
  simp[GSYM alias_diamond_plan_def, alias_diamond_plans, alias_diamond_dfs_j] >> EVAL_TAC
QED

Theorem alias_diamond_dfs_states:
  dfs_block_state (liveness_analyze alias_diamond_fn)
    (dfg_build_function alias_diamond_fn) (cfg_analyze alias_diamond_fn) alias_diamond_fn
    (init_cleanup_plan_state NONE [] 0 0) "entry" (init_cleanup_plan_state NONE [] 0 0) /\
  dfs_block_state (liveness_analyze alias_diamond_fn)
    (dfg_build_function alias_diamond_fn) (cfg_analyze alias_diamond_fn) alias_diamond_fn
    (init_cleanup_plan_state NONE [] 0 0) "header" (SND alias_diamond_e) /\
  dfs_block_state (liveness_analyze alias_diamond_fn)
    (dfg_build_function alias_diamond_fn) (cfg_analyze alias_diamond_fn) alias_diamond_fn
    (init_cleanup_plan_state NONE [] 0 0) "right" (SND alias_diamond_h) /\
  dfs_block_state (liveness_analyze alias_diamond_fn)
    (dfg_build_function alias_diamond_fn) (cfg_analyze alias_diamond_fn) alias_diamond_fn
    (init_cleanup_plan_state NONE [] 0 0) "join" (SND alias_diamond_r) /\
  dfs_block_state (liveness_analyze alias_diamond_fn)
    (dfg_build_function alias_diamond_fn) (cfg_analyze alias_diamond_fn) alias_diamond_fn
    (init_cleanup_plan_state NONE [] 0 0) "backedge" (SND alias_diamond_jr)
Proof
  rewrite_tac[dfs_block_state_def] >> rpt conj_tac
  >- (qexistsl_tac [`[]`, `[]`] >> simp[] >> irule dfs_aux_call_entry >> EVAL_TAC)
  >- (qexistsl_tac [`[]`, `["entry"]`] >> simp[alias_diamond_dfs_h])
  >- (qexistsl_tac [`[]`, `["header"; "entry"]`] >> simp[alias_diamond_dfs_r])
  >- (qexistsl_tac [`[]`, `["right"; "header"; "entry"]`] >> simp[alias_diamond_dfs_j]) >>
  qexistsl_tac [`[]`, `["exit"; "join"; "right"; "header"; "entry"]`] >>
  simp[alias_diamond_dfs_back]
QED

Theorem alias_diamond_lineage_header:
  lineage_state (liveness_analyze alias_diamond_fn)
    (dfg_build_function alias_diamond_fn) (cfg_analyze alias_diamond_fn) alias_diamond_fn
    (init_cleanup_plan_state NONE [] 0 0) "header" (SND alias_diamond_e)
Proof
  `SND alias_diamond_e = (SND alias_diamond_e) with
    <|ps_stack := (SND alias_diamond_e).ps_stack;
      ps_spilled := (SND alias_diamond_e).ps_spilled|>` by simp[] >>
  pop_assum SUBST1_TAC >> irule lineage_state_step >> simp[alias_diamond_dfs_states] >>
  qexistsl_tac [`EL 0 alias_diamond_fn.fn_blocks`, `FST alias_diamond_e`, `NONE`, `"entry"`, `F`,
    `init_cleanup_plan_state NONE [] 0 0`, `init_cleanup_plan_state NONE [] 0 0`,
    `SND alias_diamond_e`] >>
  simp[GSYM alias_diamond_plan_def, alias_diamond_plans, alias_diamond_dfs_states,
       alias_diamond_edges] >> conj_tac >- EVAL_TAC >>
  reverse conj_tac >- (irule lineage_state_entry >> EVAL_TAC) >>
  `init_cleanup_plan_state NONE [] 0 0 with
    <|ps_cleanup_height := NONE; ps_cleanup_promised := F|> =
    init_cleanup_plan_state NONE [] 0 0` by simp[init_cleanup_plan_state_def] >>
  simp[GSYM alias_diamond_plan_def, alias_diamond_plans]
QED

Theorem alias_diamond_lineage_right:
  lineage_state (liveness_analyze alias_diamond_fn)
    (dfg_build_function alias_diamond_fn) (cfg_analyze alias_diamond_fn) alias_diamond_fn
    (init_cleanup_plan_state NONE [] 0 0) "right" (SND alias_diamond_h)
Proof
  `SND alias_diamond_h = (SND alias_diamond_h) with
    <|ps_stack := (SND alias_diamond_h).ps_stack;
      ps_spilled := (SND alias_diamond_h).ps_spilled|>` by simp[] >>
  pop_assum SUBST1_TAC >> irule lineage_state_step >> simp[alias_diamond_dfs_states] >>
  qexistsl_tac [`EL 1 alias_diamond_fn.fn_blocks`, `FST alias_diamond_h`, `NONE`, `"header"`, `F`,
    `SND alias_diamond_e`, `SND alias_diamond_e`, `SND alias_diamond_h`] >>
  simp[GSYM alias_diamond_plan_def, alias_diamond_plans, alias_diamond_dfs_states,
       alias_diamond_edges, alias_diamond_lineage_header] >>
  `SND alias_diamond_e with
    <|ps_cleanup_height := NONE; ps_cleanup_promised := F|> =
    SND alias_diamond_e` by
    simp[alias_diamond_e_state, init_cleanup_plan_state_def] >>
  simp[alias_diamond_plans] >> EVAL_TAC
QED

Theorem alias_diamond_lineage_join:
  lineage_state (liveness_analyze alias_diamond_fn)
    (dfg_build_function alias_diamond_fn) (cfg_analyze alias_diamond_fn) alias_diamond_fn
    (init_cleanup_plan_state NONE [] 0 0) "join" (SND alias_diamond_r)
Proof
  `SND alias_diamond_r = (SND alias_diamond_r) with
    <|ps_stack := (SND alias_diamond_r).ps_stack;
      ps_spilled := (SND alias_diamond_r).ps_spilled|>` by simp[] >>
  pop_assum SUBST1_TAC >> irule lineage_state_step >> simp[alias_diamond_dfs_states] >>
  qexistsl_tac [`EL 3 alias_diamond_fn.fn_blocks`, `FST alias_diamond_r`, `NONE`, `"right"`, `F`,
    `SND alias_diamond_h`, `SND alias_diamond_h`, `SND alias_diamond_r`] >>
  simp[GSYM alias_diamond_plan_def, alias_diamond_plans, alias_diamond_dfs_states,
       alias_diamond_edges, alias_diamond_lineage_right] >>
  rewrite_tac[alias_diamond_h_state, alias_diamond_r_def] >>
  rewrite_tac[alias_diamond_h_state] >> EVAL_TAC
QED

Theorem alias_diamond_lineage_backedge:
  lineage_state (liveness_analyze alias_diamond_fn)
    (dfg_build_function alias_diamond_fn) (cfg_analyze alias_diamond_fn) alias_diamond_fn
    (init_cleanup_plan_state NONE [] 0 0) "backedge" (SND alias_diamond_jr)
Proof
  `SND alias_diamond_jr = (SND alias_diamond_jr) with
    <|ps_stack := (SND alias_diamond_jr).ps_stack;
      ps_spilled := (SND alias_diamond_jr).ps_spilled|>` by simp[] >>
  pop_assum SUBST1_TAC >> irule lineage_state_step >> simp[alias_diamond_dfs_states] >>
  qexistsl_tac [`EL 4 alias_diamond_fn.fn_blocks`, `FST alias_diamond_jr`, `NONE`, `"join"`, `F`,
    `SND alias_diamond_r`, `SND alias_diamond_r`, `SND alias_diamond_jr`] >>
  simp[GSYM alias_diamond_plan_def, alias_diamond_plans, alias_diamond_dfs_states,
       alias_diamond_edges, alias_diamond_lineage_join] >>
  rewrite_tac[alias_diamond_branch_states, alias_diamond_jr_def] >>
  rewrite_tac[alias_diamond_branch_states] >> EVAL_TAC
QED

Theorem alias_diamond_back_plan:
  alias_diamond_plan 6 (SND alias_diamond_jr) =
    SOME (FST alias_diamond_back, SND alias_diamond_jr)
Proof
  rewrite_tac[alias_diamond_back_def, alias_diamond_join_state] >> EVAL_TAC
QED

Definition alias_diamond_loop_entry_def:
  alias_diamond_loop_entry = SND alias_diamond_e with
    <|ps_stack := (SND alias_diamond_jr).ps_stack;
      ps_spilled := (SND alias_diamond_jr).ps_spilled|>
End

Theorem alias_diamond_lineage_loop:
  lineage_state (liveness_analyze alias_diamond_fn)
    (dfg_build_function alias_diamond_fn) (cfg_analyze alias_diamond_fn) alias_diamond_fn
    (init_cleanup_plan_state NONE [] 0 0) "header" alias_diamond_loop_entry
Proof
  rewrite_tac[alias_diamond_loop_entry_def] >> irule lineage_state_step >>
  simp[alias_diamond_dfs_states] >>
  qexistsl_tac [`EL 6 alias_diamond_fn.fn_blocks`, `FST alias_diamond_back`, `NONE`, `"backedge"`, `F`,
    `SND alias_diamond_jr`, `SND alias_diamond_jr`, `SND alias_diamond_jr`] >>
  simp[GSYM alias_diamond_plan_def, alias_diamond_back_plan, alias_diamond_dfs_states,
       alias_diamond_edges, alias_diamond_lineage_backedge] >>
  rewrite_tac[alias_diamond_join_state, alias_diamond_back_def] >>
  rewrite_tac[alias_diamond_join_state] >> EVAL_TAC
QED

Theorem alias_diamond_loop_fields:
  alias_diamond_loop_entry =
    (init_cleanup_plan_state NONE [] 0 0 with ps_stack := [Var "z"]) /\
  normalize_operand (dfg_build_function alias_diamond_fn) [] (Var "u") = Var "r" /\
  normalize_operand (dfg_build_function alias_diamond_fn) [] (Var "v") = Var "r" /\
  ~plan_holds alias_diamond_loop_entry (Var "u") /\
  ~plan_holds alias_diamond_loop_entry (Var "v")
Proof
  rewrite_tac[alias_diamond_loop_entry_def, alias_diamond_join_state] >>
  rpt conj_tac >> EVAL_TAC
QED

Definition alias_diamond_header_phi_def:
  alias_diamond_header_phi =
    generate_phi_plan (EL 0 (EL 1 alias_diamond_fn.fn_blocks).bb_instructions)
      (live_vars_at (liveness_analyze alias_diamond_fn) "header" 1) F
      alias_diamond_loop_entry
End

Theorem alias_diamond_header_phi_fields:
  (SND alias_diamond_header_phi).ps_stack = [Var "t"] /\
  (SND alias_diamond_header_phi).ps_spilled = FEMPTY
Proof
  rewrite_tac[alias_diamond_header_phi_def, alias_diamond_loop_fields] >> EVAL_TAC
QED

Theorem alias_diamond_header_root_prefix:
  IS_SOME (generate_block_insts_plan (liveness_analyze alias_diamond_fn)
    (dfg_build_function alias_diamond_fn) (cfg_analyze alias_diamond_fn)
    alias_diamond_fn "header" F 0 2 0
    (TAKE 2 (EL 1 alias_diamond_fn.fn_blocks).bb_instructions) alias_diamond_loop_entry) /\
  (SND (THE (generate_block_insts_plan (liveness_analyze alias_diamond_fn)
    (dfg_build_function alias_diamond_fn) (cfg_analyze alias_diamond_fn)
    alias_diamond_fn "header" F 0 2 0
    (TAKE 2 (EL 1 alias_diamond_fn.fn_blocks).bb_instructions) alias_diamond_loop_entry))).ps_stack =
    [Var "r"; Var "t"]
Proof
  rewrite_tac[alias_diamond_loop_fields] >> conj_tac >> EVAL_TAC
QED

Theorem alias_diamond_header_replay:
  alias_diamond_plan 1 alias_diamond_loop_entry = SOME alias_diamond_h
Proof
  rewrite_tac[alias_diamond_loop_fields] >> EVAL_TAC
QED

(* C2.1 finite mechanism domain: retain a header-root alias on the
   alternate (exit) edge; independently try copying a consumed PHI source. *)
Definition alias_search_fn_def:
  alias_search_fn retain absent two = alias_diamond_fn with fn_blocks :=
    MAP (\bb.
      if bb.bb_label = "header" /\ retain then
        bb with bb_instructions :=
          TAKE 2 bb.bb_instructions ++
          [mk_inst 20 ASSIGN [Var "r"] ["keep1"]] ++
          (if two then [mk_inst 21 ASSIGN [Var "keep1"] ["keep2"]] else []) ++
          DROP 2 bb.bb_instructions
      else if bb.bb_label = "exit" /\ retain then
        bb with bb_instructions :=
          mk_inst 22 ISZERO [Var (if two then "keep2" else "keep1")] ["sink"] ::
          bb.bb_instructions
      else if bb.bb_label = "join" /\ absent then
        bb with bb_instructions :=
          TAKE 2 bb.bb_instructions ++
          [mk_inst 23 ASSIGN [Var "u"] ["miss1"]] ++
          (if two then [mk_inst 24 ASSIGN [Var "miss1"] ["miss2"]] else []) ++
          DROP 2 bb.bb_instructions
      else bb) alias_diamond_fn.fn_blocks
End

Theorem alias_search_readiness:
  codegen_ready_fn (alias_search_fn F F F) /\
  codegen_ready_fn (alias_search_fn T F F) /\
  codegen_ready_fn (alias_search_fn T F T)
Proof
  rpt conj_tac >> CONV_TAC (RAND_CONV EVAL) >>
  rewrite_tac[codegen_ready_fn_def] >> rpt conj_tac
  >- EVAL_TAC >- EVAL_TAC >- EVAL_TAC >- EVAL_TAC
  >- EVAL_TAC >- EVAL_TAC >- EVAL_TAC >- EVAL_TAC
  >- EVAL_TAC >- EVAL_TAC >- EVAL_TAC >- EVAL_TAC
  >- EVAL_TAC >- EVAL_TAC >- EVAL_TAC >- EVAL_TAC
  >- EVAL_TAC >- EVAL_TAC >- EVAL_TAC >- EVAL_TAC
  >- EVAL_TAC >- EVAL_TAC >- EVAL_TAC >- EVAL_TAC
  >- EVAL_TAC >- EVAL_TAC >- EVAL_TAC >- EVAL_TAC
  >- EVAL_TAC >- EVAL_TAC >- EVAL_TAC >- EVAL_TAC
  >- EVAL_TAC >- EVAL_TAC >- EVAL_TAC >> EVAL_TAC
QED

Theorem alias_search_rejected:
  ~codegen_ready_fn (alias_search_fn F T F) /\
  ~codegen_ready_fn (alias_search_fn F T T) /\
  ~codegen_ready_fn (alias_search_fn T T F) /\
  ~codegen_ready_fn (alias_search_fn T T T)
Proof
  rpt conj_tac >> CONV_TAC (RAND_CONV (RAND_CONV EVAL)) >> EVAL_TAC
QED

Definition alias_search_plan_def:
  alias_search_plan two n ps =
    generate_block_plan (liveness_analyze (alias_search_fn T F two))
      (dfg_build_function (alias_search_fn T F two))
      (cfg_analyze (alias_search_fn T F two)) (alias_search_fn T F two)
      (EL n (alias_search_fn T F two).fn_blocks) ps
End

Definition alias_search_e_def:
  alias_search_e two = THE (alias_search_plan two 0 (init_cleanup_plan_state NONE [] 0 0))
End

Theorem alias_search_e_state:
  !two. IS_SOME (alias_search_plan two 0 (init_cleanup_plan_state NONE [] 0 0)) /\
    SND (alias_search_e two) =
      (init_cleanup_plan_state NONE [] 0 0 with ps_stack := [Var "seed"])
Proof
  Cases >> EVAL_TAC
QED

Definition alias_search_h_def:
  alias_search_h two = THE (alias_search_plan two 1 (SND (alias_search_e two)))
End

Theorem alias_search_h_state:
  !two. IS_SOME (alias_search_plan two 1 (SND (alias_search_e two))) /\
    SND (alias_search_h two) =
      (init_cleanup_plan_state NONE [] 0 0 with ps_stack :=
        [Var "r"; Var (if two then "keep2" else "keep1"); Var "c"])
Proof
  rewrite_tac[alias_search_h_def, alias_search_e_state] >> Cases >> EVAL_TAC
QED

Definition alias_search_r_def:
  alias_search_r two = THE (alias_search_plan two 3 (SND (alias_search_h two)))
End

Theorem alias_search_r_state:
  !two. IS_SOME (alias_search_plan two 3 (SND (alias_search_h two))) /\
    SND (alias_search_r two) =
      (init_cleanup_plan_state NONE [] 0 0 with ps_stack :=
        [Var (if two then "keep2" else "keep1"); Var "v2"; Var "v"])
Proof
  rewrite_tac[alias_search_r_def, alias_search_h_state] >> Cases >> EVAL_TAC
QED

Definition alias_search_j_def:
  alias_search_j two = THE (alias_search_plan two 4 (SND (alias_search_r two)))
End

Theorem alias_search_j_state:
  !two. IS_SOME (alias_search_plan two 4 (SND (alias_search_r two))) /\
    SND (alias_search_j two) =
      (init_cleanup_plan_state NONE [] 0 0 with ps_stack :=
        [Var (if two then "keep2" else "keep1"); Var "z"])
Proof
  rewrite_tac[alias_search_j_def, alias_search_r_state] >> Cases >> EVAL_TAC
QED

Definition alias_search_b_def:
  alias_search_b two = THE (alias_search_plan two 6 (SND (alias_search_j two)))
End

Theorem alias_search_b_state:
  !two. IS_SOME (alias_search_plan two 6 (SND (alias_search_j two))) /\
    SND (alias_search_b two) =
      (init_cleanup_plan_state NONE [] 0 0 with ps_stack := [Var "z"])
Proof
  rewrite_tac[alias_search_b_def, alias_search_j_state] >> Cases >> EVAL_TAC
QED


(* The exit-only demand retains the alias at join, but backedge cleanup
   removes it before returning to the root-defining header. *)
Definition alias_search_loop_def:
  alias_search_loop two = SND (alias_search_e two) with
    <|ps_stack := (SND (alias_search_b two)).ps_stack;
      ps_spilled := (SND (alias_search_b two)).ps_spilled|>
End

Theorem alias_search_loop_state:
  !two. alias_search_loop two =
    (init_cleanup_plan_state NONE [] 0 0 with ps_stack := [Var "z"])
Proof
  rewrite_tac[alias_search_loop_def, alias_search_e_state, alias_search_b_state] >>
  EVAL_TAC
QED

Theorem alias_search_header_replay:
  !two. alias_search_plan two 1 (alias_search_loop two) = SOME (alias_search_h two)
Proof
  rewrite_tac[alias_search_loop_state, alias_search_h_def, alias_search_e_state] >>
  Cases >> EVAL_TAC
QED

Theorem alias_search_header_liveness:
  !two.
    live_vars_at (liveness_analyze (alias_search_fn T F two)) "header" 1 = ["t"] /\
    live_vars_at (liveness_analyze (alias_search_fn T F two)) "header" 2 = ["r"; "t"]
Proof
  Cases >> conj_tac >> EVAL_TAC
QED

Theorem alias_search_header_prefix_plan:
  !two. generate_block_insts_plan (liveness_analyze (alias_search_fn T F two))
      (dfg_build_function (alias_search_fn T F two))
      (cfg_analyze (alias_search_fn T F two)) (alias_search_fn T F two)
      "header" F 0 2 0
      (TAKE 2 (EL 1 (alias_search_fn T F two).fn_blocks).bb_instructions)
      (init_cleanup_plan_state NONE [] 0 0 with ps_stack := [Var "z"]) =
    SOME ([SOPoke 0 (Var "t"); SOEmit "CALLDATASIZE"; SOSwap 1],
      init_cleanup_plan_state NONE [] 0 0 with ps_stack := [Var "r"; Var "t"])
Proof
  Cases >>
  simp[alias_search_fn_def, generate_block_insts_plan_def,
       alias_search_header_liveness] >> EVAL_TAC
QED

Theorem alias_search_header_prefixes:
  !two.
    (SND (generate_phi_plan
      (EL 0 (EL 1 (alias_search_fn T F two).fn_blocks).bb_instructions)
      (live_vars_at (liveness_analyze (alias_search_fn T F two)) "header" 1) F
      (alias_search_loop two))).ps_stack = [Var "t"] /\
    IS_SOME (generate_block_insts_plan (liveness_analyze (alias_search_fn T F two))
      (dfg_build_function (alias_search_fn T F two))
      (cfg_analyze (alias_search_fn T F two)) (alias_search_fn T F two)
      "header" F 0 2 0
      (TAKE 2 (EL 1 (alias_search_fn T F two).fn_blocks).bb_instructions)
      (alias_search_loop two)) /\
    (SND (THE (generate_block_insts_plan (liveness_analyze (alias_search_fn T F two))
      (dfg_build_function (alias_search_fn T F two))
      (cfg_analyze (alias_search_fn T F two)) (alias_search_fn T F two)
      "header" F 0 2 0
      (TAKE 2 (EL 1 (alias_search_fn T F two).fn_blocks).bb_instructions)
      (alias_search_loop two)))).ps_stack = [Var "r"; Var "t"]
Proof
  rewrite_tac[alias_search_loop_state, alias_search_header_prefix_plan] >>
  simp[alias_search_header_liveness, init_cleanup_plan_state_def, init_plan_state_def] >>
  Cases >> EVAL_TAC
QED

Theorem alias_search_no_retained_root_alias:
  !two at. plan_holds (alias_search_loop two) at ==>
    normalize_operand (dfg_build_function (alias_search_fn T F two)) [] at = at
Proof
  simp[alias_search_loop_state, plan_holds_def, init_cleanup_plan_state_def,
       init_plan_state_def] >> rpt strip_tac >> gvs[] >> Cases_on `two` >> EVAL_TAC
QED
(* Bounded residual-alias search: no planner stack is manufactured. Padding
   is defined at entry and read in the loop header; the body copy is demanded
   only by the exit edge. The path is planned one actual block at a time. *)
Definition alias_buried_fn_def:
  alias_buried_fn phi n flip = alias_diamond_fn with fn_blocks :=
    MAP (\bb.
      if bb.bb_label = "entry" then
        bb with bb_instructions :=
          TAKE 1 bb.bb_instructions ++
          GENLIST (\k. mk_inst (30 + k) CALLDATASIZE []
            [EL k ["d0"; "d1"; "d2"; "d3"]]) n ++ DROP 1 bb.bb_instructions
      else if bb.bb_label = "header" then
        bb with bb_instructions :=
          TAKE 1 bb.bb_instructions ++
          GENLIST (\k. mk_inst (40 + k) PHI
            [Label "entry"; Var (EL k ["d0"; "d1"; "d2"; "d3"]);
             Label "backedge"; Var (EL k ["f0"; "f1"; "f2"; "f3"])]
            [EL k ["s0"; "s1"; "s2"; "s3"]]) n ++
          [EL 1 bb.bb_instructions; EL 2 bb.bb_instructions;
           mk_inst 5 JNZ [Var "c"; Label (if flip then "right" else "left");
             Label (if flip then "left" else "right")] []]
      else if bb.bb_label = "join" then
        bb with bb_instructions := TAKE 2 bb.bb_instructions ++
          [mk_inst 50 ASSIGN [Var (if phi then "t" else "r")] ["buried"]] ++
          GENLIST (\k. mk_inst (60 + k) ADD
            [Var (EL k ["s0"; "s1"; "s2"; "s3"]); Lit 1w]
            [EL k ["f0"; "f1"; "f2"; "f3"]]) n ++ DROP 2 bb.bb_instructions
      else if bb.bb_label = "exit" then
        bb with bb_instructions :=
          mk_inst 51 ISZERO [Var "buried"] ["sink"] :: bb.bb_instructions
      else bb) alias_diamond_fn.fn_blocks
End

Definition alias_buried_plan_def:
  alias_buried_plan phi n flip idx ps =
    generate_block_plan (liveness_analyze (alias_buried_fn phi n flip))
      (dfg_build_function (alias_buried_fn phi n flip))
      (cfg_analyze (alias_buried_fn phi n flip)) (alias_buried_fn phi n flip)
      (EL idx (alias_buried_fn phi n flip).fn_blocks) ps
End

Definition alias_buried_path_def:
  (alias_buried_path phi n flip [] = init_cleanup_plan_state NONE [] 0 0) /\
  (alias_buried_path phi n flip (idx::rest) =
    SND (THE (alias_buried_plan phi n flip idx (alias_buried_path phi n flip rest))))
End

Theorem alias_buried_zero_def:
  dfg_get_def (dfg_build_function (alias_buried_fn F 0 F)) "buried" =
    SOME (mk_inst 50 ASSIGN [Var "r"] ["buried"]) /\
  dfg_get_def (dfg_build_function (alias_buried_fn F 0 F)) "r" =
    SOME (mk_inst 3 CALLDATASIZE [] ["r"])
Proof
  EVAL_TAC
QED

Theorem alias_buried_zero_probe:
  normalize_operand (dfg_build_function (alias_buried_fn F 0 F)) []
    (Var "buried") = Var "r" /\
  (alias_buried_path F 0 F [4; 3; 1; 0]).ps_stack =
    [Var "buried"; Var "z"] /\
  ~plan_holds (alias_buried_path F 0 F [6; 4; 3; 1; 0]) (Var "buried")
Proof
  conj_tac
  >- (simp[Once normalize_operand_def, GSYM dfg_get_def_def,
           alias_buried_zero_def, mk_inst_def] >>
      simp[Once normalize_operand_def, GSYM dfg_get_def_def,
           alias_buried_zero_def, mk_inst_def]) >>
  conj_tac >- EVAL_TAC >>
  EVAL_TAC
QED

Definition alias_buried_path_ok_def:
  (alias_buried_path_ok phi n b [] <=> T) /\
  (alias_buried_path_ok phi n b (idx::rest) <=>
    alias_buried_path_ok phi n b rest /\
    IS_SOME (alias_buried_plan phi n b idx (alias_buried_path phi n b rest)))
End

(* Evaluate one innermost closed planner application per proof step. *)
local
  fun buried_plan_stage tm =
    ((RAND_CONV buried_plan_stage) ORELSEC
     (RATOR_CONV buried_plan_stage) ORELSEC
     (fn t =>
       if same_const (fst (strip_comb t)) ``alias_buried_plan`` andalso
          length (snd (strip_comb t)) = 5
       then computeLib.EVAL_CONV t
       else NO_CONV t)) tm
in
Theorem alias_buried_padding_plans_succeed:
  !n b phi. n <= 4 ==>
    alias_buried_path_ok phi n b [6; 4; (if b then 2 else 3); 1; 0]
Proof
  map_every qx_gen_tac [`n`, `b`, `phi`] >> strip_tac >>
  rewrite_tac[alias_buried_path_ok_def] >>
  `n = 0 \/ n = 1 \/ n = 2 \/ n = 3 \/ n = 4` by decide_tac >> gvs[] >>
  Cases_on `b` >> Cases_on `phi` >> rpt conj_tac >>
  simp[] >> rewrite_tac[alias_buried_path_def] >>
  rpt (CONV_TAC buried_plan_stage) >> EVAL_TAC
QED

Theorem alias_buried_four_inventory:
  (alias_buried_path F 4 F [4;3;1;0]).ps_stack =
    [Var "f2"; Var "f1"; Var "f0"; Var "buried"; Var "f3"; Var "z"]
Proof
  rewrite_tac[Once alias_buried_path_def] >>
  CONV_TAC (LHS_CONV (RAND_CONV (RAND_CONV (RAND_CONV
    (RAND_CONV computeLib.EVAL_CONV))))) >> EVAL_TAC
QED

Theorem alias_buried_backedge_state:
  !n b phi. n <= 4 ==>
    alias_buried_path phi n b [6;4;(if b then 2 else 3);1;0] =
      (init_cleanup_plan_state NONE [] 0 0 with ps_stack :=
        REVERSE (TAKE n (MAP Var ["f0";"f1";"f2";"f3"])) ++ [Var "z"])
Proof
  map_every qx_gen_tac [`n`, `b`, `phi`] >> strip_tac >>
  `n = 0 \/ n = 1 \/ n = 2 \/ n = 3 \/ n = 4` by decide_tac >> gvs[] >>
  Cases_on `b` >> Cases_on `phi` >> simp[] >>
  rewrite_tac[alias_buried_path_def] >>
  rpt (CONV_TAC buried_plan_stage) >> EVAL_TAC
QED
end

(* The buried name is dead on the backedge, but is not below every live
   slot: z is still below it. Thus clean_stack_plan includes it in physical
   and to_cleanup, not retained. popmany_plan removes it even when cleanup
   is promised; promises do not retain the identity of a dead slot. *)
Theorem alias_buried_cleanup_diagnostic:
  MEM "buried" (live_vars_at (liveness_analyze (alias_buried_fn F 4 F))
    "join" (LENGTH (EL 4 (alias_buried_fn F 4 F).fn_blocks).bb_instructions)) /\
  ~MEM "buried" (input_vars_from "join"
    (EL 6 (alias_buried_fn F 4 F).fn_blocks).bb_instructions
    (live_vars_at (liveness_analyze (alias_buried_fn F 4 F)) "backedge" 0)) /\
  ~below_all_live (Var "buried")
    (input_vars_from "join" (EL 6 (alias_buried_fn F 4 F).fn_blocks).bb_instructions
      (live_vars_at (liveness_analyze (alias_buried_fn F 4 F)) "backedge" 0))
    (alias_buried_path F 4 F [4;3;1;0]).ps_stack
Proof
  rewrite_tac[alias_buried_four_inventory] >> rpt conj_tac
  >- EVAL_TAC >- EVAL_TAC >> EVAL_TAC
QED

Definition alias_buried_replay_def:
  alias_buried_replay phi n b h promised = alias_buried_plan phi n b 1
    (alias_buried_path phi n b [6;4;(if b then 2 else 3);1;0] with
      <|ps_cleanup_height := h; ps_cleanup_promised := promised|>)
End

Theorem alias_buried_replay_filter:
  !n b phi h promised. n <= 4 ==>
    IS_SOME (alias_buried_replay phi n b h promised) /\
    ~plan_holds (SND (THE (alias_buried_replay phi n b h promised))) (Var "buried")
Proof
  map_every qx_gen_tac [`n`, `b`, `phi`, `h`, `promised`] >> strip_tac >>
  simp[alias_buried_replay_def, alias_buried_backedge_state] >>
  `n = 0 \/ n = 1 \/ n = 2 \/ n = 3 \/ n = 4` by decide_tac >> gvs[]
  >- (Cases_on `b` >> Cases_on `phi` >> conj_tac
      >- EVAL_TAC >- EVAL_TAC >- EVAL_TAC >- EVAL_TAC
      >- EVAL_TAC >- EVAL_TAC >- EVAL_TAC >> EVAL_TAC)
  >- (Cases_on `b` >> Cases_on `phi` >> conj_tac
      >- EVAL_TAC >- EVAL_TAC >- EVAL_TAC >- EVAL_TAC
      >- EVAL_TAC >- EVAL_TAC >- EVAL_TAC >> EVAL_TAC)
  >- (Cases_on `b` >> Cases_on `phi` >> conj_tac
      >- EVAL_TAC >- EVAL_TAC >- EVAL_TAC >- EVAL_TAC
      >- EVAL_TAC >- EVAL_TAC >- EVAL_TAC >> EVAL_TAC)
  >- (Cases_on `b` >> Cases_on `phi` >> conj_tac
      >- EVAL_TAC >- EVAL_TAC >- EVAL_TAC >- EVAL_TAC
      >- EVAL_TAC >- EVAL_TAC >- EVAL_TAC >> EVAL_TAC) >>
  Cases_on `b` >> Cases_on `phi` >> conj_tac
  >- EVAL_TAC >- EVAL_TAC >- EVAL_TAC >- EVAL_TAC
  >- EVAL_TAC >- EVAL_TAC >- EVAL_TAC >> EVAL_TAC
QED

Theorem eval_one_phi_without_predecessor:
  s.vs_prev_bb = NONE ==> eval_one_phi s inst = NONE
Proof
  simp[eval_one_phi_def] >> Cases_on `inst.inst_outputs` >> simp[]
QED

Theorem alias_compute_operand_use:
  MEM (Var x) (compute_operands inst) ==> MEM x (inst_uses inst)
Proof
  simp[inst_uses_def, passSharedDefsTheory.MEM_operand_vars_eq_Var,
       compute_operands_def] >>
  rpt IF_CASES_TAC >> simp[asmIRTheory.get_non_label_operands_def, MEM_FILTER] >>
  rpt strip_tac >> gvs[] >>
  Cases_on `inst.inst_operands` >> gvs[]
QED

Theorem alias_live_cut_origin:
  wf_function fn /\ MEM lbl (cfg_analyze fn).cfg_dfs_pre /\
  lookup_block lbl fn.fn_blocks = SOME bb /\ i < LENGTH bb.bb_instructions /\
  inst = EL i bb.bb_instructions /\
  MEM x (live_vars_at (liveness_analyze fn) lbl (SUC i)) ==>
  MEM x (live_vars_at (liveness_analyze fn) lbl i) \/ MEM x inst.inst_outputs
Proof
  strip_tac >>
  drule livenessAnalysisPropsTheory.live_vars_at_transfer >> simp[] >>
  disch_then (qspecl_then [`lbl`, `bb`, `i`] mp_tac) >>
  simp[] >> strip_tac >>
  Cases_on `MEM x inst.inst_outputs` >> simp[] >>
  gvs[liveness_transfer_def, live_update_def, inst_defs_def, MEM_FILTER]
QED

Theorem alias_regular_plan_live_cut_coverage:
  wf_function fn /\ MEM lbl (cfg_analyze fn).cfg_dfs_pre /\
  lookup_block lbl fn.fn_blocks = SOME bb /\ i < LENGTH bb.bb_instructions /\
  inst = EL i bb.bb_instructions /\ inst.inst_opcode <> JMP /\
  (!y. MEM y (live_vars_at (liveness_analyze fn) lbl i) ==> plan_holds ps (Var y)) /\
  generate_regular_inst_plan (liveness_analyze fn) dfg cfg fn inst
    (live_vars_at (liveness_analyze fn) lbl (SUC i)) halting next_term lbl ps = (ops,qs) ==>
  !x. MEM x (live_vars_at (liveness_analyze fn) lbl (SUC i)) ==> plan_holds qs (Var x)
Proof
  rpt strip_tac >>
  `!op. MEM op (compute_operands inst) /\ is_var_operand op ==> plan_holds ps op` by
    (rpt strip_tac >> Cases_on `op` >> gvs[is_var_operand_def] >>
     first_x_assum irule >>
     drule alias_compute_operand_use >> strip_tac >>
     drule livenessAnalysisPropsTheory.live_vars_at_uses >> simp[] >>
     disch_then irule >> goal_assum (drule_at Any) >> gvs[]) >>
  `MEM x (live_vars_at (liveness_analyze fn) lbl i) \/ MEM x inst.inst_outputs` by
    metis_tac[alias_live_cut_origin] >>
  metis_tac[alias_regular_plan_holds_live]
QED

Theorem alias_jmp_plan_live_cut_coverage:
  wf_function fn /\ MEM lbl (cfg_analyze fn).cfg_dfs_pre /\
  lookup_block lbl fn.fn_blocks = SOME bb /\ i < LENGTH bb.bb_instructions /\
  inst = EL i bb.bb_instructions /\ inst_wf inst /\ inst.inst_opcode = JMP /\
  (!y. MEM y (live_vars_at (liveness_analyze fn) lbl i) ==> plan_holds ps (Var y)) /\
  generate_regular_inst_plan (liveness_analyze fn) dfg cfg fn inst
    (live_vars_at (liveness_analyze fn) lbl (SUC i)) halting next_term lbl ps = (ops,qs) ==>
  !x. MEM x (live_vars_at (liveness_analyze fn) lbl (SUC i)) ==> plan_holds qs (Var x)
Proof
  rpt strip_tac >>
  `MEM x (live_vars_at (liveness_analyze fn) lbl i) \/ MEM x inst.inst_outputs` by
    metis_tac[alias_live_cut_origin] >>
  `?target. inst.inst_operands = [Label target] /\ inst.inst_outputs = []` by
    gvs[inst_wf_def] >>
  metis_tac[alias_jmp_plan_holds_live, MEM]
QED

Theorem alias_offset_plan_live_cut_coverage:
  wf_function fn /\ MEM lbl (cfg_analyze fn).cfg_dfs_pre /\
  lookup_block lbl fn.fn_blocks = SOME bb /\ i < LENGTH bb.bb_instructions /\
  inst = EL i bb.bb_instructions /\ inst_wf inst /\ inst.inst_opcode = OFFSET /\
  (!y. MEM y (live_vars_at (liveness_analyze fn) lbl i) ==> plan_holds ps (Var y)) ==>
  !x. MEM x (live_vars_at (liveness_analyze fn) lbl (SUC i)) ==>
    plan_holds (SND (generate_offset_plan inst ps)) (Var x)
Proof
  rpt strip_tac >>
  `MEM x (live_vars_at (liveness_analyze fn) lbl i) \/ MEM x inst.inst_outputs` by
    metis_tac[alias_live_cut_origin] >>
  `?v target out. inst.inst_operands = [Lit v; Label target] /\ inst.inst_outputs = [out]` by
    gvs[inst_wf_def, listTheory.LENGTH_EQ_NUM_compute] >>
  gvs[generate_offset_plan_def, plan_holds_def, stackModelTheory.stack_push_def] >>
  metis_tac[]
QED

Theorem alias_inst_plan_live_cut_coverage:
  wf_function fn /\ MEM lbl (cfg_analyze fn).cfg_dfs_pre /\
  lookup_block lbl fn.fn_blocks = SOME bb /\ i < LENGTH bb.bb_instructions /\
  inst = EL i bb.bb_instructions /\ inst_wf inst /\ inst.inst_opcode <> PHI /\
  ~is_param_opcode inst.inst_opcode /\
  (!y. MEM y (live_vars_at (liveness_analyze fn) lbl i) ==> plan_holds ps (Var y)) /\
  generate_inst_plan (liveness_analyze fn) dfg cfg fn inst
    (live_vars_at (liveness_analyze fn) lbl (SUC i)) halting next_term lbl ps = SOME (ops,qs) ==>
  !x. MEM x (live_vars_at (liveness_analyze fn) lbl (SUC i)) ==> plan_holds qs (Var x)
Proof
  rpt strip_tac >> gvs[] >>
  qpat_x_assum `generate_inst_plan _ _ _ _ _ _ _ _ _ _ = _` mp_tac >>
  simp[generate_inst_plan_def] >>
  Cases_on `is_pre_codegen_opcode (EL i bb.bb_instructions).inst_opcode` >> simp[] >>
  Cases_on `(EL i bb.bb_instructions).inst_opcode = INVOKE /\ ~invoke_operands_wf (EL i bb.bb_instructions)` >> simp[] >>
  Cases_on `(EL i bb.bb_instructions).inst_opcode = OFFSET`
  >- (simp[] >> strip_tac >> gvs[] >>
      metis_tac[alias_offset_plan_live_cut_coverage, pairTheory.SND]) >>
  simp[] >> Cases_on `(EL i bb.bb_instructions).inst_opcode = NOP`
  >- (simp[] >> strip_tac >> gvs[] >>
      `MEM x (live_vars_at (liveness_analyze fn) lbl i) \/ MEM x (EL i bb.bb_instructions).inst_outputs` by
        metis_tac[alias_live_cut_origin] >>
      gvs[inst_wf_def]) >>
  simp[] >>
  Cases_on `generate_regular_inst_plan (liveness_analyze fn) dfg cfg fn (EL i bb.bb_instructions)
    (live_vars_at (liveness_analyze fn) lbl (SUC i)) halting next_term lbl ps` >> simp[] >>
  strip_tac >> gvs[] >>
  Cases_on `(EL i bb.bb_instructions).inst_opcode = JMP`
  >- metis_tac[alias_jmp_plan_live_cut_coverage] >>
  metis_tac[alias_regular_plan_live_cut_coverage]
QED

Theorem alias_body_plan_live_cut_coverage:
  !insts prefix i ps ops qs.
  wf_function fn /\ MEM lbl (cfg_analyze fn).cfg_dfs_pre /\
  lookup_block lbl fn.fn_blocks = SOME bb /\
  bb.bb_instructions = prefix ++ insts /\ LENGTH prefix = i + n_params /\
  EVERY (\inst. inst_wf inst /\ inst.inst_opcode <> PHI /\
                  ~is_param_opcode inst.inst_opcode) insts /\
  (!y. MEM y (live_vars_at (liveness_analyze fn) lbl (i + n_params)) ==> plan_holds ps (Var y)) /\
  generate_block_insts_plan (liveness_analyze fn) dfg cfg fn lbl halting
    n_params (LENGTH bb.bb_instructions) i insts ps = SOME (ops,qs) ==>
  !x. MEM x (live_vars_at (liveness_analyze fn) lbl (LENGTH bb.bb_instructions)) ==>
    plan_holds qs (Var x)
Proof
  Induct >> rpt gen_tac >> strip_tac
  >- (gvs[generate_block_insts_plan_def] >> metis_tac[]) >>
  `i + n_params < LENGTH bb.bb_instructions /\
   EL (i + n_params) bb.bb_instructions = h` by
    simp[EL_APPEND_EQN] >>
  `i + n_params + 1 = SUC (i + n_params)` by decide_tac >>
  `live_vars_at (liveness_analyze fn) lbl
      (if insts = [] then LENGTH bb.bb_instructions else i + n_params + 1) =
   live_vars_at (liveness_analyze fn) lbl (SUC (i + n_params))` by
    (Cases_on `insts` >> gvs[] >> AP_TERM_TAC >> simp[]) >>
  gvs[Once generate_block_insts_plan_def, AllCaseEqs()] >>
  `!y. MEM y (live_vars_at (liveness_analyze fn) lbl (SUC (i + n_params))) ==>
       plan_holds ps' (Var y)` by
    (rpt strip_tac >> irule alias_inst_plan_live_cut_coverage >>
     goal_assum (drule_at Any) >> simp[] >> metis_tac[]) >>
  `i + 1 + n_params = SUC (i + n_params) /\
   i + (n_params + SUC (LENGTH insts)) = LENGTH insts + SUC (i + n_params) /\
   i + (n_params + (LENGTH insts + 1)) = LENGTH insts + SUC (i + n_params)` by decide_tac >>
  first_x_assum (qspecl_then [`i + 1`, `ps'`, `rest_ops`, `qs`] mp_tac) >>
  simp[]
QED

Theorem alias_live_prefix_origin:
  !n. wf_function fn /\ MEM lbl (cfg_analyze fn).cfg_dfs_pre /\
  lookup_block lbl fn.fn_blocks = SOME bb /\ n <= LENGTH bb.bb_instructions /\
  MEM x (live_vars_at (liveness_analyze fn) lbl n) ==>
  (MEM x (live_vars_at (liveness_analyze fn) lbl 0) /\
   (!i. i < n ==> MEM x (live_vars_at (liveness_analyze fn) lbl (SUC i)))) \/
  (?j. j < n /\ MEM x (EL j bb.bb_instructions).inst_outputs /\
   (!i. j <= i /\ i < n ==> MEM x (live_vars_at (liveness_analyze fn) lbl (SUC i))))
Proof
  Induct >- simp[] >> strip_tac >>
  Cases_on `MEM x (EL n bb.bb_instructions).inst_outputs`
  >- (disj2_tac >> qexists_tac `n` >> simp[] >> rpt strip_tac >>
      `i = n` by decide_tac >> gvs[]) >>
  `n < LENGTH bb.bb_instructions` by decide_tac >>
  `MEM x (live_vars_at (liveness_analyze fn) lbl n)` by
    metis_tac[alias_live_cut_origin] >>
  qpat_x_assum `_ ==> _` mp_tac >> simp[] >> strip_tac
  >- (disj1_tac >> simp[] >> rpt strip_tac >>
      Cases_on `i = n` >- gvs[] >> first_x_assum irule >> decide_tac) >>
  disj2_tac >> qexists_tac `j` >> simp[] >> rpt strip_tac >>
  Cases_on `i = n` >- gvs[] >> first_x_assum irule >> decide_tac
QED

Theorem alias_lineage_join_phi_cut_coverage:
  liveness = liveness_analyze fn /\ dfg = dfg_build_function fn /\
  cfg = cfg_analyze fn /\ codegen_ready_fn fn /\
  lineage_state liveness dfg cfg fn
    (init_cleanup_plan_state ch growth spill_base lbl_ctr) lbl ps /\
  lookup_block lbl fn.fn_blocks = SOME bb /\
  1 < LENGTH (cfg_preds_of cfg lbl) /\
  MEM x (live_vars_at liveness lbl (LENGTH (collect_phis bb.bb_instructions))) ==>
  plan_holds (FOLDL (\s p.
    SND (generate_phi_plan (FST p) (SND p) halting s)) ps
    (MAP (\i. (EL i (collect_phis bb.bb_instructions),
              live_vars_at liveness lbl (SUC i)))
      (COUNT_LIST (LENGTH (collect_phis bb.bb_instructions))))) (Var x)
Proof
  strip_tac >>
  `wf_function fn` by gvs[codegen_ready_fn_def] >>
  `MEM lbl (cfg_analyze fn).cfg_dfs_pre` by
    (`cfg_reachable_of (cfg_analyze fn) lbl` by
       metis_tac[alias_lineage_reachable] >>
     drule cfgAnalysisPropsTheory.cfg_analyze_reachable_sets >>
     simp[pred_setTheory.EXTENSION] >> metis_tac[]) >>
  `?rest. bb.bb_instructions = collect_phis bb.bb_instructions ++ rest` by
    metis_tac[alias_collect_phis_prefix] >>
  `LENGTH (collect_phis bb.bb_instructions) <= LENGTH bb.bb_instructions` by
    (qpat_assum `bb.bb_instructions = _` (mp_tac o AP_TERM ``LENGTH : instruction list -> num``) >>
     simp[]) >>
  `!j. j < LENGTH (collect_phis bb.bb_instructions) ==>
    EL j bb.bb_instructions = EL j (collect_phis bb.bb_instructions)` by
    (rpt strip_tac >>
     qpat_assum `bb.bb_instructions = _`
       (fn th => CONV_TAC (LHS_CONV (RAND_CONV (REWR_CONV th)))) >>
     simp[EL_APPEND_EQN]) >>
  `((MEM x (live_vars_at (liveness_analyze fn) lbl 0) /\
     (!i. i < LENGTH (collect_phis bb.bb_instructions) ==>
       MEM x (live_vars_at (liveness_analyze fn) lbl (SUC i)))) \/
    (?j. j < LENGTH (collect_phis bb.bb_instructions) /\
     MEM x (EL j bb.bb_instructions).inst_outputs /\
     (!i. j <= i /\ i < LENGTH (collect_phis bb.bb_instructions) ==>
       MEM x (live_vars_at (liveness_analyze fn) lbl (SUC i)))))` by
    (irule alias_live_prefix_origin >> simp[] >> metis_tac[])
  >- (ho_match_mp_tac alias_lineage_join_phi_fold_lower_coverage >>
      goal_assum (drule_at Any) >> simp[] >> disj1_tac >>
      simp[plan_holds_def] >> disj1_tac >>
      irule alias_lineage_join_ordinary_coverage >>
      goal_assum (drule_at Any) >> simp[] >> metis_tac[]) >>
  `?out. (EL j (collect_phis bb.bb_instructions)).inst_outputs = [out]` by
    (irule alias_ready_phi_single_output >> goal_assum (drule_at Any) >>
     simp[EL_MEM]) >>
  `out = x` by metis_tac[MEM] >>
  ho_match_mp_tac alias_lineage_join_phi_fold_lower_coverage >>
  goal_assum (drule_at Any) >> simp[] >> metis_tac[]
QED

Theorem alias_collect_phis_length:
  !insts. LENGTH (collect_phis insts) = phi_prefix_length insts
Proof
  Induct >> simp[collect_phis_def, phi_prefix_length_def] >>
  Cases_on `h.inst_opcode = PHI` >> simp[collect_phis_def, phi_prefix_length_def]
QED

Theorem alias_ready_phi_suffix:
  codegen_ready_fn fn /\ lookup_block lbl fn.fn_blocks = SOME bb ==>
  EVERY (\inst. inst_wf inst /\ inst.inst_opcode <> PHI)
    (DROP (LENGTH (collect_phis bb.bb_instructions)) bb.bb_instructions)
Proof
  strip_tac >>
  `MEM bb fn.fn_blocks` by metis_tac[lookup_block_MEM] >>
  `wf_function fn /\ fn_inst_wf fn` by gvs[codegen_ready_fn_def] >>
  `bb_well_formed bb` by metis_tac[wf_function_def] >>
  `EVERY inst_wf bb.bb_instructions` by metis_tac[fn_inst_wf_every_bb] >>
  simp[EVERY_CONJ, alias_collect_phis_length] >> conj_tac
  >- metis_tac[EVERY_DROP] >>
  irule scfg_phi_suffix_nonphi >> gvs[bb_well_formed_def]
QED

Theorem alias_ready_param_partition:
  codegen_ready_fn fn /\ lookup_block lbl fn.fn_blocks = SOME bb ==>
  bb.bb_instructions = get_params bb.bb_instructions ++ non_param_insts bb /\
  EVERY (\inst. ~is_param_opcode inst.inst_opcode) (non_param_insts bb) /\
  (bb <> HD fn.fn_blocks ==> get_params bb.bb_instructions = [])
Proof
  strip_tac >>
  `MEM bb fn.fn_blocks` by metis_tac[lookup_block_MEM] >>
  `canonical_param_prefix fn` by gvs[codegen_ready_fn_def] >>
  drule (iffLR callLayoutDefsTheory.canonical_param_prefix_iff) >> strip_tac >>
  (Cases_on `bb = entry`
  >- (qpat_x_assum `bb = entry` SUBST_ALL_TAC >>
      rename1 `no_param_insts tail` >>
      `EVERY (\inst. is_param_opcode inst.inst_opcode) (users ++ fmp ++ retpc)` by
        (gvs[EVERY_MEM, is_param_opcode_def] >> metis_tac[]) >>
      `get_params (users ++ fmp ++ retpc ++ tail) = users ++ fmp ++ retpc` by
        (irule get_params_prefix >> gvs[callLayoutDefsTheory.no_param_insts_def]) >>
      `FILTER (\inst. ~is_param_opcode inst.inst_opcode) users = []` by
        (gvs[FILTER_EQ_NIL, EVERY_MEM, is_param_opcode_def]) >>
      `FILTER (\inst. ~is_param_opcode inst.inst_opcode) tail = tail` by
        gvs[FILTER_EQ_ID, callLayoutDefsTheory.no_param_insts_def] >>
      gvs[non_param_insts_def, FILTER_APPEND, is_param_opcode_def,
          callLayoutDefsTheory.no_param_insts_def]) >>
  `no_param_insts bb.bb_instructions` by gvs[EVERY_MEM] >>
  `FILTER (\inst. ~is_param_opcode inst.inst_opcode) bb.bb_instructions = bb.bb_instructions` by
    gvs[FILTER_EQ_ID, callLayoutDefsTheory.no_param_insts_def] >>
  `get_params bb.bb_instructions = []` by
    (Cases_on `bb.bb_instructions` >> gvs[get_params_def, callLayoutDefsTheory.no_param_insts_def]) >>
  gvs[non_param_insts_def, callLayoutDefsTheory.no_param_insts_def])
QED

Theorem alias_ready_entry_body:
  codegen_ready_fn fn /\ lookup_block lbl fn.fn_blocks = SOME bb /\
  bb = HD fn.fn_blocks ==>
  cfg_preds_of (cfg_analyze fn) bb.bb_label = [] /\
  collect_phis bb.bb_instructions = [] /\
  EVERY (\inst. inst_wf inst /\ inst.inst_opcode <> PHI /\
               ~is_param_opcode inst.inst_opcode) (non_param_insts bb)
Proof
  strip_tac >>
  `cfg_preds_of (cfg_analyze fn) bb.bb_label = [] /\
   collect_phis bb.bb_instructions = []` by
    (Cases_on `fn.fn_blocks` >>
     gvs[codegen_ready_fn_def, block_entries_ready_def, entry_block_def, NULL_EQ,
         lookup_block_def, FIND_thm]) >>
  simp[] >>
  `EVERY (\inst. inst_wf inst /\ inst.inst_opcode <> PHI) bb.bb_instructions` by
    (drule_all alias_ready_phi_suffix >> simp[]) >>
  drule_all alias_ready_param_partition >> strip_tac >>
  gvs[EVERY_MEM, non_param_insts_def, MEM_FILTER] >> metis_tac[]
QED

Theorem alias_prepare_params_entry_fresh:
  codegen_ready_fn fn /\ ps.ps_stack = [] /\ ps.ps_spilled = FEMPTY /\
  MEM inst (non_param_insts (HD fn.fn_blocks)) /\ MEM x inst.inst_outputs ==>
  ~plan_holds (SND (prepare_params_plan (liveness_analyze fn) fn ps)) (Var x)
Proof
  strip_tac >> strip_tac >>
  `MEM x (MAP (\inst. HD inst.inst_outputs)
    (get_params (HD fn.fn_blocks).bb_instructions))` by
    (irule alias_prepare_params_parameter_provenance >> simp[] >> metis_tac[]) >>
  `param_insts_from 0 (get_params (HD fn.fn_blocks).bb_instructions)` by
    (drule canonical_get_params_layout >> simp[]) >>
  drule param_insts_flat_outputs >> disch_then (SUBST_ALL_TAC o SYM) >>
  Cases_on `fn.fn_blocks`
  >- gvs[codegen_ready_fn_def, callLayoutDefsTheory.canonical_param_prefix_def] >>
  rename1 `fn.fn_blocks = entry::rest` >> gvs[] >>
  `lookup_block entry.bb_label fn.fn_blocks = SOME entry` by
    simp[lookup_block_def, FIND_thm] >>
  drule_all alias_ready_param_partition >> strip_tac >>
  `ssa_form fn` by gvs[codegen_ready_fn_def] >>
  qpat_x_assum `ssa_form fn` mp_tac >>
  simp[ssa_form_def, fn_insts_def, fn_insts_blocks_def] >>
  qpat_x_assum `entry.bb_instructions = _` (fn th =>
    CONV_TAC (RAND_CONV (ONCE_REWRITE_CONV [th]))) >>
  simp[MAP_APPEND, FLAT_APPEND, ALL_DISTINCT_APPEND] >>
  `MEM x (FLAT (MAP (\i. i.inst_outputs) (non_param_insts entry)))` by
    (simp[MEM_FLAT, MEM_MAP] >> metis_tac[]) >>
  metis_tac[]
QED

Theorem alias_prepare_params_initialized_budget:
  codegen_ready_fn fn ==>
  alias_var_budget []
    (SND (prepare_params_plan (liveness_analyze fn) fn
      ((init_cleanup_plan_state ch growth spill_base lbl_ctr) with
        <| ps_cleanup_height := h; ps_cleanup_promised := promised |>)))
Proof
  strip_tac >> irule alias_prepare_params_entry_budget >>
  simp[init_cleanup_plan_state_def, init_plan_state_def]
QED

Theorem alias_prepare_params_initialized_provenance:
  plan_holds
    (SND (prepare_params_plan live fn
      ((init_cleanup_plan_state ch growth spill_base lbl_ctr) with
        <| ps_cleanup_height := h; ps_cleanup_promised := promised |>))) (Var x) ==>
  MEM x (MAP (\inst. HD inst.inst_outputs)
    (get_params (HD fn.fn_blocks).bb_instructions))
Proof
  strip_tac >> irule alias_prepare_params_parameter_provenance >>
  goal_assum (drule_at Any) >>
  simp[init_cleanup_plan_state_def, init_plan_state_def]
QED

Theorem alias_prepare_params_initialized_fresh:
  codegen_ready_fn fn /\
  MEM inst (non_param_insts (HD fn.fn_blocks)) /\ MEM x inst.inst_outputs ==>
  ~plan_holds
    (SND (prepare_params_plan (liveness_analyze fn) fn
      ((init_cleanup_plan_state ch growth spill_base lbl_ctr) with
        <| ps_cleanup_height := h; ps_cleanup_promised := promised |>))) (Var x)
Proof
  strip_tac >> irule alias_prepare_params_entry_fresh >>
  simp[init_cleanup_plan_state_def, init_plan_state_def] >>
  metis_tac[]
QED

Theorem alias_ready_inst_arity:
  codegen_ready_fn fn /\ MEM bb fn.fn_blocks /\
  MEM inst bb.bb_instructions /\ inst.inst_opcode <> PHI ==>
  LENGTH (compute_operands inst) <= 16
Proof
  simp[codegen_ready_fn_def, EVERY_MEM, codegen_ready_inst_def] >>
  metis_tac[]
QED

Theorem alias_non_param_cut_member:
  lookup_block lbl fn.fn_blocks = SOME bb /\
  DROP i (non_param_insts bb) = inst::rest ==>
  MEM inst (fn_insts fn)
Proof
  strip_tac >>
  `MEM inst (non_param_insts bb)` by metis_tac[rich_listTheory.MEM_DROP_IMP, MEM] >>
  simp[fn_insts_def, MEM_fn_insts_blocks_iff] >>
  qexists_tac `bb` >>
  gvs[non_param_insts_def, MEM_FILTER] >> metis_tac[lookup_block_MEM]
QED

Theorem alias_ready_cut_arity:
  codegen_ready_fn fn /\ lookup_block lbl fn.fn_blocks = SOME bb /\
  DROP i (non_param_insts bb) = inst::rest /\ inst.inst_opcode <> PHI ==>
  LENGTH (compute_operands inst) <= 16
Proof
  strip_tac >> irule alias_ready_inst_arity >>
  `MEM inst (non_param_insts bb)` by metis_tac[rich_listTheory.MEM_DROP_IMP, MEM] >>
  gvs[non_param_insts_def, MEM_FILTER] >> metis_tac[lookup_block_MEM]
QED

Theorem alias_ready_cut_outputs_distinct:
  codegen_ready_fn fn /\ lookup_block lbl fn.fn_blocks = SOME bb /\
  DROP i (non_param_insts bb) = inst::rest ==>
  ALL_DISTINCT inst.inst_outputs
Proof
  strip_tac >> irule genBlockSimTheory.codegen_ready_inst_outputs_distinct >>
  goal_assum (drule_at Any) >> irule alias_non_param_cut_member >>
  metis_tac[]
QED

Theorem alias_phi_prefix_plan_state:
  !phis i body ps ops qs.
    EVERY (\inst. inst.inst_opcode = PHI) phis /\
    block_len = i + n_params + LENGTH (phis ++ body) /\
    generate_block_insts_prefix liveness dfg cfg fn lbl halting n_params
      block_len i (LENGTH phis) (phis ++ body) ps = SOME (ops, qs) ==>
    qs = FOLDL (\s p. SND (generate_phi_plan (FST p) (SND p) halting s)) ps
      (MAPi (\j inst. (inst, live_vars_at liveness lbl (i + n_params + SUC j))) phis)
Proof
  Induct >> simp[generate_block_insts_prefix_def, indexedListsTheory.MAPi_def] >>
  rpt gen_tac >> strip_tac >> gvs[] >>
  gvs[generate_inst_plan_def, is_pre_codegen_opcode_def, AllCaseEqs()] >>
  first_x_assum (qspecl_then [`i + 1`, `body'`] mp_tac) >>
  simp[] >> disch_then drule >> strip_tac >> gvs[combinTheory.o_DEF] >>
  AP_TERM_TAC >> AP_THM_TAC >> AP_TERM_TAC >>
  simp[FUN_EQ_THM] >> gen_tac >> AP_TERM_TAC >> decide_tac
QED

Theorem alias_nonjoin_edge_preds:
  MEM lbl (cfg_succs_of (cfg_analyze fn) pred) /\
  LENGTH (cfg_preds_of (cfg_analyze fn) lbl) <= 1 ==>
  cfg_preds_of (cfg_analyze fn) lbl = [pred]
Proof
  strip_tac >>
  `MEM pred (cfg_preds_of (cfg_analyze fn) lbl)` by
    metis_tac[cfgAnalysisPropsTheory.cfg_edge_symmetry_uncond] >>
  Cases_on `cfg_preds_of (cfg_analyze fn) lbl` >> gvs[] >>
  Cases_on `t` >> gvs[]
QED

(* The actual preparation and an arbitrary instruction cut.  Unlike an
   isolated prefix plan, this retains the full-list lookahead. *)
Theorem alias_block_plan_cut:
  generate_block_plan liveness dfg cfg fn bb ps = SOME (ops, ps_after) /\
  j <= LENGTH (non_param_insts bb) ==>
  ?param_ops ps_param clean_ops ps_clean prefix_ops ps_cut body_ops.
    (if bb = HD fn.fn_blocks then prepare_params_plan liveness fn ps
     else ([], ps)) = (param_ops, ps_param) /\
    (if LENGTH (cfg_preds_of cfg bb.bb_label) = 1
     then clean_stack_plan liveness cfg fn bb ps_param
     else ([], ps_param)) = (clean_ops, ps_clean) /\
    generate_block_insts_prefix liveness dfg cfg fn bb.bb_label
      (bb_is_halting bb) (LENGTH (get_params bb.bb_instructions))
      (LENGTH bb.bb_instructions) 0 j (non_param_insts bb) ps_clean =
      SOME (prefix_ops, ps_cut) /\
    generate_block_insts_plan liveness dfg cfg fn bb.bb_label
      (bb_is_halting bb) (LENGTH (get_params bb.bb_instructions))
      (LENGTH bb.bb_instructions) j (DROP j (non_param_insts bb)) ps_cut =
      SOME (body_ops, ps_after) /\
    ops = SOLabel bb.bb_label :: param_ops ++ clean_ops ++ prefix_ops ++ body_ops
Proof
  strip_tac >>
  qpat_x_assum `generate_block_plan _ _ _ _ _ _ = _` mp_tac >>
  simp[generate_block_plan_def] >> pairarg_tac >> simp[] >>
  pairarg_tac >> simp[AllCaseEqs()] >> strip_tac >> gvs[] >>
  qexistsl_tac [`clean_ops`, `ps2`] >>
  Cases_on `LENGTH (cfg_preds_of cfg bb.bb_label) = 1` >> gvs[] >>
  metis_tac[generate_block_insts_plan_split, arithmeticTheory.ADD_CLAUSES]
QED

Theorem alias_entry_block_plan_cut:
  codegen_ready_fn fn /\ lookup_block lbl fn.fn_blocks = SOME bb /\
  bb = HD fn.fn_blocks /\
  generate_block_plan liveness dfg (cfg_analyze fn) fn bb ps = SOME (ops, qs) ==>
  ?param_ops ps_param body_ops.
    prepare_params_plan liveness fn ps = (param_ops, ps_param) /\
    generate_block_insts_plan liveness dfg (cfg_analyze fn) fn bb.bb_label
      (bb_is_halting bb) (LENGTH (get_params bb.bb_instructions))
      (LENGTH bb.bb_instructions) 0 (non_param_insts bb) ps_param =
      SOME (body_ops, qs) /\
    ops = SOLabel bb.bb_label :: param_ops ++ body_ops
Proof
  strip_tac >>
  `cfg_preds_of (cfg_analyze fn) bb.bb_label = []` by
    metis_tac[alias_ready_entry_body] >>
  drule alias_block_plan_cut >> disch_then (qspec_then `0` mp_tac) >>
  simp[generate_block_insts_prefix_def] >> metis_tac[]
QED

Theorem alias_nonentry_block_plan_cut:
  codegen_ready_fn fn /\ lookup_block lbl fn.fn_blocks = SOME bb /\
  bb <> HD fn.fn_blocks /\
  generate_block_plan liveness dfg cfg fn bb ps = SOME (ops, qs) ==>
  ?clean_ops ps_clean phi_ops ps_phi body_ops.
    bb.bb_instructions = non_param_insts bb /\
    (if LENGTH (cfg_preds_of cfg bb.bb_label) = 1
     then clean_stack_plan liveness cfg fn bb ps else ([], ps)) =
      (clean_ops, ps_clean) /\
    ps_phi = FOLDL (\s p. SND (generate_phi_plan (FST p) (SND p)
      (bb_is_halting bb) s)) ps_clean
      (MAP (\i. (EL i (collect_phis bb.bb_instructions),
                 live_vars_at liveness bb.bb_label (SUC i)))
        (COUNT_LIST (LENGTH (collect_phis bb.bb_instructions)))) /\
    generate_block_insts_plan liveness dfg cfg fn bb.bb_label
      (bb_is_halting bb) 0 (LENGTH bb.bb_instructions)
      (LENGTH (collect_phis bb.bb_instructions))
      (DROP (LENGTH (collect_phis bb.bb_instructions)) bb.bb_instructions)
      ps_phi = SOME (body_ops, qs) /\
    ops = SOLabel bb.bb_label :: clean_ops ++ phi_ops ++ body_ops
Proof
  strip_tac >>
  drule_all alias_ready_param_partition >> strip_tac >>
  `get_params bb.bb_instructions = [] /\
   non_param_insts bb = bb.bb_instructions` by metis_tac[APPEND] >>
  `?tail. bb.bb_instructions = collect_phis bb.bb_instructions ++ tail` by
    metis_tac[alias_collect_phis_prefix] >>
  `LENGTH (collect_phis bb.bb_instructions) <= LENGTH (non_param_insts bb)` by
    (qpat_assum `bb.bb_instructions = collect_phis _ ++ _`
       (mp_tac o AP_TERM ``LENGTH : instruction list -> num``) >> simp[]) >>
  drule_all alias_block_plan_cut >> strip_tac >>
  gvs[] >>
  `EVERY (\inst. inst.inst_opcode = PHI) (collect_phis bb.bb_instructions)` by
    (simp[EVERY_MEM] >> metis_tac[livenessProofsTheory.collect_phis_mem]) >>
  `LENGTH bb.bb_instructions = 0 + 0 +
     LENGTH (collect_phis bb.bb_instructions ++ tail)` by
    (qpat_assum `bb.bb_instructions = collect_phis _ ++ _`
       (mp_tac o AP_TERM ``LENGTH : instruction list -> num``) >> simp[]) >>
  `generate_block_insts_prefix liveness dfg cfg fn bb.bb_label (bb_is_halting bb) 0
     (LENGTH bb.bb_instructions) 0 (LENGTH (collect_phis bb.bb_instructions))
     (collect_phis bb.bb_instructions ++ tail) ps_clean = SOME (prefix_ops, ps_cut)` by
    metis_tac[] >>
  drule_all alias_phi_prefix_plan_state >> simp[] >> strip_tac >>
  `MAPi (\j inst. (inst, live_vars_at liveness bb.bb_label (SUC j)))
      (collect_phis bb.bb_instructions) =
   MAP (\i. (EL i (collect_phis bb.bb_instructions),
             live_vars_at liveness bb.bb_label (SUC i)))
      (COUNT_LIST (LENGTH (collect_phis bb.bb_instructions)))` by
    (irule LIST_EQ >> simp[indexedListsTheory.LENGTH_MAPi,
       indexedListsTheory.EL_MAPi, LENGTH_COUNT_LIST, EL_MAP, EL_COUNT_LIST]) >>
  gvs[] >> metis_tac[]
QED

(* Lower-inventory probe ledger (not a universal lineage inventory theorem).
   Checked boundaries:
   - alias_prepare_params_entry_demand anchors the actual post-parameter cut.
   - alias_lineage_join_phi_cut_coverage anchors the post-PHI fold, using
     lives i = live_vars_at liveness lbl (SUC i), not a constant end-live list.
   - alias_body_plan_live_cut_coverage transports total cut coverage through
     the actual non-PHI/non-parameter instruction suffix to block end.
   - alias_clean_stack_holds_input preserves already-held selected inputs.
   - alias_ready_nonjoin_input_liveout transports ordinary nonjoin entry
     demand to its predecessor's block end.
   - alias_entry_block_plan_cut excludes entry cleanup and exposes the
     actual parameter preparation and full-lookahead body plan.
   - alias_nonentry_block_plan_cut identifies non_param_insts with the
     original instructions and the PHI prefix state with the indexed fold.
   - alias_ready_entry_body and alias_ready_phi_suffix exclude body PHIs;
     alias_ready_param_partition excludes nonentry parameters.
   - alias_nonjoin_edge_preds identifies the unique analyzed predecessor
     from the actual lineage edge.
   Remaining assembly obligations before lineage_state_ind can be closed:
   Combine these boundaries into conditional block-end lower coverage, then use
       lineage_state_ind: entry uses the parameter anchor, step uses the
       predecessor block-end result and the stack/spill record update.
   These are not supplied as hypotheses to an exported inventory claim.
   No statement here constrains stale extra held names or root writes. *)
Theorem alias_clean_stack_holds_input:
  cfg_preds_of cfg bb.bb_label = [pred] /\
  MEM x (input_vars_from pred bb.bb_instructions (live_vars_at live bb.bb_label 0)) /\
  plan_holds ps (Var x) ==>
  plan_holds (SND (clean_stack_plan live cfg fn bb ps)) (Var x)
Proof
  strip_tac >>
  Cases_on `Var x IN FDOM ps.ps_spilled`
  >- (Cases_on `clean_stack_plan live cfg fn bb ps` >>
      drule alias_clean_stack_spilled >> gvs[plan_holds_def]) >>
  `MEM (Var x) ps.ps_stack` by gvs[plan_holds_def] >>
  simp[clean_stack_plan_def] >>
  Cases_on `LENGTH (cfg_succs_of cfg pred) <= 1`
  >- simp[plan_holds_def] >>
  Cases_on `lookup_block pred fn.fn_blocks`
  >- simp[plan_holds_def] >> simp[] >>
  qmatch_goalsub_abbrev_tac `if guard then _ else _` >>
  `~guard` by (simp[Abbr `guard`] >> disj1_tac >>
    gvs[NULL_EQ] >> metis_tac[MEM]) >> simp[] >>
  qmatch_goalsub_abbrev_tac `if enabled then _ else _` >>
  qmatch_goalsub_abbrev_tac `popmany_plan cleanup ps` >>
  qmatch_goalsub_abbrev_tac `mark_dead_stack retained` >>
  qmatch_goalsub_abbrev_tac `popmany_plan (MAP Var dead_names) ps` >>
  `~MEM (Var x) retained /\ ~MEM (Var x) cleanup /\ ~MEM x dead_names` by
    (simp[Abbr `retained`, Abbr `cleanup`, Abbr `dead_names`,
          MEM_FILTER, MEM_MAP] >> metis_tac[]) >>
  simp[] >> Cases_on `enabled` >> simp[]
  >- (pairarg_tac >> simp[plan_holds_def, alias_mark_dead_stack_upper_support] >>
      drule popmany_plan_plan_holds >>
      disch_then (qspec_then `ps` mp_tac) >> gvs[plan_holds_def]) >>
  irule popmany_plan_plan_holds >> simp[MEM_MAP]
QED

Theorem alias_ready_nonjoin_no_phis:
  codegen_ready_fn fn /\ lookup_block lbl fn.fn_blocks = SOME bb /\
  LENGTH (cfg_preds_of (cfg_analyze fn) lbl) <= 1 ==>
  collect_phis bb.bb_instructions = []
Proof
  strip_tac >>
  `MEM bb fn.fn_blocks /\ bb.bb_label = lbl` by
    metis_tac[lookup_block_MEM, lookup_block_label] >>
  gvs[codegen_ready_fn_def, phis_at_joins_def, EVERY_MEM, NULL_EQ] >>
  metis_tac[]
QED

Theorem alias_ready_nonjoin_input_liveout:
  codegen_ready_fn fn /\ cfg_reachable_of (cfg_analyze fn) pred /\
  MEM lbl (cfg_succs_of (cfg_analyze fn) pred) /\
  lookup_block pred fn.fn_blocks = SOME pb /\
  lookup_block lbl fn.fn_blocks = SOME bb /\
  LENGTH (cfg_preds_of (cfg_analyze fn) lbl) <= 1 /\
  MEM x (live_vars_at (liveness_analyze fn) lbl 0) ==>
  MEM x (live_vars_at (liveness_analyze fn) pred (LENGTH pb.bb_instructions))
Proof
  strip_tac >>
  `collect_phis bb.bb_instructions = []` by
    metis_tac[alias_ready_nonjoin_no_phis] >>
  `MEM x (input_vars_from pred bb.bb_instructions
    (live_vars_at (liveness_analyze fn) lbl 0))` by
    simp[alias_input_vars_no_phis] >>
  `wf_function fn` by gvs[codegen_ready_fn_def] >>
  drule_all alias_selected_input_liveout >> simp[]
QED

Theorem alias_do_dup_cleanup_update:
  do_dup dist ps = (ops, qs) ==>
  do_dup dist (ps with <|ps_cleanup_height := h; ps_cleanup_promised := promised|>) =
    (ops, qs with <|ps_cleanup_height := h; ps_cleanup_promised := promised|>)
Proof
  simp[do_dup_def] >> IF_CASES_TAC >> simp[]
  >- simp[plan_state_component_equality] >>
  pairarg_tac >> simp[plan_state_component_equality]
QED

Theorem alias_do_swap_cleanup_update:
  do_swap dist ps = (ops, qs) ==>
  do_swap dist (ps with <|ps_cleanup_height := h; ps_cleanup_promised := promised|>) =
    (ops, qs with <|ps_cleanup_height := h; ps_cleanup_promised := promised|>)
Proof
  Cases_on `dist = 0` >- simp[do_swap_def] >>
  simp[do_swap_def] >> IF_CASES_TAC >> simp[]
  >- simp[plan_state_component_equality] >>
  pairarg_tac >> simp[plan_state_component_equality]
QED

Theorem alias_popmany_singleton_cleanup_update:
  popmany_plan [v] ps = (ops, qs) ==>
  popmany_plan [v] (ps with <|ps_cleanup_height := h; ps_cleanup_promised := promised|>) =
    (ops, qs with <|ps_cleanup_height := h; ps_cleanup_promised := promised|>)
Proof
  simp[popmany_plan_def, popmany_individual_def, QSORT_DEF, PARTITION_DEF, PART_DEF] >>
  Cases_on `stack_get_depth v ps.ps_stack` >>
  simp[is_contiguous_top_def, QSORT_DEF, PARTITION_DEF, PART_DEF] >>
  Cases_on `x = 1` >> gvs[]
  >- (Cases_on `do_swap 1 ps` >>
      drule alias_do_swap_cleanup_update >>
      disch_then (qspecl_then [`promised`, `h`] mp_tac) >>
      simp[] >> strip_tac >> simp[plan_state_component_equality]) >>
  Cases_on `x = 0` >> gvs[]
  >- simp[plan_state_component_equality] >>
  Cases_on `do_swap x ps` >>
  drule alias_do_swap_cleanup_update >>
  disch_then (qspecl_then [`promised`, `h`] mp_tac) >>
  simp[] >> strip_tac >> simp[plan_state_component_equality]
QED

Theorem alias_phi_cleanup_update:
  SND (generate_phi_plan inst live halting
    (ps with <|ps_cleanup_height := h; ps_cleanup_promised := promised|>)) =
  (SND (generate_phi_plan inst live halting ps)) with
    <|ps_cleanup_height := h; ps_cleanup_promised := promised|>
Proof
  simp[generate_phi_plan_def] >>
  Cases_on `stack_get_phi_depth (FILTER is_var_operand inst.inst_operands) ps.ps_stack` >> simp[] >>
  Cases_on `MEM (operand_to_string (stack_peek x ps.ps_stack)) live` >> simp[]
  >- (Cases_on `do_dup x ps` >>
      drule alias_do_dup_cleanup_update >>
      disch_then (qspecl_then [`promised`, `h`] mp_tac) >>
      simp[] >> strip_tac >>
      IF_CASES_TAC >> simp[] >>
      Cases_on `popmany_plan [Var (HD inst.inst_outputs)]
        (r with ps_stack := stack_poke 0 (Var (HD inst.inst_outputs)) r.ps_stack)` >>
      drule alias_popmany_singleton_cleanup_update >>
      disch_then (qspecl_then [`promised`, `h`] mp_tac) >> simp[]) >>
  IF_CASES_TAC >> simp[] >>
  Cases_on `popmany_plan [Var (HD inst.inst_outputs)]
    (ps with ps_stack := stack_poke x (Var (HD inst.inst_outputs)) ps.ps_stack)` >>
  drule alias_popmany_singleton_cleanup_update >>
  disch_then (qspecl_then [`promised`, `h`] mp_tac) >> simp[]
QED

Theorem alias_phi_fold_cleanup_update:
  !pairs ps.
  FOLDL (\s p. SND (generate_phi_plan (FST p) (SND p) halting s))
    (ps with <|ps_cleanup_height := h; ps_cleanup_promised := promised|>) pairs =
  (FOLDL (\s p. SND (generate_phi_plan (FST p) (SND p) halting s)) ps pairs) with
    <|ps_cleanup_height := h; ps_cleanup_promised := promised|>
Proof
  Induct >> simp[alias_phi_cleanup_update]
QED

Theorem alias_block_plan_conditional_liveout:
  liveness = liveness_analyze fn /\ dfg = dfg_build_function fn /\
  cfg = cfg_analyze fn /\ codegen_ready_fn fn /\
  lineage_state liveness dfg cfg fn
    (init_cleanup_plan_state ch growth spill_base lbl_ctr) lbl ps /\
  lookup_block lbl fn.fn_blocks = SOME bb /\
  (fn_entry_label fn <> SOME lbl /\ LENGTH (cfg_preds_of cfg lbl) <= 1 ==>
    !x. MEM x (live_vars_at liveness lbl 0) ==> plan_holds ps (Var x)) /\
  generate_block_plan liveness dfg cfg fn bb
    (ps with <| ps_cleanup_height := h; ps_cleanup_promised := promised |>) =
      SOME (ops, qs) ==>
  !x. MEM x (live_vars_at liveness lbl (LENGTH bb.bb_instructions)) ==>
    plan_holds qs (Var x)
Proof
  strip_tac >>
  `wf_function fn` by gvs[codegen_ready_fn_def] >>
  `bb.bb_label = lbl` by metis_tac[lookup_block_label] >>
  `MEM lbl (cfg_analyze fn).cfg_dfs_pre` by
    (`cfg_reachable_of (cfg_analyze fn) lbl` by
       metis_tac[alias_lineage_reachable] >>
     drule cfgAnalysisPropsTheory.cfg_analyze_reachable_sets >>
     simp[pred_setTheory.EXTENSION] >> metis_tac[]) >>
  Cases_on `bb = HD fn.fn_blocks`
  >- (gvs[] >>
      drule_at (Pat `generate_block_plan _ _ _ _ _ _ = _`) alias_entry_block_plan_cut >>
      simp[] >> disch_then drule >> strip_tac >>
      drule_all alias_ready_param_partition >> strip_tac >>
      drule alias_ready_entry_body >> simp[] >> disch_then drule >> strip_tac >>
      `!y. MEM y (live_vars_at (liveness_analyze fn) (HD fn.fn_blocks).bb_label
           (LENGTH (get_params (HD fn.fn_blocks).bb_instructions))) ==>
           plan_holds ps_param (Var y)` by
        (rpt strip_tac >> drule_all alias_prepare_params_entry_demand >>
         disch_then (qspec_then
           `ps with <|ps_cleanup_height := h; ps_cleanup_promised := promised|>` mp_tac) >>
         simp[]) >>
      drule_at (Pat `generate_block_insts_plan _ _ _ _ _ _ _ _ _ _ _ = _`)
        alias_body_plan_live_cut_coverage >>
      disch_then (qspec_then `get_params (HD fn.fn_blocks).bb_instructions` mp_tac) >>
      simp[]) >>
  suspend "nonentry"
QED

Resume alias_block_plan_conditional_liveout[nonentry]:
  gvs[] >> drule_all alias_nonentry_block_plan_cut >> strip_tac >>
  `EVERY (\inst. inst_wf inst /\ inst.inst_opcode <> PHI /\
           ~is_param_opcode inst.inst_opcode)
      (DROP (LENGTH (collect_phis bb.bb_instructions)) bb.bb_instructions)` by
    (drule_all alias_ready_phi_suffix >> strip_tac >>
     drule_all alias_ready_param_partition >> strip_tac >>
     gvs[EVERY_CONJ] >> metis_tac[EVERY_DROP]) >>
  `fn_entry_label fn <> SOME bb.bb_label` by
    (Cases_on `fn.fn_blocks` >>
     gvs[fn_entry_label_def, entry_block_def, lookup_block_def, FIND_thm] >>
     strip_tac >> gvs[]) >>
  Cases_on `1 < LENGTH (cfg_preds_of (cfg_analyze fn) bb.bb_label)`
  >- suspend "join" >>
  `LENGTH (cfg_preds_of (cfg_analyze fn) bb.bb_label) <= 1` by decide_tac >>
  `collect_phis bb.bb_instructions = []` by
    metis_tac[alias_ready_nonjoin_no_phis] >>
  `?pred. MEM bb.bb_label (cfg_succs_of (cfg_analyze fn) pred)` by
    (qpat_x_assum `lineage_state _ _ _ _ _ _ _` mp_tac >>
     simp[Once lineage_state_cases] >> metis_tac[]) >>
  `cfg_preds_of (cfg_analyze fn) bb.bb_label = [pred]` by
    metis_tac[alias_nonjoin_edge_preds] >>
  `!y. MEM y (live_vars_at (liveness_analyze fn) bb.bb_label 0) ==>
     plan_holds ps_clean (Var y)` by
    (rpt strip_tac >>
     `plan_holds (ps with <|ps_cleanup_height := h; ps_cleanup_promised := promised|>)
       (Var y)` by simp[] >>
     `MEM y (input_vars_from pred bb.bb_instructions
        (live_vars_at (liveness_analyze fn) bb.bb_label 0))` by
       simp[alias_input_vars_no_phis] >>
     drule_all alias_clean_stack_holds_input >>
     disch_then (qspec_then `fn` mp_tac) >> gvs[]) >>
  qpat_x_assum `bb.bb_instructions = non_param_insts bb` (assume_tac o SYM) >>
  gvs[COUNT_LIST_def] >>
  drule_at (Pat `generate_block_insts_plan _ _ _ _ _ _ _ _ _ _ _ = _`)
    alias_body_plan_live_cut_coverage >>
  disch_then (qspec_then `[]` mp_tac) >> simp[]
QED

Resume alias_block_plan_conditional_liveout[join]:
  qpat_x_assum `bb.bb_instructions = non_param_insts bb` (assume_tac o SYM) >>
  `LENGTH (cfg_preds_of (cfg_analyze fn) bb.bb_label) <> 1` by decide_tac >>
  `ps_clean = ps with <|ps_cleanup_height := h; ps_cleanup_promised := promised|>` by
    (qpat_x_assum `(if _ then _ else _) = _` mp_tac >> simp[]) >>
  `!y. MEM y (live_vars_at (liveness_analyze fn) bb.bb_label
      (LENGTH (collect_phis bb.bb_instructions))) ==> plan_holds ps_phi (Var y)` by
    (rpt strip_tac >>
     qpat_assum `ps_phi = _` (fn th => rewrite_tac[th]) >>
     simp[alias_phi_fold_cleanup_update] >>
     drule_at (Pat `lineage_state _ _ _ _ _ _ _`)
       alias_lineage_join_phi_cut_coverage >>
     simp[] >> disch_then drule >> simp[]) >>
  drule_at (Pat `generate_block_insts_plan _ _ _ _ _ _ _ _ _ _ _ = _`)
    alias_body_plan_live_cut_coverage >>
  disch_then (qspec_then `collect_phis bb.bb_instructions` mp_tac) >>
  `bb.bb_instructions = collect_phis bb.bb_instructions ++
      DROP (LENGTH (collect_phis bb.bb_instructions)) bb.bb_instructions` by
    (qspec_then `bb.bb_instructions` strip_assume_tac alias_collect_phis_prefix >>
     qpat_assum `bb.bb_instructions = _ ++ rest`
       (fn th => CONV_TAC (RAND_CONV (RAND_CONV (RAND_CONV (REWR_CONV th))))) >>
     simp[DROP_APPEND]) >>
  simp[]
QED

Finalise alias_block_plan_conditional_liveout

Theorem alias_lineage_block_liveout:
  !liveness dfg cfg fn ps0 lbl ps.
  lineage_state liveness dfg cfg fn ps0 lbl ps ==>
  !ch growth spill_base lbl_ctr bb h promised ops qs.
  ps0 = init_cleanup_plan_state ch growth spill_base lbl_ctr /\
  liveness = liveness_analyze fn /\ dfg = dfg_build_function fn /\
  cfg = cfg_analyze fn /\ codegen_ready_fn fn /\
  lookup_block lbl fn.fn_blocks = SOME bb /\
  generate_block_plan liveness dfg cfg fn bb
    (ps with <|ps_cleanup_height := h; ps_cleanup_promised := promised|>) =
      SOME (ops, qs) ==>
  !x. MEM x (live_vars_at liveness lbl (LENGTH bb.bb_instructions)) ==>
    plan_holds qs (Var x)
Proof
  rpt gen_tac >> qid_spec_tac `ps` >> qid_spec_tac `lbl` >>
  ho_match_mp_tac lineage_state_strongind >> rpt strip_tac
  >- (`lineage_state liveness dfg cfg fn ps0 lbl ps0` by
        metis_tac[lineage_state_entry] >>
      gvs[] >>
      drule_at (Pat `generate_block_plan _ _ _ _ _ _ = _`)
        alias_block_plan_conditional_liveout >>
      simp[] >> disch_then drule >> simp[]) >>
  `lineage_state liveness dfg cfg fn ps0 lbl'
    (ps_succ with <|ps_stack := ps_after.ps_stack; ps_spilled := ps_after.ps_spilled|>)` by
      (irule lineage_state_step >> goal_assum (drule_at Any) >> metis_tac[]) >>
  `!y. MEM y (live_vars_at liveness lbl (LENGTH bb.bb_instructions)) ==>
      plan_holds ps_after (Var y)` by
    (first_x_assum (drule_at (Pat `generate_block_plan _ _ _ _ _ _ = _`)) >>
     simp[] >> metis_tac[]) >>
  gvs[] >>
  `wf_function fn` by gvs[codegen_ready_fn_def] >>
  `cfg_reachable_of (cfg_analyze fn) lbl` by
    metis_tac[alias_lineage_reachable] >>
  `fn_entry_label fn <> SOME lbl' /\
     LENGTH (cfg_preds_of (cfg_analyze fn) lbl') <= 1 ==>
     !y. MEM y (live_vars_at (liveness_analyze fn) lbl' 0) ==>
       plan_holds (ps_succ with <|ps_stack := ps_after.ps_stack;
                                 ps_spilled := ps_after.ps_spilled|>) (Var y)` by
    (rpt strip_tac >>
     `MEM y (live_vars_at (liveness_analyze fn) lbl (LENGTH bb.bb_instructions))` by
       (irule alias_ready_nonjoin_input_liveout >>
        goal_assum (drule_at Any) >> simp[] >> metis_tac[]) >>
     simp[plan_holds_def] >> metis_tac[plan_holds_def]) >>
  qpat_assum `lineage_state _ _ _ _ _ lbl' _`
    (mp_then (Pat `lineage_state _ _ _ _ _ _ _`) mp_tac
      alias_block_plan_conditional_liveout) >>
  simp[] >> disch_then drule >> simp[]
QED

Theorem alias_lineage_nonjoin_livein:
  liveness = liveness_analyze fn /\ dfg = dfg_build_function fn /\
  cfg = cfg_analyze fn /\ codegen_ready_fn fn /\
  lineage_state liveness dfg cfg fn
    (init_cleanup_plan_state ch growth spill_base lbl_ctr) lbl ps /\
  lookup_block lbl fn.fn_blocks = SOME bb /\
  fn_entry_label fn <> SOME lbl /\ LENGTH (cfg_preds_of cfg lbl) <= 1 ==>
  !x. MEM x (live_vars_at liveness lbl 0) ==> plan_holds ps (Var x)
Proof
  strip_tac >> gvs[] >>
  qpat_x_assum `lineage_state _ _ _ _ _ _ _` mp_tac >>
  simp[Once lineage_state_cases] >> strip_tac >> gvs[] >>
  `wf_function fn` by gvs[codegen_ready_fn_def] >>
  `cfg_reachable_of (cfg_analyze fn) lbl'` by
    metis_tac[alias_lineage_reachable] >>
  `!y. MEM y (live_vars_at (liveness_analyze fn) lbl' (LENGTH bb'.bb_instructions)) ==>
      plan_holds ps_after (Var y)` by
    (drule alias_lineage_block_liveout >>
     disch_then (drule_at (Pat `generate_block_plan _ _ _ _ _ _ = _`)) >>
     simp[] >> metis_tac[]) >>
  rpt strip_tac >>
  `MEM x (live_vars_at (liveness_analyze fn) lbl' (LENGTH bb'.bb_instructions))` by
    (irule alias_ready_nonjoin_input_liveout >>
     goal_assum (drule_at Any) >> simp[] >> metis_tac[]) >>
  metis_tac[plan_holds_def]
QED

(* Universal block-end lower coverage is alias_lineage_block_liveout above;
   retain that general theorem rather than add an equivalent initialized copy. *)
Theorem alias_lineage_entry_input_coverage:
  liveness = liveness_analyze fn /\ dfg = dfg_build_function fn /\
  cfg = cfg_analyze fn /\ codegen_ready_fn fn /\
  lineage_entry liveness dfg cfg fn
    (init_cleanup_plan_state ch growth spill_base lbl_ctr) pred lbl ps /\
  lookup_block lbl fn.fn_blocks = SOME bb ==>
  !x. MEM x (input_vars_from pred bb.bb_instructions
    (live_vars_at liveness lbl 0)) ==> plan_holds ps (Var x)
Proof
  strip_tac >>
  gvs[lineage_entry_def] >>
  `wf_function fn` by gvs[codegen_ready_fn_def] >>
  `cfg_reachable_of (cfg_analyze fn) pred` by
    metis_tac[alias_lineage_reachable] >>
  `!y. MEM y (live_vars_at (liveness_analyze fn) pred
      (LENGTH bb'.bb_instructions)) ==> plan_holds ps_after (Var y)` by
    (drule alias_lineage_block_liveout >>
     disch_then (drule_at (Pat `generate_block_plan _ _ _ _ _ _ = _`)) >>
     simp[] >> metis_tac[]) >>
  rpt strip_tac >>
  `MEM x (live_vars_at (liveness_analyze fn) pred (LENGTH bb'.bb_instructions))` by
    (irule alias_selected_input_liveout >> goal_assum (drule_at Any) >>
     simp[] >> metis_tac[]) >>
  simp[plan_holds_def] >> metis_tac[plan_holds_def]
QED

Theorem alias_run_without_predecessor_no_phis:
  s.vs_prev_bb = NONE /\ run_block fuel ctx bb s = OK s' ==>
  collect_phis bb.bb_instructions = []
Proof
  Cases_on `bb.bb_instructions` >> simp[collect_phis_def] >>
  strip_tac >> Cases_on `h.inst_opcode = PHI` >>
  gvs[collect_phis_def, run_block_def, eval_phis_def,
      eval_one_phi_without_predecessor]
QED

Theorem alias_lineage_join_without_predecessor_coverage:
  liveness = liveness_analyze fn /\ dfg = dfg_build_function fn /\
  cfg = cfg_analyze fn /\ codegen_ready_fn fn /\
  lineage_state liveness dfg cfg fn
    (init_cleanup_plan_state ch growth spill_base lbl_ctr) lbl ps /\
  lookup_block lbl fn.fn_blocks = SOME bb /\
  1 < LENGTH (cfg_preds_of cfg lbl) /\
  s.vs_prev_bb = NONE /\ run_block fuel ctx bb s = OK s' /\
  MEM x (live_vars_at liveness lbl 0) ==>
  plan_holds ps (Var x)
Proof
  strip_tac >>
  `collect_phis bb.bb_instructions = []` by
    metis_tac[alias_run_without_predecessor_no_phis] >>
  `MEM x (live_vars_at liveness lbl (LENGTH (collect_phis bb.bb_instructions)))`
    by gvs[] >>
  drule_all alias_lineage_join_ordinary_coverage >> simp[plan_holds_def]
QED

Theorem alias_entry_ordinary_ownership:
  codegen_ready_fn fn /\ lookup_block lbl fn.fn_blocks = SOME bb /\
  s.vs_prev_bb = SOME pred /\
  (!p x. s.vs_prev_bb = SOME p /\
    MEM x (input_vars_from p bb.bb_instructions
      (live_vars_at (liveness_analyze fn) lbl 0)) ==> plan_holds ps (Var x)) /\
  MEM x (live_vars_at (liveness_analyze fn) lbl 0) /\
  MEM x (live_vars_at (liveness_analyze fn) lbl
    (LENGTH (collect_phis bb.bb_instructions))) ==>
  plan_holds ps (Var x)
Proof
  strip_tac >> first_x_assum irule >> qexists_tac `pred` >> simp[] >>
  Cases_on `NULL (collect_phis bb.bb_instructions)`
  >- gvs[NULL_EQ, alias_input_vars_no_phis] >>
  `MEM bb fn.fn_blocks /\ bb.bb_label = lbl` by
    metis_tac[lookup_block_MEM, lookup_block_label] >>
  `phi_block_ready (liveness_analyze fn) bb` by
    (gvs[codegen_ready_fn_def, phi_operands_ready_def, EVERY_MEM] >> metis_tac[]) >>
  qpat_x_assum `bb.bb_label = lbl` (SUBST_ALL_TAC o SYM) >>
  drule_all alias_phi_ready_ordinary_input >> simp[]
QED

Theorem alias_use_entry_or_earlier_definition:
  wf_function fn /\ MEM lbl (cfg_analyze fn).cfg_dfs_pre /\
  lookup_block lbl fn.fn_blocks = SOME bb /\
  i < LENGTH bb.bb_instructions /\
  MEM x (inst_uses (EL i bb.bb_instructions)) ==>
  MEM x (live_vars_at (liveness_analyze fn) lbl 0) \/
  ?k. k < i /\ MEM x (inst_defs (EL k bb.bb_instructions))
Proof
  strip_tac >>
  Cases_on `?k. k < i /\ MEM x (inst_defs (EL k bb.bb_instructions))`
  >- metis_tac[] >>
  disj1_tac >>
  `MEM x (live_vars_at (liveness_analyze fn) lbl i)` by
    (drule livenessAnalysisPropsTheory.live_vars_at_uses >> simp[] >>
     disch_then irule >> goal_assum (drule_at Any) >> simp[]) >>
  drule livenessAnalysisPropsTheory.live_vars_at_propagate_range >> simp[] >>
  disch_then irule >> goal_assum (drule_at Any) >>
  qexistsl_tac [`bb`, `i`] >> simp[] >> metis_tac[]
QED

Theorem alias_lineage_ordinary_entry_held:
  liveness = liveness_analyze fn /\ dfg = dfg_build_function fn /\
  cfg = cfg_analyze fn /\ codegen_ready_fn fn /\
  lineage_state liveness dfg cfg fn
    (init_cleanup_plan_state ch growth spill_base lbl_ctr) lbl ps /\
  lookup_block lbl fn.fn_blocks = SOME bb /\ fn_entry_label fn <> SOME lbl /\
  run_block fuel ctx bb s = OK s' /\
  (!pred y. s.vs_prev_bb = SOME pred /\
    MEM y (input_vars_from pred bb.bb_instructions (live_vars_at liveness lbl 0)) ==>
      plan_holds ps (Var y)) /\
  MEM x (live_vars_at liveness lbl 0) /\
  MEM x (live_vars_at liveness lbl (LENGTH (collect_phis bb.bb_instructions))) ==>
  plan_holds ps (Var x)
Proof
  strip_tac >> gvs[Excl "run_block_def"] >> Cases_on `s.vs_prev_bb`
  >- (Cases_on `LENGTH (cfg_preds_of (cfg_analyze fn) lbl) <= 1`
      >- (drule_at (Pat `lineage_state _ _ _ _ _ _ _`) alias_lineage_nonjoin_livein >>
          simp[] >> disch_then drule >> simp[]) >>
      `1 < LENGTH (cfg_preds_of (cfg_analyze fn) lbl)` by decide_tac >>
      drule_at (Pat `lineage_state _ _ _ _ _ _ _`) alias_lineage_join_without_predecessor_coverage >>
      simp[] >> disch_then drule >> simp[] >> metis_tac[]) >>
  drule_at (Pat `s.vs_prev_bb = SOME _`) alias_entry_ordinary_ownership >>
  simp[] >> disch_then drule >> simp[] >> metis_tac[]
QED

Theorem alias_lineage_nonentry_use_origin:
  liveness = liveness_analyze fn /\ dfg = dfg_build_function fn /\
  cfg = cfg_analyze fn /\ codegen_ready_fn fn /\
  lineage_state liveness dfg cfg fn
    (init_cleanup_plan_state ch growth spill_base lbl_ctr) lbl ps /\
  lookup_block lbl fn.fn_blocks = SOME bb /\ fn_entry_label fn <> SOME lbl /\
  run_block fuel ctx bb s = OK s' /\
  (!pred y. s.vs_prev_bb = SOME pred /\
    MEM y (input_vars_from pred bb.bb_instructions (live_vars_at liveness lbl 0)) ==>
      plan_holds ps (Var y)) /\
  LENGTH (collect_phis bb.bb_instructions) <= i /\ i < LENGTH bb.bb_instructions /\
  MEM x (inst_uses (EL i bb.bb_instructions)) ==>
  plan_holds ps (Var x) \/ ?k. k < i /\ MEM x (EL k bb.bb_instructions).inst_outputs
Proof
  strip_tac >>
  Cases_on `?k. k < i /\ MEM x (EL k bb.bb_instructions).inst_outputs`
  >- metis_tac[] >>
  disj1_tac >>
  `wf_function fn` by gvs[codegen_ready_fn_def] >>
  `MEM lbl (cfg_analyze fn).cfg_dfs_pre` by
    (`cfg_reachable_of (cfg_analyze fn) lbl` by
       metis_tac[alias_lineage_reachable] >>
     drule cfgAnalysisPropsTheory.cfg_analyze_reachable_sets >>
     simp[pred_setTheory.EXTENSION] >> metis_tac[]) >>
  `MEM x (live_vars_at (liveness_analyze fn) lbl 0)` by
    (drule_all alias_use_entry_or_earlier_definition >>
     simp[inst_defs_def] >> metis_tac[]) >>
  `MEM x (live_vars_at (liveness_analyze fn) lbl i)` by
    (drule livenessAnalysisPropsTheory.live_vars_at_uses >> simp[] >>
     disch_then irule >> goal_assum (drule_at Any) >> simp[]) >>
  `MEM x (live_vars_at (liveness_analyze fn) lbl
      (LENGTH (collect_phis bb.bb_instructions)))` by
    (drule livenessAnalysisPropsTheory.live_vars_at_propagate_range >> simp[] >>
     disch_then irule >> goal_assum (drule_at Any) >>
     qexistsl_tac [`bb`, `i`] >> simp[inst_defs_def] >> metis_tac[]) >>
  drule_at (Pat `lineage_state _ _ _ _ _ _ _`) alias_lineage_ordinary_entry_held >>
  simp[] >> disch_then drule >> simp[] >> metis_tac[]
QED

Theorem alias_entry_use_origin:
  wf_function fn /\ def_dominates_uses fn /\ fn_entry_label fn = SOME lbl /\
  lookup_block lbl fn.fn_blocks = SOME bb /\
  LENGTH (collect_phis bb.bb_instructions) <= i /\ i < LENGTH bb.bb_instructions /\
  MEM x (inst_uses (EL i bb.bb_instructions)) ==>
  ?k. k < i /\ MEM x (EL k bb.bb_instructions).inst_outputs
Proof
  strip_tac >>
  `~alias_pending_phi fn lbl i x` by
    metis_tac[alias_pending_phi_past_prefix] >>
  `alias_path_available fn lbl i x` by
    metis_tac[alias_use_available_or_pending] >>
  qpat_x_assum `alias_path_available _ _ _ _` mp_tac >>
  simp[alias_path_available_def] >>
  disch_then (qspec_then `[lbl]` mp_tac) >>
  `is_fn_path fn [lbl]` by
    (gvs[fn_entry_label_def, entry_block_def, AllCaseEqs()] >>
     simp[is_fn_path_def]) >>
  simp[] >> strip_tac >> gvs[inst_defs_def] >> metis_tac[]
QED

Theorem alias_lineage_use_origin:
  liveness = liveness_analyze fn /\ dfg = dfg_build_function fn /\
  cfg = cfg_analyze fn /\ codegen_ready_fn fn /\
  lineage_state liveness dfg cfg fn
    (init_cleanup_plan_state ch growth spill_base lbl_ctr) lbl ps /\
  lookup_block lbl fn.fn_blocks = SOME bb /\
  run_block fuel ctx bb s = OK s' /\
  (!pred y. s.vs_prev_bb = SOME pred /\
    MEM y (input_vars_from pred bb.bb_instructions (live_vars_at liveness lbl 0)) ==>
      plan_holds ps (Var y)) /\
  LENGTH (collect_phis bb.bb_instructions) <= i /\ i < LENGTH bb.bb_instructions /\
  MEM x (inst_uses (EL i bb.bb_instructions)) ==>
  plan_holds ps (Var x) \/ ?k. k < i /\ MEM x (EL k bb.bb_instructions).inst_outputs
Proof
  strip_tac >> Cases_on `fn_entry_label fn = SOME lbl`
  >- (disj2_tac >> irule alias_entry_use_origin >>
      goal_assum (drule_at Any) >> simp[] >>
      gvs[codegen_ready_fn_def] >> metis_tac[]) >>
  drule_at (Pat `lineage_state _ _ _ _ _ _ _`) alias_lineage_nonentry_use_origin >>
  simp[] >> disch_then drule >> simp[] >> metis_tac[]
QED

Theorem alias_available_promote_entry:
  lookup_block lbl fn.fn_blocks = SOME bb /\ alias_path_available fn lbl i x /\
  (!k. k < i /\ k < LENGTH bb.bb_instructions ==>
    ~MEM x (EL k bb.bb_instructions).inst_outputs) ==>
  alias_path_available fn lbl 0 x
Proof
  simp[alias_path_available_def] >> rpt strip_tac >>
  first_x_assum drule >> simp[] >> strip_tac
  >- metis_tac[] >>
  gvs[inst_defs_def] >> metis_tac[]
QED

Theorem alias_nonlocal_use_available_entry:
  wf_function fn /\ def_dominates_uses fn /\
  lookup_block lbl fn.fn_blocks = SOME bb /\
  LENGTH (collect_phis bb.bb_instructions) <= i /\ i < LENGTH bb.bb_instructions /\
  MEM x (inst_uses (EL i bb.bb_instructions)) /\
  (!k. k < i ==> ~MEM x (EL k bb.bb_instructions).inst_outputs) ==>
  alias_path_available fn lbl 0 x
Proof
  strip_tac >> irule alias_available_promote_entry >>
  goal_assum (drule_at Any) >> simp[] >>
  `~alias_pending_phi fn lbl i x` by metis_tac[alias_pending_phi_past_prefix] >>
  metis_tac[alias_use_available_or_pending]
QED

Theorem alias_nonlocal_use_not_output:
  wf_function fn /\ ssa_form fn /\ def_dominates_uses fn /\ fn_reachable fn lbl /\
  lookup_block lbl fn.fn_blocks = SOME bb /\
  LENGTH (collect_phis bb.bb_instructions) <= i /\ i < LENGTH bb.bb_instructions /\
  MEM x (inst_uses (EL i bb.bb_instructions)) /\
  (!k. k < i ==> ~MEM x (EL k bb.bb_instructions).inst_outputs) ==>
  !inst. MEM inst bb.bb_instructions ==> ~MEM x inst.inst_outputs
Proof
  strip_tac >>
  `alias_path_available fn lbl 0 x` by
    (irule alias_nonlocal_use_available_entry >> goal_assum (drule_at Any) >>
     simp[] >> qexists_tac `i` >> simp[]) >>
  metis_tac[alias_available_entry_not_output]
QED

Theorem alias_nonlocal_use_root_not_output:
  wf_function fn /\ ssa_form fn /\ def_dominates_uses fn /\ fn_reachable fn lbl /\
  lookup_block lbl fn.fn_blocks = SOME bb /\
  LENGTH (collect_phis bb.bb_instructions) <= i /\ i < LENGTH bb.bb_instructions /\
  MEM x (inst_uses (EL i bb.bb_instructions)) /\
  (!k. k < i ==> ~MEM x (EL k bb.bb_instructions).inst_outputs) /\
  normalize_operand (dfg_build_function fn) [] (Var x) = Var r ==>
  !inst. MEM inst bb.bb_instructions ==> ~MEM r inst.inst_outputs
Proof
  strip_tac >>
  `alias_path_available fn lbl 0 x` by
    (irule alias_nonlocal_use_available_entry >> goal_assum (drule_at Any) >>
     simp[] >> qexists_tac `i` >> simp[]) >>
  `alias_path_available fn lbl 0 r` by
    (irule alias_normalize_available >> simp[] >>
     qexistsl_tac [`Var x`, `[]`] >> simp[]) >>
  metis_tac[alias_available_entry_not_output]
QED

Theorem alias_run_block_non_output_lookup:
  run_block fuel ctx bb s = OK s' /\
  (!inst. MEM inst bb.bb_instructions ==> ~MEM x inst.inst_outputs) ==>
  lookup_var x s' = lookup_var x s
Proof
  strip_tac >>
  qspecl_then [`s`, `bb.bb_instructions`] strip_assume_tac
    eval_phis_ok_or_error_defs >>
  gvs[run_block_def] >>
  drule venomExecProofsTheory.exec_block_preserves_non_output_vars >>
  disch_then (qspec_then `x` mp_tac) >>
  simp[MEM_FLAT, MEM_MAP] >>
  impl_tac >- metis_tac[] >>
  strip_tac >>
  drule venomExecProofsTheory.eval_phis_flookup_not_phi_output >>
  disch_then (qspec_then `x` mp_tac) >>
  simp[lookup_var_def] >> metis_tac[]
QED

Theorem alias_nonlocal_use_run_equality:
  wf_function fn /\ ssa_form fn /\ def_dominates_uses fn /\ fn_reachable fn lbl /\
  lookup_block lbl fn.fn_blocks = SOME bb /\
  LENGTH (collect_phis bb.bb_instructions) <= i /\ i < LENGTH bb.bb_instructions /\
  MEM x (inst_uses (EL i bb.bb_instructions)) /\
  (!k. k < i ==> ~MEM x (EL k bb.bb_instructions).inst_outputs) /\
  run_block fuel ctx bb s = OK s' /\
  operand_val (frame_view fn ra s) lo (Var x) =
    operand_val (frame_view fn ra s) lo (normalize_operand (dfg_build_function fn) [] (Var x)) ==>
  operand_val (frame_view fn ra s') lo (Var x) =
    operand_val (frame_view fn ra s') lo (normalize_operand (dfg_build_function fn) [] (Var x))
Proof
  strip_tac >>
  `lookup_var x s' = lookup_var x s` by
    (irule alias_run_block_non_output_lookup >> goal_assum (drule_at Any) >>
     metis_tac[alias_nonlocal_use_not_output]) >>
  Cases_on `normalize_operand (dfg_build_function fn) [] (Var x)` >>
  gvs[operand_val_def, frame_view_vars_lookup, GSYM lookup_var_def] >>
  rename1 `normalize_operand _ _ _ = Var r` >>
  `lookup_var r s' = lookup_var r s` by
    (irule alias_run_block_non_output_lookup >> goal_assum (drule_at Any) >>
     metis_tac[alias_nonlocal_use_root_not_output]) >>
  gvs[]
QED

Theorem alias_lineage_nonlocal_use_equality:
  liveness = liveness_analyze fn /\ dfg = dfg_build_function fn /\
  cfg = cfg_analyze fn /\ codegen_ready_fn fn /\
  lineage_state liveness dfg cfg fn
    (init_cleanup_plan_state ch growth spill_base lbl_ctr) lbl ps /\
  lookup_block lbl fn.fn_blocks = SOME bb /\
  run_block fuel ctx bb s = OK s' /\
  (!pred y. s.vs_prev_bb = SOME pred /\
    MEM y (input_vars_from pred bb.bb_instructions (live_vars_at liveness lbl 0)) ==>
      plan_holds ps (Var y)) /\
  LENGTH (collect_phis bb.bb_instructions) <= i /\ i < LENGTH bb.bb_instructions /\
  MEM x (inst_uses (EL i bb.bb_instructions)) /\
  (!k. k < i ==> ~MEM x (EL k bb.bb_instructions).inst_outputs) /\
  (!at. plan_holds ps at ==>
    operand_val (frame_view fn ra s) lo at =
    operand_val (frame_view fn ra s) lo (normalize_operand dfg [] at)) ==>
  operand_val (frame_view fn ra s') lo (Var x) =
    operand_val (frame_view fn ra s') lo (normalize_operand dfg [] (Var x))
Proof
  strip_tac >>
  `plan_holds ps (Var x)` by
    (drule_at (Pat `lineage_state _ _ _ _ _ _ _`) alias_lineage_use_origin >>
     simp[] >> disch_then drule >> simp[] >> metis_tac[]) >>
  gvs[Excl "run_block_def"] >>
  `wf_function fn` by gvs[codegen_ready_fn_def] >>
  `fn_reachable fn lbl` by
    metis_tac[alias_lineage_reachable, fn_reachable_cfg_analyze] >>
  drule_at (Pat `run_block _ _ _ _ = _`) alias_nonlocal_use_run_equality >>
  simp[] >> disch_then irule >>
  gvs[codegen_ready_fn_def] >> conj_tac
  >- (qexists_tac `i` >> simp[]) >>
  qexists_tac `lbl` >> simp[]
QED

Definition alias_prefix_edge_def:
  alias_prefix_edge s t writes <=>
    (?fuel ctx inst. step_inst fuel ctx inst s = OK t /\
      writes = set inst.inst_outputs) \/
    (?instructions. eval_phis s instructions = OK t /\
      writes = {x | ?inst. MEM inst instructions /\ inst.inst_opcode = PHI /\
        MEM x inst.inst_outputs}) \/
    (?i. t = s with vs_inst_idx := i /\ writes = {})
End

Inductive alias_execution_prefix:
  (!s. alias_execution_prefix [s] {}) /\
  (!states writes t edge_writes.
    alias_execution_prefix states writes /\
    alias_prefix_edge (LAST states) t edge_writes ==>
    alias_execution_prefix (states ++ [t]) (writes UNION edge_writes))
End

Theorem alias_execution_prefix_nonempty:
  !states writes. alias_execution_prefix states writes ==> states <> []
Proof
  ho_match_mp_tac alias_execution_prefix_ind >> simp[]
QED

Theorem alias_prefix_snoc_cut:
  states <> [] ==>
  PRE (LENGTH (states ++ [t])) = LENGTH states /\
  EL (PRE (LENGTH states)) (states ++ [t]) = LAST states /\
  EL (LENGTH states) (states ++ [t]) = t
Proof
  simp[EL_APPEND, LAST_EL] >> rpt strip_tac >>
  `0 < LENGTH states` by (Cases_on `states` >> gvs[]) >> simp[]
QED

Theorem alias_certificate_prefix_extension:
  !fn dfg lo ps states n at.
  alias_certificate fn dfg lo ps states n at ==>
  !suffix. alias_certificate fn dfg lo ps (states ++ suffix) n at
Proof
  ho_match_mp_tac alias_certificate_ind >> rpt strip_tac
  >- (irule (cj 1 alias_certificate_rules) >> simp[])
  >- (irule (cj 2 alias_certificate_rules) >> simp[])
  >- (irule (cj 2 alias_certificate_rules) >> simp[])
  >- (irule (cj 3 alias_certificate_rules) >> simp[] >>
      goal_assum (drule_at Any) >> simp[EL_APPEND1] >> metis_tac[])
  >- (irule (cj 4 alias_certificate_rules) >> simp[] >>
      goal_assum (drule_at Any) >> simp[EL_APPEND1] >> metis_tac[])
  >- (irule (cj 5 alias_certificate_rules) >> simp[EL_APPEND1] >>
      `n < LENGTH states` by decide_tac >> simp[EL_APPEND1] >>
      qexistsl_tac [`ctx`, `fuel`, `inst`, `at`] >> simp[]) >>
  irule (cj 6 alias_certificate_rules) >> simp[] >>
  `n < LENGTH states` by decide_tac >> simp[EL_APPEND1] >> metis_tac[]
QED

Theorem alias_prefix_edge_certificate:
  alias_prefix_edge (EL n states) (EL (SUC n) states) writes /\
  alias_certificate fn dfg lo ps states n at /\ SUC n < LENGTH states /\
  (!x. at = Var x ==> x NOTIN writes) /\
  (!x. normalize_operand dfg [] at = Var x ==> x NOTIN writes) ==>
  alias_certificate fn dfg lo ps states (SUC n) at
Proof
  simp[alias_prefix_edge_def] >> strip_tac
  >- (irule (cj 3 alias_certificate_rules) >>
      goal_assum (drule_at Any) >> simp[] >> metis_tac[])
  >- (irule (cj 4 alias_certificate_rules) >>
      goal_assum (drule_at Any) >> simp[] >> qexists_tac `instructions` >>
      gvs[] >> metis_tac[]) >>
  irule (cj 6 alias_certificate_rules) >> simp[] >> metis_tac[]
QED

Theorem alias_execution_prefix_certificate:
  !states writes. alias_execution_prefix states writes ==>
  !fn dfg lo ps at. plan_holds ps at /\
    (!x. at = Var x ==> x NOTIN writes) /\
    (!x. normalize_operand dfg [] at = Var x ==> x NOTIN writes) ==>
    alias_certificate fn dfg lo ps states (PRE (LENGTH states)) at
Proof
  ho_match_mp_tac alias_execution_prefix_strongind >> conj_tac
  >- (rpt strip_tac >> simp[] >> irule (cj 2 alias_certificate_rules) >>
      gvs[plan_holds_def]) >>
  rpt strip_tac >>
  `states <> []` by metis_tac[alias_execution_prefix_nonempty] >>
  `alias_certificate fn dfg lo ps states (PRE (LENGTH states)) at` by
    (first_x_assum irule >> gvs[]) >>
  drule alias_certificate_prefix_extension >>
  disch_then (qspec_then `[t]` assume_tac) >>
  `SUC (PRE (LENGTH states)) = LENGTH states` by
    (Cases_on `states` >> gvs[]) >>
  drule alias_prefix_snoc_cut >> strip_tac >>
  `alias_certificate fn dfg lo ps (states ++ [t])
      (SUC (PRE (LENGTH states))) at` by
    (irule alias_prefix_edge_certificate >>
     simp[] >> qexists_tac `edge_writes` >> gvs[]) >>
  gvs[GSYM arithmeticTheory.ADD1]
QED

Theorem alias_execution_prefix_value:
  alias_execution_prefix states writes /\ plan_holds ps at /\
  (!x. at = Var x ==> x NOTIN writes) /\
  (!x. normalize_operand dfg [] at = Var x ==> x NOTIN writes) /\
  (!op. plan_holds ps op ==>
    operand_val (frame_view fn ra (HD states)) lo op =
    operand_val (frame_view fn ra (HD states)) lo (normalize_operand dfg [] op)) ==>
  operand_val (frame_view fn ra (LAST states)) lo at =
  operand_val (frame_view fn ra (LAST states)) lo (normalize_operand dfg [] at)
Proof
  strip_tac >>
  `states <> []` by metis_tac[alias_execution_prefix_nonempty] >>
  `alias_certificate fn dfg lo ps states (PRE (LENGTH states)) at` by
    metis_tac[alias_execution_prefix_certificate] >>
  drule alias_certificate_sound >> disch_then (qspec_then `ra` mp_tac) >>
  simp[GSYM LAST_EL, EL, plan_holds_def] >> metis_tac[plan_holds_def]
QED

Theorem alias_execution_prefix_extend_edge:
  alias_execution_prefix states writes /\ LAST states = s /\
  alias_prefix_edge s t edge_writes ==>
  alias_execution_prefix (states ++ [t]) (writes UNION edge_writes) /\
  LAST (states ++ [t]) = t
Proof
  strip_tac >> simp[] >> metis_tac[alias_execution_prefix_rules]
QED

Theorem alias_exec_block_indexed_cut:
  alias_execution_prefix states writes /\ LAST states = s /\
  exec_block fuel ctx bb s = OK t /\
  s.vs_inst_idx <= i /\ i < LENGTH bb.bb_instructions /\
  (!j. s.vs_inst_idx <= j /\ j < i ==>
    ~is_terminator (EL j bb.bb_instructions).inst_opcode) ==>
  ?suffix u writes'.
    alias_execution_prefix (states ++ suffix) writes' /\
    LAST (states ++ suffix) = u /\ u.vs_inst_idx = i /\
    exec_block fuel ctx bb u = OK t /\
    writes' SUBSET (writes UNION
      {x | ?j. s.vs_inst_idx <= j /\ j < i /\
        MEM x (EL j bb.bb_instructions).inst_outputs})
Proof
  qid_spec_tac `writes` >> qid_spec_tac `states` >> qid_spec_tac `s` >>
  measureInduct_on `i - s.vs_inst_idx` >> rpt strip_tac >>
  Cases_on `s.vs_inst_idx = i`
  >- (qexistsl_tac [`[]`, `s`, `writes`] >> simp[]) >>
  `s.vs_inst_idx < i` by decide_tac >>
  `~is_terminator (EL s.vs_inst_idx bb.bb_instructions).inst_opcode` by simp[] >>
  qpat_x_assum `exec_block _ _ _ _ = _` mp_tac >>
  CONV_TAC (LAND_CONV (ONCE_REWRITE_CONV [exec_block_def])) >>
  simp[get_instruction_def, Excl "exec_block_def"] >>
  Cases_on `step_inst fuel ctx (EL s.vs_inst_idx bb.bb_instructions) s` >> simp[] >>
  rename1 `step_inst _ _ _ _ = OK u` >> strip_tac >>
  qabbrev_tac `ew = set (EL s.vs_inst_idx bb.bb_instructions).inst_outputs` >>
  qabbrev_tac `r = u with vs_inst_idx := SUC s.vs_inst_idx` >>
  `alias_prefix_edge s u ew` by
    (simp[alias_prefix_edge_def, Abbr `ew`] >> metis_tac[]) >>
  `alias_execution_prefix (states ++ [u]) (writes UNION ew)` by
    metis_tac[alias_execution_prefix_extend_edge] >>
  `alias_prefix_edge u r {}` by
    (simp[alias_prefix_edge_def, Abbr `r`] >> disj2_tac >> disj2_tac >>
     qexists_tac `SUC s.vs_inst_idx` >> simp[]) >>
  `alias_execution_prefix ((states ++ [u]) ++ [r]) (writes UNION ew)` by
    (drule alias_execution_prefix_extend_edge >> simp[] >>
     disch_then drule >> simp[]) >>
  qpat_x_assum `!y. i - y < _ ==> _` (qspec_then `SUC s.vs_inst_idx` mp_tac) >> simp[] >>
  disch_then (qspec_then `r` mp_tac) >> simp[Abbr `r`] >>
  disch_then (qspecl_then [`states ++ [u] ++ [u with vs_inst_idx := SUC s.vs_inst_idx]`,
    `writes UNION ew`] mp_tac) >>
  impl_tac >- (simp[] >> rpt strip_tac >> first_x_assum irule >> decide_tac) >>
  strip_tac >> rename1 `result_writes SUBSET _` >>
  qexistsl_tac [`[u; u with vs_inst_idx := SUC s.vs_inst_idx] ++ suffix`, `result_writes`] >>
  conj_tac >- (qpat_x_assum `alias_execution_prefix (_ ++ _ ++ _ ++ _) _` mp_tac >>
    pure_rewrite_tac[GSYM APPEND_ASSOC, APPEND] >> simp[]) >>
  conj_tac >- (qpat_x_assum `(LAST _).vs_inst_idx = i` mp_tac >>
    pure_rewrite_tac[GSYM APPEND_ASSOC, APPEND] >> simp[]) >>
  conj_tac >- (qpat_x_assum `exec_block _ _ _ _ = OK t` mp_tac >>
    pure_rewrite_tac[GSYM APPEND_ASSOC, APPEND] >> simp[]) >>
  qpat_x_assum `result_writes SUBSET _` mp_tac >>
  simp[pred_setTheory.SUBSET_DEF, Abbr `ew`] >>
  rpt strip_tac >> first_x_assum drule >> strip_tac >- simp[]
  >- (disj2_tac >> qexists_tac `s.vs_inst_idx` >> simp[]) >>
  disj2_tac >> goal_assum (drule_at Any) >> decide_tac
QED

Theorem alias_exec_local_base_source_certificate:
  alias_execution_prefix states writes /\ LAST states = s /\
  exec_block fuel ctx bb s = OK t /\
  s.vs_inst_idx <= i /\ i < LENGTH bb.bb_instructions /\
  (!j. s.vs_inst_idx <= j /\ j < i ==>
    ~is_terminator (EL j bb.bb_instructions).inst_opcode) /\
  ssa_form fn /\ MEM bb fn.fn_blocks /\ k < i /\
  MEM x (EL k bb.bb_instructions).inst_outputs /\
  (EL k bb.bb_instructions).inst_opcode <> ASSIGN /\
  MEM x (inst_uses (EL i bb.bb_instructions)) /\
  (EL i bb.bb_instructions).inst_opcode <> PHI ==>
  ?suffix u writes'.
    alias_execution_prefix (states ++ suffix) writes' /\
    LAST (states ++ suffix) = u /\ u.vs_inst_idx = i /\
    exec_block fuel ctx bb u = OK t /\
    writes' SUBSET (writes UNION
      {x | ?j. s.vs_inst_idx <= j /\ j < i /\
        MEM x (EL j bb.bb_instructions).inst_outputs}) /\
    alias_certificate fn (dfg_build_function fn) lo ps (states ++ suffix)
      (PRE (LENGTH (states ++ suffix))) (Var x)
Proof
  rpt strip_tac >>
  `k < LENGTH bb.bb_instructions` by decide_tac >>
  `MEM (EL k bb.bb_instructions) (fn_insts fn)` by
    (simp[fn_insts_def, MEM_fn_insts_blocks_iff] >>
     qexists_tac `bb` >> simp[] >> irule EL_MEM >> decide_tac) >>
  `normalize_operand (dfg_build_function fn) [] (Var x) = Var x` by
    (irule normalize_operand_non_assign_output >> simp[] >>
     qexists_tac `EL k bb.bb_instructions` >> simp[]) >>
  drule_all alias_exec_block_indexed_cut >> strip_tac >>
  qexistsl_tac [`suffix`, `u`, `writes'`] >> simp[] >>
  irule (cj 1 alias_certificate_rules) >> simp[] >>
  `states <> []` by metis_tac[alias_execution_prefix_nonempty] >>
  Cases_on `states` >> gvs[]
QED

Theorem alias_exec_assign_cut_certificate:
  alias_execution_prefix states writes /\ LAST states = s /\
  exec_block fuel ctx bb s = OK t /\ s.vs_inst_idx = i /\
  wf_function fn /\ ssa_form fn /\ def_dominates_uses fn /\
  fn_reachable fn lbl /\ lookup_block lbl fn.fn_blocks = SOME bb /\
  i < LENGTH bb.bb_instructions /\
  (EL i bb.bb_instructions).inst_opcode = ASSIGN /\
  (EL i bb.bb_instructions).inst_outputs = [x] /\
  (EL i bb.bb_instructions).inst_operands = [src] /\
  (!l. FLOOKUP s.vs_labels l = OPTION_MAP n2w (FLOOKUP lo l)) /\
  alias_certificate fn (dfg_build_function fn) lo ps states
    (PRE (LENGTH states)) src ==>
  ?u. step_inst fuel ctx (EL i bb.bb_instructions) s = OK u /\
    alias_execution_prefix (states ++ [u; u with vs_inst_idx := SUC i])
      (writes UNION {x}) /\
    exec_block fuel ctx bb (u with vs_inst_idx := SUC i) = OK t /\
    alias_certificate fn (dfg_build_function fn) lo ps
      (states ++ [u; u with vs_inst_idx := SUC i])
      (PRE (LENGTH (states ++ [u; u with vs_inst_idx := SUC i]))) (Var x)
Proof
  strip_tac >>
  `states <> []` by metis_tac[alias_execution_prefix_nonempty] >>
  `normalize_operand (dfg_build_function fn) [] (Var x) =
   normalize_operand (dfg_build_function fn) [] src` by
    (irule alias_local_assign_normalize >> metis_tac[]) >>
  `!y. normalize_operand (dfg_build_function fn) [] src = Var y ==>
     ~MEM y (EL i bb.bb_instructions).inst_outputs` by
    (gen_tac >> disch_tac >>
     irule alias_assign_source_root_suffix_not_output >>
     simp[] >> qexistsl_tac [`src`, `fn`, `i`, `lbl`] >> simp[]) >>
  qpat_x_assum `exec_block _ _ _ _ = _` mp_tac >>
  CONV_TAC (LAND_CONV (ONCE_REWRITE_CONV [exec_block_def])) >>
  simp[get_instruction_def, is_terminator_def] >>
  Cases_on `step_inst fuel ctx (EL i bb.bb_instructions) s` >> simp[] >>
  rename1 `step_inst _ _ _ _ = OK u` >> strip_tac >>
  `alias_prefix_edge s u {x}` by
    (simp[alias_prefix_edge_def] >> disj1_tac >>
     qexistsl_tac [`fuel`, `ctx`, `EL i bb.bb_instructions`] >> simp[]) >>
  `alias_prefix_edge u (u with vs_inst_idx := SUC i) {}` by
    (simp[alias_prefix_edge_def] >> disj2_tac >> disj2_tac >>
     qexists_tac `SUC i` >> simp[]) >>
  conj_tac
  >- (`alias_execution_prefix (states ++ [u]) (writes UNION {x})` by
        metis_tac[alias_execution_prefix_extend_edge] >>
      `alias_execution_prefix ((states ++ [u]) ++ [u with vs_inst_idx := SUC i])
         (writes UNION {x})` by
        (drule alias_execution_prefix_extend_edge >> simp[] >>
         disch_then drule >> simp[]) >>
      qpat_x_assum `alias_execution_prefix (_ ++ _ ++ _) _` mp_tac >>
      pure_rewrite_tac[GSYM APPEND_ASSOC, APPEND] >> simp[]) >>
  `0 < LENGTH states` by (Cases_on `states` >> gvs[]) >>
  `SUC (PRE (LENGTH states)) = LENGTH states` by decide_tac >>
  `EL (PRE (LENGTH states)) (states ++ [u; u with vs_inst_idx := SUC i]) = s` by
    (simp[EL_APPEND1] >> metis_tac[LAST_EL]) >>
  `alias_certificate fn (dfg_build_function fn) lo ps
     (states ++ [u; u with vs_inst_idx := SUC i])
     (SUC (PRE (LENGTH states))) (Var x)` by
    (irule (cj 5 alias_certificate_rules) >> simp[] >>
     qexistsl_tac [`ctx`, `fuel`, `EL i bb.bb_instructions`, `src`] >>
     simp[EL_APPEND2] >>
     metis_tac[alias_certificate_prefix_extension, lookup_block_MEM,
       MEM_fn_insts_blocks_iff, fn_insts_def, EL_MEM]) >>
  `PRE (LENGTH states + 2) = SUC (LENGTH states)` by decide_tac >>
  simp[] >> irule alias_certificate_admin_transport >>
  simp[EL_APPEND2] >> conj_tac
  >- (qexists_tac `SUC i` >> simp[]) >>
  metis_tac[]
QED

Theorem alias_exec_block_suffix_prefix:
  alias_execution_prefix states writes /\ LAST states = s /\
  exec_block fuel ctx bb s = OK t ==>
  ?suffix writes'. alias_execution_prefix (states ++ suffix) writes' /\
    LAST (states ++ suffix) = t /\
    writes' SUBSET (writes UNION
      {x | ?j. s.vs_inst_idx <= j /\ j < LENGTH bb.bb_instructions /\
        MEM x (EL j bb.bb_instructions).inst_outputs})
Proof
  qid_spec_tac `writes` >> qid_spec_tac `states` >> qid_spec_tac `s` >>
  measureInduct_on `LENGTH bb.bb_instructions - s.vs_inst_idx` >>
  rpt strip_tac >>
  qpat_x_assum `exec_block _ _ _ _ = _` mp_tac >>
  once_rewrite_tac[exec_block_def] >>
  Cases_on `get_instruction bb s.vs_inst_idx` >> simp[] >>
  rename1 `get_instruction bb s.vs_inst_idx = SOME inst` >>
  Cases_on `step_inst fuel ctx inst s` >> simp[] >>
  rename1 `step_inst fuel ctx inst s = OK u` >>
  `s.vs_inst_idx < LENGTH bb.bb_instructions /\ MEM inst bb.bb_instructions` by
    (gvs[get_instruction_def] >> metis_tac[MEM_EL]) >>
  `inst = EL s.vs_inst_idx bb.bb_instructions` by
    gvs[get_instruction_def] >>
  `alias_prefix_edge s u (set inst.inst_outputs)` by
    (simp[alias_prefix_edge_def] >> metis_tac[]) >>
  `alias_execution_prefix (states ++ [u]) (writes UNION set inst.inst_outputs)` by
    metis_tac[alias_execution_prefix_extend_edge] >>
  Cases_on `is_terminator inst.inst_opcode`
  >- (Cases_on `u.vs_halted` >> simp[] >> strip_tac >>
      qexistsl_tac [`[t]`, `writes UNION set inst.inst_outputs`] >> simp[] >>
      conj_tac >- gvs[] >>
      simp[pred_setTheory.SUBSET_DEF] >> rpt strip_tac >>
      disj2_tac >> qexists_tac `s.vs_inst_idx` >> simp[]) >>
  simp[] >> strip_tac >>
  qabbrev_tac `r = u with vs_inst_idx := SUC s.vs_inst_idx` >>
  `alias_prefix_edge u r {}` by
    (simp[alias_prefix_edge_def, Abbr `r`] >> disj2_tac >> disj2_tac >>
     qexists_tac `SUC s.vs_inst_idx` >> simp[]) >>
  `alias_execution_prefix ((states ++ [u]) ++ [r])
      (writes UNION set inst.inst_outputs)` by
    (drule alias_execution_prefix_extend_edge >> simp[] >>
     disch_then drule >> simp[]) >>
  first_x_assum (qspec_then `SUC s.vs_inst_idx` mp_tac) >>
  simp[] >>
  disch_then (qspec_then `r` mp_tac) >>
  simp[Abbr `r`] >>
  disch_then (qspecl_then [`states ++ [u] ++ [u with vs_inst_idx := SUC s.vs_inst_idx]`,
    `writes UNION set inst.inst_outputs`] mp_tac) >>
  simp[] >> strip_tac >>
  rename1 `result_writes SUBSET _` >>
  qexistsl_tac [`[u; u with vs_inst_idx := SUC s.vs_inst_idx] ++ suffix`, `result_writes`] >>
  conj_tac >- (qpat_x_assum `alias_execution_prefix (_ ++ _ ++ _ ++ _) _` mp_tac >>
    pure_rewrite_tac[GSYM APPEND_ASSOC, APPEND] >> simp[]) >>
  conj_tac >- (qpat_x_assum `LAST _ = t` mp_tac >>
    pure_rewrite_tac[GSYM APPEND_ASSOC, APPEND] >> simp[]) >>
  qpat_x_assum `result_writes SUBSET _` mp_tac >>
  simp[pred_setTheory.SUBSET_DEF] >>
  rpt strip_tac >> first_x_assum drule >> strip_tac >- simp[]
  >- (disj2_tac >> qexists_tac `s.vs_inst_idx` >> simp[]) >>
  disj2_tac >> goal_assum (drule_at Any) >> decide_tac
QED

Theorem alias_exec_block_prefix:
  alias_execution_prefix states writes /\ LAST states = s /\
  exec_block fuel ctx bb s = OK t ==>
  ?suffix writes'. alias_execution_prefix (states ++ suffix) writes' /\
    LAST (states ++ suffix) = t /\
    writes' SUBSET (writes UNION
      {x | ?inst. MEM inst bb.bb_instructions /\ MEM x inst.inst_outputs})
Proof
  strip_tac >> drule_all alias_exec_block_suffix_prefix >> strip_tac >>
  qexistsl_tac [`suffix`, `writes'`] >> simp[] >>
  qpat_x_assum `writes' SUBSET _` mp_tac >>
  simp[pred_setTheory.SUBSET_DEF] >> metis_tac[MEM_EL]
QED

Theorem alias_run_block_prefix:
  run_block fuel ctx bb s = OK t ==>
  ?states writes. alias_execution_prefix states writes /\
    HD states = s /\ LAST states = t /\
    writes SUBSET {x | ?inst. MEM inst bb.bb_instructions /\ MEM x inst.inst_outputs}
Proof
  strip_tac >>
  qspecl_then [`s`, `bb.bb_instructions`] strip_assume_tac
    eval_phis_ok_or_error_defs >>
  gvs[run_block_def] >>
  qabbrev_tac `pw = {x | ?inst. MEM inst bb.bb_instructions /\
    inst.inst_opcode = PHI /\ MEM x inst.inst_outputs}` >>
  qabbrev_tac `r = s' with vs_inst_idx := phi_prefix_length bb.bb_instructions` >>
  `alias_prefix_edge s s' pw` by
    (simp[alias_prefix_edge_def] >> disj2_tac >> disj1_tac >>
     qexists_tac `bb.bb_instructions` >> simp[Abbr `pw`]) >>
  `alias_execution_prefix [s; s'] pw` by
    (mp_tac (Q.SPEC `s` (cj 1 alias_execution_prefix_rules)) >>
     strip_tac >> drule alias_execution_prefix_extend_edge >> simp[] >>
     disch_then drule >> simp[]) >>
  `alias_prefix_edge s' r {}` by
    (simp[alias_prefix_edge_def, Abbr `r`] >> disj2_tac >> disj2_tac >>
     qexists_tac `phi_prefix_length bb.bb_instructions` >> simp[]) >>
  `alias_execution_prefix ([s; s'] ++ [r]) pw` by
    (drule alias_execution_prefix_extend_edge >> simp[] >>
     disch_then drule >> simp[]) >>
  drule alias_exec_block_prefix >>
  disch_then (qspecl_then [`t`, `r`, `fuel`, `ctx`, `bb`] mp_tac) >>
  simp[] >> strip_tac >>
  qexistsl_tac [`([s; s'] ++ [r]) ++ suffix`, `writes'`] >>
  simp[] >> qpat_x_assum `writes' SUBSET _` mp_tac >>
  simp[pred_setTheory.SUBSET_DEF, Abbr `pw`] >> metis_tac[]
QED

(* Used at each jump of the block induction, for the successor's alias
   premise.  The invariant reads only ps_stack and ps_spilled, so the
   lineage entry state of the successor (its DFS state with ps_after's
   stack and spill map, lineage_entry) inherits it from ps_after.  The
   block's code is the one lineage_state_block_plan regenerates from the
   lineage state ps, with the cleanup fields it chooses.

   The ownership premise is the planner's static entry invariant: every
   variable live into the block along the edge taken is on the stack or
   spilled.  Without it a block could copy (ASSIGN) a variable the planner
   doesn't hold, whose value need not be its root's after a loop
   iteration, and push the copy.

   Why it should hold: a variable defined in the block by ASSIGN of an
   owned operand takes that operand's value, which is its root's; any
   other definition is its own root.  A root's value only changes when
   its definition runs again, and by SSA and def_dominates_uses a
   variable derived from it is then no longer live, so the planner has
   dropped it: popped, overwritten by a PHI poke, or left behind at the
   join reorder of a JMP (every loop header is a join).  An INVOKE
   changes only its own outputs among the caller's variables.  Return-PC
   variables all read ra in the frame view, and so do their roots. *)

(* Notes from a statement check (intuition, not a prescribed proof):
   - Where the planner drops names (stackPlanGen): an operand dead after
     its instruction is consumed rather than duplicated; dead outputs are
     popped at the end of generate_regular_inst_plan when the block does
     not halt (PHI outputs likewise); after a JNZ clean_stack_plan pops
     dead names or marks them dead_stack_marker; release_dead_spills
     drops dead spills after each regular instruction.  reorder_one's
     alias step only swaps the names of two slots.  So a name in ps_after
     is a name of ps (stack or spill map) or an output of bb.
   - A name z live out of bb, not defined in bb, whose root is defined in
     bb, is impossible: bb dominates z's definition (def_dominates_uses,
     transitively along the ASSIGN chain), and an entry path that meets
     bb only at its end, followed by liveness_sound's witness path, misses
     z's definition.  A bb entered around a loop is a join (entry block
     has no predecessors), entered only by JMP (block_entries_ready),
     whose reorder leaves only names live into it.
   - The ps premises tie ps to vs only through ownership and the alias
     premise; ps's names beyond those are bounded by a static invariant
     of lineage states (their names are live out of the lineage
     predecessor, and the vars live along that edge are all held), which
     also covers a run with vs_prev_bb = NONE at a non-entry block.  The
     entry block has no live-in variables.
   - dead_stack_marker is Label "", and Lit/Label operands are fixed by
     normalize_operand, so only Var operands matter.  PHI and INVOKE
     outputs are their own roots.  For return-PC variables, copy_phi_var
     and retpc_shape_ok keep every link of the chain a return-PC
     variable, so both sides read ra. *)
(* The old all-name support obstructions do not themselves obstruct the
   alias-only availability candidate: each distinguished name is its root. *)
Theorem alias_diamond_edge_alias_premises:
  codegen_ready_fn alias_diamond_fn /\
  lookup_block "right" alias_diamond_fn.fn_blocks =
    SOME (EL 3 alias_diamond_fn.fn_blocks) /\
  generate_block_plan (liveness_analyze alias_diamond_fn)
    (dfg_build_function alias_diamond_fn) (cfg_analyze alias_diamond_fn)
    alias_diamond_fn (EL 3 alias_diamond_fn.fn_blocks) (SND alias_diamond_h) =
    SOME alias_diamond_r /\
  MEM "join" (cfg_succs_of (cfg_analyze alias_diamond_fn) "right") /\
  plan_holds (SND alias_diamond_r) (Var "v") /\
  normalize_operand (dfg_build_function alias_diamond_fn) [] (Var "v") <> Var "v"
Proof
  simp[alias_diamond_ready, GSYM alias_diamond_plan_def,
       alias_diamond_plans, alias_diamond_branch_states, plan_holds_def] >>
  EVAL_TAC
QED

Theorem alias_diamond_right_alias_available:
  alias_path_available alias_diamond_fn "right"
    (LENGTH (EL 3 alias_diamond_fn.fn_blocks).bb_instructions) "v"
Proof
  rewrite_tac[alias_path_available_def] >> rpt strip_tac >>
  disj2_tac >> qexistsl_tac [`EL 3 alias_diamond_fn.fn_blocks`, `0`] >>
  EVAL_TAC
QED

Theorem alias_diamond_join_alias_unavailable:
  ~alias_path_available alias_diamond_fn "join" 0 "v"
Proof
  simp[alias_path_available_def] >>
  qexists_tac `["entry"; "header"; "left"; "join"]` >>
  conj_tac
  >- (simp[is_fn_path_def, fn_cfg_edge_def] >> rpt conj_tac
      >- (qexists_tac `EL 0 alias_diamond_fn.fn_blocks` >> EVAL_TAC)
      >- (qexists_tac `EL 1 alias_diamond_fn.fn_blocks` >> EVAL_TAC)
      >- (qexists_tac `EL 2 alias_diamond_fn.fn_blocks` >> EVAL_TAC) >>
      EVAL_TAC) >>
  rpt gen_tac >> disch_tac >>
  Cases_on `k < 3` >- (
    `k = 0 \/ k = 1 \/ k = 2` by decide_tac >>
    gvs[] >> pop_assum mp_tac >> EVAL_TAC >> rpt strip_tac >> gvs[] >>
    EVAL_TAC >> CCONTR_TAC >> gvs[] >> EVAL_TAC) >>
  simp[]
QED

(* A state-independent cut interface.  No planner coverage is assumed here. *)
Definition alias_cut_closure_def:
  alias_cut_closure Z S R H =
    Z UNION {a | a IN H /\ S a} UNION {d | ?s. s IN H /\ R d s}
End

Theorem alias_cut_closure_backward:
  !Z H D safe repair.
  D SUBSET alias_cut_closure Z safe repair H <=>
  ?Ds P. Ds SUBSET H /\ (!a. a IN Ds ==> safe a) /\
    (!d s. P d s ==> repair d s /\ s IN H) /\
    D SUBSET (Z UNION Ds UNION {d | ?s. P d s})
Proof
  rpt gen_tac >> eq_tac
  >- (strip_tac >>
      qexistsl_tac [`{a | a IN H /\ safe a}`, `\d s. s IN H /\ repair d s`] >>
      gvs[alias_cut_closure_def, pred_setTheory.SUBSET_DEF]) >>
  rw[alias_cut_closure_def, pred_setTheory.SUBSET_DEF] >> metis_tac[]
QED

Theorem alias_cut_zero_coverage:
  D SUBSET ({a | normalize_operand dfg [] a = a} UNION {a | plan_holds ps a}) <=>
  (!a. a IN D ==> normalize_operand dfg [] a = a \/ plan_holds ps a)
Proof
  simp[pred_setTheory.SUBSET_DEF]
QED

Theorem alias_cut_entry_input_coverage:
  D DIFF {a | normalize_operand dfg [] a = a} SUBSET {Var x | MEM x inputs} /\
  (!x. MEM x inputs ==> plan_holds ps (Var x)) ==>
  D SUBSET ({a | normalize_operand dfg [] a = a} UNION {a | plan_holds ps a})
Proof
  rw[pred_setTheory.SUBSET_DEF] >> metis_tac[]
QED

Theorem alias_cut_zero_certificates:
  0 < LENGTH states /\
  D SUBSET ({a | normalize_operand dfg [] a = a} UNION {a | plan_holds ps a}) ==>
  !a. a IN D ==> alias_certificate fn dfg lo ps states 0 a
Proof
  rw[pred_setTheory.SUBSET_DEF, plan_holds_def] >> metis_tac[alias_certificate_rules]
QED

Theorem alias_cut_step_certificates:
  SUC n < LENGTH states /\ ssa_form fn /\ MEM inst (fn_insts fn) /\
  step_inst fuel ctx inst (EL n states) = OK (EL (SUC n) states) /\
  (!l. FLOOKUP (EL n states).vs_labels l = OPTION_MAP n2w (FLOOKUP lo l)) /\
  (!a. a IN H ==> alias_certificate fn dfg lo ps states n a) ==>
  !a. a IN alias_cut_closure
    {a | normalize_operand dfg [] a = a}
    (\a. (!x. a = Var x ==> ~MEM x inst.inst_outputs) /\
         (!x. normalize_operand dfg [] a = Var x ==> ~MEM x inst.inst_outputs))
    (\dst src. ?x. dst = Var x /\ inst.inst_opcode = ASSIGN /\
       inst.inst_operands = [src] /\ inst.inst_outputs = [x] /\
       normalize_operand dfg [] (Var x) = normalize_operand dfg [] src /\
       (!y. normalize_operand dfg [] src = Var y ==> ~MEM y inst.inst_outputs)) H ==>
    alias_certificate fn dfg lo ps states (SUC n) a
Proof
  rw[alias_cut_closure_def]
  >- (irule (cj 1 alias_certificate_rules) >> simp[]) 
  >- (irule (cj 3 alias_certificate_rules) >> metis_tac[]) >>
  irule (cj 5 alias_certificate_rules) >> metis_tac[]
QED

Theorem alias_cut_closure_coverage:
  Q SUBSET alias_cut_closure Z safe repair H <=>
  (!a. a IN Q /\ a NOTIN Z ==>
    (safe a /\ a IN H) \/ ?src. src IN H /\ repair a src)
Proof
  rw[alias_cut_closure_def, pred_setTheory.SUBSET_DEF] >> metis_tac[]
QED

Theorem alias_cut_closure_barrier:
  a NOTIN Z /\ ~safe a /\ (!src. ~repair a src) ==>
  a NOTIN alias_cut_closure Z safe repair H
Proof
  simp[alias_cut_closure_def]
QED

Theorem alias_cut_closure_repair:
  repair a src /\ src IN H ==> a IN alias_cut_closure Z safe repair H
Proof
  rw[alias_cut_closure_def] >> metis_tac[]
QED

Theorem alias_cut_closure_two_cut_repair:
  src IN Z /\ repair2 a src ==>
  a IN alias_cut_closure Z safe2 repair2 (alias_cut_closure Z safe1 repair1 H)
Proof
  rw[alias_cut_closure_def] >> metis_tac[]
QED

Theorem alias_cut_root_write_barrier:
  normalize_operand dfg [] a <> a /\
  normalize_operand dfg [] a = Var r /\ MEM r inst.inst_outputs /\
  (!src. ~repair a src) ==>
  a NOTIN alias_cut_closure {a | normalize_operand dfg [] a = a}
    (\a. (!x. a = Var x ==> ~MEM x inst.inst_outputs) /\
         (!x. normalize_operand dfg [] a = Var x ==> ~MEM x inst.inst_outputs)) repair H
Proof
  strip_tac >> irule alias_cut_closure_barrier >> simp[] >>
  metis_tac[alias_certificate_root_write_blocks_survival]
QED

Theorem alias_cut_phi_root_write_barrier:
  normalize_operand dfg [] a <> a /\
  normalize_operand dfg [] a = Var r /\ MEM inst instructions /\
  inst.inst_opcode = PHI /\ MEM r inst.inst_outputs ==>
  a NOTIN alias_cut_closure {a | normalize_operand dfg [] a = a}
    (\a. (!x t. a = Var x /\ MEM t instructions /\ t.inst_opcode = PHI ==>
            ~MEM x t.inst_outputs) /\
         (!x t. normalize_operand dfg [] a = Var x /\
            MEM t instructions /\ t.inst_opcode = PHI ==> ~MEM x t.inst_outputs))
    (\dst src. F) H
Proof
  strip_tac >> irule alias_cut_closure_barrier >> simp[] >> metis_tac[]
QED

(* Endpoint demand cannot cross a PHI root-write barrier unchanged.
   The producer must delete this demand or supply a later ASSIGN repair. *)
Theorem alias_cut_phi_demand_exclusion:
  Q SUBSET alias_cut_closure {a | normalize_operand dfg [] a = a}
    (\a. (!x t. a = Var x /\ MEM t instructions /\ t.inst_opcode = PHI ==>
            ~MEM x t.inst_outputs) /\
         (!x t. normalize_operand dfg [] a = Var x /\
            MEM t instructions /\ t.inst_opcode = PHI ==> ~MEM x t.inst_outputs))
    (\dst src. F) H /\
  normalize_operand dfg [] a <> a /\
  normalize_operand dfg [] a = Var r /\ MEM inst instructions /\
  inst.inst_opcode = PHI /\ MEM r inst.inst_outputs ==>
  a NOTIN Q
Proof
  strip_tac >> drule_all alias_cut_phi_root_write_barrier >>
  gvs[pred_setTheory.SUBSET_DEF] >> metis_tac[]
QED

(* Root-cut diagnostic: an incoming PHI source may alias that PHI's output.
   Entry-held is intentionally distinguished from final-held. *)
Definition alias_root_phi_fn_def:
  alias_root_phi_fn = mk_raw_function "root_phi"
    [<| bb_label := "entry"; bb_instructions :=
       [mk_inst 0 CALLDATASIZE [] ["seed"];
        mk_inst 1 JMP [Label "header"] []] |>;
     <| bb_label := "header"; bb_instructions :=
       [mk_inst 2 PHI [Label "entry"; Var "seed"; Label "body"; Var "a"] ["r"];
        mk_inst 3 JMP [Label "body"] []] |>;
     <| bb_label := "body"; bb_instructions :=
       [mk_inst 4 ASSIGN [Var "r"] ["a"];
        mk_inst 5 JMP [Label "header"] []] |>]
End

Theorem alias_root_phi_static:
  codegen_ready_fn alias_root_phi_fn /\
  normalize_operand (dfg_build_function alias_root_phi_fn) [] (Var "a") = Var "r" /\
  MEM "a" (input_vars_from "body" (EL 1 alias_root_phi_fn.fn_blocks).bb_instructions
    (live_vars_at (liveness_analyze alias_root_phi_fn) "header" 0)) /\
  MEM "r" (HD (EL 1 alias_root_phi_fn.fn_blocks).bb_instructions).inst_outputs
Proof
  EVAL_TAC
QED

(* C1.33: one bounded repeated-source candidate. *)
Definition alias_repeat_phi_fn_def:
  alias_repeat_phi_fn = mk_raw_function "repeat_phi"
    [<| bb_label := "entry"; bb_instructions :=
       [mk_inst 0 CALLDATASIZE [] ["seed"];
        mk_inst 1 JMP [Label "header"] []] |>;
     <| bb_label := "header"; bb_instructions :=
       [mk_inst 2 PHI [Label "entry"; Var "seed"; Label "body"; Var "b"] ["r"];
        mk_inst 3 PHI [Label "entry"; Var "seed"; Label "body"; Var "a"] ["q"];
        mk_inst 4 PHI [Label "entry"; Var "seed"; Label "body"; Var "a"] ["t"];
        mk_inst 5 JMP [Label "body"] []] |>;
     <| bb_label := "body"; bb_instructions :=
       [mk_inst 6 ADD [Var "q"; Var "t"] ["sink"];
        mk_inst 7 ASSIGN [Var "r"] ["a"];
        mk_inst 8 ADD [Var "r"; Lit 1w] ["b"];
        mk_inst 9 JMP [Label "header"] []] |>]
End

(* Readiness rejects repeated PHI sources before plan/lineage testing.
   In particular a is used by both PHI q and PHI t; seed is shared too. *)
Theorem alias_repeat_phi_disjoint_obstruction:
  MEM "a" (inst_uses (EL 1 (EL 1 alias_repeat_phi_fn.fn_blocks).bb_instructions)) /\
  MEM "a" (inst_uses (EL 2 (EL 1 alias_repeat_phi_fn.fn_blocks).bb_instructions)) /\
  ~phi_uses_disjoint (collect_phis (EL 1 alias_repeat_phi_fn.fn_blocks).bb_instructions) /\
  ~phi_operands_ready alias_repeat_phi_fn
Proof
  EVAL_TAC
QED

Theorem alias_repeat_phi_not_ready:
  ~codegen_ready_fn alias_repeat_phi_fn
Proof
  EVAL_TAC
QED

Definition alias_root_phi_plan_def:
  alias_root_phi_plan i ps = generate_block_plan (liveness_analyze alias_root_phi_fn)
    (dfg_build_function alias_root_phi_fn) (cfg_analyze alias_root_phi_fn)
    alias_root_phi_fn (EL i alias_root_phi_fn.fn_blocks) ps
End

Definition alias_root_phi_e_def:
  alias_root_phi_e = THE (alias_root_phi_plan 0 (init_cleanup_plan_state NONE [] 0 0))
End
Definition alias_root_phi_h_def:
  alias_root_phi_h = THE (alias_root_phi_plan 1 (SND alias_root_phi_e))
End
Definition alias_root_phi_b_def:
  alias_root_phi_b = THE (alias_root_phi_plan 2 (SND alias_root_phi_h))
End

Theorem alias_root_phi_plans:
  alias_root_phi_plan 0 (init_cleanup_plan_state NONE [] 0 0) = SOME alias_root_phi_e /\
  alias_root_phi_plan 1 (SND alias_root_phi_e) = SOME alias_root_phi_h /\
  alias_root_phi_plan 2 (SND alias_root_phi_h) = SOME alias_root_phi_b /\
  plan_holds (SND alias_root_phi_b) (Var "a") /\
  (SND alias_root_phi_b).ps_cleanup_height = NONE /\
  (SND alias_root_phi_b).ps_cleanup_promised = F
Proof
  EVAL_TAC
QED

Theorem alias_root_phi_edges:
  cfg_succs_of (cfg_analyze alias_root_phi_fn) "entry" = ["header"] /\
  cfg_succs_of (cfg_analyze alias_root_phi_fn) "header" = ["body"] /\
  cfg_succs_of (cfg_analyze alias_root_phi_fn) "body" = ["header"]
Proof
  EVAL_TAC
QED

Theorem alias_root_phi_dfs_h:
  dfs_aux_call (liveness_analyze alias_root_phi_fn)
    (dfg_build_function alias_root_phi_fn) (cfg_analyze alias_root_phi_fn) alias_root_phi_fn
    (init_cleanup_plan_state NONE [] 0 0) ["header"] ["entry"] (SND alias_root_phi_e)
Proof
  `SND alias_root_phi_e = (SND alias_root_phi_e) with
    <|ps_stack := (SND alias_root_phi_e).ps_stack;
      ps_spilled := (SND alias_root_phi_e).ps_spilled|>` by simp[] >>
  pop_assum SUBST1_TAC >> irule dfs_aux_call_branch >> qexists_tac `[]` >>
  rewrite_tac[GSYM (cj 1 alias_root_phi_edges)] >>
  irule dfs_aux_call_succs >> simp[] >>
  qexistsl_tac [`EL 0 alias_root_phi_fn.fn_blocks`, `FST alias_root_phi_e`,
    `init_cleanup_plan_state NONE [] 0 0`, `[]`] >>
  simp[GSYM alias_root_phi_plan_def, alias_root_phi_plans] >>
  conj_tac >- EVAL_TAC >> irule dfs_aux_call_entry >> EVAL_TAC
QED

Theorem alias_root_phi_dfs_b:
  dfs_aux_call (liveness_analyze alias_root_phi_fn)
    (dfg_build_function alias_root_phi_fn) (cfg_analyze alias_root_phi_fn) alias_root_phi_fn
    (init_cleanup_plan_state NONE [] 0 0) ["body"] ["header"; "entry"] (SND alias_root_phi_h)
Proof
  `SND alias_root_phi_h = (SND alias_root_phi_h) with
    <|ps_stack := (SND alias_root_phi_h).ps_stack;
      ps_spilled := (SND alias_root_phi_h).ps_spilled|>` by simp[] >>
  pop_assum SUBST1_TAC >> irule dfs_aux_call_branch >> qexists_tac `[]` >>
  rewrite_tac[GSYM (cj 2 alias_root_phi_edges)] >>
  irule dfs_aux_call_succs >> simp[] >>
  qexistsl_tac [`EL 1 alias_root_phi_fn.fn_blocks`, `FST alias_root_phi_h`,
    `SND alias_root_phi_e`, `[]`] >>
  simp[GSYM alias_root_phi_plan_def, alias_root_phi_plans, alias_root_phi_dfs_h] >> EVAL_TAC
QED

Theorem alias_root_phi_dfs_states:
  dfs_block_state (liveness_analyze alias_root_phi_fn)
    (dfg_build_function alias_root_phi_fn) (cfg_analyze alias_root_phi_fn) alias_root_phi_fn
    (init_cleanup_plan_state NONE [] 0 0) "entry" (init_cleanup_plan_state NONE [] 0 0) /\
  dfs_block_state (liveness_analyze alias_root_phi_fn)
    (dfg_build_function alias_root_phi_fn) (cfg_analyze alias_root_phi_fn) alias_root_phi_fn
    (init_cleanup_plan_state NONE [] 0 0) "header" (SND alias_root_phi_e) /\
  dfs_block_state (liveness_analyze alias_root_phi_fn)
    (dfg_build_function alias_root_phi_fn) (cfg_analyze alias_root_phi_fn) alias_root_phi_fn
    (init_cleanup_plan_state NONE [] 0 0) "body" (SND alias_root_phi_h)
Proof
  rewrite_tac[dfs_block_state_def] >> conj_tac
  >- (qexistsl_tac [`[]`, `[]`] >> simp[] >> irule dfs_aux_call_entry >> EVAL_TAC) >>
  conj_tac
  >- (qexistsl_tac [`[]`, `["entry"]`] >> simp[alias_root_phi_dfs_h]) >>
  qexistsl_tac [`[]`, `["header"; "entry"]`] >> simp[alias_root_phi_dfs_b]
QED

Theorem alias_root_phi_lineage_header:
  lineage_state (liveness_analyze alias_root_phi_fn)
    (dfg_build_function alias_root_phi_fn) (cfg_analyze alias_root_phi_fn) alias_root_phi_fn
    (init_cleanup_plan_state NONE [] 0 0) "header" (SND alias_root_phi_e)
Proof
  `SND alias_root_phi_e = (SND alias_root_phi_e) with
    <|ps_stack := (SND alias_root_phi_e).ps_stack;
      ps_spilled := (SND alias_root_phi_e).ps_spilled|>` by simp[] >>
  pop_assum SUBST1_TAC >> irule lineage_state_step >> simp[alias_root_phi_dfs_states] >>
  qexistsl_tac [`EL 0 alias_root_phi_fn.fn_blocks`, `FST alias_root_phi_e`, `NONE`, `"entry"`, `F`,
    `init_cleanup_plan_state NONE [] 0 0`, `init_cleanup_plan_state NONE [] 0 0`,
    `SND alias_root_phi_e`] >>
  simp[GSYM alias_root_phi_plan_def, alias_root_phi_plans, alias_root_phi_dfs_states,
       alias_root_phi_edges] >> conj_tac >- EVAL_TAC >>
  reverse conj_tac >- (irule lineage_state_entry >> EVAL_TAC) >>
  `init_cleanup_plan_state NONE [] 0 0 with
    <|ps_cleanup_height := NONE; ps_cleanup_promised := F|> =
    init_cleanup_plan_state NONE [] 0 0` by simp[init_cleanup_plan_state_def] >>
  simp[GSYM alias_root_phi_plan_def, alias_root_phi_plans]
QED

Theorem alias_root_phi_lineage_body:
  lineage_state (liveness_analyze alias_root_phi_fn)
    (dfg_build_function alias_root_phi_fn) (cfg_analyze alias_root_phi_fn) alias_root_phi_fn
    (init_cleanup_plan_state NONE [] 0 0) "body" (SND alias_root_phi_h)
Proof
  `SND alias_root_phi_h = (SND alias_root_phi_h) with
    <|ps_stack := (SND alias_root_phi_h).ps_stack;
      ps_spilled := (SND alias_root_phi_h).ps_spilled|>` by simp[] >>
  pop_assum SUBST1_TAC >> irule lineage_state_step >> simp[alias_root_phi_dfs_states] >>
  qexistsl_tac [`EL 1 alias_root_phi_fn.fn_blocks`, `FST alias_root_phi_h`, `NONE`, `"header"`, `F`,
    `SND alias_root_phi_e`, `SND alias_root_phi_e`, `SND alias_root_phi_h`] >>
  simp[GSYM alias_root_phi_plan_def, alias_root_phi_plans, alias_root_phi_dfs_states,
       alias_root_phi_edges, alias_root_phi_lineage_header] >> EVAL_TAC
QED

Theorem alias_root_phi_lineage_loop:
  lineage_state (liveness_analyze alias_root_phi_fn)
    (dfg_build_function alias_root_phi_fn) (cfg_analyze alias_root_phi_fn) alias_root_phi_fn
    (init_cleanup_plan_state NONE [] 0 0) "header" (SND alias_root_phi_b)
Proof
  `SND alias_root_phi_b = (SND alias_root_phi_e) with
    <|ps_stack := (SND alias_root_phi_b).ps_stack;
      ps_spilled := (SND alias_root_phi_b).ps_spilled|>` by EVAL_TAC >>
  pop_assum SUBST1_TAC >> irule lineage_state_step >> simp[alias_root_phi_dfs_states] >>
  qexistsl_tac [`EL 2 alias_root_phi_fn.fn_blocks`, `FST alias_root_phi_b`, `NONE`, `"body"`, `F`,
    `SND alias_root_phi_h`, `SND alias_root_phi_h`, `SND alias_root_phi_b`] >>
  simp[GSYM alias_root_phi_plan_def, alias_root_phi_plans, alias_root_phi_dfs_states,
       alias_root_phi_edges, alias_root_phi_lineage_body] >> EVAL_TAC
QED

Theorem alias_root_phi_root_cut_counterinstance:
  codegen_ready_fn alias_root_phi_fn /\
  lineage_state (liveness_analyze alias_root_phi_fn)
    (dfg_build_function alias_root_phi_fn) (cfg_analyze alias_root_phi_fn) alias_root_phi_fn
    (init_cleanup_plan_state NONE [] 0 0) "header" (SND alias_root_phi_b) /\
  lookup_block "header" alias_root_phi_fn.fn_blocks =
    SOME (EL 1 alias_root_phi_fn.fn_blocks) /\
  plan_holds (SND alias_root_phi_b) (Var "a") /\
  normalize_operand (dfg_build_function alias_root_phi_fn) [] (Var "a") = Var "r" /\
  "a" <> "r" /\
  MEM (HD (EL 1 alias_root_phi_fn.fn_blocks).bb_instructions)
    (EL 1 alias_root_phi_fn.fn_blocks).bb_instructions /\
  MEM "r" (HD (EL 1 alias_root_phi_fn.fn_blocks).bb_instructions).inst_outputs
Proof
  simp[alias_root_phi_static, alias_root_phi_plans, alias_root_phi_lineage_loop] >> EVAL_TAC
QED

(* Historical selected-input membership does not exclude a PHI root write.
   This witness does not refute the endpoint invariant: the header consumes a. *)
Theorem alias_root_phi_selected_root_obstruction:
  codegen_ready_fn alias_root_phi_fn /\
  cfg_reachable_of (cfg_analyze alias_root_phi_fn) "body" /\
  MEM "header" (cfg_succs_of (cfg_analyze alias_root_phi_fn) "body") /\
  lookup_block "body" alias_root_phi_fn.fn_blocks =
    SOME (EL 2 alias_root_phi_fn.fn_blocks) /\
  lookup_block "header" alias_root_phi_fn.fn_blocks =
    SOME (EL 1 alias_root_phi_fn.fn_blocks) /\
  MEM "a" (input_vars_from "body" (EL 1 alias_root_phi_fn.fn_blocks).bb_instructions
    (live_vars_at (liveness_analyze alias_root_phi_fn) "header" 0)) /\
  normalize_operand (dfg_build_function alias_root_phi_fn) [] (Var "a") = Var "r" /\
  MEM (HD (EL 1 alias_root_phi_fn.fn_blocks).bb_instructions)
    (collect_phis (EL 1 alias_root_phi_fn.fn_blocks).bb_instructions) /\
  MEM "r" (inst_defs (HD (EL 1 alias_root_phi_fn.fn_blocks).bb_instructions)) /\
  IS_SOME (alias_root_phi_plan 1 (SND alias_root_phi_b)) /\
  ~plan_holds (SND (THE (alias_root_phi_plan 1 (SND alias_root_phi_b)))) (Var "a")
Proof
  simp[alias_root_phi_static] >> EVAL_TAC
QED

Theorem alias_support_obstruction_names_reflexive:
  normalize_operand (dfg_build_function alias_retired_fn) [] (Var "b") = Var "b" /\
  normalize_operand (dfg_build_function alias_halting_cut_fn) [] (Var "dead") = Var "dead" /\
  normalize_operand (dfg_build_function alias_offset_branch_fn) [] (Var "v") = Var "v"
Proof
  EVAL_TAC
QED

(* Ghost cut histories: demands are parameters only for this interface audit.
   A lineage lift must instantiate them with actual pre-PHI edge inputs or
   ordinary live_vars_at sets, and must prove the planner-step projection. *)
Definition alias_retirement_witness_def:
  alias_retirement_witness dfg cuts demand writes (n:num) x <=>
    ?j. j <= n /\ plan_holds (cuts j) (Var x) /\ x IN demand j /\
      !k. j <= k /\ k < n ==>
        x NOTIN writes k /\
        !r. normalize_operand dfg [] (Var x) = Var r ==> r NOTIN writes k
End

Definition alias_live_or_retired_def:
  alias_live_or_retired dfg cuts demand writes n <=>
    !x. plan_holds (cuts n) (Var x) /\
        normalize_operand dfg [] (Var x) <> Var x ==>
      alias_var_mass x (cuts n) <= 1 /\
      (x IN demand n \/ alias_retirement_witness dfg cuts demand writes n x)
End

(* Exact write obligations, NOT assertions that lineage produces them.
   The regular obligation permits an executed ASSIGN repair separately. *)
Definition alias_regular_tracked_fresh_def:
  alias_regular_tracked_fresh dfg inst x <=>
    ~MEM x inst.inst_outputs /\
    !r. normalize_operand dfg [] (Var x) = Var r ==> ~MEM r inst.inst_outputs
End

Definition alias_phi_root_exclusion_def:
  alias_phi_root_exclusion dfg inst after <=>
    !x r. normalize_operand dfg [] (Var x) <> Var x /\
      normalize_operand dfg [] (Var x) = Var r /\ MEM r inst.inst_outputs ==>
      ~plan_holds after (Var x)
End

Theorem alias_retirement_last_write_barrier:
  normalize_operand dfg [] (Var x) = Var r /\ r IN writes n /\
  x NOTIN demand (SUC n) ==>
  ~alias_retirement_witness dfg cuts demand writes (SUC n) x
Proof
  strip_tac >> pure_rewrite_tac [alias_retirement_witness_def] >>
  strip_tac >>
  Cases_on `j = SUC n` >- gvs[] >>
  `j <= n` by decide_tac >>
  first_x_assum (qspec_then `n` mp_tac) >> simp[]
QED

Theorem alias_live_or_retired_root_write_obligation:
  alias_live_or_retired dfg cuts demand writes (SUC n) /\
  normalize_operand dfg [] (Var x) <> Var x /\
  normalize_operand dfg [] (Var x) = Var r /\ r IN writes n /\
  x NOTIN demand (SUC n) ==>
  ~plan_holds (cuts (SUC n)) (Var x)
Proof
  strip_tac >> drule_all alias_retirement_last_write_barrier >>
  disch_then (qspec_then `cuts` assume_tac) >>
  fs[alias_live_or_retired_def] >> strip_tac >>
  first_x_assum (qspec_then `x` mp_tac) >> simp[]
QED

(* A prior live PHI keeps a, and a different selected alias b is then
   consumed by a root-writing PHI. This is a symbolic planner cut, NOT a
   reachable function/lineage counterexample. In particular the demands
   and PHI placement here have not been justified by analyzed liveness. *)
Theorem alias_history_unselected_phi_cut:
  (SND (generate_phi_plan
    (mk_inst 0 PHI [Label "left"; Var "a"] ["p"])
    ["a"; "b"; "p"] F
    ((init_plan_state 0) with ps_stack := [Var "a"; Var "b"]))).ps_stack =
      [Var "a"; Var "b"; Var "p"] /\
  (SND (generate_phi_plan
    (mk_inst 1 PHI [Label "left"; Var "b"] ["r"])
    ["r"] F
    ((init_plan_state 0) with ps_stack := [Var "a"; Var "b"; Var "p"]))).ps_stack =
      [Var "a"; Var "r"; Var "p"]
Proof
  EVAL_TAC
QED

Theorem alias_history_shared_root_exclusion_fails:
  normalize_operand dfg [] (Var "a") = Var "r" /\
  normalize_operand dfg [] (Var "b") = Var "r" ==>
  ~alias_phi_root_exclusion dfg
    (mk_inst 1 PHI [Label "left"; Var "b"] ["r"])
    (SND (generate_phi_plan
      (mk_inst 1 PHI [Label "left"; Var "b"] ["r"])
      ["r"] F
      ((init_plan_state 0) with ps_stack := [Var "a"; Var "b"; Var "p"])))
Proof
  strip_tac >>
  simp[alias_phi_root_exclusion_def] >>
  qexistsl_tac [`"a"`, `"r"`] >>
  simp[mk_inst_def, plan_holds_def, alias_history_unselected_phi_cut]
QED

(* C1.93.3.4.1 write-interface audit:
   - Demanded nonreflexive x at an ordinary cut: alias_live_available_after_phis
     supplies availability; alias_available_suffix_not_output excludes writes
     to x; alias_live_root_not_defined excludes writes to its variable root.
     Thus alias_regular_tracked_fresh follows at that cut. An output x itself
     instead requires the executed ASSIGN repair, not this freshness claim.
   - Retired nonreflexive x: the witness excludes earlier writes only. It says
     NOTHING about writes n. alias_retirement_last_write_barrier proves that
     a root write at n destroys every old witness if x is not newly demanded.
     Exclusion of the retained x (or a reformulated repair-aware invariant)
     is therefore a producer obligation, not a consequence of retirement.
   - Reflexive residue: alias_live_or_retired deliberately imposes no budget
     or history requirement. Its alias equality is reflexive even at a write.
   - PHI selected source: alias_phi_dead_selected_consumed requires SOME d,
     peek d = Var x, deadness, x <> output, and mass x <= 1. Slot existence
     comes from alias_lineage_join_phi_prefix_total_slots; identifying x with
     the selected slot and establishing the budget remain separate obligations.
     Nonreflexivity supplies output difference when the output is its root.
     A live PHI retains its source, as alias_history_unselected_phi_cut checks.
   - Unselected sharing-root source: even a per-name budget of one does not
     delete a when the selected b is poked to r. The checked cut above keeps
     a, consumes b and leaves the unrelated p untouched. Its arbitrary dfg
     premises express the sharing-root case; they do not establish a reachable
     SSA function, genuine analyzed demand, or lineage-step projection.
     alias_history_shared_root_exclusion_fails refutes blanket PHI exclusion
     on arbitrary cuts, NOT lineage_alias_successor. The history candidate
     is not yet an inductive lineage invariant. Its genuine write-step
     preservation and initial-state projection remain unproved. *)

Theorem alias_var_mass_init_cleanup[simp]:
  alias_var_mass x (init_cleanup_plan_state ch growth spill_base lbl_ctr) = 0
Proof
  simp[alias_var_mass_def, init_cleanup_plan_state_def, init_plan_state_def,
       LIST_ELEM_COUNT_THM]
QED

Theorem alias_live_or_retired_initial:
  alias_live_or_retired dfg
    (\k. init_cleanup_plan_state ch growth spill_base lbl_ctr)
    demand writes 0
Proof
  simp[alias_live_or_retired_def]
QED

Definition alias_shared_phi_fn_def:
  alias_shared_phi_fn = mk_raw_function "shared_phi_probe"
    [<| bb_label := "entry"; bb_instructions :=
       [mk_inst 0 CALLDATASIZE [] ["e"];
        mk_inst 1 JMP [Label "header"] []] |>;
     <| bb_label := "header"; bb_instructions :=
       [mk_inst 2 PHI [Label "entry"; Var "e"; Label "backedge"; Var "a"] ["p"];
        mk_inst 3 PHI [Label "entry"; Var "e"; Label "backedge"; Var "b"] ["r"];
        mk_inst 4 PHI [Label "entry"; Var "e"; Label "backedge"; Var "a"] ["s"];
        mk_inst 5 JMP [Label "body"] []] |>;
     <| bb_label := "body"; bb_instructions :=
       [mk_inst 6 ASSIGN [Var "r"] ["a"];
        mk_inst 7 ASSIGN [Var "r"] ["b"];
        mk_inst 8 ADD [Var "p"; Var "s"] ["t"];
        mk_inst 9 ISZERO [Var "t"] ["z"];
        mk_inst 10 JNZ [Var "z"; Label "backedge"; Label "exit"] []] |>;
     <| bb_label := "exit"; bb_instructions := [mk_inst 11 STOP [] []] |>;
     <| bb_label := "backedge"; bb_instructions :=
       [mk_inst 12 JMP [Label "header"] []] |>]
End

Theorem alias_shared_phi_readiness_audit:
  [canonical_param_prefix alias_shared_phi_fn;
   wf_function alias_shared_phi_fn;
   fn_inst_wf alias_shared_phi_fn;
   ssa_form alias_shared_phi_fn;
   def_dominates_uses alias_shared_phi_fn;
   single_use_form alias_shared_phi_fn;
   cfg_is_normalized (cfg_analyze alias_shared_phi_fn) alias_shared_phi_fn;
   block_entries_ready (cfg_analyze alias_shared_phi_fn) alias_shared_phi_fn;
   phi_operands_ready alias_shared_phi_fn;
   EVERY (\bb. EVERY codegen_ready_inst bb.bb_instructions) alias_shared_phi_fn.fn_blocks;
   offset_outputs_used alias_shared_phi_fn;
   phis_at_joins (cfg_analyze alias_shared_phi_fn) alias_shared_phi_fn] =
  [T;T;T;T;T;T;T;T;F;T;T;T]
Proof
  EVAL_TAC
QED

Theorem alias_shared_phi_roots:
  normalize_operand (dfg_build_function alias_shared_phi_fn) [] (Var "a") = Var "r" /\
  normalize_operand (dfg_build_function alias_shared_phi_fn) [] (Var "b") = Var "r"
Proof
  EVAL_TAC
QED

(* The repeated-name retention mechanism is inadmissible: a occurs in two
   PHIs and e occurs in all three. The readiness vector fails only its ninth
   clause, phi_operands_ready. No DFS/lineage or run witness is constructed
   for this rejected fixture. Universal interfaces already available are
   alias_phi_uses_disjoint_index, alias_phi_ready_ordinary_input and
   alias_phi_ready_postprefix_input. These constrain PHI input NAMES and their
   subsequent demand, not distinct aliases sharing a normalized root, nor
   unrelated retired stack residues. This is not a target counterexample. *)
Theorem alias_shared_phi_rejected:
  ~codegen_ready_fn alias_shared_phi_fn /\
  ~phi_uses_disjoint
    (collect_phis (EL 1 alias_shared_phi_fn.fn_blocks).bb_instructions) /\
  MEM "a" (inst_uses (EL 0 (EL 1 alias_shared_phi_fn.fn_blocks).bb_instructions)) /\
  MEM "a" (inst_uses (EL 2 (EL 1 alias_shared_phi_fn.fn_blocks).bb_instructions))
Proof
  EVAL_TAC
QED

(* Single-PHI experiment: a is dead and is not a PHI input. *)
Definition alias_dead_phi_fn_def:
  alias_dead_phi_fn = mk_raw_function "dead_phi_probe"
    [<| bb_label := "entry"; bb_instructions :=
         [mk_inst 100 CALLDATASIZE [] ["e"];
          mk_inst 101 JMP [Label "header"] []] |>;
     <| bb_label := "header"; bb_instructions :=
         [mk_inst 102 PHI [Label "entry"; Var "e"; Label "backedge"; Var "b"] ["r"];
          mk_inst 103 JMP [Label "body"] []] |>;
     <| bb_label := "body"; bb_instructions :=
         [mk_inst 104 ASSIGN [Var "r"] ["a"];
          mk_inst 105 ASSIGN [Var "r"] ["b"];
          mk_inst 106 CALLDATASIZE [] ["c"];
          mk_inst 107 JNZ [Var "c"; Label "backedge"; Label "exit"] []] |>;
     <| bb_label := "exit"; bb_instructions := [mk_inst 108 STOP [] []] |>;
     <| bb_label := "backedge"; bb_instructions := [mk_inst 109 JMP [Label "header"] []] |>]
End

Theorem alias_dead_phi_ready:
  codegen_ready_fn alias_dead_phi_fn
Proof
  EVAL_TAC
QED

Theorem alias_dead_phi_roots:
  normalize_operand (dfg_build_function alias_dead_phi_fn) [] (Var "a") = Var "r" /\
  normalize_operand (dfg_build_function alias_dead_phi_fn) [] (Var "b") = Var "r"
Proof
  EVAL_TAC
QED

Definition alias_dead_phi_plan_def:
  alias_dead_phi_plan n ps = generate_block_plan
    (liveness_analyze alias_dead_phi_fn) (dfg_build_function alias_dead_phi_fn)
    (cfg_analyze alias_dead_phi_fn) alias_dead_phi_fn (EL n alias_dead_phi_fn.fn_blocks) ps
End

Definition alias_dead_phi_entry_def:
  alias_dead_phi_entry = THE (alias_dead_phi_plan 0 (init_cleanup_plan_state NONE [] 0 0))
End

Definition alias_dead_phi_header_def:
  alias_dead_phi_header = THE (alias_dead_phi_plan 1 (SND alias_dead_phi_entry))
End

Definition alias_dead_phi_body_def:
  alias_dead_phi_body = THE (alias_dead_phi_plan 2 (SND alias_dead_phi_header))
End

Definition alias_dead_phi_backedge_def:
  alias_dead_phi_backedge = THE (alias_dead_phi_plan 4 (SND alias_dead_phi_body))
End

Definition alias_dead_phi_reentry_def:
  alias_dead_phi_reentry = (SND alias_dead_phi_entry) with
    <|ps_stack := (SND alias_dead_phi_backedge).ps_stack;
      ps_spilled := (SND alias_dead_phi_backedge).ps_spilled|>
End

Theorem alias_dead_phi_plans_success:
  IS_SOME (alias_dead_phi_plan 0 (init_cleanup_plan_state NONE [] 0 0)) /\
  IS_SOME (alias_dead_phi_plan 1 (SND alias_dead_phi_entry)) /\
  IS_SOME (alias_dead_phi_plan 2 (SND alias_dead_phi_header)) /\
  IS_SOME (alias_dead_phi_plan 4 (SND alias_dead_phi_body)) /\
  IS_SOME (alias_dead_phi_plan 1 alias_dead_phi_reentry)
Proof
  conj_tac >- EVAL_TAC >> conj_tac >- EVAL_TAC >>
  conj_tac >- EVAL_TAC >> conj_tac >- EVAL_TAC >> EVAL_TAC
QED

Theorem alias_dead_phi_endpoint_inventory:
  (SND alias_dead_phi_entry).ps_stack = [Var "e"] /\
  (SND alias_dead_phi_header).ps_stack = [Var "r"] /\
  (SND alias_dead_phi_body).ps_stack = [Var "b"] /\
  (SND alias_dead_phi_body).ps_spilled = FEMPTY /\
  (SND alias_dead_phi_backedge).ps_stack = [Var "b"] /\
  (SND alias_dead_phi_backedge).ps_spilled = FEMPTY /\
  (SND (THE (alias_dead_phi_plan 1 alias_dead_phi_reentry))).ps_stack = [Var "r"] /\
  (SND (THE (alias_dead_phi_plan 1 alias_dead_phi_reentry))).ps_spilled = FEMPTY
Proof
  conj_tac >- EVAL_TAC >> conj_tac >- EVAL_TAC >>
  conj_tac >- EVAL_TAC >> conj_tac >- EVAL_TAC >>
  conj_tac >- EVAL_TAC >> conj_tac >- EVAL_TAC >>
  conj_tac >- EVAL_TAC >> EVAL_TAC
QED

Definition alias_dead_phi_body_cut_def:
  (alias_dead_phi_body_cut 0 = SND (clean_stack_plan
    (liveness_analyze alias_dead_phi_fn) (cfg_analyze alias_dead_phi_fn)
    alias_dead_phi_fn (EL 2 alias_dead_phi_fn.fn_blocks) (SND alias_dead_phi_header))) /\
  (alias_dead_phi_body_cut (SUC n) = SND (THE (generate_inst_plan
    (liveness_analyze alias_dead_phi_fn) (dfg_build_function alias_dead_phi_fn)
    (cfg_analyze alias_dead_phi_fn) alias_dead_phi_fn
    (EL n (EL 2 alias_dead_phi_fn.fn_blocks).bb_instructions)
    (live_vars_at (liveness_analyze alias_dead_phi_fn) "body" (SUC n))
    F (n = 2) "body" (alias_dead_phi_body_cut n))))
End

Theorem alias_dead_phi_body_cuts:
  (alias_dead_phi_body_cut 0).ps_stack = [Var "r"] /\
  (alias_dead_phi_body_cut 1).ps_stack = [Var "r"] /\
  (alias_dead_phi_body_cut 2).ps_stack = [Var "b"] /\
  (alias_dead_phi_body_cut 3).ps_stack = [Var "b"; Var "c"] /\
  (alias_dead_phi_body_cut 4).ps_stack = [Var "b"]
Proof
  conj_tac >- EVAL_TAC >>
  conj_tac >- EVAL_TAC >>
  conj_tac >- EVAL_TAC >>
  conj_tac >- EVAL_TAC >> EVAL_TAC
QED

Theorem alias_dead_phi_plans:
  alias_dead_phi_plan 0 (init_cleanup_plan_state NONE [] 0 0) = SOME alias_dead_phi_entry /\
  alias_dead_phi_plan 1 (SND alias_dead_phi_entry) = SOME alias_dead_phi_header /\
  alias_dead_phi_plan 2 (SND alias_dead_phi_header) = SOME alias_dead_phi_body /\
  alias_dead_phi_plan 4 (SND alias_dead_phi_body) = SOME alias_dead_phi_backedge
Proof
  mp_tac alias_dead_phi_plans_success >>
  Cases_on `alias_dead_phi_plan 0 (init_cleanup_plan_state NONE [] 0 0)` >>
  Cases_on `alias_dead_phi_plan 1 (SND alias_dead_phi_entry)` >>
  Cases_on `alias_dead_phi_plan 2 (SND alias_dead_phi_header)` >>
  Cases_on `alias_dead_phi_plan 4 (SND alias_dead_phi_body)` >>
  simp[alias_dead_phi_entry_def, alias_dead_phi_header_def,
       alias_dead_phi_body_def, alias_dead_phi_backedge_def]
QED

Theorem alias_dead_phi_entry_state:
  SND alias_dead_phi_entry =
    init_cleanup_plan_state NONE [] 0 0 with ps_stack := [Var "e"]
Proof
  EVAL_TAC
QED

Theorem alias_dead_phi_header_state:
  SND alias_dead_phi_header =
    init_cleanup_plan_state NONE [] 0 0 with ps_stack := [Var "r"]
Proof
  rewrite_tac[alias_dead_phi_header_def, alias_dead_phi_entry_state] >> EVAL_TAC
QED

Theorem alias_dead_phi_body_state:
  SND alias_dead_phi_body =
    init_cleanup_plan_state NONE [] 0 0 with ps_stack := [Var "b"]
Proof
  rewrite_tac[alias_dead_phi_body_def, alias_dead_phi_header_state] >> EVAL_TAC
QED

Theorem alias_dead_phi_dfs_header:
  dfs_aux_call (liveness_analyze alias_dead_phi_fn)
    (dfg_build_function alias_dead_phi_fn) (cfg_analyze alias_dead_phi_fn) alias_dead_phi_fn
    (init_cleanup_plan_state NONE [] 0 0) ["header"] ["entry"] (SND alias_dead_phi_entry)
Proof
  `SND alias_dead_phi_entry = (SND alias_dead_phi_entry) with
    <|ps_stack := (SND alias_dead_phi_entry).ps_stack;
      ps_spilled := (SND alias_dead_phi_entry).ps_spilled|>` by simp[] >>
  pop_assum SUBST1_TAC >> irule dfs_aux_call_branch >> qexists_tac `[]` >>
  `cfg_succs_of (cfg_analyze alias_dead_phi_fn) "entry" = ["header"]` by EVAL_TAC >>
  pop_assum (fn th => rewrite_tac[GSYM th]) >>
  irule dfs_aux_call_succs >> simp[] >>
  qexistsl_tac [`EL 0 alias_dead_phi_fn.fn_blocks`, `FST alias_dead_phi_entry`,
    `init_cleanup_plan_state NONE [] 0 0`, `[]`] >>
  simp[GSYM alias_dead_phi_plan_def, alias_dead_phi_plans] >>
  conj_tac >- EVAL_TAC >> irule dfs_aux_call_entry >> EVAL_TAC
QED

Theorem alias_dead_phi_dfs_body:
  dfs_aux_call (liveness_analyze alias_dead_phi_fn)
    (dfg_build_function alias_dead_phi_fn) (cfg_analyze alias_dead_phi_fn) alias_dead_phi_fn
    (init_cleanup_plan_state NONE [] 0 0) ["body"] ["header"; "entry"] (SND alias_dead_phi_header)
Proof
  `SND alias_dead_phi_header = (SND alias_dead_phi_header) with
    <|ps_stack := (SND alias_dead_phi_header).ps_stack;
      ps_spilled := (SND alias_dead_phi_header).ps_spilled|>` by simp[] >>
  pop_assum SUBST1_TAC >> irule dfs_aux_call_branch >> qexists_tac `[]` >>
  `cfg_succs_of (cfg_analyze alias_dead_phi_fn) "header" = ["body"]` by EVAL_TAC >>
  pop_assum (fn th => rewrite_tac[GSYM th]) >>
  irule dfs_aux_call_succs >> simp[] >>
  qexistsl_tac [`EL 1 alias_dead_phi_fn.fn_blocks`, `FST alias_dead_phi_header`,
    `SND alias_dead_phi_entry`, `[]`] >>
  simp[GSYM alias_dead_phi_plan_def, alias_dead_phi_plans, alias_dead_phi_dfs_header] >> EVAL_TAC
QED

Theorem alias_dead_phi_exit_dfs_result:
  generate_fn_plan_aux (liveness_analyze alias_dead_phi_fn)
    (dfg_build_function alias_dead_phi_fn) (cfg_analyze alias_dead_phi_fn) alias_dead_phi_fn
    ["exit"] ["body"; "header"; "entry"] (SND alias_dead_phi_body) =
    SOME ([SOLabel "exit"; SOPop 1; SOEmit "STOP"],
      ["exit"; "body"; "header"; "entry"], init_cleanup_plan_state NONE [] 0 0)
Proof
  EVAL_TAC
QED

Theorem alias_dead_phi_dfs_backedge:
  dfs_aux_call (liveness_analyze alias_dead_phi_fn)
    (dfg_build_function alias_dead_phi_fn) (cfg_analyze alias_dead_phi_fn) alias_dead_phi_fn
    (init_cleanup_plan_state NONE [] 0 0) ["backedge"]
    ["exit"; "body"; "header"; "entry"] (SND alias_dead_phi_body)
Proof
  `SND alias_dead_phi_body = (SND alias_dead_phi_body) with
    <|ps_stack := (SND alias_dead_phi_body).ps_stack;
      ps_spilled := (SND alias_dead_phi_body).ps_spilled|>` by simp[] >>
  pop_assum SUBST1_TAC >> irule dfs_aux_call_branch >> qexists_tac `[]` >>
  `SND alias_dead_phi_body = (SND alias_dead_phi_body) with
    <|ps_alloc := (init_cleanup_plan_state NONE [] 0 0).ps_alloc with
        sa_free_slots := (SND alias_dead_phi_body).ps_alloc.sa_free_slots;
      ps_label_counter := (init_cleanup_plan_state NONE [] 0 0).ps_label_counter|>` by
    simp[alias_dead_phi_body_state, init_cleanup_plan_state_def,
         init_plan_state_def, init_spill_alloc_def] >>
  pop_assum SUBST1_TAC >> irule dfs_aux_call_sibling >>
  qexistsl_tac [`[SOLabel "exit"; SOPop 1; SOEmit "STOP"]`,
    `"exit"`, `["body"; "header"; "entry"]`] >>
  simp[alias_dead_phi_exit_dfs_result] >>
  `cfg_succs_of (cfg_analyze alias_dead_phi_fn) "body" = ["exit"; "backedge"]` by EVAL_TAC >>
  pop_assum (fn th => rewrite_tac[GSYM th]) >>
  irule dfs_aux_call_succs >> simp[] >>
  qexistsl_tac [`EL 2 alias_dead_phi_fn.fn_blocks`, `FST alias_dead_phi_body`,
    `SND alias_dead_phi_header`, `[]`] >>
  simp[GSYM alias_dead_phi_plan_def, alias_dead_phi_plans, alias_dead_phi_dfs_body] >> EVAL_TAC
QED

Theorem alias_dead_phi_dfs_states:
  dfs_block_state (liveness_analyze alias_dead_phi_fn)
    (dfg_build_function alias_dead_phi_fn) (cfg_analyze alias_dead_phi_fn) alias_dead_phi_fn
    (init_cleanup_plan_state NONE [] 0 0) "entry" (init_cleanup_plan_state NONE [] 0 0) /\
  dfs_block_state (liveness_analyze alias_dead_phi_fn)
    (dfg_build_function alias_dead_phi_fn) (cfg_analyze alias_dead_phi_fn) alias_dead_phi_fn
    (init_cleanup_plan_state NONE [] 0 0) "header" (SND alias_dead_phi_entry) /\
  dfs_block_state (liveness_analyze alias_dead_phi_fn)
    (dfg_build_function alias_dead_phi_fn) (cfg_analyze alias_dead_phi_fn) alias_dead_phi_fn
    (init_cleanup_plan_state NONE [] 0 0) "body" (SND alias_dead_phi_header) /\
  dfs_block_state (liveness_analyze alias_dead_phi_fn)
    (dfg_build_function alias_dead_phi_fn) (cfg_analyze alias_dead_phi_fn) alias_dead_phi_fn
    (init_cleanup_plan_state NONE [] 0 0) "backedge" (SND alias_dead_phi_body)
Proof
  rewrite_tac[dfs_block_state_def] >> conj_tac
  >- (qexistsl_tac [`[]`, `[]`] >> simp[] >> irule dfs_aux_call_entry >> EVAL_TAC) >>
  conj_tac >- (qexistsl_tac [`[]`, `["entry"]`] >> simp[alias_dead_phi_dfs_header]) >>
  conj_tac >- (qexistsl_tac [`[]`, `["header"; "entry"]`] >> simp[alias_dead_phi_dfs_body]) >>
  qexistsl_tac [`[]`, `["exit"; "body"; "header"; "entry"]`] >> simp[alias_dead_phi_dfs_backedge]
QED

Theorem alias_dead_phi_lineage_header:
  lineage_state (liveness_analyze alias_dead_phi_fn)
    (dfg_build_function alias_dead_phi_fn) (cfg_analyze alias_dead_phi_fn) alias_dead_phi_fn
    (init_cleanup_plan_state NONE [] 0 0) "header" (SND alias_dead_phi_entry)
Proof
  `SND alias_dead_phi_entry = (SND alias_dead_phi_entry) with
    <|ps_stack := (SND alias_dead_phi_entry).ps_stack;
      ps_spilled := (SND alias_dead_phi_entry).ps_spilled|>` by simp[] >>
  pop_assum SUBST1_TAC >> irule lineage_state_step >> simp[alias_dead_phi_dfs_states] >>
  qexistsl_tac [`EL 0 alias_dead_phi_fn.fn_blocks`, `FST alias_dead_phi_entry`, `NONE`,
    `"entry"`, `F`, `init_cleanup_plan_state NONE [] 0 0`,
    `init_cleanup_plan_state NONE [] 0 0`, `SND alias_dead_phi_entry`] >>
  simp[GSYM alias_dead_phi_plan_def, alias_dead_phi_plans, alias_dead_phi_dfs_states] >>
  conj_tac >- EVAL_TAC >> conj_tac >- EVAL_TAC >>
  conj_tac >- EVAL_TAC >> irule lineage_state_entry >> EVAL_TAC
QED

Theorem alias_dead_phi_lineage_body:
  lineage_state (liveness_analyze alias_dead_phi_fn)
    (dfg_build_function alias_dead_phi_fn) (cfg_analyze alias_dead_phi_fn) alias_dead_phi_fn
    (init_cleanup_plan_state NONE [] 0 0) "body" (SND alias_dead_phi_header)
Proof
  `SND alias_dead_phi_header = (SND alias_dead_phi_header) with
    <|ps_stack := (SND alias_dead_phi_header).ps_stack;
      ps_spilled := (SND alias_dead_phi_header).ps_spilled|>` by simp[] >>
  pop_assum SUBST1_TAC >> irule lineage_state_step >> simp[alias_dead_phi_dfs_states] >>
  qexistsl_tac [`EL 1 alias_dead_phi_fn.fn_blocks`, `FST alias_dead_phi_header`, `NONE`,
    `"header"`, `F`, `SND alias_dead_phi_entry`, `SND alias_dead_phi_entry`,
    `SND alias_dead_phi_header`] >>
  simp[GSYM alias_dead_phi_plan_def, alias_dead_phi_plans, alias_dead_phi_dfs_states,
       alias_dead_phi_lineage_header] >>
  conj_tac >- EVAL_TAC >> conj_tac >- EVAL_TAC >> EVAL_TAC
QED

Theorem alias_dead_phi_lineage_backedge:
  lineage_state (liveness_analyze alias_dead_phi_fn)
    (dfg_build_function alias_dead_phi_fn) (cfg_analyze alias_dead_phi_fn) alias_dead_phi_fn
    (init_cleanup_plan_state NONE [] 0 0) "backedge" (SND alias_dead_phi_body)
Proof
  `SND alias_dead_phi_body = (SND alias_dead_phi_body) with
    <|ps_stack := (SND alias_dead_phi_body).ps_stack;
      ps_spilled := (SND alias_dead_phi_body).ps_spilled|>` by simp[] >>
  pop_assum SUBST1_TAC >> irule lineage_state_step >> simp[alias_dead_phi_dfs_states] >>
  qexistsl_tac [`EL 2 alias_dead_phi_fn.fn_blocks`, `FST alias_dead_phi_body`, `NONE`,
    `"body"`, `F`, `SND alias_dead_phi_header`, `SND alias_dead_phi_header`,
    `SND alias_dead_phi_body`] >>
  simp[GSYM alias_dead_phi_plan_def, alias_dead_phi_plans, alias_dead_phi_dfs_states,
       alias_dead_phi_lineage_body] >>
  conj_tac >- EVAL_TAC >> conj_tac >- EVAL_TAC >> EVAL_TAC
QED

Theorem alias_dead_phi_lineage_reentry:
  lineage_entry (liveness_analyze alias_dead_phi_fn)
    (dfg_build_function alias_dead_phi_fn) (cfg_analyze alias_dead_phi_fn) alias_dead_phi_fn
    (init_cleanup_plan_state NONE [] 0 0) "backedge" "header" alias_dead_phi_reentry
Proof
  simp[lineage_entry_def] >>
  qexistsl_tac [`SND alias_dead_phi_body`, `EL 4 alias_dead_phi_fn.fn_blocks`,
    `SND alias_dead_phi_body`, `FST alias_dead_phi_backedge`, `SND alias_dead_phi_backedge`,
    `NONE`, `F`, `SND alias_dead_phi_backedge`, `SND alias_dead_phi_entry`] >>
  simp[GSYM alias_dead_phi_plan_def, alias_dead_phi_plans, alias_dead_phi_dfs_states,
       alias_dead_phi_lineage_backedge, alias_dead_phi_reentry_def] >>
  conj_tac >- EVAL_TAC >> conj_tac >- EVAL_TAC >> EVAL_TAC
QED

Theorem alias_dead_phi_cut_inventory:
  (alias_dead_phi_body_cut 0).ps_spilled = FEMPTY /\
  (alias_dead_phi_body_cut 1).ps_spilled = FEMPTY /\
  (alias_dead_phi_body_cut 2).ps_spilled = FEMPTY /\
  (alias_dead_phi_body_cut 3).ps_spilled = FEMPTY /\
  alias_dead_phi_body_cut 4 = SND alias_dead_phi_body /\
  ~MEM "a" (live_vars_at (liveness_analyze alias_dead_phi_fn) "body" 1)
Proof
  conj_tac >- EVAL_TAC >> conj_tac >- EVAL_TAC >>
  conj_tac >- EVAL_TAC >> conj_tac >- EVAL_TAC >>
  conj_tac >- EVAL_TAC >> EVAL_TAC
QED

Theorem alias_dead_phi_steps_success:
  !n. n < 4 ==>
  IS_SOME (generate_inst_plan
    (liveness_analyze alias_dead_phi_fn) (dfg_build_function alias_dead_phi_fn)
    (cfg_analyze alias_dead_phi_fn) alias_dead_phi_fn
    (EL n (EL 2 alias_dead_phi_fn.fn_blocks).bb_instructions)
    (live_vars_at (liveness_analyze alias_dead_phi_fn) "body" (SUC n))
    F (n = 2) "body" (alias_dead_phi_body_cut n))
Proof
  rpt strip_tac >> `n = 0 \/ n = 1 \/ n = 2 \/ n = 3` by decide_tac >>
  gvs[]
  >- (CONV_TAC (RAND_CONV (computeLib.RESTR_EVAL_CONV [``generate_inst_plan``])) >> EVAL_TAC)
  >- (CONV_TAC (RAND_CONV (computeLib.RESTR_EVAL_CONV [``generate_inst_plan``])) >> EVAL_TAC)
  >- (CONV_TAC (RAND_CONV (computeLib.RESTR_EVAL_CONV [``generate_inst_plan``])) >> EVAL_TAC) >>
  CONV_TAC (RAND_CONV (computeLib.RESTR_EVAL_CONV [``generate_inst_plan``])) >> EVAL_TAC
QED

Definition alias_dead_phi_phi_cut_def:
  alias_dead_phi_phi_cut = SND (generate_phi_plan
    (HD (EL 1 alias_dead_phi_fn.fn_blocks).bb_instructions)
    (live_vars_at (liveness_analyze alias_dead_phi_fn) "header" 1) F
    alias_dead_phi_reentry)
End

Theorem alias_dead_phi_reentry_inventory:
  alias_dead_phi_reentry.ps_stack = [Var "b"] /\
  alias_dead_phi_reentry.ps_spilled = FEMPTY /\
  alias_dead_phi_phi_cut.ps_stack = [Var "r"] /\
  alias_dead_phi_phi_cut.ps_spilled = FEMPTY /\
  FST (THE (alias_dead_phi_plan 1 alias_dead_phi_reentry)) = FST alias_dead_phi_header
Proof
  conj_tac >- EVAL_TAC >> conj_tac >- EVAL_TAC >>
  conj_tac >- EVAL_TAC >> conj_tac >- EVAL_TAC >> EVAL_TAC
QED

(* C1.102.2.2 destructive-PHI branch audit (not a target proof):
   The first-PHI-keeps-its-source branch in
   alias_history_unselected_phi_cut cannot have analyzed ready liveness:
   alias_ready_phi_selected_dead rules out the do_dup guard, and
   alias_ready_phi_source_dead_cuts rules out that source's later demand
   throughout the prefix. This restriction does not depend on vs_prev_bb.
   If a is instead an unselected old residue, generate_phi_plan does not
   collect it: alias_phi_plan_retains_stack covers that branch. A later
   PHI r <- b with an independent old b value can then break a = r.
   Entry held-alias equations force neutrality when normalize(b) = r
   (alias_phi_selected_root_old_value); when normalize(b) differs, mere
   input coverage supplies no equality between b and r. In particular no
   frozen premise identifies the runtime predecessor with the lineage
   witness's final predecessor. Both choices must be checked separately.
   The regular planner only pops consumed operands/dead newly produced
   outputs and releases dead spills; it is not a dead-stack sweep. Thus
   the unresolved branch is an unselected nonreflexive old stack residue,
   not the impossible live selected source. A universal producer must
   show that such a residue cannot arise from initialized lineage when an
   independent root source is selected, or identify an actual later
   consuming/repairing transition. Neither the arbitrary cut above nor
   deadness, a singleton bound, or the neutral boundary establishes this.
   No actual-lineage destructive counterexample is asserted here. *)
Theorem alias_shallow_singleton_reorder_counts:
  !dfg op ps ops qs d at.
  LENGTH ps.ps_stack <= 16 /\
  stack_get_depth op ps.ps_stack = SOME d /\
  reorder_plan dfg [op] ps = (ops,qs) ==>
  LIST_ELEM_COUNT at qs.ps_stack = LIST_ELEM_COUNT at ps.ps_stack
Proof
  rpt gen_tac >> strip_tac >>
  `d < LENGTH ps.ps_stack /\ stack_peek d ps.ps_stack = op` by
    metis_tac[stack_get_depth_props] >>
  `~(d > 16) /\ 0 < LENGTH ps.ps_stack` by decide_tac >>
  qpat_x_assum `reorder_plan _ _ _ = _` mp_tac >>
  simp[reorder_plan_def, reorder_one_def, stack_get_unfixed_depth_empty_window] >>
  Cases_on `d = 0` >- simp[] >>
  Cases_on `operand_equiv dfg op (stack_peek 0 ps.ps_stack)` >> simp[]
  >- (strip_tac >> gvs[] >>
      irule doSwapSimTheory.stack_poke_exchange_multiplicity >> simp[]) >>
  qspecl_then [`d`, `ps`, `at`] mp_tac doSwapSimTheory.do_swap_multiplicity >>
  simp[do_swap_def] >> strip_tac >> strip_tac >> gvs[]
QED

Theorem alias_shallow_emit_one_shape:
  !opc live x ps ops qs d.
  ps.ps_spilled = FEMPTY /\ LENGTH ps.ps_stack <= 15 /\
  stack_get_depth (Var x) ps.ps_stack = SOME d /\
  emit_one_input opc live (Var x) ps = (ops,qs) ==>
  qs.ps_stack = if MEM x live then ps.ps_stack ++ [Var x] else ps.ps_stack
Proof
  rpt gen_tac >> strip_tac >>
  `d < LENGTH ps.ps_stack /\ stack_peek d ps.ps_stack = Var x` by
    metis_tac[stack_get_depth_props] >>
  `d <= 15` by decide_tac >>
  gvs[emit_one_input_def, is_var_operand_def, finite_mapTheory.FLOOKUP_EMPTY] >>
  Cases_on `MEM x live` >>
  gvs[do_dup_def, stack_dup_def, SNOC_APPEND]
QED

Theorem alias_shallow_singleton_consumption_counts:
  !opc live x ps emit mid dfg ops qs d at.
  ps.ps_spilled = FEMPTY /\ LENGTH ps.ps_stack <= 15 /\
  stack_get_depth (Var x) ps.ps_stack = SOME d /\
  emit_one_input opc live (Var x) ps = (emit,mid) /\
  reorder_plan dfg [Var x] mid = (ops,qs) ==>
  LIST_ELEM_COUNT at (stack_pop 1 qs.ps_stack) +
    (if at = Var x then 1 else 0) =
  LIST_ELEM_COUNT at ps.ps_stack +
    (if MEM x live /\ at = Var x then 1 else 0)
Proof
  rpt gen_tac >> strip_tac >>
  `mid.ps_stack = if MEM x live then ps.ps_stack ++ [Var x] else ps.ps_stack` by
    metis_tac[alias_shallow_emit_one_shape] >>
  `d < LENGTH ps.ps_stack /\ stack_peek d ps.ps_stack = Var x` by
    metis_tac[stack_get_depth_props] >>
  `LENGTH mid.ps_stack <= 16 /\ 0 < LENGTH mid.ps_stack` by
    (Cases_on `MEM x live` >> gvs[] >> decide_tac) >>
  `?e. stack_get_depth (Var x) mid.ps_stack = SOME e` by
    (Cases_on `stack_get_depth (Var x) mid.ps_stack` >-
      (gvs[stack_get_depth_NONE] >> Cases_on `MEM x live` >> gvs[]
       >- (first_x_assum (qspec_then `0` mp_tac) >>
           simp[stack_peek_def, EL_LENGTH_APPEND]) >> metis_tac[]) >>
     metis_tac[]) >>
  `LIST_ELEM_COUNT at qs.ps_stack = LIST_ELEM_COUNT at mid.ps_stack` by
    metis_tac[alias_shallow_singleton_reorder_counts] >>
  `reorder_one dfg [Var x] 0 (Var x) mid = (ops,qs)` by
    (gvs[reorder_plan_def] >> pairarg_tac >> gvs[]) >>
  `stack_peek 0 qs.ps_stack = Var x` by
    (qspecl_then [`dfg`, `[Var x]`, `0`, `Var x`] mp_tac reorder_one_places >>
     simp[stack_get_unfixed_depth_empty_window] >>
     disch_then (qspec_then `mid` mp_tac) >>
     `1 <= LENGTH mid.ps_stack` by decide_tac >> simp[]) >>
  `MEM (Var x) mid.ps_stack` by
    (qpat_assum `stack_get_depth _ _ = SOME e` (mp_tac o MATCH_MP stack_get_depth_props) >>
     pure_rewrite_tac[stack_peek_def] >> strip_tac >>
     pure_rewrite_tac[MEM_EL] >>
     qexists `LENGTH mid.ps_stack - 1 - e` >>
     conj_tac >- decide_tac >> metis_tac[]) >>
  `qs.ps_stack <> []` by
    (`LIST_ELEM_COUNT (Var x) qs.ps_stack = LIST_ELEM_COUNT (Var x) mid.ps_stack` by
       metis_tac[alias_shallow_singleton_reorder_counts] >>
     strip_tac >> fs[LIST_ELEM_COUNT_DEF, GSYM LIST_ELEM_COUNT_MEM]) >>
  `?ys y. qs.ps_stack = SNOC y ys` by metis_tac[rich_listTheory.SNOC_CASES] >>
  gvs[stack_pop_def, stack_peek_def,
      rich_listTheory.TAKE_SNOC, EL_LENGTH_SNOC] >>
  Cases_on `MEM x live` >> Cases_on `at = Var x` >>
  gvs[SNOC_APPEND, elem_count_append, LIST_ELEM_COUNT_DEF,
      FILTER_APPEND, TAKE_APPEND, EL_APPEND_EQN]
QED

Theorem alias_shallow_dead_singleton_consumed:
  ps.ps_spilled = FEMPTY /\ LENGTH ps.ps_stack <= 15 /\
  stack_get_depth (Var x) ps.ps_stack = SOME d /\
  emit_one_input opc live (Var x) ps = (emit,mid) /\
  reorder_plan dfg [Var x] mid = (ops,qs) /\
  ~MEM x live /\ LIST_ELEM_COUNT (Var x) ps.ps_stack = 1 ==>
  ~MEM (Var x) (stack_pop 1 qs.ps_stack)
Proof
  strip_tac >>
  drule_all alias_shallow_singleton_consumption_counts >>
  disch_then (qspec_then `Var x` mp_tac) >>
  simp[GSYM LIST_ELEM_COUNT_MEM]
QED

Theorem alias_shallow_other_operand_consumed:
  ps.ps_spilled = FEMPTY /\ LENGTH ps.ps_stack <= 15 /\
  stack_get_depth (Var x) ps.ps_stack = SOME d /\
  emit_one_input opc live (Var x) ps = (emit,mid) /\
  reorder_plan dfg [Var x] mid = (ops,qs) /\ at <> Var x ==>
  LIST_ELEM_COUNT at (stack_pop 1 qs.ps_stack) = LIST_ELEM_COUNT at ps.ps_stack
Proof
  strip_tac >>
  drule_all alias_shallow_singleton_consumption_counts >>
  disch_then (qspec_then `at` mp_tac) >> simp[]
QED

Theorem alias_eval_phis_neutral_lookup:
  !insts s t r.
    eval_phis s insts = OK t /\
    (!inst v. MEM inst (TAKE (phi_prefix_length insts) insts) /\
      eval_one_phi s inst = SOME (r,v) ==> FLOOKUP s.vs_vars r = SOME v) ==>
    FLOOKUP t.vs_vars r = FLOOKUP s.vs_vars r
Proof
  Induct_on `insts`
  >- simp[eval_phis_def] >>
  rpt gen_tac >>
  Cases_on `h.inst_opcode = PHI` >>
  simp[eval_phis_def, phi_prefix_length_def] >>
  Cases_on `eval_one_phi s h` >> simp[] >>
  PairCases_on `x` >> simp[] >>
  Cases_on `eval_phis s insts` >> simp[] >>
  strip_tac >> gvs[update_var_def, finite_mapTheory.FLOOKUP_UPDATE] >>
  Cases_on `x0 = r` >> gvs[]
  >- metis_tac[] >>
  first_x_assum irule >> simp[] >> metis_tac[]
QED

Theorem alias_eval_phis_shared_root:
  eval_phis s insts = OK t /\
  (!inst v. MEM inst (TAKE (phi_prefix_length insts) insts) /\
    eval_one_phi s inst = SOME (r,v) ==> FLOOKUP s.vs_vars r = SOME v) /\
  FLOOKUP t.vs_vars x = FLOOKUP s.vs_vars x /\
  FLOOKUP s.vs_vars x = FLOOKUP s.vs_vars r ==>
  FLOOKUP t.vs_vars x = FLOOKUP t.vs_vars r
Proof
  metis_tac[alias_eval_phis_neutral_lookup]
QED

Theorem alias_phi_selected_root_old_value:
  eval_one_phi s inst = SOME (r,v) /\
  s.vs_prev_bb = SOME pred /\
  resolve_phi pred inst.inst_operands = SOME (Var b) /\
  normalize_operand dfg [] (Var b) = Var r /\
  operand_val (frame_view fn ra s) lo (Var b) =
    operand_val (frame_view fn ra s) lo (normalize_operand dfg [] (Var b)) /\
  ~retpc_var fn b /\ ~retpc_var fn r ==>
  FLOOKUP s.vs_vars r = SOME v
Proof
  strip_tac >>
  gvs[operand_val_def, frame_view_non_retpc] >>
  gvs[eval_one_phi_def, AllCaseEqs(), eval_operand_def, lookup_var_def]
QED

Theorem alias_eval_phis_shared_root_frame:
  eval_phis s insts = OK t /\
  (!inst v. MEM inst (TAKE (phi_prefix_length insts) insts) /\
    eval_one_phi s inst = SOME (r,v) ==> FLOOKUP s.vs_vars r = SOME v) /\
  FLOOKUP t.vs_vars x = FLOOKUP s.vs_vars x /\
  normalize_operand dfg [] (Var x) = Var r /\
  operand_val (frame_view fn ra s) lo (Var x) =
    operand_val (frame_view fn ra s) lo (normalize_operand dfg [] (Var x)) /\
  ~retpc_var fn x /\ ~retpc_var fn r ==>
  operand_val (frame_view fn ra t) lo (Var x) =
    operand_val (frame_view fn ra t) lo (normalize_operand dfg [] (Var x))
Proof
  strip_tac >> gvs[operand_val_def, frame_view_non_retpc] >>
  sym_tac >> irule alias_eval_phis_neutral_lookup >>
  goal_assum (drule_at Any) >> simp[]
QED

(* Totalized reads in the occurrence replay layer.  A copy records an
   existing parent; an absent location records the exact operand read by
   the planner, without choosing a value for HOL's unspecified EL. *)
Datatype:
  alias_occ_read_event =
      AliasOccCopy num num
    | AliasOccTotalRead num num operand
End

Definition alias_occ_read_def:
  alias_occ_read i fresh (occs : (operand # num) list) =
    if i < LENGTH occs then
      ((FST (EL i occs), fresh), AliasOccCopy (SND (EL i occs)) fresh)
    else
      ((EL i (MAP FST occs), fresh),
       AliasOccTotalRead i fresh (EL i (MAP FST occs)))
End

Theorem alias_occ_read_erases:
  FST (FST (alias_occ_read i fresh occs)) = EL i (MAP FST occs)
Proof
  Cases_on `i < LENGTH occs` >> simp[alias_occ_read_def, EL_MAP]
QED

Theorem alias_occ_read_identity:
  SND (FST (alias_occ_read i fresh occs)) = fresh
Proof
  simp[alias_occ_read_def] >> IF_CASES_TAC >> simp[]
QED

Theorem alias_occ_read_copy_parent:
  SND (alias_occ_read i fresh occs) = AliasOccCopy parent child ==>
  i < LENGTH occs /\ child = fresh /\
  MEM (EL i occs) occs /\ SND (EL i occs) = parent
Proof
  simp[alias_occ_read_def] >> IF_CASES_TAC >> simp[] >>
  strip_tac >> irule EL_MEM >> simp[]
QED

Theorem alias_occ_read_total_location:
  SND (alias_occ_read i fresh occs) = AliasOccTotalRead j child at ==>
  LENGTH occs <= i /\ j = i /\ child = fresh /\
  at = EL i (MAP FST occs)
Proof
  simp[alias_occ_read_def] >> IF_CASES_TAC >> simp[]
QED

Definition alias_occ_dup_def:
  alias_occ_dup dist fresh (occs : (operand # num) list) =
    (SNOC (FST (alias_occ_read (LENGTH occs - 1 - dist) fresh occs)) occs,
     SUC fresh, SND (alias_occ_read (LENGTH occs - 1 - dist) fresh occs))
End

Theorem alias_occ_dup_erases:
  MAP FST (FST (alias_occ_dup dist fresh occs)) =
  stack_dup dist (MAP FST occs)
Proof
  simp[alias_occ_dup_def, stack_dup_def, stack_peek_def,
    MAP_SNOC, alias_occ_read_erases]
QED

Theorem alias_occ_dup_empty:
  stack_dup dist [] = [EL 0 []] /\
  alias_occ_dup dist fresh [] =
    ([(EL 0 [], fresh)], SUC fresh, AliasOccTotalRead 0 fresh (EL 0 []))
Proof
  simp[stack_dup_def, stack_peek_def, alias_occ_dup_def, alias_occ_read_def]
QED

Theorem alias_occ_dup_no_spontaneous_old:
  MEM occ (FST (alias_occ_dup dist fresh occs)) /\ SND occ < fresh ==>
  MEM occ occs
Proof
  simp[alias_occ_dup_def, MEM_SNOC] >> rpt strip_tac >>
  gvs[alias_occ_read_identity]
QED

Theorem alias_occ_dup_bounded:
  EVERY (\occ. SND occ < fresh) occs ==>
  EVERY (\occ. SND occ < SUC fresh) (FST (alias_occ_dup dist fresh occs))
Proof
  simp[alias_occ_dup_def, EVERY_SNOC, alias_occ_read_identity, EVERY_MEM] >>
  rpt strip_tac >> gvs[alias_occ_read_identity] >>
  first_x_assum drule >> simp[]
QED

Theorem alias_occ_do_dup_erases:
  ps.ps_stack = MAP FST occs ==>
  (SND (do_dup dist ps)).ps_stack =
  MAP FST (FST (alias_occ_dup dist fresh occs))
Proof
  strip_tac >> rewrite_tac[alias_occ_dup_erases] >>
  Cases_on `dist <= 15` >> simp[do_dup_def, LET_THM] >>
  rpt (pairarg_tac >> gvs[]) >> simp[]
QED

(* The shadow records identities, never allocator addresses. *)
Datatype:
  alias_occ_inventory = <|
    alias_occs : (operand # num) list;
    alias_spill_ids : operand |-> num;
    alias_next : num
  |>
End

Definition alias_occ_align_def:
  alias_occ_align inv ps <=>
    MAP FST inv.alias_occs = ps.ps_stack /\
    FDOM inv.alias_spill_ids = FDOM ps.ps_spilled
End

Definition alias_occ_ids_def:
  alias_occ_ids inv =
    MAP SND inv.alias_occs ++ MAP SND (fmap_to_alist inv.alias_spill_ids)
End

Definition alias_occ_wf_def:
  alias_occ_wf inv <=>
    ALL_DISTINCT (alias_occ_ids inv) /\
    EVERY (\id. id < inv.alias_next) (alias_occ_ids inv)
End

Definition alias_occ_residents_def:
  alias_occ_residents inv =
    {occ | MEM occ inv.alias_occs} UNION
    {(at,id) | FLOOKUP inv.alias_spill_ids at = SOME id}
End

Definition alias_occ_deleted_def:
  alias_occ_deleted old new =
    IMAGE SND (alias_occ_residents old) DIFF
    IMAGE SND (alias_occ_residents new)
End

Definition alias_occ_empty_def:
  alias_occ_empty = <| alias_occs := []; alias_spill_ids := FEMPTY;
                       alias_next := 0 |>
End

(* A read log retains its selected list, rather than treating an absent
   selected location as an absent global stack. *)
Datatype:
  alias_occ_read_log = AliasOccReadLog num (operand list) alias_occ_read_event
End

Definition alias_occ_read_log_ok_def:
  (alias_occ_read_log_ok (AliasOccReadLog site source (AliasOccCopy p c)) = T) /\
  (alias_occ_read_log_ok
     (AliasOccReadLog site source (AliasOccTotalRead i c at)) =
     (LENGTH source <= i /\ at = EL i source))
End

Theorem alias_occ_empty_wf:
  alias_occ_wf alias_occ_empty /\
  alias_occ_residents alias_occ_empty = EMPTY
Proof
  simp[alias_occ_wf_def, alias_occ_ids_def, alias_occ_empty_def,
       alias_occ_residents_def, alistTheory.fmap_to_alist_FEMPTY,
       pred_setTheory.EXTENSION]
QED

Theorem alias_occ_empty_align:
  alias_occ_align alias_occ_empty ps <=>
  ps.ps_stack = [] /\ ps.ps_spilled = FEMPTY
Proof
  simp[alias_occ_align_def, alias_occ_empty_def, finite_mapTheory.FDOM_EQ_EMPTY]
QED

Theorem alias_occ_read_log_valid:
  alias_occ_read_log_ok
    (AliasOccReadLog site (MAP FST occs) (SND (alias_occ_read i fresh occs)))
Proof
  simp[alias_occ_read_def] >> IF_CASES_TAC >>
  simp[alias_occ_read_log_ok_def]
QED

Theorem alias_occ_residents_member:
  (at,id) IN alias_occ_residents shadow <=>
  MEM (at,id) shadow.alias_occs \/ FLOOKUP shadow.alias_spill_ids at = SOME id
Proof
  simp[alias_occ_residents_def]
QED

Theorem alias_occ_pop_residents:
  alias_occ_residents (shadow with alias_occs := TL shadow.alias_occs)
    SUBSET alias_occ_residents shadow
Proof
  simp[pred_setTheory.SUBSET_DEF, pairTheory.FORALL_PROD,
       alias_occ_residents_member] >>
  Cases_on `shadow.alias_occs` >> simp[] >> metis_tac[]
QED

Theorem alias_occ_remove_spill_residents:
  (at,id) IN alias_occ_residents
    (shadow with alias_spill_ids := shadow.alias_spill_ids \\ key) <=>
  MEM (at,id) shadow.alias_occs \/
    (at <> key /\ FLOOKUP shadow.alias_spill_ids at = SOME id)
Proof
  simp[alias_occ_residents_member, finite_mapTheory.DOMSUB_FLOOKUP_THM] >>
  metis_tac[]
QED

Theorem alias_occ_replace_spill_residents:
  (at,id) IN alias_occ_residents
    (shadow with alias_spill_ids := shadow.alias_spill_ids |+ (key,fresh)) <=>
  MEM (at,id) shadow.alias_occs \/
    (at = key /\ id = fresh) \/
    (at <> key /\ FLOOKUP shadow.alias_spill_ids at = SOME id)
Proof
  simp[alias_occ_residents_member, finite_mapTheory.FLOOKUP_UPDATE] >>
  Cases_on `at = key` >> simp[] >> metis_tac[]
QED

Definition alias_occ_to_spill_def:
  alias_occ_to_spill shadow =
    case shadow.alias_occs of
      [] => shadow
    | (at,id)::rest =>
        shadow with <| alias_occs := rest;
          alias_spill_ids := shadow.alias_spill_ids |+ (at,id) |>
End

Definition alias_occ_from_spill_def:
  alias_occ_from_spill key shadow =
    case FLOOKUP shadow.alias_spill_ids key of
      NONE => shadow
    | SOME id =>
        shadow with <| alias_occs := SNOC (key,id) shadow.alias_occs;
          alias_spill_ids := shadow.alias_spill_ids \\ key |>
End

Definition alias_occ_insert_def:
  alias_occ_insert at shadow =
    shadow with <| alias_occs := SNOC (at,shadow.alias_next) shadow.alias_occs;
                   alias_next := SUC shadow.alias_next |>
End

Theorem alias_occ_to_spill_residents:
  shadow.alias_occs = (key,moved)::rest ==>
  ((at,id) IN alias_occ_residents (alias_occ_to_spill shadow) <=>
   MEM (at,id) rest \/ (at = key /\ id = moved) \/
   (at <> key /\ FLOOKUP shadow.alias_spill_ids at = SOME id))
Proof
  strip_tac >> simp[alias_occ_to_spill_def, alias_occ_residents_member,
    finite_mapTheory.FLOOKUP_UPDATE] >>
  Cases_on `at = key` >> simp[] >> metis_tac[]
QED

Theorem alias_occ_to_spill_no_new:
  alias_occ_residents (alias_occ_to_spill shadow)
    SUBSET alias_occ_residents shadow
Proof
  Cases_on `shadow.alias_occs` >- simp[alias_occ_to_spill_def] >>
  PairCases_on `h` >>
  simp[pred_setTheory.SUBSET_DEF, pairTheory.FORALL_PROD,
       alias_occ_to_spill_def, alias_occ_residents_member,
       finite_mapTheory.FLOOKUP_UPDATE] >>
  rpt gen_tac >> IF_CASES_TAC >> simp[] >> metis_tac[]
QED

Theorem alias_occ_from_spill_residents:
  alias_occ_residents (alias_occ_from_spill key shadow) =
  alias_occ_residents shadow
Proof
  Cases_on `FLOOKUP shadow.alias_spill_ids key` >>
  simp[alias_occ_from_spill_def, pred_setTheory.EXTENSION,
       pairTheory.FORALL_PROD, alias_occ_residents_member, MEM_SNOC,
       finite_mapTheory.DOMSUB_FLOOKUP_THM] >>
  map_every qx_gen_tac [`at`,`id`] >>
  Cases_on `at = key` >> gvs[] >> metis_tac[]
QED

Theorem alias_occ_insert_residents:
  (at,id) IN alias_occ_residents (alias_occ_insert key shadow) <=>
  (at = key /\ id = shadow.alias_next) \/
  (at,id) IN alias_occ_residents shadow
Proof
  simp[alias_occ_insert_def, alias_occ_residents_member, MEM_SNOC] >>
  metis_tac[]
QED

Theorem alias_occ_insert_wf:
  alias_occ_wf shadow ==> alias_occ_wf (alias_occ_insert at shadow)
Proof
  strip_tac >>
  `~MEM shadow.alias_next (alias_occ_ids shadow)` by
    (strip_tac >> gvs[alias_occ_wf_def, EVERY_MEM] >>
     first_x_assum drule >> simp[]) >>
  gvs[alias_occ_wf_def, alias_occ_ids_def, alias_occ_insert_def,
      MAP_SNOC, ALL_DISTINCT_APPEND, ALL_DISTINCT_SNOC,
      EVERY_APPEND, EVERY_SNOC, EVERY_MEM, MEM_SNOC] >>
  rpt strip_tac >> gvs[] >>
  qpat_x_assum `!id. _ ==> id < _` (qspec_then `id` mp_tac) >> simp[]
QED

(* In this ready fixture the dead a disappears at its own regular ASSIGN
   post-processing, before b is defined, not at the branch, backedge or PHI.
   This finite deletion result does not establish universal root freshness. *)
Theorem lineage_alias_successor:
  !fuel ctx lo liveness dfg cfg ch growth spill_base lbl_ctr fn lbl bb ps h
   promised block_ops ps_after ra vs vs'.
    liveness = liveness_analyze fn /\ dfg = dfg_build_function fn /\
    cfg = cfg_analyze fn /\ codegen_ready_fn fn /\
    retpc_shape_ok fn /\ opaque_use_ok fn /\
    lineage_state liveness dfg cfg fn
      (init_cleanup_plan_state ch growth spill_base lbl_ctr) lbl ps /\
    vs.vs_current_bb = lbl /\
    (!l. FLOOKUP vs.vs_labels l = OPTION_MAP n2w (FLOOKUP lo l)) /\
    lookup_block lbl fn.fn_blocks = SOME bb /\
    generate_block_plan liveness dfg cfg fn bb
      (ps with <| ps_cleanup_height := h; ps_cleanup_promised := promised |>) =
      SOME (block_ops, ps_after) /\
    (!pred x. vs.vs_prev_bb = SOME pred /\
       MEM x (input_vars_from pred bb.bb_instructions
                (live_vars_at liveness lbl 0)) ==>
       MEM (Var x) ps.ps_stack \/ Var x IN FDOM ps.ps_spilled) /\
    (!at. MEM at ps.ps_stack \/ at IN FDOM ps.ps_spilled ==>
       operand_val (frame_view fn ra vs) lo at =
       operand_val (frame_view fn ra vs) lo (normalize_operand dfg [] at)) /\
    run_block fuel ctx bb vs = OK vs' /\ ~vs'.vs_halted
    ==>
    !at. MEM at ps_after.ps_stack \/ at IN FDOM ps_after.ps_spilled ==>
      operand_val (frame_view fn ra vs') lo at =
      operand_val (frame_view fn ra vs') lo (normalize_operand dfg [] at)
Proof
  cheat
QED
