(*
 * SCCP — Correctness proof helpers
 *
 * All intermediate lemmas used by sccpCorrectnessScript.
 * Includes: context infrastructure, dominance invariants,
 * FDOM monotonicity, block-level equality, function-level result_equiv.
 *)

Theory sccpCorrectnessProofs
Ancestors
  sccpProofs sccpProofsBase sccpDefs sccpSound sccpConvergence
  analysisSimDefs analysisSimProps
  venomWf venomExecSemantics venomExecProofs venomInst venomInstProps venomExecProps
  passSharedDefs passSharedProps
  stateEquiv stateEquivProps
  passSimulationDefs passSimulationProps passSimulationProofs
  finite_map venomState list
  cfgAnalysisProps cfgDefs
  dfAnalyzeDefs

Theorem sccp_function_fn_name:
  !f f'. sccp_function f = SOME f' ==> f'.fn_name = f.fn_name
Proof
  rw[sccp_function_def, AllCaseEqs()] >>
  simp[clear_nops_function_def, analysis_function_transform_def,
       function_map_transform_def]
QED

Theorem sccp_ctx_fn:
  !f. (case sccp_function f of NONE => f | SOME f' => f').fn_name = f.fn_name
Proof
  rw[] >> Cases_on `sccp_function f` >> simp[] >>
  metis_tac[sccp_function_fn_name]
QED

Theorem lookup_function_sccp_context:
  !entry fns f.
    lookup_function entry fns = SOME f ==>
    lookup_function entry
      (MAP (\fn. case sccp_function fn of NONE => fn | SOME fn' => fn') fns) =
    SOME (case sccp_function f of NONE => f | SOME f' => f')
Proof
  Induct_on `fns` >> rw[lookup_function_def, FIND_thm] >>
  pop_assum mp_tac >>
  PURE_ONCE_REWRITE_TAC[FIND_thm] >> simp[] >>
  `(case sccp_function h of NONE => h | SOME fn' => fn').fn_name =
   h.fn_name` by metis_tac[sccp_ctx_fn] >>
  Cases_on `h.fn_name = entry` >> simp[] >> rw[] >>
  `(case sccp_function f of NONE => f | SOME fn' => fn').fn_name =
   f.fn_name` by metis_tac[sccp_ctx_fn] >>
  fs[lookup_function_def]
QED

(* state_equiv_empty_eq: now in stateEquivPropsTheory *)

(* ================================================================= *)
(*  Part 2: Dominance / path helpers                                 *)
(* ================================================================= *)

(* Bridge: fn_reachable => in cfg_dfs_pre *)
Theorem fn_cfg_edge_in_dfs_pre:
  !f x y.
    wf_function f /\
    fn_cfg_edge f x y /\
    MEM x (cfg_analyze f).cfg_dfs_pre ==>
    MEM y (cfg_analyze f).cfg_dfs_pre
Proof
  rw[fn_cfg_edge_def] >>
  `MEM y (cfg_succs_of (cfg_analyze f) bb.bb_label)` by (
    irule bb_succs_in_cfg_succs >> fs[wf_function_def] >>
    metis_tac[]) >>
  imp_res_tac cfg_dfs_pre_succs_closed >>
  fs[EVERY_MEM]
QED

Theorem fn_reachable_in_dfs_pre:
  !f lbl.
    wf_function f /\ fn_reachable f lbl ==>
    MEM lbl (cfg_analyze f).cfg_dfs_pre
Proof
  rpt strip_tac >> fs[fn_reachable_def] >>
  `!x y. (fn_cfg_edge f)^* x y ==>
    MEM x (cfg_analyze f).cfg_dfs_pre ==>
    MEM y (cfg_analyze f).cfg_dfs_pre` by (
    ho_match_mp_tac relationTheory.RTC_INDUCT >> rpt strip_tac >>
    metis_tac[fn_cfg_edge_in_dfs_pre]) >>
  metis_tac[entry_label_in_dfs_pre]
QED

(* ================================================================= *)
(*  Part 3: FDOM monotonicity and output tracking                    *)
(* ================================================================= *)

Theorem run_block_fdom_mono:
  !fuel ctx bb s s'.
    run_block fuel ctx bb s = OK s' /\
    bb_well_formed bb /\ EVERY inst_wf bb.bb_instructions ==>
    FDOM s.vs_vars SUBSET FDOM s'.vs_vars
Proof
  rpt gen_tac >> strip_tac >>
  `!n f c st st'.
     n = LENGTH bb.bb_instructions - st.vs_inst_idx /\
     run_block f c bb st = OK st' /\
     bb_well_formed bb /\ EVERY inst_wf bb.bb_instructions ==>
     FDOM st.vs_vars SUBSET FDOM st'.vs_vars`
    suffices_by (
      disch_then (qspecl_then
        [`LENGTH bb.bb_instructions - s.vs_inst_idx`,
         `fuel`, `ctx`, `s`, `s'`] mp_tac) >>
      simp[]) >>
  completeInduct_on `n` >> rw[] >>
  qabbrev_tac `idx = st.vs_inst_idx` >>
  Cases_on `idx >= LENGTH bb.bb_instructions`
  >- (
    qpat_x_assum `run_block _ _ _ _ = _` mp_tac >>
    ONCE_REWRITE_TAC[run_block_def] >>
    simp[get_instruction_def]) >>
  `idx < LENGTH bb.bb_instructions` by fs[] >>
  qpat_x_assum `run_block _ _ _ _ = _` mp_tac >>
  ONCE_REWRITE_TAC[run_block_def] >>
  simp[get_instruction_def] >>
  Cases_on `step_inst f c (EL idx bb.bb_instructions) st` >> gvs[] >>
  Cases_on `is_terminator (EL idx bb.bb_instructions).inst_opcode` >> gvs[]
  >- (
    (* Terminator: lookup_var preserved => FDOM preserved *)
    Cases_on `v.vs_halted` >> gvs[] >>
    simp[pred_setTheory.SUBSET_DEF] >> rpt strip_tac >>
    irule lookup_var_fdom >> qexists_tac `st` >>
    metis_tac[step_terminator_preserves_vars]) >>
  (* Non-terminator: step_inst_fdom gives FDOM grows, then IH *)
  strip_tac >>
  `FDOM v.vs_vars = FDOM st.vs_vars UNION
     set (EL idx bb.bb_instructions).inst_outputs` by (
    `inst_wf (EL idx bb.bb_instructions)` by
      fs[EVERY_EL] >>
    metis_tac[step_inst_fdom]) >>
  `FDOM st.vs_vars SUBSET FDOM v.vs_vars` by
    (simp[] >> simp[pred_setTheory.SUBSET_DEF]) >>
  `FDOM v.vs_vars SUBSET FDOM st'.vs_vars` by (
    first_x_assum (qspec_then `LENGTH bb.bb_instructions - SUC idx` mp_tac) >>
    (impl_tac >- simp[Abbr `idx`]) >>
    disch_then (qspecl_then [`f`, `c`,
      `v with vs_inst_idx := SUC idx`, `st'`] mp_tac) >>
    simp[]) >>
  metis_tac[pred_setTheory.SUBSET_TRANS]
QED

(* After running a block, non-terminator instruction outputs are in FDOM.
   Proof approach: completeInduct_on with rpt strip_tac (NOT rw[]).
   rw[] is too aggressive with arithmetic premises. *)
(* Separate the induction to avoid scoping issues with outer run_block *)
Theorem run_block_output_in_fdom_aux:
  !bb idx v n f c st st'.
    idx < LENGTH bb.bb_instructions /\
    ~is_terminator (EL idx bb.bb_instructions).inst_opcode /\
    MEM v (EL idx bb.bb_instructions).inst_outputs /\
    n = LENGTH bb.bb_instructions - st.vs_inst_idx /\
    run_block f c bb st = OK st' /\
    bb_well_formed bb /\ EVERY inst_wf bb.bb_instructions /\
    st.vs_inst_idx <= idx ==>
    v IN FDOM st'.vs_vars
Proof
  ntac 3 gen_tac >>
  completeInduct_on `n` >> rw[] >>
  qabbrev_tac `k = st.vs_inst_idx` >>
  Cases_on `k >= LENGTH bb.bb_instructions`
  >- fs[Abbr `k`] >>
  `k < LENGTH bb.bb_instructions` by fs[] >>
  qpat_x_assum `run_block _ _ _ _ = _` mp_tac >>
  ONCE_REWRITE_TAC[run_block_def] >>
  simp[get_instruction_def, Abbr `k`] >>
  Cases_on `step_inst f c (EL st.vs_inst_idx bb.bb_instructions) st` >>
  gvs[] >>
  Cases_on `is_terminator (EL st.vs_inst_idx bb.bb_instructions).inst_opcode`
  >> gvs[]
  >- (
    (* terminator case: contradiction *)
    fs[bb_well_formed_def] >>
    `st.vs_inst_idx = PRE (LENGTH bb.bb_instructions)` by
      (first_x_assum irule >> simp[]) >>
    `idx = st.vs_inst_idx` by simp[] >>
    gvs[]
  ) >>
  strip_tac >>
  Cases_on `st.vs_inst_idx = idx`
  >- (
    `inst_wf (EL idx bb.bb_instructions)` by fs[EVERY_EL] >>
    `FDOM v'.vs_vars = FDOM st.vs_vars UNION
       set (EL idx bb.bb_instructions).inst_outputs` by
      metis_tac[step_inst_fdom] >>
    `v IN FDOM v'.vs_vars` by simp[] >>
    `FDOM v'.vs_vars SUBSET FDOM st'.vs_vars` by (
      mp_tac (Q.SPECL [`f`, `c`, `bb`,
        `v' with vs_inst_idx := SUC st.vs_inst_idx`, `st'`]
        run_block_fdom_mono) >>
      simp[]) >>
    metis_tac[pred_setTheory.SUBSET_DEF]
  ) >>
  (* recursive case: st.vs_inst_idx < idx *)
  `st.vs_inst_idx < idx` by simp[] >>
  first_x_assum (qspec_then
    `LENGTH bb.bb_instructions - SUC st.vs_inst_idx` mp_tac) >>
  simp[] >>
  disch_then (qspecl_then [`f`, `c`,
    `v' with vs_inst_idx := SUC st.vs_inst_idx`, `st'`] mp_tac) >>
  simp[]
QED

Theorem run_block_outputs_in_fdom:
  !fuel ctx bb s s' idx v.
    run_block fuel ctx bb s = OK s' /\
    s.vs_inst_idx = 0 /\
    bb_well_formed bb /\
    EVERY inst_wf bb.bb_instructions /\
    idx < LENGTH bb.bb_instructions /\
    ~is_terminator (EL idx bb.bb_instructions).inst_opcode /\
    MEM v (EL idx bb.bb_instructions).inst_outputs ==>
    v IN FDOM s'.vs_vars
Proof
  rpt gen_tac >> strip_tac >>
  irule run_block_output_in_fdom_aux >>
  qexistsl_tac [`bb`, `ctx`, `fuel`, `idx`,
    `LENGTH bb.bb_instructions`, `s`] >>
  simp[]
QED

(* ================================================================= *)
(*  Part 4: The dominance invariant                                  *)
(* ================================================================= *)

Definition strict_dom_vars_defined_def:
  strict_dom_vars_defined f s <=>
    !d_bb d_inst v.
      MEM d_bb f.fn_blocks /\
      MEM d_inst d_bb.bb_instructions /\
      MEM v d_inst.inst_outputs /\
      fn_dominates f d_bb.bb_label s.vs_current_bb /\
      d_bb.bb_label <> s.vs_current_bb ==>
      v IN FDOM s.vs_vars
End

(* At entry: vacuously true because entry has no strict dominator *)
(* At entry: vacuously true because entry has no strict dominator.
   Any path from entry to entry is [entry]; a strict dominator must
   appear on it AND differ from entry — contradiction. *)
Theorem strict_dom_vars_defined_entry:
  !f s.
    fn_entry_label f = SOME s.vs_current_bb ==>
    strict_dom_vars_defined f s
Proof
  rw[strict_dom_vars_defined_def] >> rpt strip_tac >>
  `F` suffices_by simp[] >>
  qpat_x_assum `fn_dominates _ _ _` mp_tac >>
  simp[fn_dominates_def] >> DISJ2_TAC >>
  qmatch_asmsub_abbrev_tac `fn_entry_label _ = SOME lbl` >>
  qexists_tac `[lbl]` >>
  simp[is_fn_path_def, fn_entry_label_def, entry_block_def, Abbr `lbl`]
QED

Theorem strict_dom_vars_defined_preserved:
  !f bb s s' fuel ctx.
    wf_function f /\ ssa_form f /\
    MEM bb f.fn_blocks /\
    bb.bb_label = s.vs_current_bb /\
    run_block fuel ctx bb s = OK s' /\
    s.vs_inst_idx = 0 /\
    ~s'.vs_halted /\
    strict_dom_vars_defined f s /\
    fn_reachable f s.vs_current_bb /\
    bb_well_formed bb /\
    EVERY inst_wf bb.bb_instructions ==>
    strict_dom_vars_defined f s'
Proof
  rw[strict_dom_vars_defined_def] >> rpt strip_tac >>
  Cases_on `d_bb.bb_label = s.vs_current_bb`
  >- (
    (* Case 1: d_bb is the block we just ran *)
    `d_bb.bb_label = bb.bb_label` by simp[] >>
    `d_bb = bb` by metis_tac[same_label_same_block] >>
    gvs[] >>
    (* d_inst is at some index idx *)
    `?idx. idx < LENGTH bb.bb_instructions /\
           EL idx bb.bb_instructions = d_inst` by
      metis_tac[MEM_EL] >>
    (* d_inst has outputs, so it's not a terminator *)
    `~is_terminator d_inst.inst_opcode` by (
      spose_not_then assume_tac >>
      `d_inst.inst_outputs = []` by
        metis_tac[terminator_no_outputs, EVERY_MEM] >>
      fs[]) >>
    irule run_block_outputs_in_fdom >>
    qexistsl_tac [`bb`, `ctx`, `fuel`, `idx`, `s`] >> simp[])
  >- (
    (* Case 2: d_bb is NOT the current block *)
    (* s'.vs_current_bb is a successor of bb *)
    `MEM s'.vs_current_bb (bb_succs bb)` by (
      mp_tac (Q.SPECL [`fuel`, `ctx`, `bb`, `s`, `s'`]
        run_block_current_bb_in_succs) >>
      simp[] >> disch_then irule >>
      fs[bb_well_formed_def] >>
      rpt strip_tac >> spose_not_then assume_tac >>
      res_tac >> fs[]) >>
    (* fn_cfg_edge from bb to s'.vs_current_bb *)
    `fn_cfg_edge f s.vs_current_bb s'.vs_current_bb` by
      (simp[fn_cfg_edge_def] >> metis_tac[]) >>
    (* d_bb dominates s.vs_current_bb (predecessor of s'.vs_current_bb) *)
    `fn_dominates f d_bb.bb_label s.vs_current_bb` by
      metis_tac[fn_dominates_predecessor] >>
    (* strict dominance: d_bb.bb_label <> s.vs_current_bb *)
    `v IN FDOM s.vs_vars` by metis_tac[] >>
    (* FDOM mono *)
    `FDOM s.vs_vars SUBSET FDOM s'.vs_vars` by
      metis_tac[run_block_fdom_mono] >>
    metis_tac[pred_setTheory.SUBSET_DEF])
QED

(* ================================================================= *)
(*  Part 5: Operand vars in FDOM at each instruction                 *)
(* ================================================================= *)

(* Under wf_ssa + wf_function + strict_dom_vars_defined + intra-block
   outputs in FDOM, all Var operands at instruction idx are in FDOM.
   def_dominates_uses gives i < j with EL j = EL idx in same-block case.
   inst_ids_el_eq (from fn_inst_ids_distinct) gives j = idx, hence i < idx. *)
Theorem operand_vars_in_fdom:
  !f bb idx s.
    wf_ssa f /\ wf_function f /\ fn_inst_wf f /\
    MEM bb f.fn_blocks /\
    bb.bb_label = s.vs_current_bb /\
    idx < LENGTH bb.bb_instructions /\
    strict_dom_vars_defined f s /\
    (!j v. j < idx /\ MEM v (EL j bb.bb_instructions).inst_outputs ==>
           v IN FDOM s.vs_vars) ==>
    !v. MEM (Var v) (EL idx bb.bb_instructions).inst_operands ==>
        v IN FDOM s.vs_vars
Proof
  rpt strip_tac >>
  fs[wf_ssa_def] >>
  `MEM (EL idx bb.bb_instructions) bb.bb_instructions` by
    metis_tac[MEM_EL] >>
  fs[def_dominates_uses_def] >>
  first_x_assum (qspecl_then [`bb`, `EL idx bb.bb_instructions`, `v`]
    mp_tac) >>
  simp[] >> strip_tac >>
  Cases_on `def_bb.bb_label = bb.bb_label`
  >- (
    (* Same block: def_bb = bb by label uniqueness *)
    `def_bb = bb` by metis_tac[same_label_same_block] >>
    gvs[] >>
    (* i < j, EL j = EL idx. fn_inst_ids_distinct gives j = idx. *)
    `fn_inst_ids_distinct f` by fs[wf_function_def] >>
    `j = idx` by metis_tac[inst_ids_el_eq] >>
    gvs[] >>
    first_x_assum irule >> simp[] >> metis_tac[])
  >- (
    (* Different block: strict_dom_vars_defined *)
    fs[strict_dom_vars_defined_def] >>
    qpat_x_assum `!d_bb d_inst v. _` (qspecl_then
      [`def_bb`, `def_inst`, `v`] mp_tac) >>
    simp[] >> gvs[])
QED

(* ================================================================= *)
(*  Part 6: Block-level execution equality                           *)
(* ================================================================= *)

(* Different blocks, different ctx, fuel-specific per-step equality *)
Theorem run_block_eq_fuel:
  !n fuel ctx1 ctx2 bb1 bb2 s.
    n = LENGTH bb1.bb_instructions - s.vs_inst_idx /\
    LENGTH bb1.bb_instructions = LENGTH bb2.bb_instructions /\
    bb1.bb_label = bb2.bb_label /\
    (!idx. idx < LENGTH bb1.bb_instructions ==>
      is_terminator (EL idx bb1.bb_instructions).inst_opcode =
      is_terminator (EL idx bb2.bb_instructions).inst_opcode) /\
    (!idx s'.
      idx < LENGTH bb1.bb_instructions /\ s'.vs_inst_idx = idx ==>
      step_inst fuel ctx1 (EL idx bb1.bb_instructions) s' =
      step_inst fuel ctx2 (EL idx bb2.bb_instructions) s') ==>
    run_block fuel ctx1 bb1 s = run_block fuel ctx2 bb2 s
Proof
  Induct >> rpt gen_tac >> strip_tac
  >- (
    `s.vs_inst_idx >= LENGTH bb1.bb_instructions` by simp[] >>
    ONCE_REWRITE_TAC[run_block_def] >>
    simp[get_instruction_def])
  >>
  ONCE_REWRITE_TAC[run_block_def] >>
  `s.vs_inst_idx < LENGTH bb1.bb_instructions` by simp[] >>
  simp[get_instruction_def] >>
  `step_inst fuel ctx1 (EL s.vs_inst_idx bb1.bb_instructions) s =
   step_inst fuel ctx2 (EL s.vs_inst_idx bb2.bb_instructions) s` by
    metis_tac[] >>
  simp[] >>
  Cases_on `step_inst fuel ctx2 (EL s.vs_inst_idx bb2.bb_instructions) s` >>
  simp[] >>
  `is_terminator (EL s.vs_inst_idx bb1.bb_instructions).inst_opcode =
   is_terminator (EL s.vs_inst_idx bb2.bb_instructions).inst_opcode` by
    metis_tac[] >>
  simp[] >>
  Cases_on `is_terminator (EL s.vs_inst_idx bb2.bb_instructions).inst_opcode` >>
  simp[]
QED

(* Same block, different ctx: per-step result_equiv => block result_equiv *)
Theorem run_block_result_equiv_ctx:
  !n fuel ctx1 ctx2 bb s.
    n = LENGTH bb.bb_instructions - s.vs_inst_idx /\
    (!idx s'.
      idx < LENGTH bb.bb_instructions /\ s'.vs_inst_idx = idx ==>
      result_equiv {}
        (step_inst fuel ctx1 (EL idx bb.bb_instructions) s')
        (step_inst fuel ctx2 (EL idx bb.bb_instructions) s')) ==>
    result_equiv {}
      (run_block fuel ctx1 bb s) (run_block fuel ctx2 bb s)
Proof
  Induct >> rpt gen_tac >> strip_tac
  >- (
    `s.vs_inst_idx >= LENGTH bb.bb_instructions` by simp[] >>
    ONCE_REWRITE_TAC[run_block_def] >>
    simp[get_instruction_def, result_equiv_def])
  >>
  ONCE_REWRITE_TAC[run_block_def] >>
  `s.vs_inst_idx < LENGTH bb.bb_instructions` by simp[] >>
  simp[get_instruction_def] >>
  `result_equiv {}
    (step_inst fuel ctx1 (EL s.vs_inst_idx bb.bb_instructions) s)
    (step_inst fuel ctx2 (EL s.vs_inst_idx bb.bb_instructions) s)` by
    metis_tac[] >>
  Cases_on `step_inst fuel ctx1 (EL s.vs_inst_idx bb.bb_instructions) s` >>
  Cases_on `step_inst fuel ctx2 (EL s.vs_inst_idx bb.bb_instructions) s` >>
  gvs[result_equiv_def] >>
  (* Both OK: state_equiv {} => equal states *)
  imp_res_tac state_equiv_empty_eq >> gvs[] >>
  Cases_on `is_terminator (EL s.vs_inst_idx bb.bb_instructions).inst_opcode` >>
  simp[] >>
  Cases_on `v.vs_halted` >>
  simp[result_equiv_def, state_equiv_refl, execution_equiv_refl]
QED

(* ================================================================= *)
(*  Part 7: SCCP-specific step_inst equality                         *)
(* ================================================================= *)

(* For non-INVOKE: step_inst is ctx-independent AND sccp transform
   gives same result when operand vars are in FDOM *)
(* ================================================================= *)
(*  Part 8: SCCP transform structural properties                     *)
(* ================================================================= *)

(* Helper: the sccp-transformed function *)
Definition sccp_fn_def:
  sccp_fn f = case sccp_function f of NONE => f | SOME f' => f'
End

(* The sccp block transform preserves labels *)
Theorem sccp_block_transform_label:
  !f bb. (clear_nops_block (analysis_block_transform sccp_bottom
           (sccp_df_analyze f)
           (\lat inst. [sccp_inst lat.sl_vals inst]) bb)).bb_label =
        bb.bb_label
Proof
  simp[clear_nops_block_def, analysis_block_transform_def]
QED

(* Abbreviation for the per-block transform *)
val sccp_transform_block_def = Define `
  sccp_transform_block f bb =
    clear_nops_block (analysis_block_transform sccp_bottom
      (sccp_df_analyze f)
      (\lat inst. [sccp_inst lat.sl_vals inst]) bb)`;

(* Master structural lemma: sccp_fn blocks *)
Theorem sccp_fn_blocks:
  !f. (sccp_fn f).fn_blocks =
      case sccp_function f of
        NONE => f.fn_blocks
      | SOME _ => MAP (sccp_transform_block f) f.fn_blocks
Proof
  rw[sccp_fn_def] >>
  Cases_on `sccp_function f` >> simp[] >>
  gvs[sccp_function_def, AllCaseEqs(), LET_THM,
      clear_nops_function_def, analysis_function_transform_def,
      function_map_transform_def] >>
  rw[MAP_MAP_o, combinTheory.o_DEF] >>
  irule listTheory.MAP_CONG >> simp[sccp_transform_block_def]
QED

(* sccp_fn preserves fn_name *)
Theorem sccp_fn_fn_name:
  !f. (sccp_fn f).fn_name = f.fn_name
Proof
  rw[sccp_fn_def] >>
  Cases_on `sccp_function f` >> simp[] >>
  metis_tac[sccp_function_fn_name]
QED

(* sccp_fn preserves entry label *)
Theorem sccp_fn_entry_label:
  !f. fn_entry_label (sccp_fn f) = fn_entry_label f
Proof
  rw[sccp_fn_def] >>
  Cases_on `sccp_function f` >> simp[] >>
  gvs[sccp_function_def, AllCaseEqs(), LET_THM] >>
  simp[fn_entry_label_def, entry_block_def,
       clear_nops_function_def, analysis_function_transform_def,
       function_map_transform_def, NULL_MAP] >>
  Cases_on `f.fn_blocks` >> gvs[] >>
  simp[clear_nops_block_def, analysis_block_transform_def]
QED

(* sccp_fn preserves block non-emptiness *)
Theorem sccp_fn_blocks_nonempty:
  !f. ~NULL f.fn_blocks ==> ~NULL (sccp_fn f).fn_blocks
Proof
  rw[sccp_fn_blocks] >>
  Cases_on `sccp_function f` >> simp[NULL_MAP]
QED

(* setup_callee preserved under sccp_fn *)
Theorem setup_callee_sccp_fn:
  !f args s.
    ~NULL f.fn_blocks ==>
    setup_callee (sccp_fn f) args s = setup_callee f args s
Proof
  rw[sccp_fn_def] >>
  Cases_on `sccp_function f` >> simp[] >>
  gvs[setup_callee_def, sccp_function_def, AllCaseEqs(), LET_THM] >>
  simp[clear_nops_function_def, analysis_function_transform_def,
       function_map_transform_def, NULL_MAP] >>
  Cases_on `f.fn_blocks` >> gvs[] >>
  simp[clear_nops_block_def, analysis_block_transform_def]
QED

(* lookup_block NONE correspondence for sccp_fn *)
Theorem lookup_block_sccp_fn_none:
  !lbl f.
    lookup_block lbl f.fn_blocks = NONE ==>
    lookup_block lbl (sccp_fn f).fn_blocks = NONE
Proof
  rpt strip_tac >> simp[sccp_fn_blocks] >>
  Cases_on `sccp_function f` >> simp[] >>
  simp[lookup_block_map, sccp_transform_block_def, sccp_block_transform_label]
QED

(* lookup_block SOME correspondence for sccp_fn — gives exact transform *)
Theorem lookup_block_sccp_fn_some:
  !lbl f bb.
    lookup_block lbl f.fn_blocks = SOME bb ==>
    lookup_block lbl (sccp_fn f).fn_blocks =
      SOME (case sccp_function f of
              NONE => bb
            | SOME _ => sccp_transform_block f bb)
Proof
  rpt strip_tac >>
  simp[sccp_fn_blocks] >>
  Cases_on `sccp_function f` >> simp[] >>
  `!bb. (sccp_transform_block f bb).bb_label = bb.bb_label` by
    simp[sccp_transform_block_def, clear_nops_block_def,
         analysis_block_transform_def] >>
  simp[lookup_block_map]
QED

(* ================================================================= *)
(*  Part 9: Main fuel induction — full execution equality            *)
(* =================================================================  *)

(* FIND NONE on MAP when predicate preserved *)
Theorem FIND_NONE_MAP:
  !P f l.
    (!x. P (f x) = P x) ==>
    (FIND P (MAP f l) = NONE <=> FIND P l = NONE)
Proof
  gen_tac >> gen_tac >> Induct >> simp[FIND_thm]
QED

(* lookup_function NONE preserved by MAP sccp_fn *)
Theorem lookup_function_none_sccp_context:
  !name ctx.
    lookup_function name ctx.ctx_functions = NONE ==>
    lookup_function name (sccp_context ctx).ctx_functions = NONE
Proof
  simp[lookup_function_def, sccp_context_def, sccp_fn_def] >>
  rpt strip_tac >>
  qspecl_then [`\f. f.fn_name = name`,
    `\fn. case sccp_function fn of NONE => fn | SOME fn' => fn'`,
    `ctx.ctx_functions`] mp_tac FIND_NONE_MAP >>
  simp[sccp_ctx_fn]
QED

(* Step 1: INVOKE step_inst gives result_equiv for ctx change *)
Theorem step_inst_invoke_result_equiv:
  !fuel ctx inst s.
    inst.inst_opcode = INVOKE /\
    (!f callee_s.
      MEM f ctx.ctx_functions /\
      callee_s.vs_inst_idx = 0 /\
      FDOM callee_s.vs_vars = {} /\
      fn_entry_label f = SOME callee_s.vs_current_bb ==>
      result_equiv {}
        (run_function fuel ctx f callee_s)
        (run_function fuel (sccp_context ctx) (sccp_fn f) callee_s)) ==>
    result_equiv {}
      (step_inst fuel ctx inst s)
      (step_inst fuel (sccp_context ctx) inst s)
Proof
  rpt strip_tac >>
  ONCE_REWRITE_TAC[step_inst_def] >> simp[] >>
  Cases_on `decode_invoke inst` >> simp[result_equiv_def] >>
  rename1 `SOME cn_args` >> Cases_on `cn_args` >>
  rename1 `SOME (callee_name, arg_ops)` >>
  Cases_on `lookup_function callee_name ctx.ctx_functions`
  >- (
    imp_res_tac lookup_function_none_sccp_context >>
    simp[result_equiv_def])
  >>
  rename1 `_ = SOME f_callee` >>
  `lookup_function callee_name (sccp_context ctx).ctx_functions =
   SOME (sccp_fn f_callee)` by (
    simp[sccp_context_def, sccp_fn_def] >>
    metis_tac[lookup_function_sccp_context]) >>
  simp[] >>
  Cases_on `eval_operands arg_ops s` >> simp[result_equiv_def] >>
  rename1 `_ = SOME args` >>
  `MEM f_callee ctx.ctx_functions` by metis_tac[lookup_function_MEM] >>
  Cases_on `NULL f_callee.fn_blocks`
  >- (
    (* NULL fn_blocks => setup_callee = NONE on both sides *)
    simp[setup_callee_def, result_equiv_def] >>
    `NULL (sccp_fn f_callee).fn_blocks` by (
      simp[sccp_fn_def] >> Cases_on `sccp_function f_callee` >> simp[] >>
      gvs[sccp_function_def, AllCaseEqs(), LET_THM,
          clear_nops_function_def, analysis_function_transform_def,
          function_map_transform_def, NULL_EQ]) >>
    simp[setup_callee_def, result_equiv_def])
  >>
  `setup_callee (sccp_fn f_callee) args s =
   setup_callee f_callee args s` by
    metis_tac[setup_callee_sccp_fn] >>
  simp[] >>
  Cases_on `setup_callee f_callee args s` >> simp[result_equiv_def] >>
  rename1 `_ = SOME callee_s` >>
  `callee_s.vs_inst_idx = 0 /\
   FDOM callee_s.vs_vars = {} /\
   fn_entry_label f_callee = SOME callee_s.vs_current_bb` by (
    qpat_x_assum `setup_callee _ _ _ = SOME _` mp_tac >>
    simp[setup_callee_def] >> strip_tac >> gvs[] >>
    simp[fn_entry_label_def, entry_block_def]) >>
  `result_equiv {}
    (run_function fuel ctx f_callee callee_s)
    (run_function fuel (sccp_context ctx) (sccp_fn f_callee) callee_s)` by
    metis_tac[] >>
  Cases_on `run_function fuel ctx f_callee callee_s` >>
  Cases_on `run_function fuel (sccp_context ctx) (sccp_fn f_callee) callee_s` >>
  gvs[result_equiv_def] >>
  TRY (imp_res_tac state_equiv_empty_eq >> gvs[] >>
       simp[result_equiv_def, state_equiv_refl, execution_equiv_refl] >>
       NO_TAC) >>
  (* IntRet case: execution_equiv {} => merge_callee_state equal *)
  `merge_callee_state s v = merge_callee_state s v'` by (
    fs[execution_equiv_def, merge_callee_state_def,
       venom_state_component_equality]) >>
  gvs[] >>
  Cases_on `bind_outputs inst.inst_outputs l (merge_callee_state s v')` >>
  simp[result_equiv_def, state_equiv_refl, execution_equiv_refl]
QED

(* Step 2: Block-level ctx change via run_block_result_equiv_ctx *)
(* Non-INVOKE: step_inst_ctx_irrel gives equality => result_equiv
   INVOKE: step_inst_invoke_result_equiv gives result_equiv *)
Theorem run_block_ctx_change:
  !fuel ctx bb s.
    (!f callee_s.
      MEM f ctx.ctx_functions /\
      callee_s.vs_inst_idx = 0 /\
      FDOM callee_s.vs_vars = {} /\
      fn_entry_label f = SOME callee_s.vs_current_bb ==>
      result_equiv {}
        (run_function fuel ctx f callee_s)
        (run_function fuel (sccp_context ctx) (sccp_fn f) callee_s)) ==>
    result_equiv {}
      (run_block fuel ctx bb s) (run_block fuel (sccp_context ctx) bb s)
Proof
  rpt strip_tac >>
  `!idx s'. idx < LENGTH bb.bb_instructions /\ s'.vs_inst_idx = idx ==>
    result_equiv {}
      (step_inst fuel ctx (EL idx bb.bb_instructions) s')
      (step_inst fuel (sccp_context ctx) (EL idx bb.bb_instructions) s')` by (
    rpt strip_tac >>
    Cases_on `(EL idx bb.bb_instructions).inst_opcode = INVOKE`
    >- (
      mp_tac (Q.SPECL [`fuel`, `ctx`,
        `EL idx bb.bb_instructions`, `s'`]
        step_inst_invoke_result_equiv) >>
      simp[])
    >- (
      `step_inst fuel ctx (EL idx bb.bb_instructions) s' =
       step_inst fuel (sccp_context ctx) (EL idx bb.bb_instructions) s'` by
        metis_tac[step_inst_ctx_irrel] >>
      simp[] >>
      Cases_on `step_inst fuel (sccp_context ctx) (EL idx bb.bb_instructions) s'` >>
      simp[result_equiv_def, state_equiv_refl, execution_equiv_refl])) >>
  mp_tac (Q.SPECL [`LENGTH bb.bb_instructions - s.vs_inst_idx`,
    `fuel`, `ctx`, `sccp_context ctx`, `bb`, `s`]
    run_block_result_equiv_ctx) >>
  simp[]
QED

(* ================================================================= *)
(*  Part 9b: Block-level exact equality for SCCP substitution        *)
(* ================================================================= *)

Theorem sccp_inst_is_terminator:
  !st inst. is_terminator (sccp_inst st inst).inst_opcode =
            is_terminator inst.inst_opcode
Proof
  rpt gen_tac >> simp[sccp_inst_def, LET_THM] >>
  IF_CASES_TAC >> simp[] >>
  BasicProvers.every_case_tac >> simp[] >>
  gvs[is_terminator_def, mk_nop_inst_def]
QED

(* non_terminator_not_last: now in venomExecPropsTheory *)

(* Helper: derive cond_const_sound from nophi conditions + phi_bottom tracker
   when the current instruction is non-PHI. Since PHIs form a prefix
   (bb_well_formed), all PHI positions are < idx, so the tracker covers them. *)
Theorem nophi_derive_cond_const_sound:
  !f bb idx lat s.
    bb_well_formed bb /\
    lookup_block bb.bb_label f.fn_blocks = SOME bb /\
    idx < LENGTH bb.bb_instructions /\
    (EL idx bb.bb_instructions).inst_opcode <> PHI /\
    (!x c. FLOOKUP lat x = SOME (CL_Const c) /\
           x IN FDOM s.vs_vars /\
           ~is_phi_output_of_block f.fn_blocks bb.bb_label x ==>
           FLOOKUP s.vs_vars x = SOME c) /\
    (!k y. k < idx /\
           (EL k bb.bb_instructions).inst_opcode = PHI /\
           MEM y (EL k bb.bb_instructions).inst_outputs ==>
           FLOOKUP lat y = SOME CL_Bottom) ==>
    cond_const_sound lat s
Proof
  rpt strip_tac >>
  simp[cond_const_sound_def] >> rpt strip_tac >>
  Cases_on `is_phi_output_of_block f.fn_blocks bb.bb_label x`
  >- (
    (* x is a phi output of this block ⇒ CL_Bottom, contradicting CL_Const *)
    pop_assum mp_tac >> simp[is_phi_output_of_block_def] >> strip_tac >>
    `?n'. n' < LENGTH bb.bb_instructions /\
          EL n' bb.bb_instructions = inst` by metis_tac[MEM_EL] >>
    `n' < idx` by metis_tac[phi_before_non_phi] >>
    `FLOOKUP lat x = SOME CL_Bottom` by metis_tac[] >>
    fs[])
  >- metis_tac[]
QED

(* Step equality: sccp_inst preserves step_inst behavior under nophi conditions *)
Theorem sccp_step_eq_nophi:
  !fuel ctx f bb s.
    bb_well_formed bb /\
    lookup_block bb.bb_label f.fn_blocks = SOME bb /\
    s.vs_inst_idx < LENGTH bb.bb_instructions /\
    inst_wf (EL s.vs_inst_idx bb.bb_instructions) /\
    (!v. MEM (Var v) (EL s.vs_inst_idx bb.bb_instructions).inst_operands ==>
         v IN FDOM s.vs_vars) /\
    (!x c. FLOOKUP (df_at sccp_bottom (sccp_df_analyze f)
              bb.bb_label s.vs_inst_idx).sl_vals x
              = SOME (CL_Const c) /\
           x IN FDOM s.vs_vars /\
           ~is_phi_output_of_block f.fn_blocks bb.bb_label x ==>
           FLOOKUP s.vs_vars x = SOME c) /\
    (!k y. k < s.vs_inst_idx /\
           (EL k bb.bb_instructions).inst_opcode = PHI /\
           MEM y (EL k bb.bb_instructions).inst_outputs ==>
           FLOOKUP (df_at sccp_bottom (sccp_df_analyze f)
              bb.bb_label s.vs_inst_idx).sl_vals y = SOME CL_Bottom) ==>
    step_inst fuel ctx
      (sccp_inst (df_at sccp_bottom (sccp_df_analyze f)
         bb.bb_label s.vs_inst_idx).sl_vals
         (EL s.vs_inst_idx bb.bb_instructions)) s =
    step_inst fuel ctx (EL s.vs_inst_idx bb.bb_instructions) s
Proof
  rpt strip_tac >>
  Cases_on `(EL s.vs_inst_idx bb.bb_instructions).inst_opcode = PHI`
  >- simp[sccp_inst_def]
  >- (
    irule sccp_inst_step_correct_cond >> simp[] >>
    irule nophi_derive_cond_const_sound >>
    qexistsl_tac [`bb`, `f`, `s.vs_inst_idx`] >> simp[] >>
    metis_tac[])
QED

(* Under sound lattice + wf_ssa, sccp_inst_step_correct_cond gives exact
   equality at each instruction. This propagates to block-level equality
   between the original block and the analysis_block_transform block.
   Key advantage over sccp_per_block_sim_nophi: no Error∨ escape.

   Uses nophi-style hypotheses (not cond_const_sound) so it can be called
   from idx=0 where cond_const_sound may not hold for phi outputs.
   At non-PHI instructions, cond_const_sound is derived via
   nophi_phi_bottom_imp_cond (since all preceding PHIs have CL_Bottom
   by the phi_bottom tracker and bb_well_formed ensures PHIs are a prefix). *)
Theorem sccp_run_block_eq:
  !n fuel ctx f bb s.
    n = LENGTH bb.bb_instructions - s.vs_inst_idx /\
    wf_function f /\ wf_ssa f /\ fn_inst_wf f /\
    MEM bb f.fn_blocks /\ bb.bb_label = s.vs_current_bb /\
    MEM bb.bb_label (cfg_analyze f).cfg_dfs_pre /\
    strict_dom_vars_defined f s /\
    s.vs_inst_idx < LENGTH bb.bb_instructions /\
    (* nophi_sound at current idx *)
    (!x c. FLOOKUP (df_at sccp_bottom (sccp_df_analyze f)
              bb.bb_label s.vs_inst_idx).sl_vals x
              = SOME (CL_Const c) /\
           x IN FDOM s.vs_vars /\
           ~is_phi_output_of_block f.fn_blocks bb.bb_label x ==>
           FLOOKUP s.vs_vars x = SOME c) /\
    (* phi_bottom tracker *)
    (!k y. k < s.vs_inst_idx /\
           (EL k bb.bb_instructions).inst_opcode = PHI /\
           MEM y (EL k bb.bb_instructions).inst_outputs ==>
           FLOOKUP (df_at sccp_bottom (sccp_df_analyze f)
              bb.bb_label s.vs_inst_idx).sl_vals y = SOME CL_Bottom) /\
    (* FDOM tracker *)
    (!j v. j < s.vs_inst_idx /\
           MEM v (EL j bb.bb_instructions).inst_outputs ==>
           v IN FDOM s.vs_vars) /\
    lookup_block bb.bb_label f.fn_blocks = SOME bb ==>
    run_block fuel ctx bb s =
    run_block fuel ctx
      (analysis_block_transform sccp_bottom (sccp_df_analyze f)
        (\lat inst. [sccp_inst lat.sl_vals inst]) bb) s
Proof
  Induct >> rpt gen_tac >> strip_tac
  >- (
    (* n = 0: inst_idx >= LENGTH — contradiction *)
    `s.vs_inst_idx >= LENGTH bb.bb_instructions` by simp[] >> fs[])
  >>
  qabbrev_tac `abt_bb = analysis_block_transform sccp_bottom
    (sccp_df_analyze f) (\lat inst. [sccp_inst lat.sl_vals inst]) bb` >>
  `bb_well_formed bb` by
    (drule_all wf_function_bb_well_formed >> simp[]) >>
  `inst_wf (EL s.vs_inst_idx bb.bb_instructions)` by
    (fs[fn_inst_wf_def] >> metis_tac[MEM_EL]) >>
  `!v. MEM (Var v) (EL s.vs_inst_idx bb.bb_instructions).inst_operands ==>
       v IN FDOM s.vs_vars` by (
    mp_tac (Q.SPECL [`f`, `bb`, `s.vs_inst_idx`, `s`] operand_vars_in_fdom) >>
    simp[] >> metis_tac[]) >>
  `LENGTH abt_bb.bb_instructions = LENGTH bb.bb_instructions` by
    simp[Abbr `abt_bb`, sccp_bt_length] >>
  `abt_bb.bb_label = bb.bb_label` by
    simp[Abbr `abt_bb`, analysis_block_transform_def] >>
  (* Step equality: sccp_inst produces same step_inst result.
     For PHI: sccp_inst is identity.
     For non-PHI: derive cond_const_sound via nophi_phi_bottom_imp_cond. *)
  `step_inst fuel ctx
     (sccp_inst (df_at sccp_bottom (sccp_df_analyze f)
        bb.bb_label s.vs_inst_idx).sl_vals
        (EL s.vs_inst_idx bb.bb_instructions)) s =
   step_inst fuel ctx (EL s.vs_inst_idx bb.bb_instructions) s` by
    metis_tac[sccp_step_eq_nophi] >>
  `is_terminator
     (sccp_inst (df_at sccp_bottom (sccp_df_analyze f)
        bb.bb_label s.vs_inst_idx).sl_vals
        (EL s.vs_inst_idx bb.bb_instructions)).inst_opcode =
   is_terminator (EL s.vs_inst_idx bb.bb_instructions).inst_opcode` by
    simp[sccp_inst_is_terminator] >>
  (* Unfold run_block on both sides.
     Remove bb.bb_label = s.vs_current_bb to prevent simp from rewriting
     bb.bb_label -> s.vs_current_bb in the expanded abt_bb term. *)
  qpat_x_assum `bb.bb_label = s.vs_current_bb` (fn lbl_eq =>
    ONCE_REWRITE_TAC[run_block_def] >>
    simp[get_instruction_def, Abbr `abt_bb`, sccp_bt_el, sccp_bt_length] >>
    assume_tac lbl_eq) >>
  Cases_on `step_inst fuel ctx (EL s.vs_inst_idx bb.bb_instructions) s` >>
  simp[]
  >- (
    (* OK case *)
    Cases_on `is_terminator (EL s.vs_inst_idx bb.bb_instructions).inst_opcode`
    >- simp[]
    >- (
      simp[] >>
      `v.vs_current_bb = s.vs_current_bb` by
        metis_tac[step_preserves_control_flow] >>
      `SUC s.vs_inst_idx < LENGTH bb.bb_instructions` by (
        irule non_terminator_not_last >> simp[]) >>
      (* Establish common facts for IH application *)
      `FDOM v.vs_vars = FDOM s.vs_vars UNION
         set (EL s.vs_inst_idx bb.bb_instructions).inst_outputs` by
        metis_tac[step_inst_fdom] >>
      `df_at sccp_bottom (sccp_df_analyze f) bb.bb_label
         (SUC s.vs_inst_idx) =
       sccp_transfer_inst f (EL s.vs_inst_idx bb.bb_instructions)
         (df_at sccp_bottom (sccp_df_analyze f) bb.bb_label
            s.vs_inst_idx)` by (
        irule sccp_intra_fwd >> simp[]) >>
      first_x_assum irule >> simp[] >>
      rpt conj_tac
      >- suspend "nophi"
      >- suspend "phibot"
      >- suspend "fdom"
      >- suspend "sdom"))
QED

Resume sccp_run_block_eq[nophi]:
  (* nophi_sound at SUC idx.
     Rewrite s.vs_current_bb -> bb.bb_label first *)
  qpat_x_assum `bb.bb_label = s.vs_current_bb` (fn eq =>
    PURE_REWRITE_TAC[GSYM eq] >> assume_tac eq) >>
  (* Strip universals but keep antecedent as single assumption *)
  rpt gen_tac >> DISCH_TAC >>
  (* Extract FLOOKUP from df_at (SUC idx) = transfer ... *)
  `FLOOKUP (sccp_transfer_inst f (EL s.vs_inst_idx bb.bb_instructions)
      (df_at sccp_bottom (sccp_df_analyze f) bb.bb_label s.vs_inst_idx)).sl_vals
      x = SOME (CL_Const c)` by (fs[] >> metis_tac[]) >>
  Cases_on `MEM x (EL s.vs_inst_idx bb.bb_instructions).inst_outputs`
  >- suspend "nophi_mem"
  >- (
    (* x is NOT an output: lattice and state preserved for non-outputs *)
    `FLOOKUP (df_at sccp_bottom (sccp_df_analyze f)
        bb.bb_label s.vs_inst_idx).sl_vals x
       = SOME (CL_Const c)` by
      metis_tac[sccp_transfer_non_output_flookup] >>
    `x IN FDOM s.vs_vars` by (fs[] >> metis_tac[]) >>
    `lookup_var x v = lookup_var x s` by
      (irule step_preserves_non_output_vars >> metis_tac[]) >>
    `FLOOKUP s.vs_vars x = SOME c` by metis_tac[] >>
    fs[lookup_var_def])
QED

Resume sccp_run_block_eq[phibot]:
  (* phi_bottom tracker at SUC s.vs_inst_idx *)
  rpt strip_tac >>
  qpat_x_assum `bb.bb_label = s.vs_current_bb` (fn eq =>
    PURE_REWRITE_TAC[GSYM eq] >> assume_tac eq) >>
  qpat_x_assum `df_at _ _ _ (SUC _) = _` (fn eq =>
    PURE_REWRITE_TAC[eq]) >>
  Cases_on `k = s.vs_inst_idx`
  >- (
    (* k = idx: current instruction is PHI, transfer maps outputs to CL_Bottom *)
    gvs[] >>
    simp[sccp_transfer_inst_def] >>
    imp_res_tac (cj 1 foldl_fupdate_bottom) >> simp[])
  >- (
    (* k < idx: preserved from previous *)
    `k < s.vs_inst_idx` by simp[] >>
    `FLOOKUP (df_at sccp_bottom (sccp_df_analyze f)
        bb.bb_label s.vs_inst_idx).sl_vals y
       = SOME CL_Bottom` by metis_tac[] >>
    `ssa_form f` by fs[wf_ssa_def] >>
    `~MEM y (EL s.vs_inst_idx bb.bb_instructions).inst_outputs` by (
      `k < LENGTH bb.bb_instructions` by simp[] >>
      metis_tac[ssa_no_output_overlap_inst]) >>
    metis_tac[sccp_transfer_non_output_flookup])
QED

Resume sccp_run_block_eq[fdom]:
  (* FDOM tracker *)
  rpt strip_tac >>
  Cases_on `j < s.vs_inst_idx`
  >- metis_tac[]
  >- (`j = s.vs_inst_idx` by simp[] >> gvs[])
QED

Resume sccp_run_block_eq[sdom]:
  (* strict_dom_vars_defined preserved *)
  fs[strict_dom_vars_defined_def] >>
  rpt strip_tac >>
  fs[pred_setTheory.IN_UNION] >> res_tac >> simp[]
QED

Resume sccp_run_block_eq[nophi_mem]:
  (* x IS an output of the current instruction.
     Case split: PHI gives contradiction, non-PHI uses cond_const_sound *)
  Cases_on `(EL s.vs_inst_idx bb.bb_instructions).inst_opcode = PHI`
  >- (
    (* PHI + MEM x outputs: transfer maps all outputs to CL_Bottom.
       This contradicts FLOOKUP = SOME (CL_Const c). *)
    qpat_x_assum `FLOOKUP (sccp_transfer_inst _ _ _).sl_vals _ = SOME (CL_Const _)`
      mp_tac >>
    simp[sccp_transfer_inst_def] >>
    imp_res_tac (cj 1 foldl_fupdate_bottom) >>
    simp[])
  >- (
    (* non-PHI + MEM x outputs: use cond_const_sound + transfer_sound *)
    `cond_const_sound
       (df_at sccp_bottom (sccp_df_analyze f)
          bb.bb_label s.vs_inst_idx).sl_vals s` by (
      irule nophi_derive_cond_const_sound >>
      qexistsl_tac [`bb`, `f`, `s.vs_inst_idx`] >>
      simp[] >> metis_tac[]) >>
    `cond_const_sound
       (sccp_transfer_inst f (EL s.vs_inst_idx bb.bb_instructions)
          (df_at sccp_bottom (sccp_df_analyze f)
             bb.bb_label s.vs_inst_idx)).sl_vals v` by (
      irule (SIMP_RULE (srw_ss()) [transfer_sound_wf_def]
        (SPEC ``f:ir_function`` sccp_transfer_sound_cond)) >>
      metis_tac[]) >>
    fs[cond_const_sound_def])
QED

Finalise sccp_run_block_eq;

(* Handle the case when inst_idx = 0 and block may be empty *)
Theorem sccp_run_block_eq_entry:
  !fuel ctx f bb s.
    wf_function f /\ wf_ssa f /\ fn_inst_wf f /\
    MEM bb f.fn_blocks /\ bb.bb_label = s.vs_current_bb /\
    MEM bb.bb_label (cfg_analyze f).cfg_dfs_pre /\
    strict_dom_vars_defined f s /\ s.vs_inst_idx = 0 /\
    nophi_inv f s /\
    lookup_block bb.bb_label f.fn_blocks = SOME bb ==>
    run_block fuel ctx bb s =
    run_block fuel ctx
      (analysis_block_transform sccp_bottom (sccp_df_analyze f)
        (\lat inst. [sccp_inst lat.sl_vals inst]) bb) s
Proof
  rpt strip_tac >>
  Cases_on `bb.bb_instructions`
  >- (
    (* Empty block — both sides behave the same *)
    ONCE_REWRITE_TAC[run_block_def] >>
    simp[get_instruction_def, analysis_block_transform_def])
  >>
  (* Non-empty block *)
  `0 < LENGTH bb.bb_instructions` by simp[] >>
  irule sccp_run_block_eq >> simp[] >>
  fs[nophi_inv_def]
QED

(* ================================================================= *)
(*  Part 10: Function-level result_equiv                             *)
(* ================================================================= *)

(* Entry state satisfies nophi_inv, strict_dom_vars_defined, fn_reachable *)
(* FDOM = {} needed for nophi_inv (vacuous universals over vs_vars).
   Always true for callees (setup_callee sets vs_vars := FEMPTY). *)
Theorem callee_entry_preconditions:
  !f s.
    wf_function f /\ wf_ssa f /\
    fn_entry_label f = SOME s.vs_current_bb /\
    FDOM s.vs_vars = {} /\
    s.vs_inst_idx = 0 ==>
    nophi_inv f s /\ strict_dom_vars_defined f s /\
    fn_reachable f s.vs_current_bb
Proof
  rpt gen_tac >> strip_tac >>
  `fn_reachable f s.vs_current_bb` by
    (simp[fn_reachable_def] >> qexists_tac `s.vs_current_bb` >> simp[]) >>
  rpt conj_tac
  >- (simp[nophi_inv_def] >>
      irule fn_reachable_in_dfs_pre >> simp[])
  >- (irule strict_dom_vars_defined_entry >> simp[])
  >- simp[]
QED

(* fn_reachable is preserved by stepping to a successor block *)
(* Block result_equiv for the SOME case of sccp_function *)
Theorem sccp_block_result_equiv_some:
  !fuel ctx f bb s.
    MEM bb f.fn_blocks /\
    bb.bb_label = s.vs_current_bb /\
    s.vs_inst_idx = 0 /\
    MEM bb.bb_label (cfg_analyze f).cfg_dfs_pre /\
    wf_function f /\ wf_ssa f /\ fn_inst_wf f /\
    bb_well_formed bb /\ EVERY inst_wf bb.bb_instructions /\
    nophi_inv f s /\ strict_dom_vars_defined f s /\
    sccp_function f <> NONE /\
    (!f' callee_s.
      MEM f' ctx.ctx_functions /\
      callee_s.vs_inst_idx = 0 /\
      FDOM callee_s.vs_vars = {} /\
      fn_entry_label f' = SOME callee_s.vs_current_bb ==>
      result_equiv {}
        (run_function fuel ctx f' callee_s)
        (run_function fuel (sccp_context ctx) (sccp_fn f') callee_s)) ==>
    result_equiv {}
      (run_block fuel ctx bb s)
      (run_block fuel (sccp_context ctx)
        (sccp_transform_block f bb) s)
Proof
  rpt strip_tac >>
  `lookup_block bb.bb_label f.fn_blocks = SOME bb` by
    (irule MEM_lookup_block >> fs[wf_function_def, fn_labels_def]) >>
  qabbrev_tac `abt_bb = analysis_block_transform sccp_bottom
    (sccp_df_analyze f) (\lat inst. [sccp_inst lat.sl_vals inst]) bb` >>
  (* Phase 1: exact equality *)
  `run_block fuel ctx bb s = run_block fuel ctx abt_bb s` by (
    qunabbrev_tac `abt_bb` >>
    irule sccp_run_block_eq_entry >> simp[]) >>
  (* Phase 1.5: clear_nops gives result_equiv *)
  `result_equiv {} (run_block fuel ctx abt_bb s)
    (run_block fuel ctx (sccp_transform_block f bb) s)` by (
    `sccp_transform_block f bb = clear_nops_block abt_bb` by
      simp[Abbr `abt_bb`, sccp_transform_block_def] >>
    simp[] >> irule clear_nops_block_correct >> simp[]) >>
  (* Phase 2: ctx change gives result_equiv *)
  `result_equiv {} (run_block fuel ctx (sccp_transform_block f bb) s)
    (run_block fuel (sccp_context ctx) (sccp_transform_block f bb) s)` by (
    irule run_block_ctx_change >>
    first_x_assum ACCEPT_TAC) >>
  (* Compose *)
  metis_tac[result_equiv_trans]
QED

(* Main theorem: result_equiv {} at every fuel, unconditionally.
   Key improvement: no Error∨ escape, enabling direct pass_correct. *)
Theorem sccp_run_function_equiv:
  !fuel ctx.
    venom_wf ctx /\
    (!f. MEM f ctx.ctx_functions ==> wf_ssa f) ==>
    !f s.
      MEM f ctx.ctx_functions /\
      s.vs_inst_idx = 0 /\
      nophi_inv f s /\
      strict_dom_vars_defined f s /\
      fn_reachable f s.vs_current_bb ==>
      result_equiv {}
        (run_function fuel ctx f s)
        (run_function fuel (sccp_context ctx) (sccp_fn f) s)
Proof
  Induct >> rpt gen_tac >> strip_tac >> rpt gen_tac >> strip_tac
  >- (
    (* Base: fuel = 0 — both return Error "out of fuel" *)
    ONCE_REWRITE_TAC[run_function_def] >> simp[result_equiv_def])
  >>
  (* Inductive step *)
  ONCE_REWRITE_TAC[run_function_def] >> simp[] >>
  Cases_on `lookup_block s.vs_current_bb f.fn_blocks`
  >- (
    (* NONE — both return Error "block not found" *)
    `lookup_block s.vs_current_bb (sccp_fn f).fn_blocks = NONE` by
      metis_tac[lookup_block_sccp_fn_none] >>
    simp[result_equiv_def])
  >>
  rename1 `_ = SOME bb` >>
  `MEM bb f.fn_blocks` by metis_tac[lookup_block_MEM] >>
  `bb.bb_label = s.vs_current_bb` by metis_tac[lookup_block_label] >>
  `wf_function f` by fs[venom_wf_def] >>
  `wf_ssa f` by metis_tac[] >>
  `fn_inst_wf f` by fs[venom_wf_def] >>
  `bb_well_formed bb` by fs[wf_function_def] >>
  `EVERY inst_wf bb.bb_instructions` by (
    fs[fn_inst_wf_def] >> simp[EVERY_MEM] >> metis_tac[]) >>
  (* Get the exact transformed block *)
  `lookup_block s.vs_current_bb (sccp_fn f).fn_blocks =
   SOME (case sccp_function f of NONE => bb
         | SOME _ => sccp_transform_block f bb)` by
    metis_tac[lookup_block_sccp_fn_some] >>
  simp[] >>
  qabbrev_tac `bt_bb = case sccp_function f of NONE => bb
    | SOME _ => sccp_transform_block f bb` >>
  (* Block in dfs_pre *)
  `MEM bb.bb_label (cfg_analyze f).cfg_dfs_pre` by
    metis_tac[fn_reachable_in_dfs_pre] >>
  (* Specialize IH to current ctx, keeping the general form too *)
  `!f' s'. MEM f' ctx.ctx_functions /\ s'.vs_inst_idx = 0 /\
    nophi_inv f' s' /\ strict_dom_vars_defined f' s' /\
    fn_reachable f' s'.vs_current_bb ==>
    result_equiv {} (run_function fuel ctx f' s')
      (run_function fuel (sccp_context ctx) (sccp_fn f') s')` by (
    rpt strip_tac >>
    first_x_assum (qspec_then `ctx` mp_tac) >>
    (impl_tac >- simp[]) >>
    disch_then (qspecl_then [`f'`, `s'`] mp_tac) >> simp[]) >>
  (* Callee result_equiv — needed by run_block_ctx_change *)
  `!f' callee_s. MEM f' ctx.ctx_functions /\
    callee_s.vs_inst_idx = 0 /\ FDOM callee_s.vs_vars = EMPTY /\
    fn_entry_label f' = SOME callee_s.vs_current_bb ==>
    result_equiv {} (run_function fuel ctx f' callee_s)
      (run_function fuel (sccp_context ctx) (sccp_fn f') callee_s)` by (
    rpt strip_tac >>
    `wf_function f'` by fs[venom_wf_def] >>
    `wf_ssa f'` by metis_tac[] >>
    `nophi_inv f' callee_s /\ strict_dom_vars_defined f' callee_s /\
     fn_reachable f' callee_s.vs_current_bb` by
      metis_tac[callee_entry_preconditions] >>
    qpat_assum `!f' s'. MEM f' ctx.ctx_functions /\
      s'.vs_inst_idx = 0 /\ nophi_inv f' s' /\ _ ==> _`
      (qspecl_then [`f'`, `callee_s`] mp_tac) >> simp[]) >>
  (* Establish result_equiv for the block *)
  `result_equiv {} (run_block fuel ctx bb s)
    (run_block fuel (sccp_context ctx) bt_bb s)` by (
    Cases_on `sccp_function f`
    >- (
      (* NONE: bt_bb = bb, just ctx change *)
      `bt_bb = bb` by simp[Abbr `bt_bb`] >>
      simp[] >> irule run_block_ctx_change >>
      first_x_assum ACCEPT_TAC)
    >- (
      (* SOME: use extracted helper *)
      `bt_bb = sccp_transform_block f bb` by simp[Abbr `bt_bb`] >>
      simp[] >> irule sccp_block_result_equiv_some >> simp[] >>
      first_x_assum ACCEPT_TAC)) >>
  (* Case split on original block result *)
  Cases_on `run_block fuel ctx bb s` >>
  Cases_on `run_block fuel (sccp_context ctx) bt_bb s` >>
  fs[result_equiv_def]
  >- (
    (* OK / OK — state_equiv {} implies equality, then recurse *)
    imp_res_tac state_equiv_empty_eq >> BasicProvers.VAR_EQ_TAC >>
    rename1 `run_block fuel ctx bb s = OK s'` >>
    Cases_on `s'.vs_halted` >> simp[]
    >- simp[result_equiv_def, execution_equiv_refl]
    >>
    `s'.vs_inst_idx = 0` by metis_tac[run_block_OK_inst_idx_0] >>
    `nophi_inv f s'` by (
      simp[nophi_inv_def] >>
      mp_tac (Q.SPECL [`f`, `bb`, `fuel`, `ctx`, `s`, `s'`]
        sccp_cross_block_inv) >>
      simp[] >> (impl_tac >- fs[nophi_inv_def]) >> simp[]) >>
    `strict_dom_vars_defined f s'` by (
      mp_tac (Q.SPECL [`f`, `bb`, `s`, `s'`, `fuel`, `ctx`]
        strict_dom_vars_defined_preserved) >>
      (impl_tac >- fs[wf_ssa_def]) >> simp[]) >>
    `MEM s'.vs_current_bb (bb_succs bb)` by (
      mp_tac (Q.SPECL [`fuel`, `ctx`, `bb`, `s`, `s'`]
        run_block_current_bb_in_succs) >>
      simp[] >> disch_then irule >>
      fs[bb_well_formed_def] >>
      rpt strip_tac >> CCONTR_TAC >> fs[] >> res_tac >> fs[]) >>
    `fn_reachable f s'.vs_current_bb` by (
      irule fn_reachable_step >> qexists_tac `s.vs_current_bb` >> simp[] >>
      simp[fn_cfg_edge_def] >> qexists_tac `bb` >> simp[]) >>
    (* Apply the specialized IH (not the callee fact) *)
    qpat_assum `!f' s'. MEM f' ctx.ctx_functions /\
      s'.vs_inst_idx = 0 /\ nophi_inv f' s' /\ _ ==> _`
      (qspecl_then [`f`, `s'`] mp_tac) >>
    simp[])
QED

(* ================================================================= *)
(*  Entry block propagation through sccp_fn                          *)
(* ================================================================= *)

Theorem entry_block_sccp_fn_none:
  !fn. entry_block fn = NONE ==> entry_block (sccp_fn fn) = NONE
Proof
  rpt strip_tac >>
  `fn_entry_label (sccp_fn fn) = NONE` by
    simp[sccp_fn_entry_label, fn_entry_label_def] >>
  Cases_on `entry_block (sccp_fn fn)` >> gvs[fn_entry_label_def]
QED

(* Helper: entry_block SOME propagates through sccp_fn with same label *)
Theorem entry_block_sccp_fn_some:
  !fn entry_bb.
    entry_block fn = SOME entry_bb ==>
    ?entry_bb'. entry_block (sccp_fn fn) = SOME entry_bb' /\
                entry_bb'.bb_label = entry_bb.bb_label
Proof
  rpt strip_tac >>
  `~NULL fn.fn_blocks` by gvs[entry_block_def] >>
  `~NULL (sccp_fn fn).fn_blocks` by metis_tac[sccp_fn_blocks_nonempty] >>
  qexists_tac `HD (sccp_fn fn).fn_blocks` >>
  simp[entry_block_def, listTheory.NULL_EQ] >>
  `fn_entry_label (sccp_fn fn) = fn_entry_label fn` by
    simp[sccp_fn_entry_label] >>
  gvs[fn_entry_label_def, entry_block_def, listTheory.NULL_EQ]
QED
