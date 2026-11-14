(* Correctness of the ordered supply-threaded memory merging pass. *)
Theory mmBlockSimProofs
Ancestors
  mmCorrectnessProofs mmTraceProofs mmDloadProofs mmLocalScanProofs
  mmTransformSupply dftCorrectnessFinal passSimulationDefs passSimulationProofs
  stateEquiv stateEquivProofs cfgWf mmWfProofs

Theorem mm_result_refl[local]:
  !r. lift_result (state_equiv UNIV) (execution_equiv UNIV) revert_equiv r r
Proof
  Cases >> simp[lift_result_def, state_equiv_refl,
                execution_equiv_refl, revert_equiv_def]
QED

Theorem mm_result_trans[local]:
  !r1 r2 r3.
  lift_result (state_equiv UNIV) (execution_equiv UNIV) revert_equiv r1 r2 /\
  lift_result (state_equiv UNIV) (execution_equiv UNIV) revert_equiv r2 r3 ==>
  lift_result (state_equiv UNIV) (execution_equiv UNIV) revert_equiv r1 r3
Proof
  rpt strip_tac >> irule lift_result_trans_proof >>
  metis_tac[state_equiv_trans, execution_equiv_trans, revert_equiv_def]
QED

Theorem mm_result_no_error[local]:
  !r1 r2.
  lift_result (state_equiv UNIV) (execution_equiv UNIV) revert_equiv r1 r2 /\
  ~(?e. r1 = Error e) ==> ~(?e. r2 = Error e)
Proof
  Cases >> Cases >> simp[lift_result_def]
QED

Theorem mm_entry_state_transport[local]:
  fn_entry_state fn s /\ fn_entry_label fn' = fn_entry_label fn ==>
  fn_entry_state fn' s
Proof
  simp[o1PassLiftTheory.fn_entry_state_def]
QED

Theorem mm_local_prefix_correct[local]:
  !k fn0 supply index bb sk.
  k <= 4 /\ fn_inst_wf fn0 /\ wf_function fn0 /\ wf_ssa fn0 /\ all_reachable fn0 /\
  ir_supply_covers_fn supply fn0 /\ index < LENGTH fn0.fn_blocks /\
  FOLDL (\(b,t) phase. case phase of
      NONE => transform_block_memzero_supply (dfg_build_function fn0) t b
    | SOME m => transform_block_mode_supply (dfg_build_function fn0) m t b)
    (EL index fn0.fn_blocks,supply)
    (TAKE k [NONE; SOME CalldataMerge; SOME DloadMerge; SOME Mem2Mem]) = (bb,sk) ==>
  fn_inst_wf (fn0 with fn_blocks := LUPDATE bb index fn0.fn_blocks) /\
  wf_function (fn0 with fn_blocks := LUPDATE bb index fn0.fn_blocks) /\
  wf_ssa (fn0 with fn_blocks := LUPDATE bb index fn0.fn_blocks) /\
  all_reachable (fn0 with fn_blocks := LUPDATE bb index fn0.fn_blocks) /\
  ir_supply_covers_fn sk (fn0 with fn_blocks := LUPDATE bb index fn0.fn_blocks) /\
  fn_entry_label (fn0 with fn_blocks := LUPDATE bb index fn0.fn_blocks) = fn_entry_label fn0 /\
  (!fuel ctx eom s.
    fn_entry_state fn0 s /\ LENGTH s.vs_call_ctx.cc_calldata < dimword (:256) /\
    eom < dimword (:256) /\
    EVERY (\((p,d,id),f,i,t). p = [] ==> static_mem_ok eom ctx f i t)
      (trace_function fuel ctx fn0 s) /\
    ~(?err. run_function fuel ctx fn0 s = Error err) ==>
    lift_result (state_equiv UNIV) (execution_equiv UNIV) revert_equiv
      (run_function fuel ctx fn0 s)
      (run_function fuel ctx (fn0 with fn_blocks := LUPDATE bb index fn0.fn_blocks) s) /\
    EVERY (\((p,d,id),f,i,t). p = [] ==> static_mem_ok eom ctx f i t)
      (trace_function fuel ctx (fn0 with fn_blocks := LUPDATE bb index fn0.fn_blocks) s))
Proof
  Induct_on `k`
  >- (simp[] >> rpt strip_tac >> gvs[listTheory.LUPDATE_SAME] >>
      simp[mm_result_refl]) >>
  rpt gen_tac >> strip_tac >>
  `k < 4` by decide_tac >>
  Cases_on `FOLDL (\(b,t) phase. case phase of
      NONE => transform_block_memzero_supply (dfg_build_function fn0) t b
    | SOME m => transform_block_mode_supply (dfg_build_function fn0) m t b)
    (EL index fn0.fn_blocks,supply)
    (TAKE k [NONE; SOME CalldataMerge; SOME DloadMerge; SOME Mem2Mem])` >>
  rename1 `_ = (b,t)` >>
  first_x_assum (qspecl_then [`fn0`,`supply`,`index`,`b`,`t`] mp_tac) >>
  simp[] >> strip_tac >>
  `TAKE (SUC k) [NONE; SOME CalldataMerge; SOME DloadMerge; SOME Mem2Mem] =
   SNOC (EL k [NONE; SOME CalldataMerge; SOME DloadMerge; SOME Mem2Mem])
     (TAKE k [NONE; SOME CalldataMerge; SOME DloadMerge; SOME Mem2Mem])`
    by (irule rich_listTheory.TAKE_SUC_BY_TAKE >> simp[]) >>
  gvs[listTheory.FOLDL_SNOC] >>
  qspecl_then [`fn0`,`supply`,`index`,`k`] mp_tac mm_local_stage_correct >>
  simp[] >> strip_tac >> rpt gen_tac >> strip_tac >>
  qpat_x_assum `!fuel ctx eom s. fn_entry_state fn0 s /\ _ ==> _`
    drule_all >> strip_tac >>
  `fn_entry_state (fn0 with fn_blocks := LUPDATE b index fn0.fn_blocks) s`
    by metis_tac[mm_entry_state_transport] >>
  `~(?err. run_function fuel ctx
      (fn0 with fn_blocks := LUPDATE b index fn0.fn_blocks) s = Error err)`
    by metis_tac[mm_result_no_error] >>
  gvs[] >>
  first_x_assum drule_all >> strip_tac >>
  metis_tac[mm_result_trans]
QED

Theorem mm_local_supply_correct[local]:
  !fn0 supply index bb sk.
  fn_inst_wf fn0 /\ wf_function fn0 /\ wf_ssa fn0 /\ all_reachable fn0 /\
  ir_supply_covers_fn supply fn0 /\ index < LENGTH fn0.fn_blocks /\
  transform_block_supply (dfg_build_function fn0) supply (EL index fn0.fn_blocks) = (bb,sk) ==>
  fn_inst_wf (fn0 with fn_blocks := LUPDATE bb index fn0.fn_blocks) /\
  wf_function (fn0 with fn_blocks := LUPDATE bb index fn0.fn_blocks) /\
  wf_ssa (fn0 with fn_blocks := LUPDATE bb index fn0.fn_blocks) /\
  all_reachable (fn0 with fn_blocks := LUPDATE bb index fn0.fn_blocks) /\
  ir_supply_covers_fn sk (fn0 with fn_blocks := LUPDATE bb index fn0.fn_blocks) /\
  fn_entry_label (fn0 with fn_blocks := LUPDATE bb index fn0.fn_blocks) = fn_entry_label fn0 /\
  (!fuel ctx eom s.
    fn_entry_state fn0 s /\ LENGTH s.vs_call_ctx.cc_calldata < dimword (:256) /\
    eom < dimword (:256) /\
    EVERY (\((p,d,id),f,i,t). p = [] ==> static_mem_ok eom ctx f i t)
      (trace_function fuel ctx fn0 s) /\
    ~(?err. run_function fuel ctx fn0 s = Error err) ==>
    lift_result (state_equiv UNIV) (execution_equiv UNIV) revert_equiv
      (run_function fuel ctx fn0 s)
      (run_function fuel ctx (fn0 with fn_blocks := LUPDATE bb index fn0.fn_blocks) s) /\
    EVERY (\((p,d,id),f,i,t). p = [] ==> static_mem_ok eom ctx f i t)
      (trace_function fuel ctx (fn0 with fn_blocks := LUPDATE bb index fn0.fn_blocks) s))
Proof
  rpt gen_tac >> strip_tac >>
  gvs[transform_block_supply_def, AllCaseEqs()] >>
  qspec_then `4` (qspecl_then [`fn0`,`supply`,`index`] mp_tac)
    mm_local_prefix_correct >>
  simp[] >> metis_tac[]
QED

Theorem mm_visit_correct[local]:
  fn_inst_wf fn /\ wf_function fn /\ wf_ssa fn /\ all_reachable fn /\
  ir_supply_covers_fn supply fn /\ index < LENGTH fn.fn_blocks /\
  pairs = find_dload_pairs (dfg_build_function fn) (EL index fn.fn_blocks).bb_instructions /\
  updated = fn with fn_blocks := MAP (transform_block_dload pairs) fn.fn_blocks /\
  transform_block_supply (dfg_build_function updated) supply
    (transform_block_dload pairs (EL index fn.fn_blocks)) = (bb,sk) /\
  fn' = updated with fn_blocks := LUPDATE bb index updated.fn_blocks /\
  fn_entry_state fn s /\ LENGTH s.vs_call_ctx.cc_calldata < dimword (:256) /\
  eom < dimword (:256) /\
  EVERY (\((p,d,id),f,i,t). p = [] ==> static_mem_ok eom ctx f i t)
    (trace_function fuel ctx fn s) /\
  ~(?err. run_function fuel ctx fn s = Error err) ==>
  fn_inst_wf fn' /\ wf_function fn' /\ wf_ssa fn' /\ all_reachable fn' /\
  ir_supply_covers_fn sk fn' /\ fn_entry_state fn' s /\
  EVERY (\((p,d,id),f,i,t). p = [] ==> static_mem_ok eom ctx f i t)
    (trace_function fuel ctx fn' s) /\
  ~(?err. run_function fuel ctx fn' s = Error err) /\
  lift_result (state_equiv UNIV) (execution_equiv UNIV) revert_equiv
    (run_function fuel ctx fn s) (run_function fuel ctx fn' s)
Proof
  strip_tac >>
  `MEM (EL index fn.fn_blocks) fn.fn_blocks` by simp[listTheory.EL_MEM] >>
  `all_reachable updated` by
    (gvs[] >> irule selected_dload_all_reachable >> simp[]) >>
  drule_all mm_dload_visit_correct >> strip_tac >>
  `index < LENGTH updated.fn_blocks /\
   EL index updated.fn_blocks = transform_block_dload pairs (EL index fn.fn_blocks)`
    by simp[listTheory.EL_MAP] >>
  `transform_block_supply (dfg_build_function updated) supply
    (EL index updated.fn_blocks) = (bb,sk)` by metis_tac[] >>
  drule_all mm_local_supply_correct >> strip_tac >>
  qpat_x_assum `!fuel ctx eom s. fn_entry_state fn s /\ _ ==> _`
    drule_all >> strip_tac >>
  `fn_entry_state updated s` by metis_tac[mm_entry_state_transport] >>
  `~(?err. run_function fuel ctx updated s = Error err)`
    by metis_tac[mm_result_no_error] >>
  gvs[] >> first_x_assum drule_all >> strip_tac >>
  metis_tac[mm_entry_state_transport, mm_result_no_error, mm_result_trans]
QED

Theorem mm_function_correct:
  fn_inst_wf fn /\ wf_function fn /\ wf_ssa fn /\ all_reachable fn /\
  ir_supply_covers_fn supply fn /\ fn_entry_state fn s /\
  LENGTH s.vs_call_ctx.cc_calldata < dimword (:256) /\
  eom < dimword (:256) /\ reachability_closed Inv ctx /\
  fn_entry_inv Inv ctx fn s /\
  (!inst st. Inv ctx fn inst st ==> static_mem_ok eom ctx fn inst st) /\
  transform_function_supply supply fn = (fn', supply') ==>
  (?e. run_function fuel ctx fn s = Error e) \/
  lift_result (state_equiv UNIV) (execution_equiv UNIV) revert_equiv
    (run_function fuel ctx fn s) (run_function fuel ctx fn' s)
Proof
  strip_tac >>
  Cases_on `?e. run_function fuel ctx fn s = Error e` >- simp[] >>
  disj2_tac >>
  `EVERY (\((p,d,id),f,i,t). p = [] ==> static_mem_ok eom ctx f i t)
     (trace_function fuel ctx fn s)` by metis_tac[mm_entry_trace_bound] >>
  qpat_x_assum `transform_function_supply _ _ = _` mp_tac >>
  rewrite_tac[transform_function_supply_def, mmTransformTheory.transform_function_with_def] >>
  qmatch_goalsub_abbrev_tac `FOLDL visit (fn,supply) indices` >>
  strip_tac >>
  qabbrev_tac `P = \(current,st).
    fn_inst_wf current /\ wf_function current /\ wf_ssa current /\ all_reachable current /\
    ir_supply_covers_fn st current /\ fn_entry_state current s /\
    EVERY (\((p,d,id),f,i,t). p = [] ==> static_mem_ok eom ctx f i t)
      (trace_function fuel ctx current s) /\
    ~(?err. run_function fuel ctx current s = Error err) /\
    lift_result (state_equiv UNIV) (execution_equiv UNIV) revert_equiv
      (run_function fuel ctx fn s) (run_function fuel ctx current s)` >>
  `P (fn,supply)` by (simp[Abbr `P`, mm_result_refl] >> metis_tac[]) >>
  `!index acc. MEM index indices /\ P acc ==>
     visit acc index = visit acc index /\ P (visit acc index)` by
    (rpt gen_tac >> strip_tac >> simp[] >>
     PairCases_on `acc` >> gvs[Abbr `P`] >>
     simp[Abbr `visit`] >>
     IF_CASES_TAC
     >- (qmatch_goalsub_abbrev_tac `transform_block_dload pairs (EL index acc0.fn_blocks)` >>
         qmatch_goalsub_abbrev_tac `dfg_build_function updated` >>
         BasicProvers.TOP_CASE_TAC >> simp[] >>
         drule_at (Pat `transform_block_supply _ _ _ = _`) mm_visit_correct >>
         simp[Abbr `pairs`, Abbr `updated`] >>
         disch_then drule_all >> strip_tac >>
         metis_tac[mm_result_trans]) >>
     simp[]) >>
  qspec_then `P` (qspecl_then [`visit`,`visit`] mp_tac)
    rich_listTheory.FOLDL_CONG_invariant >>
  disch_then (qspecl_then [`indices`,`(fn,supply)`] mp_tac) >>
  simp[] >> simp[Abbr `P`]
QED

Theorem eol_function_pass_correct[local]:
  !R_ok R_term R_abort exec1 exec2.
    (!fuel. (?e. exec1 fuel = Error e) \/
            lift_result R_ok R_term R_abort
              (exec1 fuel) (exec2 fuel)) /\
    (!fuel fuel'. terminates (exec1 fuel) /\ terminates (exec1 fuel') ==>
      exec1 fuel = exec1 fuel') /\
    (!fuel fuel'. terminates (exec2 fuel) /\ terminates (exec2 fuel') ==>
      exec2 fuel = exec2 fuel') /\
    (?f0. terminates (exec1 f0)) ==>
    pass_correct R_ok R_term R_abort exec1 exec2
Proof
  rw[pass_correct_def]
  >- ((* Goal 1: ∃fuel'. terminates (exec2 fuel') *)
      qpat_x_assum `!fuel. _ \/ lift_result _ _ _ _ _`
        (qspec_then `f0` mp_tac) >>
      strip_tac >> gvs[]
      >- (Cases_on `exec1 f0` >> gvs[terminates_def]) >>
      qexists_tac `f0` >>
      Cases_on `exec1 f0` >> Cases_on `exec2 f0` >>
      gvs[lift_result_def, terminates_def])
  >- ((* Goal 2: lift_result when both terminate *)
      qpat_x_assum `!fuel. _ \/ lift_result _ _ _ _ _`
        (qspec_then `fuel` mp_tac) >>
      strip_tac >> gvs[]
      >- (Cases_on `exec1 fuel` >> gvs[terminates_def]) >>
      `terminates (exec2 fuel)` by
        (Cases_on `exec1 fuel` >> Cases_on `exec2 fuel` >>
         gvs[lift_result_def, terminates_def]) >>
      `exec2 fuel' = exec2 fuel` by metis_tac[] >>
      gvs[])
QED

Theorem mm_pass_correct:
  fn_inst_wf fn /\ wf_function fn /\ wf_ssa fn /\ all_reachable fn /\
  ir_supply_covers_fn supply fn /\ fn_entry_state fn s /\
  LENGTH s.vs_call_ctx.cc_calldata < dimword (:256) /\
  eom < dimword (:256) /\ reachability_closed Inv ctx /\
  fn_entry_inv Inv ctx fn s /\
  (!inst st. Inv ctx fn inst st ==> static_mem_ok eom ctx fn inst st) /\
  transform_function_supply supply fn = (fn', supply') /\
  (?fuel. terminates (run_function fuel ctx fn s)) ==>
  pass_correct (state_equiv UNIV) (execution_equiv UNIV) revert_equiv
    (\fuel. run_function fuel ctx fn s)
    (\fuel. run_function fuel ctx fn' s)
Proof
  rpt strip_tac >>
  irule eol_function_pass_correct >>
  BETA_TAC >> rpt conj_tac >>
  metis_tac[mm_function_correct, run_function_fuel_determ]
QED
