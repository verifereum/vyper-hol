(* dftCorrectnessFinalScript.sml
   Final proofs for DFT pass correctness.
   Depends on dftCorrectnessTheory (truncated to proven theorems).
*)

Theory dftCorrectnessFinal
Ancestors
  dftCorrectness dftCanonicalDep dftPermSim dftPipelineInvar
  dftTopoSort dftStructural dftFrontEquiv dftBlockSim
  dftWf venomWf venomState venomInst venomEffects
  venomExecSemantics venomExecProps venomInstProps
  stateEquiv stateEquivProps passSimulationDefs passSimulationProofs
  crossBlockSimProps passSharedProps passSharedDefs passSharedFrame
  analysisSimDefs analysisSimProofsBase dftDefs dftHelpers
  dftCompleteness dftIdempotent dftContraHelpers dftScheduleFixed
  sorting list rich_list combin arithmetic finite_map relation
Libs
  pairLib

(* ===== DFT preserves fn_pseudos_prefix ===== *)

(* A block whose instructions are pseudos-then-nonpseudos satisfies pseudos_prefix *)
Theorem pseudos_prefix_filter_append:
  !l1 l2 bb.
    (!x. MEM x l1 ==> is_pseudo x.inst_opcode) /\
    (!x. MEM x l2 ==> ~is_pseudo x.inst_opcode) ==>
    pseudos_prefix (bb with bb_instructions := l1 ++ l2)
Proof
  simp[pseudos_prefix_def] >> rpt strip_tac >>
  Cases_on `j < LENGTH l1` >- (
    `i < LENGTH l1` by decide_tac >>
    simp[EL_APPEND1] >>
    `MEM (EL i l1) l1` by metis_tac[MEM_EL] >>
    metis_tac[]) >>
  `j - LENGTH l1 < LENGTH l2` by (
    fs[LENGTH_APPEND] >> decide_tac) >>
  `EL j (l1 ++ l2) = EL (j - LENGTH l1) l2` by simp[EL_APPEND2] >>
  `MEM (EL (j - LENGTH l1) l2) l2` by metis_tac[MEM_EL] >>
  metis_tac[]
QED

(* dft_block always produces a pseudos_prefix block *)
Theorem dft_block_pseudos_prefix:
  !order bb. pseudos_prefix (dft_block order bb)
Proof
  rw[dft_block_def, LET_THM] >>
  irule pseudos_prefix_filter_append >> simp[MEM_FILTER] >>
  rpt strip_tac >>
  `eda_wf (build_eda bb.bb_instructions) bb.bb_instructions` by
    simp[build_eda_wf] >>
  `EVERY (\i. MEM i bb.bb_instructions)
         (entry_instructions bb.bb_instructions order
            (build_eda bb.bb_instructions))` by
    simp[entry_instructions_mem] >>
  imp_res_tac schedule_output_from_block
QED

(* Processing one DFT block preserves pseudos_prefix across all blocks in state *)
Theorem dft_process_one_preserves_pseudos_prefix:
  !cfg lr fn st lbl.
    EVERY pseudos_prefix st.dls_blocks ==>
    EVERY pseudos_prefix (FST (dft_process_one cfg lr fn st lbl)).dls_blocks
Proof
  rw[dft_process_one_def, LET_THM] >>
  Cases_on `lookup_block lbl st.dls_blocks` >> simp[] >>
  pairarg_tac >> simp[] >> pairarg_tac >> simp[] >>
  IF_CASES_TAC >> simp[] >>
  irule every_map_replace >> simp[] >>
  irule dft_block_pseudos_prefix
QED

(* One step of the DFT loop preserves pseudos_prefix across all blocks *)
Theorem dft_loop_step_preserves_pseudos_prefix:
  !cfg lr fn trip.
    EVERY pseudos_prefix (FST trip).dls_blocks ==>
    EVERY pseudos_prefix (FST (dft_loop_step cfg lr fn trip)).dls_blocks
Proof
  rpt gen_tac >> PairCases_on `trip` >>
  simp[dft_loop_step_def, LET_THM] >>
  IF_CASES_TAC >> simp[] >>
  Cases_on `trip1` >> simp[] >> strip_tac >>
  Cases_on `dft_process_one cfg lr fn trip0 h` >>
  Cases_on `r` >> simp[] >>
  qspecl_then [`cfg`,`lr`,`fn`,`trip0`,`h`]
    mp_tac dft_process_one_preserves_pseudos_prefix >>
  simp[] >> strip_tac >>
  IF_CASES_TAC >> simp[]
QED

(* Repeated DFT loop steps preserve pseudos_prefix across all blocks *)
Theorem funpow_dft_loop_preserves_pseudos_prefix:
  !n cfg lr fn trip.
    EVERY pseudos_prefix (FST trip).dls_blocks ==>
    EVERY pseudos_prefix (FST (FUNPOW (dft_loop_step cfg lr fn) n trip)).dls_blocks
Proof
  Induct >> simp[FUNPOW_SUC] >> rpt strip_tac >>
  irule dft_loop_step_preserves_pseudos_prefix >>
  first_x_assum irule >> simp[]
QED

(* DFT preserves fn_pseudos_prefix: if the input function has it, so does the output *)
Theorem dft_fn_pseudos_prefix:
  !fn. fn_pseudos_prefix fn ==> fn_pseudos_prefix (dft_fn fn)
Proof
  rpt strip_tac >>
  simp[dft_fn_def, LET_THM] >>
  CONV_TAC (DEPTH_CONV PairRules.PBETA_CONV) >>
  simp[] >>
  simp[fn_pseudos_prefix_def] >>
  rewrite_tac[GSYM EVERY_MEM] >>
  irule funpow_dft_loop_preserves_pseudos_prefix >>
  simp[fn_pseudos_prefix_def, EVERY_MEM] >>
  fs[fn_pseudos_prefix_def]
QED

(* ===== Function-level: run_blocks lift_result ===== *)

(* Unfold run_blocks for SUC fuel *)
val run_blocks_SUC = let
  val rb = run_blocks_def
  val (vars, _) = strip_forall (concl rb)
  val [sv,fv,fnv,cv] = vars
  val inst = SPECL [sv, mk_comb(``SUC``, fv), fnv, cv] rb
in SIMP_RULE (srw_ss()) [] inst |> GENL [sv, fv, fnv, cv] end;

(* ===== Function-level: run_function lift_result ===== *)

(* DFT preserves the function entry label *)
Theorem dft_fn_entry_label:
  !fn. fn_entry_label (dft_fn fn) = fn_entry_label fn
Proof
  gen_tac >>
  Cases_on `fn.fn_blocks` >- (
    Cases_on `(dft_fn fn).fn_blocks` >- (
      simp[fn_entry_label_def, entry_block_def]) >>
    assume_tac (Q.SPEC `fn` dft_fn_labels_map) >>
    gvs[MAP_EQ_NIL]) >>
  Cases_on `(dft_fn fn).fn_blocks` >- (
    assume_tac (Q.SPEC `fn` dft_fn_labels_map) >>
    gvs[MAP_EQ_NIL]) >>
  simp[fn_entry_label_def, entry_block_def] >>
  assume_tac (Q.SPEC `fn` dft_fn_labels_map) >> gvs[]
QED

(* DFT preserves run_function results up to lift_result equivalence *)
Theorem dft_fn_run_function_lift:
  !fuel ctx fn s.
    dft_schedule_safe /\
    wf_ssa fn /\ wf_function fn /\ fn_pseudos_prefix fn /\
    s.vs_inst_idx = 0 /\ ~s.vs_halted ==>
    lift_result (state_equiv {}) (execution_equiv {}) revert_equiv
      (run_function fuel ctx fn s)
      (run_function fuel ctx (dft_fn fn) s)
Proof
  simp[dft_schedule_safe_false]
QED

(* ===== Pass-level correctness ===== *)

(* The DFT pass is correct: it preserves the observable behavior of run_function *)
Theorem dft_pass_correct:
  !fn ctx s.
    dft_schedule_safe /\
    wf_ssa fn /\ wf_function fn /\ fn_pseudos_prefix fn /\
    s.vs_inst_idx = 0 /\ ~s.vs_halted ==>
    pass_correct (state_equiv {}) (execution_equiv {}) revert_equiv
      (\fuel. run_function fuel ctx fn s)
      (\fuel. run_function fuel ctx (dft_fn fn) s)
Proof
  simp[dft_schedule_safe_false]
QED
