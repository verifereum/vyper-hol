(*
 * Function Inliner — Intret Suffix Chain
 *
 * Extracted from CallSimScript to avoid OOM on the 4400+ line file.
 * Contains intret_suffix_chain and its local dependencies.
 *)

Theory functionInlinerIntretChain
Ancestors
  functionInlinerCallSimPhiStep functionInlinerSim
  functionInlinerCallSimHelpers functionInlinerCalleeSim
  functionInlinerInvokeCloneHelpers
  venomExecSemantics venomInst venomWf stateEquiv stateEquivProps
  execEquivProps cfgTransformProps venomExecProps venomInstProps

open stringTheory rich_listTheory listTheory venomStateTheory
     finite_mapTheory pairTheory

open functionInlinerCallSimPhiStepTheory
     functionInlinerSimTheory
     functionInlinerCallSimHelpersTheory
     functionInlinerCalleeSimTheory
     functionInlinerInvokeCloneHelpersTheory
     venomExecSemanticsTheory venomInstTheory venomStateTheory
     venomWfTheory stateEquivTheory stateEquivPropsTheory
     execEquivPropsTheory cfgTransformPropsTheory
     venomExecPropsTheory venomInstPropsTheory
     pred_setTheory

(* ================================================================
   Shared tactics
   ================================================================ *)

(* Unfold run_function once and reduce all case expressions via ASM_REWRITE.
   Pattern: ONCE_REWRITE[run_function_def] then reduce num_case, option_case,
   exec_result_case with BETA_TAC + ASM_REWRITE_TAC interleaved.
   Requires in scope: ~s.vs_halted, lookup_block = SOME bb, run_block = <result>
   Works ONLY when fuel is syntactically SUC n. *)
val UNFOLD_RF_TAC =
  ONCE_REWRITE_TAC[run_function_def] >>
  REWRITE_TAC[arithmeticTheory.num_case_def] >> BETA_TAC >>
  ASM_REWRITE_TAC[] >>
  REWRITE_TAC[optionTheory.option_case_def] >> BETA_TAC >>
  ASM_REWRITE_TAC[] >>
  REWRITE_TAC[exec_result_case_def] >> BETA_TAC >>
  ASM_REWRITE_TAC[];

(* ================================================================
   Helper: one-step run_function unfolding
   ================================================================ *)
Triviality run_function_one_step[local]:
  !fuel ctx fn s bb.
    ~s.vs_halted /\
    lookup_block s.vs_current_bb fn.fn_blocks = SOME bb ==>
    run_function (SUC fuel) ctx fn s =
    case run_block fuel ctx bb s of
      OK s' => if s'.vs_halted then Halt s' else run_function fuel ctx fn s'
    | Halt v => Halt v
    | Abort a v => Abort a v
    | IntRet l v => IntRet l v
    | Error e => Error e
Proof
  rpt strip_tac >>
  CONV_TAC (LAND_CONV (ONCE_REWRITE_CONV [run_function_def])) >>
  REWRITE_TAC[arithmeticTheory.num_case_def] >> BETA_TAC >>
  ASM_REWRITE_TAC[] >>
  REWRITE_TAC[optionTheory.option_case_def] >> BETA_TAC >>
  ASM_REWRITE_TAC[]
QED

(* ================================================================
   Helper: one-step + fuel mono composition
   If run_block from s gives OK s' (not halted), and run_function
   from s' terminates with fuel_rest, then run_function from s
   with fuel SUC(fuel_blk + fuel_rest) = run_function fuel_rest from s'.
   ================================================================ *)
Triviality run_function_one_step_eq[local]:
  !fuel_blk fuel_rest ctx fn s bb s'.
    ~s.vs_halted /\
    lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
    run_block fuel_blk ctx bb s = OK s' /\
    ~s'.vs_halted /\
    terminates (run_function fuel_rest ctx fn s') ==>
    run_function (SUC (fuel_blk + fuel_rest)) ctx fn s =
    run_function fuel_rest ctx fn s'
Proof
  rpt strip_tac >>
  (* One step *)
  mp_tac (Q.SPECL [`fuel_blk + fuel_rest`, `ctx`, `fn`, `s`, `bb`]
    run_function_one_step) >>
  (impl_tac >- ASM_REWRITE_TAC[]) >> DISCH_TAC >>
  (* Fuel mono on run_block *)
  `!e. run_block fuel_blk ctx bb s <> Error e` by
    metis_tac[exec_result_distinct] >>
  `run_block (fuel_blk + fuel_rest) ctx bb s = OK s'` by
    metis_tac[run_block_fuel_mono] >>
  (* Fuel mono on run_function *)
  mp_tac (Q.SPECL [`fuel_rest`, `ctx`, `fn`, `s'`]
    run_function_fuel_mono) >>
  (impl_tac >- first_assum ACCEPT_TAC) >>
  DISCH_THEN (qspec_then `fuel_blk` ASSUME_TAC) >>
  (* Compose: SUC(blk+rest) => case OK s' => rf(blk+rest) s' = rf(rest) s' *)
  ASM_REWRITE_TAC[] >>
  REWRITE_TAC[exec_result_case_def] >> BETA_TAC >>
  ASM_REWRITE_TAC[] >>
  ONCE_REWRITE_TAC[arithmeticTheory.ADD_COMM] >>
  first_assum ACCEPT_TAC
QED

(* ================================================================
   Helper: run_function never returns OK
   ================================================================ *)
Triviality run_function_not_ok[local]:
  !fuel ctx fn s v. run_function fuel ctx fn s <> OK v
Proof
  Induct >> rpt gen_tac
  >- (ONCE_REWRITE_TAC[run_function_def] >> simp[]) >>
  ONCE_REWRITE_TAC[run_function_def] >>
  simp[] >>
  Cases_on `lookup_block s.vs_current_bb fn.fn_blocks` >> simp[] >>
  Cases_on `run_block fuel ctx x s` >> simp[] >>
  Cases_on `v'.vs_halted` >> simp[]
QED

(* ================================================================
   Helper: run_block OK prev_bb for any starting inst_idx
   ================================================================ *)
Triviality run_block_ok_prev_bb_any_idx[local]:
  !fuel ctx bb s s1.
    bb_well_formed bb /\
    s.vs_inst_idx <= LENGTH bb.bb_instructions /\
    run_block fuel ctx bb s = OK s1 ==>
    s1.vs_prev_bb = SOME s.vs_current_bb
Proof
  rpt strip_tac >>
  `!n fuel ctx s'.
     n = LENGTH bb.bb_instructions - s'.vs_inst_idx /\
     s'.vs_inst_idx <= LENGTH bb.bb_instructions /\
     s'.vs_current_bb = s.vs_current_bb /\
     run_block fuel ctx bb s' = OK s1 ==>
     s1.vs_prev_bb = SOME s.vs_current_bb`
    suffices_by (
      disch_then (qspecl_then
        [`LENGTH bb.bb_instructions - s.vs_inst_idx`,
         `fuel`, `ctx`, `s`] mp_tac) >>
      simp[]) >>
  completeInduct_on `n` >> rpt strip_tac >>
  qabbrev_tac `i = s'.vs_inst_idx` >>
  Cases_on `i >= LENGTH bb.bb_instructions`
  >- (
    qpat_x_assum `run_block _ _ _ _ = _` mp_tac >>
    ONCE_REWRITE_TAC[run_block_def] >>
    simp[get_instruction_def]
  ) >>
  `i < LENGTH bb.bb_instructions` by fs[] >>
  qpat_x_assum `run_block _ _ _ _ = _` mp_tac >>
  ONCE_REWRITE_TAC[run_block_def] >>
  simp[get_instruction_def] >>
  Cases_on `step_inst fuel' ctx' (EL i bb.bb_instructions) s'` >>
  gvs[]
  >- (
    strip_tac >>
    Cases_on `is_terminator (EL i bb.bb_instructions).inst_opcode` >> gvs[]
    >- (
      Cases_on `v.vs_halted` >> gvs[] >>
      `i = PRE (LENGTH bb.bb_instructions)` by
        (fs[bb_well_formed_def] >> first_x_assum drule >> simp[]) >>
      gvs[] >>
      `(EL (PRE (LENGTH bb.bb_instructions)) bb.bb_instructions).inst_opcode
         <> INVOKE` by
        (CCONTR_TAC >> gvs[is_terminator_def]) >>
      `step_inst_base
         (EL (PRE (LENGTH bb.bb_instructions)) bb.bb_instructions) s' = OK s1` by
        gvs[step_inst_non_invoke] >>
      drule_all step_inst_base_term_prev_bb >> simp[]
    )
    >- (
      `v.vs_current_bb = s'.vs_current_bb` by
        (mp_tac step_preserves_control_flow >>
         disch_then (qspecl_then [`fuel'`, `ctx'`,
           `EL i bb.bb_instructions`, `s'`, `v`] mp_tac) >> simp[]) >>
      qpat_x_assum `!m. m < _ ==> _`
        (qspec_then `LENGTH bb.bb_instructions - SUC i` mp_tac) >>
      impl_tac >- simp[Abbr `i`] >>
      disch_then (qspecl_then [`fuel'`, `ctx'`,
        `v with vs_inst_idx := SUC i`] mp_tac) >>
      simp[]
    )
  )
QED

(* ================================================================
   Helper: extract_labels and is_label
   ================================================================ *)
Triviality extract_labels_every_is_label[local]:
  !ops lbls. extract_labels ops = SOME lbls ==>
    EVERY (\op. IS_SOME (get_label op)) ops
Proof
  Induct >> simp[extract_labels_def] >>
  Cases >> simp[extract_labels_def, get_label_def] >>
  rpt strip_tac >> Cases_on `extract_labels ops` >> gvs[]
QED

(* ================================================================
   Helper: step_inst_base on terminator implies successor
   ================================================================ *)
Triviality step_inst_base_term_succs_no_wf[local]:
  !inst s s'.
    is_terminator inst.inst_opcode /\
    step_inst_base inst s = OK s' /\ ~s'.vs_halted ==>
    MEM s'.vs_current_bb (get_successors inst)
Proof
  rpt strip_tac >>
  Cases_on `inst.inst_opcode` >>
  fs[is_terminator_def] >>
  fs[step_inst_base_def, get_successors_def,
     get_label_def, AllCaseEqs(), jump_to_def, is_terminator_def] >>
  gvs[]
  >- (Cases_on `cond_op` >> fs[get_label_def])
  >- (Cases_on `cond_op` >> fs[get_label_def])
  >- (
    `EVERY (\op. IS_SOME (get_label op)) label_ops` by
      metis_tac[extract_labels_every_is_label] >>
    `MAP (THE o get_label) label_ops = labels` by
      metis_tac[extract_labels_eq_map] >>
    `FILTER IS_SOME (MAP get_label label_ops) = MAP get_label label_ops` by
      simp[FILTER_EQ_ID, EVERY_MAP] >>
    `MAP THE (MAP get_label label_ops) = labels` by
      fs[MAP_MAP_o] >>
    Cases_on `IS_SOME (get_label selector_op)` >> asm_rewrite_tac[MAP, MEM] >>
    fs[MEM_EL] >> metis_tac[MEM_EL])
QED

(* ================================================================
   Helper: run_block OK on well-formed block implies current_bb in succs
   ================================================================ *)
Triviality run_block_current_bb_in_succs_wf[local]:
  !fuel ctx bb s s1.
    bb_well_formed bb /\
    s.vs_inst_idx = 0 /\
    run_block fuel ctx bb s = OK s1 ==>
    MEM s1.vs_current_bb (bb_succs bb)
Proof
  rpt strip_tac >>
  `!n fuel ctx s.
     n = LENGTH bb.bb_instructions - s.vs_inst_idx /\
     s.vs_inst_idx <= LENGTH bb.bb_instructions /\
     run_block fuel ctx bb s = OK s1 ==>
     MEM s1.vs_current_bb (bb_succs bb)`
    suffices_by (
      disch_then (qspecl_then
        [`LENGTH bb.bb_instructions`, `fuel`, `ctx`, `s`] mp_tac) >>
      simp[]) >>
  completeInduct_on `n` >> rpt strip_tac >>
  qabbrev_tac `i = s'.vs_inst_idx` >>
  Cases_on `i >= LENGTH bb.bb_instructions`
  >- (
    qpat_x_assum `run_block _ _ _ _ = _` mp_tac >>
    ONCE_REWRITE_TAC[run_block_def] >>
    simp[get_instruction_def]
  ) >>
  `i < LENGTH bb.bb_instructions` by fs[] >>
  qpat_x_assum `run_block _ _ _ _ = _` mp_tac >>
  ONCE_REWRITE_TAC[run_block_def] >>
  simp[get_instruction_def] >>
  Cases_on `step_inst fuel' ctx' (EL i bb.bb_instructions) s'` >>
  gvs[]
  >- (
    strip_tac >>
    Cases_on `is_terminator (EL i bb.bb_instructions).inst_opcode` >> gvs[]
    >- (
      Cases_on `v.vs_halted` >> gvs[] >>
      `~(i < LENGTH bb.bb_instructions - 1)` by
        (fs[bb_well_formed_def] >>
         `i = PRE (LENGTH bb.bb_instructions)` by
           (first_x_assum drule >> simp[]) >>
         simp[]) >>
      `i = PRE (LENGTH bb.bb_instructions)` by fs[] >> gvs[] >>
      `(EL (PRE (LENGTH bb.bb_instructions)) bb.bb_instructions).inst_opcode
         <> INVOKE` by
        (CCONTR_TAC >> gvs[is_terminator_def]) >>
      `step_inst_base
         (EL (PRE (LENGTH bb.bb_instructions)) bb.bb_instructions) s' = OK s1` by
        gvs[step_inst_non_invoke] >>
      drule_all step_inst_base_term_succs_no_wf >> strip_tac >>
      simp[bb_succs_def] >>
      Cases_on `bb.bb_instructions` >> gvs[LAST_EL, MEM_nub, MEM_REVERSE]
    )
    >- (
      qpat_x_assum `!m. m < _ ==> _`
        (qspec_then `LENGTH bb.bb_instructions - SUC i` mp_tac) >>
      impl_tac >- simp[Abbr `i`] >>
      disch_then (qspecl_then [`fuel'`, `ctx'`,
        `v with vs_inst_idx := SUC i`] mp_tac) >>
      simp[]
    )
  )
QED

(* ================================================================
   Helper: lift_result symmetry
   ================================================================ *)
Triviality lift_result_sym[local]:
  !R_ok R_term a b.
    (!s1 s2. R_ok s1 s2 ==> R_ok s2 s1) /\
    (!s1 s2. R_term s1 s2 ==> R_term s2 s1) /\
    lift_result R_ok R_term a b ==>
    lift_result R_ok R_term b a
Proof
  rpt gen_tac >> Cases_on `a` >> Cases_on `b` >>
  simp[lift_result_def]
QED

(* ================================================================
   Helper: run_function prev_bb irrelevance for any fuel
   ================================================================ *)
Triviality run_function_prev_bb_any_fuel[local]:
  !fuel ctx fn s p bb.
    lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
    EVERY (\inst. inst.inst_opcode <> PHI) bb.bb_instructions /\
    bb_well_formed bb ==>
    lift_result (=) shared_globals_np
      (run_function fuel ctx fn s)
      (run_function fuel ctx fn (s with vs_prev_bb := p))
Proof
  Cases >- (
    rpt strip_tac >>
    ONCE_REWRITE_TAC[run_function_def] >> simp[lift_result_def]) >>
  rpt strip_tac >>
  irule run_function_no_phi_entry_prev_bb_eq >> metis_tac[]
QED

(* ================================================================
   Helper: clone_adj_to_caller_xf — lift terminating result from
   s_clone_adj (= s_jmp with prev_bb := NONE) to s2 (before bb_trunc)
   ================================================================ *)
Triviality clone_adj_to_caller_xf[local]:
  !fuel_adj fuel_bb ctx fn bb_trunc s2 s_jmp clone_entry_bb.
    terminates (run_function fuel_adj ctx fn (s_jmp with vs_prev_bb := NONE)) /\
    run_block fuel_bb ctx bb_trunc s2 = OK s_jmp /\
    ~s_jmp.vs_halted /\
    lookup_block s2.vs_current_bb fn.fn_blocks = SOME bb_trunc /\
    lookup_block s_jmp.vs_current_bb fn.fn_blocks = SOME clone_entry_bb /\
    EVERY (\inst. inst.inst_opcode <> PHI) clone_entry_bb.bb_instructions /\
    bb_well_formed clone_entry_bb ==>
    ?fuel_total.
      lift_result (=) shared_globals_np
        (run_function fuel_adj ctx fn (s_jmp with vs_prev_bb := NONE))
        (run_function fuel_total ctx fn s2)
Proof
  rpt gen_tac >> strip_tac >>
  qexists_tac `SUC (fuel_bb + fuel_adj)` >>
  `!e. run_block fuel_bb ctx bb_trunc s2 <> Error e` by simp[] >>
  `run_block (fuel_bb + fuel_adj) ctx bb_trunc s2 = OK s_jmp` by
    metis_tac[run_block_fuel_mono] >>
  CONV_TAC (RAND_CONV (ONCE_REWRITE_CONV [run_function_def])) >>
  ASM_REWRITE_TAC[] >>
  `lift_result (=) shared_globals_np
     (run_function (fuel_bb + fuel_adj) ctx fn s_jmp)
     (run_function (fuel_bb + fuel_adj) ctx fn (s_jmp with vs_prev_bb := NONE))` by
    (irule run_function_prev_bb_any_fuel >> metis_tac[]) >>
  `run_function (fuel_bb + fuel_adj) ctx fn (s_jmp with vs_prev_bb := NONE) =
   run_function fuel_adj ctx fn (s_jmp with vs_prev_bb := NONE)` by (
    `fuel_bb + fuel_adj = fuel_adj + fuel_bb` by simp[] >>
    metis_tac[run_function_fuel_mono]) >>
  gvs[] >>
  irule lift_result_sym >>
  rpt conj_tac
  >- metis_tac[]
  >- simp[shared_globals_np_def]
  >- ASM_REWRITE_TAC[]
QED

(* ================================================================
   Helper: terminal_right_chain — given terminates on s_at_ret,
   compose with clone_adj_to_caller_xf to get run_function at s2
   ================================================================ *)
Triviality terminal_right_chain[local]:
  !fuel_rf fuel_bb fuel_clone ctx caller_xf
   bb_trunc s2 s_at_ret s_jmp ce_bb.
    terminates (run_function fuel_rf ctx caller_xf s_at_ret) /\
    run_block fuel_bb ctx bb_trunc s2 = OK s_jmp /\
    ~s_jmp.vs_halted /\
    lookup_block s2.vs_current_bb caller_xf.fn_blocks = SOME bb_trunc /\
    lookup_block s_jmp.vs_current_bb caller_xf.fn_blocks = SOME ce_bb /\
    EVERY (\inst. inst.inst_opcode <> PHI) ce_bb.bb_instructions /\
    bb_well_formed ce_bb /\
    (!fuel_k. terminates (run_function fuel_k ctx caller_xf s_at_ret) ==>
       run_function (fuel_clone + fuel_k) ctx caller_xf
         (s_jmp with vs_prev_bb := NONE) =
       run_function fuel_k ctx caller_xf s_at_ret) ==>
    ?fuel_total.
      lift_result (=) shared_globals_np
        (run_function fuel_rf ctx caller_xf s_at_ret)
        (run_function fuel_total ctx caller_xf s2)
Proof
  rpt gen_tac >> strip_tac >>
  mp_tac (Q.SPECL [`fuel_clone + fuel_rf`, `fuel_bb`, `ctx`, `caller_xf`,
    `bb_trunc`, `s2`, `s_jmp`, `ce_bb`] clone_adj_to_caller_xf) >>
  impl_tac >- (
    ASM_REWRITE_TAC[] >>
    first_x_assum (qspec_then `fuel_rf` mp_tac) >>
    impl_tac >- ASM_REWRITE_TAC[] >>
    DISCH_TAC >> ASM_REWRITE_TAC[]) >>
  strip_tac >> qexists_tac `fuel_total` >>
  `run_function (fuel_clone + fuel_rf) ctx caller_xf
     (s_jmp with vs_prev_bb := NONE) =
   run_function fuel_rf ctx caller_xf s_at_ret` by
    (first_x_assum irule >> ASM_REWRITE_TAC[]) >>
  gvs[lift_result_def]
QED

(* execution_equiv implies shared_globals_np *)
Triviality execution_equiv_shared_globals_np[local]:
  !vars s1 s2. execution_equiv vars s1 s2 ==> shared_globals_np s1 s2
Proof
  rpt strip_tac >> fs[execution_equiv_def, shared_globals_np_def]
QED

(* Chain shared_globals_np through lift_result for terminal results. *)
Triviality lift_result_np_halt[local]:
  !R s1 s2 r.
    shared_globals_np s1 s2 /\
    lift_result (=) shared_globals_np (Halt s2) r ==>
    lift_result R shared_globals_np (Halt s1) r
Proof
  rpt gen_tac >> Cases_on `r` >> simp[lift_result_def] >>
  metis_tac[shared_globals_np_trans]
QED

Triviality lift_result_np_abort[local]:
  !R a s1 s2 r.
    shared_globals_np s1 s2 /\
    lift_result (=) shared_globals_np (Abort a s2) r ==>
    lift_result R shared_globals_np (Abort a s1) r
Proof
  rpt gen_tac >> Cases_on `r` >> simp[lift_result_def] >>
  metis_tac[shared_globals_np_trans]
QED

Triviality lift_result_np_intret[local]:
  !R l s1 s2 r.
    shared_globals_np s1 s2 /\
    lift_result (=) shared_globals_np (IntRet l s2) r ==>
    lift_result R shared_globals_np (IntRet l s1) r
Proof
  rpt gen_tac >> Cases_on `r` >> simp[lift_result_def] >>
  metis_tac[shared_globals_np_trans]
QED

(* Shared tactic for terminal cases (Halt/Abort/IntRet/OK-halted):
   Given rf_eq: `run_function (SUC fuel) ctx caller_xf s_at_ret = <result>`,
   derive terminates, apply terminal_right_chain, witness fuel_total,
   and reduce the case expression. *)
val TERMINAL_RIGHT_TAC =
  `terminates (run_function (SUC fuel) ctx caller_xf s_at_ret)` by
    ASM_REWRITE_TAC[terminates_def, exec_result_case_def] >>
  mp_tac (Q.SPECL [`SUC fuel`, `fuel_bb`, `fuel_clone`, `ctx`, `caller_xf`,
    `bb_trunc`, `s2`, `s_at_ret`, `s_jmp`, `ce_bb`]
    terminal_right_chain) >>
  (impl_tac >- ASM_REWRITE_TAC[]) >>
  strip_tac >> qexists_tac `fuel_total` >>
  REWRITE_TAC[exec_result_case_def] >> BETA_TAC >>
  ASM_REWRITE_TAC[];

(* lift_result transitivity when second relation uses (=) for R_ok *)
Triviality lift_result_trans_eq[local]:
  !R_ok R_term r1 r2 r3.
    (!s1 s2 s3. R_term s1 s2 /\ R_term s2 s3 ==> R_term s1 s3) ==>
    lift_result R_ok R_term r1 r2 ==>
    lift_result (=) R_term r2 r3 ==>
    lift_result R_ok R_term r1 r3
Proof
  rpt gen_tac >> strip_tac >>
  Cases_on `r1` >> Cases_on `r2` >> Cases_on `r3` >>
  simp[lift_result_def] >>
  metis_tac[]
QED

(* ================================================================
   MAIN THEOREM: intret_suffix_chain
   ================================================================ *)
Theorem intret_suffix_chain:
  !fuel fuel_bb fuel_clone ctx caller caller_xf
   bb ret_bb bb_trunc s2 s_ok s_at_ret s_jmp ce_bb
   excl_vars idx.
    lift_result
      (\s1 s2. execution_equiv excl_vars s1 s2 /\
               s1.vs_current_bb = s2.vs_current_bb)
      (\s1 s2. execution_equiv excl_vars s1 s2)
      (run_block fuel ctx bb (s_ok with vs_inst_idx := SUC idx))
      (run_block fuel ctx ret_bb s_at_ret) /\
    lookup_block s_at_ret.vs_current_bb caller_xf.fn_blocks = SOME ret_bb /\
    s_at_ret.vs_inst_idx = 0 /\
    ~s_at_ret.vs_halted /\
    run_block fuel_bb ctx bb_trunc s2 = OK s_jmp /\
    ~s_jmp.vs_halted /\
    lookup_block s2.vs_current_bb caller_xf.fn_blocks = SOME bb_trunc /\
    lookup_block s_jmp.vs_current_bb caller_xf.fn_blocks = SOME ce_bb /\
    EVERY (\inst. inst.inst_opcode <> PHI) ce_bb.bb_instructions /\
    bb_well_formed ce_bb /\
    (!fuel_k. terminates (run_function fuel_k ctx caller_xf s_at_ret) ==>
       run_function (fuel_clone + fuel_k) ctx caller_xf
         (s_jmp with vs_prev_bb := NONE) =
       run_function fuel_k ctx caller_xf s_at_ret) /\
    bb_well_formed bb /\
    bb_well_formed ret_bb /\
    SUC idx <= LENGTH bb.bb_instructions /\
    (!s1' s2'.
       execution_equiv excl_vars s1' s2' /\
       s1'.vs_current_bb = s2'.vs_current_bb /\
       s1'.vs_inst_idx = 0 /\ s2'.vs_inst_idx = 0 /\
       FDOM s1'.vs_labels = {} /\
       ~s1'.vs_halted /\
       ((s1'.vs_prev_bb = s2'.vs_prev_bb /\
         s1'.vs_prev_bb <> SOME s_at_ret.vs_current_bb /\
         (MEM s1'.vs_current_bb (bb_succs ret_bb) ==>
          s1'.vs_prev_bb <> SOME s_ok.vs_current_bb)) \/
        (s1'.vs_prev_bb = SOME s_ok.vs_current_bb /\
         s2'.vs_prev_bb = SOME s_at_ret.vs_current_bb /\
         MEM s1'.vs_current_bb (bb_succs ret_bb))) ==>
       ?fuel'.
         lift_result (state_equiv excl_vars) shared_globals_np
           (run_function fuel ctx caller s1')
           (run_function fuel' ctx caller_xf s2')) /\
    (!f s s'. run_block f ctx bb s = OK s' ==> FDOM s'.vs_labels = FDOM s.vs_labels) /\
    (!f s s'. run_block f ctx ret_bb s = OK s' ==> FDOM s'.vs_labels = FDOM s.vs_labels) /\
    FDOM s_ok.vs_labels = {}
    ==>
    ?fuel'.
      lift_result (state_equiv excl_vars) shared_globals_np
        (case run_block fuel ctx bb (s_ok with vs_inst_idx := SUC idx) of
           OK s'' => if s''.vs_halted then Halt s''
                     else run_function fuel ctx caller s''
         | Halt s1 => Halt s1
         | Abort a s1 => Abort a s1
         | IntRet v1 s1 => IntRet v1 s1
         | Error e => Error e)
        (run_function fuel' ctx caller_xf s2)
Proof
  rpt gen_tac >> strip_tac >>
  Cases_on `run_block fuel ctx bb (s_ok with vs_inst_idx := SUC idx)` >>
  Cases_on `run_block fuel ctx ret_bb s_at_ret` >>
  FULL_SIMP_TAC bool_ss [lift_result_def] >>
  REWRITE_TAC[exec_result_case_def] >> BETA_TAC
  >- ((* OK/OK *)
    rename1 `run_block _ _ bb _ = OK s1'` >>
    rename1 `run_block _ _ ret_bb _ = OK s2'` >>
    Cases_on `s1'.vs_halted`
    (* halted *)
    >- (
      `s2'.vs_halted` by (
        qpat_x_assum `execution_equiv _ s1' s2'` mp_tac >>
        REWRITE_TAC[execution_equiv_def] >> metis_tac[]) >>
      `shared_globals_np s1' s2'` by
        metis_tac[execution_equiv_shared_globals_np] >>
      ASM_REWRITE_TAC[] >>
      `run_function (SUC fuel) ctx caller_xf s_at_ret = Halt s2'` by (
        `s_at_ret.vs_halted = F` by ASM_REWRITE_TAC[] >>
        `s2'.vs_halted = T` by ASM_REWRITE_TAC[] >>
        UNFOLD_RF_TAC) >>
      `terminates (run_function (SUC fuel) ctx caller_xf s_at_ret)` by
        ASM_REWRITE_TAC[terminates_def, exec_result_case_def] >>
      mp_tac (Q.SPECL [`SUC fuel`, `fuel_bb`, `fuel_clone`, `ctx`, `caller_xf`,
        `bb_trunc`, `s2`, `s_at_ret`, `s_jmp`, `ce_bb`]
        terminal_right_chain) >>
      (impl_tac >- ASM_REWRITE_TAC[]) >>
      strip_tac >> qexists_tac `fuel_total` >>
      qpat_x_assum `lift_result _ _ (run_function _ _ _ _) _` mp_tac >>
      ASM_REWRITE_TAC[] >> strip_tac >>
      irule lift_result_np_halt >> qexists_tac `s2'` >>
      ASM_REWRITE_TAC[])
    (* non-halted *)
    >- (
      ASM_REWRITE_TAC[] >>
      (* Derive halted equivalence *)
      `~s2'.vs_halted` by (
        qpat_x_assum `execution_equiv _ s1' s2'` mp_tac >>
        REWRITE_TAC[execution_equiv_def] >> metis_tac[]) >>
      (* Derive inst_idx = 0 *)
      `s1'.vs_inst_idx = 0` by metis_tac[run_block_OK_inst_idx_0] >>
      `s2'.vs_inst_idx = 0` by metis_tac[run_block_OK_inst_idx_0] >>
      (* Derive prev_bb *)
      `s1'.vs_prev_bb = SOME s_ok.vs_current_bb` by (
        mp_tac (Q.SPECL [`fuel`, `ctx`, `bb`,
          `s_ok with vs_inst_idx := SUC idx`, `s1'`]
          run_block_ok_prev_bb_any_idx) >>
        REWRITE_TAC[venomStateTheory.venom_state_accfupds,
                     combinTheory.K_THM] >>
        ASM_REWRITE_TAC[]) >>
      `s2'.vs_prev_bb = SOME s_at_ret.vs_current_bb` by (
        mp_tac (Q.SPECL [`fuel`, `ctx`, `ret_bb`, `s_at_ret`, `s2'`]
          run_block_ok_prev_bb_any_idx) >>
        ASM_REWRITE_TAC[] >>
        `0n <= LENGTH ret_bb.bb_instructions` by
          REWRITE_TAC[arithmeticTheory.ZERO_LESS_EQ] >>
        ASM_REWRITE_TAC[]) >>
      (* Derive MEM in succs *)
      `MEM s2'.vs_current_bb (bb_succs ret_bb)` by
        metis_tac[run_block_current_bb_in_succs_wf] >>
      (* Derive labels preservation *)
      `FDOM s1'.vs_labels = {}` by (
        `FDOM s1'.vs_labels = FDOM (s_ok with vs_inst_idx := SUC idx).vs_labels` by
          metis_tac[] >>
        FULL_SIMP_TAC bool_ss
          [venomStateTheory.venom_state_accfupds, combinTheory.K_THM]) >>
      (* Apply IH *)
      first_x_assum (qspecl_then [`s1'`, `s2'`] mp_tac) >>
      (impl_tac >- (
        ASM_REWRITE_TAC[] >> DISJ2_TAC >> ASM_REWRITE_TAC[] >>
        `s1'.vs_current_bb = s2'.vs_current_bb` by ASM_REWRITE_TAC[] >>
        ASM_REWRITE_TAC[])) >>
      strip_tac >>
      rename1 `lift_result _ _ _ (run_function fuel_ih _ _ _)` >>
      (* Handle Error case first: if IH right = Error, left must be Error too *)
      reverse (Cases_on `terminates (run_function fuel_ih ctx caller_xf s2')`)
      >- (
        (* ~terminates means Error *)
        Cases_on `run_function fuel_ih ctx caller_xf s2'` >>
        FULL_SIMP_TAC bool_ss [terminates_def, exec_result_case_def] >>
        (* IH is Error; left must also be Error for lift_result to hold *)
        Cases_on `run_function fuel ctx caller s1'` >>
        FULL_SIMP_TAC bool_ss [lift_result_def] >>
        (* Both Error: witness 0, run_function 0 = Error *)
        qexists_tac `0` >> ONCE_REWRITE_TAC[run_function_def] >>
        REWRITE_TAC[arithmeticTheory.num_case_def, lift_result_def]) >>
      (* Now: terminates (run_function fuel_ih ctx caller_xf s2') *)
      suspend "ok_nonhalted"
    )
  )
  (* Halt on left, Halt on right *)
  >- (
    `shared_globals_np v v'` by metis_tac[execution_equiv_shared_globals_np] >>
    `run_function (SUC fuel) ctx caller_xf s_at_ret = Halt v'` by
      UNFOLD_RF_TAC >>
    `terminates (run_function (SUC fuel) ctx caller_xf s_at_ret)` by
      ASM_REWRITE_TAC[terminates_def, exec_result_case_def] >>
    mp_tac (Q.SPECL [`SUC fuel`, `fuel_bb`, `fuel_clone`, `ctx`, `caller_xf`,
      `bb_trunc`, `s2`, `s_at_ret`, `s_jmp`, `ce_bb`]
      terminal_right_chain) >>
    (impl_tac >- ASM_REWRITE_TAC[]) >>
    strip_tac >> qexists_tac `fuel_total` >>
    qpat_x_assum `lift_result _ _ (run_function _ _ _ _) _` mp_tac >>
    ASM_REWRITE_TAC[] >> strip_tac >>
    irule lift_result_np_halt >> qexists_tac `v'` >>
    ASM_REWRITE_TAC[])
  (* Abort on left, Abort on right *)
  >- (
    `shared_globals_np v v'` by metis_tac[execution_equiv_shared_globals_np] >>
    `run_function (SUC fuel) ctx caller_xf s_at_ret = Abort a v'` by
      UNFOLD_RF_TAC >>
    `terminates (run_function (SUC fuel) ctx caller_xf s_at_ret)` by
      ASM_REWRITE_TAC[terminates_def, exec_result_case_def] >>
    mp_tac (Q.SPECL [`SUC fuel`, `fuel_bb`, `fuel_clone`, `ctx`, `caller_xf`,
      `bb_trunc`, `s2`, `s_at_ret`, `s_jmp`, `ce_bb`]
      terminal_right_chain) >>
    (impl_tac >- ASM_REWRITE_TAC[]) >>
    strip_tac >> qexists_tac `fuel_total` >>
    qpat_x_assum `lift_result _ _ (run_function _ _ _ _) _` mp_tac >>
    ASM_REWRITE_TAC[] >> strip_tac >>
    irule lift_result_np_abort >> qexists_tac `v'` >>
    ASM_REWRITE_TAC[])
  (* IntRet on left, IntRet on right *)
  >- (
    `shared_globals_np v v'` by metis_tac[execution_equiv_shared_globals_np] >>
    `run_function (SUC fuel) ctx caller_xf s_at_ret = IntRet l v'` by
      UNFOLD_RF_TAC >>
    `terminates (run_function (SUC fuel) ctx caller_xf s_at_ret)` by
      ASM_REWRITE_TAC[terminates_def, exec_result_case_def] >>
    mp_tac (Q.SPECL [`SUC fuel`, `fuel_bb`, `fuel_clone`, `ctx`, `caller_xf`,
      `bb_trunc`, `s2`, `s_at_ret`, `s_jmp`, `ce_bb`]
      terminal_right_chain) >>
    (impl_tac >- ASM_REWRITE_TAC[]) >>
    strip_tac >> qexists_tac `fuel_total` >>
    qpat_x_assum `lift_result _ _ (run_function _ _ _ _) _` mp_tac >>
    ASM_REWRITE_TAC[] >> strip_tac >>
    irule lift_result_np_intret >> qexists_tac `v'` >>
    ASM_REWRITE_TAC[])
  (* Error — left run_block = Error, right run_block = Error *)
  >> (qexists_tac `0` >> ONCE_REWRITE_TAC[run_function_def] >>
      REWRITE_TAC[arithmeticTheory.num_case_def, lift_result_def])
QED

Resume intret_suffix_chain[ok_nonhalted]:
  mp_tac (Q.SPECL [`fuel`, `fuel_ih`, `ctx`, `caller_xf`,
    `s_at_ret`, `ret_bb`, `s2'`] run_function_one_step_eq) >>
  (impl_tac >- ASM_REWRITE_TAC[]) >>
  DISCH_TAC >>
  `terminates (run_function (SUC (fuel + fuel_ih)) ctx caller_xf s_at_ret)` by (
    pop_assum (fn th => REWRITE_TAC[th]) >>
    first_assum ACCEPT_TAC) >>
  (* Apply terminal_right_chain *)
  mp_tac (Q.SPECL [`SUC (fuel + fuel_ih)`, `fuel_bb`, `fuel_clone`,
    `ctx`, `caller_xf`, `bb_trunc`, `s2`, `s_at_ret`, `s_jmp`, `ce_bb`]
    terminal_right_chain) >>
  (impl_tac >- ASM_REWRITE_TAC[]) >>
  strip_tac >>
  (* Rewrite: rf(SUC(fuel+fuel_ih)) = rf(fuel_ih) s2' *)
  qpat_x_assum `lift_result _ _ (run_function (SUC _) _ _ _) _` mp_tac >>
  qpat_x_assum `run_function (SUC _) _ _ s_at_ret = _`
    (fn th => REWRITE_TAC[th]) >>
  DISCH_TAC >>
  (* Witness fuel_total, compose via case split *)
  qexists_tac `fuel_total` >>
  Cases_on `run_function fuel ctx caller s1'` >>
  Cases_on `run_function fuel_ih ctx caller_xf s2'` >>
  FULL_SIMP_TAC bool_ss [lift_result_def, run_function_not_ok] >>
  Cases_on `run_function fuel_total ctx caller_xf s2` >>
  FULL_SIMP_TAC bool_ss [lift_result_def] >>
  metis_tac[shared_globals_np_trans]
QED

Finalise intret_suffix_chain;

val _ = export_theory();
