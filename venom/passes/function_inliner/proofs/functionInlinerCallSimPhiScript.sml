(*
 * Function Inliner — Block-level PHI-label substitution equivalence
 *
 * Key result: run_block_phi_subst_result_equiv
 * Uses step-level results from functionInlinerCallSimPhiStep.
 *)

Theory functionInlinerCallSimPhi
Ancestors
  functionInlinerCallSimPhiStep
  functionInlinerPrevBBMap functionInlinerCallSimHelpers
  functionInlinerInline functionInlinerDefs functionInlinerSim
  functionInlinerFresh functionInlinerCloneSim functionInlinerStepClone
  functionInlinerCalleeSim functionInlinerCloneExec
  functionInlinerBlockSplit
  venomExecSemantics venomInst venomWf stateEquiv stateEquivProps
  execEquivProps cfgTransform cfgTransformProps venomExecProps

open stringTheory rich_listTheory listTheory venomStateTheory
     finite_mapTheory pairTheory

open functionInlinerCallSimPhiStepTheory
     functionInlinerPrevBBMapTheory functionInlinerCallSimHelpersTheory
     functionInlinerDefsTheory functionInlinerInlineTheory
     functionInlinerCloneSimTheory functionInlinerSimTheory
     functionInlinerStepCloneTheory functionInlinerFreshTheory
     functionInlinerRenumberTheory functionInlinerCalleeSimTheory
     functionInlinerCloneExecTheory functionInlinerBlockSplitTheory
     venomExecSemanticsTheory venomInstTheory venomStateTheory
     venomWfTheory stateEquivTheory stateEquivPropsTheory
     execEquivPropsTheory cfgTransformTheory cfgTransformPropsTheory
     venomExecPropsTheory venomInstPropsTheory


(* Block-level PHI-label substitution equivalence.
   For blocks where PHI operand labels are substituted (old_lbl → new_lbl),
   execution with correspondingly-related prev_bb gives equivalent results. *)
Theorem run_block_phi_subst_result_equiv:
  !fuel ctx vars bb old_lbl new_lbl s1 s2.
    execution_equiv vars s1 s2 /\
    s1.vs_current_bb = s2.vs_current_bb /\
    s1.vs_inst_idx = s2.vs_inst_idx /\
    FDOM s1.vs_labels = {} /\
    ((s1.vs_prev_bb = s2.vs_prev_bb /\
      s1.vs_prev_bb <> SOME old_lbl /\ s1.vs_prev_bb <> SOME new_lbl) \/
     (s1.vs_prev_bb = SOME old_lbl /\ s2.vs_prev_bb = SOME new_lbl)) /\
    (!inst. MEM inst bb.bb_instructions ==>
            !x. MEM (Var x) inst.inst_operands ==> x NOTIN vars) /\
    ~MEM (Label new_lbl)
       (FLAT (MAP (\i. i.inst_operands) bb.bb_instructions)) ==>
    let bb' = bb with bb_instructions :=
      MAP (\inst. if inst.inst_opcode <> PHI then inst
                  else subst_label_inst old_lbl new_lbl inst)
          bb.bb_instructions in
    result_equiv vars (run_block fuel ctx bb s1) (run_block fuel ctx bb' s2)
Proof
  rpt gen_tac >> simp[] >>
  `!n fuel ctx vars bb old_lbl new_lbl sa sb.
     n = LENGTH bb.bb_instructions - sa.vs_inst_idx ==>
     execution_equiv vars sa sb /\
     sa.vs_current_bb = sb.vs_current_bb /\
     sa.vs_inst_idx = sb.vs_inst_idx /\
     FDOM sa.vs_labels = {} /\
     ((sa.vs_prev_bb = sb.vs_prev_bb /\
       sa.vs_prev_bb <> SOME old_lbl /\ sa.vs_prev_bb <> SOME new_lbl) \/
      (sa.vs_prev_bb = SOME old_lbl /\ sb.vs_prev_bb = SOME new_lbl)) /\
     (!inst. MEM inst bb.bb_instructions ==>
             !x. MEM (Var x) inst.inst_operands ==> x NOTIN vars) /\
     ~MEM (Label new_lbl)
        (FLAT (MAP (\i. i.inst_operands) bb.bb_instructions)) ==>
     let bb' = bb with bb_instructions :=
       MAP (\inst. if inst.inst_opcode <> PHI then inst
                   else subst_label_inst old_lbl new_lbl inst)
           bb.bb_instructions in
     result_equiv vars (run_block fuel ctx bb sa) (run_block fuel ctx bb' sb)`
    suffices_by (
    disch_then (qspecl_then
      [`LENGTH bb.bb_instructions - s1.vs_inst_idx`,
       `fuel`, `ctx`, `vars`, `bb`, `old_lbl`, `new_lbl`,
       `s1`, `s2`] mp_tac) >> simp[]
  ) >>
  completeInduct_on `n` >> rpt gen_tac >> strip_tac >> DISCH_TAC >>
  `execution_equiv vars sa sb` by fs[] >>
  `sa.vs_current_bb = sb.vs_current_bb` by fs[] >>
  `sa.vs_inst_idx = sb.vs_inst_idx` by fs[] >>
  `FDOM sa.vs_labels = {}` by fs[] >>
  `(!inst. MEM inst bb.bb_instructions ==>
           !x. MEM (Var x) inst.inst_operands ==> x NOTIN vars)` by fs[] >>
  `~MEM (Label new_lbl)
     (FLAT (MAP (\i. i.inst_operands) bb.bb_instructions))` by fs[] >>
  simp[] >>
  ONCE_REWRITE_TAC[run_block_def] >>
  simp[get_instruction_def] >>
  Cases_on `sb.vs_inst_idx < LENGTH bb.bb_instructions` >>
  simp[result_equiv_def] >>
  qabbrev_tac `inst = EL sb.vs_inst_idx bb.bb_instructions` >>
  qabbrev_tac `inst' = if inst.inst_opcode <> PHI then inst
                        else subst_label_inst old_lbl new_lbl inst` >>
  `EL sb.vs_inst_idx
     (MAP (\i. if i.inst_opcode <> PHI then i
               else subst_label_inst old_lbl new_lbl i)
          bb.bb_instructions) = inst'` by
    simp[Abbr `inst'`, EL_MAP] >>
  `inst'.inst_opcode = inst.inst_opcode` by
    (simp[Abbr `inst'`] >> IF_CASES_TAC >> simp[subst_label_inst_def]) >>
  `!x. MEM (Var x) inst.inst_operands ==> x NOTIN vars` by
    (gvs[Abbr `inst`] >>
     first_x_assum match_mp_tac >> simp[EL_MEM]) >>
  `~MEM (Label new_lbl) inst.inst_operands` by
    (fs[Abbr `inst`, MEM_FLAT, MEM_MAP] >>
     metis_tac[EL_MEM]) >>
  simp[] >>
  Cases_on `inst.inst_opcode = PHI`
  >- suspend "phi"
  >> suspend "non_phi"
QED

Resume run_block_phi_subst_result_equiv[non_phi]:
  simp[Abbr `inst'`]
  \\ mp_tac (Q.SPECL [`fuel`, `ctx`, `inst`, `vars`, `sa`, `sb`]
      step_inst_non_phi_same_tag)
  \\ simp[] \\ strip_tac
  \\ Cases_on `step_inst fuel ctx inst sa`
  \\ Cases_on `step_inst fuel ctx inst sb`
  \\ fs[exec_result_tag_def]
  \\ simp[result_equiv_def]
  (* Non-OK matching pairs: Halt, Abort, IntRet — use result_equiv_non_ok *)
  \\ TRY (
    mp_tac (Q.SPECL [`fuel`, `ctx`, `inst`, `vars`, `sa`, `sb`]
      step_inst_non_phi_result_equiv_non_ok) >>
    simp[result_equiv_def] >> NO_TAC
  )
  (* OK/OK: 2 goals. Apply step_inst_non_phi_exec_equiv *)
  \\ mp_tac (Q.SPECL [`fuel`, `ctx`, `inst`, `vars`, `sa`, `sb`, `v`, `v'`]
      step_inst_non_phi_exec_equiv)
  \\ simp[] \\ strip_tac
  \\ Cases_on `is_terminator inst.inst_opcode` \\ simp[]
  (* Terminator goals *)
  \\ TRY (
    Cases_on `v'.vs_halted` >> simp[result_equiv_def] >>
    simp[state_equiv_def] >> NO_TAC
  )
  (* Non-terminator: apply IH *)
  \\ `FDOM v.vs_labels = {}` by
      (imp_res_tac step_inst_preserves_labels_always >> gvs[])
  \\ first_x_assum (qspec_then
      `LENGTH bb.bb_instructions - SUC sb.vs_inst_idx` mp_tac)
  \\ (impl_tac >- simp[])
  \\ simp[LET_THM]
  \\ disch_then (qspecl_then
      [`fuel`, `ctx`, `vars`, `bb`, `old_lbl`, `new_lbl`,
       `v with vs_inst_idx := SUC sb.vs_inst_idx`,
       `v' with vs_inst_idx := SUC sb.vs_inst_idx`] mp_tac)
  \\ simp[]
  \\ disch_then match_mp_tac
  \\ simp[execution_equiv_update_inst_idx]
  \\ rpt conj_tac
  \\ TRY (first_assum ACCEPT_TAC)
  \\ TRY (rpt strip_tac >> res_tac >> NO_TAC)
  \\ gvs[]
QED

Resume run_block_phi_subst_result_equiv[phi]:
  (* ---- PHI case ---- *)
  `inst' = subst_label_inst old_lbl new_lbl inst` by
    simp[Abbr `inst'`]
  \\ `exec_result_tag (step_inst fuel ctx inst sa) =
       exec_result_tag (step_inst fuel ctx inst' sb) /\
       !va vb. step_inst fuel ctx inst sa = OK va /\
               step_inst fuel ctx inst' sb = OK vb ==>
         execution_equiv vars va vb /\
         va.vs_current_bb = vb.vs_current_bb /\
         va.vs_inst_idx = vb.vs_inst_idx /\
         va.vs_prev_bb = sa.vs_prev_bb /\
         vb.vs_prev_bb = sb.vs_prev_bb /\
         (va.vs_halted <=> vb.vs_halted)` by (
    simp[]
    \\ mp_tac (SIMP_RULE (srw_ss()) [LET_THM] step_phi_subst_equiv)
    \\ disch_then (qspecl_then [`fuel`, `ctx`, `vars`, `inst`,
        `old_lbl`, `new_lbl`, `sa`, `sb`] mp_tac)
    \\ (impl_tac >- (rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >> fs[]))
    \\ simp[]
  )
  \\ `(?va. step_inst fuel ctx inst sa = OK va) \/
       (?e. step_inst fuel ctx inst sa = Error e)` by
      (irule step_phi_ok_or_error \\ simp[])
  \\ `inst'.inst_opcode = PHI` by
      (simp[subst_label_inst_def])
  \\ `(?vb. step_inst fuel ctx inst' sb = OK vb) \/
       (?e'. step_inst fuel ctx inst' sb = Error e')` by
      (irule step_phi_ok_or_error \\ simp[])
  \\ fs[exec_result_tag_def]
  \\ TRY (simp[result_equiv_def] >> NO_TAC)
  \\ simp[is_terminator_def]
  \\ `FDOM va.vs_labels = {}` by
      (imp_res_tac step_inst_preserves_labels_always >> fs[])
  \\ first_x_assum (qspec_then
      `LENGTH bb.bb_instructions - SUC sb.vs_inst_idx` mp_tac)
  \\ (impl_tac >- simp[])
  \\ simp[LET_THM]
  \\ disch_then (qspecl_then
      [`fuel`, `ctx`, `vars`, `bb`, `old_lbl`, `new_lbl`,
       `va with vs_inst_idx := SUC sb.vs_inst_idx`,
       `vb with vs_inst_idx := SUC sb.vs_inst_idx`] mp_tac)
  \\ simp[]
  \\ disch_then match_mp_tac
  \\ simp[execution_equiv_update_inst_idx]
  \\ rpt conj_tac
  \\ TRY (first_assum ACCEPT_TAC)
  \\ TRY (rpt strip_tac >> res_tac >> NO_TAC)
  \\ disj1_tac >> conj_tac >> (CCONTR_TAC >> fs[])
QED

Finalise run_block_phi_subst_result_equiv;

(* run_block_reaches on PHI-substituted prefix preserves execution_equiv.
   Key helper for call-site proof: both sides reach equivalent states
   after the pre-invoke prefix. *)
Theorem run_block_reaches_phi_subst_equiv:
  !k fuel ctx vars bb old_lbl new_lbl s1 s2 s1'.
    run_block_reaches fuel ctx bb s1 k = SOME s1' /\
    s1.vs_inst_idx = s2.vs_inst_idx /\
    s1.vs_inst_idx + k <= LENGTH bb.bb_instructions /\
    execution_equiv vars s1 s2 /\
    s1.vs_current_bb = s2.vs_current_bb /\
    FDOM s1.vs_labels = {} /\
    ((s1.vs_prev_bb = s2.vs_prev_bb /\
      s1.vs_prev_bb <> SOME old_lbl /\ s1.vs_prev_bb <> SOME new_lbl) \/
     (s1.vs_prev_bb = SOME old_lbl /\ s2.vs_prev_bb = SOME new_lbl)) /\
    (!i. s1.vs_inst_idx <= i /\ i < s1.vs_inst_idx + k ==>
         ~is_terminator (EL i bb.bb_instructions).inst_opcode) /\
    (!inst. MEM inst bb.bb_instructions ==>
            !x. MEM (Var x) inst.inst_operands ==> x NOTIN vars) /\
    ~MEM (Label new_lbl)
       (FLAT (MAP (\i. i.inst_operands) bb.bb_instructions)) ==>
    let bb' = bb with bb_instructions :=
      MAP (\inst. if inst.inst_opcode <> PHI then inst
                  else subst_label_inst old_lbl new_lbl inst)
          bb.bb_instructions in
    ?s2'. run_block_reaches fuel ctx bb' s2 k = SOME s2' /\
          execution_equiv vars s1' s2' /\
          s1'.vs_current_bb = s2'.vs_current_bb /\
          s1'.vs_inst_idx = s2'.vs_inst_idx /\
          FDOM s1'.vs_labels = {} /\
          ((s1'.vs_prev_bb = s2'.vs_prev_bb /\
            s1'.vs_prev_bb <> SOME old_lbl /\
            s1'.vs_prev_bb <> SOME new_lbl) \/
           (s1'.vs_prev_bb = SOME old_lbl /\
            s2'.vs_prev_bb = SOME new_lbl))
Proof
  Induct_on `k`
  >- (rpt strip_tac >> gvs[run_block_reaches_def, LET_THM] >>
      qexists_tac `s2` >> simp[run_block_reaches_def])
  >>
  rpt gen_tac \\ simp[LET_THM]
  \\ DISCH_THEN (fn th => map_every ASSUME_TAC (CONJUNCTS th))
  (* Decompose run_block_reaches SUC via helper lemma *)
  \\ drule run_block_reaches_SUC \\ strip_tac
  \\ rename [`get_instruction bb s1.vs_inst_idx = SOME inst`,
             `step_inst _ _ inst s1 = OK s1_step`]
  (* Build corresponding instruction for bb' *)
  \\ qabbrev_tac `inst' = if inst.inst_opcode <> PHI then inst
                        else subst_label_inst old_lbl new_lbl inst`
  \\ (SUBGOAL_THEN ``get_instruction
       (bb with bb_instructions :=
          MAP (\inst. if inst.inst_opcode <> PHI then inst
                      else subst_label_inst old_lbl new_lbl inst)
              bb.bb_instructions)
       s2.vs_inst_idx = SOME inst'``
       ASSUME_TAC >- (
    gvs[get_instruction_def, Abbr `inst'`] >> simp[EL_MAP]))
  \\ (SUBGOAL_THEN ``inst'.inst_opcode = inst.inst_opcode``
       ASSUME_TAC >- (
    simp[Abbr `inst'`] >> IF_CASES_TAC >> simp[subst_label_inst_def]))
  \\ (SUBGOAL_THEN ``~is_terminator inst'.inst_opcode``
       ASSUME_TAC >- simp[])
  \\ (SUBGOAL_THEN ``!x. MEM (Var x) inst.inst_operands ==> x NOTIN vars``
       ASSUME_TAC >- (
    gvs[get_instruction_def] >>
    first_x_assum match_mp_tac >> simp[EL_MEM]))
  \\ (SUBGOAL_THEN ``~MEM (Label new_lbl) inst.inst_operands``
       ASSUME_TAC >- (
    fs[get_instruction_def, MEM_FLAT, MEM_MAP] >>
    metis_tac[EL_MEM]))
  (* Establish step equivalence via PHI/non-PHI case *)
  \\ (SUBGOAL_THEN ``?s2_step. step_inst fuel ctx inst' s2 = OK s2_step /\
             execution_equiv vars s1_step s2_step /\
             s1_step.vs_current_bb = s2_step.vs_current_bb /\
             s1_step.vs_inst_idx = s2_step.vs_inst_idx /\
             ((s1_step.vs_prev_bb = s2_step.vs_prev_bb /\
               s1_step.vs_prev_bb <> SOME old_lbl /\
               s1_step.vs_prev_bb <> SOME new_lbl) \/
              (s1_step.vs_prev_bb = SOME old_lbl /\
               s2_step.vs_prev_bb = SOME new_lbl))``
       STRIP_ASSUME_TAC
    >- suspend "step_equiv")
  \\ simp[run_block_reaches_def]
  \\ (SUBGOAL_THEN ``FDOM s1_step.vs_labels = {}`` ASSUME_TAC
       >- (imp_res_tac step_inst_preserves_labels_always >> gvs[]))
  \\ first_x_assum (qspecl_then [`fuel`, `ctx`, `vars`, `bb`,
      `old_lbl`, `new_lbl`,
      `s1_step with vs_inst_idx := SUC s1.vs_inst_idx`,
      `s2_step with vs_inst_idx := SUC s2.vs_inst_idx`] mp_tac)
  \\ simp[execution_equiv_update_inst_idx]
  \\ disch_then match_mp_tac
  \\ rpt conj_tac \\ TRY (first_assum ACCEPT_TAC)
  \\ TRY (rpt strip_tac >>
       qpat_x_assum `!i. _ <= i /\ _ ==> _`
         (qspec_then `i` mp_tac) >> simp[] >> NO_TAC)
  (* Remaining: propagate prev_bb disjunction to s2_step *)
  \\ TRY (disj1_tac >> gvs[] >> NO_TAC)
  \\ TRY (disj2_tac >> gvs[] >> NO_TAC)
  \\ simp[]
QED

Resume run_block_reaches_phi_subst_equiv[step_equiv]:
  mp_tac (SIMP_RULE (srw_ss()) [LET_THM] step_phi_subst_or_same_step_equiv)
  \\ disch_then (qspecl_then [`fuel`, `ctx`, `vars`, `inst`,
      `old_lbl`, `new_lbl`, `s1`, `s2`, `s1_step`] mp_tac)
  \\ simp[Abbr `inst'`]
  \\ (impl_tac >- (
    rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >> simp[]))
  \\ strip_tac
  \\ qpat_x_assum `step_inst _ _ _ s2 = OK _` (fn eq =>
       EXISTS_TAC (rand (rhs (concl eq))) >> ASSUME_TAC eq)
  \\ simp[]
QED

Finalise run_block_reaches_phi_subst_equiv;

val _ = export_theory();
