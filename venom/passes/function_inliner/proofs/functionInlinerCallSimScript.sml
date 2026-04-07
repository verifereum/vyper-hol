(*
 * Function Inliner — Call Site Simulation
 *
 * Proves that inlining a single call site preserves execution behavior,
 * then lifts to iterated inlining and context-level correctness.
 *
 * Proof chain:
 *   1. inline_one_site_fn_correct: single call site simulation
 *   2. inline_at_sites_fn_correct: iterated inlining (induction + transitivity)
 *   3. inline_candidate_correct: context-level lifting
 *)

Theory functionInlinerCallSim
Ancestors
  functionInlinerCallSimPhi functionInlinerCallSimHelpers functionInlinerPrevBBMap
  functionInlinerInline functionInlinerDefs functionInlinerSim
  functionInlinerFresh functionInlinerCloneSim functionInlinerStepClone
  functionInlinerCalleeSim functionInlinerCloneExec
  functionInlinerBlockSplit functionInlinerBridge functionInlinerSuffixSim
  functionInlinerLabelOps
  functionInlinerInvokeClone functionInlinerInvokeCloneHelpers
  functionInlinerIntretChain
  venomExecSemantics venomInst venomWf stateEquiv stateEquivProps
  execEquivProps cfgTransform cfgTransformProps venomExecProps

open stringTheory rich_listTheory listTheory venomStateTheory
     finite_mapTheory pairTheory

open functionInlinerCallSimHelpersTheory functionInlinerCallSimPhiTheory
     functionInlinerCallSimPhiStepTheory functionInlinerPrevBBMapTheory
     functionInlinerDefsTheory functionInlinerInlineTheory
     functionInlinerCloneSimTheory functionInlinerSimTheory
     functionInlinerStepCloneTheory functionInlinerFreshTheory
     functionInlinerRenumberTheory functionInlinerCalleeSimTheory
     functionInlinerCloneExecTheory functionInlinerBlockSplitTheory
     functionInlinerBridgeTheory functionInlinerSuffixSimTheory
     functionInlinerLabelOpsTheory
     functionInlinerInvokeCloneTheory functionInlinerInvokeCloneHelpersTheory
     functionInlinerIntretChainTheory
     venomExecSemanticsTheory venomInstTheory venomStateTheory
     venomWfTheory stateEquivTheory stateEquivPropsTheory
     execEquivPropsTheory cfgTransformTheory cfgTransformPropsTheory
     venomExecPropsTheory venomInstPropsTheory
     pred_setTheory markerLib

(* Recursively split conjunctions into a list of theorems,
   stopping at non-conjunctions (e.g. disjunctions stay intact) *)
fun conj_list th =
  let val (l, r) = CONJ_PAIR th
  in conj_list l @ conj_list r end
  handle _ => [th];

(* Tactic: decompose a conjunction assumption into separate assumptions
   without splitting disjunctions *)
val CONJ_ASSUME_TAC = (fn th => MAP_EVERY ASSUME_TAC (conj_list th));

(* Substitute a named Abbrev everywhere (goal + assumptions) *)
val SUBST_NAMED_ABBREV_TAC = fn q =>
  qpat_x_assum q (SUBST_ALL_TAC o REWRITE_RULE[markerTheory.Abbrev_def]);

(* Unfold run_function once and reduce all case expressions via ASM_REWRITE.
   Use inside `by` blocks where gvs/simp hang due to 100+ assumptions.
   Pattern: ONCE_REWRITE[run_function_def] then reduce num_case, option_case,
   exec_result_case with BETA_TAC + ASM_REWRITE_TAC interleaved. *)
val UNFOLD_RF_TAC =
  ONCE_REWRITE_TAC[run_function_def] >>
  REWRITE_TAC[arithmeticTheory.num_case_def] >> BETA_TAC >>
  ASM_REWRITE_TAC[] >>
  REWRITE_TAC[optionTheory.option_case_def] >> BETA_TAC >>
  ASM_REWRITE_TAC[] >>
  REWRITE_TAC[exec_result_case_def] >> BETA_TAC >>
  ASM_REWRITE_TAC[];

(* One-step run_function unfolding: given preconditions, express
   run_function (SUC fuel) in terms of run_block result *)
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

Triviality lookup_block_label[local]:
  !lbl bbs bb. lookup_block lbl bbs = SOME bb ==> bb.bb_label = lbl
Proof
  rw[lookup_block_def] >> imp_res_tac FIND_pred >> gvs[]
QED

(* Non-call-site blocks in inline_call_site are preserved *)
Theorem lookup_block_inline_call_site_neq[local]:
  !prefix ret_lbl caller callee call_lbl idx lbl bb.
    lbl <> call_lbl /\
    lookup_block lbl caller.fn_blocks = SOME bb ==>
    lookup_block lbl
      (inline_call_site prefix ret_lbl caller callee call_lbl idx).fn_blocks =
    SOME bb
Proof
  rw[inline_call_site_def, LET_THM] >>
  BasicProvers.EVERY_CASE_TAC >> gvs[] >>
  pairarg_tac >> gvs[] >>
  imp_res_tac lookup_block_label >> gvs[] >>
  simp[lookup_block_APPEND, lookup_block_replace_neq]
QED

(* Combined: for non-call blocks, caller_xf has either the PHI-subst
   version or the identical block *)
Theorem lookup_block_caller_xf_neq[local]:
  !prefix ret_lbl caller callee call_lbl idx ret_bb orig_lbl new_lbl lbl bb.
    lbl <> call_lbl /\
    lookup_block lbl caller.fn_blocks = SOME bb ==>
    (lookup_block lbl
      (fix_inline_phis orig_lbl new_lbl ret_bb
        (inline_call_site prefix ret_lbl caller callee call_lbl idx)).fn_blocks =
    SOME (bb with bb_instructions :=
      MAP (\inst. if inst.inst_opcode <> PHI then inst
                  else subst_label_inst orig_lbl new_lbl inst)
          bb.bb_instructions))
    \/
    (lookup_block lbl
      (fix_inline_phis orig_lbl new_lbl ret_bb
        (inline_call_site prefix ret_lbl caller callee call_lbl idx)).fn_blocks =
    SOME bb)
Proof
  rw[] >> drule_all lookup_block_inline_call_site_neq >> strip_tac >>
  simp[lookup_block_fix_inline_phis] >>
  Cases_on `MEM lbl (bb_succs ret_bb)` >> simp[]
QED

(* ================================================================
   Fuel simulation step: general-purpose combinator for block-level
   simulation lifting to function-level with fuel existential.
   ================================================================ *)
Theorem run_function_sim_step:
  !fuel ctx func1 func2 bb1 bb2 s1 s2 vars.
    lookup_block s1.vs_current_bb func1.fn_blocks = SOME bb1 /\
    lookup_block s2.vs_current_bb func2.fn_blocks = SOME bb2 /\
    s1.vs_current_bb = s2.vs_current_bb /\
    result_equiv vars
      (run_block fuel ctx bb1 s1) (run_block fuel ctx bb2 s2) /\
    (!s1' s2'.
       run_block fuel ctx bb1 s1 = OK s1' /\
       run_block fuel ctx bb2 s2 = OK s2' /\
       ~s1'.vs_halted ==>
       ?fuel'.
         result_equiv vars
           (run_function fuel ctx func1 s1')
           (run_function fuel' ctx func2 s2')) ==>
    ?fuel'.
      result_equiv vars
        (run_function (SUC fuel) ctx func1 s1)
        (run_function fuel' ctx func2 s2)
Proof
  rpt strip_tac >>
  Cases_on `run_block fuel ctx bb1 s1`
  >~[`_ = OK _`] >- (
    rename1 `_ = OK s1'` >>
    `?s2'. run_block fuel ctx bb2 s2 = OK s2'` by
      (Cases_on `run_block fuel ctx bb2 s2` >> fs[result_equiv_def]) >>
    pop_assum strip_assume_tac >>
    `state_equiv vars s1' s2'` by fs[result_equiv_def] >>
    Cases_on `s1'.vs_halted`
    >- (
      `s2'.vs_halted` by fs[state_equiv_def, execution_equiv_def] >>
      qexists_tac `SUC fuel` >>
      ONCE_REWRITE_TAC[run_function_def] >> simp[] >>
      simp[result_equiv_def] >> fs[state_equiv_def]
    )
    >- (
      `~s2'.vs_halted` by fs[state_equiv_def, execution_equiv_def] >>
      first_x_assum (qspecl_then [`s1'`, `s2'`] mp_tac) >> simp[] >>
      strip_tac >>
      suspend "non_halted"
    )
  )
  >> (
    qexists_tac `SUC fuel` >>
    ONCE_REWRITE_TAC[run_function_def] >> simp[] >>
    Cases_on `run_block fuel ctx bb2 s2` >> fs[result_equiv_def]
  )
QED

Resume run_function_sim_step[non_halted]:
  (* Case split: is the left continuation Error? *)
  Cases_on `?e. run_function fuel ctx func1 s1' = Error e`
  >- (
    (* Left is Error → pick fuel' = 0 *)
    gvs[] \\ qexists_tac `0`
    \\ ONCE_REWRITE_TAC[run_function_def] \\ simp[result_equiv_def]
  )
  >- (
    (* Left is non-Error → use fuel_mono *)
    gvs[] \\
    qexists_tac `SUC (fuel + fuel')`
    \\ ONCE_REWRITE_TAC[run_function_def] \\ simp[]
    (* Block step: fuel_mono on run_block *)
    \\ `run_block (fuel + fuel') ctx bb2 s2 = OK s2'` by (
         mp_tac (Q.SPECL [`fuel`, `fuel + fuel'`, `ctx`, `bb2`, `s2`, `OK s2'`]
           (CONJUNCT1 (CONJUNCT2 fuel_mono))) \\ simp[]
       )
    \\ simp[]
    (* Continuation: fuel_mono on run_function *)
    \\ `terminates (run_function fuel' ctx func2 s2')` by (
         Cases_on `run_function fuel ctx func1 s1'` >>
         Cases_on `run_function fuel' ctx func2 s2'` >>
         fs[result_equiv_def, terminates_def]
       )
    \\ `run_function (fuel + fuel') ctx func2 s2' =
        run_function fuel' ctx func2 s2'` by (
         `fuel + fuel' = fuel' + fuel` by simp[] >>
         pop_assum SUBST1_TAC >>
         irule run_function_fuel_mono >> simp[]
       )
    \\ simp[]
  )
QED

Finalise run_function_sim_step;

(* Generalized sim step: lift_result (state_equiv vars) shared_globals_np.
   Same structure as run_function_sim_step but with weaker terminal relation.
   Used for inliner proofs where Halt/Abort from INVOKE can't satisfy
   execution_equiv (callee vs clone variable environments differ). *)
Theorem run_function_sim_step_gen[local]:
  !fuel ctx func1 func2 bb1 bb2 s1 s2 vars.
    lookup_block s1.vs_current_bb func1.fn_blocks = SOME bb1 /\
    lookup_block s2.vs_current_bb func2.fn_blocks = SOME bb2 /\
    s1.vs_current_bb = s2.vs_current_bb /\
    lift_result (state_equiv vars) shared_globals_np
      (run_block fuel ctx bb1 s1) (run_block fuel ctx bb2 s2) /\
    (!s1' s2'.
       run_block fuel ctx bb1 s1 = OK s1' /\
       run_block fuel ctx bb2 s2 = OK s2' /\
       ~s1'.vs_halted ==>
       ?fuel'.
         lift_result (state_equiv vars) shared_globals_np
           (run_function fuel ctx func1 s1')
           (run_function fuel' ctx func2 s2')) ==>
    ?fuel'.
      lift_result (state_equiv vars) shared_globals_np
        (run_function (SUC fuel) ctx func1 s1)
        (run_function fuel' ctx func2 s2)
Proof
  rpt strip_tac >>
  Cases_on `run_block fuel ctx bb1 s1`
  >~[`_ = OK _`] >- (
    rename1 `_ = OK s1'` >>
    `?s2'. run_block fuel ctx bb2 s2 = OK s2'` by
      (Cases_on `run_block fuel ctx bb2 s2` >> fs[lift_result_def]) >>
    pop_assum strip_assume_tac >>
    `state_equiv vars s1' s2'` by fs[lift_result_def] >>
    Cases_on `s1'.vs_halted`
    >- (
      (* OK + halted → Halt. Need shared_globals_np (weaker than execution_equiv) *)
      `s2'.vs_halted` by fs[state_equiv_def, execution_equiv_def] >>
      qexists_tac `SUC fuel` >>
      ONCE_REWRITE_TAC[run_function_def] >> simp[] >>
      simp[lift_result_def] >>
      imp_res_tac state_equiv_shared_globals_np
    )
    >- (
      (* OK + not halted → continuation *)
      `~s2'.vs_halted` by fs[state_equiv_def, execution_equiv_def] >>
      first_x_assum (qspecl_then [`s1'`, `s2'`] mp_tac) >> simp[] >>
      strip_tac >>
      (* Case: left continuation Error? *)
      Cases_on `?e. run_function fuel ctx func1 s1' = Error e`
      >- (
        gvs[] >> qexists_tac `0` >>
        ONCE_REWRITE_TAC[run_function_def] >> simp[lift_result_def]
      )
      >- (
        gvs[] >>
        qexists_tac `SUC (fuel + fuel')` >>
        ONCE_REWRITE_TAC[run_function_def] >> simp[] >>
        `run_block (fuel + fuel') ctx bb2 s2 = OK s2'` by (
          mp_tac (Q.SPECL [`fuel`, `fuel + fuel'`, `ctx`, `bb2`, `s2`, `OK s2'`]
            (CONJUNCT1 (CONJUNCT2 fuel_mono))) >> simp[]
        ) >>
        simp[] >>
        `terminates (run_function fuel' ctx func2 s2')` by (
          Cases_on `run_function fuel ctx func1 s1'` >>
          Cases_on `run_function fuel' ctx func2 s2'` >>
          fs[lift_result_def, terminates_def]
        ) >>
        `run_function (fuel + fuel') ctx func2 s2' =
         run_function fuel' ctx func2 s2'` by (
          `fuel + fuel' = fuel' + fuel` by simp[] >>
          pop_assum SUBST1_TAC >>
          irule run_function_fuel_mono >> simp[]
        ) >>
        simp[]
      )
    )
  )
  >> (
    (* Non-OK block result: Halt/Abort/IntRet/Error *)
    qexists_tac `SUC fuel` >>
    ONCE_REWRITE_TAC[run_function_def] >> simp[] >>
    Cases_on `run_block fuel ctx bb2 s2` >> fs[lift_result_def]
  )
QED

(* run_block OK ⇒ prev_bb = SOME current_bb.
   Works for any starting inst_idx (not just 0).
   Generalizes venomExecProps.run_block_ok_prev_bb. *)
Theorem run_block_ok_prev_bb_any_idx[local]:
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
      (* i must be the last instruction index *)
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

(* Corollary for inst_idx = 0 *)
Theorem run_block_ok_prev_bb_wf[local]:
  !fuel ctx bb s s1.
    bb_well_formed bb /\
    s.vs_inst_idx = 0 /\
    run_block fuel ctx bb s = OK s1 ==>
    s1.vs_prev_bb = SOME s.vs_current_bb
Proof
  metis_tac[run_block_ok_prev_bb_any_idx, DECIDE ``0n <= n``]
QED

(* Step 7 helper: MEM case — PHI-subst block *)
Triviality non_call_block_mem[local]:
  !fuel ctx excl_vars bb call_lbl ret_lbl s1 s2.
    execution_equiv excl_vars s1 s2 /\
    s1.vs_current_bb = s2.vs_current_bb /\
    s1.vs_inst_idx = s2.vs_inst_idx /\
    FDOM s1.vs_labels = {} /\
    ((s1.vs_prev_bb = s2.vs_prev_bb /\
      s1.vs_prev_bb <> SOME call_lbl /\ s1.vs_prev_bb <> SOME ret_lbl) \/
     (s1.vs_prev_bb = SOME call_lbl /\ s2.vs_prev_bb = SOME ret_lbl)) /\
    (!inst. MEM inst bb.bb_instructions ==>
            !x. MEM (Var x) inst.inst_operands ==> x NOTIN excl_vars) /\
    ~MEM (Label ret_lbl) (FLAT (MAP (\i. i.inst_operands) bb.bb_instructions))
    ==>
    result_equiv excl_vars (run_block fuel ctx bb s1)
      (run_block fuel ctx
        (bb with bb_instructions :=
          MAP (\inst. if inst.inst_opcode <> PHI then inst
                      else subst_label_inst call_lbl ret_lbl inst)
              bb.bb_instructions) s2)
Proof
  rpt strip_tac >>
  mp_tac (SRULE [LET_THM] run_block_phi_subst_result_equiv) >>
  disch_then match_mp_tac >> metis_tac[]
QED

(* Step 7 helper: ~MEM case — identical block *)
Triviality non_call_block_not_mem[local]:
  !fuel ctx excl_vars bb s1 s2.
    execution_equiv excl_vars s1 s2 /\
    s1.vs_current_bb = s2.vs_current_bb /\
    s1.vs_inst_idx = s2.vs_inst_idx /\
    s1.vs_prev_bb = s2.vs_prev_bb /\
    (!inst. MEM inst bb.bb_instructions ==>
            !x. MEM (Var x) inst.inst_operands ==> x NOTIN excl_vars)
    ==>
    result_equiv excl_vars (run_block fuel ctx bb s1)
      (run_block fuel ctx bb s2)
Proof
  rpt strip_tac >>
  irule run_block_same_ctx_result_equiv >>
  conj_tac >- first_assum ACCEPT_TAC >>
  simp[state_equiv_def]
QED

(* Combined step 7 helper: handles both MEM and ~MEM cases.
   mem_cond = MEM s1.vs_current_bb (bb_succs ret_bb) in the caller. *)
Triviality non_call_block_sim[local]:
  !fuel ctx excl_vars bb call_lbl ret_lbl (mem_cond:bool) s1 s2.
    execution_equiv excl_vars s1 s2 /\
    s1.vs_current_bb = s2.vs_current_bb /\
    s1.vs_inst_idx = s2.vs_inst_idx /\
    FDOM s1.vs_labels = {} /\
    ((s1.vs_prev_bb = s2.vs_prev_bb /\
      s1.vs_prev_bb <> SOME ret_lbl /\
      (mem_cond ==> s1.vs_prev_bb <> SOME call_lbl)) \/
     (s1.vs_prev_bb = SOME call_lbl /\ s2.vs_prev_bb = SOME ret_lbl /\
      mem_cond)) /\
    (!inst. MEM inst bb.bb_instructions ==>
            !x. MEM (Var x) inst.inst_operands ==> x NOTIN excl_vars) /\
    ~MEM (Label ret_lbl) (FLAT (MAP (\i. i.inst_operands) bb.bb_instructions))
    ==>
    result_equiv excl_vars (run_block fuel ctx bb s1)
      (run_block fuel ctx
        (if mem_cond then
           bb with bb_instructions :=
             MAP (\inst. if inst.inst_opcode <> PHI then inst
                         else subst_label_inst call_lbl ret_lbl inst)
                 bb.bb_instructions
         else bb) s2)
Proof
  rpt strip_tac >>
  Cases_on `mem_cond` >> fs[] >>
  metis_tac[non_call_block_mem, non_call_block_not_mem]
QED

(* General: MAP preserving opcodes preserves bb_well_formed.
   Key: use simp[EL_MAP] in small by-blocks to avoid ∀inst loop (L435). *)
Triviality bb_well_formed_map_opcode[local]:
  !bb insts (f:instruction -> instruction).
    (!inst. (f inst).inst_opcode = inst.inst_opcode) ==>
    bb_well_formed (bb with bb_instructions := insts) ==>
    bb_well_formed (bb with bb_instructions := MAP f insts)
Proof
  rpt strip_tac >>
  fs[bb_well_formed_def, basic_block_accfupds, combinTheory.K_THM] >>
  rpt conj_tac >| [
    (* only-last-terminator *)
    rpt strip_tac >>
    `is_terminator (EL i insts).inst_opcode` by
      (qpat_x_assum `is_terminator _` mp_tac >> simp[EL_MAP]) >>
    res_tac,
    (* PHI-ordering *)
    rpt strip_tac >>
    `(EL j insts).inst_opcode = PHI` by
      (qpat_x_assum `_ = PHI` mp_tac >> simp[EL_MAP]) >>
    `(EL i insts).inst_opcode = PHI` by
      (first_x_assum (qspecl_then [`i`, `j`] mp_tac) >> simp[]) >>
    simp[EL_MAP]
  ]
QED

(* bb_well_formed for conditional PHI-subst block *)
Triviality bb_well_formed_phi_subst[local]:
  !bb call_lbl ret_lbl (mem_cond:bool).
    bb_well_formed bb ==>
    bb_well_formed
      (if mem_cond then
         bb with bb_instructions :=
           MAP (\inst. if inst.inst_opcode <> PHI then inst
                       else subst_label_inst call_lbl ret_lbl inst)
               bb.bb_instructions
       else bb)
Proof
  rpt strip_tac >> Cases_on `mem_cond` >> simp[] >>
  irule bb_well_formed_map_opcode >>
  conj_tac >- (rw[] >> rw[subst_label_inst_def]) >>
  Cases_on `bb` >> fs[basic_block_fn_updates, combinTheory.K_THM]
QED

(* lookup_block success ⇒ label is in fn_labels *)
Triviality lookup_block_MEM_labels[local]:
  !lbl bbs bb.
    lookup_block lbl bbs = SOME bb ==>
    MEM lbl (MAP (\bb. bb.bb_label) bbs)
Proof
  rpt strip_tac >>
  imp_res_tac lookup_block_MEM >>
  imp_res_tac lookup_block_label >>
  simp[MEM_MAP] >> qexists_tac `bb` >> simp[]
QED

(* ================================================================
   Section 4.5: Clone execution simulation
   
   Key lemma: running the callee via INVOKE produces the same
   observable effects as running the rewritten clone blocks inline.
   
   When the callee returns IntRet, the clone execution reaches ret_lbl
   with outputs bound and matching globals.
   When the callee halts/aborts/errors, the clone does the same.
   ================================================================ *)

(* One-step unrolling of run_function *)
Triviality run_function_chain[local]:
  !ctx fn bb s s' fuel.
    lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
    run_block fuel ctx bb s = OK s' /\
    ~s'.vs_halted ==>
    run_function (SUC fuel) ctx fn s = run_function fuel ctx fn s'
Proof
  rpt strip_tac >>
  CONV_TAC (LAND_CONV (ONCE_REWRITE_CONV [run_function_def])) >>
  simp[]
QED

(*
 * clone_execution_sim: The core clone ↔ callee simulation.
 *
 * When the callee is run via INVOKE (producing IntRet), executing the
 * rewritten clone blocks inline in caller_xf produces an equivalent
 * result: reaching ret_lbl with outputs bound and globals matching.
 *
 * Proved by induction on fuel (matching callee's run_function).
 * Each block transition on the callee side corresponds to a block
 * transition on the clone side via clone_rel_np preservation.
 * The RET block is the exit: callee returns IntRet, clone does
 * ASSIGN outputs + JMP ret_lbl.
 *
 * Preconditions (all dischargeable from inline_one_site_fn_correct context):
 *   - Block lookup: clone labels in caller_xf give rewritten blocks
 *   - State: vars correspond (clone_rel_np minus prev_bb)
 *   - Params: invoke_ops in clone state eval to callee params
 *   - WF: callee no self-invoke, extern targets, no alloca, blocks well-formed
 *)
(* Placeholder: clone_execution_sim will be developed separately. *)
(*
Theorem clone_execution_sim[local]: ...
QED
*)

(* ================================================================
   Call-site block lookup in fn_inlined / caller_xf
   ================================================================ *)

(* lookup_block call_lbl fn_inlined gives the truncated block *)
Triviality lookup_block_call_lbl_fn_inlined[local]:
  !prefix ret_lbl caller callee call_lbl call_idx bb.
    lookup_block call_lbl caller.fn_blocks = SOME bb /\
    ALL_DISTINCT (fn_labels caller) ==>
    lookup_block call_lbl
      (inline_call_site prefix ret_lbl caller callee call_lbl call_idx).fn_blocks =
    SOME (bb with bb_instructions :=
      TAKE call_idx bb.bb_instructions ++
      [<|inst_id := 0; inst_opcode := JMP;
         inst_operands :=
           [Label (case (clone_function prefix callee).fn_blocks of
                     [] => "" | eb::_ => eb.bb_label)];
         inst_outputs := []|>])
Proof
  rw[inline_call_site_def, LET_THM] >>
  pairarg_tac >> gvs[] >>
  imp_res_tac lookup_block_label >>
  simp[lookup_block_APPEND, lookup_block_replace_eq] >>
  gvs[fn_labels_def]
QED

(* lookup_block call_lbl caller_xf gives truncated block (possibly PHI-rewritten) *)
Triviality lookup_block_call_lbl_caller_xf[local]:
  !prefix ret_lbl caller callee call_lbl call_idx ret_bb fn_inlined caller_xf bb.
    fn_inlined = inline_call_site prefix ret_lbl caller callee call_lbl call_idx /\
    caller_xf = fix_inline_phis call_lbl ret_lbl ret_bb fn_inlined /\
    lookup_block call_lbl caller.fn_blocks = SOME bb /\
    ALL_DISTINCT (fn_labels caller) /\
    call_idx < LENGTH bb.bb_instructions ==>
    ?trunc_bb.
      lookup_block call_lbl caller_xf.fn_blocks = SOME trunc_bb /\
      trunc_bb.bb_label = call_lbl /\
      LENGTH trunc_bb.bb_instructions = call_idx + 1 /\
      (!i. i < call_idx ==>
           EL i trunc_bb.bb_instructions =
           (if MEM call_lbl (bb_succs ret_bb) /\
               (EL i bb.bb_instructions).inst_opcode = PHI
            then subst_label_inst call_lbl ret_lbl (EL i bb.bb_instructions)
            else EL i bb.bb_instructions)) /\
      (EL call_idx trunc_bb.bb_instructions).inst_opcode = JMP
Proof
  rw[] >>
  drule_all lookup_block_call_lbl_fn_inlined >> strip_tac >>
  simp[lookup_block_fix_inline_phis] >>
  imp_res_tac lookup_block_label >>
  Cases_on `MEM call_lbl (bb_succs ret_bb)` >> simp[]
  >- (
    (* PHI-rewritten case *)
    simp[LENGTH_MAP, LENGTH_APPEND, LENGTH_TAKE] >>
    rpt strip_tac
    >- (simp[EL_MAP, EL_APPEND1, LENGTH_TAKE, EL_TAKE] >>
        Cases_on `(EL i bb.bb_instructions).inst_opcode = PHI` >> simp[])
    >- simp[EL_MAP, EL_APPEND2, LENGTH_TAKE]
  )
  >- (
    (* Non-PHI-rewritten case *)
    simp[LENGTH_APPEND, LENGTH_TAKE] >>
    rpt strip_tac
    >- simp[EL_APPEND1, LENGTH_TAKE, EL_TAKE]
    >- simp[EL_APPEND2, LENGTH_TAKE]
  )
QED

(* ================================================================
   Cloned entry label ≠ return label.
   Used to show Label ret_lbl ∉ truncated block's JMP operands.
   ================================================================ *)

Triviality inl_prefix_inline_return:
  !counter. "inl" ≼ STRCAT "inline_return" (toString counter)
Proof
  simp[isPREFIX_THM]
QED

(* The cloned entry label ≠ return_block_label.
   cloned entry = prefix ++ callee_entry (or "" if empty callee)
   ret_lbl = prefix ++ "inline_return" ++ counter
   Callee labels have no "inline_return" prefix (labels_no_inline_return).
   So entry label ≠ "inline_return" ++ counter. *)
Triviality cloned_entry_neq_ret_lbl[local]:
  !prefix callee counter.
    labels_no_inline_return callee ==>
    (case (clone_function prefix callee).fn_blocks of
       [] => "" | eb::_ => eb.bb_label) <>
    return_block_label prefix counter
Proof
  rpt gen_tac >> strip_tac >>
  rewrite_tac[clone_function_def, LET_THM, return_block_label_def] >>
  BETA_TAC >>
  Cases_on `callee.fn_blocks` >>
  rewrite_tac[MAP, list_case_def]
  >- simp[] >>
  rewrite_tac[clone_basic_block_def] >> BETA_TAC >>
  rewrite_tac[STRCAT_11] >>
  (* Goal: h.bb_label ≠ "inline_return" ++ toString counter *)
  `~isPREFIX "inline_return" h.bb_label` by (
    fs[labels_no_inline_return_def, fn_labels_def, EVERY_MAP, EVERY_MEM] >>
    first_x_assum match_mp_tac >> simp[]) >>
  strip_tac >> gvs[isPREFIX_STRCAT]
QED

(* ================================================================
   Pre-INVOKE prefix failure: when run_block_reaches NONE,
   the truncated block (with any terminator) gives the same result.
   This handles ALL result types (Halt/Abort/IntRet/Error) at once.
   ================================================================ *)

Triviality pre_invoke_prefix_fail[local]:
  !fuel ctx bb s call_idx term.
    run_block_reaches fuel ctx bb s call_idx = NONE /\
    s.vs_inst_idx = 0 /\
    call_idx <= LENGTH bb.bb_instructions ==>
    run_block fuel ctx bb s =
    run_block fuel ctx
      (bb with bb_instructions := TAKE call_idx bb.bb_instructions ++ [term]) s
Proof
  metis_tac[run_block_prefix_fail_take]
QED

(* ================================================================
   Pre-INVOKE helpers (standalone for fast iteration)
   ================================================================ *)

(* INVOKE at call_idx means call_idx is not the last instruction *)
Triviality invoke_not_last_inst:
  !bb call_idx.
    bb_well_formed bb /\
    call_idx < LENGTH bb.bb_instructions /\
    (EL call_idx bb.bb_instructions).inst_opcode = INVOKE ==>
    call_idx <> PRE (LENGTH bb.bb_instructions)
Proof
  rpt strip_tac >> gvs[] >>
  fs[bb_well_formed_def] >>
  `LAST bb.bb_instructions = EL (PRE (LENGTH bb.bb_instructions))
     bb.bb_instructions` by (irule LAST_EL >> fs[]) >>
  metis_tac[is_terminator_def, EVAL ``is_terminator INVOKE``]
QED

(* All instructions before call_idx are non-terminators *)
Triviality pre_invoke_non_terminator:
  !bb call_idx i.
    bb_well_formed bb /\
    call_idx < LENGTH bb.bb_instructions /\
    call_idx <> PRE (LENGTH bb.bb_instructions) /\
    i < call_idx ==>
    ~is_terminator (EL i bb.bb_instructions).inst_opcode
Proof
  rpt strip_tac >> CCONTR_TAC >> fs[] >>
  `i < LENGTH bb.bb_instructions` by simp[] >>
  `i = PRE (LENGTH bb.bb_instructions)` by
    metis_tac[bb_well_formed_def] >>
  fs[]
QED


(* run_block_reaches preserves execution_equiv for the SAME block,
   when both sides start with matching prev_bb and inst_idx.
   Used for the ¬MEM case where no PHI substitution occurs. *)
Triviality run_block_reaches_same_block_equiv[local]:
  !k fuel ctx vars bb s1 s2 s1'.
    run_block_reaches fuel ctx bb s1 k = SOME s1' /\
    s1.vs_inst_idx = s2.vs_inst_idx /\
    s1.vs_inst_idx + k <= LENGTH bb.bb_instructions /\
    execution_equiv vars s1 s2 /\
    s1.vs_current_bb = s2.vs_current_bb /\
    s1.vs_prev_bb = s2.vs_prev_bb /\
    FDOM s1.vs_labels = {} /\
    (!i. s1.vs_inst_idx <= i /\ i < s1.vs_inst_idx + k ==>
         ~is_terminator (EL i bb.bb_instructions).inst_opcode) /\
    (!inst. MEM inst bb.bb_instructions ==>
            !x. MEM (Var x) inst.inst_operands ==> x NOTIN vars) ==>
    ?s2'. run_block_reaches fuel ctx bb s2 k = SOME s2' /\
          execution_equiv vars s1' s2' /\
          s1'.vs_current_bb = s2'.vs_current_bb /\
          s1'.vs_inst_idx = s2'.vs_inst_idx /\
          s1'.vs_prev_bb = s2'.vs_prev_bb /\
          FDOM s1'.vs_labels = {}
Proof
  Induct_on `k`
  >- (rpt strip_tac >> gvs[run_block_reaches_def] >>
      qexists_tac `s2` >> simp[])
  >>
  rpt gen_tac >> strip_tac >>
  drule run_block_reaches_SUC >> strip_tac >>
  rename [`get_instruction bb s1.vs_inst_idx = SOME inst`,
          `step_inst _ _ inst s1 = OK s1_step`] >>
  `!x. MEM (Var x) inst.inst_operands ==> x NOTIN vars` by (
    gvs[get_instruction_def] >>
    first_x_assum match_mp_tac >> simp[EL_MEM]) >>
  `state_equiv vars s1 s2` by
    (simp[state_equiv_def] >> first_assum ACCEPT_TAC) >>
  `result_equiv vars (step_inst fuel ctx inst s1) (step_inst fuel ctx inst s2)` by (
    mp_tac (Q.SPECL [`fuel`, `ctx`, `vars`, `inst`, `s1`, `s2`]
      step_inst_same_ctx_result_equiv) >>
    simp[]) >>
  `?s2_step. step_inst fuel ctx inst s2 = OK s2_step /\
     state_equiv vars s1_step s2_step` by (
    qpat_x_assum `result_equiv _ _ _` mp_tac >>
    qpat_x_assum `step_inst _ _ _ s1 = _` (SUBST1_TAC) >>
    Cases_on `step_inst fuel ctx inst s2` >>
    simp[result_equiv_def]) >>
  `get_instruction bb s2.vs_inst_idx = SOME inst` by gvs[] >>
  simp[run_block_reaches_def] >>
  `execution_equiv vars s1_step s2_step` by
    fs[state_equiv_def, execution_equiv_def] >>
  `s1_step.vs_current_bb = s2_step.vs_current_bb` by
    fs[state_equiv_def] >>
  `s1_step.vs_prev_bb = s2_step.vs_prev_bb` by
    fs[state_equiv_def] >>
  `s1_step.vs_inst_idx = s2_step.vs_inst_idx` by (
    imp_res_tac step_inst_preserves_inst_idx >>
    gvs[is_terminator_def]) >>
  `FDOM s1_step.vs_labels = {}` by (
    imp_res_tac step_inst_preserves_labels_always >> gvs[]) >>
  first_x_assum (qspecl_then [`fuel`, `ctx`, `vars`, `bb`,
    `s1_step with vs_inst_idx := SUC s1.vs_inst_idx`,
    `s2_step with vs_inst_idx := SUC s2.vs_inst_idx`] mp_tac) >>
  simp[execution_equiv_update_inst_idx] >>
  disch_then match_mp_tac >>
  rpt conj_tac >> TRY (first_assum ACCEPT_TAC)
  >> rpt strip_tac >> qpat_x_assum `!i. _ <= i /\ _ ==> _`
       (qspec_then `i` mp_tac) >> simp[]
QED

(* Factor out renumbering: inline_one_site = renumber(fix_phis(inline_call_site(...)))
   renumber is transparent by renumber_fn_inst_ids_correct.
   So we prove the result for the un-renumbered version. *)

(*
 * inline_one_site_fn_correct — core single-site simulation
 *
 * Strategy: factor out renumber (transparent), then prove for
 * fix_phis(inline_call_site(...)) by complete induction on fuel.
 *
 * At each block transition:
 *   - Unchanged block: same execution (same ctx), IH for continuation
 *   - PHI-fixed block: resolve_phi_subst_label gives same values
 *   - Call-site block: INVOKE (left) vs JMP+clone+return (right)
 *
 * The call-site case is handled by showing the clone execution
 * produces equivalent state to the INVOKE, using run_block_clone
 * and the callee-clone simulation infrastructure.
 *)

(* Properties of a truncated block: prefix instructions from the original
   block ++ a single JMP instruction. The JMP has only Label operands and
   no Var operands. Labels in the prefix come from the original caller,
   so fresh ret_lbl doesn't appear. *)
Triviality trunc_block_label_ops[local]:
  !bb caller call_lbl call_idx jmp_inst ret_lbl excl_vars.
    lookup_block call_lbl caller.fn_blocks = SOME bb /\
    call_idx < LENGTH bb.bb_instructions /\
    jmp_inst.inst_operands = [Label clone_entry_lbl] /\
    clone_entry_lbl <> ret_lbl /\
    ~MEM ret_lbl (fn_labels caller) /\
    (!bb' inst lbl. MEM bb' caller.fn_blocks /\
                    MEM inst bb'.bb_instructions /\
                    MEM (Label lbl) inst.inst_operands ==>
                    MEM lbl (fn_labels caller)) /\
    (!bb' inst x. MEM bb' caller.fn_blocks /\
                  MEM inst bb'.bb_instructions /\
                  MEM (Var x) inst.inst_operands ==>
                  x NOTIN excl_vars) ==>
    ~MEM (Label ret_lbl)
       (FLAT (MAP (\i. i.inst_operands)
         (TAKE call_idx bb.bb_instructions ++ [jmp_inst]))) /\
    (!inst'. MEM inst' (TAKE call_idx bb.bb_instructions ++ [jmp_inst]) ==>
             !x. MEM (Var x) inst'.inst_operands ==> x NOTIN excl_vars)
Proof
  rpt strip_tac >>
  imp_res_tac lookup_block_MEM >>
  fs[MEM_FLAT, MEM_MAP, MEM_APPEND] >>
  imp_res_tac MEM_TAKE >>
  gvs[] >> metis_tac[]
QED

Theorem inline_one_site_fn_correct[local]:
  !caller callee ist caller' ist' excl_vars fuel ctx s.
    inline_one_site caller callee ist = SOME (caller', ist') /\
    lookup_function callee.fn_name ctx.ctx_functions = SOME callee /\
    fn_no_invoke callee.fn_name callee /\
    invoke_targets_extern callee /\
    ALL_DISTINCT (fn_labels callee) /\
    labels_no_inline_return callee /\
    EVERY bb_well_formed callee.fn_blocks /\
    EVERY (\bb. params_sequential bb.bb_instructions 0) callee.fn_blocks /\
    EVERY (\bb. EVERY (\i. i.inst_opcode <> PARAM) bb.bb_instructions)
      (TL callee.fn_blocks) /\
    ALL_DISTINCT (fn_labels caller) /\
    labels_fresh_above ist.is_inline_count caller /\
    vars_fresh_above ist.is_inline_count caller /\
    fn_no_alloca caller /\
    fn_no_alloca callee /\
    EVERY bb_well_formed caller.fn_blocks /\
    fn_has_entry callee /\
    label_ops_closed callee /\
    EVERY (\bb. EVERY (\inst.
      inst_targets callee.fn_name inst ==>
      callee_ret_arity_le (LENGTH inst.inst_outputs) callee)
      bb.bb_instructions) caller.fn_blocks /\
    EVERY (\bb. EVERY (\inst.
      inst_targets callee.fn_name inst ==>
      EVERY (\blk. count_params blk.bb_instructions <=
                   LENGTH (TL inst.inst_operands)) callee.fn_blocks)
      bb.bb_instructions) caller.fn_blocks /\
    EVERY (\bb. EVERY (\inst.
      inst_targets callee.fn_name inst ==>
      ALL_DISTINCT inst.inst_outputs)
      bb.bb_instructions) caller.fn_blocks /\
    EVERY (\bb. EVERY (\inst.
      inst_targets callee.fn_name inst ==>
      EVERY (\op. !v. op = Var v ==> ~MEM v inst.inst_outputs)
        (TL inst.inst_operands))
      bb.bb_instructions) caller.fn_blocks /\
    s.vs_prev_bb = NONE /\
    s.vs_inst_idx = 0 /\
    FDOM s.vs_labels = {} /\
    ~s.vs_halted /\
    (!bb inst x. MEM bb caller.fn_blocks /\
                 MEM inst bb.bb_instructions /\
                 MEM (Var x) inst.inst_operands ==> x NOTIN excl_vars) /\
    (!v. isPREFIX (inline_prefix ist.is_inline_count) v ==> v IN excl_vars) /\
    (!bb inst lbl. MEM bb caller.fn_blocks /\
                   MEM inst bb.bb_instructions /\
                   MEM (Label lbl) inst.inst_operands ==>
                   MEM lbl (fn_labels caller)) ==>
    ?fuel'.
      lift_result (state_equiv excl_vars) shared_globals_np
        (run_function fuel ctx caller s)
        (run_function fuel' ctx caller' s)
Proof
  rpt gen_tac >> strip_tac >>
  (* Step 1: Unfold inline_one_site, case-split, abbreviate *)
  fs[inline_one_site_def, LET_THM] >>
  Cases_on `find_invoke_site callee.fn_name caller.fn_blocks` >> fs[] >>
  PairCases_on `x` >> fs[] >>
  rename1 `find_invoke_site _ _ = SOME (call_lbl, call_idx)` >>
  Cases_on `lookup_block
    (return_block_label (inline_prefix ist.is_inline_count)
       ist.is_label_counter)
    (inline_call_site (inline_prefix ist.is_inline_count)
       (return_block_label (inline_prefix ist.is_inline_count)
          ist.is_label_counter) caller callee call_lbl call_idx).fn_blocks` >>
  fs[] >- (
    imp_res_tac find_invoke_site_lookup >>
    mp_tac inline_call_site_has_ret_bb >>
    disch_then (qspecl_then [`inline_prefix ist.is_inline_count`,
      `return_block_label (inline_prefix ist.is_inline_count)
         ist.is_label_counter`,
      `caller`, `callee`, `call_lbl`, `call_idx`] mp_tac) >>
    simp[]
  ) >>
  rename1 `lookup_block _ _ = SOME ret_bb` >>
  qabbrev_tac `prefix = inline_prefix ist.is_inline_count` >>
  qabbrev_tac `ret_lbl = return_block_label prefix ist.is_label_counter` >>
  qabbrev_tac `fn_inl = inline_call_site prefix ret_lbl caller callee call_lbl call_idx` >>
  qabbrev_tac `caller_xf = fix_inline_phis call_lbl ret_lbl ret_bb fn_inl` >>
  (* Step 2: Establish fn_no_alloca chain (Abbrev-safe) *)
  `fn_no_alloca fn_inl` by (
    qpat_assum `Abbrev (fn_inl = _)` mp_tac >>
    qpat_assum `fn_no_alloca caller` mp_tac >>
    qpat_assum `fn_no_alloca callee` mp_tac >>
    rpt (pop_assum kall_tac) >> rpt strip_tac >>
    gvs[markerTheory.Abbrev_def] >>
    irule inline_call_site_no_alloca >> simp[]) >>
  `fn_no_alloca caller_xf` by (
    qpat_assum `Abbrev (caller_xf = _)` mp_tac >>
    qpat_assum `fn_no_alloca fn_inl` mp_tac >>
    rpt (pop_assum kall_tac) >> rpt strip_tac >>
    gvs[markerTheory.Abbrev_def] >>
    irule fix_inline_phis_no_alloca >> simp[]) >>
  (* Step 3: Factor out renumber *)
  `!f s'. run_function f ctx (renumber_fn_inst_ids caller_xf) s' =
          run_function f ctx caller_xf s'` by
    (rpt strip_tac >> irule renumber_fn_inst_ids_correct >> simp[]) >>
  pop_assum (fn ren_th =>
    PAT_X_ASSUM ``renumber_fn_inst_ids _ = _`` (fn eq =>
      SUBST_ALL_TAC (SYM eq)) >>
    REWRITE_TAC[ren_th]) >>
  (* Step 4: Strengthen with two-state invariant *)
  `!fuel s1 s2.
     execution_equiv excl_vars s1 s2 /\
     s1.vs_current_bb = s2.vs_current_bb /\
     s1.vs_inst_idx = 0 /\ s2.vs_inst_idx = 0 /\
     FDOM s1.vs_labels = {} /\
     ~s1.vs_halted /\
     ((s1.vs_prev_bb = s2.vs_prev_bb /\
       s1.vs_prev_bb <> SOME ret_lbl /\
       (MEM s1.vs_current_bb (bb_succs ret_bb) ==>
        s1.vs_prev_bb <> SOME call_lbl)) \/
      (s1.vs_prev_bb = SOME call_lbl /\ s2.vs_prev_bb = SOME ret_lbl /\
       MEM s1.vs_current_bb (bb_succs ret_bb))) ==>
     ?fuel'.
       lift_result (state_equiv excl_vars) shared_globals_np
         (run_function fuel ctx caller s1)
         (run_function fuel' ctx caller_xf s2)` suffices_by (
    disch_then (qspecl_then [`fuel`, `s`, `s`] mp_tac) >>
    simp[execution_equiv_refl]
  ) >>
  (* Step 5: Induction on fuel *)
  Induct_on `fuel` >- (
    rpt strip_tac >> qexists_tac `0` >>
    ONCE_REWRITE_TAC[run_function_def] >> simp[lift_result_def]
  ) \\
  rpt gen_tac >> DISCH_TAC >>
  pop_assum CONJ_ASSUME_TAC >>
  Cases_on `lookup_block s1.vs_current_bb caller.fn_blocks` >- (
    qexists_tac `0` >>
    ONCE_REWRITE_TAC[run_function_def] >> simp[lift_result_def]
  ) >>
  rename1 `_ = SOME bb` >>
  (* Step 6: Case split — call site vs non-call-site *)
  reverse (Cases_on `s1.vs_current_bb = call_lbl`) >- (
    (* ===== NON-CALL-SITE BLOCK ===== *)
    `lookup_block s1.vs_current_bb fn_inl.fn_blocks = SOME bb` by (
      qunabbrev_tac `fn_inl` >>
      irule lookup_block_inline_call_site_neq >> simp[]) >>
    `bb_well_formed bb` by
      (imp_res_tac lookup_block_MEM >> fs[EVERY_MEM]) >>
    qabbrev_tac `bb2 =
      if MEM s1.vs_current_bb (bb_succs ret_bb) then
        bb with bb_instructions :=
          MAP (\inst. if inst.inst_opcode <> PHI then inst
                      else subst_label_inst call_lbl ret_lbl inst)
              bb.bb_instructions
      else bb` >>
    `lookup_block s1.vs_current_bb caller_xf.fn_blocks = SOME bb2` by (
      qunabbrev_tac `bb2` >> qunabbrev_tac `caller_xf` >>
      qunabbrev_tac `fn_inl` >>
      PURE_REWRITE_TAC[lookup_block_fix_inline_phis] >>
      qpat_x_assum `lookup_block _ (inline_call_site _ _ _ _ _ _).fn_blocks = SOME bb`
        (fn h => PURE_REWRITE_TAC[h, optionTheory.option_case_def]) >>
      BETA_TAC >> IF_CASES_TAC >> rewrite_tac[]) >>
    `~MEM ret_lbl (fn_labels caller)` by (
      qunabbrev_tac `ret_lbl` >> qunabbrev_tac `prefix` >>
      rewrite_tac[return_block_label_def] >>
      irule prefixed_label_not_in_labels >>
      first_assum ACCEPT_TAC) >>
    `~MEM (Label ret_lbl)
       (FLAT (MAP (\i. i.inst_operands) bb.bb_instructions))` by (
      strip_tac >>
      `MEM bb caller.fn_blocks` by metis_tac[lookup_block_MEM] >>
      fs[MEM_FLAT, MEM_MAP] >>
      qpat_x_assum `!bb inst lbl. _` imp_res_tac >> metis_tac[]) >>
    `!inst'. MEM inst' bb.bb_instructions ==>
             !x. MEM (Var x) inst'.inst_operands ==> x NOTIN excl_vars` by (
      rpt strip_tac >>
      `MEM bb caller.fn_blocks` by metis_tac[lookup_block_MEM] >>
      metis_tac[]) >>
    (* Block-level simulation via non_call_block_sim *)
    `s1.vs_inst_idx = s2.vs_inst_idx` by gvs[] >>
    `result_equiv excl_vars (run_block fuel ctx bb s1)
       (run_block fuel ctx bb2 s2)` by (
      qunabbrev_tac `bb2` >>
      irule non_call_block_sim >>
      rpt conj_tac >> TRY (first_assum ACCEPT_TAC)) >>
    `lift_result (state_equiv excl_vars) shared_globals_np
       (run_block fuel ctx bb s1) (run_block fuel ctx bb2 s2)` by
      metis_tac[result_equiv_weaken_terminal] >>
    `lookup_block s2.vs_current_bb caller_xf.fn_blocks = SOME bb2` by (
      qpat_x_assum `s1.vs_current_bb = s2.vs_current_bb`
        (fn h => rewrite_tac[GSYM h]) >>
      first_assum ACCEPT_TAC) >>
    (* Lift to function level *)
    mp_tac (Q.SPECL [`fuel`, `ctx`, `caller`, `caller_xf`,
                      `bb`, `bb2`, `s1`, `s2`, `excl_vars`]
                     run_function_sim_step_gen) >>
    disch_then match_mp_tac >>
    rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
    (* Continuation: apply IH *)
    rpt strip_tac >>
    `s1'.vs_inst_idx = 0` by metis_tac[run_block_OK_inst_idx_0] >>
    `s2'.vs_inst_idx = 0` by metis_tac[run_block_OK_inst_idx_0] >>
    `state_equiv excl_vars s1' s2'` by (
      qpat_x_assum `lift_result _ _ _ _` mp_tac >>
      qpat_x_assum `run_block _ _ _ s1 = _` (fn h => rewrite_tac[h]) >>
      qpat_x_assum `run_block _ _ _ s2 = _` (fn h => rewrite_tac[h]) >>
      rewrite_tac[lift_result_def] >> strip_tac) >>
    `execution_equiv excl_vars s1' s2' /\
     s1'.vs_current_bb = s2'.vs_current_bb /\
     s1'.vs_prev_bb = s2'.vs_prev_bb` by (
      qpat_x_assum `state_equiv _ _ _` mp_tac >>
      rewrite_tac[state_equiv_def] >> strip_tac >>
      rpt conj_tac >> first_assum ACCEPT_TAC) >>
    `bb_well_formed bb2` by (
      qunabbrev_tac `bb2` >>
      irule bb_well_formed_phi_subst >> first_assum ACCEPT_TAC) >>
    `s1'.vs_prev_bb = SOME s1.vs_current_bb` by
      metis_tac[run_block_ok_prev_bb_wf] >>
    `s2'.vs_prev_bb = SOME s2.vs_current_bb` by
      metis_tac[run_block_ok_prev_bb_wf] >>
    `MEM s1.vs_current_bb (fn_labels caller)` by (
      imp_res_tac lookup_block_MEM_labels >>
      rewrite_tac[fn_labels_def] >> first_assum ACCEPT_TAC) >>
    `s1.vs_current_bb <> ret_lbl` by (
      strip_tac >> pop_assum SUBST_ALL_TAC >> res_tac) >>
    `FDOM s1'.vs_labels = {}` by
      (imp_res_tac run_block_preserves_labels >> gvs[]) >>
    first_x_assum irule >>
    rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
    disj1_tac >> rpt conj_tac >> TRY (first_assum ACCEPT_TAC)
    >- (
      qpat_assum `s1'.vs_prev_bb = SOME _` (fn h => rewrite_tac[h]) >>
      rewrite_tac[optionTheory.SOME_11] >> first_assum ACCEPT_TAC)
    >- (
      strip_tac >>
      qpat_assum `s1'.vs_prev_bb = SOME _` (fn h => rewrite_tac[h]) >>
      rewrite_tac[optionTheory.SOME_11] >> first_assum ACCEPT_TAC)
  ) >>
  (* ===== CALL-SITE BLOCK ===== *)
  suspend "call_site"
QED

(* Generalization of run_function_no_phi_entry_prev_bb_eq to all fuel values.
   For fuel=0 both sides are Error; for SUC n use the existing theorem. *)
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

(* Helper: run_block on truncated block with JMP gives jump_to result.
   Extracted from the call-site continuation to avoid rich-context issues. *)
Triviality trunc_bb_jmp_result[local]:
  !fuel ctx bb s call_idx s_pre jmp_inst clone_entry_lbl orig_insts.
    run_block_reaches fuel ctx bb s call_idx = SOME s_pre /\
    bb.bb_instructions = TAKE call_idx orig_insts ++ [jmp_inst] /\
    jmp_inst.inst_opcode = JMP /\
    jmp_inst.inst_operands = [Label clone_entry_lbl] /\
    jmp_inst.inst_outputs = [] /\
    s.vs_inst_idx = 0 /\
    call_idx < LENGTH orig_insts /\
    ~s_pre.vs_halted /\
    bb_well_formed bb ==>
    run_block fuel ctx bb s = OK (jump_to clone_entry_lbl s_pre) /\
    ~(jump_to clone_entry_lbl s_pre).vs_halted
Proof
  rpt gen_tac >> strip_tac >>
  `s_pre.vs_inst_idx = s.vs_inst_idx + call_idx`
    by metis_tac[run_block_reaches_inst_idx] >>
  `s_pre.vs_inst_idx = call_idx` by simp[] >>
  `s_pre.vs_inst_idx < LENGTH bb.bb_instructions` by simp[] >>
  drule_all run_block_decompose_at >> strip_tac >>
  `EL s_pre.vs_inst_idx bb.bb_instructions = jmp_inst` by
    simp[EL_APPEND2, LENGTH_TAKE] >>
  `step_inst fuel ctx jmp_inst s_pre = step_inst_base jmp_inst s_pre` by (
    irule step_inst_non_invoke >> simp[]) >>
  `step_inst_base jmp_inst s_pre = OK (jump_to clone_entry_lbl s_pre)` by
    simp[step_inst_base_def, jump_to_def] >>
  rpt conj_tac
  >- (
    `is_terminator JMP` by EVAL_TAC >>
    gvs[jump_to_def])
  >- simp[jump_to_def]
QED

Triviality step_inst_base_phi_no_prev[local]:
  !inst s. inst.inst_opcode = PHI /\ s.vs_prev_bb = NONE ==>
    ?e. step_inst_base inst s = Error e
Proof
  rpt strip_tac >>
  ONCE_REWRITE_TAC[step_inst_base_def] >> simp[] >>
  Cases_on `inst.inst_outputs` >> simp[] >>
  Cases_on `t` >> simp[]
QED

(* Helper: if callee entry has PHI and setup_callee succeeds (prev_bb=NONE),
   run_function on callee returns Error. *)
Triviality entry_phi_callee_errors[local]:
  !fuel ctx callee args s callee_s.
    setup_callee callee args s = SOME callee_s /\
    EVERY bb_well_formed callee.fn_blocks /\
    ~EVERY (\inst. inst.inst_opcode <> PHI)
       (HD callee.fn_blocks).bb_instructions ==>
    ?e. run_function (SUC fuel) ctx callee callee_s = Error e
Proof
  rpt strip_tac >>
  `callee.fn_blocks <> []` by (
    gvs[setup_callee_def] >> Cases_on `callee.fn_blocks` >> gvs[]) >>
  `callee_s.vs_current_bb = (HD callee.fn_blocks).bb_label` by
    (gvs[setup_callee_def] >> Cases_on `callee.fn_blocks` >> gvs[]) >>
  `callee_s.vs_prev_bb = NONE` by
    (gvs[setup_callee_def] >> Cases_on `callee.fn_blocks` >> gvs[]) >>
  `callee_s.vs_inst_idx = 0` by
    (gvs[setup_callee_def] >> Cases_on `callee.fn_blocks` >> gvs[]) >>
  (* Lookup entry block = HD callee.fn_blocks *)
  `lookup_block callee_s.vs_current_bb callee.fn_blocks =
   SOME (HD callee.fn_blocks)` by (
    simp[lookup_block_def] >>
    Cases_on `callee.fn_blocks` >> gvs[FIND_thm]) >>
  qabbrev_tac `entry_bb = HD callee.fn_blocks` >>
  `bb_well_formed entry_bb` by (
    qunabbrev_tac `entry_bb` >>
    Cases_on `callee.fn_blocks` >> gvs[EVERY_MEM]) >>
  (* Entry block has PHI at some index *)
  `?j. j < LENGTH entry_bb.bb_instructions /\
       entry_bb.bb_instructions❲j❳.inst_opcode = PHI` by (
    gvs[NOT_EVERY_EXISTS_FIRST] >> metis_tac[]) >>
  (* bb_well_formed: PHI forms prefix, so index 0 is also PHI *)
  `(EL 0 entry_bb.bb_instructions).inst_opcode = PHI` by (
    Cases_on `j` >> gvs[] >>
    gvs[bb_well_formed_def] >>
    first_x_assum (qspecl_then [`0`, `SUC n`] mp_tac) >> simp[]) >>
  (* Unfold run_function *)
  ONCE_REWRITE_TAC[run_function_def] >> simp[] >>
  `get_instruction entry_bb 0 = SOME (EL 0 entry_bb.bb_instructions)` by (
    simp[get_instruction_def] >>
    gvs[bb_well_formed_def] >>
    Cases_on `entry_bb.bb_instructions` >> gvs[]) >>
  ONCE_REWRITE_TAC[run_block_def] >> simp[] >>
  `?e. step_inst fuel ctx (HD entry_bb.bb_instructions) callee_s = Error e` by (
    `(HD entry_bb.bb_instructions).inst_opcode = PHI` by (
      Cases_on `entry_bb.bb_instructions` >> gvs[]) >>
    `step_inst fuel ctx (HD entry_bb.bb_instructions) callee_s =
     step_inst_base (HD entry_bb.bb_instructions) callee_s` by (
      irule step_inst_non_invoke >> simp[]) >>
    pop_assum SUBST1_TAC >>
    metis_tac[step_inst_base_phi_no_prev]) >>
  simp[]
QED

(* When step_inst on the invoke returns Error, the original run_function
   also returns Error. Pick fuel'=0 for transformed side → also Error.
   lift_result on (Error, Error) is trivially true. *)
Triviality invoke_step_error_sim[local]:
  !fuel ctx caller caller_xf bb s1 s2 invoke_inst s1_pre call_idx err_msg
   excl_vars.
    lookup_block s1.vs_current_bb caller.fn_blocks = SOME bb /\
    s1.vs_inst_idx = 0 /\
    run_block_reaches fuel ctx bb s1 call_idx = SOME s1_pre /\
    run_block fuel ctx bb s1 =
      (let inst = EL s1_pre.vs_inst_idx bb.bb_instructions in
       case step_inst fuel ctx inst s1_pre of
         OK s'' =>
           if is_terminator inst.inst_opcode then
             if s''.vs_halted then Halt s'' else OK s''
           else run_block fuel ctx bb (s'' with vs_inst_idx := SUC s1_pre.vs_inst_idx)
       | Halt s' => Halt s'
       | Abort a s' => Abort a s'
       | IntRet vals s' => IntRet vals s'
       | Error e => Error e) /\
    s1_pre.vs_inst_idx = call_idx /\
    EL s1_pre.vs_inst_idx bb.bb_instructions = invoke_inst /\
    step_inst fuel ctx invoke_inst s1_pre = Error err_msg ==>
    ?fuel'.
      lift_result (state_equiv excl_vars) shared_globals_np
        (run_function (SUC fuel) ctx caller s1)
        (run_function fuel' ctx caller_xf s2)
Proof
  rpt strip_tac >>
  qexists_tac `0` >>
  (* Original: run_function (SUC fuel) = Error *)
  ONCE_REWRITE_TAC[run_function_def] >> simp[] >>
  qpat_x_assum `run_block _ _ bb s1 = _` SUBST1_TAC >>
  simp[] >>
  (* Transformed: run_function 0 = Error "out of fuel" *)
  ONCE_REWRITE_TAC[run_function_def] >> simp[lift_result_def]
QED

Triviality run_block_reaches_preserves_halted[local]:
  !k fuel ctx bb s s'.
    run_block_reaches fuel ctx bb s k = SOME s' /\
    (!i. s.vs_inst_idx <= i /\ i < s.vs_inst_idx + k ==>
         ~is_terminator (EL i bb.bb_instructions).inst_opcode) ==>
    (s'.vs_halted <=> s.vs_halted)
Proof
  Induct >- simp[run_block_reaches_def] >>
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `run_block_reaches _ _ _ _ (SUC _) = _` mp_tac >>
  simp[run_block_reaches_def] >>
  BasicProvers.EVERY_CASE_TAC >> simp[] >>
  strip_tac >>
  `~is_terminator x.inst_opcode` by (
    first_x_assum (qspec_then `s.vs_inst_idx` mp_tac) >> simp[]) >>
  gvs[] >>
  `(v.vs_halted <=> s.vs_halted)` by metis_tac[step_preserves_halted] >>
  `s'.vs_halted <=> v.vs_halted` by (
    first_x_assum (qspecl_then [`fuel`, `ctx`, `bb`,
      `v with vs_inst_idx := SUC s.vs_inst_idx`, `s'`] mp_tac) >>
    simp[] >> disch_then irule >>
    rpt strip_tac >> first_x_assum (qspec_then `i` mp_tac) >> simp[]) >>
  simp[]
QED

Triviality step_inst_invoke_not_intret[local]:
  !fuel ctx inst s vals s'.
    inst.inst_opcode = INVOKE /\
    step_inst fuel ctx inst s = IntRet vals s' ==> F
Proof
  rpt strip_tac >>
  gvs[step_inst_def] >>
  BasicProvers.EVERY_CASE_TAC >> gvs[]
QED

(* Unified INVOKE decomposition: for ANY non-Error step_inst result,
   gives common facts (decode, lookup, eval, setup) plus callee run_function.
   Replaces the three separate halt/abort/ok decomposition lemmas. *)
Triviality step_inst_invoke_decompose[local]:
  !fuel ctx inst s.
    inst.inst_opcode = INVOKE /\
    (!e. step_inst fuel ctx inst s <> Error e) ==>
    ?callee_name arg_ops callee_fn args callee_s.
      decode_invoke inst = SOME (callee_name, arg_ops) /\
      lookup_function callee_name ctx.ctx_functions = SOME callee_fn /\
      eval_operands arg_ops s = SOME args /\
      setup_callee callee_fn args s = SOME callee_s /\
      (case run_function fuel ctx callee_fn callee_s of
         Halt s_halt => step_inst fuel ctx inst s = Halt s_halt
       | Abort ab s_ab => step_inst fuel ctx inst s = Abort ab s_ab
       | IntRet vals cs =>
           (case bind_outputs inst.inst_outputs vals
                   (merge_callee_state s cs) of
              NONE => step_inst fuel ctx inst s =
                      Error "invoke: return arity mismatch"
            | SOME s_ok => step_inst fuel ctx inst s = OK s_ok)
       | _ => T)
Proof
  rpt strip_tac >>
  gvs[step_inst_def] >>
  BasicProvers.EVERY_CASE_TAC >> gvs[]
QED

(* find_invoke_idx: SOME idx implies inst_targets at that index *)
Triviality find_invoke_idx_inst_targets[local]:
  !name insts n idx.
    find_invoke_idx name insts n = SOME idx ==>
    n <= idx /\ idx - n < LENGTH insts /\
    inst_targets name (EL (idx - n) insts)
Proof
  Induct_on `insts` >> simp[find_invoke_idx_def] >>
  rpt gen_tac >> IF_CASES_TAC >> strip_tac >> gvs[]
  >- gvs[inst_targets_def]
  >> first_x_assum drule >> strip_tac >>
  `idx - n = SUC (idx - (n + 1))` by simp[] >> simp[]
QED

(* find_invoke_site gives inst_targets at the found location *)
Triviality find_invoke_site_inst_targets[local]:
  !callee_name bbs lbl idx.
    find_invoke_site callee_name bbs = SOME (lbl, idx) /\
    ALL_DISTINCT (MAP (\b. b.bb_label) bbs) ==>
    ?bb. lookup_block lbl bbs = SOME bb /\
         idx < LENGTH bb.bb_instructions /\
         inst_targets callee_name (EL idx bb.bb_instructions)
Proof
  Induct_on `bbs` >> simp[find_invoke_site_def] >>
  rpt gen_tac >>
  Cases_on `find_invoke_idx callee_name h.bb_instructions 0` >> simp[] >>
  strip_tac >> gvs[]
  >- (
    (* Recursive case: found in rest *)
    first_x_assum drule >> strip_tac >>
    qexists_tac `bb` >> simp[] >>
    `h.bb_label <> lbl` by (
      spose_not_then assume_tac >> fs[] >>
      imp_res_tac lookup_block_MEM >>
      imp_res_tac lookup_block_label >> fs[] >>
      metis_tac[MEM_MAP]) >>
    fs[lookup_block_def, FIND_thm]
  )
  >- (
    (* Base case: found in h *)
    qexists_tac `h` >>
    simp[lookup_block_def, FIND_thm] >>
    imp_res_tac find_invoke_idx_inst_targets >> gvs[]
  )
QED

(* MEM bb bbs ∧ MEM inst bb.bb_instructions ⇒ MEM inst (fn_insts_blocks bbs) *)
Triviality mem_fn_insts_blocks[local]:
  !inst bb bbs.
    MEM bb bbs /\ MEM inst bb.bb_instructions ==>
    MEM inst (fn_insts_blocks bbs)
Proof
  Induct_on `bbs` >> simp[fn_insts_blocks_def] >> metis_tac[MEM_APPEND]
QED

(* Contrapositive: if step_inst doesn't error, callee doesn't error *)
Triviality invoke_callee_no_error[local]:
  !fuel ctx inst s callee_name arg_ops callee args callee_s.
    inst.inst_opcode = INVOKE /\
    decode_invoke inst = SOME (callee_name, arg_ops) /\
    lookup_function callee_name ctx.ctx_functions = SOME callee /\
    eval_operands arg_ops s = SOME args /\
    setup_callee callee args s = SOME callee_s /\
    (!e. step_inst fuel ctx inst s <> Error e) ==>
    (!e. run_function fuel ctx callee callee_s <> Error e)
Proof
  rpt strip_tac >>
  first_x_assum (qspec_then `e` mp_tac) >>
  simp[step_inst_def] >> fs[]
QED

Resume inline_one_site_fn_correct[call_site]:
  (* Phase 0: Establish structural facts about call site *)
  `bb_well_formed bb` by
    (imp_res_tac lookup_block_MEM >> fs[EVERY_MEM]) >>
  qpat_x_assum `ALL_DISTINCT (fn_labels _)` mp_tac >>
  rewrite_tac[fn_labels_def] >> strip_tac >>
  imp_res_tac find_invoke_site_lookup >>
  `bb' = bb` by fs[] >>
  pop_assum (fn h => RULE_ASSUM_TAC (REWRITE_RULE [h])) >>
  `call_idx < LENGTH bb.bb_instructions` by (
    irule find_invoke_site_idx_bound >> simp[] >> metis_tac[]) >>
  `(EL call_idx bb.bb_instructions).inst_opcode = INVOKE` by (
    irule find_invoke_site_opcode >> simp[] >> metis_tac[]) >>
  imp_res_tac invoke_not_last_inst >>
  qabbrev_tac `invoke_inst = EL call_idx bb.bb_instructions` >>
  (* Phase 1: Case on whether prefix reaches the INVOKE *)
  Cases_on `run_block_reaches fuel ctx bb s1 call_idx`
  >- (
    (* Prefix fails: rewrite original via pre_invoke_prefix_fail,
       then apply non_call_block_sim on truncated block,
       then run_function_sim_step_gen for function level. *)
    (* PF1: Concrete truncated block from fn_inlined *)
    qabbrev_tac `clone_entry_lbl =
      case (clone_function prefix callee).fn_blocks of
        [] => "" | eb::_ => eb.bb_label` >>
    qabbrev_tac `jmp_inst =
      <|inst_id := 0; inst_opcode := JMP;
        inst_operands := [Label clone_entry_lbl];
        inst_outputs := []|>` >>
    qabbrev_tac `bb_trunc = bb with bb_instructions :=
      TAKE call_idx bb.bb_instructions ++ [jmp_inst]` >>
    (* PF2: lookup in fn_inl gives bb_trunc *)
    `lookup_block call_lbl fn_inl.fn_blocks = SOME bb_trunc` by (
      qunabbrev_tac `bb_trunc` >> qunabbrev_tac `jmp_inst` >>
      qunabbrev_tac `clone_entry_lbl` >> qunabbrev_tac `fn_inl` >>
      irule lookup_block_call_lbl_fn_inlined >>
      simp[fn_labels_def]) >>
    (* PF3: lookup in caller_xf gives phi_subst_or_id of bb_trunc *)
    `lookup_block call_lbl caller_xf.fn_blocks =
       SOME (if MEM call_lbl (bb_succs ret_bb)
             then bb_trunc with bb_instructions :=
               MAP (\inst. if inst.inst_opcode <> PHI then inst
                           else subst_label_inst call_lbl ret_lbl inst)
                   bb_trunc.bb_instructions
             else bb_trunc)` by (
      qunabbrev_tac `caller_xf` >>
      PURE_REWRITE_TAC[lookup_block_fix_inline_phis] >>
      qpat_x_assum `lookup_block call_lbl fn_inl.fn_blocks = SOME bb_trunc`
        (fn h => PURE_REWRITE_TAC[h, optionTheory.option_case_def]) >>
      BETA_TAC >> IF_CASES_TAC >> rewrite_tac[]) >>
    qabbrev_tac `trunc_bb2 =
      if MEM call_lbl (bb_succs ret_bb)
      then bb_trunc with bb_instructions :=
        MAP (\inst. if inst.inst_opcode <> PHI then inst
                    else subst_label_inst call_lbl ret_lbl inst)
            bb_trunc.bb_instructions
      else bb_trunc` >>
    (* PF4: run_block on bb = run_block on bb_trunc (prefix fails) *)
    `run_block fuel ctx bb s1 = run_block fuel ctx bb_trunc s1` by (
      qunabbrev_tac `bb_trunc` >>
      irule pre_invoke_prefix_fail >> simp[]) >>
    (* PF5: Establish conditions for non_call_block_sim *)
    `~MEM ret_lbl (fn_labels caller)` by (
      qunabbrev_tac `ret_lbl` >> qunabbrev_tac `prefix` >>
      rewrite_tac[return_block_label_def] >>
      irule prefixed_label_not_in_labels >>
      first_assum ACCEPT_TAC) >>
    `clone_entry_lbl <> ret_lbl` by (
      qunabbrev_tac `clone_entry_lbl` >> qunabbrev_tac `ret_lbl` >>
      qunabbrev_tac `prefix` >>
      mp_tac (Q.SPECL [`inline_prefix ist.is_inline_count`,
        `callee`, `ist.is_label_counter`] cloned_entry_neq_ret_lbl) >>
      simp[]) >>
    `jmp_inst.inst_operands = [Label clone_entry_lbl]` by
      (qunabbrev_tac `jmp_inst` >> simp[]) >>
    mp_tac (Q.SPECL [`bb`, `caller`, `call_lbl`, `call_idx`,
      `jmp_inst`, `ret_lbl`, `excl_vars`] trunc_block_label_ops) >>
    impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC) >>
    strip_tac >>
    (* PF6: result_equiv between bb_trunc and trunc_bb2 *)
    `s1.vs_inst_idx = s2.vs_inst_idx` by simp[] >>
    `bb_trunc.bb_instructions =
       TAKE call_idx bb.bb_instructions ++ [jmp_inst]` by
      (qunabbrev_tac `bb_trunc` >> simp[]) >>
    `result_equiv excl_vars (run_block fuel ctx bb_trunc s1)
       (run_block fuel ctx trunc_bb2 s2)` by (
      qpat_x_assum `Abbrev (trunc_bb2 = _)`
        (SUBST1_TAC o REWRITE_RULE[markerTheory.Abbrev_def]) >>
      irule non_call_block_sim >> fs[] >>
      rpt conj_tac >> TRY (first_assum ACCEPT_TAC)) >>
    `lift_result (state_equiv excl_vars) shared_globals_np
       (run_block fuel ctx bb s1) (run_block fuel ctx trunc_bb2 s2)` by
      metis_tac[result_equiv_weaken_terminal] >>
    (* PF7: lookup_block for run_function_sim_step_gen *)
    `lookup_block s2.vs_current_bb caller_xf.fn_blocks = SOME trunc_bb2` by (
      `s2.vs_current_bb = call_lbl` by
        (qpat_x_assum `s1.vs_current_bb = s2.vs_current_bb` (SUBST1_TAC o SYM) >>
         first_assum ACCEPT_TAC) >>
      gvs[]) >>
    mp_tac (Q.SPECL [`fuel`, `ctx`, `caller`, `caller_xf`,
      `bb`, `trunc_bb2`, `s1`, `s2`, `excl_vars`]
      run_function_sim_step_gen) >>
    disch_then match_mp_tac >>
    rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
    (* PF8: Continuation vacuous — prefix fails so run_block bb s1 <> OK *)
    rpt strip_tac >>
    `!s'. run_block fuel ctx bb s1 <> OK s'` by (
      mp_tac (Q.SPECL [`call_idx`, `fuel`, `ctx`, `bb`, `s1`]
        run_block_reaches_none_non_ok) >>
      impl_tac >- (
        rpt conj_tac >> TRY (first_assum ACCEPT_TAC)
        >- simp[]
        >- (rpt strip_tac >> imp_res_tac pre_invoke_non_terminator)) >>
      simp[]) >>
    metis_tac[]
  ) >>
  (* ===== CALL-SITE, PREFIX SUCCEEDS ===== *)
  rename1 `run_block_reaches _ _ _ _ _ = SOME s1_pre` >>
  imp_res_tac run_block_reaches_inst_idx >>
  `s1_pre.vs_inst_idx = call_idx` by gvs[] >>
  `s1_pre.vs_inst_idx < LENGTH bb.bb_instructions` by simp[] >>
  drule_all run_block_decompose_at >> strip_tac >>
  `EL s1_pre.vs_inst_idx bb.bb_instructions = invoke_inst` by
    (gvs[markerTheory.Abbrev_def]) >>
  qabbrev_tac `clone_entry_lbl =
    case (clone_function prefix callee).fn_blocks of
      [] => "" | eb::_ => eb.bb_label` >>
  qabbrev_tac `jmp_inst =
    <|inst_id := 0; inst_opcode := JMP;
      inst_operands := [Label clone_entry_lbl];
      inst_outputs := []|>` >>
  qabbrev_tac `bb_trunc = bb with bb_instructions :=
    TAKE call_idx bb.bb_instructions ++ [jmp_inst]` >>
  `lookup_block call_lbl fn_inl.fn_blocks = SOME bb_trunc` by (
    qunabbrev_tac `bb_trunc` >> qunabbrev_tac `jmp_inst` >>
    qunabbrev_tac `clone_entry_lbl` >> qunabbrev_tac `fn_inl` >>
    irule lookup_block_call_lbl_fn_inlined >>
    simp[fn_labels_def]) >>
  `~MEM ret_lbl (fn_labels caller)` by (
    qunabbrev_tac `ret_lbl` >> qunabbrev_tac `prefix` >>
    rewrite_tac[return_block_label_def] >>
    irule prefixed_label_not_in_labels >>
    first_assum ACCEPT_TAC) >>
  qabbrev_tac `trunc_bb2 =
    if MEM call_lbl (bb_succs ret_bb)
    then bb_trunc with bb_instructions :=
      MAP (\inst. if inst.inst_opcode <> PHI then inst
                  else subst_label_inst call_lbl ret_lbl inst)
          bb_trunc.bb_instructions
    else bb_trunc` >>
  `lookup_block call_lbl caller_xf.fn_blocks = SOME trunc_bb2` by (
    qunabbrev_tac `trunc_bb2` >> qunabbrev_tac `caller_xf` >>
    PURE_REWRITE_TAC[lookup_block_fix_inline_phis] >>
    qpat_x_assum `lookup_block call_lbl fn_inl.fn_blocks = SOME bb_trunc`
      (fn h => PURE_REWRITE_TAC[h, optionTheory.option_case_def]) >>
    BETA_TAC >> IF_CASES_TAC >> rewrite_tac[]) >>
  `clone_entry_lbl <> ret_lbl` by (
    qunabbrev_tac `clone_entry_lbl` >> qunabbrev_tac `ret_lbl` >>
    qunabbrev_tac `prefix` >>
    mp_tac (Q.SPECL [`inline_prefix ist.is_inline_count`,
      `callee`, `ist.is_label_counter`] cloned_entry_neq_ret_lbl) >>
    simp[]) >>
  `jmp_inst.inst_operands = [Label clone_entry_lbl]` by
    (qunabbrev_tac `jmp_inst` >> simp[]) >>
  `~MEM (Label ret_lbl)
     (FLAT (MAP (\i. i.inst_operands) bb.bb_instructions))` by (
    strip_tac >>
    `MEM bb caller.fn_blocks` by metis_tac[lookup_block_MEM] >>
    fs[MEM_FLAT, MEM_MAP] >>
    qpat_x_assum `!bb inst lbl. _` imp_res_tac >> metis_tac[]) >>
  `!inst'. MEM inst' bb.bb_instructions ==>
           !x. MEM (Var x) inst'.inst_operands ==> x NOTIN excl_vars` by (
    rpt strip_tac >>
    `MEM bb caller.fn_blocks` by metis_tac[lookup_block_MEM] >>
    metis_tac[]) >>
  `!i. i < call_idx ==>
       ~is_terminator (EL i bb.bb_instructions).inst_opcode` by (
    rpt strip_tac >> imp_res_tac pre_invoke_non_terminator) >>
  (* Phase CS6: MEM case — phi substitution *)
  Cases_on `MEM call_lbl (bb_succs ret_bb)` >- (
    suspend "mem_case") >>
  (* Phase CS6: ¬MEM case — same block *)
  `trunc_bb2 = bb_trunc` by (qunabbrev_tac `trunc_bb2` >> simp[]) >>
  `s1.vs_prev_bb = s2.vs_prev_bb` by (
    qpat_x_assum `_ \/ _` mp_tac >> strip_tac >> gvs[]) >>
  mp_tac (Q.SPECL [`call_idx`, `fuel`, `ctx`, `excl_vars`, `bb`,
    `s1`, `s2`, `s1_pre`] run_block_reaches_same_block_equiv) >>
  impl_tac >- (
    simp[] >>
    metis_tac[pre_invoke_non_terminator]) >>
  strip_tac >>
  `run_block_reaches fuel ctx bb s2 call_idx =
   run_block_reaches fuel ctx bb_trunc s2 call_idx` by (
    qunabbrev_tac `bb_trunc` >>
    irule run_block_reaches_take_agree >> simp[]) >>
  `?s2_pre. run_block_reaches fuel ctx trunc_bb2 s2 call_idx = SOME s2_pre /\
     execution_equiv excl_vars s1_pre s2_pre /\
     s1_pre.vs_current_bb = s2_pre.vs_current_bb /\
     s1_pre.vs_inst_idx = s2_pre.vs_inst_idx /\
     FDOM s1_pre.vs_labels = {}` by
    (qexists_tac `s2'` >> gvs[]) >>
  (* CS7: Establish bb_well_formed *)
  `~is_terminator (EL call_idx bb.bb_instructions).inst_opcode` by
    (gvs[markerTheory.Abbrev_def] >> EVAL_TAC) >>
  `bb_well_formed bb_trunc` by (
    qunabbrev_tac `bb_trunc` >> qunabbrev_tac `jmp_inst` >>
    irule truncated_bb_well_formed >> simp[]) >>
  `bb_well_formed trunc_bb2` by fs[] >>
  (* CS7b: Derive ~s1_pre.vs_halted from ~s1.vs_halted + prefix preservation *)
  `~s1_pre.vs_halted` by (
    mp_tac (Q.SPECL [`call_idx`, `fuel`, `ctx`, `bb`, `s1`, `s1_pre`]
      run_block_reaches_preserves_halted) >>
    simp[] >> disch_then irule >>
    rpt strip_tac >> imp_res_tac pre_invoke_non_terminator) >>
  `~s2_pre.vs_halted` by (
    qpat_x_assum `execution_equiv _ s1_pre s2_pre` mp_tac >>
    simp[execution_equiv_def]) >>
  (* CS7c: Establish s2 side truncated block result = OK (jump_to ...) *)
  `trunc_bb2.bb_instructions = TAKE call_idx bb.bb_instructions ++ [jmp_inst]`
    by (fs[] >> qunabbrev_tac `bb_trunc` >> simp[]) >>
  `jmp_inst.inst_outputs = []` by (qunabbrev_tac `jmp_inst` >> simp[]) >>
  `jmp_inst.inst_opcode = JMP` by (qunabbrev_tac `jmp_inst` >> simp[]) >>
  `jmp_inst.inst_operands = [Label clone_entry_lbl]` by
    (qunabbrev_tac `jmp_inst` >> simp[]) >>
  `run_block fuel ctx trunc_bb2 s2 = OK (jump_to clone_entry_lbl s2_pre) /\
   ~(jump_to clone_entry_lbl s2_pre).vs_halted` by (
    mp_tac (Q.SPECL [`fuel`, `ctx`, `trunc_bb2`, `s2`, `call_idx`,
      `s2_pre`, `jmp_inst`, `clone_entry_lbl`, `bb.bb_instructions`]
      trunc_bb_jmp_result) >>
    simp[]) >>
  (* CS8: Establish inst_targets — needed by all non-error cases *)
  `inst_targets callee.fn_name invoke_inst` by (
    qunabbrev_tac `invoke_inst` >>
    mp_tac (Q.SPECL [`callee.fn_name`, `caller.fn_blocks`, `call_lbl`,
      `call_idx`] find_invoke_site_inst_targets) >>
    simp[fn_labels_def]) >>
  (* CS8b: Decode INVOKE operands (shared across all non-error cases) *)
  `?arg_ops. decode_invoke invoke_inst = SOME (callee.fn_name, arg_ops)` by (
    gvs[inst_targets_def] >>
    Cases_on `invoke_inst.inst_operands` >> gvs[] >>
    Cases_on `h` >> gvs[] >>
    simp[decode_invoke_def]) >>
  (* CS9: Error vs non-error case split *)
  `invoke_inst.inst_opcode = INVOKE` by
    (gvs[markerTheory.Abbrev_def] >> EVAL_TAC) >>
  Cases_on `!e. step_inst fuel ctx invoke_inst s1_pre <> Error e`
  >- (
    (* Non-error: unified INVOKE decomposition *)
    drule_all step_inst_invoke_decompose >> strip_tac >>
    (* Step G early: Callee doesn't error — prove BEFORE unification
       consumes decode_invoke. After gvs[], callee_fn→callee propagates. *)
    `!e. run_function fuel ctx callee_fn callee_s <> Error e` by
      (drule_all invoke_callee_no_error >> disch_then ACCEPT_TAC) >>
    (* Unify decode_invoke and callee *)
    `callee_name = callee.fn_name /\ arg_ops' = arg_ops` by (
      qpat_x_assum `decode_invoke _ = SOME (callee_name, _)` mp_tac >>
      qpat_x_assum `decode_invoke _ = SOME (callee.fn_name, _)` mp_tac >>
      simp[]) >>
    `callee_fn = callee` by (
      qpat_x_assum `lookup_function _ _ = SOME callee_fn` mp_tac >>
      qpat_x_assum `lookup_function _ _ = SOME callee` mp_tac >> fs[]) >>
    gvs[] >>
    (* CS10: Common setup for clone simulation — shared across all result types *)
    suspend "cs10")
  >>
  (* Error case: ~!e. ... becomes ?e. step_inst = Error e *)
  fs[] >>
  MATCH_MP_TAC invoke_step_error_sim >>
  MAP_EVERY qexists_tac [`bb`, `invoke_inst`, `s1_pre`, `call_idx`,
    `e`] >>
  gvs[markerTheory.Abbrev_def] >>
  rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
  `s2.vs_current_bb = s1.vs_current_bb` by gvs[] >> gvs[]
QED

(* run_function never returns OK *)
Triviality run_function_not_OK[local]:
  !fuel ctx fn s v. run_function fuel ctx fn s <> OK v
Proof
  Induct_on `fuel` >>
  ONCE_REWRITE_TAC[run_function_def] >> simp[] >>
  rpt gen_tac >>
  BasicProvers.EVERY_CASE_TAC >> simp[] >>
  fs[]
QED

Triviality setup_callee_fields[local]:
  !callee args s callee_s.
    setup_callee callee args s = SOME callee_s /\
    fn_has_entry callee ==>
    callee_s.vs_vars = FEMPTY /\
    callee_s.vs_params = args /\
    callee_s.vs_current_bb = (HD callee.fn_blocks).bb_label /\
    callee_s.vs_inst_idx = 0 /\
    callee_s.vs_prev_bb = NONE /\
    callee_s.vs_halted = F /\
    callee_s.vs_memory = s.vs_memory /\
    callee_s.vs_transient = s.vs_transient /\
    callee_s.vs_accounts = s.vs_accounts /\
    callee_s.vs_returndata = s.vs_returndata /\
    callee_s.vs_logs = s.vs_logs /\
    callee_s.vs_immutables = s.vs_immutables /\
    callee_s.vs_allocas = FEMPTY /\
    callee_s.vs_alloca_next = s.vs_alloca_next /\
    callee_s.vs_call_ctx = s.vs_call_ctx /\
    callee_s.vs_tx_ctx = s.vs_tx_ctx /\
    callee_s.vs_block_ctx = s.vs_block_ctx /\
    callee_s.vs_code = s.vs_code /\
    callee_s.vs_data_section = s.vs_data_section /\
    callee_s.vs_labels = s.vs_labels /\
    callee_s.vs_prev_hashes = s.vs_prev_hashes
Proof
  rpt strip_tac >>
  qpat_x_assum `setup_callee _ _ _ = _` mp_tac >>
  simp[setup_callee_def] >>
  `callee.fn_blocks <> []` by fs[fn_has_entry_def] >>
  Cases_on `callee.fn_blocks` >> fs[] >> strip_tac >> gvs[]
QED

Triviality clone_entry_label[local]:
  !prefix callee.
    fn_has_entry callee ==>
    (case (clone_function prefix callee).fn_blocks of
       [] => ""
     | eb::v1 => eb.bb_label) =
    STRCAT prefix (HD callee.fn_blocks).bb_label
Proof
  rpt strip_tac >>
  simp[clone_function_def, LET_THM] >>
  `callee.fn_blocks <> []` by fs[fn_has_entry_def] >>
  Cases_on `callee.fn_blocks` >> fs[clone_basic_block_def]
QED

(* bb_succs only produces labels from Label operands in the block *)
Triviality bb_succs_from_operands[local]:
  !bb l. MEM l (bb_succs bb) ==>
    ?inst. MEM inst bb.bb_instructions /\ MEM (Label l) inst.inst_operands
Proof
  rpt strip_tac >>
  fs[bb_succs_def] >>
  Cases_on `bb.bb_instructions` >> gvs[] >>
  qexists_tac `LAST (h::t)` >>
  `MEM (LAST (h::t)) (h::t)` by simp[MEM_LAST_NOT_NIL] >>
  gvs[MEM_nub, MEM_REVERSE, get_successors_def] >>
  Cases_on `is_terminator (LAST (h::t)).inst_opcode` >> gvs[] >>
  gvs[MEM_MAP, MEM_FILTER] >>
  Cases_on `y'` >> gvs[get_label_def]
QED

(* ret_bb successors are in fn_labels caller — EVERY version *)
Triviality ret_bb_succs_in_caller[local]:
  !ret_bb call_lbl caller call_bb k.
    lookup_block call_lbl caller.fn_blocks = SOME call_bb /\
    ret_bb.bb_instructions = DROP (k + 1) call_bb.bb_instructions /\
    (!bb inst lbl. MEM bb caller.fn_blocks /\
       MEM inst bb.bb_instructions /\
       MEM (Label lbl) inst.inst_operands ==> MEM lbl (fn_labels caller)) ==>
    EVERY (\l. MEM l (fn_labels caller)) (bb_succs ret_bb)
Proof
  rpt strip_tac >>
  REWRITE_TAC[EVERY_MEM] >> BETA_TAC >> rpt strip_tac >>
  drule bb_succs_from_operands >> strip_tac >>
  imp_res_tac lookup_block_MEM >>
  first_x_assum irule >>
  MAP_EVERY qexists_tac [`call_bb`, `inst`] >> simp[] >>
  metis_tac[MEM_DROP_IMP]
QED

(* Combined: ret_bb's successors are all in fn_labels caller.
   Derives ret_lbl <> call_lbl internally, uses inline_call_site_ret_bb_instructions
   to get ret_bb.bb_instructions = DROP, then applies ret_bb_succs_in_caller. *)
Triviality ret_bb_succs_from_inline_call_site[local]:
  !n lc caller callee call_lbl call_idx call_bb ret_bb.
    lookup_block call_lbl caller.fn_blocks = SOME call_bb /\
    ~MEM (return_block_label (inline_prefix n) lc) (fn_labels caller) /\
    lookup_block (return_block_label (inline_prefix n) lc)
      (inline_call_site (inline_prefix n)
        (return_block_label (inline_prefix n) lc)
        caller callee call_lbl call_idx).fn_blocks = SOME ret_bb /\
    (!bb inst lbl. MEM bb caller.fn_blocks /\
       MEM inst bb.bb_instructions /\
       MEM (Label lbl) inst.inst_operands ==> MEM lbl (fn_labels caller)) ==>
    EVERY (\l. MEM l (fn_labels caller)) (bb_succs ret_bb)
Proof
  rpt gen_tac >> strip_tac >>
  `return_block_label (inline_prefix n) lc <> call_lbl` by (
    CCONTR_TAC >> gvs[] >>
    imp_res_tac lookup_block_MEM_labels >> gvs[fn_labels_def]) >>
  `ret_bb.bb_instructions = DROP (call_idx + 1) call_bb.bb_instructions` by (
    drule_all inline_call_site_ret_bb_instructions >> simp[]) >>
  metis_tac[ret_bb_succs_in_caller]
QED

(* === Discharge clone_execution_sim_ext preconditions *)
(* NOTE: rpt conj_tac produces ~10 goals. ACCEPT_TAC/simp dismiss ~6, leaving 4.
   Verify count with hol_state_at before using >| *)
(* Helper: decode_invoke gives operand structure *)
Triviality decode_invoke_operands[local]:
  !inst name ops.
    decode_invoke inst = SOME (name, ops) ==>
    inst.inst_operands = Label name :: ops
Proof
  rpt strip_tac >> fs[decode_invoke_def] >>
  Cases_on `inst.inst_operands` >> gvs[] >>
  Cases_on `h` >> gvs[]
QED

(* Helper: eval_operand only depends on vars/labels, not control flow fields *)
Triviality eval_operand_jump_to[local]:
  !op s lbl.
    eval_operand op (jump_to lbl s) = eval_operand op s
Proof
  Cases >> simp[eval_operand_def, jump_to_def, lookup_var_def]
QED

Triviality eval_operand_prev_bb_upd[local]:
  !op s p.
    eval_operand op (s with vs_prev_bb := p) = eval_operand op s
Proof
  Cases >> simp[eval_operand_def, lookup_var_def]
QED

(* Shared core: decompose invoke_ops[i] for i < LENGTH args.
   Derives EL i invoke_ops = EL i arg_ops, evaluation, and not-Label. *)
Triviality invoke_ops_el_decompose[local]:
  !invoke_ops invoke_inst arg_ops args s callee_name i.
    decode_invoke invoke_inst = SOME (callee_name, arg_ops) /\
    Abbrev (invoke_ops = rotate_invoke_ops invoke_inst.inst_operands) /\
    eval_operands arg_ops s = SOME args /\
    FDOM s.vs_labels = {} /\
    i < LENGTH args ==>
    EL i invoke_ops = EL i arg_ops /\
    i < LENGTH arg_ops /\
    eval_operand (EL i arg_ops) s = SOME (EL i args) /\
    ~is_label_op (EL i arg_ops)
Proof
  rpt gen_tac >> strip_tac >>
  drule decode_invoke_operands >> strip_tac >>
  `invoke_ops = arg_ops ++ [Label callee_name]` by
    fs[markerTheory.Abbrev_def, rotate_invoke_ops_def] >>
  qpat_x_assum `Abbrev _` (K ALL_TAC) >>
  `LENGTH arg_ops = LENGTH args` by metis_tac[eval_operands_some_length] >>
  `i < LENGTH arg_ops` by simp[] >>
  `EL i invoke_ops = EL i arg_ops` by simp[EL_APPEND1] >>
  drule eval_operands_some_el >> disch_then (qspec_then `i` mp_tac) >>
  simp[] >> strip_tac >>
  (* Now have: eval_operand (EL i arg_ops) s = SOME (EL i args) *)
  (* Label case is impossible since FDOM s.vs_labels = {} *)
  `~is_label_op (EL i arg_ops)` suffices_by simp[] >>
  spose_not_then assume_tac >>
  Cases_on `EL i arg_ops` >> gvs[is_label_op_def, eval_operand_def, FLOOKUP_DEF]
QED

(* Stronger: classifies invoke_ops[i] directly as Var or Lit *)
Triviality invoke_ops_el_classify[local]:
  !invoke_ops invoke_inst arg_ops args s callee_name i.
    decode_invoke invoke_inst = SOME (callee_name, arg_ops) /\
    Abbrev (invoke_ops = rotate_invoke_ops invoke_inst.inst_operands) /\
    eval_operands arg_ops s = SOME args /\
    FDOM s.vs_labels = {} /\
    i < LENGTH args ==>
    (?v. invoke_ops ❲i❳ = Var v /\
         eval_operand (Var v) s = SOME (EL i args)) \/
    (?w. invoke_ops ❲i❳ = Lit w /\
         eval_operand (Lit w) s = SOME (EL i args))
Proof
  rpt gen_tac >> strip_tac >>
  mp_tac (Q.SPECL [`invoke_ops`, `invoke_inst`, `arg_ops`, `args`,
    `s`, `callee_name`, `i`] invoke_ops_el_decompose) >>
  impl_tac >- simp[] >> strip_tac >>
  Cases_on `EL i arg_ops` >> gvs[is_label_op_def] >| [
    DISJ2_TAC >> qexists_tac `c` >> simp[],
    DISJ1_TAC >> qexists_tac `s'` >> simp[]
  ]
QED

Triviality vars_fresh_above_notin_prefix_set[local]:
  !n fn bb inst x.
    vars_fresh_above n fn /\
    MEM bb fn.fn_blocks /\
    MEM inst bb.bb_instructions /\
    MEM (Var x) inst.inst_operands ==>
    x NOTIN {v | isPREFIX (inline_prefix n) v}
Proof
  rw[vars_fresh_above_def, EVERY_MEM] >> rpt strip_tac >>
  res_tac >> gvs[] >>
  first_x_assum (qspec_then `n` mp_tac) >> simp[]
QED

(* Derive LENGTH/is_label_op from decode_invoke + eval_operands.
   Used in cs10_discharge to establish per_block_sim_helper's preconditions. *)
Triviality invoke_ops_length_and_no_label[local]:
  !inst arg_ops args s name.
    decode_invoke inst = SOME (name, arg_ops) /\
    eval_operands arg_ops s = SOME args /\
    FDOM s.vs_labels = {} ==>
    LENGTH (rotate_invoke_ops inst.inst_operands) >= LENGTH args /\
    (!i. i < LENGTH args ==>
         ~is_label_op (EL i (rotate_invoke_ops inst.inst_operands)))
Proof
  rpt gen_tac >> strip_tac >>
  `inst.inst_operands = Label name :: arg_ops` by
    metis_tac[decode_invoke_operands] >>
  `rotate_invoke_ops inst.inst_operands = arg_ops ++ [Label name]` by
    simp[rotate_invoke_ops_def] >>
  `LENGTH arg_ops = LENGTH args` by metis_tac[eval_operands_some_length] >>
  conj_tac >- simp[LENGTH_APPEND] >>
  gen_tac >> strip_tac >>
  `i < LENGTH arg_ops` by simp[] >>
  drule eval_operands_some_el >> disch_then (qspec_then `i` mp_tac) >>
  simp[] >> strip_tac >>
  simp[EL_APPEND1] >>
  Cases_on `EL i arg_ops` >>
  gvs[is_label_op_def, eval_operand_def, FLOOKUP_DEF]
QED


(* === per_block_sim: callee blocks -> clone blocks in caller_xf *)

(* rewrite_inline_blocks_head_pidx is now exported from CallSimHelpers *)

(* General: fn_insts EVERY → per-block EVERY *)
Triviality every_fn_insts_block[local]:
  !P fn bb.
    EVERY P (fn_insts fn) /\ MEM bb fn.fn_blocks ==>
    EVERY P bb.bb_instructions
Proof
  rpt strip_tac >> fs[fn_insts_def] >>
  qsuff_tac `!bbs bb. EVERY P (fn_insts_blocks bbs) /\ MEM bb bbs ==>
    EVERY P bb.bb_instructions` >- metis_tac[] >>
  Induct >> simp[fn_insts_blocks_def] >>
  rpt strip_tac >> gvs[EVERY_APPEND]
QED

(* Helper: clone block lookup with pidx=0 guaranteed.
   Combines lookup_block_clone_in_fn_inl logic with pidx handling:
   - Entry block: derive pidx=0 from head_pidx
   - Non-entry: derive pidx=0 via pidx_irrel + no-PARAM *)
Triviality lookup_block_clone_pidx0[local]:
  !prefix ret_lbl caller callee call_lbl call_idx lbl bb n lc.
    lookup_block lbl callee.fn_blocks = SOME bb /\
    lookup_block call_lbl caller.fn_blocks <> NONE /\
    ALL_DISTINCT (fn_labels callee) /\
    ~MEM (STRCAT prefix lbl) (fn_labels caller) /\
    STRCAT prefix lbl <> ret_lbl /\
    prefix = inline_prefix n /\
    ret_lbl = return_block_label prefix lc /\
    fn_has_entry callee /\
    EVERY (\bb. EVERY (\i. i.inst_opcode <> PARAM) bb.bb_instructions)
      (TL callee.fn_blocks) ==>
    ?bb'.
      lookup_block (STRCAT prefix lbl)
        (inline_call_site prefix ret_lbl caller callee call_lbl call_idx).fn_blocks =
        SOME bb' /\
      bb'.bb_label = STRCAT prefix lbl /\
      bb'.bb_instructions =
        FST (rewrite_inline_insts
          (rotate_invoke_ops
            (THE (lookup_block call_lbl caller.fn_blocks)).bb_instructions
              ❲call_idx❳.inst_operands)
          (THE (lookup_block call_lbl caller.fn_blocks)).bb_instructions
              ❲call_idx❳.inst_outputs
          ret_lbl
          (MAP (clone_instruction prefix (fn_labels callee))
               bb.bb_instructions)
          0)
Proof
  rpt gen_tac >> strip_tac >> rpt BasicProvers.VAR_EQ_TAC >>
  imp_res_tac lookup_block_MEM >>
  `callee.fn_blocks <> []` by fs[fn_has_entry_def] >>
  (* Case split: entry block or not *)
  Cases_on `MEM bb (TL callee.fn_blocks)`
  >- (
    (* ═══ Non-entry block: pidx_irrel ═══ *)
    mp_tac (Q.SPECL [
      `inline_prefix n`,
      `return_block_label (inline_prefix n) lc`,
      `caller`, `callee`, `call_lbl`, `call_idx`, `lbl`, `bb`]
      lookup_block_clone_in_fn_inl) >>
    ASM_REWRITE_TAC[] >> strip_tac >>
    qexists_tac `bb'` >> ASM_REWRITE_TAC[] >>
    `EVERY (\i. i.inst_opcode <> PARAM) bb.bb_instructions` by
      (fs[EVERY_MEM] >> res_tac) >>
    `EVERY (\i. i.inst_opcode <> PARAM)
       (MAP (clone_instruction (inline_prefix n) (fn_labels callee))
            bb.bb_instructions)` by (
      fs[EVERY_MEM, MEM_MAP] >> rpt strip_tac >>
      gvs[clone_instruction_opcode]) >>
    metis_tac[rewrite_inline_insts_pidx_irrel])
  >>
  (* ═══ Entry block: head gets pidx=0 via lookup_block_clone_in_fn_inl_head ═══ *)
  `bb = HD callee.fn_blocks` by (
    Cases_on `callee.fn_blocks` >> fs[]) >>
  (* Bridge: lbl = (HD callee.fn_blocks).bb_label *)
  `(HD callee.fn_blocks).bb_label = lbl` by
    (imp_res_tac lookup_block_label >> gvs[]) >>
  mp_tac (Q.SPECL [
    `inline_prefix n`,
    `return_block_label (inline_prefix n) lc`,
    `caller`, `callee`, `call_lbl`, `call_idx`]
    lookup_block_clone_in_fn_inl_head) >>
  ASM_REWRITE_TAC[]
QED


(* Reusable pattern: clone labels are never in bb_succs ret_bb.
   bb_succs ret_bb ⊆ fn_labels caller (from ret_bb_succs_in_caller),
   STRCAT prefix lbl ∉ fn_labels caller (from prefixed_label_not_in_labels). *)
Triviality clone_label_not_in_ret_bb_succs[local]:
  !n caller ret_bb lbl.
    labels_fresh_above n caller /\
    EVERY (\l. MEM l (fn_labels caller)) (bb_succs ret_bb)
    ==>
    ~MEM (STRCAT (inline_prefix n) lbl) (bb_succs ret_bb)
Proof
  rpt strip_tac >>
  fs[EVERY_MEM] >> res_tac >>
  metis_tac[prefixed_label_not_in_labels]
QED

(* Corollary: fix_inline_phis is identity on blocks not in bb_succs ret_bb *)
Triviality fix_inline_phis_passthrough[local]:
  !orig_lbl new_lbl ret_bb func lbl.
    ~MEM lbl (bb_succs ret_bb) ==>
    lookup_block lbl (fix_inline_phis orig_lbl new_lbl ret_bb func).fn_blocks =
    lookup_block lbl func.fn_blocks
Proof
  rpt strip_tac >>
  REWRITE_TAC[lookup_block_fix_inline_phis] >>
  Cases_on `lookup_block lbl func.fn_blocks` >> simp[]
QED

(* clone_label_neq_ret_lbl: A cloned callee label STRCAT prefix lbl cannot
   equal the return block label, because callee labels have no "inline_return"
   prefix but the return block label's suffix starts with "inline_return". *)
Triviality clone_label_neq_ret_lbl[local]:
  !prefix lbl lc callee.
    MEM lbl (fn_labels callee) /\
    labels_no_inline_return callee ==>
    STRCAT prefix lbl <> return_block_label prefix lc
Proof
  rpt gen_tac >> strip_tac >>
  REWRITE_TAC[return_block_label_def] >>
  simp[STRCAT_11] >>
  DISCH_TAC >>
  (* lbl = STRCAT "inline_return" (toString lc) *)
  qpat_x_assum `labels_no_inline_return _` mp_tac >>
  REWRITE_TAC[labels_no_inline_return_def, EVERY_MEM] >>
  DISCH_THEN (qspec_then `lbl` mp_tac) >>
  ASM_REWRITE_TAC[] >>
  (* Goal: ~isPREFIX "inline_return" lbl ==> F *)
  qpat_x_assum `lbl = _` SUBST1_TAC >>
  simp[isPREFIX_THM]
QED


(* Extract per-block properties from function-level properties.
   Clean standalone context avoids by-block pollution. *)
Triviality callee_block_props[local]:
  !callee bb lbl.
    lookup_block lbl callee.fn_blocks = SOME bb /\
    EVERY bb_well_formed callee.fn_blocks /\
    EVERY (\bb. params_sequential bb.bb_instructions 0) callee.fn_blocks /\
    fn_no_alloca callee /\
    label_ops_closed callee /\
    invoke_targets_extern callee ==>
    bb_well_formed bb /\
    params_sequential bb.bb_instructions 0 /\
    EVERY (\inst. inst.inst_opcode <> ALLOCA) bb.bb_instructions /\
    EVERY (\inst. EVERY (\op. !l. op = Label l ==> MEM l (fn_labels callee))
                        inst.inst_operands) bb.bb_instructions /\
    EVERY (\inst. inst.inst_opcode = INVOKE ==>
       case inst.inst_operands of
         Label l :: _ => ~MEM l (fn_labels callee) | _ => T)
       bb.bb_instructions
Proof
  rpt gen_tac >> strip_tac >>
  imp_res_tac lookup_block_MEM >>
  gvs[EVERY_MEM, fn_no_alloca_def, label_ops_closed_def,
      invoke_targets_extern_def] >>
  rpt conj_tac >> rpt strip_tac >> gvs[] >>
  TRY res_tac >>
  `MEM inst (fn_insts callee)` by
    (simp[fn_insts_def] >> metis_tac[mem_fn_insts_blocks]) >>
  res_tac
QED

Triviality LENGTH_rotate_invoke_ops[local]:
  !ops. LENGTH (rotate_invoke_ops ops) = LENGTH ops
Proof
  Cases >> simp[rotate_invoke_ops_def]
QED

Triviality EVERY_rotate_invoke_ops[local]:
  !P ops. EVERY P ops ==> EVERY P (rotate_invoke_ops ops)
Proof
  gen_tac >> Cases >> simp[rotate_invoke_ops_def, EVERY_APPEND]
QED

(* Extract caller-instruction-level facts from function-level EVERY assumptions.
   Parallel to callee_block_props for the callee side. Clean context. *)
Triviality caller_invoke_props[local]:
  !caller callee call_bb call_inst n.
    EVERY (\bb. EVERY (\inst.
      inst_targets callee.fn_name inst ==>
      callee_ret_arity_le (LENGTH inst.inst_outputs) callee)
        bb.bb_instructions) caller.fn_blocks /\
    EVERY (\bb. EVERY (\inst.
      inst_targets callee.fn_name inst ==>
      EVERY (\blk. count_params blk.bb_instructions <=
                   LENGTH inst.inst_operands - 1) callee.fn_blocks)
        bb.bb_instructions) caller.fn_blocks /\
    vars_fresh_above n caller /\
    MEM call_bb caller.fn_blocks /\
    MEM call_inst call_bb.bb_instructions /\
    inst_targets callee.fn_name call_inst ==>
    callee_ret_arity_le (LENGTH call_inst.inst_outputs) callee /\
    EVERY (\blk. count_params blk.bb_instructions <=
                 LENGTH call_inst.inst_operands - 1) callee.fn_blocks /\
    EVERY (\v. ~isPREFIX (inline_prefix n) v) call_inst.inst_outputs /\
    EVERY (\op. !v. op = Var v ==> ~isPREFIX (inline_prefix n) v)
      call_inst.inst_operands
Proof
  rpt strip_tac
  (* callee_ret_arity_le *)
  >- (fs[EVERY_MEM] >> res_tac >> res_tac)
  (* count_params *)
  >- (fs[EVERY_MEM] >> res_tac >> res_tac)
  (* output freshness *)
  >- (fs[vars_fresh_above_def, EVERY_MEM] >>
      rpt strip_tac >> res_tac >> res_tac >>
      first_x_assum (qspec_then `n` mp_tac) >> simp[])
  (* operand freshness *)
  >> (
    `EVERY (\op. case op of Lit _ => T
       | Var v => !k. k >= n ==> ~isPREFIX (inline_prefix k) v
       | Label _ => T) call_inst.inst_operands` by
       (fs[vars_fresh_above_def, EVERY_MEM] >> res_tac >> res_tac) >>
    irule EVERY_MONOTONIC >> first_assum (irule_at Any) >>
    BETA_TAC >> rpt strip_tac >>
    Cases_on `x` >> fs[] >>
    first_x_assum (qspec_then `n` mp_tac) >> simp[])
QED

(* Helper: extract callee_ret_arity_le for a specific callee block *)
Triviality callee_ret_arity_bounded[local]:
  !callee k lbl bb_callee.
    callee_ret_arity_le k callee /\
    lookup_block lbl callee.fn_blocks = SOME bb_callee ==>
    EVERY (\inst. inst.inst_opcode = RET ==>
                  LENGTH inst.inst_operands <= k) bb_callee.bb_instructions
Proof
  rw[callee_ret_arity_le_def, EVERY_MEM] >>
  rpt strip_tac >>
  imp_res_tac lookup_block_MEM >>
  res_tac >> fs[EVERY_MEM] >> res_tac
QED

(* Extract callee_ret_arity_le from EVERY: simple double-MEM extraction *)
Triviality every_callee_ret_arity_le[local]:
  !fn_blocks bb inst callee_name callee.
    EVERY (\bb. EVERY (\inst.
      inst_targets callee_name inst ==>
      callee_ret_arity_le (LENGTH inst.inst_outputs) callee)
        bb.bb_instructions) fn_blocks /\
    MEM bb fn_blocks /\
    MEM inst bb.bb_instructions /\
    inst_targets callee_name inst ==>
    callee_ret_arity_le (LENGTH inst.inst_outputs) callee
Proof
  rpt strip_tac >>
  fs[EVERY_MEM] >>
  res_tac >> res_tac
QED

(* For a RET block in callee, the LAST instruction's operand count
   is bounded by the callee_ret_arity_le bound. *)
Triviality callee_last_ret_bounded[local]:
  !callee k lbl bb.
    callee_ret_arity_le k callee /\
    lookup_block lbl callee.fn_blocks = SOME bb /\
    bb.bb_instructions <> [] /\
    (LAST bb.bb_instructions).inst_opcode = RET ==>
    k >= LENGTH (LAST bb.bb_instructions).inst_operands
Proof
  rpt strip_tac >>
  mp_tac (Q.SPECL [`callee`, `k`, `lbl`, `bb`] callee_ret_arity_bounded) >>
  ASM_REWRITE_TAC[] >> strip_tac >>
  `MEM (LAST bb.bb_instructions) bb.bb_instructions` by
    metis_tac[MEM_LAST_NOT_NIL] >>
  fs[EVERY_MEM] >> res_tac >> simp[]
QED

(* Combine clone_block_sim_ret/no_ret with case split.
   Clean context — fs/simp work. *)
Triviality clone_block_sim_case_split[local]:
  !prefix labels ret_lbl invoke_ops invoke_outs ctx fuel
   bb bb_clone sc sd args callee lbl n.
    bb_clone.bb_instructions =
      FST (rewrite_inline_insts invoke_ops invoke_outs ret_lbl
        (MAP (clone_instruction prefix labels) bb.bb_instructions) 0) /\
    bb_clone.bb_label = STRCAT prefix bb.bb_label /\
    clone_rel_np prefix labels sc sd /\
    sc.vs_inst_idx = 0 /\ sd.vs_inst_idx = 0 /\
    ~sc.vs_halted /\
    bb_well_formed bb /\
    EVERY (\inst. inst.inst_opcode <> ALLOCA) bb.bb_instructions /\
    EVERY (\inst. EVERY (\op. !l. op = Label l ==> MEM l labels)
                        inst.inst_operands)
          bb.bb_instructions /\
    EVERY (\inst. inst.inst_opcode = INVOKE ==>
             case inst.inst_operands of
               Label l :: _ => ~MEM l labels | _ => T)
          bb.bb_instructions /\
    params_sequential bb.bb_instructions 0 /\
    (!i. i < LENGTH invoke_ops /\ i < LENGTH args ==>
         eval_operand (EL i invoke_ops) sd = SOME (EL i args) /\
         EL i sc.vs_params = EL i args) /\
    LENGTH args = LENGTH sc.vs_params /\
    LENGTH invoke_ops >= LENGTH args /\
    (!i. i < LENGTH args ==> ~is_label_op (EL i invoke_ops)) /\
    EVERY (\op. !v. op = Var v ==> ~isPREFIX prefix v) invoke_ops /\
    EVERY (\v. ~isPREFIX prefix v) invoke_outs /\
    ALL_DISTINCT invoke_outs /\
    callee_ret_arity_le (LENGTH invoke_outs) callee /\
    lookup_block lbl callee.fn_blocks = SOME bb /\
    count_params bb.bb_instructions <= LENGTH invoke_ops
    ==>
    clone_block_sim prefix labels ret_lbl invoke_outs ctx fuel
      bb bb_clone sc sd
Proof
  rpt strip_tac >>
  `bb.bb_instructions <> []` by fs[bb_well_formed_def] >>
  Cases_on `(LAST bb.bb_instructions).inst_opcode = RET`
  >- (
    `LENGTH invoke_outs >= LENGTH (LAST bb.bb_instructions).inst_operands` by
      metis_tac[callee_last_ret_bounded] >>
    mp_tac (Q.SPECL [`LENGTH bb.bb_instructions`,
      `fuel`, `ctx`, `bb`, `bb_clone`, `prefix`, `labels`,
      `invoke_ops`, `invoke_outs`, `ret_lbl`, `invoke_outs`,
      `sc`, `sd`, `args`] clone_block_sim_ret) >>
    simp[]
  ) >>
  `EVERY (\inst. inst.inst_opcode <> RET) bb.bb_instructions` by (
    simp[EVERY_EL] >> rpt strip_tac >>
    Cases_on `n = PRE (LENGTH bb.bb_instructions)`
    >- (`EL n bb.bb_instructions = LAST bb.bb_instructions` by
          simp[LAST_EL] >> metis_tac[])
    >> (`n < PRE (LENGTH bb.bb_instructions)` by decide_tac >>
        `~is_terminator (EL n bb.bb_instructions).inst_opcode` by
          metis_tac[wf_non_last_non_terminator] >>
        pop_assum mp_tac >> simp[is_terminator_def])
  ) >>
  mp_tac (Q.SPECL [`LENGTH bb.bb_instructions`,
    `fuel`, `ctx`, `bb`, `bb_clone`, `prefix`, `labels`,
    `invoke_ops`, `invoke_outs`, `ret_lbl`, `invoke_outs`,
    `sc`, `sd`, `args`] clone_block_sim_no_ret) >>
  simp[]
QED

(* Helper: comprehensive per_block_sim — clean context *)
Triviality per_block_sim_helper[local]:
  !n lc caller callee call_lbl call_idx call_bb ret_bb args ctx.
    ALL_DISTINCT (fn_labels callee) /\
    labels_no_inline_return callee /\
    EVERY bb_well_formed callee.fn_blocks /\
    EVERY (\bb. params_sequential bb.bb_instructions 0) callee.fn_blocks /\
    EVERY (\bb. EVERY (\i. i.inst_opcode <> PARAM) bb.bb_instructions)
      (TL callee.fn_blocks) /\
    fn_no_alloca callee /\
    fn_has_entry callee /\
    label_ops_closed callee /\
    invoke_targets_extern callee /\
    ALL_DISTINCT (fn_labels caller) /\
    labels_fresh_above n caller /\
    vars_fresh_above n caller /\
    lookup_block call_lbl caller.fn_blocks = SOME call_bb /\
    lookup_block (return_block_label (inline_prefix n) lc)
      (inline_call_site (inline_prefix n)
        (return_block_label (inline_prefix n) lc)
        caller callee call_lbl call_idx).fn_blocks = SOME ret_bb /\
    ALL_DISTINCT call_bb.bb_instructions❲call_idx❳.inst_outputs /\
    EVERY (\bb. EVERY (\inst.
      inst_targets callee.fn_name inst ==>
      callee_ret_arity_le (LENGTH inst.inst_outputs) callee)
      bb.bb_instructions) caller.fn_blocks /\
    EVERY (\bb. EVERY (\inst.
      inst_targets callee.fn_name inst ==>
      EVERY (\blk. count_params blk.bb_instructions <=
                   LENGTH inst.inst_operands - 1) callee.fn_blocks)
      bb.bb_instructions) caller.fn_blocks /\
    MEM call_bb caller.fn_blocks /\
    MEM call_bb.bb_instructions❲call_idx❳ call_bb.bb_instructions /\
    inst_targets callee.fn_name call_bb.bb_instructions❲call_idx❳ /\
    EVERY (\bb. EVERY (\inst.
      inst_targets callee.fn_name inst ==>
      EVERY (\op. !v. op = Var v ==> ~MEM v inst.inst_outputs)
        (TL inst.inst_operands))
      bb.bb_instructions) caller.fn_blocks /\
    EVERY (\l. MEM l (fn_labels caller)) (bb_succs ret_bb) /\
    LENGTH (rotate_invoke_ops call_bb.bb_instructions❲call_idx❳.inst_operands)
      >= LENGTH args /\
    (!i. i < LENGTH args ==>
         ~is_label_op (EL i (rotate_invoke_ops
           call_bb.bb_instructions❲call_idx❳.inst_operands))) ==>
    let prefix = inline_prefix n in
    let ret_lbl = return_block_label prefix lc in
    let fn_inl = inline_call_site prefix ret_lbl caller callee call_lbl call_idx in
    let caller_xf = fix_inline_phis call_lbl ret_lbl ret_bb fn_inl in
    let invoke_ops = rotate_invoke_ops
      call_bb.bb_instructions❲call_idx❳.inst_operands in
    let invoke_outs = call_bb.bb_instructions❲call_idx❳.inst_outputs in
    !fuel' lbl bb sc sd.
      lookup_block lbl callee.fn_blocks = SOME bb /\
      clone_rel_np prefix (fn_labels callee) sc sd /\
      sc.vs_inst_idx = 0 /\ sd.vs_inst_idx = 0 /\ ~sc.vs_halted /\
      LENGTH args = LENGTH sc.vs_params /\
      (!i. i < LENGTH invoke_ops /\ i < LENGTH args ==>
           eval_operand (EL i invoke_ops) sd = SOME (EL i args) /\
           EL i sc.vs_params = EL i args) ==>
      ?bb'.
        lookup_block (STRCAT prefix lbl) caller_xf.fn_blocks = SOME bb' /\
        clone_block_sim prefix (fn_labels callee) ret_lbl invoke_outs
          ctx fuel' bb bb' sc sd
Proof
  rpt gen_tac >> strip_tac >>
  (* Derive lookup_block <> NONE for downstream helpers *)
  `lookup_block call_lbl caller.fn_blocks <> NONE` by simp[] >>
  simp[LET_THM] >>
  rpt gen_tac >> strip_tac >>
  (* Step 1: Per-block properties via callee_block_props *)
  imp_res_tac lookup_block_MEM >>
  `MEM lbl (fn_labels callee)` by
    (imp_res_tac lookup_block_MEM_labels >> fs[fn_labels_def]) >>
  mp_tac (Q.SPECL [`callee`, `bb`, `lbl`] callee_block_props) >>
  ASM_REWRITE_TAC[] >> strip_tac >>
  (* Step 2: Label freshness for clone *)
  `~MEM (STRCAT (inline_prefix n) lbl) (fn_labels caller)` by
    (irule prefixed_label_not_in_labels >> first_assum ACCEPT_TAC) >>
  `STRCAT (inline_prefix n) lbl <>
   return_block_label (inline_prefix n) lc` by
    (irule clone_label_neq_ret_lbl >>
     qexists_tac `callee` >> ASM_REWRITE_TAC[]) >>
  (* Step 3: Find clone block in fn_inl with pidx=0 *)
  mp_tac (Q.SPECL [
    `inline_prefix n`,
    `return_block_label (inline_prefix n) lc`,
    `caller`, `callee`, `call_lbl`, `call_idx`, `lbl`, `bb`,
    `n`, `lc`]
    lookup_block_clone_pidx0) >>
  ASM_REWRITE_TAC[] >> strip_tac >>
  (* Step 4: Pass through fix_inline_phis *)
  `~MEM (STRCAT (inline_prefix n) lbl) (bb_succs ret_bb)` by
    (irule clone_label_not_in_ret_bb_succs >>
     qexists_tac `caller` >> ASM_REWRITE_TAC[]) >>
  `lookup_block (STRCAT (inline_prefix n) lbl)
     (fix_inline_phis call_lbl (return_block_label (inline_prefix n) lc)
        ret_bb (inline_call_site (inline_prefix n)
          (return_block_label (inline_prefix n) lc)
          caller callee call_lbl call_idx)).fn_blocks = SOME bb'` by
    (mp_tac (Q.SPECL [`call_lbl`,
       `return_block_label (inline_prefix n) lc`,
       `ret_bb`,
       `inline_call_site (inline_prefix n)
          (return_block_label (inline_prefix n) lc)
          caller callee call_lbl call_idx`,
       `STRCAT (inline_prefix n) lbl`] fix_inline_phis_passthrough) >>
     ASM_REWRITE_TAC[]) >>
  (* Step 5: Apply clone_block_sim via case split helper *)
  qexists_tac `bb'` >> conj_tac >- first_assum ACCEPT_TAC >>
  `bb.bb_label = lbl` by (imp_res_tac lookup_block_label) >>
  (* 5a: Extract caller-instruction facts via caller_invoke_props *)
  mp_tac (Q.SPECL [`caller`, `callee`,
    `call_bb`,
    `call_bb.bb_instructions
       ❲call_idx❳`,
    `n`] caller_invoke_props) >>
  ASM_REWRITE_TAC[] >> strip_tac >>
  (* 5b: Derive rotate_invoke_ops freshness and count_params bound *)
  `EVERY (\op. !v. op = Var v ==> ~isPREFIX (inline_prefix n) v)
     (rotate_invoke_ops
       call_bb.bb_instructions
         ❲call_idx❳.inst_operands)` by
    metis_tac[EVERY_rotate_invoke_ops] >>
  `count_params bb.bb_instructions <=
     LENGTH (rotate_invoke_ops
       call_bb.bb_instructions
         ❲call_idx❳.inst_operands)` by
    (simp[LENGTH_rotate_invoke_ops] >>
     qpat_assum `EVERY (\blk. count_params _ <= _) _`
       (mp_tac o REWRITE_RULE [EVERY_MEM]) >>
     DISCH_THEN (mp_tac o Q.SPEC `bb`) >> simp[] >> strip_tac >>
     decide_tac) >>
  (* 5c: Apply clone_block_sim_case_split (accepts args-based LENGTH/is_label_op) *)
  mp_tac (Q.SPECL [
    `inline_prefix n`, `fn_labels callee`,
    `return_block_label (inline_prefix n) lc`,
    `rotate_invoke_ops
       call_bb.bb_instructions
         ❲call_idx❳.inst_operands`,
    `call_bb.bb_instructions
         ❲call_idx❳.inst_outputs`,
    `ctx`, `fuel'`, `bb`, `bb'`, `sc`, `sd`,
    `args`, `callee`, `lbl`, `n`]
    clone_block_sim_case_split) >>
  ASM_REWRITE_TAC[optionTheory.THE_DEF]
QED


(* === frame: clone blocks preserve frame variables *)

(* Standalone helper: if all outputs of a block are prefixed or in outs,
   and v is neither prefixed nor in outs, then run_block preserves v. *)
Triviality frame_var_preserved_by_clone_block[local]:
  !fuel ctx bb sd sd' prefix outs v.
    run_block fuel ctx bb sd = OK sd' /\
    EVERY (\v. isPREFIX prefix v \/ MEM v outs)
      (FLAT (MAP (\i. i.inst_outputs) bb.bb_instructions)) /\
    ~isPREFIX prefix v /\ ~MEM v outs ==>
    lookup_var v sd' = lookup_var v sd
Proof
  rpt strip_tac >>
  drule run_block_preserves_non_output_vars >> DISCH_THEN irule >>
  CCONTR_TAC >> gvs[] >>
  fs[EVERY_MEM] >>
  first_x_assum drule >> strip_tac >> gvs[]
QED

(*
 * frame_proof_helper: Clone blocks only write prefixed vars and invoke outputs.
 * Any variable outside that set (the "frame") is preserved by run_block.
 *)
Triviality frame_proof_helper[local]:
  !fuel' ret_lbl caller callee caller_xf fn_inl ret_bb
   invoke_outs n call_lbl idx ctx bb_clone sd sd' v lbl
   call_bb invoke_inst lc.
    lookup_block (STRCAT (inline_prefix n) lbl) caller_xf.fn_blocks = SOME bb_clone /\
    run_block fuel' ctx bb_clone sd = OK sd' /\
    ~isPREFIX (inline_prefix n) v /\ ~MEM v invoke_outs /\
    caller_xf = fix_inline_phis call_lbl ret_lbl ret_bb fn_inl /\
    fn_inl = inline_call_site (inline_prefix n) ret_lbl caller callee call_lbl idx /\
    ret_lbl = return_block_label (inline_prefix n) lc /\
    lookup_block call_lbl caller.fn_blocks = SOME call_bb /\
    ~MEM ret_lbl (fn_labels caller) /\
    lookup_block ret_lbl fn_inl.fn_blocks = SOME ret_bb /\
    ALL_DISTINCT (fn_labels callee) /\
    EVERY bb_well_formed callee.fn_blocks /\
    labels_no_inline_return callee /\
    vars_fresh_above n caller /\
    labels_fresh_above n caller /\
    ALL_DISTINCT (MAP (\bb. bb.bb_label) caller.fn_blocks) /\
    EVERY (\bb. EVERY (\inst.
      inst_targets callee.fn_name inst ==>
      callee_ret_arity_le (LENGTH inst.inst_outputs) callee)
        bb.bb_instructions) caller.fn_blocks /\
    MEM invoke_inst call_bb.bb_instructions /\
    inst_targets callee.fn_name invoke_inst /\
    invoke_outs = invoke_inst.inst_outputs /\
    invoke_outs = call_bb.bb_instructions ❲idx❳.inst_outputs /\
    MEM lbl (fn_labels callee) /\
    (!bb inst lbl'. MEM bb caller.fn_blocks /\
       MEM inst bb.bb_instructions /\
       MEM (Label lbl') inst.inst_operands ==> MEM lbl' (fn_labels caller))
    ==>
    lookup_var v sd' = lookup_var v sd
Proof
  rpt gen_tac >> strip_tac >>
  (* Substitute away definitional equalities so irule/ASM_REWRITE match directly *)
  qpat_x_assum `fn_inl = _` SUBST_ALL_TAC >>
  qpat_x_assum `caller_xf = _` SUBST_ALL_TAC >>
  qpat_x_assum `ret_lbl = _` SUBST_ALL_TAC >>
  (* Unify invoke_outs: substitute away so callee_ret_arity_bounded matches *)
  qpat_x_assum `invoke_outs = (EL _ _).inst_outputs` SUBST_ALL_TAC >>
  (* Derive MEM and label facts *)
  imp_res_tac lookup_block_MEM >>
  imp_res_tac lookup_block_label >>
  (* callee_ret_arity_le *)
  `callee_ret_arity_le (LENGTH invoke_inst.inst_outputs) callee` by (
    mp_tac (Q.SPECL [`caller.fn_blocks`, `call_bb`, `invoke_inst`,
      `callee.fn_name`, `callee`] every_callee_ret_arity_le) >>
    ASM_REWRITE_TAC[]) >>
  qpat_x_assum `EVERY (\bb. EVERY _ bb.bb_instructions) caller.fn_blocks` kall_tac >>
  (* return_block_label <> call_lbl *)
  `return_block_label (inline_prefix n) lc <> call_lbl` by (
    strip_tac >> qpat_x_assum `~MEM _ (fn_labels caller)` mp_tac >>
    ASM_REWRITE_TAC[fn_labels_def, MEM_MAP] >>
    qexists_tac `call_bb` >> BETA_TAC >> ASM_REWRITE_TAC[]) >>
  (* ret_bb structure *)
  mp_tac (Q.SPECL [`inline_prefix n`,
    `return_block_label (inline_prefix n) lc`,
    `caller`, `callee`, `call_lbl`, `idx`, `call_bb`, `ret_bb`]
    inline_call_site_ret_bb_instructions) >>
  ASM_REWRITE_TAC[] >> strip_tac >>
  (* EVERY bb_succs ret_bb in fn_labels caller *)
  `EVERY (\l. MEM l (fn_labels caller)) (bb_succs ret_bb)` by (
    mp_tac (Q.SPECL [`ret_bb`, `call_lbl`, `caller`, `call_bb`, `idx`]
      ret_bb_succs_in_caller) >>
    ASM_REWRITE_TAC[]) >>
  (* STRCAT prefix lbl <> return_block_label *)
  `STRCAT (inline_prefix n) lbl <> return_block_label (inline_prefix n) lc` by (
    irule clone_label_neq_ret_lbl >>
    qexists_tac `callee` >> ASM_REWRITE_TAC[]) >>
  (* Clone label not in bb_succs ret_bb *)
  `~MEM (STRCAT (inline_prefix n) lbl) (bb_succs ret_bb)` by
    metis_tac[clone_label_not_in_ret_bb_succs] >>
  (* fix_inline_phis passthrough *)
  first_x_assum (fn nmem =>
    qpat_x_assum `lookup_block _ (fix_inline_phis _ _ _ _).fn_blocks = _`
      (fn th => assume_tac (REWRITE_RULE [MATCH_MP fix_inline_phis_passthrough nmem] th)
                >> assume_tac nmem)) >>
  (* Clone label not in caller labels *)
  `~MEM (STRCAT (inline_prefix n) lbl) (fn_labels caller)` by
    (irule prefixed_label_not_in_labels >> ASM_REWRITE_TAC[]) >>
  (* Reverse lookup to get callee block *)
  mp_tac (Q.SPECL [`inline_prefix n`,
    `return_block_label (inline_prefix n) lc`,
    `caller`, `callee`, `call_lbl`, `idx`, `lbl`, `bb_clone`]
    clone_in_fn_inl_reverse) >>
  ASM_REWRITE_TAC[optionTheory.NOT_SOME_NONE] >> strip_tac >>
  (* Get outputs bounded — use invoke_inst.inst_outputs form *)
  `EVERY (\inst. inst.inst_opcode = RET ==>
    LENGTH inst.inst_operands <= LENGTH invoke_inst.inst_outputs)
    bb_callee.bb_instructions` by (
    irule callee_ret_arity_bounded >>
    qexistsl_tac [`callee`, `lbl`] >> ASM_REWRITE_TAC[]) >>
  mp_tac (Q.SPECL [`bb_callee.bb_instructions`,
    `rotate_invoke_ops
       call_bb.bb_instructions ❲idx❳.inst_operands`,
    `call_bb.bb_instructions ❲idx❳.inst_outputs`,
    `return_block_label (inline_prefix n) lc`,
    `inline_prefix n`, `fn_labels callee`, `pidx_bb`]
    clone_rewrite_outputs_bounded) >>
  ASM_REWRITE_TAC[] >> strip_tac >>
  (* Apply frame_var_preserved_by_clone_block *)
  irule frame_var_preserved_by_clone_block >>
  qexistsl_tac [`bb_clone`, `ctx`, `fuel'`,
    `call_bb.bb_instructions ❲idx❳.inst_outputs`, `inline_prefix n`] >>
  ASM_REWRITE_TAC[optionTheory.THE_DEF]
QED


(* Helper: invoke_ops[i] = Var v implies frame v, given well-formedness.
   Captures the two-part reasoning: (1) v not prefixed via vars_fresh_above,
   (2) v not in invoke_outs via EVERY operand/output disjointness. *)
Triviality invoke_ops_var_in_frame[local]:
  !n fn bb inst callee_name arg_ops invoke_ops i v.
    invoke_ops ❲i❳ = Var v /\
    inst.inst_operands = Label callee_name :: arg_ops /\
    Abbrev (invoke_ops = rotate_invoke_ops inst.inst_operands) /\
    i < LENGTH arg_ops /\
    vars_fresh_above n fn /\
    MEM bb fn.fn_blocks /\ MEM inst bb.bb_instructions /\
    inst_targets callee_name inst /\
    EVERY (\bb. EVERY (\inst'. inst_targets callee_name inst' ==>
      EVERY (\op. !v. op = Var v ==> ~MEM v inst'.inst_outputs)
        (TL inst'.inst_operands)) bb.bb_instructions) fn.fn_blocks ==>
    ~isPREFIX (inline_prefix n) v /\ ~MEM v inst.inst_outputs
Proof
  rpt gen_tac >> strip_tac >>
  (* Part 1: ~isPREFIX *)
  `invoke_ops = arg_ops ++ [Label callee_name]` by
    fs[markerTheory.Abbrev_def, rotate_invoke_ops_def] >>
  `EL i arg_ops = Var v` by (gvs[EL_APPEND1]) >>
  conj_tac >- (
    mp_tac (Q.SPECL [`n`, `fn`, `bb`, `inst`, `v`]
      vars_fresh_above_notin_prefix_set) >>
    simp[] >> disch_then MATCH_MP_TAC >>
    `MEM (Var v) arg_ops` by (simp[MEM_EL] >> qexists_tac `i` >> simp[]) >>
    simp[MEM]
  ) >>
  (* Part 2: ~MEM v inst.inst_outputs *)
  qpat_x_assum `EVERY _ fn.fn_blocks`
    (mp_tac o REWRITE_RULE [EVERY_MEM]) >>
  disch_then (qspec_then `bb` mp_tac) >> simp[] >>
  simp[EVERY_MEM] >>
  disch_then (qspec_then `inst` mp_tac) >> simp[] >>
  simp[TL, EVERY_MEM] >>
  disch_then (qspec_then `Var v` mp_tac) >>
  impl_tac >- (simp[MEM_EL] >> qexists_tac `i` >> simp[]) >>
  simp[]
QED

(* === args_by_frame: invoke operands are Var-with-frame or Lit *)

(* === easy_and_initial: clone_rel_np, inst_idx, halted, etc. + initial args *)

(* === initial_args: eval_operand invoke_ops[i] matches callee params *)

(* === initial_args_eval: Lit and Var cases for eval_operand *)

(* === initial_args_eval: handles both Lit and Var cases *)

(* === OK case: run_function never returns OK — contradiction *)

(* lift_result is symmetric when both relations are symmetric *)
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

(* Shared helper: lift a terminating result from s_clone_adj to s2.
   s2 runs bb_trunc to get s_jmp, s_clone_adj = s_jmp with vs_prev_bb := NONE.
   The clone entry block has no PHIs, so prev_bb doesn't affect execution.
   Fuel monotonicity lets us combine the two fuel budgets. *)
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
  (* Step 1: run_block fuel mono — run_block (fuel_bb + fuel_adj) = OK s_jmp *)
  `!e. run_block fuel_bb ctx bb_trunc s2 <> Error e` by simp[] >>
  `run_block (fuel_bb + fuel_adj) ctx bb_trunc s2 = OK s_jmp` by
    metis_tac[run_block_fuel_mono] >>
  (* Step 2: unfold run_function (SUC (fuel_bb + fuel_adj)) *)
  CONV_TAC (RAND_CONV (ONCE_REWRITE_CONV [run_function_def])) >>
  ASM_REWRITE_TAC[] >>
  (* Step 3: prev_bb irrelevance — lift_result relates s_jmp and s_jmp with prev_bb := NONE *)
  `lift_result (=) shared_globals_np
     (run_function (fuel_bb + fuel_adj) ctx fn s_jmp)
     (run_function (fuel_bb + fuel_adj) ctx fn (s_jmp with vs_prev_bb := NONE))` by
    (irule run_function_prev_bb_any_fuel >> metis_tac[]) >>
  (* Step 4: fuel mono — run_function (fuel_bb + fuel_adj) = run_function fuel_adj on s_adj *)
  `run_function (fuel_bb + fuel_adj) ctx fn (s_jmp with vs_prev_bb := NONE) =
   run_function fuel_adj ctx fn (s_jmp with vs_prev_bb := NONE)` by (
    `fuel_bb + fuel_adj = fuel_adj + fuel_bb` by simp[] >>
    metis_tac[run_function_fuel_mono]) >>
  (* Step 5: combine — swap via lift_result_sym *)
  gvs[] >>
  irule lift_result_sym >>
  rpt conj_tac
  >- metis_tac[]
  >- simp[shared_globals_np_def]
  >- ASM_REWRITE_TAC[]
QED

(* shared_globals_np is symmetric *)
Triviality shared_globals_np_sym[local]:
  !s1 s2. shared_globals_np s1 s2 ==> shared_globals_np s2 s1
Proof
  simp[shared_globals_np_def]
QED

Triviality jump_to_current_bb[local]:
  !lbl s. (jump_to lbl s).vs_current_bb = lbl
Proof
  REWRITE_TAC[jump_to_def, venom_state_accfupds, combinTheory.K_THM]
QED

Triviality jump_to_halted[local]:
  !lbl s. (jump_to lbl s).vs_halted = s.vs_halted
Proof
  REWRITE_TAC[jump_to_def, venom_state_accfupds, combinTheory.K_THM]
QED

(* clone_entry_block_in_caller_xf: The clone of callee's entry block
   exists in caller_xf, is well-formed, and has no PHI instructions.
   Shared by cs10_halt, cs10_abort, cs10_intret. *)
Triviality clone_entry_block_in_caller_xf[local]:
  !n lc caller callee call_lbl call_idx ret_bb call_bb.
    callee.fn_blocks <> [] /\
    EVERY bb_well_formed callee.fn_blocks /\
    EVERY bb_well_formed caller.fn_blocks /\
    EVERY (\inst. inst.inst_opcode <> PHI)
      (HD callee.fn_blocks).bb_instructions /\
    ALL_DISTINCT (fn_labels callee) /\
    labels_no_inline_return callee /\
    labels_fresh_above n caller /\
    ~MEM (return_block_label (inline_prefix n) lc) (fn_labels caller) /\
    lookup_block (return_block_label (inline_prefix n) lc)
      (inline_call_site (inline_prefix n)
         (return_block_label (inline_prefix n) lc)
         caller callee call_lbl call_idx).fn_blocks = SOME ret_bb /\
    (!bb inst lbl. MEM bb caller.fn_blocks /\
       MEM inst bb.bb_instructions /\
       MEM (Label lbl) inst.inst_operands ==> MEM lbl (fn_labels caller)) /\
    lookup_block call_lbl caller.fn_blocks = SOME call_bb /\
    call_idx < LENGTH call_bb.bb_instructions /\
    ~is_terminator (EL call_idx call_bb.bb_instructions).inst_opcode
    ==>
    ?ce_bb.
      lookup_block (STRCAT (inline_prefix n) (HD callee.fn_blocks).bb_label)
        (fix_inline_phis call_lbl (return_block_label (inline_prefix n) lc)
           ret_bb
           (inline_call_site (inline_prefix n)
              (return_block_label (inline_prefix n) lc)
              caller callee call_lbl call_idx)).fn_blocks = SOME ce_bb /\
      bb_well_formed ce_bb /\
      EVERY (\inst. inst.inst_opcode <> PHI) ce_bb.bb_instructions
Proof
  rpt gen_tac >> strip_tac >>
  (* Derive EVERY succs in caller via combined helper *)
  `EVERY (\l. MEM l (fn_labels caller)) (bb_succs ret_bb)` by
    metis_tac[ret_bb_succs_from_inline_call_site] >>
  (* Step 1: HD callee label is in fn_labels callee *)
  `MEM (HD callee.fn_blocks).bb_label (fn_labels callee)` by (
    Cases_on `callee.fn_blocks` >> gvs[fn_labels_def, MEM_MAP] >>
    qexists_tac `h` >> simp[]) >>
  (* Step 2: clone label not in caller labels *)
  `~MEM (STRCAT (inline_prefix n) (HD callee.fn_blocks).bb_label)
        (fn_labels caller)` by
    metis_tac[prefixed_label_not_in_labels] >>
  (* Step 3: clone label != ret_lbl *)
  `STRCAT (inline_prefix n) (HD callee.fn_blocks).bb_label <>
   return_block_label (inline_prefix n) lc` by
    metis_tac[clone_label_neq_ret_lbl] >>
  (* Step 4: HD callee block exists via lookup_block *)
  `lookup_block (HD callee.fn_blocks).bb_label callee.fn_blocks =
   SOME (HD callee.fn_blocks)` by (
    Cases_on `callee.fn_blocks` >> gvs[lookup_block_def, FIND_thm]) >>
  (* Step 5: lookup in fn_inl *)
  mp_tac (Q.SPECL [`inline_prefix n`,
    `return_block_label (inline_prefix n) lc`,
    `caller`, `callee`, `call_lbl`, `call_idx`,
    `(HD callee.fn_blocks).bb_label`, `HD callee.fn_blocks`]
    lookup_block_clone_in_fn_inl) >>
  ASM_REWRITE_TAC[] >>
  simp[] >> strip_tac >>
  (* Step 6: clone label not in bb_succs ret_bb *)
  `~MEM (STRCAT (inline_prefix n) (HD callee.fn_blocks).bb_label)
        (bb_succs ret_bb)` by
    metis_tac[clone_label_not_in_ret_bb_succs] >>
  (* Step 7: passthrough fix_inline_phis *)
  mp_tac (Q.SPECL [`call_lbl`,
    `return_block_label (inline_prefix n) lc`, `ret_bb`,
    `inline_call_site (inline_prefix n)
       (return_block_label (inline_prefix n) lc)
       caller callee call_lbl call_idx`,
    `STRCAT (inline_prefix n) (HD callee.fn_blocks).bb_label`]
    fix_inline_phis_passthrough) >>
  ASM_REWRITE_TAC[] >> DISCH_TAC >>
  qexists_tac `bb'` >>
  `lookup_block (STRCAT (inline_prefix n) (HD callee.fn_blocks).bb_label)
     (fix_inline_phis call_lbl (return_block_label (inline_prefix n) lc)
        ret_bb
        (inline_call_site (inline_prefix n)
           (return_block_label (inline_prefix n) lc)
           caller callee call_lbl call_idx)).fn_blocks = SOME bb'` by
    ASM_REWRITE_TAC[] >>
  ASM_REWRITE_TAC[] >>
  conj_tac
  >- ((* bb_well_formed *)
    `EVERY bb_well_formed
       (inline_call_site (inline_prefix n)
          (return_block_label (inline_prefix n) lc)
          caller callee call_lbl call_idx).fn_blocks` by
      metis_tac[inline_call_site_every_bb_well_formed] >>
    `EVERY bb_well_formed
       (fix_inline_phis call_lbl (return_block_label (inline_prefix n) lc)
          ret_bb
          (inline_call_site (inline_prefix n)
             (return_block_label (inline_prefix n) lc)
             caller callee call_lbl call_idx)).fn_blocks` by
      (irule fix_inline_phis_every_bb_well_formed >> ASM_REWRITE_TAC[]) >>
    drule_then (fn th => gvs[EVERY_MEM, th]) lookup_block_MEM)
  >- ((* no PHI *)
    irule rewrite_inline_insts_no_phi >>
    REWRITE_TAC[EVERY_MAP] >>
    qpat_x_assum `EVERY _ (HD callee.fn_blocks).bb_instructions` mp_tac >>
    MATCH_MP_TAC EVERY_MONOTONIC >>
    simp[clone_instruction_opcode])
QED

(* lift_result_trans_eq: transitivity when second relation uses (=) for R_ok.
   Shared by cs10_halt, cs10_abort, cs10_intret. *)
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



(* cs10_terminal_combine: From raw assumptions (run_function = Halt/Abort,
   shared_globals_np) plus clone_adj preconditions, directly produce
   the final lift_result. This avoids needing to derive intermediate
   lift_result/terminates facts inside Resume with 100+ assumptions. *)
Triviality cs10_terminal_halt[local]:
  !R_ok v s_clone fuel_adj fuel_bb ctx fn bb_trunc s2 s_jmp ce_lbl ce_bb.
    run_function fuel_adj ctx fn (s_jmp with vs_prev_bb := NONE) = Halt s_clone /\
    shared_globals_np v s_clone /\
    run_block fuel_bb ctx bb_trunc s2 = OK s_jmp /\
    ~s_jmp.vs_halted /\
    lookup_block s2.vs_current_bb fn.fn_blocks = SOME bb_trunc /\
    s_jmp.vs_current_bb = ce_lbl /\
    lookup_block ce_lbl fn.fn_blocks = SOME ce_bb /\
    EVERY (\inst. inst.inst_opcode <> PHI) ce_bb.bb_instructions /\
    bb_well_formed ce_bb
    ==>
    ?fuel_total. lift_result R_ok shared_globals_np (Halt v)
      (run_function fuel_total ctx fn s2)
Proof
  rpt gen_tac >> strip_tac >>
  mp_tac (Q.SPECL [`fuel_adj`, `fuel_bb`, `ctx`, `fn`, `bb_trunc`,
    `s2`, `s_jmp`, `ce_bb`] clone_adj_to_caller_xf) >>
  impl_tac >- (
    rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
    TRY (ASM_REWRITE_TAC[terminates_def, exec_result_case_def] >> BETA_TAC >> NO_TAC) >>
    ASM_REWRITE_TAC[]) >>
  strip_tac >>
  qexists_tac `fuel_total` >>
  mp_tac (Q.SPECL [`R_ok`, `shared_globals_np`, `Halt v`,
    `run_function fuel_adj ctx fn (s_jmp with vs_prev_bb := NONE)`,
    `run_function fuel_total ctx fn s2`] lift_result_trans_eq) >>
  impl_tac >- (rpt strip_tac >> irule shared_globals_np_trans >> metis_tac[]) >>
  DISCH_TAC >> first_x_assum irule >>
  conj_tac >- (ASM_REWRITE_TAC[lift_result_def, exec_result_case_def] >> BETA_TAC) >>
  first_assum ACCEPT_TAC
QED

Triviality cs10_terminal_abort[local]:
  !R_ok a v s_clone fuel_adj fuel_bb ctx fn bb_trunc s2 s_jmp ce_lbl ce_bb.
    run_function fuel_adj ctx fn (s_jmp with vs_prev_bb := NONE) = Abort a s_clone /\
    shared_globals_np v s_clone /\
    run_block fuel_bb ctx bb_trunc s2 = OK s_jmp /\
    ~s_jmp.vs_halted /\
    lookup_block s2.vs_current_bb fn.fn_blocks = SOME bb_trunc /\
    s_jmp.vs_current_bb = ce_lbl /\
    lookup_block ce_lbl fn.fn_blocks = SOME ce_bb /\
    EVERY (\inst. inst.inst_opcode <> PHI) ce_bb.bb_instructions /\
    bb_well_formed ce_bb
    ==>
    ?fuel_total. lift_result R_ok shared_globals_np (Abort a v)
      (run_function fuel_total ctx fn s2)
Proof
  rpt gen_tac >> strip_tac >>
  mp_tac (Q.SPECL [`fuel_adj`, `fuel_bb`, `ctx`, `fn`, `bb_trunc`,
    `s2`, `s_jmp`, `ce_bb`] clone_adj_to_caller_xf) >>
  impl_tac >- (
    rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
    TRY (ASM_REWRITE_TAC[terminates_def, exec_result_case_def] >> BETA_TAC >> NO_TAC) >>
    ASM_REWRITE_TAC[]) >>
  strip_tac >>
  qexists_tac `fuel_total` >>
  mp_tac (Q.SPECL [`R_ok`, `shared_globals_np`, `Abort a v`,
    `run_function fuel_adj ctx fn (s_jmp with vs_prev_bb := NONE)`,
    `run_function fuel_total ctx fn s2`] lift_result_trans_eq) >>
  impl_tac >- (rpt strip_tac >> irule shared_globals_np_trans >> metis_tac[]) >>
  DISCH_TAC >> first_x_assum irule >>
  conj_tac >- (ASM_REWRITE_TAC[lift_result_def, exec_result_case_def] >> BETA_TAC) >>
  first_assum ACCEPT_TAC
QED



(* Shared tactic for cs10 terminal cases (Halt and Abort).
   Assumes the suspended goal has case expression on callee result
   and clone-side existentials to introduce. *)
(* === Halt case: callee halts -> chain bb_trunc + clone -> Halt *)

(* === Abort case: callee aborts -> chain bb_trunc + clone -> Abort *)

(* execution_equiv is preserved by jump_to and prev_bb update *)
Triviality execution_equiv_jump_to_prev_bb[local]:
  !excl_vars s1 s2 lbl.
    execution_equiv excl_vars s1 s2 ==>
    execution_equiv excl_vars s1
      ((jump_to lbl s2) with vs_prev_bb := NONE)
Proof
  rw[execution_equiv_def, jump_to_def,
     venom_state_accfupds, combinTheory.K_THM, lookup_var_def]
QED

(* ctx_fields_match through setup_callee + run_function IntRet *)
Triviality ctx_fields_match_callee_intret[local]:
  !fuel ctx callee args s1_pre callee_s l v.
    setup_callee callee args s1_pre = SOME callee_s /\
    run_function fuel ctx callee callee_s = IntRet l v ==>
    ctx_fields_match s1_pre v
Proof
  rpt strip_tac >>
  imp_res_tac setup_callee_ctx_fields >>
  imp_res_tac run_function_ctx_fields >>
  fs[ctx_fields_match_def]
QED

(* bind_outputs from non-NONE case expression assumption *)
Triviality bind_outputs_from_case[local]:
  !invoke_outs l s1_pre v s_ok.
    (case bind_outputs invoke_outs l (merge_callee_state s1_pre v) of
       NONE => F | SOME s_ok' => s_ok = s_ok') ==>
    bind_outputs invoke_outs l (merge_callee_state s1_pre v) = SOME s_ok
Proof
  rpt strip_tac >>
  Cases_on `bind_outputs invoke_outs l (merge_callee_state s1_pre v)` >> gvs[]
QED

(* LENGTH from bind_outputs SOME *)
Triviality bind_outputs_length[local]:
  !outs vals s s'.
    bind_outputs outs vals s = SOME s' ==> LENGTH outs = LENGTH vals
Proof
  rw[bind_outputs_def] >> BasicProvers.EVERY_CASE_TAC >> gvs[]
QED

(* Frame condition bridges to invoke_clone_bridge's form *)
Triviality frame_to_excl_bridge[local]:
  !excl_vars prefix invoke_outs s_at_ret s_clone_adj.
    (!v. ~isPREFIX prefix v /\ ~MEM v invoke_outs ==>
         lookup_var v s_at_ret = lookup_var v s_clone_adj) /\
    (!v. isPREFIX prefix v ==> v IN excl_vars) ==>
    (!v. v NOTIN excl_vars /\ ~MEM v invoke_outs ==>
         lookup_var v s_at_ret = lookup_var v s_clone_adj)
Proof
  rpt strip_tac >> first_x_assum match_mp_tac >>
  conj_tac >- (CCONTR_TAC >> fs[] >> res_tac) >>
  first_assum ACCEPT_TAC
QED

(* lookup_block ret_lbl in caller_xf passes through fix_inline_phis *)
Triviality ret_lbl_in_caller_xf[local]:
  !ret_lbl fn_inl ret_bb orig_lbl caller_xf.
    lookup_block ret_lbl fn_inl.fn_blocks = SOME ret_bb /\
    caller_xf = fix_inline_phis orig_lbl ret_lbl ret_bb fn_inl /\
    ~MEM ret_lbl (bb_succs ret_bb) ==>
    lookup_block ret_lbl caller_xf.fn_blocks = SOME ret_bb
Proof
  rpt strip_tac >> gvs[] >>
  metis_tac[fix_inline_phis_passthrough]
QED

(* === IntRet case: callee returns normally *)

(* Bridge: derive execution_equiv s_ok s_at_ret from available facts.
   Takes frame condition in "frame" form (¬prefix ∧ ¬MEM) and bridges to excl_vars. *)
Triviality intret_bridge[local]:
  !excl_vars prefix outs s1_pre s_clone callee_s' s_ok s_at_ret vals frame.
    execution_equiv excl_vars s1_pre s_clone /\
    bind_outputs outs vals (merge_callee_state s1_pre callee_s') = SOME s_ok /\
    ALL_DISTINCT outs /\
    shared_globals_np callee_s' s_at_ret /\
    s_at_ret.vs_params = s_clone.vs_params /\
    ~s_at_ret.vs_halted /\
    (frame = (\v. ~isPREFIX prefix v /\ ~MEM v outs)) /\
    (!v. frame v ==> lookup_var v s_at_ret = lookup_var v s_clone) /\
    (!i. i < LENGTH vals /\ i < LENGTH outs ==>
         lookup_var (EL i outs) s_at_ret = SOME (EL i vals)) /\
    (!v. isPREFIX prefix v ==> v IN excl_vars) /\
    ctx_fields_match s1_pre callee_s' /\
    s_at_ret.vs_allocas = s_clone.vs_allocas /\
    ~s1_pre.vs_halted ==>
    execution_equiv excl_vars s_ok s_at_ret
Proof
  rpt strip_tac >>
  irule invoke_clone_bridge >>
  conj_tac >- first_assum ACCEPT_TAC >>
  MAP_EVERY qexists_tac [`callee_s'`, `outs`, `s_clone`, `s1_pre`, `vals`] >>
  rpt conj_tac >> TRY (first_assum ACCEPT_TAC)
  >- (rpt strip_tac >>
      `frame v` by (qpat_x_assum `frame = _` (fn th => REWRITE_TAC[th]) >>
                     BETA_TAC >> conj_tac >- (CCONTR_TAC >> gvs[] >> res_tac)
                     >> first_assum ACCEPT_TAC) >>
      res_tac)
  >- (imp_res_tac bind_outputs_length >> first_assum ACCEPT_TAC)
QED

(* Terminal right-side chain: when run_block at s_at_ret terminates (not OK-non-halted),
   chain through clone_adj_to_caller_xf to get the final lift_result. *)
(* Terminal right-side chain helper: given that run_function at s_at_ret terminates,
   compose with clone_adj_to_caller_xf to get run_function at s2. *)
Triviality terminal_right_chain[local]:
  !fuel_rf fuel_bb fuel_clone ctx caller_xf
   bb_trunc s2 s_at_ret s_jmp ce_bb.
    terminates (run_function fuel_rf ctx caller_xf s_at_ret) /\
    (* Right-side chain *)
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

Triviality extract_labels_every_is_label[local]:
  !ops lbls. extract_labels ops = SOME lbls ==>
    EVERY (\op. IS_SOME (get_label op)) ops
Proof
  Induct >> simp[extract_labels_def] >>
  Cases >> simp[extract_labels_def, get_label_def] >>
  rpt strip_tac >> Cases_on `extract_labels ops` >> gvs[]
QED

(* step_inst_base OK on a terminator implies successor in get_successors.
   Stronger than step_inst_base_term_succs: no inst_wf needed. *)
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

(* run_block OK on bb_well_formed block: current_bb is in bb_succs.
   Stronger than run_block_current_bb_in_succs: no EVERY inst_wf needed. *)
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

Triviality intret_suffix_chain[local]:
  ^(concl functionInlinerIntretChainTheory.intret_suffix_chain)
Proof
  ACCEPT_TAC functionInlinerIntretChainTheory.intret_suffix_chain
QED


(* Helper: lookup_block implies MEM in fn_labels *)
Triviality lookup_block_mem_fn_labels[local]:
  !lbl fn bb. lookup_block lbl fn.fn_blocks = SOME bb ==>
    MEM lbl (fn_labels fn)
Proof
  rw[fn_labels_def, lookup_block_def] >>
  imp_res_tac FIND_MEM >> imp_res_tac FIND_P >>
  fs[MEM_MAP] >> qexists_tac `bb` >> simp[]
QED

(* bind_outputs = FOLDL of update_var, which only touches vs_vars.
   So all other state fields are preserved. *)
Triviality bind_outputs_preserves_labels[local]:
  !outs vals s s'. bind_outputs outs vals s = SOME s' ==>
    s'.vs_labels = s.vs_labels
Proof
  rw[bind_outputs_def] >>
  qsuff_tac `!l s. (FOLDL (\s' (out,val). update_var out val s') s l).vs_labels = s.vs_labels`
  >- metis_tac[] >>
  Induct_on `l` >> simp[] >> Cases >> simp[update_var_def]
QED

Triviality bind_outputs_preserves_current_bb[local]:
  !outs vals s s'. bind_outputs outs vals s = SOME s' ==>
    s'.vs_current_bb = s.vs_current_bb
Proof
  rw[bind_outputs_def] >>
  qsuff_tac `!l s. (FOLDL (\s' (out,val). update_var out val s') s l).vs_current_bb = s.vs_current_bb`
  >- metis_tac[] >>
  Induct_on `l` >> simp[] >> Cases >> simp[update_var_def]
QED

(* Helper: well-formed block suffix (after a non-PHI instruction) has no PHIs.
   Because bb_well_formed says i < j /\ EL j = PHI ==> EL i = PHI.
   If EL k is non-PHI, then for all j > k, EL j <> PHI. *)
Triviality wf_suffix_no_phi[local]:
  !bb k. bb_well_formed bb /\ k < LENGTH bb.bb_instructions /\
    (EL k bb.bb_instructions).inst_opcode <> PHI ==>
    EVERY (\inst. inst.inst_opcode <> PHI) (DROP (k + 1) bb.bb_instructions)
Proof
  rpt strip_tac >>
  REWRITE_TAC[EVERY_MEM] >> rpt strip_tac >>
  FULL_SIMP_TAC std_ss [MEM_DROP] >>
  CCONTR_TAC >>
  FULL_SIMP_TAC std_ss [] >>
  `(EL (m + (k + 1)) bb.bb_instructions).inst_opcode = PHI` by metis_tac[] >>
  `k < m + (k + 1)` by DECIDE_TAC >>
  qpat_x_assum `bb_well_formed bb` mp_tac >>
  REWRITE_TAC[bb_well_formed_def] >> strip_tac >>
  first_x_assum (qspecl_then [`k`, `m + (k + 1)`] mp_tac) >>
  ASM_REWRITE_TAC[]
QED

(* Helper: suffix of a block inherits the "no excluded vars" property *)
Triviality suffix_no_excl_vars[local]:
  !bb k vars.
    EVERY (\inst. !x. MEM (Var x) inst.inst_operands ==> x NOTIN vars)
      bb.bb_instructions /\
    k <= LENGTH bb.bb_instructions ==>
    EVERY (\inst. !x. MEM (Var x) inst.inst_operands ==> x NOTIN vars)
      (DROP k bb.bb_instructions)
Proof
  rpt strip_tac >> irule EVERY_DROP >> first_assum ACCEPT_TAC
QED

(* Helper: execution_equiv is preserved by vs_inst_idx update *)
Triviality execution_equiv_inst_idx_update[local]:
  !vars s1 s2 n. execution_equiv vars s1 s2 ==>
    execution_equiv vars (s1 with vs_inst_idx := n) s2
Proof
  rw[execution_equiv_def, lookup_var_def, update_var_def] >> simp[]
QED

(* Helper: run_block_reaches preserves vs_current_bb *)
Triviality run_block_reaches_preserves_current_bb[local]:
  !k fuel ctx bb s s'.
    run_block_reaches fuel ctx bb s k = SOME s' /\
    (!i. s.vs_inst_idx <= i /\ i < s.vs_inst_idx + k ==>
         ~is_terminator (EL i bb.bb_instructions).inst_opcode) ==>
    s'.vs_current_bb = s.vs_current_bb
Proof
  Induct >- simp[run_block_reaches_def] >>
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `run_block_reaches _ _ _ _ (SUC _) = _` mp_tac >>
  simp[run_block_reaches_def] >>
  BasicProvers.EVERY_CASE_TAC >> simp[] >>
  strip_tac >>
  `~is_terminator x.inst_opcode` by (
    first_x_assum (qspec_then `s.vs_inst_idx` mp_tac) >> simp[]) >>
  gvs[] >>
  `v.vs_current_bb = s.vs_current_bb` by
    metis_tac[step_preserves_control_flow] >>
  `s'.vs_current_bb = v.vs_current_bb` by (
    first_x_assum (qspecl_then [`fuel`, `ctx`, `bb`,
      `v with vs_inst_idx := SUC s.vs_inst_idx`, `s'`] mp_tac) >>
    simp[] >> disch_then irule >>
    rpt strip_tac >> first_x_assum (qspec_then `i` mp_tac) >> simp[]) >>
  simp[]
QED

(* Helper: derive s_ok.vs_current_bb = s.vs_current_bb through the chain *)
Triviality bind_merge_preserves_current_bb[local]:
  !invoke_outs l s1_pre v s_ok.
    bind_outputs invoke_outs l (merge_callee_state s1_pre v) = SOME s_ok ==>
    s_ok.vs_current_bb = s1_pre.vs_current_bb
Proof
  rpt strip_tac >>
  imp_res_tac bind_outputs_preserves_current_bb >>
  gvs[merge_callee_state_def]
QED

(* Combined helper: s_ok.vs_current_bb = s_orig.vs_current_bb
   through bind_outputs + merge + run_block_reaches chain *)
Triviality sok_current_bb_eq[local]:
  !invoke_outs l s1_pre v s_ok k fuel ctx bb s_orig.
    bind_outputs invoke_outs l (merge_callee_state s1_pre v) = SOME s_ok /\
    run_block_reaches fuel ctx bb s_orig k = SOME s1_pre /\
    s_orig.vs_inst_idx = 0 /\
    (!i. i < k ==> ~is_terminator (EL i bb.bb_instructions).inst_opcode) ==>
    s_ok.vs_current_bb = s_orig.vs_current_bb
Proof
  rpt strip_tac >>
  imp_res_tac bind_merge_preserves_current_bb >>
  `s1_pre.vs_current_bb = s_orig.vs_current_bb` by (
    mp_tac (Q.SPECL [`k`, `fuel`, `ctx`, `bb`, `s_orig`, `s1_pre`]
      run_block_reaches_preserves_current_bb) >>
    impl_tac >- (conj_tac >- first_assum ACCEPT_TAC >> simp[]) >>
    simp[]) >>
  simp[]
QED

(* Helper: run_block_preserves_labels lifted to FDOM *)
Triviality run_block_preserves_labels_FDOM[local]:
  !fuel ctx bb s s'.
    run_block fuel ctx bb s = OK s' ==>
    FDOM s'.vs_labels = FDOM s.vs_labels
Proof
  rpt strip_tac >> imp_res_tac run_block_preserves_labels >> gvs[]
QED

(* Helper: clone_entry_lbl is STRCAT prefix (HD callee.fn_blocks).bb_label *)
Triviality clone_entry_lbl_eq[local]:
  !pfx callee.
    callee.fn_blocks <> [] ==>
    (case (clone_function pfx callee).fn_blocks of
       [] => "" | eb::v1 => eb.bb_label) =
    STRCAT pfx (HD callee.fn_blocks).bb_label
Proof
  rpt strip_tac >> Cases_on `callee.fn_blocks` >>
  gvs[clone_function_def, clone_basic_block_def]
QED

(* Phase 8+: Apply intret_suffix_chain with derived preconditions *)

(* === Standalone initial_args lemma ===
   Proves: ∀i. eval_operand invoke_ops[i] s_clone_adj = SOME args[i] ∧
                callee_s.vs_params[i] = args[i]
   Replaces the fragile iae_var_tac/initial_args_eval_tac/initial_args_tac val chain.
   Key advantage: no variable-name sensitivity (s' clash issue). *)
Triviality initial_args_bridge[local]:
  !invoke_ops invoke_inst arg_ops args s1_pre s2' callee_s
   callee excl_vars bb clone_entry_lbl.
    decode_invoke invoke_inst = SOME (callee.fn_name, arg_ops) /\
    Abbrev (invoke_ops = rotate_invoke_ops invoke_inst.inst_operands) /\
    eval_operands arg_ops s1_pre = SOME args /\
    FDOM s1_pre.vs_labels = {} /\
    callee_s.vs_params = args /\
    execution_equiv excl_vars s1_pre s2' /\
    MEM invoke_inst bb.bb_instructions /\
    invoke_inst.inst_operands = Label callee.fn_name :: arg_ops /\
    (!inst'. MEM inst' bb.bb_instructions ==>
       !x. MEM (Var x) inst'.inst_operands ==> x NOTIN excl_vars) ==>
    !i. i < LENGTH invoke_ops /\ i < LENGTH args ==>
        eval_operand (EL i invoke_ops)
          ((jump_to clone_entry_lbl s2') with vs_prev_bb := NONE) =
            SOME (EL i args) /\
        callee_s.vs_params ❲i❳ = args ❲i❳
Proof
  rpt gen_tac >> strip_tac >> rpt gen_tac >> strip_tac >>
  conj_tac
  >- (
    mp_tac (Q.SPECL [`invoke_ops`, `invoke_inst`, `arg_ops`, `args`,
      `s1_pre`, `callee.fn_name`, `i`] invoke_ops_el_classify) >>
    (impl_tac >- simp[]) >> strip_tac >>
    gvs[eval_operand_def, jump_to_def, lookup_var_def] >>
    (* Var case: need FLOOKUP s2'.vs_vars v = SOME callee_s.vs_params[i] *)
    (* Get v NOTIN excl_vars via: MEM (Var v) invoke_inst.inst_operands *)
    qpat_x_assum `Abbrev (invoke_ops = _)` mp_tac >>
    simp[markerTheory.Abbrev_def, rotate_invoke_ops_def] >> strip_tac >>
    (* invoke_ops = arg_ops ++ [Label name], EL i invoke_ops = Var v,
       so MEM (Var v) invoke_ops, so MEM (Var v) arg_ops (not Label),
       so MEM (Var v) invoke_inst.inst_operands *)
    qpat_x_assum `!inst'. MEM inst' bb.bb_instructions ==> _`
      (qspec_then `invoke_inst` mp_tac) >>
    (impl_tac >- first_assum ACCEPT_TAC) >>
    disch_then (qspec_then `v` mp_tac) >>
    (impl_tac >- metis_tac[EL_MEM, MEM_APPEND, MEM, operand_distinct]) >>
    strip_tac >>
    (* v NOTIN excl_vars ==> lookup_var v s1_pre = lookup_var v s2' *)
    qpat_x_assum `execution_equiv _ _ _` mp_tac >>
    simp[execution_equiv_def] >> strip_tac >>
    first_x_assum (qspec_then `v` mp_tac) >> simp[] >>
    simp[lookup_var_def])
  >- simp[]
QED

(* === Error case: callee errors → step_inst errors → contradiction *)
(* ===============================================================
   Val tactic definitions for cs10 subtree.
   These replace the suspend/Resume tree with direct tactic calls.
   Order: leaves first (bottom-up in dependency tree).
   =============================================================== *)

(* --- initial_args_tac: uses initial_args_bridge via forward reasoning ---
   Uses qspecl_then + mp_tac to avoid MATCH_MP_TAC unification failures
   when record projections (e.g. callee_s.vs_params) appear in goal. *)
val initial_args_tac : tactic =
  qunabbrev_tac `s_clone_adj` >> qunabbrev_tac `s_jmp` >>
  qspecl_then [`invoke_ops`, `invoke_inst`, `arg_ops`, `args`,
    `s1_pre`, `s2'`, `callee_s`, `callee`, `excl_vars`, `bb`,
    `clone_entry_lbl`] mp_tac initial_args_bridge >>
  (impl_tac >- (
    rpt conj_tac >>
    TRY (first_assum ACCEPT_TAC) >>
    TRY (ASM_REWRITE_TAC[]) >>
    TRY (metis_tac[decode_invoke_operands]))) >>
  DISCH_THEN MATCH_ACCEPT_TAC;

(* --- easy_and_initial_tac: clone_rel_np, inst_idx, halted, etc. + initial args --- *)
val easy_and_initial_tac : tactic =
  conj_tac >- first_assum ACCEPT_TAC >>   (* clone_rel_np *)
  conj_tac >- first_assum ACCEPT_TAC >>   (* vs_inst_idx = 0 *)
  conj_tac >- first_assum ACCEPT_TAC >>   (* callee_s.vs_inst_idx = 0 *)
  conj_tac >- ASM_REWRITE_TAC[] >>        (* ~callee_s.vs_halted *)
  conj_tac >- first_assum ACCEPT_TAC >>   (* vs_current_bb *)
  conj_tac >- first_assum ACCEPT_TAC >>   (* LENGTH *)
  (* Last conjunct: forall i. eval_operand + params *)
  initial_args_tac;

(* --- per_block_sim_tac: callee blocks -> clone blocks in caller_xf --- *)
val per_block_sim_tac : tactic =
  (* Substitute all relevant Abbrevs in dependency order *)
  SUBST_NAMED_ABBREV_TAC `Abbrev (invoke_inst = _)` >>
  SUBST_NAMED_ABBREV_TAC `Abbrev (invoke_ops = _)` >>
  SUBST_NAMED_ABBREV_TAC `Abbrev (invoke_outs = _)` >>
  SUBST_NAMED_ABBREV_TAC `Abbrev (prefix = _)` >>
  SUBST_NAMED_ABBREV_TAC `Abbrev (ret_lbl = _)` >>
  SUBST_NAMED_ABBREV_TAC `Abbrev (fn_inl = _)` >>
  SUBST_NAMED_ABBREV_TAC `Abbrev (caller_xf = _)` >>
  (* Derive ret_bb succs in caller via combined helper *)
  `EVERY (\l. MEM l (fn_labels caller)) (bb_succs ret_bb)` by
    metis_tac[ret_bb_succs_from_inline_call_site] >>
  mp_tac (Q.SPECL [
    `ist.is_inline_count`, `ist.is_label_counter`,
    `caller`, `callee`, `s2.vs_current_bb`, `s1_pre.vs_inst_idx`,
    `bb`, `ret_bb`, `args`, `ctx`] per_block_sim_helper) >>
  impl_tac
  >- (rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
      TRY (REWRITE_TAC[fn_labels_def] >> first_assum ACCEPT_TAC)) >>
  REWRITE_TAC[LET_THM] >> BETA_TAC >>
  DISCH_THEN MATCH_ACCEPT_TAC;

(* --- frame_tac: clone blocks preserve frame variables --- *)
val frame_tac : tactic =
  (* Unfold ALL Abbrevs via SUBST_ALL_TAC FIRST, then strip *)
  qpat_x_assum `Abbrev (invoke_inst = _)` (SUBST_ALL_TAC o REWRITE_RULE [markerTheory.Abbrev_def]) >>
  qpat_x_assum `Abbrev (invoke_outs = _)` (SUBST_ALL_TAC o REWRITE_RULE [markerTheory.Abbrev_def]) >>
  qpat_x_assum `Abbrev (frame = _)` (SUBST_ALL_TAC o REWRITE_RULE [markerTheory.Abbrev_def]) >>
  qpat_x_assum `Abbrev (prefix = _)` (SUBST_ALL_TAC o REWRITE_RULE [markerTheory.Abbrev_def]) >>
  qpat_x_assum `Abbrev (ret_lbl = _)` (SUBST_ALL_TAC o REWRITE_RULE [markerTheory.Abbrev_def]) >>
  qpat_x_assum `Abbrev (fn_inl = _)` (SUBST_ALL_TAC o REWRITE_RULE [markerTheory.Abbrev_def]) >>
  qpat_x_assum `Abbrev (caller_xf = _)` (SUBST_ALL_TAC o REWRITE_RULE [markerTheory.Abbrev_def]) >>
  (* Now strip the goal *)
  rpt gen_tac >> strip_tac >>
  gen_tac >> BETA_TAC >> strip_tac >>
  (* Apply frame_proof_helper via irule + fill all 17 existentials *)
  irule frame_proof_helper >>
  qexistsl_tac [
    `bb'`, `bb`, `s2.vs_current_bb`, `callee`, `caller`,
    `fix_inline_phis s2.vs_current_bb
       (return_block_label (inline_prefix ist.is_inline_count) ist.is_label_counter)
       ret_bb
       (inline_call_site (inline_prefix ist.is_inline_count)
          (return_block_label (inline_prefix ist.is_inline_count) ist.is_label_counter)
          caller callee s2.vs_current_bb s1_pre.vs_inst_idx)`,
    `ctx`,
    `inline_call_site (inline_prefix ist.is_inline_count)
       (return_block_label (inline_prefix ist.is_inline_count) ist.is_label_counter)
       caller callee s2.vs_current_bb s1_pre.vs_inst_idx`,
    `fuel'`, `s1_pre.vs_inst_idx`,
    `bb.bb_instructions ❲s1_pre.vs_inst_idx❳`,
    `bb.bb_instructions ❲s1_pre.vs_inst_idx❳.inst_outputs`,
    `lbl`, `ist.is_label_counter`, `ist.is_inline_count`, `ret_bb`,
    `return_block_label (inline_prefix ist.is_inline_count) ist.is_label_counter`
  ] >>
  ASM_REWRITE_TAC[] >>
  irule EL_MEM >> ASM_REWRITE_TAC[];

(* --- args_by_frame_tac: invoke args are frame-preserved or constant --- *)
val args_by_frame_tac : tactic =
  rpt strip_tac >>
  (* Classify invoke_ops[i] as Var or Lit *)
  mp_tac (Q.SPECL [`invoke_ops`, `invoke_inst`, `arg_ops`, `args`,
    `s1_pre`, `callee.fn_name`, `i`] invoke_ops_el_classify) >>
  ASM_REWRITE_TAC[] >>
  strip_tac >| [
    (* Var case: invoke_ops[i] = Var v *)
    qexists_tac `v` >> DISJ1_TAC >> ASM_REWRITE_TAC[] >>
    qpat_x_assum `Abbrev (frame = _)` mp_tac >>
    REWRITE_TAC[markerTheory.Abbrev_def] >>
    DISCH_THEN SUBST1_TAC >> REWRITE_TAC[] >>
    (* Need: ~isPREFIX prefix v /\ ~MEM v invoke_outs *)
    qpat_x_assum `Abbrev (invoke_outs = _)` mp_tac >>
    REWRITE_TAC[markerTheory.Abbrev_def] >>
    DISCH_THEN SUBST1_TAC >>
    qpat_x_assum `Abbrev (prefix = _)` mp_tac >>
    REWRITE_TAC[markerTheory.Abbrev_def] >>
    DISCH_THEN SUBST1_TAC >>
    BETA_TAC >>
    mp_tac (Q.SPECL [`ist.is_inline_count`, `caller`, `bb`,
      `invoke_inst`, `callee.fn_name`, `arg_ops`, `invoke_ops`,
      `i`, `v`] invoke_ops_var_in_frame) >>
    ASM_REWRITE_TAC[] >>
    (* Discharge i < LENGTH arg_ops *)
    (impl_tac >- (
      mp_tac (Q.SPECL [`invoke_ops`, `invoke_inst`, `arg_ops`, `args`,
        `s1_pre`, `callee.fn_name`, `i`] invoke_ops_el_decompose) >>
      ASM_REWRITE_TAC[] >> strip_tac >> ASM_REWRITE_TAC[])) >>
    REWRITE_TAC[],
    (* Lit case *)
    qexists_tac `""` >> DISJ2_TAC >> qexists_tac `w` >> ASM_REWRITE_TAC[]
  ];

(* --- cs10_discharge_tac: discharge clone_execution_sim_ext preconditions --- *)
val cs10_discharge_tac : tactic =
  (* Common facts for multiple sub-goals *)
  `MEM bb caller.fn_blocks` by metis_tac[lookup_block_MEM] >>
  `MEM invoke_inst bb.bb_instructions` by (
    qpat_assum `Abbrev (invoke_inst = _)` mp_tac >>
    simp[markerTheory.Abbrev_def] >> metis_tac[MEM_EL]) >>
  `invoke_inst.inst_operands = Label callee.fn_name :: arg_ops` by
    metis_tac[decode_invoke_operands] >>
  (* Derive LENGTH/is_label_op for per_block_sim_helper *)
  `LENGTH (rotate_invoke_ops invoke_inst.inst_operands) >= LENGTH args /\
   (!i. i < LENGTH args ==>
        ~is_label_op (EL i (rotate_invoke_ops invoke_inst.inst_operands)))` by
    (mp_tac (Q.SPECL [`invoke_inst`, `arg_ops`, `args`, `s1_pre`,
       `callee.fn_name`] invoke_ops_length_and_no_label) >>
     impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC) >>
     REWRITE_TAC[]) >>
  (* Now have: MEM bb, MEM invoke_inst, inst_operands = Label :: arg_ops,
     LENGTH/is_label_op *)
  conj_tac >- per_block_sim_tac >>
  conj_tac >- frame_tac >>
  (* Allocas: clone block OK steps preserve vs_allocas *)
  conj_tac >- (
    rpt gen_tac >> strip_tac >>
    irule run_block_no_alloca_preserves_allocas >>
    first_assum (irule_at Any) >>
    drule_all fn_no_alloca_lookup >> simp[]
  ) >>
  conj_tac >- args_by_frame_tac >>
  (* Remaining: easy conjuncts + initial_args *)
  easy_and_initial_tac;

(* --- cs10_ok_tac: OK case contradiction --- *)
val cs10_ok_tac : tactic =
  fs[run_function_not_OK];

(* --- cs10_halt_tac: Halt case --- *)
val cs10_halt_tac : tactic =
  (* Phase 1 *)
  REWRITE_TAC[exec_result_case_def] >> BETA_TAC >> strip_tac >>
  qpat_x_assum `exec_result_CASE (Halt v) _ _ _ _ _` mp_tac >>
  REWRITE_TAC[exec_result_case_def] >> BETA_TAC >> DISCH_TAC >>
  (* Phase 2 *)
  qpat_x_assum `run_block fuel ctx bb s1 = _` mp_tac >>
  ASM_REWRITE_TAC[exec_result_case_def] >> BETA_TAC >> DISCH_TAC >>
  qpat_x_assum `run_function (SUC fuel) ctx caller s1 = _` mp_tac >>
  ASM_REWRITE_TAC[exec_result_case_def] >> BETA_TAC >> DISCH_TAC >>
  (* Phase 3 *)
  ASM_REWRITE_TAC[lift_result_def] >>
  (* Phase 4 *)
  SUBST_NAMED_ABBREV_TAC `Abbrev (s_clone_adj = _)` >>
  SUBST_NAMED_ABBREV_TAC `Abbrev (s_jmp = _)` >>
  SUBST_NAMED_ABBREV_TAC `Abbrev (invoke_inst = _)` >>
  SUBST_NAMED_ABBREV_TAC `Abbrev (prefix = _)` >>
  SUBST_NAMED_ABBREV_TAC `Abbrev (ret_lbl = _)` >>
  SUBST_NAMED_ABBREV_TAC `Abbrev (fn_inl = _)` >>
  SUBST_NAMED_ABBREV_TAC `Abbrev (caller_xf = _)` >>
  (* Phase 5 *)
  mp_tac (Q.SPECL [`ist.is_inline_count`, `ist.is_label_counter`,
    `caller`, `callee`, `s2.vs_current_bb`, `s1_pre.vs_inst_idx`,
    `ret_bb`, `bb`] clone_entry_block_in_caller_xf) >>
  (impl_tac >- ASM_REWRITE_TAC[] >> strip_tac) >>
  (* Phase 6: Apply cs10_terminal_halt *)
  mp_tac (Q.SPECL [`state_equiv excl_vars`, `v`, `s_clone'`,
    `fuel'`, `fuel`, `ctx`,
    `fix_inline_phis s2.vs_current_bb
       (return_block_label (inline_prefix ist.is_inline_count) ist.is_label_counter)
       ret_bb
       (inline_call_site (inline_prefix ist.is_inline_count)
          (return_block_label (inline_prefix ist.is_inline_count) ist.is_label_counter)
          caller callee s2.vs_current_bb s1_pre.vs_inst_idx)`,
    `bb_trunc`, `s2`,
    `jump_to clone_entry_lbl s2'`, `clone_entry_lbl`, `ce_bb`] cs10_terminal_halt) >>
  impl_tac >- ASM_REWRITE_TAC[jump_to_current_bb, jump_to_halted] >>
  DISCH_THEN ACCEPT_TAC;

(* --- cs10_abort_tac: Abort case --- *)
val cs10_abort_tac : tactic =
  (* Phase 1 *)
  REWRITE_TAC[exec_result_case_def] >> BETA_TAC >> strip_tac >>
  qpat_x_assum `exec_result_CASE (Abort a v) _ _ _ _ _` mp_tac >>
  REWRITE_TAC[exec_result_case_def] >> BETA_TAC >> DISCH_TAC >>
  (* Phase 2 *)
  qpat_x_assum `run_block fuel ctx bb s1 = _` mp_tac >>
  ASM_REWRITE_TAC[exec_result_case_def] >> BETA_TAC >> DISCH_TAC >>
  qpat_x_assum `run_function (SUC fuel) ctx caller s1 = _` mp_tac >>
  ASM_REWRITE_TAC[exec_result_case_def] >> BETA_TAC >> DISCH_TAC >>
  (* Phase 3 *)
  ASM_REWRITE_TAC[lift_result_def] >>
  (* Phase 4 *)
  SUBST_NAMED_ABBREV_TAC `Abbrev (s_clone_adj = _)` >>
  SUBST_NAMED_ABBREV_TAC `Abbrev (s_jmp = _)` >>
  SUBST_NAMED_ABBREV_TAC `Abbrev (invoke_inst = _)` >>
  SUBST_NAMED_ABBREV_TAC `Abbrev (prefix = _)` >>
  SUBST_NAMED_ABBREV_TAC `Abbrev (ret_lbl = _)` >>
  SUBST_NAMED_ABBREV_TAC `Abbrev (fn_inl = _)` >>
  SUBST_NAMED_ABBREV_TAC `Abbrev (caller_xf = _)` >>
  (* Phase 5 *)
  mp_tac (Q.SPECL [`ist.is_inline_count`, `ist.is_label_counter`,
    `caller`, `callee`, `s2.vs_current_bb`, `s1_pre.vs_inst_idx`,
    `ret_bb`, `bb`] clone_entry_block_in_caller_xf) >>
  (impl_tac >- ASM_REWRITE_TAC[] >> strip_tac) >>
  (* Phase 6: Apply cs10_terminal_abort *)
  mp_tac (Q.SPECL [`state_equiv excl_vars`, `a`, `v`, `s_clone'`,
    `fuel'`, `fuel`, `ctx`,
    `fix_inline_phis s2.vs_current_bb
       (return_block_label (inline_prefix ist.is_inline_count) ist.is_label_counter)
       ret_bb
       (inline_call_site (inline_prefix ist.is_inline_count)
          (return_block_label (inline_prefix ist.is_inline_count) ist.is_label_counter)
          caller callee s2.vs_current_bb s1_pre.vs_inst_idx)`,
    `bb_trunc`, `s2`,
    `jump_to clone_entry_lbl s2'`, `clone_entry_lbl`, `ce_bb`] cs10_terminal_abort) >>
  impl_tac >- ASM_REWRITE_TAC[jump_to_current_bb, jump_to_halted] >>
  DISCH_THEN ACCEPT_TAC;

(* --- intret_chain_tac: IntRet chain simulation (largest piece, ~220 lines) --- *)
val intret_chain_tac : tactic =
  (* IC0: ret_lbl <> bb_lbl *)
  `return_block_label (inline_prefix ist.is_inline_count)
     ist.is_label_counter <> s2.vs_current_bb` by
    metis_tac[lookup_block_mem_fn_labels] >>
  (* IC1: ret_bb instructions = suffix of bb *)
  `ret_bb.bb_instructions = DROP (s1_pre.vs_inst_idx + 1) bb.bb_instructions /\
   ret_bb.bb_label = return_block_label
     (inline_prefix ist.is_inline_count) ist.is_label_counter` by (
    mp_tac (Q.SPECL [`inline_prefix ist.is_inline_count`,
      `return_block_label (inline_prefix ist.is_inline_count)
         ist.is_label_counter`,
      `caller`, `callee`, `s2.vs_current_bb`, `s1_pre.vs_inst_idx`,
      `bb`, `ret_bb`]
      inline_call_site_ret_bb_instructions) >>
    impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC) >>
    DISCH_TAC >> first_assum ACCEPT_TAC) >>
  (* IC2: bb_well_formed ret_bb *)
  `bb_well_formed ret_bb` by (
    `EVERY bb_well_formed
       (inline_call_site (inline_prefix ist.is_inline_count)
          (return_block_label (inline_prefix ist.is_inline_count)
             ist.is_label_counter) caller callee s2.vs_current_bb
          s1_pre.vs_inst_idx).fn_blocks` by (
      mp_tac (Q.SPECL [`inline_prefix ist.is_inline_count`,
        `return_block_label (inline_prefix ist.is_inline_count)
           ist.is_label_counter`,
        `caller`, `callee`, `s2.vs_current_bb`, `s1_pre.vs_inst_idx`]
        (INST [``call_bb:basic_block`` |-> ``bb:basic_block``]
          inline_call_site_every_bb_well_formed)) >>
      impl_tac >- (
        rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
        ASM_REWRITE_TAC[is_terminator_def]) >>
      DISCH_TAC >> first_assum ACCEPT_TAC) >>
    metis_tac[lookup_block_MEM, EVERY_MEM]) >>
  (* IC3: no PHI in ret_bb *)
  `EVERY (\inst. inst.inst_opcode <> PHI) ret_bb.bb_instructions` by (
    ASM_REWRITE_TAC[] >>
    mp_tac (Q.SPECL [`bb`, `s1_pre.vs_inst_idx`] wf_suffix_no_phi) >>
    (impl_tac >- (
      rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
      ASM_REWRITE_TAC[EVAL ``INVOKE = PHI``])) >>
    DISCH_TAC >> first_assum ACCEPT_TAC) >>
  (* IC4: no excl_vars in ret_bb operands *)
  `EVERY (\inst. !x. MEM (Var x) inst.inst_operands ==> x NOTIN excl_vars)
     ret_bb.bb_instructions` by (
    ASM_REWRITE_TAC[] >>
    irule EVERY_DROP >>
    REWRITE_TAC[EVERY_MEM] >> BETA_TAC >>
    rpt strip_tac >> RES_TAC) >>
  (* IC5: lift_result on run_block suffix *)
  `lift_result
     (\s1' s2''. execution_equiv excl_vars s1' s2'' /\
                 s1'.vs_current_bb = s2''.vs_current_bb)
     (\s1' s2''. execution_equiv excl_vars s1' s2'')
     (run_block fuel ctx bb (s_ok with vs_inst_idx := SUC s1_pre.vs_inst_idx))
     (run_block fuel ctx ret_bb s_at_ret)` by (
    mp_tac (Q.SPECL [`fuel`, `ctx`, `bb`, `ret_bb`, `excl_vars`,
      `s_ok with vs_inst_idx := SUC s1_pre.vs_inst_idx`,
      `s_at_ret`, `SUC s1_pre.vs_inst_idx`]
      run_block_suffix_exec_equiv) >>
    impl_tac >- (
      rpt conj_tac >> TRY (first_assum ACCEPT_TAC)
      >- (ASM_REWRITE_TAC[] >> REWRITE_TAC[arithmeticTheory.ADD1])
      >- (irule execution_equiv_inst_idx_update >> first_assum ACCEPT_TAC)
      >- REWRITE_TAC[venomStateTheory.venom_state_accfupds,
                       combinTheory.K_THM]
      >> DECIDE_TAC) >>
    DISCH_TAC >> first_assum ACCEPT_TAC) >>
  (* IC6: ret_lbl not in bb_succs ret_bb *)
  `~MEM (return_block_label (inline_prefix ist.is_inline_count)
           ist.is_label_counter) (bb_succs ret_bb)` by (
    strip_tac >>
    `?inst. MEM inst ret_bb.bb_instructions /\
            MEM (Label (return_block_label (inline_prefix ist.is_inline_count)
                   ist.is_label_counter)) inst.inst_operands` by
      metis_tac[bb_succs_from_operands] >>
    `MEM inst bb.bb_instructions` by (
      qpat_x_assum `ret_bb.bb_instructions = _` mp_tac >>
      DISCH_TAC >> FULL_SIMP_TAC bool_ss [MEM_DROP] >>
      metis_tac[MEM_EL]) >>
    `MEM (Label (return_block_label (inline_prefix ist.is_inline_count)
            ist.is_label_counter))
         (FLAT (MAP (\i. i.inst_operands) bb.bb_instructions))` by
      (REWRITE_TAC[MEM_FLAT, MEM_MAP] >> metis_tac[]) >>
    metis_tac[]) >>
  (* IC6b: lookup ret_lbl in caller_xf = SOME ret_bb *)
  `lookup_block
     (return_block_label (inline_prefix ist.is_inline_count)
        ist.is_label_counter)
     (fix_inline_phis s2.vs_current_bb
        (return_block_label (inline_prefix ist.is_inline_count)
           ist.is_label_counter) ret_bb
        (inline_call_site (inline_prefix ist.is_inline_count)
           (return_block_label (inline_prefix ist.is_inline_count)
              ist.is_label_counter) caller callee s2.vs_current_bb
           s1_pre.vs_inst_idx)).fn_blocks = SOME ret_bb` by (
    mp_tac (Q.SPECL [`s2.vs_current_bb`,
      `return_block_label (inline_prefix ist.is_inline_count)
         ist.is_label_counter`,
      `ret_bb`,
      `inline_call_site (inline_prefix ist.is_inline_count)
         (return_block_label (inline_prefix ist.is_inline_count)
            ist.is_label_counter) caller callee s2.vs_current_bb
         s1_pre.vs_inst_idx`,
      `return_block_label (inline_prefix ist.is_inline_count)
         ist.is_label_counter`]
      fix_inline_phis_passthrough) >>
    (impl_tac >- first_assum ACCEPT_TAC) >>
    DISCH_TAC >> ASM_REWRITE_TAC[]) >>
  (* IC7: FDOM s_ok.vs_labels = {} *)
  `s_ok.vs_labels = s1_pre.vs_labels` by (
    `(merge_callee_state s1_pre v).vs_labels = s1_pre.vs_labels` by
      REWRITE_TAC[merge_callee_state_def,
        venomStateTheory.venom_state_accfupds, combinTheory.K_THM] >>
    `s_ok.vs_labels = (merge_callee_state s1_pre v).vs_labels` suffices_by
      ASM_REWRITE_TAC[] >>
    mp_tac (Q.SPECL [`invoke_outs`, `l`, `merge_callee_state s1_pre v`, `s_ok`]
      bind_outputs_preserves_labels) >>
    (impl_tac >- first_assum ACCEPT_TAC) >>
    DISCH_TAC >> first_assum ACCEPT_TAC) >>
  `FDOM s_ok.vs_labels = {}` by ASM_REWRITE_TAC[] >>
  (* IC8: SUC s1_pre.vs_inst_idx <= LENGTH bb.bb_instructions *)
  `SUC s1_pre.vs_inst_idx <= LENGTH bb.bb_instructions` by DECIDE_TAC >>
  (* IC9: labels preservation for run_block on bb and ret_bb *)
  `(!f s s'. run_block f ctx bb s = OK s' ==>
     FDOM s'.vs_labels = FDOM s.vs_labels) /\
   (!f s s'. run_block f ctx ret_bb s = OK s' ==>
     FDOM s'.vs_labels = FDOM s.vs_labels)` by
    metis_tac[run_block_preserves_labels_FDOM] >>
  (* IC9b: s_ok.vs_current_bb = s2.vs_current_bb *)
  `s_ok.vs_current_bb = s2.vs_current_bb` by (
    `s_ok.vs_current_bb = s1.vs_current_bb` by (
      mp_tac (Q.SPECL [`invoke_outs`, `l`, `s1_pre`, `v`, `s_ok`,
        `s1_pre.vs_inst_idx`, `fuel`, `ctx`, `bb`, `s1`]
        sok_current_bb_eq) >>
      (impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)) >>
      DISCH_TAC >> first_assum ACCEPT_TAC) >>
    ASM_REWRITE_TAC[]) >>
  (* IC9c_pre: clone_entry_lbl = STRCAT prefix (HD callee.fn_blocks).bb_label *)
  `clone_entry_lbl =
     STRCAT (inline_prefix ist.is_inline_count)
       (HD callee.fn_blocks).bb_label` by (
    qpat_x_assum `Abbrev (clone_entry_lbl = _)` mp_tac >>
    REWRITE_TAC[markerTheory.Abbrev_def] >> DISCH_TAC >>
    ASM_REWRITE_TAC[] >>
    mp_tac (Q.SPECL [`inline_prefix ist.is_inline_count`, `callee`]
      clone_entry_lbl_eq) >>
    (impl_tac >- ASM_REWRITE_TAC[GSYM fn_has_entry_def]) >>
    DISCH_TAC >> first_assum ACCEPT_TAC) >>
  (* IC9c: clone_entry_block properties *)
  `?ce_bb. lookup_block clone_entry_lbl
     (fix_inline_phis s2.vs_current_bb
        (return_block_label (inline_prefix ist.is_inline_count)
           ist.is_label_counter) ret_bb
        (inline_call_site (inline_prefix ist.is_inline_count)
           (return_block_label (inline_prefix ist.is_inline_count)
              ist.is_label_counter) caller callee s2.vs_current_bb
           s1_pre.vs_inst_idx)).fn_blocks = SOME ce_bb /\
     EVERY (\inst. inst.inst_opcode <> PHI) ce_bb.bb_instructions /\
     bb_well_formed ce_bb` by (
    ASM_REWRITE_TAC[] >>
    mp_tac (Q.SPECL [`ist.is_inline_count`, `ist.is_label_counter`,
      `caller`, `callee`, `s2.vs_current_bb`, `s1_pre.vs_inst_idx`,
      `ret_bb`, `bb`] clone_entry_block_in_caller_xf) >>
    (impl_tac >- ASM_REWRITE_TAC[]) >>
    strip_tac >> qexists_tac `ce_bb` >> ASM_REWRITE_TAC[]) >>
  (* IC5: lift_result suffix simulation *)
  `execution_equiv excl_vars (s_ok with vs_inst_idx := SUC s1_pre.vs_inst_idx) s_at_ret` by (
    irule execution_equiv_inst_idx_update >> first_assum ACCEPT_TAC) >>
  `EVERY (\inst. inst.inst_opcode <> PHI)
     ret_bb.bb_instructions` by (
    ASM_REWRITE_TAC[] >>
    mp_tac (Q.SPECL [`bb`, `s1_pre.vs_inst_idx`] wf_suffix_no_phi) >>
    (impl_tac >- ASM_REWRITE_TAC[]) >>
    DISCH_TAC >> first_assum ACCEPT_TAC) >>
  `EVERY (\inst. !x. MEM (Var x) inst.inst_operands ==> x NOTIN excl_vars)
     ret_bb.bb_instructions` by (
    ASM_REWRITE_TAC[] >> irule EVERY_DROP >>
    REWRITE_TAC[EVERY_MEM] >> BETA_TAC >> ASM_REWRITE_TAC[]) >>
  `ret_bb.bb_instructions = DROP (SUC s1_pre.vs_inst_idx) bb.bb_instructions` by
    ASM_REWRITE_TAC[arithmeticTheory.ADD1] >>
  `(s_ok with vs_inst_idx := SUC s1_pre.vs_inst_idx).vs_inst_idx =
     SUC s1_pre.vs_inst_idx` by
    REWRITE_TAC[venomStateTheory.venom_state_accfupds, combinTheory.K_THM] >>
  `SUC s1_pre.vs_inst_idx <= LENGTH bb.bb_instructions` by DECIDE_TAC >>
  mp_tac (Q.SPECL [`fuel`, `ctx`, `bb`, `ret_bb`, `excl_vars`,
    `s_ok with vs_inst_idx := SUC s1_pre.vs_inst_idx`, `s_at_ret`,
    `SUC s1_pre.vs_inst_idx`] run_block_suffix_exec_equiv) >>
  (impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)) >>
  DISCH_TAC >>
  (* IC10: pre-derive jump_to facts, then apply intret_suffix_chain *)
  `~(jump_to clone_entry_lbl s2').vs_halted` by
    ASM_REWRITE_TAC[jump_to_def,
      venomStateTheory.venom_state_accfupds, combinTheory.K_THM] >>
  `(jump_to clone_entry_lbl s2').vs_current_bb = clone_entry_lbl` by
    REWRITE_TAC[jump_to_def,
      venomStateTheory.venom_state_accfupds, combinTheory.K_THM] >>
  `SUC s1_pre.vs_inst_idx <= LENGTH bb.bb_instructions` by DECIDE_TAC >>
  qpat_x_assum `Abbrev (caller_xf = _)`
    (SUBST_ALL_TAC o REWRITE_RULE [markerTheory.Abbrev_def]) >>
  mp_tac (Q.SPECL [`fuel`, `fuel`, `fuel_clone`, `ctx`, `caller`,
    `fix_inline_phis s2.vs_current_bb
       (return_block_label (inline_prefix ist.is_inline_count)
          ist.is_label_counter) ret_bb
       (inline_call_site (inline_prefix ist.is_inline_count)
          (return_block_label (inline_prefix ist.is_inline_count)
             ist.is_label_counter) caller callee s2.vs_current_bb
          s1_pre.vs_inst_idx)`,
    `bb`, `ret_bb`, `bb_trunc`, `s2`, `s_ok`, `s_at_ret`,
    `jump_to clone_entry_lbl s2'`, `ce_bb`, `excl_vars`,
    `s1_pre.vs_inst_idx`] intret_suffix_chain) >>
  impl_tac >- (
    rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
    ASM_REWRITE_TAC[jump_to_def,
      venomStateTheory.venom_state_accfupds, combinTheory.K_THM,
      venomStateTheory.venom_state_component_equality] >>
    DECIDE_TAC) >>
  strip_tac >> qexists_tac `fuel'` >> first_assum ACCEPT_TAC;

(* --- intret_main_tac: IntRet bridge + chain --- *)
val intret_main_tac : tactic =
  (* Phase 7: Bridge — establish execution_equiv s_ok s_at_ret *)
  mp_tac (Q.SPECL [
    `excl_vars`, `inline_prefix ist.is_inline_count`,
    `invoke_outs`, `s1_pre`,
    `jump_to clone_entry_lbl s2' with vs_prev_bb := NONE`,
    `v`, `s_ok`, `s_at_ret`, `l`, `frame`] intret_bridge) >>
  (impl_tac
  >- (
    rpt conj_tac >> TRY (first_assum ACCEPT_TAC)
    >- (irule execution_equiv_jump_to_prev_bb >> first_assum ACCEPT_TAC)
    >- (qpat_x_assum `Abbrev (frame = _)` mp_tac >>
         REWRITE_TAC[markerTheory.Abbrev_def])
    >- (mp_tac (Q.SPECL [`fuel`, `ctx`, `callee`, `args`, `s1_pre`,
              `callee_s`, `l`, `v`] ctx_fields_match_callee_intret) >>
         (impl_tac >- (conj_tac >> first_assum ACCEPT_TAC)) >>
         DISCH_TAC >> first_assum ACCEPT_TAC))) >>
  DISCH_TAC >>
  intret_chain_tac;

(* --- cs10_intret_tac: IntRet case --- *)
val cs10_intret_tac : tactic =
  (* Phase 1: Reduce case IntRet l v in goal and assumption *)
  REWRITE_TAC[exec_result_case_def] >> BETA_TAC >> strip_tac >>
  (* Reduce the step_inst case expression assumption *)
  qpat_x_assum `exec_result_CASE (IntRet l v) _ _ _ _ _` mp_tac >>
  REWRITE_TAC[exec_result_case_def] >> BETA_TAC >> DISCH_TAC >>
  (* Phase 2: Extract bind_outputs and step_inst from option case *)
  `?s_ok. bind_outputs invoke_outs l (merge_callee_state s1_pre v) = SOME s_ok /\
          step_inst fuel ctx invoke_inst s1_pre = OK s_ok` by (
    Cases_on `bind_outputs invoke_outs l (merge_callee_state s1_pre v)` >>
    gvs[]) >>
  (* Chain run_block through step_inst = OK *)
  qpat_x_assum `run_block fuel ctx bb s1 = _` mp_tac >>
  ASM_REWRITE_TAC[exec_result_case_def] >> BETA_TAC >> DISCH_TAC >>
  (* Phase 4: SUBST all Abbrevs *)
  SUBST_NAMED_ABBREV_TAC `Abbrev (s_clone_adj = _)` >>
  SUBST_NAMED_ABBREV_TAC `Abbrev (s_jmp = _)` >>
  SUBST_NAMED_ABBREV_TAC `Abbrev (invoke_inst = _)` >>
  SUBST_NAMED_ABBREV_TAC `Abbrev (prefix = _)` >>
  SUBST_NAMED_ABBREV_TAC `Abbrev (ret_lbl = _)` >>
  SUBST_NAMED_ABBREV_TAC `Abbrev (fn_inl = _)` >>
  SUBST_NAMED_ABBREV_TAC `Abbrev (caller_xf = _)` >>
  (* Phase 5: Derive clone entry block *)
  mp_tac (Q.SPECL [`ist.is_inline_count`, `ist.is_label_counter`,
    `caller`, `callee`, `s2.vs_current_bb`, `s1_pre.vs_inst_idx`,
    `ret_bb`, `bb`] clone_entry_block_in_caller_xf) >>
  (impl_tac >- ASM_REWRITE_TAC[] >> strip_tac) >>
  (* Phase 6: Substitute run_block equation into goal *)
  qpat_x_assum `run_block fuel ctx bb s1 = _`
    (fn th => REWRITE_TAC[th]) >>
  (* Phase 7+: IntRet main chain *)
  intret_main_tac;

(* --- cs10_error_tac: Error case contradiction --- *)
val cs10_error_tac : tactic =
  (* Contradiction: callee doesn't error *)
  metis_tac[];
(* Shared tactic for cs10: Steps A-L of invoke clone simulation.
   Both the not-MEM and MEM cases reach the same proof state after block execution
   is resolved, differing only in the name of the pre-invoke state variable.
   The not-MEM case has s2', the MEM case renames s2_pre -> s2' before calling.
   Self-contained: uses val tactics instead of suspend/Resume.

   Split into cs10_setup_tac (Steps A-K) and cs10_dispatch_tac (Step L).
   MEM case needs to pop prev_bb disjunction during setup (fs diverges with it)
   and restore it before dispatch. See L#375. *)
val cs10_setup_tac : tactic =
  (* Step A: Extract setup_callee fields — use targeted discharge
     to avoid setup_callee expansion in rich contexts (L#309) *)
  mp_tac (Q.SPECL [`callee`, `args`, `s1_pre`, `callee_s`]
    setup_callee_fields) >>
  (impl_tac >- (conj_tac >> first_assum ACCEPT_TAC)) >>
  disch_then CONJ_ASSUME_TAC >>
  (* Step B: Resolve clone_entry_lbl *)
  `clone_entry_lbl = STRCAT prefix (HD callee.fn_blocks).bb_label` by (
    qpat_x_assum `Abbrev (clone_entry_lbl = _)` mp_tac >>
    simp[markerTheory.Abbrev_def] >>
    drule clone_entry_label >> simp[]) >>
  (* Step C: Establish shared_globals_np callee_s (jump_to clone_entry_lbl s2')
     Pop case expression before fs to prevent divergence (L#375) *)
  TRY (qpat_x_assum `case run_function _ _ _ _ of _ => _` mp_tac) >>
  `shared_globals_np callee_s (jump_to clone_entry_lbl s2')` by
    fs[shared_globals_np_def, execution_equiv_def, jump_to_def] >>
  TRY (disch_then assume_tac) >>
  (* Step D: Unfold original run_function to get run_block equation *)
  `run_function (SUC fuel) ctx caller s1 =
   case run_block fuel ctx bb s1 of
     OK s' => if s'.vs_halted then Halt s' else run_function fuel ctx caller s'
   | Halt s' => Halt s'
   | Abort a s' => Abort a s'
   | IntRet v s' => IntRet v s'
   | Error e => Error e` by (
    CONV_TAC (LAND_CONV (ONCE_REWRITE_CONV [run_function_def])) >>
    simp[]) >>
  (* Step E: ALL_DISTINCT invoke_inst.inst_outputs *)
  `ALL_DISTINCT invoke_inst.inst_outputs` by (
    imp_res_tac lookup_block_MEM >>
    `MEM invoke_inst bb.bb_instructions` by (
      gvs[markerTheory.Abbrev_def, Excl "setup_callee_def"] >>
      metis_tac[MEM_EL]) >>
    qpat_x_assum `EVERY (\bb. EVERY (\inst. inst_targets _ inst ==>
      ALL_DISTINCT _) _) _`
      (fn th => assume_tac (REWRITE_RULE [EVERY_MEM] th)) >>
    first_x_assum (qspec_then `bb` mp_tac) >> simp[] >>
    disch_then (fn th => assume_tac (REWRITE_RULE [EVERY_MEM] th)) >>
    first_x_assum (qspec_then `invoke_inst` mp_tac) >> simp[]) >>
  (* Step F: Callee entry block and clone state setup *)
  `callee.fn_blocks <> []` by fs[fn_has_entry_def] >>
  `lookup_block (HD callee.fn_blocks).bb_label callee.fn_blocks =
   SOME (HD callee.fn_blocks)` by (
    simp[lookup_block_def] >>
    Cases_on `callee.fn_blocks` >>
    gvs[FIND_thm, Excl "setup_callee_def"]) >>
  `bb_well_formed (HD callee.fn_blocks)` by (
    Cases_on `callee.fn_blocks` >>
    gvs[EVERY_MEM, Excl "setup_callee_def"]) >>
  qabbrev_tac `s_jmp = jump_to clone_entry_lbl s2'` >>
  qabbrev_tac `s_clone_adj = s_jmp with vs_prev_bb := NONE` >>
  `FDOM s2'.vs_labels = {}` by
    (fs[execution_equiv_def, Excl "setup_callee_def"] >>
     gvs[Excl "setup_callee_def"]) >>
  `clone_rel_np prefix (fn_labels callee) callee_s s_clone_adj` by (
    qunabbrev_tac `s_clone_adj` >> qunabbrev_tac `s_jmp` >>
    simp[clone_rel_np_def, jump_to_def, FDOM_FEMPTY] >>
    fs[shared_globals_np_def, jump_to_def]) >>
  `s_clone_adj.vs_inst_idx = 0` by
    (qunabbrev_tac `s_clone_adj` >> qunabbrev_tac `s_jmp` >>
     simp[jump_to_def]) >>
  `~s_clone_adj.vs_halted` by
    (qunabbrev_tac `s_clone_adj` >> qunabbrev_tac `s_jmp` >>
     simp[jump_to_def]) >>
  `s_clone_adj.vs_current_bb = STRCAT prefix callee_s.vs_current_bb` by
    (qunabbrev_tac `s_clone_adj` >> qunabbrev_tac `s_jmp` >>
     simp[jump_to_def]) >>
  `LENGTH args = LENGTH callee_s.vs_params` by simp[] >>
  (* Step G: Callee doesn't error at fuel — already in assumptions
     (proved before unification in both MEM and ¬MEM cases) *)
  (* Step H: Entry has no PHI *)
  `EVERY (\inst. inst.inst_opcode <> PHI)
     (HD callee.fn_blocks).bb_instructions` by (
    spose_not_then assume_tac >>
    mp_tac (Q.SPECL [`fuel`, `ctx`, `callee`, `args`, `s1_pre`, `callee_s`]
      entry_phi_callee_errors) >>
    simp[] >> strip_tac >>
    `terminates (run_function fuel ctx callee callee_s)` by (
      Cases_on `run_function fuel ctx callee callee_s` >>
      simp[terminates_def] >> metis_tac[]) >>
    mp_tac (Q.SPECL [`fuel`, `ctx`, `callee`, `callee_s`]
      run_function_fuel_mono) >>
    simp[] >>
    disch_then (qspec_then `1` mp_tac) >> simp[arithmeticTheory.ADD1] >>
    Cases_on `run_function fuel ctx callee callee_s` >>
    gvs[terminates_def, Excl "setup_callee_def"]) >>
  (* Step I: Define invoke_ops and invoke_outs for clone_execution_sim_ext *)
  qabbrev_tac `invoke_ops = rotate_invoke_ops invoke_inst.inst_operands` >>
  qabbrev_tac `invoke_outs = invoke_inst.inst_outputs` >>
  (* Step J: Abbreviate frame *)
  qabbrev_tac `frame = \v:string. ~isPREFIX prefix v /\ ~MEM v invoke_outs` >>
  (* Step K: Apply clone_execution_sim_ext — discharge preconditions *)
  mp_tac (Q.SPECL [
    `fuel`, `ctx`, `callee`, `caller_xf`, `prefix`, `ret_lbl`,
    `frame`, `invoke_outs`, `invoke_ops`, `args`,
    `callee_s`, `s_clone_adj`]
    clone_execution_sim_ext) >>
  (impl_tac >- cs10_discharge_tac);

(* Step L: Case split on callee result and dispatch to sub-tactics *)
val cs10_dispatch_tac : tactic =
  Cases_on `run_function fuel ctx callee callee_s`
  >| [cs10_ok_tac,
      cs10_halt_tac,
      cs10_abort_tac,
      cs10_intret_tac,
      cs10_error_tac];

(* Combined tactic for cases where disjunction is not an issue (e.g., ¬MEM) *)
val cs10_body_tac : tactic = cs10_setup_tac >> cs10_dispatch_tac;

Resume inline_one_site_fn_correct[cs10]:
  cs10_body_tac
QED

(* === MEM case helper: establish s2_pre on phi-subst block === *)
Triviality mem_case_phi_subst_reaches[local]:
  !call_idx fuel ctx vars bb call_lbl ret_lbl s1 s2 s1_pre jmp_inst.
    run_block_reaches fuel ctx bb s1 call_idx = SOME s1_pre /\
    s1.vs_inst_idx = 0 /\ s2.vs_inst_idx = 0 /\
    call_idx < LENGTH bb.bb_instructions /\
    execution_equiv vars s1 s2 /\
    s1.vs_current_bb = s2.vs_current_bb /\
    FDOM s1.vs_labels = {} /\
    (s1.vs_prev_bb = s2.vs_prev_bb /\ s1.vs_prev_bb <> SOME ret_lbl /\
     s1.vs_prev_bb <> SOME call_lbl \/
     s1.vs_prev_bb = SOME call_lbl /\ s2.vs_prev_bb = SOME ret_lbl) /\
    (!i. i < call_idx ==>
         ~is_terminator (EL i bb.bb_instructions).inst_opcode) /\
    (!inst. MEM inst bb.bb_instructions ==>
            !x. MEM (Var x) inst.inst_operands ==> x NOTIN vars) /\
    ~MEM (Label ret_lbl) (FLAT (MAP (\i. i.inst_operands) bb.bb_instructions)) /\
    jmp_inst.inst_opcode = JMP
    ==>
    let trunc_bb2 = (bb with bb_instructions :=
           MAP (\inst. if inst.inst_opcode <> PHI then inst
                       else subst_label_inst call_lbl ret_lbl inst)
               (TAKE call_idx bb.bb_instructions ++ [jmp_inst])) in
    ?s2_pre. run_block_reaches fuel ctx trunc_bb2 s2 call_idx = SOME s2_pre /\
      execution_equiv vars s1_pre s2_pre /\
      s1_pre.vs_current_bb = s2_pre.vs_current_bb /\
      s1_pre.vs_inst_idx = s2_pre.vs_inst_idx /\
      FDOM s1_pre.vs_labels = {}
Proof
  rpt gen_tac >> strip_tac >>
  simp[] >>
  (* Both prev_bb disjuncts handled identically *)
  (
  (* Step 1: Apply phi_subst equiv on the FULL bb *)
  mp_tac (Q.SPECL [`call_idx`, `fuel`, `ctx`, `vars`, `bb`,
    `call_lbl`, `ret_lbl`, `s1`, `s2`, `s1_pre`]
    run_block_reaches_phi_subst_equiv) >>
  REWRITE_TAC[LET_THM] >> BETA_TAC >>
  impl_tac >- (
    ASM_REWRITE_TAC[] >> rpt conj_tac >>
    TRY (simp[] >> NO_TAC) >>
    TRY (DISJ1_TAC >> ASM_REWRITE_TAC[] >> NO_TAC) >>
    TRY (DISJ2_TAC >> ASM_REWRITE_TAC[] >> NO_TAC) >>
    rpt strip_tac >> first_x_assum (qspec_then `i` mp_tac) >> simp[]) >>
  strip_tac >>
  qexists_tac `s2'` >> ASM_REWRITE_TAC[] >>
  (* Goal: reaches(bb with MAP f (TAKE k insts) ++ [jmp]) = SOME s2'
     Asm:  reaches(bb with MAP f insts) = SOME s2'
     Note: simp[] already distributed MAP over ++
     Step 1: MAP_TAKE rewrites MAP f (TAKE k insts) to TAKE k (MAP f insts) *)
  REWRITE_TAC[MAP_TAKE] >>
  (* Goal: reaches(bb with TAKE k (MAP f insts) ++ [jmp]) = SOME s2'
     Step 2: run_block_reaches_take_agree (GSYM) *)
  mp_tac (Q.SPECL [`call_idx`, `fuel`, `ctx`,
    `bb with bb_instructions :=
       MAP (\inst. if inst.inst_opcode <> PHI then inst
                   else subst_label_inst call_lbl ret_lbl inst)
           bb.bb_instructions`,
    `s2`, `jmp_inst`] run_block_reaches_take_agree) >>
  simp[LENGTH_MAP]
  )
QED

Triviality subst_label_preserves_opcode[local]:
  !call_lbl ret_lbl inst.
    (if inst.inst_opcode <> PHI then inst
     else subst_label_inst call_lbl ret_lbl inst).inst_opcode = inst.inst_opcode
Proof
  rw[] >> rw[subst_label_inst_def]
QED

(* === MEM case: call_lbl ∈ bb_succs ret_bb — use phi_subst_reaches === *)
Resume inline_one_site_fn_correct[mem_case]:
  (* Establish prev_bb in phi_subst form.
     IH form: (= /\ <> ret_lbl /\ (MEM ==> <> call_lbl)) \/ (call_lbl /\ ret_lbl /\ MEM)
     Triviality needs: (= /\ <> call_lbl /\ <> ret_lbl) \/ (call_lbl /\ ret_lbl)
     In mem_case we have MEM call_lbl (bb_succs ret_bb) and s1.vs_current_bb = call_lbl *)
  qpat_x_assum `(_ /\ _ /\ _) \/ (_ /\ _ /\ _)` mp_tac >>
  qpat_assum `s1.vs_current_bb = call_lbl` (fn h => REWRITE_TAC[h]) >>
  qpat_assum `MEM call_lbl (bb_succs ret_bb)` (fn h => REWRITE_TAC[h]) >>
  REWRITE_TAC[boolTheory.IMP_CLAUSES, boolTheory.AND_CLAUSES] >>
  DISCH_TAC >>
  (* Simplify trunc_bb2 *)
  `trunc_bb2 = bb with bb_instructions :=
     MAP (\inst. if inst.inst_opcode <> PHI then inst
                 else subst_label_inst call_lbl ret_lbl inst)
         (TAKE call_idx bb.bb_instructions ++ [jmp_inst])` by (
    qunabbrev_tac `trunc_bb2` >>
    qpat_assum `MEM call_lbl (bb_succs ret_bb)` (fn mem =>
      REWRITE_TAC[mem, COND_CLAUSES]) >>
    qpat_assum `Abbrev (bb_trunc = _)` (SUBST1_TAC o
      REWRITE_RULE [markerTheory.Abbrev_def]) >>
    REWRITE_TAC[basic_block_fupdfupds, basic_block_accfupds,
                combinTheory.K_THM] >>
    AP_THM_TAC >> AP_TERM_TAC >>
    REWRITE_TAC[FUN_EQ_THM, combinTheory.K_THM, combinTheory.o_THM]) >>
  (* Apply standalone triviality — use MATCH_MP chain to discharge *)
  `?s2_pre. run_block_reaches fuel ctx trunc_bb2 s2 call_idx = SOME s2_pre /\
     execution_equiv excl_vars s1_pre s2_pre /\
     s1_pre.vs_current_bb = s2_pre.vs_current_bb /\
     s1_pre.vs_inst_idx = s2_pre.vs_inst_idx /\
     FDOM s1_pre.vs_labels = {}` by (
    qpat_assum `trunc_bb2 = _` SUBST1_TAC >>
    mp_tac (Q.SPECL [`call_idx`, `fuel`, `ctx`, `excl_vars`, `bb`,
      `call_lbl`, `ret_lbl`, `s1`, `s2`, `s1_pre`, `jmp_inst`]
      mem_case_phi_subst_reaches) >>
    REWRITE_TAC[LET_THM] >> BETA_TAC >>
    impl_tac >- (
      rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
      TRY (ASM_REWRITE_TAC[]) >>
      qpat_assum `Abbrev (jmp_inst = _)` (SUBST1_TAC o
        REWRITE_RULE [markerTheory.Abbrev_def]) >>
      REWRITE_TAC[] >> EVAL_TAC) >>
    DISCH_TAC >> first_assum ACCEPT_TAC) >>
  (* CS7: bb_well_formed *)
  `~is_terminator (EL call_idx bb.bb_instructions).inst_opcode` by
    (gvs[markerTheory.Abbrev_def] >> EVAL_TAC) >>
  `bb_well_formed bb_trunc` by (
    qpat_assum `Abbrev (bb_trunc = _)` (SUBST1_TAC o
      REWRITE_RULE [markerTheory.Abbrev_def]) >>
    qpat_assum `Abbrev (jmp_inst = _)` (SUBST1_TAC o
      REWRITE_RULE [markerTheory.Abbrev_def]) >>
    irule truncated_bb_well_formed >> simp[]) >>
  `bb_well_formed trunc_bb2` by (
    qpat_assum `trunc_bb2 = _` SUBST1_TAC >>
    qpat_assum `bb_well_formed bb_trunc` mp_tac >>
    qpat_assum `Abbrev (bb_trunc = _)` (SUBST1_TAC o
      REWRITE_RULE [markerTheory.Abbrev_def]) >>
    DISCH_TAC >>
    irule bb_well_formed_map_opcode >>
    conj_tac >- (
      gen_tac >> Cases_on `inst.inst_opcode = PHI` >>
      ASM_REWRITE_TAC[] >> REWRITE_TAC[subst_label_inst_def] >>
      simp[]) >>
    first_assum ACCEPT_TAC) >>
  (* CS7b: halted *)
  `~s1_pre.vs_halted` by (
    mp_tac (Q.SPECL [`call_idx`, `fuel`, `ctx`, `bb`, `s1`, `s1_pre`]
      run_block_reaches_preserves_halted) >>
    simp[] >> disch_then irule >>
    rpt strip_tac >> imp_res_tac pre_invoke_non_terminator) >>
  `~s2_pre.vs_halted` by (
    qpat_x_assum `execution_equiv _ s1_pre s2_pre` mp_tac >>
    simp[execution_equiv_def]) >>
  (* CS7c: trunc_bb_jmp_result *)
  `trunc_bb2.bb_instructions =
     TAKE call_idx (MAP (\inst. if inst.inst_opcode <> PHI then inst
                                 else subst_label_inst call_lbl ret_lbl inst)
                        bb.bb_instructions) ++ [jmp_inst]` by (
    qpat_assum `trunc_bb2 = _` SUBST1_TAC >>
    simp[MAP_TAKE, MAP_APPEND] >>
    qunabbrev_tac `jmp_inst` >> simp[subst_label_inst_def]) >>
  `jmp_inst.inst_outputs = []` by (qunabbrev_tac `jmp_inst` >> simp[]) >>
  `jmp_inst.inst_opcode = JMP` by (qunabbrev_tac `jmp_inst` >> simp[]) >>
  `jmp_inst.inst_operands = [Label clone_entry_lbl]` by
    (qunabbrev_tac `jmp_inst` >> simp[]) >>
  `run_block fuel ctx trunc_bb2 s2 = OK (jump_to clone_entry_lbl s2_pre) /\
   ~(jump_to clone_entry_lbl s2_pre).vs_halted` by (
    mp_tac (Q.SPECL [`fuel`, `ctx`, `trunc_bb2`, `s2`, `call_idx`,
      `s2_pre`, `jmp_inst`, `clone_entry_lbl`,
      `MAP (\inst. if inst.inst_opcode <> PHI then inst
                   else subst_label_inst call_lbl ret_lbl inst)
           bb.bb_instructions`]
      trunc_bb_jmp_result) >>
    ASM_REWRITE_TAC[] >>
    impl_tac >- simp[] >>
    DISCH_TAC >> first_assum ACCEPT_TAC) >>
  (* CS8+: identical to ¬MEM case from here *)
  `inst_targets callee.fn_name invoke_inst` by (
    qunabbrev_tac `invoke_inst` >>
    mp_tac (Q.SPECL [`callee.fn_name`, `caller.fn_blocks`, `call_lbl`,
      `call_idx`] find_invoke_site_inst_targets) >>
    simp[fn_labels_def]) >>
  `?arg_ops. decode_invoke invoke_inst = SOME (callee.fn_name, arg_ops)` by (
    gvs[inst_targets_def] >>
    Cases_on `invoke_inst.inst_operands` >> gvs[] >>
    Cases_on `h` >> gvs[] >>
    simp[decode_invoke_def]) >>
  `invoke_inst.inst_opcode = INVOKE` by
    (gvs[markerTheory.Abbrev_def] >> EVAL_TAC) >>
  Cases_on `!e. step_inst fuel ctx invoke_inst s1_pre <> Error e`
  >- (
    drule_all step_inst_invoke_decompose >> strip_tac >>
    (* Step G early: Callee doesn't error — prove BEFORE unification
       consumes decode_invoke. After gvs[], callee_fn→callee propagates. *)
    `!e. run_function fuel ctx callee_fn callee_s <> Error e` by
      (drule_all invoke_callee_no_error >> disch_then ACCEPT_TAC) >>
    `callee_name = callee.fn_name /\ arg_ops' = arg_ops` by (
      qpat_x_assum `decode_invoke _ = SOME (callee_name, _)` mp_tac >>
      qpat_x_assum `decode_invoke _ = SOME (callee.fn_name, _)` mp_tac >>
      simp[]) >>
    (* Unify variables from step_inst_invoke_decompose with original context.
       Strategy: ONLY use SUBST_ALL_TAC — no gvs, no ML refs. This is safe
       because SUBST_ALL_TAC never expands definitions or derives new facts. *)
    `callee_fn = callee` by (
      qpat_x_assum `lookup_function _ _ = SOME callee_fn` mp_tac >>
      qpat_x_assum `lookup_function _ _ = SOME callee` mp_tac >> fs[]) >>
    qpat_x_assum `callee_fn = _` (fn h => SUBST_ALL_TAC h) >>
    qpat_x_assum `callee_name = _` (fn h => SUBST_ALL_TAC h) >>
    qpat_x_assum `arg_ops' = _` (fn h => SUBST_ALL_TAC h) >>
    (* call_lbl = s1.vs_current_bb at this point (earlier REWRITE/qpat_assum
       already rewrote call_lbl → s1.vs_current_bb in some assumptions).
       Don't SUBST s1.vs_current_bb → s2.vs_current_bb yet — Step D needs it.
       Just clean up the now-redundant s1.vs_current_bb = call_lbl. *)
    TRY (qpat_x_assum `s1.vs_current_bb = call_lbl` kall_tac) >>
    (* Substitute call_idx → s1_pre.vs_inst_idx *)
    qpat_x_assum `s1_pre.vs_inst_idx = call_idx`
      (fn h => SUBST_ALL_TAC (SYM h)) >>
    (* Kill redundant/derivable equalities left over *)
    TRY (qpat_x_assum `_ = s1.vs_inst_idx + _` kall_tac) >>
    TRY (qpat_x_assum `_ < LENGTH bb.bb_instructions` kall_tac) >>
    (* Rename s2_pre → s2' *)
    Q.MATCH_ASSUM_RENAME_TAC `execution_equiv excl_vars s1_pre s2'` >>
    (* Pop prev_bb disjunction (cs10_body_tac doesn't need it) *)
    qpat_x_assum `(_ /\ _) \/ (_ /\ _)` kall_tac >>
    (* Remove old bb_trunc references *)
    let
      val has_bb_trunc = fn t =>
        exists (fn v => fst (dest_var v) = "bb_trunc") (free_vars t)
    in
      rpt (PRED_ASSUM has_bb_trunc kall_tac)
    end >>
    (* Remove trunc_bb2 Abbrev (conditional form) *)
    TRY (qpat_x_assum `Abbrev (trunc_bb2 = _)` kall_tac) >>
    (* Substitute trunc_bb2 throughout *)
    qpat_x_assum `trunc_bb2 = _` (fn h => SUBST_ALL_TAC h) >>
    qmatch_asmsub_abbrev_tac
      `run_block fuel ctx bb_trunc s2 = OK (jump_to clone_entry_lbl s2')` >>
    (* bb_well_formed bb_trunc — already proved as bb_well_formed trunc_bb2 *)
    `bb_well_formed bb_trunc` by first_assum ACCEPT_TAC >>
    (* bb_trunc.bb_instructions — derive from Abbrev *)
    qpat_x_assum `Abbrev (bb_trunc = _)` (fn h =>
      assume_tac h >>
      assume_tac (CONV_RULE (RAND_CONV (SIMP_CONV (srw_ss()) []))
        (AP_TERM ``basic_block_bb_instructions``
          (REWRITE_RULE [markerTheory.Abbrev_def] h)))) >>
    (* Kill MEM-specific assumptions *)
    TRY (qpat_x_assum `MEM _ (bb_succs ret_bb)` kall_tac) >>
    TRY (qpat_x_assum `MAP _ _ = TAKE _ _` kall_tac) >>
    let
      val has_trunc_bb2 = fn t =>
        exists (fn v => fst (dest_var v) = "trunc_bb2") (free_vars t)
    in
      rpt (PRED_ASSUM has_trunc_bb2 kall_tac)
    end >>
    (* Simplify run_block equation to match ¬MEM form.
       1. Unfold let (beta reduction)
       2. Rewrite bb.bb_instructions❲...❳ → invoke_inst (from Abbrev)
       3. Simplify is_terminator INVOKE → F *)
    qpat_x_assum `bb.bb_instructions❲_❳ = invoke_inst` (fn eq_h =>
      qpat_x_assum `run_block fuel ctx bb s1 = _` (fn rb_h =>
        assume_tac (CONV_RULE (RAND_CONV (
          SIMP_CONV (srw_ss()) [eq_h, is_terminator_def])) rb_h))) >>
    (* Simplify the case expression: Error msg => F (using step_inst error-free).
       step_inst_invoke_decompose gives NONE => Error msg form;
       combined with !e. step_inst ... <> Error e, the Error rewrites to F. *)
    qpat_x_assum `case run_function _ _ _ _ of _ => _` (fn case_h =>
      qpat_x_assum `!e. step_inst _ _ _ _ <> Error e` (fn err_h =>
        assume_tac err_h >>
        assume_tac (SIMP_RULE (srw_ss()) [err_h] case_h))) >>
    (* Kill duplicate decode_invoke and extra lookup_function *)
    qpat_assum `decode_invoke invoke_inst = SOME _` (K ALL_TAC) >>
    TRY (qpat_x_assum `lookup_function _ _ = SOME callee` kall_tac) >>
    (* Kill extra/redundant assumptions *)
    TRY (qpat_x_assum `bb.bb_instructions❲_❳ = invoke_inst` kall_tac) >>
    TRY (qpat_x_assum `<|is_inline_count := _; is_label_counter := _|> = _` kall_tac) >>
    suspend "mem_cs10")
  >>
  (* Error case: ~!e. ... becomes ?e. step_inst = Error e
     Pop prev_bb disjunction before fs to prevent splitting into 2 subgoals *)
  qpat_x_assum `(_ /\ _) \/ (_ /\ _)` mp_tac >>
  fs[] >>
  disch_then assume_tac >>
  MATCH_MP_TAC invoke_step_error_sim >>
  MAP_EVERY qexists_tac [`bb`, `invoke_inst`, `s1_pre`, `call_idx`, `e`] >>
  gvs[markerTheory.Abbrev_def]
QED

(* mem_cs10_tac: Normalize MEM context to match notMEM, then run cs10_body_tac.
   The MEM context uses call_lbl where notMEM uses s2.vs_current_bb, has let-form
   run_block, Error string in case expr, reversed inst_idx equation, and extras.
   7 transformations bring MEM context into alignment with notMEM. *)
val mem_cs10_tac : tactic =
  (* 1. SUBST call_lbl -> s2.vs_current_bb via lookup_block_label + transitivity *)
  qpat_x_assum `lookup_block call_lbl caller.fn_blocks = SOME bb` (fn h1 =>
    qpat_assum `lookup_block s1.vs_current_bb caller.fn_blocks = SOME bb` (fn h2 =>
    qpat_assum `s1.vs_current_bb = s2.vs_current_bb` (fn h3 =>
      let val eq = TRANS (TRANS (SYM (MATCH_MP lookup_block_label h1))
                                (MATCH_MP lookup_block_label h2)) h3
      in assume_tac h1 >> SUBST_ALL_TAC eq end))) >>
  (* 2. Normalize run_block let-form: beta-reduce let, simplify is_terminator *)
  qpat_assum `invoke_inst.inst_opcode = INVOKE` (fn opc_h =>
    qpat_x_assum `run_block fuel ctx bb s1 = _` (fn rb_h =>
      assume_tac (CONV_RULE (RAND_CONV (
        SIMP_CONV (srw_ss()) [LET_THM, opc_h, is_terminator_def])) rb_h))) >>
  (* 3. Normalize case expression: Error msg -> F *)
  qpat_x_assum `case run_function _ _ _ _ of _ => _` (fn case_h =>
    qpat_assum `!e. step_inst _ _ _ _ <> Error e` (fn err_h =>
      assume_tac (SIMP_RULE (srw_ss()) [err_h] case_h))) >>
  (* 4. Kill duplicate decode_invoke *)
  TRY (qpat_assum `decode_invoke invoke_inst = SOME _` (K ALL_TAC)) >>
  (* 5. Add ~is_terminator INVOKE *)
  assume_tac (EQF_ELIM (EVAL ``is_terminator INVOKE``)) >>
  (* 6. Kill MEM-specific extras *)
  TRY (qpat_x_assum `~is_terminator bb.bb_instructions❲_❳.inst_opcode` kall_tac) >>
  TRY (qpat_x_assum `bb_trunc.bb_instructions = TAKE _ (MAP _ _) ++ _` kall_tac) >>
  TRY (qpat_x_assum `lookup_function _ _ = SOME callee` kall_tac) >>
  TRY (qpat_x_assum `<|is_inline_count := _; is_label_counter := _|> = _` kall_tac) >>
  (* 7. Flip s1_pre.vs_inst_idx = s2'.vs_inst_idx to match notMEM direction *)
  qpat_x_assum `s1_pre.vs_inst_idx = s2'.vs_inst_idx`
    (fn h => assume_tac (SYM h)) >>
  cs10_body_tac;

Resume inline_one_site_fn_correct[mem_cs10]:
  mem_cs10_tac
QED

Finalise inline_one_site_fn_correct;


(* ================================================================
   Section 5: Iterated inlining
   ================================================================ *)

(* Transitivity for lift_result (state_equiv inline_vars) shared_globals_np *)
Triviality shared_globals_np_trans[local]:
  !s1 s2 s3.
    shared_globals_np s1 s2 /\ shared_globals_np s2 s3 ==>
    shared_globals_np s1 s3
Proof
  rw[shared_globals_np_def]
QED

Triviality lift_result_inline_trans[local]:
  !r1 r2 r3.
    lift_result (state_equiv inline_vars) shared_globals_np r1 r2 /\
    lift_result (state_equiv inline_vars) shared_globals_np r2 r3 ==>
    lift_result (state_equiv inline_vars) shared_globals_np r1 r3
Proof
  Cases >> Cases >> Cases >>
  simp[lift_result_def] >>
  metis_tac[state_equiv_trans, shared_globals_np_trans]
QED

(* inline_one_site produces ist' with is_inline_count = ist.is_inline_count + 1 *)
Triviality inline_one_site_ist_count[local]:
  !fn callee ist fn' ist'.
    inline_one_site fn callee ist = SOME (fn', ist') ==>
    ist'.is_inline_count = ist.is_inline_count + 1
Proof
  rw[inline_one_site_def, LET_THM] >>
  BasicProvers.EVERY_CASE_TAC >> gvs[]
QED

(* Lift result identity (reflexivity) *)
Triviality lift_result_refl_inline[local]:
  !r. lift_result (state_equiv inline_vars) shared_globals_np r r
Proof
  Cases >>
  simp[lift_result_def, state_equiv_refl, shared_globals_np_def]
QED

(* Weaken lift_result from per-iteration exclusion set to inline_vars *)
Triviality lift_result_weaken_to_inline_vars[local]:
  !k r1 r2.
    lift_result (state_equiv {v | isPREFIX (inline_prefix k) v})
      shared_globals_np r1 r2 ==>
    lift_result (state_equiv inline_vars) shared_globals_np r1 r2
Proof
  rpt gen_tac >> Cases_on `r1` >> Cases_on `r2` >>
  simp[lift_result_def] >> rpt strip_tac >>
  irule state_equiv_mono >>
  qexists_tac `{v | isPREFIX (inline_prefix k) v}` >>
  simp[inline_prefix_vars_subset_inline_vars]
QED

(* inline_one_site preserves the EVERY callee_ret_arity_le condition.
   New blocks (truncated, clone, return) have no inst_targets callee,
   so the condition holds vacuously. Unchanged blocks inherit it. *)
(* ---- Arity preservation through inline_one_site ---- *)

(* inst_targets requires INVOKE opcode *)
Triviality inst_targets_not_invoke[local]:
  !name inst. inst.inst_opcode <> INVOKE ==> ~inst_targets name inst
Proof
  rw[inst_targets_def] >> Cases_on `inst.inst_operands` >> simp[]
QED



(* fn_no_invoke means no instruction in fn targets name *)
Triviality fn_no_invoke_inst_targets[local]:
  !name fn inst bb.
    fn_no_invoke name fn /\ MEM bb fn.fn_blocks /\
    MEM inst bb.bb_instructions ==>
    ~inst_targets name inst
Proof
  rw[fn_no_invoke_def] >>
  gvs[EVERY_MEM] >> metis_tac[]
QED

(* clone_instruction preserves ~inst_targets when fn_no_invoke + invoke_targets_extern *)
Theorem clone_inst_no_targets[local]:
  !name callee prefix inst bb.
    fn_no_invoke name callee /\
    invoke_targets_extern callee /\
    MEM bb callee.fn_blocks /\
    MEM inst bb.bb_instructions ==>
    ~inst_targets name (clone_instruction prefix (fn_labels callee) inst)
Proof
  rpt strip_tac >>
  `~inst_targets name inst` by metis_tac[fn_no_invoke_inst_targets] >>
  simp[inst_targets_def, clone_instruction_def] >>
  Cases_on `inst.inst_opcode = INVOKE` >> simp[] >>
  (* inst.inst_opcode = INVOKE *)
  Cases_on `inst.inst_operands` >> fs[inst_targets_def] >>
  Cases_on `h` >> fs[clone_operand_def, inst_targets_def] >>
  (* Label case — need ~(STRCAT prefix s = name) and s not in fn_labels *)
  Cases_on `MEM s (fn_labels callee)` >> fs[] >>
  (* MEM s (fn_labels callee) — contradicts invoke_targets_extern *)
  `MEM inst (fn_insts callee)` by
    (simp[fn_insts_def] >> metis_tac[mem_fn_insts_blocks]) >>
  qpat_x_assum `invoke_targets_extern _`
    (fn th => assume_tac (BETA_RULE (REWRITE_RULE [invoke_targets_extern_def, EVERY_MEM] th))) >>
  first_x_assum (qspec_then `inst` mp_tac) >> simp[]
QED

(* rewrite_inline_inst preserves ~inst_targets *)
Triviality rewrite_inline_inst_no_targets[local]:
  !name inst ops outs ret_lbl pidx.
    ~inst_targets name inst ==>
    EVERY (\i. ~inst_targets name i)
      (FST (rewrite_inline_inst ops outs ret_lbl inst pidx))
Proof
  rw[rewrite_inline_inst_def, LET_THM] >>
  rpt (IF_CASES_TAC >> fs[]) >>
  simp[inst_targets_def, EVERY_APPEND, EVERY_EL,
       indexedListsTheory.EL_MAPi, indexedListsTheory.LENGTH_MAPi]
QED

(* Every instruction in rewrite_inline_insts applied to clone instructions
   satisfies ~inst_targets callee.fn_name *)
Triviality rewrite_inline_insts_no_targets[local]:
  !name insts ops outs ret_lbl pidx.
    EVERY (\i. ~inst_targets name i) insts ==>
    EVERY (\i. ~inst_targets name i)
      (FST (rewrite_inline_insts ops outs ret_lbl insts pidx))
Proof
  Induct_on `insts` >>
  simp[rewrite_inline_insts_def, LET_THM] >>
  rpt gen_tac >> strip_tac >>
  Cases_on `rewrite_inline_inst ops outs ret_lbl h pidx` >>
  Cases_on `rewrite_inline_insts ops outs ret_lbl insts r` >>
  simp[EVERY_APPEND] >>
  metis_tac[rewrite_inline_inst_no_targets, FST]
QED

(* Every instruction in rewrite_inline_blocks applied to clone blocks
   satisfies ~inst_targets callee.fn_name *)
Triviality rewrite_inline_blocks_no_targets[local]:
  !name bbs ops outs ret_lbl pidx.
    EVERY (\bb. EVERY (\i. ~inst_targets name i) bb.bb_instructions) bbs ==>
    EVERY (\bb. EVERY (\i. ~inst_targets name i) bb.bb_instructions)
      (FST (rewrite_inline_blocks ops outs ret_lbl bbs pidx))
Proof
  Induct_on `bbs` >>
  simp[rewrite_inline_blocks_def, LET_THM] >>
  rpt gen_tac >> strip_tac >>
  Cases_on `rewrite_inline_block ops outs ret_lbl h pidx` >>
  Cases_on `rewrite_inline_blocks ops outs ret_lbl bbs r` >>
  simp[] >>
  conj_tac
  >- (
    gvs[rewrite_inline_block_def, LET_THM] >>
    Cases_on `rewrite_inline_insts ops outs ret_lbl h.bb_instructions pidx` >>
    gvs[] >> metis_tac[rewrite_inline_insts_no_targets, FST]
  ) >>
  `q' = FST (rewrite_inline_blocks ops outs ret_lbl bbs r)` by simp[] >>
  pop_assum SUBST_ALL_TAC >>
  first_x_assum irule >> fs[]
QED

(* clone_function blocks all satisfy ~inst_targets *)
Triviality clone_fn_no_targets[local]:
  !name callee prefix.
    fn_no_invoke name callee /\
    invoke_targets_extern callee ==>
    EVERY (\bb. EVERY (\i. ~inst_targets name i) bb.bb_instructions)
      (clone_function prefix callee).fn_blocks
Proof
  rpt strip_tac >>
  simp[clone_function_def, LET_THM, EVERY_MAP, clone_basic_block_def,
       EVERY_MEM] >> rpt strip_tac >>
  fs[MEM_MAP, clone_basic_block_def] >>
  qpat_x_assum `_ = _` SUBST_ALL_TAC >> fs[MEM_MAP] >>
  metis_tac[clone_inst_no_targets]
QED

(* General: if P holds vacuously when ~inst_targets, then P holds for
   rewritten clone blocks. Combines clone_fn_no_targets +
   rewrite_inline_blocks_no_targets + EVERY_MONOTONIC. *)
Triviality rewrite_clone_blocks_every_P[local]:
  !P name callee prefix ops outs ret_lbl pidx.
    fn_no_invoke name callee /\
    invoke_targets_extern callee /\
    (!i. ~inst_targets name i ==> P i) ==>
    EVERY (\bb. EVERY P bb.bb_instructions)
      (FST (rewrite_inline_blocks ops outs ret_lbl
             (clone_function prefix callee).fn_blocks pidx))
Proof
  rpt strip_tac >>
  `EVERY (\bb. EVERY (\i. ~inst_targets name i) bb.bb_instructions)
     (FST (rewrite_inline_blocks ops outs ret_lbl
            (clone_function prefix callee).fn_blocks pidx))` by
    (irule rewrite_inline_blocks_no_targets >> metis_tac[clone_fn_no_targets]) >>
  fs[EVERY_MEM] >> rpt strip_tac >>
  first_x_assum drule >> strip_tac >>
  fs[EVERY_MEM] >> rpt strip_tac >>
  first_x_assum drule >> strip_tac >>
  metis_tac[]
QED



(* fix_inline_phis only modifies PHI instructions, preserving any predicate
   that ignores PHI changes *)
Triviality fix_inline_phis_preserves_every[local]:
  !P olbl nlbl rbb fn_in.
    (!i. i.inst_opcode = PHI ==> P i) ==>
    (EVERY (\bb. EVERY P bb.bb_instructions)
       (fix_inline_phis olbl nlbl rbb fn_in).fn_blocks <=>
     EVERY (\bb. EVERY P bb.bb_instructions) fn_in.fn_blocks)
Proof
  rpt strip_tac >>
  simp[fix_inline_phis_def, LET_THM, EVERY_MAP] >>
  irule EVERY_CONG >> rw[] >> rename [`MEM blk _`] >>
  Cases_on `MEM blk.bb_label (bb_succs rbb)` >> simp[] >>
  simp[EVERY_MAP] >> irule EVERY_CONG >> rw[] >>
  rename [`MEM ins _`] >>
  Cases_on `ins.inst_opcode = PHI` >> simp[] >>
  `(subst_label_inst olbl nlbl ins).inst_opcode = PHI` by
    simp[subst_label_inst_def] >>
  metis_tac[]
QED

(* Helper: inline_call_site preserves EVERY P on block instructions.
   Factors out the common pattern of showing P is preserved through
   replace_block ++ [return_bb] ++ rewritten_blocks. *)
Triviality inline_call_site_preserves_every_inst[local]:
  !P prefix ret_lbl caller callee call_lbl idx.
    EVERY (\bb. EVERY P bb.bb_instructions) caller.fn_blocks /\
    (!ops outs pidx.
       EVERY (\bb. EVERY P bb.bb_instructions)
         (FST (rewrite_inline_blocks ops outs ret_lbl
                (clone_function prefix callee).fn_blocks pidx))) /\
    (!ops. P <| inst_id := 0; inst_opcode := JMP;
               inst_operands := ops; inst_outputs := [] |>) ==>
    EVERY (\bb. EVERY P bb.bb_instructions)
      (inline_call_site prefix ret_lbl caller callee call_lbl idx).fn_blocks
Proof
  rpt strip_tac >>
  simp[inline_call_site_def] >>
  Cases_on `lookup_block call_lbl caller.fn_blocks` >> simp[] >>
  rename [`_ = SOME call_bb`] >>
  simp[LET_THM, UNCURRY, EVERY_APPEND, EVERY_MAP, replace_block_def,
       EVERY_MEM, MEM_MAP] >>
  rpt strip_tac >> gvs[] >- (
    (* replace_block: bb' from caller blocks *)
    Cases_on `bb'.bb_label = call_lbl` >> gvs[] >- (
      (* Modified block: TAKE ++ [JMP] *)
      fs[MEM_APPEND, MEM_TAKE] >>
      `MEM call_bb caller.fn_blocks` by metis_tac[lookup_block_MEM] >>
      qpat_assum `EVERY _ caller.fn_blocks`
        (mp_tac o REWRITE_RULE [EVERY_MEM]) >>
      disch_then drule >> simp[EVERY_MEM] >> metis_tac[MEM_TAKE]
    ) >>
    qpat_assum `EVERY _ caller.fn_blocks`
      (mp_tac o REWRITE_RULE [EVERY_MEM]) >>
    disch_then drule >> simp[EVERY_MEM]
  ) >- (
    (* return block: DROP suffix *)
    `MEM call_bb caller.fn_blocks` by metis_tac[lookup_block_MEM] >>
    qpat_assum `EVERY _ caller.fn_blocks`
      (mp_tac o REWRITE_RULE [EVERY_MEM]) >>
    disch_then drule >> simp[EVERY_MEM] >>
    disch_then irule >> metis_tac[MEM_DROP_IMP]
  ) >>
  (* cloned blocks: from rewrite_inline_blocks assumption *)
  first_x_assum (qspecl_then [
    `rotate_invoke_ops call_bb.bb_instructions❲idx❳.inst_operands`,
    `call_bb.bb_instructions❲idx❳.inst_outputs`, `0`] mp_tac) >>
  simp[EVERY_MEM] >> disch_then drule >> disch_then drule >> simp[]
QED

(* General: any inst predicate P true for non-targeting insts is preserved
   through inline_one_site. Covers ret arity, param arity, and similar. *)
Theorem inline_one_site_preserves_every_target_prop[local]:
  !caller callee ist caller' ist' P.
    inline_one_site caller callee ist = SOME (caller', ist') /\
    fn_no_invoke callee.fn_name callee /\
    invoke_targets_extern callee /\
    ALL_DISTINCT (fn_labels caller) /\
    (!i1 i2. i1.inst_opcode = i2.inst_opcode /\
             i1.inst_operands = i2.inst_operands /\
             i1.inst_outputs = i2.inst_outputs ==>
             (P i1 <=> P i2)) /\
    (!inst. ~inst_targets callee.fn_name inst ==> P inst) /\
    EVERY (\bb. EVERY P bb.bb_instructions) caller.fn_blocks ==>
    EVERY (\bb. EVERY P bb.bb_instructions) caller'.fn_blocks
Proof
  rw[inline_one_site_def, LET_THM] >>
  (* Establish preservation lemmas for composition *)
  `!fn'. EVERY (\bb. EVERY P bb.bb_instructions) (renumber_fn_inst_ids fn').fn_blocks <=>
         EVERY (\bb. EVERY P bb.bb_instructions) fn'.fn_blocks` by (
    gen_tac >>
    mp_tac (Q.SPECL [`P`, `fn'`] renumber_fn_preserves_every_inst) >>
    impl_tac >- metis_tac[] >>
    simp[]
  ) >>
  `!olbl nlbl rbb fn_in.
     EVERY (\bb. EVERY P bb.bb_instructions) (fix_inline_phis olbl nlbl rbb fn_in).fn_blocks <=>
     EVERY (\bb. EVERY P bb.bb_instructions) fn_in.fn_blocks` by (
    rpt gen_tac >>
    irule fix_inline_phis_preserves_every >>
    rpt strip_tac >> first_x_assum irule >>
    simp[inst_targets_def]
  ) >>
  (* Case split on find_invoke_site *)
  Cases_on `find_invoke_site callee.fn_name caller.fn_blocks` >> gvs[] >>
  Cases_on `x` >> gvs[] >>
  (* Establish inline_call_site preserves EVERY P (before further case splits) *)
  `!lbl idx. EVERY (\bb. EVERY P bb.bb_instructions)
     (inline_call_site (inline_prefix ist.is_inline_count)
        (return_block_label (inline_prefix ist.is_inline_count)
           ist.is_label_counter)
        caller callee lbl idx).fn_blocks` by (
    rpt gen_tac >>
    mp_tac (Q.SPECL [`P`,
      `inline_prefix ist.is_inline_count`,
      `return_block_label (inline_prefix ist.is_inline_count) ist.is_label_counter`,
      `caller`, `callee`, `lbl`, `idx`] inline_call_site_preserves_every_inst) >>
    impl_tac >- (
      rpt conj_tac
      >- first_assum ACCEPT_TAC
      >- (
        rpt gen_tac >>
        mp_tac (Q.SPECL [`P`, `callee.fn_name`, `callee`,
          `inline_prefix ist.is_inline_count`,
          `ops`, `outs`,
          `return_block_label (inline_prefix ist.is_inline_count) ist.is_label_counter`,
          `pidx`] rewrite_clone_blocks_every_P) >>
        simp[]
      ) >>
      rpt strip_tac >>
      qpat_x_assum `!inst. ~inst_targets _ _ ==> _` irule >>
      simp[inst_targets_def]
    ) >>
    simp[]
  ) >>
  Cases_on `lookup_block
    (return_block_label (inline_prefix ist.is_inline_count) ist.is_label_counter)
    (inline_call_site (inline_prefix ist.is_inline_count)
       (return_block_label (inline_prefix ist.is_inline_count) ist.is_label_counter)
       caller callee q r).fn_blocks` >> simp[]
QED
(* Per-round exclusion: inline_one_site at counter N excludes only prefix N.
   Each round's result_equiv is weakened to inline_vars via subset.

   callee_ret_arity_le condition: at every invoke of the callee in the caller,
   the number of invoke outputs >= every RET operand count in the callee.
   This is the standard calling convention arity check. *)
Theorem inline_at_sites_fn_correct:
  !n caller callee ist caller' ist' fuel ctx s.
    inline_at_sites n caller callee ist = (caller', ist') /\
    lookup_function callee.fn_name ctx.ctx_functions = SOME callee /\
    fn_no_invoke callee.fn_name callee /\
    invoke_targets_extern callee /\
    ALL_DISTINCT (fn_labels callee) /\
    labels_no_inline_return callee /\
    ALL_DISTINCT (fn_labels caller) /\
    labels_fresh_above ist.is_inline_count caller /\
    fn_no_alloca caller /\
    fn_no_alloca callee /\
    EVERY bb_well_formed caller.fn_blocks /\
    EVERY bb_well_formed callee.fn_blocks /\
    EVERY (\bb. params_sequential bb.bb_instructions 0) callee.fn_blocks /\
    EVERY (\bb. EVERY (\i. i.inst_opcode <> PARAM) bb.bb_instructions)
      (TL callee.fn_blocks) /\
    fn_has_entry callee /\
    label_ops_closed caller /\
    label_ops_closed callee /\
    vars_fresh_above ist.is_inline_count caller /\
    (* Arity: every invoke of callee has enough outputs for callee's RETs *)
    EVERY (\bb. EVERY (\inst.
      inst_targets callee.fn_name inst ==>
      callee_ret_arity_le (LENGTH inst.inst_outputs) callee)
      bb.bb_instructions) caller.fn_blocks /\
    EVERY (\bb. EVERY (\inst.
      inst_targets callee.fn_name inst ==>
      EVERY (\blk. count_params blk.bb_instructions <=
                   LENGTH (TL inst.inst_operands)) callee.fn_blocks)
      bb.bb_instructions) caller.fn_blocks /\
    EVERY (\bb. EVERY (\inst.
      inst_targets callee.fn_name inst ==>
      ALL_DISTINCT inst.inst_outputs)
      bb.bb_instructions) caller.fn_blocks /\
    EVERY (\bb. EVERY (\inst.
      inst_targets callee.fn_name inst ==>
      EVERY (\op. !v. op = Var v ==> ~MEM v inst.inst_outputs)
        (TL inst.inst_operands))
      bb.bb_instructions) caller.fn_blocks /\
    s.vs_prev_bb = NONE /\
    s.vs_inst_idx = 0 /\
    FDOM s.vs_labels = {} /\
    ~s.vs_halted ==>
    ?fuel'.
      lift_result (state_equiv inline_vars) shared_globals_np
        (run_function fuel ctx caller s)
        (run_function fuel' ctx caller' s)
Proof
  Induct >- (
    rw[inline_at_sites_def] >>
    qexists_tac `fuel` >> simp[lift_result_refl_inline]
  ) >>
  rpt gen_tac >> strip_tac >>
  gvs[inline_at_sites_def] >>
  Cases_on `inline_one_site caller callee ist` >- (
    gvs[] >>
    qexists_tac `fuel` >> simp[lift_result_refl_inline]
  ) >>
  rename1 `_ = SOME mid_pair` >>
  PairCases_on `mid_pair` >> gvs[] >>
  rename1 `inline_one_site caller callee ist = SOME (mid, ist_mid)` >>
  (* Step 1: Apply inline_one_site_fn_correct — use suspend for debugging *)
  `?fuel1. lift_result (state_equiv
      {v | isPREFIX (inline_prefix ist.is_inline_count) v})
      shared_globals_np
      (run_function fuel ctx caller s)
      (run_function fuel1 ctx mid s)` by
    suspend "step1" >>
  (* Step 2: Establish preservation for IH *)
  `ist_mid.is_inline_count = ist.is_inline_count + 1` by
    metis_tac[inline_one_site_ist_count] >>
  `ALL_DISTINCT (fn_labels mid)` by
    metis_tac[inline_one_site_preserves_preconds] >>
  `labels_fresh_above ist_mid.is_inline_count mid` by
    metis_tac[inline_one_site_preserves_preconds] >>
  `fn_no_alloca mid` by
    metis_tac[inline_one_site_no_alloca] >>
  `EVERY bb_well_formed mid.fn_blocks` by
    metis_tac[inline_one_site_every_bb_well_formed] >>
  `label_ops_closed mid` by
    metis_tac[inline_one_site_label_ops_closed] >>
  `vars_fresh_above ist_mid.is_inline_count mid` by
    suspend "vars_fresh" >>
  `EVERY (\bb. EVERY (\inst.
     inst_targets callee.fn_name inst ==>
     callee_ret_arity_le (LENGTH inst.inst_outputs) callee)
     bb.bb_instructions) mid.fn_blocks` by (
    mp_tac (Q.SPECL [`caller`, `callee`, `ist`, `mid`, `ist_mid`,
      `\inst. inst_targets callee.fn_name inst ==>
              callee_ret_arity_le (LENGTH inst.inst_outputs) callee`]
      inline_one_site_preserves_every_target_prop) >>
    simp[] >>
    disch_then irule >> rpt conj_tac >>
    rpt strip_tac >> simp[inst_targets_def, callee_ret_arity_le_def]) >>
  `EVERY (\bb. EVERY (\inst.
     inst_targets callee.fn_name inst ==>
     EVERY (\blk. count_params blk.bb_instructions <=
                  LENGTH inst.inst_operands - 1) callee.fn_blocks)
     bb.bb_instructions) mid.fn_blocks` by (
    mp_tac (Q.SPECL [`caller`, `callee`, `ist`, `mid`, `ist_mid`,
      `\inst. inst_targets callee.fn_name inst ==>
              EVERY (\blk. count_params blk.bb_instructions <=
                           LENGTH inst.inst_operands - 1) callee.fn_blocks`]
      inline_one_site_preserves_every_target_prop) >>
    simp[] >>
    disch_then irule >> rpt conj_tac >>
    rpt strip_tac >> simp[inst_targets_def]) >>
  `EVERY (\bb. EVERY (\inst.
     inst_targets callee.fn_name inst ==>
     ALL_DISTINCT inst.inst_outputs)
     bb.bb_instructions) mid.fn_blocks` by (
    mp_tac (Q.SPECL [`caller`, `callee`, `ist`, `mid`, `ist_mid`,
      `\inst. inst_targets callee.fn_name inst ==>
              ALL_DISTINCT inst.inst_outputs`]
      inline_one_site_preserves_every_target_prop) >>
    simp[] >>
    disch_then irule >> rpt conj_tac >>
    rpt strip_tac >> simp[inst_targets_def]) >>
  `EVERY (\bb. EVERY (\inst.
     inst_targets callee.fn_name inst ==>
     EVERY (\op. !v. op = Var v ==> ~MEM v inst.inst_outputs)
       (TL inst.inst_operands))
     bb.bb_instructions) mid.fn_blocks` by (
    mp_tac (Q.SPECL [`caller`, `callee`, `ist`, `mid`, `ist_mid`,
      `\inst. inst_targets callee.fn_name inst ==>
              EVERY (\op. !v. op = Var v ==> ~MEM v inst.inst_outputs)
                (TL inst.inst_operands)`]
      inline_one_site_preserves_every_target_prop) >>
    simp[] >>
    disch_then irule >> rpt conj_tac >>
    rpt strip_tac >> simp[inst_targets_def]) >>
  `?fuel2. lift_result (state_equiv inline_vars) shared_globals_np
      (run_function fuel1 ctx mid s)
      (run_function fuel2 ctx caller' s)` by
    suspend "ih_dispatch" >>
  (* Step 4: Compose — weaken step 1 and combine with step 3 *)
  imp_res_tac lift_result_weaken_to_inline_vars >>
  qexists_tac `fuel2` >>
  irule lift_result_inline_trans >>
  qexists_tac `run_function fuel1 ctx mid s` >>
  simp[]
QED

Resume inline_at_sites_fn_correct[step1]:
  (* Establish the two ∀-quantified preconditions in NOTIN form *)
  `!bb inst x. MEM bb caller.fn_blocks /\
     MEM inst bb.bb_instructions /\ MEM (Var x) inst.inst_operands ==>
     x NOTIN {v | isPREFIX (inline_prefix ist.is_inline_count) v}` by
    metis_tac[vars_fresh_above_notin_prefix_set] >>
  `!bb inst lbl. MEM bb caller.fn_blocks /\
     MEM inst bb.bb_instructions /\
     MEM (Label lbl) inst.inst_operands ==>
     MEM lbl (fn_labels caller)` by
    gvs[label_ops_closed_def] >>
  (* Apply inline_one_site_fn_correct *)
  qspecl_then [`caller`, `callee`, `ist`, `mid`, `ist_mid`,
    `{v | isPREFIX (inline_prefix ist.is_inline_count) v}`,
    `fuel`, `ctx`, `s`]
    mp_tac inline_one_site_fn_correct >>
  impl_tac >- (rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >> fs[]) >>
  strip_tac >> qexists_tac `fuel'` >> simp[]
QED

Resume inline_at_sites_fn_correct[vars_fresh]:
  qpat_x_assum `ist_mid.is_inline_count = _` SUBST1_TAC >>
  irule vars_fresh_above_inline_one_site >>
  MAP_EVERY qexists_tac [`callee`, `caller`, `ist_mid`] >>
  rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
  (* Remaining: the arity condition at the invoke site *)
  rpt strip_tac >>
  `ALL_DISTINCT (MAP (\b. b.bb_label) caller.fn_blocks)` by
    gvs[fn_labels_def] >>
  drule find_invoke_site_inst_targets >> simp[] >> strip_tac >> gvs[] >>
  (* Now call_bb = bb from find_invoke_site_inst_targets *)
  imp_res_tac lookup_block_MEM >>
  (* Use EVERY callee_ret_arity_le on caller.fn_blocks — be specific to avoid
     picking the count_params assumption *)
  qpat_x_assum `EVERY (\bb. EVERY (\inst.
     inst_targets _ inst ==> callee_ret_arity_le _ _) bb.bb_instructions)
     caller.fn_blocks`
    (fn th => assume_tac (REWRITE_RULE [EVERY_MEM] th)) >>
  first_x_assum (qspec_then `call_bb` mp_tac) >> simp[] >> strip_tac >>
  pop_assum (fn th => assume_tac (REWRITE_RULE [EVERY_MEM] th)) >>
  first_x_assum (qspec_then `EL idx call_bb.bb_instructions` mp_tac) >>
  simp[MEM_EL] >> disch_then irule >> qexists_tac `idx` >> simp[]
QED

Resume inline_at_sites_fn_correct[ih_dispatch]:
  (* Apply the IH with mid as the caller *)
  first_x_assum (qspecl_then [`mid`, `callee`, `ist_mid`, `caller'`,
    `ist'`, `fuel1`, `ctx`, `s`] mp_tac) >>
  simp[] >>
  disch_then (qx_choose_then `fuel2` assume_tac) >>
  qexists_tac `fuel2` >> simp[]
QED

Finalise inline_at_sites_fn_correct;

(* ================================================================
   Section 6: Context-level correctness
   ================================================================ *)

Theorem inline_at_sites_identity:
  !n fn callee ist.
    fn_no_invoke callee.fn_name fn ==>
    inline_at_sites n fn callee ist = (fn, ist)
Proof
  Induct >> rw[inline_at_sites_def] >>
  SUBGOAL_THEN ``find_invoke_site callee.fn_name fn.fn_blocks = NONE``
    ASSUME_TAC >- gvs[fn_no_invoke_def, find_invoke_site_none] >>
  simp[inline_one_site_def]
QED

Triviality FIND_APPEND:
  !P (xs:'a list) ys.
    FIND P (xs ++ ys) =
    case FIND P xs of SOME x => SOME x | NONE => FIND P ys
Proof
  gen_tac >> Induct >> simp[FIND_thm] >> rpt strip_tac >>
  Cases_on `P h` >> simp[]
QED

Theorem foldl_inline_find_callee:
  !fns0 acc ist0 callee result ist1.
    FOLDL (\(fns_acc, st) caller_fn.
      let max_sites = LENGTH (fn_insts caller_fn) in
      let (caller', st') = inline_at_sites max_sites caller_fn callee st in
      (SNOC caller' fns_acc, st'))
      (acc, ist0) fns0 = (result, ist1) /\
    fn_no_invoke callee.fn_name callee /\
    FIND (\f. f.fn_name = callee.fn_name) (acc ++ fns0) = SOME callee ==>
    FIND (\f. f.fn_name = callee.fn_name) result = SOME callee
Proof
  Induct >> rpt strip_tac >> gvs[APPEND_NIL] >>
  gvs[LET_THM] >> pairarg_tac >> gvs[] >>
  first_x_assum (qspecl_then [`SNOC caller' acc`, `st'`, `callee`,
    `result`, `ist1`] mp_tac) >>
  simp[] >>
  disch_then irule >>
  imp_res_tac inline_at_sites_fn_name >>
  simp[SNOC_APPEND, FIND_APPEND] >>
  gvs[FIND_APPEND] >>
  Cases_on `FIND (\f. f.fn_name = callee.fn_name) acc` >> gvs[] >>
  Cases_on `h.fn_name = callee.fn_name` >> gvs[FIND_thm] >>
  imp_res_tac inline_at_sites_identity >> gvs[]
QED

Theorem inline_candidate_callee_unchanged:
  !ctx callee ist ctx' ist'.
    inline_candidate ctx callee ist = (ctx', ist') /\
    lookup_function callee.fn_name ctx.ctx_functions = SOME callee /\
    fn_no_invoke callee.fn_name callee ==>
    lookup_function callee.fn_name ctx'.ctx_functions = SOME callee
Proof
  rw[inline_candidate_def, lookup_function_def] >>
  pairarg_tac >> gvs[] >>
  mp_tac (SIMP_RULE (srw_ss()) [LET_THM] foldl_inline_find_callee) >>
  disch_then drule >> simp[]
QED

val _ = export_theory();

