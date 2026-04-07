(*
 * Analysis-Driven Simulation — Block/Function Compare Proofs
 *
 * EXPORTS:
 *   analysis_block_compare
 *   block_sim_function_compare
 *)

Theory analysisSimProofsCompare
Ancestors
  analysisSimProofsBase
  analysisSimDefs execEquivParamDefs
  passSimulationDefs passSimulationProofs execEquivParamProofs
  execEquivParamBase stateEquiv venomExecSemantics venomInst instIdxIndep
  venomState
Libs
  listTheory finite_mapTheory pred_setTheory

(* Shared simplification theorems for expanding Abbrev'd blocks
   WITHOUT triggering srw_ss() loops on FLAT/MAPi terms.
   Use: simp_tac std_ss abbrev_expand_thms *)
val abbrev_expand_thms = [
  basic_block_accfupds, combinTheory.K_THM, combinTheory.o_THM,
  combinTheory.K_o_THM, (* K v ∘ f = K v, needed for double-idx collapse *)
  cj 6 venom_state_fupdfupds (* vs_inst_idx double-update collapse *)];

(* Focused helper: halted agreement from R_ok.
   imp_res_tac vsr_R_ok_fields explodes when R_ok transitivity is in context. *)
Triviality vsr_R_ok_halted:
  valid_state_rel R_ok R_term /\ R_ok s1 s2 ==> (s1.vs_halted <=> s2.vs_halted)
Proof
  rw[valid_state_rel_def]
QED

Triviality is_terminator_not_INVOKE:
  is_terminator op ==> op <> INVOKE
Proof
  Cases_on `op` >> simp[is_terminator_def]
QED

(* Helper: terminator halted_wrap preserves lift_result through idx change *)
Triviality terminator_halted_wrap_lift:
  !R_ok R_term inst1 inst2 s1 s2 fuel ctx.
    valid_state_rel R_ok R_term /\
    (!s1 s2 s3. R_ok s1 s2 /\ R_ok s2 s3 ==> R_ok s1 s3) /\
    (!s1 s2 s3. R_term s1 s2 /\ R_term s2 s3 ==> R_term s1 s3) /\
    is_terminator inst1.inst_opcode /\
    is_terminator inst2.inst_opcode /\
    lift_result R_ok R_term
      (step_inst fuel ctx inst1 (s1 with vs_inst_idx := 0))
      (step_inst fuel ctx inst2 (s2 with vs_inst_idx := 0))
  ==>
    lift_result R_ok R_term
      (case step_inst fuel ctx inst1 s1 of
         OK s'' => if s''.vs_halted then Halt s'' else OK s''
       | Halt s' => Halt s' | Abort a' s' => Abort a' s'
       | IntRet rv ss => IntRet rv ss | Error e => Error e)
      (case step_inst fuel ctx inst2 s2 of
         OK s'' => if s''.vs_halted then Halt s'' else OK s''
       | Halt s' => Halt s' | Abort a' s' => Abort a' s'
       | IntRet rv ss => IntRet rv ss | Error e => Error e)
Proof
  rpt strip_tac >>
  (* Chain: halted_wrap(inst1@s1) -> halted_wrap(inst1@s1_0) ->
            halted_wrap(inst2@s2_0) -> halted_wrap(inst2@s2) *)
  irule lift_result_trans_proof >>
  conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac >- first_assum ACCEPT_TAC >>
  qexists_tac `case step_inst fuel ctx inst2 (s2 with vs_inst_idx := 0) of
    OK s'' => if s''.vs_halted then Halt s'' else OK s''
  | Halt s' => Halt s' | Abort a' s' => Abort a' s'
  | IntRet rv ss => IntRet rv ss | Error e => Error e` >>
  conj_tac
  >- (
    irule lift_result_trans_proof >>
    conj_tac >- first_assum ACCEPT_TAC >>
    conj_tac >- first_assum ACCEPT_TAC >>
    qexists_tac `case step_inst fuel ctx inst1 (s1 with vs_inst_idx := 0) of
      OK s'' => if s''.vs_halted then Halt s'' else OK s''
    | Halt s' => Halt s' | Abort a' s' => Abort a' s'
    | IntRet rv ss => IntRet rv ss | Error e => Error e` >>
    conj_tac
    >- (irule terminator_exec_block_step_lift >> simp[])
    >>
    (* halted_wrap preserves lift_result *)
    `inst1.inst_opcode <> INVOKE` by metis_tac[is_terminator_not_INVOKE] >>
    `inst2.inst_opcode <> INVOKE` by metis_tac[is_terminator_not_INVOKE] >>
    fs[step_inst_non_invoke] >>
    Cases_on `step_inst_base inst1 (s1 with vs_inst_idx := 0)` >>
    Cases_on `step_inst_base inst2 (s2 with vs_inst_idx := 0)` >>
    gvs[lift_result_def]
    >- (
      rename1 `R_ok v1 v2` >>
      `v1.vs_halted <=> v2.vs_halted` by metis_tac[vsr_R_ok_halted] >>
      simp[] >>
      Cases_on `v1.vs_halted` >> gvs[lift_result_def] >>
      metis_tac[vsr_R_ok_R_term])
    >> TRY (irule R_term_idx_change_both >> metis_tac[]))
  >>
  irule terminator_exec_block_step_lift_rev >> simp[]
QED

(* ===== Terminator case helper ===== *)
Triviality abc_terminator_case:
  !(R_ok : venom_state -> venom_state -> bool)
   (R_term : venom_state -> venom_state -> bool)
   inst1 inst2 s1 s2 s1_0 s2_0 j1 j2 bb g1 g2 fuel ctx.
    valid_state_rel R_ok R_term /\
    (!s1 s2 s3. R_ok s1 s2 /\ R_ok s2 s3 ==> R_ok s1 s3) /\
    (!s1 s2 s3. R_term s1 s2 /\ R_term s2 s3 ==> R_term s1 s3) /\
    is_terminator inst1.inst_opcode /\
    is_terminator inst2.inst_opcode /\
    R_ok s1_0 s2_0 /\
    s1_0 = s1 with vs_inst_idx := 0 /\
    s2_0 = s2 with vs_inst_idx := 0 /\
    s1.vs_inst_idx = j1 /\ s2.vs_inst_idx = j2 /\
    j1 < LENGTH (FLAT (MAPi g1 bb.bb_instructions)) /\
    j2 < LENGTH (FLAT (MAPi g2 bb.bb_instructions)) /\
    EL j1 (FLAT (MAPi g1 bb.bb_instructions)) = inst1 /\
    EL j2 (FLAT (MAPi g2 bb.bb_instructions)) = inst2 /\
    ((?e. step_inst fuel ctx inst1 s2_0 = Error e) \/
     lift_result R_ok R_term (step_inst fuel ctx inst1 s2_0)
       (step_inst fuel ctx inst2 s2_0)) /\
    lift_result R_ok R_term (step_inst fuel ctx inst1 s1_0)
      (step_inst fuel ctx inst1 s2_0)
  ==>
    (?e. exec_block fuel ctx
           (bb with bb_instructions := FLAT (MAPi g1 bb.bb_instructions))
           s1 = Error e) \/
    lift_result R_ok R_term
      (exec_block fuel ctx
         (bb with bb_instructions := FLAT (MAPi g1 bb.bb_instructions)) s1)
      (exec_block fuel ctx
         (bb with bb_instructions := FLAT (MAPi g2 bb.bb_instructions)) s2)
Proof
  rpt gen_tac >> DISCH_TAC >>
  pop_assum (REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) >>
  `inst1.inst_opcode <> INVOKE` by metis_tac[is_terminator_not_INVOKE] >>
  `inst2.inst_opcode <> INVOKE` by metis_tac[is_terminator_not_INVOKE] >>
  (* Split error/non-error without pattern matching *)
  Cases_on `?e. step_inst fuel ctx inst1 s2_0 = Error e`
  >- (
    (* Error case *)
    pop_assum strip_assume_tac >>
    `?e'. step_inst fuel ctx inst1 s1_0 = Error e'` by
      metis_tac[lift_result_error_left] >>
    DISJ1_TAC >>
    ONCE_REWRITE_TAC[venomExecSemanticsTheory.exec_block_def] >>
    simp[get_instruction_def] >>
    gvs[] >> imp_res_tac step_inst_error_idx_recover >> gvs[])
  >>
  (* Non-error case: extract lift_result from disjunction *)
  `lift_result R_ok R_term (step_inst fuel ctx inst1 s2_0)
     (step_inst fuel ctx inst2 s2_0)` by metis_tac[] >>
  `lift_result R_ok R_term (step_inst fuel ctx inst1 s1_0)
     (step_inst fuel ctx inst2 s2_0)` by (
    irule lift_result_trans_proof >>
    conj_tac >- first_assum ACCEPT_TAC >>
    conj_tac >- first_assum ACCEPT_TAC >>
    qexists_tac `step_inst fuel ctx inst1 s2_0` >>
    conj_tac >> first_assum ACCEPT_TAC) >>
  (* Unfold exec_block to halted_wrap(step_inst inst s) *)
  ONCE_REWRITE_TAC[venomExecSemanticsTheory.exec_block_def] >>
  simp[get_instruction_def] >>
  DISJ2_TAC >>
  (* Chain through s1_0/s2_0 using terminator_exec_block_step_lift *)
  irule lift_result_trans_proof >>
  conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac >- first_assum ACCEPT_TAC >>
  qexists_tac `case step_inst fuel ctx inst2 s2_0 of
    OK s'' => if s''.vs_halted then Halt s'' else OK s''
  | Halt s' => Halt s' | Abort a' s' => Abort a' s'
  | IntRet rv ss => IntRet rv ss | Error e => Error e` >>
  conj_tac
  >- (
    irule lift_result_trans_proof >>
    conj_tac >- first_assum ACCEPT_TAC >>
    conj_tac >- first_assum ACCEPT_TAC >>
    qexists_tac `case step_inst fuel ctx inst1 s1_0 of
      OK s'' => if s''.vs_halted then Halt s'' else OK s''
    | Halt s' => Halt s' | Abort a' s' => Abort a' s'
    | IntRet rv ss => IntRet rv ss | Error e => Error e` >>
    conj_tac
    >- (
      (* exec_block@s1 -> halted_wrap(inst1@s1_0) *)
      gvs[] >> irule terminator_exec_block_step_lift >> simp[venom_state_idx_self_update])
    >>
    (* halted_wrap(inst1@s1_0) -> halted_wrap(inst2@s2_0) *)
    Cases_on `step_inst fuel ctx inst1 s1_0` >>
    Cases_on `step_inst fuel ctx inst2 s2_0` >>
    gvs[lift_result_def]
    >- (
      rename1 `R_ok v1 v2` >>
      `v1.vs_halted <=> v2.vs_halted` by metis_tac[vsr_R_ok_halted] >>
      simp[] >>
      Cases_on `v1.vs_halted` >> gvs[lift_result_def] >>
      metis_tac[vsr_R_ok_R_term])
    >> TRY (irule R_term_idx_change_both >> metis_tac[]))
  >>
  (* halted_wrap(inst2@s2_0) -> exec_block@s2:
     Use reverse direction: lift_result(halted_wrap(inst@(s with idx:=j)))(halted_wrap(inst@s)) *)
  gvs[] >> irule terminator_exec_block_step_lift_rev >> simp[]
QED

(* ===== INVOKE case helper ===== *)
Triviality abc_invoke_case:
  !(R_ok : venom_state -> venom_state -> bool)
   (R_term : venom_state -> venom_state -> bool)
   inst1 inst2 s1 s2 s1_0 s2_0 j1 j2 j1_next j2_next bb g1 g2 fuel ctx
   (IH_rest : exec_result -> exec_result -> bool).
    valid_state_rel R_ok R_term /\
    (!s1 s2 s3. R_ok s1 s2 /\ R_ok s2 s3 ==> R_ok s1 s3) /\
    (!s1 s2 s3. R_term s1 s2 /\ R_term s2 s3 ==> R_term s1 s3) /\
    inst1.inst_opcode = INVOKE /\ inst2.inst_opcode = INVOKE /\
    R_ok s1_0 s2_0 /\
    s1_0 = s1 with vs_inst_idx := 0 /\
    s2_0 = s2 with vs_inst_idx := 0 /\
    s1.vs_inst_idx = j1 /\ s2.vs_inst_idx = j2 /\
    j1_next = SUC j1 /\ j2_next = SUC j2 /\
    j1 < LENGTH (FLAT (MAPi g1 bb.bb_instructions)) /\
    j2 < LENGTH (FLAT (MAPi g2 bb.bb_instructions)) /\
    EL j1 (FLAT (MAPi g1 bb.bb_instructions)) = inst1 /\
    EL j2 (FLAT (MAPi g2 bb.bb_instructions)) = inst2 /\
    ((?e. step_inst fuel ctx inst1 s2_0 = Error e) \/
     lift_result R_ok R_term (step_inst fuel ctx inst1 s2_0)
       (step_inst fuel ctx inst2 s2_0)) /\
    lift_result R_ok R_term (step_inst fuel ctx inst1 s1_0)
      (step_inst fuel ctx inst1 s2_0) /\
    (* IH_rest: after INVOKE OK/OK, remaining block simulates *)
    (!v1 v2.
       R_ok (v1 with vs_inst_idx := 0) (v2 with vs_inst_idx := 0) ==>
       (?e. exec_block fuel ctx
              (bb with bb_instructions := FLAT (MAPi g1 bb.bb_instructions))
              (v1 with vs_inst_idx := j1_next) = Error e) \/
       lift_result R_ok R_term
         (exec_block fuel ctx
            (bb with bb_instructions := FLAT (MAPi g1 bb.bb_instructions))
            (v1 with vs_inst_idx := j1_next))
         (exec_block fuel ctx
            (bb with bb_instructions := FLAT (MAPi g2 bb.bb_instructions))
            (v2 with vs_inst_idx := j2_next)))
  ==>
    (?e. exec_block fuel ctx
           (bb with bb_instructions := FLAT (MAPi g1 bb.bb_instructions))
           s1 = Error e) \/
    lift_result R_ok R_term
      (exec_block fuel ctx
         (bb with bb_instructions := FLAT (MAPi g1 bb.bb_instructions)) s1)
      (exec_block fuel ctx
         (bb with bb_instructions := FLAT (MAPi g2 bb.bb_instructions)) s2)
Proof
  rpt gen_tac >> DISCH_TAC >>
  pop_assum (REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) >>
  qpat_x_assum `j1_next = SUC j1` SUBST_ALL_TAC >>
  qpat_x_assum `j2_next = SUC j2` SUBST_ALL_TAC >>
  (* Compose: step_inst inst1 s1_0 -> step_inst inst2 s2_0 *)
  Cases_on `?e. step_inst fuel ctx inst1 s2_0 = Error e`
  >- (
    pop_assum strip_assume_tac >>
    `?e'. step_inst fuel ctx inst1 s1_0 = Error e'` by
      metis_tac[lift_result_error_left] >>
    DISJ1_TAC >>
    `step_inst fuel ctx inst1 s1 =
     case step_inst fuel ctx inst1 s1_0 of
       OK s'' => OK (s'' with vs_inst_idx := j1) | x => x` by (
      `s1 = s1_0 with vs_inst_idx := j1` by rw[venom_state_component_equality] >>
      pop_assum SUBST1_TAC >> simp[invoke_step_inst_idx_OK_only]) >>
    ONCE_REWRITE_TAC[venomExecSemanticsTheory.exec_block_def] >>
    simp[get_instruction_def])
  >>
  `lift_result R_ok R_term (step_inst fuel ctx inst1 s2_0)
     (step_inst fuel ctx inst2 s2_0)` by metis_tac[] >>
  `lift_result R_ok R_term (step_inst fuel ctx inst1 s1_0)
     (step_inst fuel ctx inst2 s2_0)` by (
    irule lift_result_trans_proof >>
    rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
    qexists_tac `step_inst fuel ctx inst1 s2_0` >>
    conj_tac >> first_assum ACCEPT_TAC) >>
  (* Case-split on step_inst inst1 s1_0 *)
  Cases_on `step_inst fuel ctx inst1 s1_0`
  >- (
    (* OK case *)
    rename1 `step_inst _ _ inst1 s1_0 = OK v1` >>
    `?v2. step_inst fuel ctx inst2 s2_0 = OK v2 /\ R_ok v1 v2` by (
      Cases_on `step_inst fuel ctx inst2 s2_0` >> fs[lift_result_def]) >>
    `step_inst fuel ctx inst1 s1 = OK (v1 with vs_inst_idx := j1)` by (
      `s1 = s1_0 with vs_inst_idx := j1` by rw[venom_state_component_equality] >>
      pop_assum SUBST1_TAC >> simp[invoke_step_inst_idx_OK_only]) >>
    `step_inst fuel ctx inst2 s2 = OK (v2 with vs_inst_idx := j2)` by (
      `s2 = s2_0 with vs_inst_idx := j2` by rw[venom_state_component_equality] >>
      pop_assum SUBST1_TAC >> simp[invoke_step_inst_idx_OK_only]) >>
    `v1.vs_inst_idx = 0` by (
      imp_res_tac step_inst_preserves_inst_idx >> gvs[is_terminator_def]) >>
    `v2.vs_inst_idx = 0` by (
      imp_res_tac step_inst_preserves_inst_idx >> gvs[is_terminator_def]) >>
    first_x_assum (qspecl_then [`v1`, `v2`] mp_tac) >>
    impl_tac >- (
      `v1 with vs_inst_idx := 0 = v1` by rw[venom_state_component_equality] >>
      `v2 with vs_inst_idx := 0 = v2` by rw[venom_state_component_equality] >>
      fs[]) >>
    DISCH_TAC >>
    ONCE_REWRITE_TAC[venomExecSemanticsTheory.exec_block_def] >>
    simp[get_instruction_def, is_terminator_def])
  (* Non-OK cases: Halt, Abort, IntRet, Error *)
  >> (
    (* Derive step_inst inst1 s1 = step_inst inst1 s1_0 for non-OK *)
    `step_inst fuel ctx inst1 s1 = step_inst fuel ctx inst1 s1_0` by (
      `s1 = s1_0 with vs_inst_idx := j1` by rw[venom_state_component_equality] >>
      pop_assum SUBST1_TAC >> simp[invoke_step_inst_idx_OK_only]) >>
    (* From composed lift_result, step_inst inst2 s2_0 has matching constructor *)
    Cases_on `step_inst fuel ctx inst2 s2_0` >>
    fs[lift_result_def] >>
    (* Derive step_inst inst2 s2 = step_inst inst2 s2_0 for non-OK *)
    `step_inst fuel ctx inst2 s2 = step_inst fuel ctx inst2 s2_0` by (
      `s2 = s2_0 with vs_inst_idx := j2` by rw[venom_state_component_equality] >>
      pop_assum SUBST1_TAC >> simp[invoke_step_inst_idx_OK_only]) >>
    DISJ2_TAC >>
    ONCE_REWRITE_TAC[venomExecSemanticsTheory.exec_block_def] >>
    simp[get_instruction_def, lift_result_def])
QED

(* ML tactic: for each assumption "s.vs_inst_idx = j",
   if "s with vs_inst_idx := j" appears in goal or assumptions,
   prove "s with vs_inst_idx := j = s" and SUBST_ALL_TAC it.
   Safe: SUBST_ALL_TAC consumes the equality, no rewrite-direction issues. *)
fun collapse_all_idx (asl, g) =
  let val sel = prim_mk_const{
        Name="recordtype.venom_state.seldef.vs_inst_idx",
        Thy="venomState"}
      val fupd = inst [alpha |-> ``:num``] (prim_mk_const{
            Name="recordtype.venom_state.seldef.vs_inst_idx_fupd",
            Thy="venomState"})
      fun find_one [] = NONE
        | find_one (a::rest) =
            (let val (l,r) = dest_eq a
             in if rator l ~~ sel
                then let val sv = rand l
                         val K_r = mk_comb(inst [alpha |-> ``:num``,
                                   beta |-> ``:num``] combinSyntax.K_tm, r)
                         val upd = mk_comb(mk_comb(fupd, K_r), sv)
                     in if can (find_term (aconv upd)) g orelse
                           List.exists (can (find_term (aconv upd))) asl
                        then SOME (upd, sv, ASSUME a)
                        else find_one rest
                     end
                else find_one rest
             end handle _ => find_one rest)
  in
    case find_one asl of
      NONE => ALL_TAC (asl, g)
    | SOME (upd, sv, th) =>
        (SUBGOAL_THEN (mk_eq(upd, sv)) SUBST_ALL_TAC
         >- (SUBST1_TAC (SYM th) >>
             REWRITE_TAC[venom_state_idx_self_update])
         >> collapse_all_idx) (asl, g)
  end;

(* Error in run_insts prefix → Error in exec_block *)
Triviality exec_block_prefix_error:
  !R_ok R_term prefix fuel ctx bb s j e.
    valid_state_rel R_ok R_term /\
    j + LENGTH prefix <= LENGTH bb.bb_instructions /\
    EVERY (\i. ~is_terminator i.inst_opcode /\ i.inst_opcode <> INVOKE)
      prefix /\
    (!k. k < LENGTH prefix ==> EL (j + k) bb.bb_instructions = EL k prefix) /\
    run_insts fuel ctx prefix s = Error e
  ==>
    ?e'. exec_block fuel ctx bb (s with vs_inst_idx := j) = Error e'
Proof
  rpt strip_tac >>
  `~(?s'. run_insts fuel ctx prefix s = OK s')` by
    (pop_assum SUBST_ALL_TAC >> simp_tac (srw_ss()) []) >>
  drule exec_block_prefix_fail_lift >>
  disch_then (qspecl_then [`prefix`, `fuel`, `ctx`, `bb`, `s`, `j`] mp_tac) >>
  simp[] >> strip_tac >>
  drule_all lift_result_error_left >>
  simp[]
QED

(* ===== Normal case helper ===== *)
Triviality abc_normal_case:
  !(R_ok : venom_state -> venom_state -> bool)
   (R_term : venom_state -> venom_state -> bool)
   f1_group f2_group s1 s2 s1_0 s2_0 j1 j2 bb
   (g1 : num -> instruction -> instruction list)
   (g2 : num -> instruction -> instruction list)
   fuel ctx j1_next j2_next.
    valid_state_rel R_ok R_term /\
    (!s1 s2 s3. R_ok s1 s2 /\ R_ok s2 s3 ==> R_ok s1 s3) /\
    (!s1 s2 s3. R_term s1 s2 /\ R_term s2 s3 ==> R_term s1 s3) /\
    EVERY (\i'. ~is_terminator i'.inst_opcode /\ i'.inst_opcode <> INVOKE)
      f1_group /\
    EVERY (\i'. ~is_terminator i'.inst_opcode /\ i'.inst_opcode <> INVOKE)
      f2_group /\
    R_ok s1_0 s2_0 /\
    s1_0 = s1 with vs_inst_idx := 0 /\
    s2_0 = s2 with vs_inst_idx := 0 /\
    s1.vs_inst_idx = j1 /\ s2.vs_inst_idx = j2 /\
    j1 + LENGTH f1_group <= LENGTH (FLAT (MAPi g1 bb.bb_instructions)) /\
    j2 + LENGTH f2_group <= LENGTH (FLAT (MAPi g2 bb.bb_instructions)) /\
    j1_next = j1 + LENGTH f1_group /\
    j2_next = j2 + LENGTH f2_group /\
    (!k. k < LENGTH f1_group ==>
       EL (j1 + k) (FLAT (MAPi g1 bb.bb_instructions)) =
       EL k f1_group) /\
    (!k. k < LENGTH f2_group ==>
       EL (j2 + k) (FLAT (MAPi g2 bb.bb_instructions)) =
       EL k f2_group) /\
    ((?e. run_insts fuel ctx f1_group s2_0 = Error e) \/
     lift_result R_ok R_term (run_insts fuel ctx f1_group s2_0)
       (run_insts fuel ctx f2_group s2_0)) /\
    lift_result R_ok R_term (run_insts fuel ctx f1_group s1_0)
      (run_insts fuel ctx f1_group s2_0) /\
    (* IH_rest: after OK/OK, remaining block simulates *)
    (!v1 v2.
       R_ok (v1 with vs_inst_idx := 0) (v2 with vs_inst_idx := 0) ==>
       (?e. exec_block fuel ctx
              (bb with bb_instructions := FLAT (MAPi g1 bb.bb_instructions))
              (v1 with vs_inst_idx := j1_next) = Error e) \/
       lift_result R_ok R_term
         (exec_block fuel ctx
            (bb with bb_instructions := FLAT (MAPi g1 bb.bb_instructions))
            (v1 with vs_inst_idx := j1_next))
         (exec_block fuel ctx
            (bb with bb_instructions := FLAT (MAPi g2 bb.bb_instructions))
            (v2 with vs_inst_idx := j2_next)))
  ==>
    (?e. exec_block fuel ctx
           (bb with bb_instructions := FLAT (MAPi g1 bb.bb_instructions))
           s1 = Error e) \/
    lift_result R_ok R_term
      (exec_block fuel ctx
         (bb with bb_instructions := FLAT (MAPi g1 bb.bb_instructions)) s1)
      (exec_block fuel ctx
         (bb with bb_instructions := FLAT (MAPi g2 bb.bb_instructions)) s2)
Proof
  rpt gen_tac >> DISCH_TAC >>
  pop_assum (REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) >>
  qpat_x_assum `s1_0 = _` SUBST_ALL_TAC >>
  qpat_x_assum `s2_0 = _` SUBST_ALL_TAC >>
  qpat_x_assum `j1_next = _` SUBST_ALL_TAC >>
  qpat_x_assum `j2_next = _` SUBST_ALL_TAC
  \\ qabbrev_tac `bb1 = bb with bb_instructions :=
       FLAT (MAPi g1 bb.bb_instructions)`
  \\ qabbrev_tac `bb2 = bb with bb_instructions :=
       FLAT (MAPi g2 bb.bb_instructions)`
  (* Pre-derive bb_instructions equalities — avoids srw_ss() loops *)
  \\ `bb1.bb_instructions = FLAT (MAPi g1 bb.bb_instructions)` by
       (qunabbrev_tac `bb1` >> REWRITE_TAC abbrev_expand_thms)
  \\ `bb2.bb_instructions = FLAT (MAPi g2 bb.bb_instructions)` by
       (qunabbrev_tac `bb2` >> REWRITE_TAC abbrev_expand_thms)
  (* Case 1: f1 on s2 errors → derive error on s1 → exec_block error *)
  \\ Cases_on `?e. run_insts fuel ctx f1_group
       (s2 with vs_inst_idx := 0) = Error e`
  >- (
    DISJ1_TAC >> qpat_x_assum `?e. _` strip_assume_tac >>
    qpat_x_assum `lift_result _ _ (run_insts _ _ f1_group _)
      (run_insts _ _ f1_group _)` mp_tac >>
    qpat_assum `_ = Error e` (fn th => REWRITE_TAC[th]) >>
    strip_tac >> drule lift_result_error_left >> strip_tac >>
    qspecl_then [`R_ok`, `R_term`, `f1_group`, `fuel`, `ctx`, `bb1`,
      `s1 with vs_inst_idx := 0`, `j1`, `e'`] mp_tac exec_block_prefix_error >>
    qpat_assum `bb1.bb_instructions = _` (fn th => REWRITE_TAC[th]) >>
    REWRITE_TAC abbrev_expand_thms >> collapse_all_idx >>
    disch_then irule >> rpt conj_tac >> first_assum ACCEPT_TAC)
  (* Case 2: f1 on s2 does NOT error — so we have lift_result f1→f2 *)
  \\ `lift_result R_ok R_term
       (run_insts fuel ctx f1_group (s2 with vs_inst_idx := 0))
       (run_insts fuel ctx f2_group (s2 with vs_inst_idx := 0))` by (
    qpat_x_assum `_ \/ _` mp_tac >>
    qpat_x_assum `~_ ` (fn th => REWRITE_TAC [th]) >>
    simp_tac (srw_ss()) [])
  (* Combined: f1 s1 → f2 s2 *)
  \\ `lift_result R_ok R_term
       (run_insts fuel ctx f1_group (s1 with vs_inst_idx := 0))
       (run_insts fuel ctx f2_group (s2 with vs_inst_idx := 0))` by (
    irule lift_result_trans_proof >>
    rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
    qexists_tac `run_insts fuel ctx f1_group (s2 with vs_inst_idx := 0)` >>
    conj_tac >> first_assum ACCEPT_TAC)
  (* Case 2a: f1 on s1 gives OK → skip prefix on both sides, apply IH *)
  \\ Cases_on `?v1. run_insts fuel ctx f1_group
       (s1 with vs_inst_idx := 0) = OK v1`
  >- (
    qpat_x_assum `?v1. _` strip_assume_tac >>
    (* Extract OK v2 from combined lift_result *)
    `?v2. run_insts fuel ctx f2_group (s2 with vs_inst_idx := 0) = OK v2 /\
          R_ok v1 v2` by (
      qpat_assum `lift_result _ _ (run_insts _ _ f1_group _)
        (run_insts _ _ f2_group _)` mp_tac >>
      qpat_assum `_ = OK v1` (fn th => REWRITE_TAC[th]) >>
      Cases_on `run_insts fuel ctx f2_group (s2 with vs_inst_idx := 0)` >>
      simp_tac (srw_ss()) [lift_result_def]) >>
    (* Rewrite exec_block on both sides using skip_prefix *)
    qsuff_tac
      `(?e. exec_block fuel ctx bb1
              (v1 with vs_inst_idx := j1 + LENGTH f1_group) = Error e) \/
       lift_result R_ok R_term
         (exec_block fuel ctx bb1
            (v1 with vs_inst_idx := j1 + LENGTH f1_group))
         (exec_block fuel ctx bb2
            (v2 with vs_inst_idx := j2 + LENGTH f2_group))`
    >- (
      `exec_block fuel ctx bb1 s1 =
       exec_block fuel ctx bb1
         (v1 with vs_inst_idx := j1 + LENGTH f1_group)` by (
        qspecl_then [`f1_group`, `fuel`, `ctx`, `bb1`,
          `s1 with vs_inst_idx := 0`, `j1`, `v1`]
          mp_tac exec_block_skip_prefix >>
        qpat_assum `bb1.bb_instructions = _` (fn th => REWRITE_TAC[th]) >>
        REWRITE_TAC abbrev_expand_thms >> collapse_all_idx >>
        disch_then irule >> rpt conj_tac >> first_assum ACCEPT_TAC) >>
      `exec_block fuel ctx bb2 s2 =
       exec_block fuel ctx bb2
         (v2 with vs_inst_idx := j2 + LENGTH f2_group)` by (
        qspecl_then [`f2_group`, `fuel`, `ctx`, `bb2`,
          `s2 with vs_inst_idx := 0`, `j2`, `v2`]
          mp_tac exec_block_skip_prefix >>
        qpat_assum `bb2.bb_instructions = _` (fn th => REWRITE_TAC[th]) >>
        REWRITE_TAC abbrev_expand_thms >> collapse_all_idx >>
        disch_then irule >> rpt conj_tac >> first_assum ACCEPT_TAC) >>
      ntac 2 (pop_assum (fn th => REWRITE_TAC[th])) >>
      simp_tac std_ss []) >>
    (* Apply IH *)
    qspecl_then [`R_ok`, `R_term`, `v1`, `v2`, `0`] mp_tac R_ok_idx_change >>
    impl_tac >- (conj_tac >> first_assum ACCEPT_TAC) >>
    disch_tac >>
    first_x_assum drule >> simp_tac std_ss [])
  (* Case 2b: f1 on s1 NOT OK → chain prefix_fail_lift *)
  \\ `~(?v2. run_insts fuel ctx f2_group
       (s2 with vs_inst_idx := 0) = OK v2)` by (
    strip_tac >>
    qpat_x_assum `~(?v1. _ = OK v1)` mp_tac >> simp_tac (srw_ss()) [] >>
    (* From combined lift_result + OK v2, derive OK v1 *)
    qpat_assum `lift_result _ _ (run_insts _ _ f1_group _)
      (run_insts _ _ f2_group _)` mp_tac >>
    qpat_assum `_ = OK v2` (fn th => REWRITE_TAC[th]) >>
    Cases_on `run_insts fuel ctx f1_group (s1 with vs_inst_idx := 0)` >>
    simp_tac (srw_ss()) [lift_result_def])
  \\ DISJ2_TAC
  (* Chain: exec_block bb1 s1 ~> f1 s1_0 ~> f2 s2_0 ~> exec_block bb2 s2 *)
  \\ irule lift_result_trans_proof
  \\ conj_tac >- first_assum ACCEPT_TAC
  \\ conj_tac >- first_assum ACCEPT_TAC
  \\ qexists_tac `run_insts fuel ctx f2_group (s2 with vs_inst_idx := 0)`
  \\ conj_tac
  >- (
    irule lift_result_trans_proof >>
    conj_tac >- first_assum ACCEPT_TAC >>
    conj_tac >- first_assum ACCEPT_TAC >>
    qexists_tac `run_insts fuel ctx f1_group (s1 with vs_inst_idx := 0)` >>
    conj_tac
    >- (
      drule exec_block_prefix_fail_lift >>
      disch_then (qspecl_then [`f1_group`, `fuel`, `ctx`, `bb1`,
        `s1 with vs_inst_idx := 0`, `j1`] mp_tac) >>
      qpat_assum `bb1.bb_instructions = _`
        (fn th => REWRITE_TAC[th]) >>
      REWRITE_TAC abbrev_expand_thms >> collapse_all_idx >>
      disch_then irule >> rpt conj_tac >> first_assum ACCEPT_TAC)
    >> first_assum ACCEPT_TAC)
  \\ drule run_insts_lift_exec_block
  \\ disch_then (qspecl_then [`f2_group`, `fuel`, `ctx`, `bb2`,
       `s2 with vs_inst_idx := 0`, `j2`] mp_tac)
  \\ qpat_assum `bb2.bb_instructions = _`
       (fn th => REWRITE_TAC[th])
  \\ REWRITE_TAC abbrev_expand_thms \\ collapse_all_idx
  \\ disch_then irule \\ rpt conj_tac \\ first_assum ACCEPT_TAC
QED

(* ===== Main theorem: analysis_block_compare ===== *)
Theorem analysis_block_compare:
  !(R_ok : venom_state -> venom_state -> bool)
   (R_term : venom_state -> venom_state -> bool)
   (f1 : 'a -> instruction -> instruction list)
   (f2 : 'a -> instruction -> instruction list) bb
   (bottom : 'a) (result : 'a df_state).
    valid_state_rel R_ok R_term /\
    (!s1 s2 s3. R_ok s1 s2 /\ R_ok s2 s3 ==> R_ok s1 s3) /\
    (!s1 s2 s3. R_term s1 s2 /\ R_term s2 s3 ==> R_term s1 s3) /\
    inst_transform_structural f1 /\
    inst_transform_structural f2 /\
    EVERY inst_wf bb.bb_instructions /\
    (!i fuel ctx s.
       i < LENGTH bb.bb_instructions ==>
       let inst = EL i bb.bb_instructions in
       let v = df_at bottom result bb.bb_label i in
       (?e. run_insts fuel ctx (f1 v inst) s = Error e) \/
       lift_result R_ok R_term
         (run_insts fuel ctx (f1 v inst) s)
         (run_insts fuel ctx (f2 v inst) s)) /\
    (!inst x.
       MEM inst (FLAT (MAPi (\idx i. f1 (df_at bottom result bb.bb_label idx) i)
                            bb.bb_instructions)) /\
       MEM (Var x) inst.inst_operands ==>
       !s1 s2. R_ok s1 s2 ==> lookup_var x s1 = lookup_var x s2)
  ==>
    !fuel ctx s.
      s.vs_inst_idx = 0 ==>
      (?e. exec_block fuel ctx
             (analysis_block_transform bottom result f1 bb) s = Error e) \/
      lift_result R_ok R_term
        (exec_block fuel ctx (analysis_block_transform bottom result f1 bb) s)
        (exec_block fuel ctx (analysis_block_transform bottom result f2 bb) s)
Proof
  rpt strip_tac
  \\ simp[analysis_block_transform_def]
  \\ qabbrev_tac `g1 = \idx inst. f1 (df_at bottom result bb.bb_label idx) inst`
  \\ qabbrev_tac `g2 = \idx inst. f2 (df_at bottom result bb.bb_label idx) inst`
  \\ qpat_x_assum `inst_transform_structural f1`
    (fn th => let val th' = REWRITE_RULE [inst_transform_structural_def] th
                  val cs = CONJUNCTS th'
              in MAP_EVERY ASSUME_TAC cs end)
  \\ qpat_x_assum `inst_transform_structural f2`
    (fn th => let val th' = REWRITE_RULE [inst_transform_structural_def] th
                  val cs = CONJUNCTS th'
              in MAP_EVERY ASSUME_TAC cs end)
  \\ qsuff_tac
    `!n fuel ctx s1 s2 i.
       R_ok (s1 with vs_inst_idx := 0) (s2 with vs_inst_idx := 0) /\
       n = LENGTH bb.bb_instructions - i /\
       i <= LENGTH bb.bb_instructions /\
       s1.vs_inst_idx =
         LENGTH (FLAT (TAKE i (MAPi g1 bb.bb_instructions))) /\
       s2.vs_inst_idx =
         LENGTH (FLAT (TAKE i (MAPi g2 bb.bb_instructions)))
       ==>
       (?e. exec_block fuel ctx
              (bb with bb_instructions := FLAT (MAPi g1 bb.bb_instructions))
              s1 = Error e) \/
       lift_result R_ok R_term
         (exec_block fuel ctx
            (bb with bb_instructions := FLAT (MAPi g1 bb.bb_instructions)) s1)
         (exec_block fuel ctx
            (bb with bb_instructions := FLAT (MAPi g2 bb.bb_instructions)) s2)`
  >- (
    disch_then (qspecl_then
      [`LENGTH bb.bb_instructions`, `fuel`, `ctx`, `s`, `s`, `0`] mp_tac) >>
    simp[TAKE_0] >>
    impl_tac >- (irule vsr_R_ok_refl >> metis_tac[]) >> simp[])
  \\ completeInduct_on `n` \\ rpt strip_tac
  \\ Cases_on `i < LENGTH bb.bb_instructions`
  >| [
    ALL_TAC,
    (* === Base case: i = LENGTH ==> past end ==> Error === *)
    `i = LENGTH bb.bb_instructions` by decide_tac >>
    pop_assum SUBST_ALL_TAC >>
    DISJ1_TAC >>
    `TAKE (LENGTH bb.bb_instructions) (MAPi g1 bb.bb_instructions) =
     MAPi g1 bb.bb_instructions` by
      simp[TAKE_LENGTH_ID, indexedListsTheory.LENGTH_MAPi] >>
    ONCE_REWRITE_TAC[venomExecSemanticsTheory.exec_block_def] >>
    simp_tac std_ss [get_instruction_def] >>
    simp[]
  ]
  (* === Inductive step: i < LENGTH === *)
  \\ qabbrev_tac `inst = EL i bb.bb_instructions`
  \\ qabbrev_tac `v = df_at bottom result bb.bb_label i`
  \\ qabbrev_tac `j1 = LENGTH (FLAT (TAKE i (MAPi g1 bb.bb_instructions)))`
  \\ qabbrev_tac `j2 = LENGTH (FLAT (TAKE i (MAPi g2 bb.bb_instructions)))`
  \\ `g1 i inst = f1 v inst` by simp[Abbr `g1`, Abbr `v`, Abbr `inst`]
  \\ `g2 i inst = f2 v inst` by simp[Abbr `g2`, Abbr `v`, Abbr `inst`]
  \\ qabbrev_tac `s1_0 = s1 with vs_inst_idx := 0`
  \\ qabbrev_tac `s2_0 = s2 with vs_inst_idx := 0`
  \\ `R_ok s1_0 s2_0` by simp[Abbr `s1_0`, Abbr `s2_0`]
  (* Indexing facts *)
  \\ `!k. k < LENGTH (f1 v inst) ==>
       EL (j1 + k) (FLAT (MAPi g1 bb.bb_instructions)) =
       EL k (f1 v inst)` by (
    rpt strip_tac >> qunabbrev_tac `j1` >>
    `EL (LENGTH (FLAT (TAKE i (MAPi g1 bb.bb_instructions))) + k)
         (FLAT (MAPi g1 bb.bb_instructions)) =
      EL k (g1 i (EL i bb.bb_instructions))`
       by (irule EL_FLAT_MAPi >> simp[]) >>
    qunabbrev_tac `inst` >> simp[])
  \\ `!k. k < LENGTH (f2 v inst) ==>
       EL (j2 + k) (FLAT (MAPi g2 bb.bb_instructions)) =
       EL k (f2 v inst)` by (
    rpt strip_tac >> qunabbrev_tac `j2` >>
    `EL (LENGTH (FLAT (TAKE i (MAPi g2 bb.bb_instructions))) + k)
         (FLAT (MAPi g2 bb.bb_instructions)) =
      EL k (g2 i (EL i bb.bb_instructions))`
       by (irule EL_FLAT_MAPi >> simp[]) >>
    qunabbrev_tac `inst` >> simp[])
  \\ `j1 + LENGTH (f1 v inst) <=
   LENGTH (FLAT (MAPi g1 bb.bb_instructions))` by (
    qunabbrev_tac `j1` >>
    qpat_assum `g1 i inst = f1 v inst`
      (fn eq => REWRITE_TAC[SYM eq]) >>
    qunabbrev_tac `inst` >>
    irule FLAT_MAPi_offset_bound >> simp[])
  \\ `j2 + LENGTH (f2 v inst) <=
   LENGTH (FLAT (MAPi g2 bb.bb_instructions))` by (
    qunabbrev_tac `j2` >>
    qpat_assum `g2 i inst = f2 v inst`
      (fn eq => REWRITE_TAC[SYM eq]) >>
    qunabbrev_tac `inst` >>
    irule FLAT_MAPi_offset_bound >> simp[])
  (* Per-group comparison *)
  \\ `!fuel' ctx' s'.
     (?e. run_insts fuel' ctx' (f1 v inst) s' = Error e) \/
     lift_result R_ok R_term (run_insts fuel' ctx' (f1 v inst) s')
       (run_insts fuel' ctx' (f2 v inst) s')` by (
    rpt gen_tac >>
    qpat_x_assum `!i fuel ctx s. i < LENGTH bb.bb_instructions ==> _`
      (fn th => mp_tac (Q.SPECL [`i`, `fuel'`, `ctx'`, `s'`] th) >>
                ASSUME_TAC th) >>
    impl_tac >- simp[] >>
    simp_tac std_ss [LET_THM] >>
    metis_tac[markerTheory.Abbrev_def])
  (* R-preservation *)
  \\ `lift_result R_ok R_term
     (run_insts fuel ctx (f1 v inst) s1_0)
     (run_insts fuel ctx (f1 v inst) s2_0)` by (
    irule run_insts_preserves_R >>
    rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
    rpt strip_tac >>
    qpat_assum `!inst' x. MEM inst' (FLAT _) /\ _ ==> _`
      (qspecl_then [`inst'`, `x`] mp_tac) >>
    impl_tac >- (
      conj_tac >- (
        simp[MEM_FLAT, indexedListsTheory.MEM_MAPi] >>
        qexists_tac `f1 v inst` >>
        conj_tac >- (qexists_tac `i` >>
          simp[Abbr `g1`, Abbr `v`, Abbr `inst`]) >>
        first_assum ACCEPT_TAC) >>
      first_assum ACCEPT_TAC) >>
    disch_then irule >> first_assum ACCEPT_TAC)
  (* IH for SUC i *)
  \\ `!v1 v2.
     R_ok (v1 with vs_inst_idx := 0) (v2 with vs_inst_idx := 0) ==>
     (?e. exec_block fuel ctx
            (bb with bb_instructions := FLAT (MAPi g1 bb.bb_instructions))
            (v1 with vs_inst_idx :=
               LENGTH (FLAT (TAKE (SUC i) (MAPi g1 bb.bb_instructions)))) =
          Error e) \/
     lift_result R_ok R_term
       (exec_block fuel ctx
          (bb with bb_instructions := FLAT (MAPi g1 bb.bb_instructions))
          (v1 with vs_inst_idx :=
             LENGTH (FLAT (TAKE (SUC i) (MAPi g1 bb.bb_instructions)))))
       (exec_block fuel ctx
          (bb with bb_instructions := FLAT (MAPi g2 bb.bb_instructions))
          (v2 with vs_inst_idx :=
             LENGTH (FLAT (TAKE (SUC i) (MAPi g2 bb.bb_instructions)))))` by (
    rpt strip_tac >>
    qpat_x_assum `!m. m < n ==> _`
      (qspec_then `LENGTH bb.bb_instructions - SUC i` mp_tac) >>
    impl_tac >- decide_tac >>
    disch_then (qspecl_then [`fuel`, `ctx`,
      `v1 with vs_inst_idx :=
         LENGTH (FLAT (TAKE (SUC i) (MAPi g1 bb.bb_instructions)))`,
      `v2 with vs_inst_idx :=
         LENGTH (FLAT (TAKE (SUC i) (MAPi g2 bb.bb_instructions)))`,
      `SUC i`] irule) >>
    simp_tac (srw_ss()) [] >>
    rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >> decide_tac)
  (* SUC i offset facts *)
  \\ `LENGTH (FLAT (TAKE (SUC i) (MAPi g1 bb.bb_instructions))) =
   j1 + LENGTH (f1 v inst)` by (
    qunabbrev_tac `j1` >>
    `LENGTH (FLAT (TAKE (SUC i) (MAPi g1 bb.bb_instructions))) =
     LENGTH (FLAT (TAKE i (MAPi g1 bb.bb_instructions))) +
       LENGTH (g1 i (EL i bb.bb_instructions))`
      by (irule FLAT_MAPi_offset_SUC >> simp[]) >>
    simp[Abbr `inst`])
  \\ `LENGTH (FLAT (TAKE (SUC i) (MAPi g2 bb.bb_instructions))) =
   j2 + LENGTH (f2 v inst)` by (
    qunabbrev_tac `j2` >>
    `LENGTH (FLAT (TAKE (SUC i) (MAPi g2 bb.bb_instructions))) =
     LENGTH (FLAT (TAKE i (MAPi g2 bb.bb_instructions))) +
       LENGTH (g2 i (EL i bb.bb_instructions))`
      by (irule FLAT_MAPi_offset_SUC >> simp[]) >>
    simp[Abbr `inst`])
  (* Rewrite IH from TAKE(SUC i) form to j+len form *)
  \\ `!v1 v2.
     R_ok (v1 with vs_inst_idx := 0) (v2 with vs_inst_idx := 0) ==>
     (?e. exec_block fuel ctx
            (bb with bb_instructions := FLAT (MAPi g1 bb.bb_instructions))
            (v1 with vs_inst_idx := j1 + LENGTH (f1 v inst)) = Error e) \/
     lift_result R_ok R_term
       (exec_block fuel ctx
          (bb with bb_instructions := FLAT (MAPi g1 bb.bb_instructions))
          (v1 with vs_inst_idx := j1 + LENGTH (f1 v inst)))
       (exec_block fuel ctx
          (bb with bb_instructions := FLAT (MAPi g2 bb.bb_instructions))
          (v2 with vs_inst_idx := j2 + LENGTH (f2 v inst)))` by (
    rpt strip_tac >>
    qpat_x_assum `!a b. R_ok _ _ ==> _ \/ lift_result _ _ _ _`
      (qspecl_then [`v1`, `v2`] mp_tac) >>
    impl_tac >- first_assum ACCEPT_TAC >>
    qpat_assum `LENGTH (FLAT (TAKE (SUC i) (MAPi g1 _))) = _`
      (fn th => REWRITE_TAC [th]) >>
    qpat_assum `LENGTH (FLAT (TAKE (SUC i) (MAPi g2 _))) = _`
      (fn th => REWRITE_TAC [th]) >>
    simp_tac std_ss [])
  (* Kill OLD IH (TAKE SUC i form) — keep rewritten IH (j+len form) *)
  \\ qpat_x_assum `!v1 v2. R_ok _ _ ==> _ \/ lift_result _ _
       (exec_block _ _ _ (v1 with vs_inst_idx := LENGTH (FLAT (TAKE (SUC i) _))))
       _` kall_tac
  (* Three-way case split *)
  (* === Terminator case === *)
  \\ Cases_on `is_terminator inst.inst_opcode`
  >- (
    qpat_x_assum `!aa bb. is_terminator _ ==> ?cc. f1 _ _ = [_] /\ _`
      (qspecl_then [`v`, `inst`] mp_tac) >>
    impl_tac >- first_assum ACCEPT_TAC >> strip_tac >>
    qpat_x_assum `!aa bb. is_terminator _ ==> ?cc. f2 _ _ = [_] /\ _`
      (qspecl_then [`v`, `inst`] mp_tac) >>
    impl_tac >- first_assum ACCEPT_TAC >> strip_tac >>
    rename1 `f1 v inst = [inst1]` >> rename1 `f2 v inst = [inst2]` >>
    SUBGOAL_THEN ``(?e. step_inst fuel ctx inst1 s2_0 = Error e) \/
       lift_result R_ok R_term (step_inst fuel ctx inst1 s2_0)
         (step_inst fuel ctx inst2 s2_0)`` ASSUME_TAC
    >- (first_x_assum (qspecl_then [`fuel`, `ctx`, `s2_0`] mp_tac) >>
        qpat_assum `f1 v inst = _` (fn th => REWRITE_TAC[th]) >>
        qpat_assum `f2 v inst = _` (fn th => REWRITE_TAC[th]) >>
        REWRITE_TAC[run_insts_singleton]) >>
    `lift_result R_ok R_term (step_inst fuel ctx inst1 s1_0)
       (step_inst fuel ctx inst1 s2_0)` by (
      qpat_assum `lift_result _ _ (run_insts _ _ (f1 v inst) s1_0) _` mp_tac >>
      qpat_assum `f1 v inst = _` (fn th => REWRITE_TAC[th]) >>
      REWRITE_TAC[run_insts_singleton]) >>
    `j1 < LENGTH (FLAT (MAPi g1 bb.bb_instructions))` by (
      qpat_assum `j1 + LENGTH (f1 v inst) <= _` mp_tac >>
      qpat_assum `f1 v inst = _` (fn th => REWRITE_TAC[th]) >>
      simp_tac (srw_ss()) [] >> decide_tac) >>
    `j2 < LENGTH (FLAT (MAPi g2 bb.bb_instructions))` by (
      qpat_assum `j2 + LENGTH (f2 v inst) <= _` mp_tac >>
      qpat_assum `f2 v inst = _` (fn th => REWRITE_TAC[th]) >>
      simp_tac (srw_ss()) [] >> decide_tac) >>
    `EL j1 (FLAT (MAPi g1 bb.bb_instructions)) = inst1` by (
      qpat_assum `!k. k < LENGTH (f1 v inst) ==> _ = EL k (f1 v inst)`
        (qspec_then `0` mp_tac) >>
      qpat_assum `f1 v inst = _` (fn th => REWRITE_TAC[th]) >>
      simp_tac (srw_ss()) []) >>
    `EL j2 (FLAT (MAPi g2 bb.bb_instructions)) = inst2` by (
      qpat_assum `!k. k < LENGTH (f2 v inst) ==> _ = EL k (f2 v inst)`
        (qspec_then `0` mp_tac) >>
      qpat_assum `f2 v inst = _` (fn th => REWRITE_TAC[th]) >>
      simp_tac (srw_ss()) []) >>
    qspecl_then [`R_ok`, `R_term`, `inst1`, `inst2`,
      `s1`, `s2`, `s1_0`, `s2_0`, `j1`, `j2`,
      `bb`, `g1`, `g2`, `fuel`, `ctx`]
      mp_tac abc_terminator_case >>
    (impl_tac >- (
      rpt conj_tac >>
      TRY (qunabbrev_tac `s1_0` >> REFL_TAC) >>
      TRY (qunabbrev_tac `s2_0` >> REFL_TAC) >>
      TRY (qunabbrev_tac `j1` >> REFL_TAC) >>
      TRY (qunabbrev_tac `j2` >> REFL_TAC) >>
      TRY (first_assum ACCEPT_TAC) >>
      first_assum MATCH_ACCEPT_TAC)) >>
    simp_tac std_ss [])
  (* === INVOKE case === *)
  \\ Cases_on `inst.inst_opcode = INVOKE`
  >- (
    qpat_x_assum `!aa bb. _ = INVOKE ==> ?cc. f1 _ _ = [_] /\ _`
      (qspecl_then [`v`, `inst`] mp_tac) >>
    (impl_tac >- first_assum ACCEPT_TAC) >> strip_tac >>
    qpat_x_assum `!aa bb. _ = INVOKE ==> ?cc. f2 _ _ = [_] /\ _`
      (qspecl_then [`v`, `inst`] mp_tac) >>
    (impl_tac >- first_assum ACCEPT_TAC) >> strip_tac >>
    rename1 `f1 v inst = [inst1]` >> rename1 `f2 v inst = [inst2]` >>
    SUBGOAL_THEN ``(?e. step_inst fuel ctx inst1 s2_0 = Error e) \/
       lift_result R_ok R_term (step_inst fuel ctx inst1 s2_0)
         (step_inst fuel ctx inst2 s2_0)`` ASSUME_TAC
    >- (first_x_assum (qspecl_then [`fuel`, `ctx`, `s2_0`] mp_tac) >>
        qpat_assum `f1 v inst = _` (fn th => REWRITE_TAC[th]) >>
        qpat_assum `f2 v inst = _` (fn th => REWRITE_TAC[th]) >>
        REWRITE_TAC[run_insts_singleton]) >>
    `lift_result R_ok R_term (step_inst fuel ctx inst1 s1_0)
       (step_inst fuel ctx inst1 s2_0)` by (
      qpat_assum `lift_result _ _ (run_insts _ _ (f1 v inst) s1_0) _` mp_tac >>
      qpat_assum `f1 v inst = _` (fn th => REWRITE_TAC[th]) >>
      REWRITE_TAC[run_insts_singleton]) >>
    `j1 < LENGTH (FLAT (MAPi g1 bb.bb_instructions))` by (
      qpat_assum `j1 + LENGTH (f1 v inst) <= _` mp_tac >>
      qpat_assum `f1 v inst = _` (fn th => REWRITE_TAC[th]) >>
      REWRITE_TAC[listTheory.LENGTH] >> decide_tac) >>
    `j2 < LENGTH (FLAT (MAPi g2 bb.bb_instructions))` by (
      qpat_assum `j2 + LENGTH (f2 v inst) <= _` mp_tac >>
      qpat_assum `f2 v inst = _` (fn th => REWRITE_TAC[th]) >>
      REWRITE_TAC[listTheory.LENGTH] >> decide_tac) >>
    `EL j1 (FLAT (MAPi g1 bb.bb_instructions)) = inst1` by (
      qpat_assum `!k. k < LENGTH (f1 v inst) ==> _ = EL k (f1 v inst)`
        (qspec_then `0` mp_tac) >>
      qpat_assum `f1 v inst = _` (fn th => REWRITE_TAC[th]) >>
      REWRITE_TAC[listTheory.LENGTH] >> simp_tac (srw_ss()) []) >>
    `EL j2 (FLAT (MAPi g2 bb.bb_instructions)) = inst2` by (
      qpat_assum `!k. k < LENGTH (f2 v inst) ==> _ = EL k (f2 v inst)`
        (qspec_then `0` mp_tac) >>
      qpat_assum `f2 v inst = _` (fn th => REWRITE_TAC[th]) >>
      REWRITE_TAC[listTheory.LENGTH] >> simp_tac (srw_ss()) []) >>
    (* Derive j + 1 = SUC j for applying abc_invoke_case *)
    `LENGTH (f1 v inst) = 1` by (
      qpat_assum `f1 v inst = [inst1]` (fn th => REWRITE_TAC[th]) >>
      REWRITE_TAC[listTheory.LENGTH] >> decide_tac) >>
    `LENGTH (f2 v inst) = 1` by (
      qpat_assum `f2 v inst = [inst2]` (fn th => REWRITE_TAC[th]) >>
      REWRITE_TAC[listTheory.LENGTH] >> decide_tac) >>
    qspecl_then [`R_ok`, `R_term`, `inst1`, `inst2`,
      `s1`, `s2`, `s1_0`, `s2_0`, `j1`, `j2`,
      `j1 + LENGTH (f1 v inst)`, `j2 + LENGTH (f2 v inst)`,
      `bb`, `g1`, `g2`, `fuel`, `ctx`,
      `\r1 r2. (?e. r1 = Error e) \/ lift_result R_ok R_term r1 r2`]
      mp_tac abc_invoke_case >>
    (impl_tac >- (
      rpt conj_tac >>
      TRY (qunabbrev_tac `s1_0` >> REFL_TAC) >>
      TRY (qunabbrev_tac `s2_0` >> REFL_TAC) >>
      TRY (qunabbrev_tac `j1` >> REFL_TAC) >>
      TRY (qunabbrev_tac `j2` >> REFL_TAC) >>
      TRY decide_tac >>
      TRY (first_assum ACCEPT_TAC) >>
      first_assum MATCH_ACCEPT_TAC)) >>
    simp_tac std_ss [])
  (* === Normal case: derive per-group comparison for specific fuel/ctx/s === *)
  \\ `(?e. run_insts fuel ctx (f1 v inst) s2_0 = Error e) \/
       lift_result R_ok R_term (run_insts fuel ctx (f1 v inst) s2_0)
         (run_insts fuel ctx (f2 v inst) s2_0)` by
    first_assum (qspecl_then [`fuel`, `ctx`, `s2_0`] ACCEPT_TAC)
  (* Derive EVERY predicates for f1 and f2 groups *)
  \\ `EVERY (\i'. ~is_terminator i'.inst_opcode /\ i'.inst_opcode <> INVOKE)
       (f1 v inst)` by (
    qpat_x_assum `!v' inst'. ~is_terminator _ /\ _ <> INVOKE ==>
      EVERY _ (f1 _ _)`
      (qspecl_then [`v`, `inst`] mp_tac) >>
    (impl_tac >- (conj_tac >> first_assum ACCEPT_TAC)) >>
    simp_tac std_ss [])
  \\ `EVERY (\i'. ~is_terminator i'.inst_opcode /\ i'.inst_opcode <> INVOKE)
       (f2 v inst)` by (
    qpat_x_assum `!v' inst'. ~is_terminator _ /\ _ <> INVOKE ==>
      EVERY _ (f2 _ _)`
      (qspecl_then [`v`, `inst`] mp_tac) >>
    (impl_tac >- (conj_tac >> first_assum ACCEPT_TAC)) >>
    simp_tac std_ss [])
  \\ qspecl_then [`R_ok`, `R_term`, `f1 v inst`, `f2 v inst`,
       `s1`, `s2`, `s1_0`, `s2_0`, `j1`, `j2`, `bb`, `g1`, `g2`,
       `fuel`, `ctx`, `j1 + LENGTH (f1 v inst)`,
       `j2 + LENGTH (f2 v inst)`]
       mp_tac abc_normal_case
  \\ simp_tac std_ss []
  \\ (impl_tac >- (
      rpt conj_tac >>
      TRY (qunabbrev_tac `s1_0` >> REFL_TAC) >>
      TRY (qunabbrev_tac `s2_0` >> REFL_TAC) >>
      TRY (qunabbrev_tac `j1` >> REFL_TAC) >>
      TRY (qunabbrev_tac `j2` >> REFL_TAC) >>
      TRY (first_assum ACCEPT_TAC) >>
      first_assum MATCH_ACCEPT_TAC))
  \\ simp_tac std_ss []
QED


(* ===== Compare variant: two transforms at function level ===== *)

Triviality block_sim_function_compare_ind_step:
  !(R_ok : venom_state -> venom_state -> bool)
   (R_term : venom_state -> venom_state -> bool) bt1 bt2 fn fuel.
    valid_state_rel R_ok R_term /\
    (!s1 s2. R_ok s1 s2 ==> R_term s1 s2) /\
    (!s1 s2. R_ok s1 s2 ==> (s1.vs_halted <=> s2.vs_halted) /\
       s1.vs_current_bb = s2.vs_current_bb /\
       s1.vs_inst_idx = s2.vs_inst_idx) /\
    (!s1 s2 s3. R_ok s1 s2 /\ R_ok s2 s3 ==> R_ok s1 s3) /\
    (!s1 s2 s3. R_term s1 s2 /\ R_term s2 s3 ==> R_term s1 s3) /\
    (!bb. (bt1 bb).bb_label = bb.bb_label) /\
    (!bb. (bt2 bb).bb_label = bb.bb_label) /\
    (!fuel ctx bb s1 s2.
       MEM bb fn.fn_blocks /\ R_ok s1 s2 ==>
       lift_result R_ok R_term (exec_block fuel ctx (bt1 bb) s1)
                                (exec_block fuel ctx (bt1 bb) s2)) /\
    (!lbl bb. lookup_block lbl fn.fn_blocks = SOME bb ==>
      !fuel ctx s.
        s.vs_inst_idx = 0 ==>
        (?e. exec_block fuel ctx (bt1 bb) s = Error e) \/
        lift_result R_ok R_term (exec_block fuel ctx (bt1 bb) s)
                                 (exec_block fuel ctx (bt2 bb) s)) /\
    (!ctx s1 s2. R_ok s1 s2 /\ s1.vs_inst_idx = 0 ==>
       (?e. run_blocks fuel ctx (function_map_transform bt1 fn) s1 = Error e) \/
       lift_result R_ok R_term
         (run_blocks fuel ctx (function_map_transform bt1 fn) s1)
         (run_blocks fuel ctx (function_map_transform bt2 fn) s2))
  ==>
    !ctx s1 s2. R_ok s1 s2 /\ s1.vs_inst_idx = 0 ==>
       (?e. run_blocks (SUC fuel) ctx
              (function_map_transform bt1 fn) s1 = Error e) \/
       lift_result R_ok R_term
         (run_blocks (SUC fuel) ctx (function_map_transform bt1 fn) s1)
         (run_blocks (SUC fuel) ctx (function_map_transform bt2 fn) s2)
Proof
  rpt gen_tac >> strip_tac >> rpt gen_tac >> strip_tac >>
  `s1.vs_current_bb = s2.vs_current_bb` by metis_tac[] >>
  `s2.vs_inst_idx = 0` by metis_tac[] >>
  ONCE_REWRITE_TAC[run_blocks_def] >>
  simp[function_map_transform_def, lookup_block_map_proof] >>
  Cases_on `lookup_block s2.vs_current_bb fn.fn_blocks`
  >- gvs[lift_result_def]
  >>
  rename1 `lookup_block _ _ = SOME bb` >>
  `MEM bb fn.fn_blocks` by metis_tac[venomExecProofsTheory.lookup_block_MEM] >>
  `lift_result R_ok R_term (exec_block fuel ctx (bt1 bb) s1)
                            (exec_block fuel ctx (bt1 bb) s2)` by metis_tac[] >>
  `(?e. exec_block fuel ctx (bt1 bb) s2 = Error e) \/
   lift_result R_ok R_term (exec_block fuel ctx (bt1 bb) s2)
     (exec_block fuel ctx (bt2 bb) s2)` by (
    qpat_assum `!lbl bb. lookup_block _ _ = SOME _ ==> _`
      (qspecl_then [`s2.vs_current_bb`, `bb`] mp_tac) >> simp[]) >>
  Cases_on `?e. exec_block fuel ctx (bt1 bb) s2 = Error e`
  >- (fs[] >> imp_res_tac lift_result_error_left >> gvs[])
  >>
  `lift_result R_ok R_term (exec_block fuel ctx (bt1 bb) s2)
                            (exec_block fuel ctx (bt2 bb) s2)` by metis_tac[] >>
  `lift_result R_ok R_term (exec_block fuel ctx (bt1 bb) s1)
                            (exec_block fuel ctx (bt2 bb) s2)` by (
    irule lift_result_trans_proof >>
    conj_tac >- first_assum ACCEPT_TAC >>
    conj_tac >- first_assum ACCEPT_TAC >>
    qexists_tac `exec_block fuel ctx (bt1 bb) s2` >>
    conj_tac >> first_assum ACCEPT_TAC) >>
  Cases_on `exec_block fuel ctx (bt1 bb) s1` >>
  Cases_on `exec_block fuel ctx (bt2 bb) s2` >>
  gvs[lift_result_def]
  >>
  rename1 `R_ok v1 v2` >>
  Cases_on `v1.vs_halted`
  >- (
    `v2.vs_halted` by metis_tac[] >> simp[lift_result_def] >>
    metis_tac[])
  >>
  `~v2.vs_halted` by metis_tac[] >> simp[lift_result_def] >>
  gvs[function_map_transform_def] >>
  `v1.vs_inst_idx = 0 /\ v2.vs_inst_idx = 0` by
    metis_tac[venomExecProofsTheory.exec_block_OK_inst_idx_0] >>
  qpat_assum `!ctx' s1' s2'. R_ok s1' s2' /\ _ ==> _`
    (qspecl_then [`ctx`, `v1`, `v2`] mp_tac) >>
  simp[]
QED

Theorem block_sim_function_compare:
  !(R_ok : venom_state -> venom_state -> bool)
   (R_term : venom_state -> venom_state -> bool) bt1 bt2 fn.
    valid_state_rel R_ok R_term /\
    (!s1 s2 s3. R_ok s1 s2 /\ R_ok s2 s3 ==> R_ok s1 s3) /\
    (!s1 s2 s3. R_term s1 s2 /\ R_term s2 s3 ==> R_term s1 s3) /\
    (!bb. (bt1 bb).bb_label = bb.bb_label) /\
    (!bb. (bt2 bb).bb_label = bb.bb_label) /\
    (!lbl bb. lookup_block lbl fn.fn_blocks = SOME bb ==>
      !fuel ctx s.
        s.vs_inst_idx = 0 ==>
        (?e. exec_block fuel ctx (bt1 bb) s = Error e) \/
        lift_result R_ok R_term (exec_block fuel ctx (bt1 bb) s)
                                 (exec_block fuel ctx (bt2 bb) s)) /\
    (!bb inst x.
       MEM bb (MAP bt1 fn.fn_blocks) /\ MEM inst bb.bb_instructions /\
       MEM (Var x) inst.inst_operands ==>
       !s1 s2. R_ok s1 s2 ==> lookup_var x s1 = lookup_var x s2)
  ==>
    !fuel ctx s.
      s.vs_inst_idx = 0 ==>
      (?e. run_blocks fuel ctx (function_map_transform bt1 fn) s = Error e) \/
      lift_result R_ok R_term
        (run_blocks fuel ctx (function_map_transform bt1 fn) s)
        (run_blocks fuel ctx (function_map_transform bt2 fn) s)
Proof
  rpt gen_tac >> strip_tac >>
  `!s1 s2. R_ok s1 s2 ==> R_term s1 s2` by
    (rpt strip_tac >> irule vsr_R_ok_R_term >> metis_tac[]) >>
  `!s1 s2. R_ok s1 s2 ==> (s1.vs_halted <=> s2.vs_halted) /\
     s1.vs_current_bb = s2.vs_current_bb /\
     s1.vs_inst_idx = s2.vs_inst_idx` by
    (rpt strip_tac >> imp_res_tac
      (REWRITE_RULE [GSYM AND_IMP_INTRO] vsr_R_ok_fields)) >>
  `!fuel ctx bb s1 s2.
     MEM bb fn.fn_blocks /\ R_ok s1 s2 ==>
     lift_result R_ok R_term (exec_block fuel ctx (bt1 bb) s1)
                              (exec_block fuel ctx (bt1 bb) s2)` by (
    rpt strip_tac >>
    qspecl_then [`R_ok`, `R_term`, `function_map_transform bt1 fn`]
      mp_tac (cj 1 exec_block_preserves_R_proof) >>
    simp[function_map_transform_def] >>
    impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC) >>
    disch_then (qspecl_then [`fuel`, `ctx`, `bt1 bb`, `s1`, `s2`] mp_tac) >>
    impl_tac >- (simp[listTheory.MEM_MAP] >> metis_tac[]) >>
    simp[]) >>
  qsuff_tac
    `!fuel ctx s1 s2. R_ok s1 s2 /\ s1.vs_inst_idx = 0 ==>
       (?e. run_blocks fuel ctx (function_map_transform bt1 fn) s1 = Error e) \/
       lift_result R_ok R_term
         (run_blocks fuel ctx (function_map_transform bt1 fn) s1)
         (run_blocks fuel ctx (function_map_transform bt2 fn) s2)`
  >- (rpt strip_tac >>
      first_x_assum (qspecl_then [`fuel`, `ctx`, `s`, `s`] mp_tac) >>
      impl_tac >- (conj_tac >- (irule vsr_R_ok_refl >> metis_tac[]) >> simp[]) >>
      simp[]) >>
  Induct_on `fuel`
  >- (rw[] >> simp[run_blocks_def, function_map_transform_def, lift_result_def])
  >>
  rpt strip_tac >>
  irule (SIMP_RULE (srw_ss()) [] block_sim_function_compare_ind_step) >>
  rpt (first_assum (fn th => EXISTS_TAC (rand (concl th)) >> ACCEPT_TAC th)
       ORELSE conj_tac ORELSE first_assum ACCEPT_TAC)
QED
