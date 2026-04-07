(*
 * Lower DLOAD Pass -- Simulation (block-level and function-level)
 *
 * Builds on lowerDloadProofs (per-instruction helpers) and
 * lowerDloadClassify (step_inst_base classification).
 *)

Theory lowerDloadSim
Ancestors
  lowerDloadProofs lowerDloadClassify lowerDloadDefs
  stateEquiv venomExecSemantics passSimulationDefs
  venomExecProps venomInst venomState venomWf
  venomInstProps analysisSimDefs instIdxIndep
  finite_map words list rich_list pred_set arithmetic

(* ===== run_insts simulation ===== *)

(* Shared IH finisher tactic for run_insts induction.
   After establishing ld_ok vars s1_mid s2_mid /\ code_layout_valid s2_mid,
   applies the IH and discharges all MEM-quantified subgoals. *)
val ld_finish_ih =
  first_x_assum irule >>
  rpt conj_tac >> TRY (rpt strip_tac >> res_tac >> gvs[] >> NO_TAC) >>
  qexists_tac `s1_mid` >> gvs[] >>
  rpt conj_tac >> rpt strip_tac >> res_tac >> gvs[];

(* Shared tactic: establish ld_dload_safe preconditions from fn-level props.
   Used by both OK and non-OK branches of ld_block_sim. *)
val ld_dload_safe_tac =
  rpt conj_tac >> TRY (rpt strip_tac >> res_tac >> gvs[] >> NO_TAC)
  >- (rpt strip_tac >>
      `MEM inst bb.bb_instructions` by metis_tac[MEM_APPEND, MEM] >>
      fs[ld_dload_safe_def] >> res_tac >> gvs[] >>
      fs[code_layout_valid_def] >> simp[])
  >- (rpt strip_tac >>
      `MEM inst bb.bb_instructions` by metis_tac[MEM_APPEND, MEM] >>
      fs[ld_dload_safe_def] >> res_tac >> gvs[] >>
      fs[code_layout_valid_def] >> simp[])
  >- (rpt strip_tac >>
      `MEM inst bb.bb_instructions` by metis_tac[MEM_APPEND, MEM] >>
      fs[ld_dload_safe_def] >> metis_tac[])
  >- (rpt strip_tac >>
      `MEM inst bb.bb_instructions` by metis_tac[MEM_APPEND, MEM] >>
      fs[ld_dload_safe_def] >> metis_tac[])
  >- (rpt strip_tac >>
      `MEM inst bb.bb_instructions` by metis_tac[MEM_APPEND, MEM] >>
      fs[ld_dload_safe_def] >>
      first_x_assum drule >> strip_tac >>
      gvs[] >> metis_tac[])
  >- (rpt strip_tac >>
      `MEM inst bb.bb_instructions` by metis_tac[MEM_APPEND, MEM] >>
      fs[ld_dload_safe_def] >>
      first_x_assum drule >> strip_tac >>
      gvs[] >> metis_tac[]);

(* DLOADBYTES Error -> expansion also errors.
   When DLOADBYTES returns Error (operand NONE), the ADD+CODECOPY expansion
   also returns Error because the same operand is NONE on s2 after ADD. *)
Theorem ld_dloadbytes_error[local]:
  !inst fuel ctx s1 s2 vars dst_op v size_op e.
    inst.inst_opcode = DLOADBYTES /\
    inst.inst_operands = [dst_op; Lit v; size_op] /\
    inst_wf inst /\
    ld_ok vars s1 s2 /\
    code_layout_valid s2 /\
    ld_add_var inst.inst_id IN vars /\
    (!x. MEM (Var x) inst.inst_operands ==> x NOTIN vars) /\
    step_inst fuel ctx inst s1 = Error e ==>
    ?e2. run_insts fuel ctx (lower_dload_inst inst) s2 = Error e2
Proof
  rpt strip_tac >>
  `inst.inst_opcode <> INVOKE` by simp[] >>
  gvs[step_inst_non_invoke] >>
  (* DLOADBYTES Error means dst_op or size_op NONE on s1 *)
  `eval_operand dst_op s1 = NONE \/ eval_operand size_op s1 = NONE` by
    (gvs[step_inst_base_def, eval_operand_def] >>
     rpt (BasicProvers.PURE_FULL_CASE_TAC >> gvs[])) >>
  (* Same on s2 by ld_eval_operand_agree *)
  `eval_operand dst_op s2 = eval_operand dst_op s1 /\
   eval_operand size_op s2 = eval_operand size_op s1` by
    (conj_tac >> irule (GSYM ld_eval_operand_agree) >>
     qexists_tac `vars` >> simp[] >> metis_tac[]) >>
  (* Unfold expansion *)
  simp[lower_dload_inst_def, LET_THM, run_insts_def, step_inst_non_invoke] >>
  (* ADD always succeeds: Lit and Label both evaluate *)
  `FLOOKUP s2.vs_labels "code_end" =
     SOME (n2w (LENGTH s2.vs_code - LENGTH s2.vs_data_section))` by
    gvs[code_layout_valid_def] >>
  simp[step_inst_base_def, exec_pure2_def, eval_operand_def, LET_THM] >>
  (* After ADD returns OK (update_var add_v result s2), dst_op/size_op
     unchanged since add_var IN vars but operand vars NOTIN vars *)
  qmatch_goalsub_abbrev_tac `update_var (ld_add_var inst.inst_id) add_result s2` >>
  `!op. (!x. op = Var x ==> x NOTIN vars) ==>
     eval_operand op (update_var (ld_add_var inst.inst_id) add_result s2) =
     eval_operand op s2` by
    (rpt strip_tac >> irule eval_operand_update_var_other >>
     rpt strip_tac >> CCONTR_TAC >> gvs[] >> res_tac >> gvs[]) >>
  (* CODECOPY errors because dst_op or size_op is NONE *)
  `eval_operand dst_op (update_var (ld_add_var inst.inst_id) add_result s2) =
     eval_operand dst_op s2` by (first_x_assum irule >> metis_tac[]) >>
  `eval_operand size_op (update_var (ld_add_var inst.inst_id) add_result s2) =
     eval_operand size_op s2` by (first_x_assum irule >> metis_tac[]) >>
  ASM_REWRITE_TAC[] >> gvs[lookup_var_def, update_var_def, FLOOKUP_UPDATE] >>
  rpt (BasicProvers.PURE_FULL_CASE_TAC >> gvs[])
QED

(* Non-OK single instruction step: if step_inst_base h s1 is non-OK,
   lift_result holds between the s1 result and run_insts of the expansion on s2.
   Handles DLOAD/ALLOCA (contradiction), DLOADBYTES (Error), passthrough (ld_ok_full). *)
Theorem ld_non_ok_inst_step[local]:
  !h fuel ctx s1 s2 vars.
    ld_ok vars s1 s2 /\
    code_layout_valid s1 /\ code_layout_valid s2 /\
    ~is_terminator h.inst_opcode /\
    h.inst_opcode <> INVOKE /\
    ~reads_memory h.inst_opcode /\
    inst_wf h /\
    (!x. MEM (Var x) h.inst_operands ==> x NOTIN vars) /\
    (!out. h.inst_opcode = ALLOCA /\ MEM out h.inst_outputs ==> out IN vars) /\
    (h.inst_opcode = DLOAD ==> ?v. h.inst_operands = [Lit v]) /\
    (h.inst_opcode = DLOADBYTES ==>
       ?dst_op v size_op. h.inst_operands = [dst_op; Lit v; size_op]) /\
    (h.inst_opcode = DLOAD \/ h.inst_opcode = DLOADBYTES ==>
       ld_add_var h.inst_id IN vars) /\
    (h.inst_opcode = DLOAD ==> ld_alloca_var h.inst_id IN vars) /\
    (h.inst_opcode = DLOAD ==>
       !v. h.inst_operands = [Lit v] ==>
         w2n v + (LENGTH s1.vs_code - LENGTH s1.vs_data_section) <
           dimword(:256)) /\
    (h.inst_opcode = DLOADBYTES ==>
       !dst_op v size_op. h.inst_operands = [dst_op; Lit v; size_op] ==>
         w2n v + (LENGTH s1.vs_code - LENGTH s1.vs_data_section) <
           dimword(:256)) /\
    (!r. step_inst fuel ctx h s1 <> OK r) ==>
    lift_result (ld_ok vars) (ld_equiv vars) (ld_equiv vars)
      (step_inst fuel ctx h s1)
      (run_insts fuel ctx (lower_dload_inst h) s2)
Proof
  rpt strip_tac >>
  `step_inst fuel ctx h s1 = step_inst_base h s1 /\
   step_inst fuel ctx h s2 = step_inst_base h s2` by
    (conj_tac >> irule step_inst_non_invoke >> gvs[]) >>
  Cases_on `h.inst_opcode = DLOAD`
  >- ((* DLOAD always OK → contradiction *)
      gvs[] >>
      `?v. h.inst_operands = [Lit v]` by metis_tac[] >>
      `?s1'. step_inst_base h s1 = OK s1'` by
        (irule_at Any step_inst_base_dload_ok >> gvs[]) >>
      gvs[]) >>
  Cases_on `h.inst_opcode = ALLOCA`
  >- ((* ALLOCA always OK → contradiction *)
      gvs[] >>
      `?s1'. step_inst_base h s1 = OK s1'` by
        (irule step_inst_base_alloca_ok >> gvs[]) >>
      gvs[]) >>
  Cases_on `h.inst_opcode = DLOADBYTES`
  >- ((* DLOADBYTES: only OK or Error; non-OK must be Error *)
      gvs[] >>
      `(!v. step_inst_base h s1 <> Halt v) /\
       (!w v. step_inst_base h s1 <> IntRet w v) /\
       (!a v. step_inst_base h s1 <> Abort a v)` by
        metis_tac[step_inst_base_dloadbytes_no_halt] >>
      Cases_on `step_inst_base h s1` >> gvs[] >>
      (* Goal: lift_result ... (Error s) (run_insts ...).
         Need to show run_insts returns Error, then lift_result closes. *)
      `?e2. run_insts fuel ctx (lower_dload_inst h) s2 = Error e2` by
        (irule ld_dloadbytes_error >> simp[] >>
         qexistsl_tac [`s`, `s1`, `vars`] >> simp[MEM] >> metis_tac[]) >>
      gvs[lift_result_def]) >>
  (* Passthrough *)
  `(?s1' s2'. step_inst_base h s1 = OK s1' /\
              step_inst_base h s2 = OK s2' /\ ld_ok vars s1' s2') \/
   (?e1 e2. step_inst_base h s1 = Error e1 /\
            step_inst_base h s2 = Error e2) \/
   (?a v1 v2. step_inst_base h s1 = Abort a v1 /\
              step_inst_base h s2 = Abort a v2 /\
              ld_equiv vars v1 v2)` by
    (irule step_inst_base_ld_ok_full >> gvs[] >> metis_tac[]) >>
  (* step_inst_base h s1 is non-OK: contradicts OK disjunct, leaves Error or Abort *)
  Cases_on `step_inst fuel ctx h s1` >> gvs[] >>
  simp[lower_dload_inst_passthrough, run_insts_append, run_insts_sing,
       lift_result_def]
QED

(* Full simulation: returns lift_result for all result types, not just OK.
   Subsumes ld_run_insts_sim for the OK case. *)
Theorem ld_run_insts_sim_full[local]:
  !insts fuel ctx s1 s2 vars.
    ld_ok vars s1 s2 /\
    code_layout_valid s1 /\ code_layout_valid s2 /\
    EVERY (\i. ~is_terminator i.inst_opcode /\
               i.inst_opcode <> INVOKE /\
               ~reads_memory i.inst_opcode) insts /\
    (!inst x. MEM inst insts /\ MEM (Var x) inst.inst_operands ==>
              x NOTIN vars) /\
    (!inst out. MEM inst insts /\ inst.inst_opcode = ALLOCA /\
               MEM out inst.inst_outputs ==> out IN vars) /\
    (!inst v. MEM inst insts /\ inst.inst_opcode = DLOAD /\
              inst.inst_operands = [Lit v] ==>
              w2n v + (LENGTH s1.vs_code - LENGTH s1.vs_data_section) <
                dimword(:256)) /\
    (!inst dst_op v size_op. MEM inst insts /\ inst.inst_opcode = DLOADBYTES /\
              inst.inst_operands = [dst_op; Lit v; size_op] ==>
              w2n v + (LENGTH s1.vs_code - LENGTH s1.vs_data_section) <
                dimword(:256)) /\
    (!inst. MEM inst insts /\ inst.inst_opcode = DLOAD ==>
            ?v. inst.inst_operands = [Lit v]) /\
    (!inst. MEM inst insts /\ inst.inst_opcode = DLOADBYTES ==>
            ?dst_op v size_op. inst.inst_operands = [dst_op; Lit v; size_op]) /\
    (!inst. MEM inst insts /\
            (inst.inst_opcode = DLOAD \/ inst.inst_opcode = DLOADBYTES) ==>
            ld_add_var inst.inst_id IN vars) /\
    (!inst. MEM inst insts /\ inst.inst_opcode = DLOAD ==>
            ld_alloca_var inst.inst_id IN vars) /\
    EVERY inst_wf insts ==>
    lift_result (ld_ok vars) (ld_equiv vars) (ld_equiv vars)
      (run_insts fuel ctx insts s1)
      (run_insts fuel ctx (FLAT (MAP lower_dload_inst insts)) s2)
Proof
  Induct >> simp[run_insts_def, lift_result_def] >>
  rpt gen_tac >> strip_tac >>
  rename1 `step_inst fuel ctx h s1` >>
  Cases_on `step_inst fuel ctx h s1` >> gvs[]
  >- ((* OK case: use ld_single_inst_step for ALL opcodes, then IH *)
      rename1 `step_inst _ _ h s1 = OK s1_mid` >>
      drule_all step_inst_preserves_layout >> strip_tac >>
      `code_layout_valid s1_mid` by
        metis_tac[step_inst_preserves_code_layout_valid] >>
      `?s2_mid. run_insts fuel ctx (lower_dload_inst h) s2 = OK s2_mid /\
                ld_ok vars s1_mid s2_mid` by
        (irule ld_single_inst_step >>
         RULE_ASSUM_TAC (REWRITE_RULE [DISJ_IMP_THM, FORALL_AND_THM]) >>
         simp[] >> metis_tac[]) >>
      simp[run_insts_append] >>
      `code_layout_valid s2_mid` by
        metis_tac[run_insts_preserves_code_layout_valid] >>
      ld_finish_ih)
  >> (* Non-OK cases: 4 goals from outer Cases_on (Error, Halt, Abort, IntRet).
        >> distributes to ALL goals, so use a single dispatch tactic.
        The tactic: establish step_inst = step_inst_base, then use
        step_inst_base_ld_ok_full (which covers all non-DLOAD/DLOADBYTES/ALLOCA)
        plus contradiction lemmas for DLOAD/ALLOCA/DLOADBYTES. *)
  (`step_inst fuel ctx h s1 = step_inst_base h s1 /\
   step_inst fuel ctx h s2 = step_inst_base h s2` by
    (conj_tac >> irule step_inst_non_invoke >> gvs[]) >>
  (* Case split + dispatch: each branch handles the current single goal *)
  Cases_on `h.inst_opcode = DLOAD`
  >- (gvs[] >>
      `?v. h.inst_operands = [Lit v]` by
        (first_x_assum (qspec_then `h` mp_tac) >> simp[]) >>
      `?s1'. step_inst_base h s1 = OK s1'` by
        (irule_at Any step_inst_base_dload_ok >> gvs[]) >>
      gvs[]) >>
  Cases_on `h.inst_opcode = ALLOCA`
  >- (gvs[] >>
      `?s1'. step_inst_base h s1 = OK s1'` by
        (irule step_inst_base_alloca_ok >> gvs[]) >>
      gvs[]) >>
  Cases_on `h.inst_opcode = DLOADBYTES`
  >- (gvs[] >>
      `(!v. step_inst_base h s1 <> Halt v) /\
       (!w v. step_inst_base h s1 <> IntRet w v) /\
       (!a v. step_inst_base h s1 <> Abort a v)` by
        metis_tac[step_inst_base_dloadbytes_no_halt] >>
      gvs[] >>
      `?dst_op v size_op. h.inst_operands = [dst_op; Lit v; size_op]` by
        (first_x_assum (qspec_then `h` mp_tac) >> simp[]) >>
      `?e2. run_insts fuel ctx (lower_dload_inst h) s2 = Error e2` by
        (irule ld_dloadbytes_error >> simp[] >>
         qexistsl_tac [`s`, `s1`, `vars`] >> simp[MEM] >> metis_tac[]) >>
      simp[run_insts_append, lift_result_def]) >>
  `(?s1' s2'. step_inst_base h s1 = OK s1' /\
              step_inst_base h s2 = OK s2' /\ ld_ok vars s1' s2') \/
   (?e1 e2. step_inst_base h s1 = Error e1 /\
            step_inst_base h s2 = Error e2) \/
   (?a v1 v2. step_inst_base h s1 = Abort a v1 /\
              step_inst_base h s2 = Abort a v2 /\
              ld_equiv vars v1 v2)` by
    (irule step_inst_base_ld_ok_full >> gvs[] >> metis_tac[]) >>
  gvs[] >>
  simp[lower_dload_inst_passthrough, run_insts_append, run_insts_sing,
       lift_result_def])
QED

(* ===== Per-block simulation ===== *)

(* Helper: BUTLAST instructions in a well-formed block are non-terminators *)
Theorem wf_block_butlast_non_term[local]:
  !bb. bb_well_formed bb ==>
    EVERY (\i. ~is_terminator i.inst_opcode) (FRONT bb.bb_instructions)
Proof
  rpt strip_tac >> fs[bb_well_formed_def] >>
  simp[EVERY_EL, LENGTH_FRONT] >> rpt strip_tac >>
  `EL n (FRONT bb.bb_instructions) = EL n bb.bb_instructions` by
    (irule EL_FRONT >> simp[LENGTH_FRONT, NULL_EQ]) >>
  gvs[] >>
  `n < LENGTH bb.bb_instructions` by
    (Cases_on `bb.bb_instructions` >> gvs[]) >>
  res_tac >> gvs[]
QED

(* Terminator step_inst_base OK non-halted results always have idx=0
   (they must be JMP/JNZ/DJMP which all use jump_to) *)
Theorem step_inst_base_term_OK_idx_0[local]:
  !inst s v.
    step_inst_base inst s = OK v /\
    is_terminator inst.inst_opcode /\
    ~v.vs_halted ==>
    v.vs_inst_idx = 0
Proof
  gen_tac >> Cases_on `inst.inst_opcode` >>
  simp[is_terminator_def] >> rpt strip_tac >>
  gvs[step_inst_base_def, AllCaseEqs(), jump_to_def]
QED

(* Helper: step_inst_base on a terminator with idx override produces
   the same lift_result as without, given ld_ok on base states. *)
Theorem ld_ok_terminator_idx_override[local]:
  !inst s1 s2 vars n1 n2.
    ld_ok vars s1 s2 /\
    is_terminator inst.inst_opcode /\
    ~reads_memory inst.inst_opcode /\
    inst.inst_opcode <> INVOKE /\
    (!x. MEM (Var x) inst.inst_operands ==> x NOTIN vars) ==>
    lift_result (ld_ok vars) (ld_equiv vars) (ld_equiv vars)
      (case step_inst_base inst (s1 with vs_inst_idx := n1) of
         OK s_out => if s_out.vs_halted then Halt s_out else OK s_out
       | Halt v => Halt v
       | Abort e v => Abort e v
       | IntRet v1 v2 => IntRet v1 v2
       | Error e => Error e)
      (case step_inst_base inst (s2 with vs_inst_idx := n2) of
         OK s_out => if s_out.vs_halted then Halt s_out else OK s_out
       | Halt v => Halt v
       | Abort e v => Abort e v
       | IntRet v1 v2 => IntRet v1 v2
       | Error e => Error e)
Proof
  rpt strip_tac >>
  (* Use idx_norm0 to normalize both sides *)
  qabbrev_tac `r1 = step_inst_base inst s1` >>
  qabbrev_tac `r2 = step_inst_base inst s2` >>
  `exec_result_map (\s'. s' with vs_inst_idx := 0)
     (step_inst_base inst (s1 with vs_inst_idx := n1)) =
   exec_result_map (\s'. s' with vs_inst_idx := 0) r1` by
    metis_tac[terminator_step_inst_base_idx_norm0] >>
  `exec_result_map (\s'. s' with vs_inst_idx := 0)
     (step_inst_base inst (s2 with vs_inst_idx := n2)) =
   exec_result_map (\s'. s' with vs_inst_idx := 0) r2` by
    metis_tac[terminator_step_inst_base_idx_norm0] >>
  (* step_inst_base_ld_ok_terminator gives lift_result for r1, r2 *)
  `lift_result (ld_ok vars) (ld_equiv vars) (ld_equiv vars) r1 r2` by
    (unabbrev_all_tac >> irule step_inst_base_ld_ok_terminator >> metis_tac[]) >>
  (* Now relate the idx-overridden versions to r1, r2 *)
  Cases_on `r1` >> Cases_on `r2` >> gvs[lift_result_def, exec_result_map_def] >>
  Cases_on `step_inst_base inst (s1 with vs_inst_idx := n1)` >>
  Cases_on `step_inst_base inst (s2 with vs_inst_idx := n2)` >>
  gvs[exec_result_map_def, lift_result_def,
      venom_state_component_equality] >>
  TRY (gvs[ld_equiv_def] >> NO_TAC) >>
  (* OK, OK: case split on halted *)
  Cases_on `v'.vs_halted` >>
  gvs[lift_result_def, ld_ok_def, ld_equiv_def, lookup_var_def] >>
  metis_tac[step_inst_base_term_OK_idx_0]
QED

(* lower_dload_inst preserves non-terminator/non-INVOKE *)
Theorem lower_dload_inst_every_non_term[local]:
  !insts.
    EVERY (\i. ~is_terminator i.inst_opcode /\ i.inst_opcode <> INVOKE) insts ==>
    EVERY (\i. ~is_terminator i.inst_opcode /\ i.inst_opcode <> INVOKE)
      (FLAT (MAP lower_dload_inst insts))
Proof
  Induct >> simp[] >> rpt strip_tac >>
  simp[EVERY_APPEND] >>
  rename1 `lower_dload_inst h` >>
  simp[lower_dload_inst_def] >>
  rpt (CASE_TAC >> gvs[]) >>
  simp[is_terminator_def, EVERY_DEF]
QED

(* Shared inductive prefix for run_block prefix factoring lemmas.
   Establishes: for non-terminator/non-INVOKE prefix, if step_inst on head
   returns OK, the run_block recurses and the IH applies to the tail. *)

(* When run_insts on non-terminator prefix returns Error,
   run_block returns the same Error (Error carries no state). *)
Theorem run_block_prefix_error[local]:
  !prefix fuel ctx bb s j e.
    j + LENGTH prefix <= LENGTH bb.bb_instructions /\
    EVERY (\i. ~is_terminator i.inst_opcode /\ i.inst_opcode <> INVOKE) prefix /\
    (!k. k < LENGTH prefix ==> EL (j + k) bb.bb_instructions = EL k prefix) /\
    run_insts fuel ctx prefix s = Error e ==>
    run_block fuel ctx bb (s with vs_inst_idx := j) = Error e
Proof
  Induct >> simp[run_insts_def] >>
  rpt gen_tac >> strip_tac >>
  rename1 `h :: prefix` >>
  fs[EVERY_DEF] >>
  `j < LENGTH bb.bb_instructions` by simp[] >>
  `EL j bb.bb_instructions = h` by
    (first_x_assum (qspec_then `0` mp_tac) >> simp[]) >>
  `step_inst fuel ctx h (s with vs_inst_idx := j) =
   exec_result_map (\s'. s' with vs_inst_idx := j)
     (step_inst fuel ctx h s)` by
    simp[step_inst_idx_indep_local] >>
  ONCE_REWRITE_TAC[run_block_def] >>
  simp[get_instruction_def] >>
  Cases_on `step_inst fuel ctx h s` >>
  gvs[exec_result_map_def, Once run_insts_def] >>
  rename1 `step_inst _ _ h s = OK s'` >>
  first_x_assum (qspecl_then [`fuel`, `ctx`, `bb`, `s'`, `SUC j`, `e`] mp_tac) >>
  simp[] >> impl_tac
  >- (simp[] >> rpt strip_tac >>
      first_x_assum (qspec_then `SUC k` mp_tac) >> simp[arithmeticTheory.ADD_CLAUSES]) >>
  simp[arithmeticTheory.ADD_CLAUSES]
QED

(* When run_insts on non-terminator prefix returns Abort,
   run_block returns Abort with same abort type and idx-modified state. *)
Theorem run_block_prefix_abort[local]:
  !prefix fuel ctx bb s j a v.
    j + LENGTH prefix <= LENGTH bb.bb_instructions /\
    EVERY (\i. ~is_terminator i.inst_opcode /\ i.inst_opcode <> INVOKE) prefix /\
    (!k. k < LENGTH prefix ==> EL (j + k) bb.bb_instructions = EL k prefix) /\
    run_insts fuel ctx prefix s = Abort a v ==>
    ?j'. run_block fuel ctx bb (s with vs_inst_idx := j) =
         Abort a (v with vs_inst_idx := j')
Proof
  Induct >> simp[run_insts_def] >>
  rpt gen_tac >> strip_tac >>
  rename1 `h :: prefix` >>
  fs[EVERY_DEF] >>
  `j < LENGTH bb.bb_instructions` by simp[] >>
  `EL j bb.bb_instructions = h` by
    (first_x_assum (qspec_then `0` mp_tac) >> simp[]) >>
  `step_inst fuel ctx h (s with vs_inst_idx := j) =
   exec_result_map (\s'. s' with vs_inst_idx := j)
     (step_inst fuel ctx h s)` by
    simp[step_inst_idx_indep_local] >>
  ONCE_REWRITE_TAC[run_block_def] >>
  simp[get_instruction_def] >>
  Cases_on `step_inst fuel ctx h s` >>
  gvs[exec_result_map_def, Once run_insts_def]
  >- (
    rename1 `step_inst _ _ h s = OK s'` >>
    first_x_assum (qspecl_then [`fuel`, `ctx`, `bb`, `s'`, `SUC j`, `a`, `v`] mp_tac) >>
    simp[] >> impl_tac
    >- (simp[] >> rpt strip_tac >>
        first_x_assum (qspec_then `SUC k` mp_tac) >> simp[arithmeticTheory.ADD_CLAUSES]) >>
    simp[arithmeticTheory.ADD_CLAUSES]
  ) >>
  (* step_inst returned Abort directly *)
  qexists_tac `j` >> simp[]
QED

(* Halt case: same pattern as Abort *)
Theorem run_block_prefix_halt[local]:
  !prefix fuel ctx bb s j v.
    j + LENGTH prefix <= LENGTH bb.bb_instructions /\
    EVERY (\i. ~is_terminator i.inst_opcode /\ i.inst_opcode <> INVOKE) prefix /\
    (!k. k < LENGTH prefix ==> EL (j + k) bb.bb_instructions = EL k prefix) /\
    run_insts fuel ctx prefix s = Halt v ==>
    ?j'. run_block fuel ctx bb (s with vs_inst_idx := j) =
         Halt (v with vs_inst_idx := j')
Proof
  Induct >> simp[run_insts_def] >>
  rpt gen_tac >> strip_tac >>
  rename1 `h :: prefix` >>
  fs[EVERY_DEF] >>
  `j < LENGTH bb.bb_instructions` by simp[] >>
  `EL j bb.bb_instructions = h` by
    (first_x_assum (qspec_then `0` mp_tac) >> simp[]) >>
  `step_inst fuel ctx h (s with vs_inst_idx := j) =
   exec_result_map (\s'. s' with vs_inst_idx := j)
     (step_inst fuel ctx h s)` by
    simp[step_inst_idx_indep_local] >>
  ONCE_REWRITE_TAC[run_block_def] >>
  simp[get_instruction_def] >>
  Cases_on `step_inst fuel ctx h s` >>
  gvs[exec_result_map_def, Once run_insts_def]
  >- (
    rename1 `step_inst _ _ h s = OK s'` >>
    first_x_assum (qspecl_then [`fuel`, `ctx`, `bb`, `s'`, `SUC j`, `v`] mp_tac) >>
    simp[] >> impl_tac
    >- (simp[] >> rpt strip_tac >>
        first_x_assum (qspec_then `SUC k` mp_tac) >> simp[arithmeticTheory.ADD_CLAUSES]) >>
    simp[arithmeticTheory.ADD_CLAUSES]
  ) >>
  qexists_tac `j` >> simp[]
QED

(* IntRet case: same pattern *)
Theorem run_block_prefix_intret[local]:
  !prefix fuel ctx bb s j l v.
    j + LENGTH prefix <= LENGTH bb.bb_instructions /\
    EVERY (\i. ~is_terminator i.inst_opcode /\ i.inst_opcode <> INVOKE) prefix /\
    (!k. k < LENGTH prefix ==> EL (j + k) bb.bb_instructions = EL k prefix) /\
    run_insts fuel ctx prefix s = IntRet l v ==>
    ?j'. run_block fuel ctx bb (s with vs_inst_idx := j) =
         IntRet l (v with vs_inst_idx := j')
Proof
  Induct >> simp[run_insts_def] >>
  rpt gen_tac >> strip_tac >>
  rename1 `h :: prefix` >>
  fs[EVERY_DEF] >>
  `j < LENGTH bb.bb_instructions` by simp[] >>
  `EL j bb.bb_instructions = h` by
    (first_x_assum (qspec_then `0` mp_tac) >> simp[]) >>
  `step_inst fuel ctx h (s with vs_inst_idx := j) =
   exec_result_map (\s'. s' with vs_inst_idx := j)
     (step_inst fuel ctx h s)` by
    simp[step_inst_idx_indep_local] >>
  ONCE_REWRITE_TAC[run_block_def] >>
  simp[get_instruction_def] >>
  Cases_on `step_inst fuel ctx h s` >>
  gvs[exec_result_map_def, Once run_insts_def]
  >- (
    rename1 `step_inst _ _ h s = OK s'` >>
    first_x_assum (qspecl_then [`fuel`, `ctx`, `bb`, `s'`, `SUC j`, `l`, `v`] mp_tac) >>
    simp[] >> impl_tac
    >- (simp[] >> rpt strip_tac >>
        first_x_assum (qspec_then `SUC k` mp_tac) >> simp[arithmeticTheory.ADD_CLAUSES]) >>
    simp[arithmeticTheory.ADD_CLAUSES]
  ) >>
  qexists_tac `j` >> simp[]
QED

(* ld_equiv is independent of vs_inst_idx *)
Theorem ld_equiv_idx_indep[local]:
  !vars s1 s2 j1 j2.
    ld_equiv vars s1 s2 ==>
    ld_equiv vars (s1 with vs_inst_idx := j1) (s2 with vs_inst_idx := j2)
Proof
  rw[ld_equiv_def, lookup_var_def]
QED

(* When s.vs_inst_idx = 0 and prefix returns OK, run_block factors into
   prefix + rest. Specializes run_block_skip_prefix_local for idx=0. *)
Theorem run_block_skip_prefix_idx0[local]:
  !prefix fuel ctx bb s s'.
    s.vs_inst_idx = 0 /\
    LENGTH prefix < LENGTH bb.bb_instructions /\
    EVERY (\i. ~is_terminator i.inst_opcode /\ i.inst_opcode <> INVOKE) prefix /\
    (!k. k < LENGTH prefix ==> EL k bb.bb_instructions = EL k prefix) /\
    run_insts fuel ctx prefix s = OK s' ==>
    run_block fuel ctx bb s =
    run_block fuel ctx bb (s' with vs_inst_idx := LENGTH prefix)
Proof
  rpt strip_tac >>
  mp_tac (Q.SPECL [`prefix`, `fuel`, `ctx`, `bb`, `s`, `0`, `s'`]
    run_block_skip_prefix_local) >>
  simp[] >>
  `s with vs_inst_idx := 0 = s` by simp[venom_state_component_equality] >>
  gvs[]
QED

(* Shared tactic for all run_block_prefix_*_idx0 theorems:
   rewrite s to (s with vs_inst_idx := 0) then apply the base lemma *)
fun idx0_tac base_thm =
  rpt strip_tac >>
  `s = s with vs_inst_idx := 0` by simp[venom_state_component_equality] >>
  pop_assum (fn th => ONCE_REWRITE_TAC [th]) >>
  irule base_thm >> qexists_tac `prefix` >> simp[];

Theorem run_block_prefix_error_idx0[local]:
  !prefix fuel ctx bb s e.
    s.vs_inst_idx = 0 /\
    LENGTH prefix < LENGTH bb.bb_instructions /\
    EVERY (\i. ~is_terminator i.inst_opcode /\ i.inst_opcode <> INVOKE) prefix /\
    (!k. k < LENGTH prefix ==> EL k bb.bb_instructions = EL k prefix) /\
    run_insts fuel ctx prefix s = Error e ==>
    run_block fuel ctx bb s = Error e
Proof
  idx0_tac run_block_prefix_error
QED

Theorem run_block_prefix_halt_idx0[local]:
  !prefix fuel ctx bb s v.
    s.vs_inst_idx = 0 /\
    LENGTH prefix < LENGTH bb.bb_instructions /\
    EVERY (\i. ~is_terminator i.inst_opcode /\ i.inst_opcode <> INVOKE) prefix /\
    (!k. k < LENGTH prefix ==> EL k bb.bb_instructions = EL k prefix) /\
    run_insts fuel ctx prefix s = Halt v ==>
    ?j. run_block fuel ctx bb s = Halt (v with vs_inst_idx := j)
Proof
  idx0_tac run_block_prefix_halt
QED

Theorem run_block_prefix_abort_idx0[local]:
  !prefix fuel ctx bb s a v.
    s.vs_inst_idx = 0 /\
    LENGTH prefix < LENGTH bb.bb_instructions /\
    EVERY (\i. ~is_terminator i.inst_opcode /\ i.inst_opcode <> INVOKE) prefix /\
    (!k. k < LENGTH prefix ==> EL k bb.bb_instructions = EL k prefix) /\
    run_insts fuel ctx prefix s = Abort a v ==>
    ?j. run_block fuel ctx bb s = Abort a (v with vs_inst_idx := j)
Proof
  idx0_tac run_block_prefix_abort
QED

Theorem run_block_prefix_intret_idx0[local]:
  !prefix fuel ctx bb s l v.
    s.vs_inst_idx = 0 /\
    LENGTH prefix < LENGTH bb.bb_instructions /\
    EVERY (\i. ~is_terminator i.inst_opcode /\ i.inst_opcode <> INVOKE) prefix /\
    (!k. k < LENGTH prefix ==> EL k bb.bb_instructions = EL k prefix) /\
    run_insts fuel ctx prefix s = IntRet l v ==>
    ?j. run_block fuel ctx bb s = IntRet l (v with vs_inst_idx := j)
Proof
  idx0_tac run_block_prefix_intret
QED

(* Shared arithmetic for offset goals: dimword DIV 2 + dimword DIV 2 = dimword *)
val dimword_half_add = prove(
  ``dimword(:256) DIV 2 + dimword(:256) DIV 2 = dimword(:256)``,
  simp[dimword_def] >>
  `1 <= dimindex(:256)` by simp[fcpTheory.DIMINDEX_GE_1] >>
  Cases_on `dimindex(:256)` >> simp[EXP, MULT_DIV]);

(* Shared tactic: prove x IN ld_fresh_vars_fn fn from MEM bb/inst *)
fun ld_fresh_mem_tac () =
  simp[ld_fresh_vars_fn_def, IN_BIGUNION, MEM_MAP, PULL_EXISTS] >>
  qexists_tac `bb` >> simp[] >>
  qexists_tac `inst` >> simp[ld_fresh_vars_inst_def];

(* Unfolded ld_dload_safe for a specific bb/inst — avoids fs[ld_dload_safe_def]
   eagerly instantiating universals in goal context *)
Theorem ld_dload_safe_inst[local]:
  !fn bb inst.
    ld_dload_safe fn /\ MEM bb fn.fn_blocks /\
    MEM inst bb.bb_instructions ==>
    (inst.inst_opcode = DLOAD ==>
       ?v. inst.inst_operands = [Lit v] /\ w2n v < dimword(:256) DIV 2) /\
    (inst.inst_opcode = DLOADBYTES ==>
       ?dst_op v size_op. inst.inst_operands = [dst_op; Lit v; size_op] /\
                           w2n v < dimword(:256) DIV 2)
Proof
  rpt strip_tac >> fs[ld_dload_safe_def] >> res_tac >> gvs[]
QED

(* Offset arithmetic: w2n v + offset < dimword when both < dimword/2 *)
Theorem ld_offset_bound[local]:
  !v (x:num).
    w2n (v:256 word) < dimword(:256) DIV 2 /\
    x <= dimword(:256) DIV 2 ==>
    w2n v + x < dimword(:256)
Proof
  rpt strip_tac >>
  `dimword(:256) DIV 2 + dimword(:256) DIV 2 = dimword(:256)`
    by simp[dimword_half_add] >>
  simp[]
QED

(* Bridge from function-level ld_dload_safe to ld_run_insts_sim_full for
   a block's non-terminator prefix. *)
Theorem ld_prefix_sim[local]:
  !fn bb prefix fuel ctx s1 s2 vars.
    vars = ld_fresh_vars_fn fn /\
    ld_ok vars s1 s2 /\
    code_layout_valid s1 /\ code_layout_valid s2 /\
    ld_dload_safe fn /\ ld_no_original_alloca fn /\
    fn_inst_wf fn /\
    MEM bb fn.fn_blocks /\
    bb.bb_instructions = prefix ++ [LAST bb.bb_instructions] /\
    EVERY (\i. ~is_terminator i.inst_opcode /\
               i.inst_opcode <> INVOKE /\
               ~reads_memory i.inst_opcode) prefix /\
    EVERY inst_wf prefix /\
    (!inst. MEM inst prefix ==> inst.inst_opcode <> ALLOCA) /\
    (!bb' inst x.
       MEM bb' fn.fn_blocks /\ MEM inst bb'.bb_instructions /\
       MEM (Var x) inst.inst_operands ==>
       x NOTIN vars) ==>
    lift_result (ld_ok vars) (ld_equiv vars) (ld_equiv vars)
      (run_insts fuel ctx prefix s1)
      (run_insts fuel ctx (FLAT (MAP lower_dload_inst prefix)) s2)
Proof
  rpt strip_tac >>
  irule ld_run_insts_sim_full >> simp[] >>
  rpt conj_tac >> rpt gen_tac >> strip_tac >>
  `MEM inst bb.bb_instructions` by metis_tac[MEM_APPEND, MEM] >>
  (* ALLOCA contradiction + operand freshness *)
  TRY (metis_tac[]) >>
  (* Specialize ld_dload_safe for this bb/inst via helper *)
  `(inst.inst_opcode = DLOAD ==>
      ?v. inst.inst_operands = [Lit v] /\ w2n v < dimword(:256) DIV 2) /\
   (inst.inst_opcode = DLOADBYTES ==>
      ?dst_op v size_op. inst.inst_operands = [dst_op; Lit v; size_op] /\
                          w2n v < dimword(:256) DIV 2)` by
    metis_tac[ld_dload_safe_inst] >>
  gvs[] >>
  (* operand shape goals: closed by gvs[] above *)
  (* offset arithmetic: both offsets bounded by dimword/2 *)
  TRY (gvs[code_layout_valid_def] >>
       `dimword(:256) DIV 2 + dimword(:256) DIV 2 = dimword(:256)`
         by simp[dimword_half_add] >>
       simp[] >> NO_TAC) >>
  (* membership: ld_alloca_var/ld_add_var IN ld_fresh_vars_fn *)
  ld_fresh_mem_tac ()
QED

(* Helper: at the terminator, run_block on ld_ok states produces
   lift_result-related results. Separates the terminator step from
   the prefix factoring logic in ld_block_sim. *)
Theorem ld_run_block_terminator[local]:
  !fuel ctx bb1 bb2 inst s1 s2 vars n1 n2.
    ld_ok vars s1 s2 /\
    is_terminator inst.inst_opcode /\
    inst.inst_opcode <> INVOKE /\
    ~reads_memory inst.inst_opcode /\
    (!x. MEM (Var x) inst.inst_operands ==> x NOTIN vars) /\
    s1.vs_inst_idx = n1 /\
    s2.vs_inst_idx = n2 /\
    n1 < LENGTH bb1.bb_instructions /\
    n2 < LENGTH bb2.bb_instructions /\
    EL n1 bb1.bb_instructions = inst /\
    EL n2 bb2.bb_instructions = inst ==>
    lift_result (ld_ok vars) (ld_equiv vars) (ld_equiv vars)
      (run_block fuel ctx bb1 s1)
      (run_block fuel ctx bb2 s2)
Proof
  rpt strip_tac >>
  ONCE_REWRITE_TAC[run_block_def] >>
  simp[get_instruction_def] >>
  ONCE_REWRITE_TAC[step_inst_def] >> simp[] >>
  `lift_result (ld_ok vars) (ld_equiv vars) (ld_equiv vars)
     (step_inst_base inst s1) (step_inst_base inst s2)` by
    (irule step_inst_base_ld_ok_terminator >> simp[]) >>
  Cases_on `step_inst_base inst s1` >>
  Cases_on `step_inst_base inst s2` >>
  gvs[lift_result_def] >>
  Cases_on `v.vs_halted` >> Cases_on `v'.vs_halted` >>
  gvs[lift_result_def, ld_ok_def, ld_equiv_def]
QED

Theorem ld_block_sim_ok[local]:
  !fuel ctx bb exp_bb prefix exp_prefix term vars s1 s2 s1_mid s2_mid.
    ld_ok vars s1_mid s2_mid /\
    s1.vs_inst_idx = 0 /\ s2.vs_inst_idx = 0 /\
    bb.bb_instructions = prefix ++ [term] /\
    exp_bb.bb_instructions = exp_prefix ++ [term] /\
    LENGTH prefix < LENGTH bb.bb_instructions /\
    LENGTH exp_prefix < LENGTH exp_bb.bb_instructions /\
    EVERY (\i. ~is_terminator i.inst_opcode /\ i.inst_opcode <> INVOKE) prefix /\
    EVERY (\i. ~is_terminator i.inst_opcode /\ i.inst_opcode <> INVOKE) exp_prefix /\
    (!k. k < LENGTH prefix ==> EL k bb.bb_instructions = EL k prefix) /\
    (!k. k < LENGTH exp_prefix ==> EL k exp_bb.bb_instructions = EL k exp_prefix) /\
    run_insts fuel ctx prefix s1 = OK s1_mid /\
    run_insts fuel ctx exp_prefix s2 = OK s2_mid /\
    is_terminator term.inst_opcode /\
    term.inst_opcode <> INVOKE /\
    ~reads_memory term.inst_opcode /\
    (!x. MEM (Var x) term.inst_operands ==> x NOTIN vars) ==>
    lift_result (ld_ok vars) (ld_equiv vars) (ld_equiv vars)
      (run_block fuel ctx bb s1)
      (run_block fuel ctx exp_bb s2)
Proof
  rpt strip_tac >>
  (* Factor run_block on s1 side *)
  `run_block fuel ctx bb s1 =
   run_block fuel ctx bb (s1_mid with vs_inst_idx := LENGTH prefix)` by
    (irule run_block_skip_prefix_idx0 >> simp[]) >>
  (* Factor run_block on s2 side *)
  `run_block fuel ctx exp_bb s2 =
   run_block fuel ctx exp_bb
     (s2_mid with vs_inst_idx := LENGTH exp_prefix)` by
    (irule run_block_skip_prefix_idx0 >> simp[]) >>
  pop_assum (fn th => REWRITE_TAC [th]) >>
  pop_assum (fn th => REWRITE_TAC [th]) >>
  (* Unfold run_block once on each side to get the terminator step *)
  ONCE_REWRITE_TAC[run_block_def] >>
  simp[get_instruction_def, EL_APPEND2] >>
  ONCE_REWRITE_TAC[step_inst_def] >> simp[] >>
  (* Use ld_ok_terminator_idx_override: handles different vs_inst_idx *)
  irule ld_ok_terminator_idx_override >> simp[]
QED

(* Helper: non-OK case for ld_block_sim — run_block propagates
   Error/Halt/Abort/IntRet from prefix, lift_result is preserved *)
Theorem ld_block_sim_non_ok[local]:
  !fuel ctx bb exp_bb prefix exp_prefix term vars s1 s2.
    s1.vs_inst_idx = 0 /\ s2.vs_inst_idx = 0 /\
    bb.bb_instructions = prefix ++ [term] /\
    exp_bb.bb_instructions = exp_prefix ++ [term] /\
    LENGTH prefix < LENGTH bb.bb_instructions /\
    LENGTH exp_prefix < LENGTH exp_bb.bb_instructions /\
    EVERY (\i. ~is_terminator i.inst_opcode /\ i.inst_opcode <> INVOKE) prefix /\
    EVERY (\i. ~is_terminator i.inst_opcode /\ i.inst_opcode <> INVOKE) exp_prefix /\
    (!k. k < LENGTH prefix ==> EL k bb.bb_instructions = EL k prefix) /\
    (!k. k < LENGTH exp_prefix ==> EL k exp_bb.bb_instructions = EL k exp_prefix) /\
    (!s1_mid. run_insts fuel ctx prefix s1 <> OK s1_mid) /\
    lift_result (ld_ok vars) (ld_equiv vars) (ld_equiv vars)
      (run_insts fuel ctx prefix s1)
      (run_insts fuel ctx exp_prefix s2) ==>
    lift_result (ld_ok vars) (ld_equiv vars) (ld_equiv vars)
      (run_block fuel ctx bb s1)
      (run_block fuel ctx exp_bb s2)
Proof
  rpt strip_tac >>
  Cases_on `run_insts fuel ctx prefix s1`
  (* OK — contradicts !s1_mid. ... <> OK s1_mid *)
  >- metis_tac[]
  (* Halt *)
  >- (
    rename1 `run_insts _ _ prefix s1 = Halt v1` >>
    `?v2. run_insts fuel ctx exp_prefix s2 = Halt v2 /\
          ld_equiv vars v1 v2` by
      (Cases_on `run_insts fuel ctx exp_prefix s2` >>
       gvs[lift_result_def]) >>
    `?j1. run_block fuel ctx bb s1 = Halt (v1 with vs_inst_idx := j1)` by
      (irule run_block_prefix_halt_idx0 >>
       conj_tac >- simp[] >>
       qexists_tac `prefix` >> simp[]) >>
    `?j2. run_block fuel ctx exp_bb s2 = Halt (v2 with vs_inst_idx := j2)` by
      (irule run_block_prefix_halt_idx0 >>
       conj_tac >- simp[] >>
       qexists_tac `exp_prefix` >> simp[]) >>
    gvs[lift_result_def] >> irule ld_equiv_idx_indep >> simp[]
  )
  (* Abort *)
  >- (
    rename1 `run_insts _ _ prefix s1 = Abort a1 v1` >>
    `?v2. run_insts fuel ctx exp_prefix s2 = Abort a1 v2 /\
          ld_equiv vars v1 v2` by
      (Cases_on `run_insts fuel ctx exp_prefix s2` >>
       gvs[lift_result_def]) >>
    `?j1. run_block fuel ctx bb s1 = Abort a1 (v1 with vs_inst_idx := j1)` by
      (irule run_block_prefix_abort_idx0 >>
       conj_tac >- simp[] >>
       qexists_tac `prefix` >> simp[]) >>
    `?j2. run_block fuel ctx exp_bb s2 =
          Abort a1 (v2 with vs_inst_idx := j2)` by
      (irule run_block_prefix_abort_idx0 >>
       conj_tac >- simp[] >>
       qexists_tac `exp_prefix` >> simp[]) >>
    gvs[lift_result_def] >> irule ld_equiv_idx_indep >> simp[]
  )
  (* IntRet *)
  >- (
    rename1 `run_insts _ _ prefix s1 = IntRet l1 v1` >>
    `?v2. run_insts fuel ctx exp_prefix s2 = IntRet l1 v2 /\
          ld_equiv vars v1 v2` by
      (Cases_on `run_insts fuel ctx exp_prefix s2` >>
       gvs[lift_result_def]) >>
    `?j1. run_block fuel ctx bb s1 = IntRet l1 (v1 with vs_inst_idx := j1)` by
      (irule run_block_prefix_intret_idx0 >>
       conj_tac >- simp[] >>
       qexists_tac `prefix` >> simp[]) >>
    `?j2. run_block fuel ctx exp_bb s2 =
          IntRet l1 (v2 with vs_inst_idx := j2)` by
      (irule run_block_prefix_intret_idx0 >>
       conj_tac >- simp[] >>
       qexists_tac `exp_prefix` >> simp[]) >>
    gvs[lift_result_def] >> irule ld_equiv_idx_indep >> simp[]
  )
  (* Error — last constructor *)
  >>
  rename1 `run_insts _ _ prefix s1 = Error err1` >>
  `run_block fuel ctx bb s1 = Error err1` by
    (irule run_block_prefix_error_idx0 >>
     conj_tac >- simp[] >>
     qexists_tac `prefix` >> simp[]) >>
  `?e2. run_insts fuel ctx exp_prefix s2 = Error e2` by
    (Cases_on `run_insts fuel ctx exp_prefix s2` >>
     gvs[lift_result_def]) >>
  `run_block fuel ctx exp_bb s2 = Error e2` by
    (irule run_block_prefix_error_idx0 >>
     conj_tac >- simp[] >>
     qexists_tac `exp_prefix` >> simp[]) >>
  gvs[lift_result_def]
QED

Theorem ld_block_sim[local]:
  !fn bb fuel ctx s1 s2.
    ld_ok (ld_exempt_vars_fn fn) s1 s2 /\
    s1.vs_inst_idx = 0 /\
    wf_function fn /\ fn_inst_wf fn /\
    code_layout_valid s1 /\ code_layout_valid s2 /\
    ld_no_mem_read fn /\ ld_dload_safe fn /\
    ld_no_original_alloca fn /\
    MEM bb fn.fn_blocks /\
    (!bb' inst x.
       MEM bb' fn.fn_blocks /\ MEM inst bb'.bb_instructions /\
       MEM (Var x) inst.inst_operands ==>
       x NOTIN ld_fresh_vars_fn fn) ==>
    lift_result (ld_ok (ld_exempt_vars_fn fn)) (ld_equiv (ld_exempt_vars_fn fn)) (ld_equiv (ld_exempt_vars_fn fn))
      (run_block fuel ctx bb s1)
      (run_block fuel ctx (lower_dload_block bb) s2)
Proof
  rpt strip_tac >>
  `ld_exempt_vars_fn fn = ld_fresh_vars_fn fn` by
    simp[ld_exempt_vars_fn_def] >>
  (* Eliminate ld_exempt_vars_fn fn from goal and assumptions *)
  pop_assum (fn eq =>
    PURE_REWRITE_TAC [eq] >>
    RULE_ASSUM_TAC (PURE_REWRITE_RULE [eq])) >>
  qabbrev_tac `vars = ld_fresh_vars_fn fn` >>
  (`bb_well_formed bb` by fs[wf_function_def]) >>
  (`bb.bb_instructions <> []` by fs[bb_well_formed_def]) >>
  qabbrev_tac `prefix = BUTLAST bb.bb_instructions` >>
  qabbrev_tac `term = LAST bb.bb_instructions` >>
  (`bb.bb_instructions = prefix ++ [term]` by
    metis_tac[APPEND_BUTLAST_LAST]) >>
  (`is_terminator term.inst_opcode` by
    fs[bb_well_formed_def, Abbr `term`]) >>
  (`EVERY (\i. ~is_terminator i.inst_opcode) prefix` by
    metis_tac[wf_block_butlast_non_term]) >>
  (`!inst. MEM inst bb.bb_instructions ==>
     ~reads_memory inst.inst_opcode /\ inst.inst_opcode <> INVOKE` by
    (rpt strip_tac >>
     fs[ld_no_mem_read_def] >> res_tac >>
     CCONTR_TAC >> gvs[] >> res_tac >> gvs[reads_memory_def])) >>
  (`EVERY (\i. ~is_terminator i.inst_opcode /\ i.inst_opcode <> INVOKE /\
              ~reads_memory i.inst_opcode) prefix` by
    (irule EVERY_MEM_MONO >> qexists_tac `\i. ~is_terminator i.inst_opcode` >>
     simp[] >> rpt strip_tac >>
     `MEM x bb.bb_instructions` by metis_tac[MEM_APPEND, MEM] >>
     res_tac)) >>
  (`EVERY (\i. ~is_terminator i.inst_opcode /\ i.inst_opcode <> INVOKE) prefix` by
    (irule EVERY_MEM_MONO >>
     qexists_tac `\i. ~is_terminator i.inst_opcode /\ i.inst_opcode <> INVOKE /\
                       ~reads_memory i.inst_opcode` >>
     simp[])) >>
  (`term.inst_opcode <> INVOKE` by
    (`MEM term bb.bb_instructions` by metis_tac[MEM_APPEND, MEM] >>
     res_tac)) >>
  (`~reads_memory term.inst_opcode` by
    (`MEM term bb.bb_instructions` by metis_tac[MEM_APPEND, MEM] >>
     fs[ld_no_mem_read_def] >> res_tac)) >>
  (`s2.vs_inst_idx = 0` by fs[ld_ok_def]) >>
  (`EVERY inst_wf prefix` by
    (simp[EVERY_MEM] >> rpt strip_tac >>
     `MEM e bb.bb_instructions` by metis_tac[MEM_APPEND, MEM] >>
     fs[fn_inst_wf_def] >> metis_tac[])) >>
  (`!inst. MEM inst prefix ==> inst.inst_opcode <> ALLOCA` by
    (rpt strip_tac >>
     `MEM inst bb.bb_instructions` by metis_tac[MEM_APPEND, MEM] >>
     fs[ld_no_original_alloca_def] >> metis_tac[])) >>
  (`term.inst_opcode <> DLOAD /\ term.inst_opcode <> DLOADBYTES` by
    (Cases_on `term.inst_opcode` >> gvs[is_terminator_def])) >>
  (`lower_dload_inst term = [term]` by
    (irule lower_dload_inst_passthrough >> simp[])) >>
  (`inst_wf term` by
    (`MEM term bb.bb_instructions` by metis_tac[MEM_APPEND, MEM] >>
     fs[fn_inst_wf_def] >> metis_tac[])) >>
  (`!x. MEM (Var x) term.inst_operands ==> x NOTIN vars` by
    (`MEM term bb.bb_instructions` by metis_tac[MEM_APPEND, MEM] >>
     rpt strip_tac >> first_x_assum drule >> simp[] >> metis_tac[])) >>
  (`LENGTH prefix < LENGTH bb.bb_instructions` by
    gvs[]) >>
  (`!k. k < LENGTH prefix ==>
      EL k bb.bb_instructions = EL k prefix` by
    (rpt strip_tac >> gvs[EL_APPEND1])) >>
  (* EL preconditions for expanded block *)
  qabbrev_tac `exp_bb = lower_dload_block bb` >>
  (`exp_bb.bb_instructions =
      FLAT (MAP lower_dload_inst prefix) ++ [term]` by
    (simp[Abbr `exp_bb`, lower_dload_block_def] >>
     gvs[MAP_APPEND, FLAT_APPEND])) >>
  qabbrev_tac `exp_prefix = FLAT (MAP lower_dload_inst prefix)` >>
  (`EVERY (\i. ~is_terminator i.inst_opcode /\ i.inst_opcode <> INVOKE)
      exp_prefix` by
    (simp[Abbr `exp_prefix`] >>
     irule lower_dload_inst_every_non_term >> gvs[EVERY_MEM] >>
     metis_tac[])) >>
  (`LENGTH exp_prefix < LENGTH exp_bb.bb_instructions` by
    gvs[]) >>
  (`!k. k < LENGTH exp_prefix ==>
      EL k exp_bb.bb_instructions = EL k exp_prefix` by
    (rpt strip_tac >> gvs[EL_APPEND1])) >>
  (* ld_run_insts_sim: apply ld_prefix_sim to prefix *)
  `lift_result (ld_ok vars) (ld_equiv vars) (ld_equiv vars)
      (run_insts fuel ctx prefix s1)
      (run_insts fuel ctx exp_prefix s2)` by
    (simp[Abbr `exp_prefix`] >>
     irule ld_prefix_sim >> metis_tac[]) >>
  Cases_on `run_insts fuel ctx prefix s1`
  >~ [`OK s1_mid`]
  >- (
    (* OK branch *)
    Cases_on `run_insts fuel ctx exp_prefix s2` >>
    fs[lift_result_def] >>
    rename1 `run_insts _ _ exp_prefix s2 = OK s2_mid` >>
    `lift_result (ld_ok vars) (ld_equiv vars) (ld_equiv vars)
       (run_block fuel ctx bb s1)
       (run_block fuel ctx exp_bb s2)` by
      (irule ld_block_sim_ok >>
       conj_tac >- simp[] >>
       conj_tac >- simp[] >>
       qexistsl_tac [`exp_prefix`, `prefix`, `s1_mid`, `s2_mid`, `term`] >>
       simp[]) >>
    gvs[]
  )
  (* Handle all non-OK cases *)
  >> (
    irule ld_block_sim_non_ok >>
    conj_tac >- simp[] >>
    (conj_tac >- simp[]) >>
    qexistsl_tac [`exp_prefix`, `prefix`, `term`] >>
    simp[]
  )
QED

(* ===== Main theorem: two-state strengthened induction ===== *)

Theorem ld_main_two_state[local]:
  !fn.
    wf_function fn /\ fn_inst_wf fn /\
    ld_no_mem_read fn /\ ld_dload_safe fn /\
    ld_no_original_alloca fn /\
    (!bb inst x.
       MEM bb fn.fn_blocks /\ MEM inst bb.bb_instructions /\
       MEM (Var x) inst.inst_operands ==>
       x NOTIN ld_fresh_vars_fn fn) ==>
    !fuel ctx s1 s2.
      ld_ok (ld_exempt_vars_fn fn) s1 s2 /\
      s1.vs_inst_idx = 0 /\
      code_layout_valid s1 /\ code_layout_valid s2 ==>
      lift_result (ld_ok (ld_exempt_vars_fn fn))
                  (ld_equiv (ld_exempt_vars_fn fn))
        (run_function fuel ctx fn s1)
        (run_function fuel ctx (lower_dload_function fn) s2)
Proof
  strip_tac >> strip_tac >>
  Induct_on `fuel`
  >- (rw[] >> ONCE_REWRITE_TAC [run_function_def] >> simp[lift_result_def]) >>
  rpt strip_tac >>
  ONCE_REWRITE_TAC [run_function_def] >> simp[] >>
  (Q.SUBGOAL_THEN `s2.vs_current_bb = s1.vs_current_bb`
    SUBST_ALL_TAC >- fs[ld_ok_def]) >>
  simp[lower_dload_function_blocks, lookup_block_lower_dload] >>
  Cases_on `lookup_block s1.vs_current_bb fn.fn_blocks`
  >- simp[lift_result_def] >>
  rename1 `_ = SOME bb` >> simp[] >>
  drule lookup_block_MEM >> strip_tac >>
  (Q.SUBGOAL_THEN
    `lift_result (ld_ok (ld_exempt_vars_fn fn))
                 (ld_equiv (ld_exempt_vars_fn fn))
      (run_block fuel ctx bb s1)
      (run_block fuel ctx (lower_dload_block bb) s2)`
    STRIP_ASSUME_TAC >- (irule ld_block_sim >> metis_tac[])) >>
  Cases_on `run_block fuel ctx bb s1` >>
  Cases_on `run_block fuel ctx (lower_dload_block bb) s2` >>
  gvs[lift_result_def] >>
  rename1 `run_block _ _ bb s1 = OK v1` >>
  rename1 `run_block _ _ _ s2 = OK v2` >>
  (Q.SUBGOAL_THEN `v1.vs_halted <=> v2.vs_halted`
    STRIP_ASSUME_TAC >- fs[ld_ok_def]) >>
  simp[] >> Cases_on `v1.vs_halted` >> gvs[]
  >- (fs[ld_ok_def, ld_equiv_def, lift_result_def]) >>
  first_x_assum irule >> simp[] >>
  metis_tac[run_block_OK_inst_idx_0,
            run_block_preserves_code_layout_valid,
            run_block_preserves_layout_fields,
            code_layout_valid_def]
QED

(* ===== Main theorem ===== *)

Theorem lower_dload_function_correct_proof:
  !fuel ctx fn s.
    wf_function fn /\ fn_inst_wf fn /\ code_layout_valid s /\
    ld_no_mem_read fn /\ ld_dload_safe fn /\
    ld_no_original_alloca fn /\
    (!bb inst x.
       MEM bb fn.fn_blocks /\ MEM inst bb.bb_instructions /\
       MEM (Var x) inst.inst_operands ==>
       x NOTIN ld_fresh_vars_fn fn) /\
    s.vs_inst_idx = 0 ==>
    lift_result
      (ld_ok (ld_exempt_vars_fn fn))
      (ld_equiv (ld_exempt_vars_fn fn))
      (run_function fuel ctx fn s)
      (run_function fuel ctx (lower_dload_function fn) s)
Proof
  rpt strip_tac >>
  irule ld_main_two_state >> simp[ld_ok_refl] >>
  metis_tac[]
QED
