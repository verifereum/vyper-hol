(*
 * Venom Semantic Properties
 *
 * General semantic lemmas useful for any optimization pass.
 * Contains properties of bool_to_word and instruction behavior lemmas.
 *
 * After the step_inst refactor, step_inst_base handles individual opcodes
 * (no INVOKE), while step_inst fuel ctx handles all opcodes including INVOKE.
 * Most behavior lemmas are about step_inst_base; the new step_inst delegates
 * to step_inst_base for non-INVOKE via step_inst_non_invoke.
 *)

Theory venomExecProofs
Ancestors
  venomExecSemantics venomInst venomState rich_list list

(* ==========================================================================
   bool_to_word Properties
   ========================================================================== *)

Theorem bool_to_word_T:
  bool_to_word T = 1w
Proof
  simp[bool_to_word_def]
QED

Theorem bool_to_word_F:
  bool_to_word F = 0w
Proof
  simp[bool_to_word_def]
QED

Theorem bool_to_word_eq_0w[local]:
  (bool_to_word b = 0w) <=> ~b
Proof
  Cases_on `b` >> simp[bool_to_word_def]
QED

Theorem bool_to_word_neq_0w[local]:
  (bool_to_word b <> 0w) <=> b
Proof
  Cases_on `b` >> simp[bool_to_word_def]
QED

(* ==========================================================================
   step_inst_base Behavior Lemmas (specific opcodes)
   ========================================================================== *)

Theorem step_iszero_value:
  !s cond_op out id cond.
    eval_operand cond_op s = SOME cond ==>
    step_inst_base <| inst_id := id; inst_opcode := ISZERO;
                 inst_operands := [cond_op]; inst_outputs := [out] |> s =
    OK (update_var out (bool_to_word (cond = 0w)) s)
Proof
  rw[step_inst_base_def, exec_pure1_def]
QED

Theorem step_assert_behavior:
  !s cond_op id cond.
    eval_operand cond_op s = SOME cond ==>
    step_inst_base <| inst_id := id; inst_opcode := ASSERT;
                 inst_operands := [cond_op]; inst_outputs := [] |> s =
    if cond = 0w then
      Abort Revert_abort (revert_state (set_returndata [] s))
    else OK s
Proof
  rw[step_inst_base_def]
QED

Theorem step_revert_behavior:
  !s off_op sz_op id off sz.
    eval_operand off_op s = SOME off /\
    eval_operand sz_op s = SOME sz ==>
    step_inst_base <| inst_id := id; inst_opcode := REVERT;
                 inst_operands := [off_op; sz_op]; inst_outputs := [] |> s =
    Abort Revert_abort
      (revert_state
        (set_returndata
          (TAKE (w2n sz) (DROP (w2n off) s.vs_memory ++ REPLICATE (w2n sz) 0w))
          s))
Proof
  rw[step_inst_base_def]
QED

Theorem step_jmp_behavior:
  !s lbl id.
    step_inst_base <| inst_id := id; inst_opcode := JMP;
                 inst_operands := [Label lbl]; inst_outputs := [] |> s =
    OK (jump_to lbl s)
Proof
  rw[step_inst_base_def]
QED

Theorem step_jnz_behavior:
  !s cond_op if_nonzero if_zero id cond.
    eval_operand cond_op s = SOME cond ==>
    step_inst_base <| inst_id := id; inst_opcode := JNZ;
                 inst_operands := [cond_op; Label if_nonzero; Label if_zero];
                 inst_outputs := [] |> s =
    if cond <> 0w then OK (jump_to if_nonzero s)
    else OK (jump_to if_zero s)
Proof
  rw[step_inst_base_def]
QED

(* ==========================================================================
   block_step / run_block Properties
   ========================================================================== *)

Theorem block_step_increments_idx:
  !bb s v.
    block_step bb s = (OK v, F)
    ==>
    v.vs_inst_idx = SUC s.vs_inst_idx
Proof
  rw[block_step_def] >>
  Cases_on `get_instruction bb s.vs_inst_idx` >> gvs[] >>
  Cases_on `step_inst_base x s` >> gvs[] >>
  Cases_on `is_terminator x.inst_opcode` >> gvs[next_inst_def] >>
  `v'.vs_inst_idx = s.vs_inst_idx` by (
    drule_all step_inst_base_preserves_inst_idx >> simp[]
  ) >>
  simp[]
QED

Theorem run_block_OK_not_halted:
  !fuel ctx bb s v. run_block fuel ctx bb s = OK v ==> ~v.vs_halted
Proof
  ho_match_mp_tac (cj 2 run_defs_ind) >>
  qexists_tac `\fuel ctx inst s. T` >>
  qexists_tac `\fuel ctx fn s. T` >> simp[] >>
  rpt gen_tac >> strip_tac >>
  simp[Once run_block_def] >>
  Cases_on `get_instruction bb s.vs_inst_idx` >> simp[] >>
  rename1 `SOME inst` >>
  Cases_on `step_inst fuel ctx inst s` >> simp[] >>
  rw[] >> gvs[]
QED

Theorem run_block_OK_inst_idx_0:
  !fuel ctx bb s v. run_block fuel ctx bb s = OK v ==> v.vs_inst_idx = 0
Proof
  ho_match_mp_tac (cj 2 run_defs_ind) >>
  qexists_tac `\fuel ctx inst s. T` >>
  qexists_tac `\fuel ctx fn s. T` >> simp[] >>
  rpt gen_tac >> strip_tac >>
  simp[Once run_block_def] >>
  Cases_on `get_instruction bb s.vs_inst_idx` >> simp[] >>
  rename1 `SOME inst` >>
  Cases_on `step_inst fuel ctx inst s` >> simp[] >>
  rw[] >> gvs[] >>
  Cases_on `is_terminator inst.inst_opcode` >> gvs[] >>
  (* terminator case: step_inst returned OK, must be JMP/JNZ/DJMP *)
  qpat_x_assum `is_terminator _` mp_tac >>
  simp[is_terminator_def] >>
  Cases_on `inst.inst_opcode` >> gvs[is_terminator_def] >>
  qpat_x_assum `step_inst _ _ _ _ = _` mp_tac >>
  simp[Once step_inst_def, step_inst_base_def, jump_to_def] >>
  gvs[AllCaseEqs(), PULL_EXISTS] >> rw[] >> gvs[]
QED

(* step_inst_base returns Error for INVOKE *)
Theorem step_inst_base_OK_not_INVOKE:
  step_inst_base inst s = OK s' ==> inst.inst_opcode <> INVOKE
Proof
  strip_tac >> strip_tac >> gvs[step_inst_base_def]
QED

Theorem step_inst_base_Halt_not_INVOKE:
  step_inst_base inst s = Halt v ==> inst.inst_opcode <> INVOKE
Proof
  strip_tac >> strip_tac >> gvs[step_inst_base_def]
QED

Theorem step_inst_base_Abort_not_INVOKE:
  step_inst_base inst s = Abort a v ==> inst.inst_opcode <> INVOKE
Proof
  strip_tac >> strip_tac >> gvs[step_inst_base_def]
QED

Theorem step_inst_base_IntRet_not_INVOKE:
  step_inst_base inst s = IntRet vals v ==> inst.inst_opcode <> INVOKE
Proof
  strip_tac >> strip_tac >> gvs[step_inst_base_def]
QED

(* Backward compat aliases (about step_inst_base, not the new step_inst) *)
Theorem step_inst_OK_not_INVOKE:
  step_inst_base inst s = OK s' ==> inst.inst_opcode <> INVOKE
Proof
  ACCEPT_TAC step_inst_base_OK_not_INVOKE
QED

Theorem step_inst_Halt_not_INVOKE:
  step_inst_base inst s = Halt v ==> inst.inst_opcode <> INVOKE
Proof
  ACCEPT_TAC step_inst_base_Halt_not_INVOKE
QED

Theorem step_inst_Abort_not_INVOKE:
  step_inst_base inst s = Abort a v ==> inst.inst_opcode <> INVOKE
Proof
  ACCEPT_TAC step_inst_base_Abort_not_INVOKE
QED

Theorem step_inst_IntRet_not_INVOKE:
  step_inst_base inst s = IntRet vals v ==> inst.inst_opcode <> INVOKE
Proof
  ACCEPT_TAC step_inst_base_IntRet_not_INVOKE
QED

(* extract_venom_result preserves vs_halted *)
Triviality extract_venom_result_preserves_halted:
  extract_venom_result s ov ro rs rr = SOME (out, s') ==>
  s'.vs_halted = s.vs_halted
Proof
  simp[extract_venom_result_def, AllCaseEqs()] >> rw[] >> gvs[] >>
  pairarg_tac >> gvs[]
QED

(* step_inst_base OK preserves vs_halted *)
Theorem step_inst_base_OK_preserves_halted:
  step_inst_base inst s = OK s' ==> s'.vs_halted = s.vs_halted
Proof
  Cases_on `inst.inst_opcode` >>
  simp[step_inst_base_def, AllCaseEqs()] >> rw[] >>
  gvs[exec_pure1_def, exec_pure2_def, exec_pure3_def,
      exec_read0_def, exec_read1_def, exec_write2_def,
      update_var_def, AllCaseEqs(), jump_to_def,
      mstore_def, mload_def, sstore_def, sload_def,
      tstore_def, tload_def, write_memory_with_expansion_def,
      mcopy_def, exec_alloca_def,
      exec_ext_call_def, exec_delegatecall_def, exec_create_def] >>
  imp_res_tac extract_venom_result_preserves_halted >> gvs[update_var_def]
QED

(* Backward compat alias *)
Theorem step_inst_OK_preserves_halted:
  step_inst_base inst s = OK s' ==> s'.vs_halted = s.vs_halted
Proof
  ACCEPT_TAC step_inst_base_OK_preserves_halted
QED

(* For non-INVOKE blocks, run_block unfolds through block_step *)
Theorem run_block_block_step:
  !fuel ctx bb s.
    EVERY (\inst. inst.inst_opcode <> INVOKE) bb.bb_instructions ==>
    run_block fuel ctx bb s =
      let (r, t) = block_step bb s in
      case r of
        OK s' => if t then (if s'.vs_halted then Halt s' else OK s')
                 else run_block fuel ctx bb s'
      | Halt s' => Halt s'
      | Abort a s' => Abort a s'
      | Error e => Error e
      | IntRet vals s' => IntRet vals s'
Proof
  rw[block_step_def, LET_THM] >>
  simp[Once run_block_def] >>
  Cases_on `get_instruction bb s.vs_inst_idx` >> simp[] >>
  rename1 `get_instruction bb _ = SOME inst` >>
  `inst.inst_opcode <> INVOKE` by
    (gvs[listTheory.EVERY_MEM, get_instruction_def] >>
     first_x_assum irule >> irule listTheory.EL_MEM >> simp[]) >>
  simp[Once step_inst_def] >>
  Cases_on `step_inst_base inst s` >> simp[] >>
  Cases_on `is_terminator inst.inst_opcode` >> simp[] >>
  (* non-terminator OK: relate new continuation to next_inst *)
  `v.vs_inst_idx = s.vs_inst_idx` by
    (drule step_inst_base_preserves_inst_idx >> simp[]) >>
  simp[next_inst_def, arithmeticTheory.ADD1]
QED

(* ==========================================================================
   FIND Lemmas
   ========================================================================== *)

Triviality FIND_MEM:
  !P l x. FIND P l = SOME x ==> MEM x l
Proof
  Induct_on `l` >> simp[FIND_thm] >> rw[] >> metis_tac[]
QED

Triviality FIND_P:
  !P l x. FIND P l = SOME x ==> P x
Proof
  Induct_on `l` >> simp[FIND_thm] >> rw[] >> metis_tac[]
QED

Triviality FIND_NONE:
  !P l. FIND P l = NONE ==> ~EXISTS P l
Proof
  Induct_on `l` >> simp[FIND_thm] >> rw[] >> gvs[]
QED

(* ==========================================================================
   Lookup Helpers
   ========================================================================== *)

Theorem lookup_block_MEM:
  !lbl bbs bb.
    lookup_block lbl bbs = SOME bb ==> MEM bb bbs
Proof
  rw[lookup_block_def] >> drule FIND_MEM >> simp[]
QED

Theorem run_block_invoke_cases:
  !fuel ctx bb1 bb2 s inst.
    get_instruction bb1 s.vs_inst_idx = SOME inst /\
    get_instruction bb2 s.vs_inst_idx = SOME inst /\
    inst.inst_opcode = INVOKE ==>
    (run_block fuel ctx bb1 s = run_block fuel ctx bb2 s) \/
    (?s'. run_block fuel ctx bb1 s = run_block fuel ctx bb1 (next_inst s') /\
          run_block fuel ctx bb2 s = run_block fuel ctx bb2 (next_inst s') /\
          s'.vs_inst_idx = s.vs_inst_idx /\
          s'.vs_halted = s.vs_halted)
Proof
  rpt gen_tac >> strip_tac >>
  qabbrev_tac `res = step_inst fuel ctx inst s` >>
  `run_block fuel ctx bb1 s =
    case res of
      OK s' =>
        if is_terminator inst.inst_opcode then
          if s'.vs_halted then Halt s' else OK s'
        else run_block fuel ctx bb1 (s' with vs_inst_idx := SUC s.vs_inst_idx)
    | IntRet v s' => IntRet v s'
    | Halt s' => Halt s'
    | Abort a s' => Abort a s'
    | Error e => Error e`
    by simp[Once run_block_def, Abbr `res`] >>
  `run_block fuel ctx bb2 s =
    case res of
      OK s' =>
        if is_terminator inst.inst_opcode then
          if s'.vs_halted then Halt s' else OK s'
        else run_block fuel ctx bb2 (s' with vs_inst_idx := SUC s.vs_inst_idx)
    | IntRet v s' => IntRet v s'
    | Halt s' => Halt s'
    | Abort a s' => Abort a s'
    | Error e => Error e`
    by simp[Once run_block_def, Abbr `res`] >>
  Cases_on `res` >> gvs[]
  >- ((* OK: INVOKE is not a terminator *)
      `~is_terminator inst.inst_opcode` by simp[is_terminator_def] >> gvs[] >>
      DISJ2_TAC >>
      rename1 `step_inst fuel ctx inst s = OK v` >>
      qexists_tac `v` >>
      imp_res_tac step_inst_preserves_inst_idx >> gvs[] >>
      simp[next_inst_def, arithmeticTheory.ADD1] >>
      (* vs_halted: need step_inst INVOKE OK preserves halted *)
      qpat_x_assum `step_inst _ _ _ _ = OK _` mp_tac >>
      simp[Once step_inst_def] >>
      gvs[AllCaseEqs()] >> rw[] >>
      imp_res_tac bind_outputs_inst_idx >>
      gvs[merge_callee_state_def, bind_outputs_def] >>
      qsuff_tac
        `!l acc. acc.vs_halted = s.vs_halted ==>
           (FOLDL (\s' (out,val). update_var out val s') acc l).vs_halted =
           s.vs_halted`
      >- (disch_then irule >> simp[])
      >> Induct >> simp[] >> Cases >> simp[update_var_def])
  >> (* IntRet/Halt/Abort/Error: both sides equal *)
     DISJ1_TAC >> simp[]
QED

Theorem block_step_prefix_same:
  !bb1 bb2 s n.
    TAKE (SUC n) bb1.bb_instructions = TAKE (SUC n) bb2.bb_instructions /\
    s.vs_inst_idx = n /\
    n < LENGTH bb1.bb_instructions /\
    n < LENGTH bb2.bb_instructions
  ==>
    block_step bb1 s = block_step bb2 s
Proof
  rw[block_step_def, get_instruction_def] >>
  `EL s.vs_inst_idx bb1.bb_instructions = EL s.vs_inst_idx bb2.bb_instructions` by (
    `EL s.vs_inst_idx (TAKE (SUC s.vs_inst_idx) bb1.bb_instructions) =
     EL s.vs_inst_idx (TAKE (SUC s.vs_inst_idx) bb2.bb_instructions)` by simp[] >>
    metis_tac[EL_TAKE, DECIDE ``n < SUC n``]
  ) >>
  simp[]
QED
