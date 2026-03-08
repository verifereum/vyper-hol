(*
 * Venom Semantic Properties
 *
 * General semantic lemmas useful for any optimization pass.
 * Contains properties of bool_to_word and instruction behavior lemmas.
 *)

Theory venomExecProofs
Ancestors
  venomExecSemantics venomInst venomState rich_list list

(* ==========================================================================
   bool_to_word Properties

   WHY THESE ARE TRUE: bool_to_word is defined as:
     bool_to_word T = 1w
     bool_to_word F = 0w
   So bool_to_word b = 0w iff b = F iff ~b.
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
   Instruction Behavior Lemmas
   ========================================================================== *)

(* WHY THIS IS TRUE: By step_inst_def, ISZERO uses exec_pure1 with
   (\x. bool_to_word (x = 0w)). exec_pure1 evaluates the single operand,
   applies the function, and updates the output variable. *)
Theorem step_iszero_value:
  !s cond_op out id cond.
    eval_operand cond_op s = SOME cond ==>
    step_inst <| inst_id := id; inst_opcode := ISZERO;
                 inst_operands := [cond_op]; inst_outputs := [out] |> s =
    OK (update_var out (bool_to_word (cond = 0w)) s)
Proof
  rw[step_inst_def, exec_pure1_def]
QED

(* WHY THIS IS TRUE: By step_inst_def, ASSERT evaluates its operand.
   If cond = 0w, it aborts with empty returndata.
   If cond <> 0w, it returns OK s. *)
Theorem step_assert_behavior:
  !s cond_op id cond.
    eval_operand cond_op s = SOME cond ==>
    step_inst <| inst_id := id; inst_opcode := ASSERT;
                 inst_operands := [cond_op]; inst_outputs := [] |> s =
    if cond = 0w then
      Abort Revert_abort (revert_state (set_returndata [] s))
    else OK s
Proof
  rw[step_inst_def]
QED

(* WHY THIS IS TRUE: By step_inst_def, REVERT evaluates offset and size
   operands, reads returndata from memory, and aborts with Revert_abort. *)
Theorem step_revert_behavior:
  !s off_op sz_op id off sz.
    eval_operand off_op s = SOME off /\
    eval_operand sz_op s = SOME sz ==>
    step_inst <| inst_id := id; inst_opcode := REVERT;
                 inst_operands := [off_op; sz_op]; inst_outputs := [] |> s =
    Abort Revert_abort
      (revert_state
        (set_returndata
          (TAKE (w2n sz) (DROP (w2n off) s.vs_memory ++ REPLICATE (w2n sz) 0w))
          s))
Proof
  rw[step_inst_def]
QED

(* WHY THIS IS TRUE: By step_inst_def, JMP unconditionally jumps to the label. *)
Theorem step_jmp_behavior:
  !s lbl id.
    step_inst <| inst_id := id; inst_opcode := JMP;
                 inst_operands := [Label lbl]; inst_outputs := [] |> s =
    OK (jump_to lbl s)
Proof
  rw[step_inst_def]
QED

(* WHY THIS IS TRUE: By step_inst_def, JNZ evaluates the condition.
   If cond <> 0w, it jumps to if_nonzero; else to if_zero. *)
Theorem step_jnz_behavior:
  !s cond_op if_nonzero if_zero id cond.
    eval_operand cond_op s = SOME cond ==>
    step_inst <| inst_id := id; inst_opcode := JNZ;
                 inst_operands := [cond_op; Label if_nonzero; Label if_zero];
                 inst_outputs := [] |> s =
    if cond <> 0w then OK (jump_to if_nonzero s)
    else OK (jump_to if_zero s)
Proof
  rw[step_inst_def]
QED

(* ==========================================================================
   block_step / run_block Properties
   ========================================================================== *)

(* Helper: block_step with is_term=F increments vs_inst_idx *)
Theorem block_step_increments_idx:
  !bb s v.
    block_step bb s = (OK v, F)
    ==>
    v.vs_inst_idx = SUC s.vs_inst_idx
Proof
  rw[block_step_def] >>
  Cases_on `get_instruction bb s.vs_inst_idx` >> gvs[] >>
  Cases_on `step_inst x s` >> gvs[] >>
  Cases_on `is_terminator x.inst_opcode` >> gvs[next_inst_def] >>
  `v'.vs_inst_idx = s.vs_inst_idx` by (
    drule_all step_inst_preserves_inst_idx >> simp[]
  ) >>
  simp[]
QED

(*
 * Helper: run_block returning OK implies state is not halted.
 *
 * WHY THIS IS TRUE: The terminator path checks vs_halted and promotes to Halt.
 * Non-terminator steps preserve vs_halted. INVOKE path merges caller state
 * (which preserves vs_halted from before the call).
 *)
Theorem run_block_OK_not_halted:
  !fuel ctx bb s v. run_block fuel ctx bb s = OK v ==> ~v.vs_halted
Proof
  ho_match_mp_tac (cj 1 run_block_ind) >>
  qexists_tac `\fuel ctx fn s. T` >> rw[] >>
  rpt strip_tac >>
  qpat_x_assum `run_block _ _ _ _ = _` mp_tac >>
  simp[Once run_block_def] >>
  gvs[AllCaseEqs()] >> rw[] >> gvs[] >>
  TRY (first_x_assum (qspec_then `v` mp_tac) >> simp[] >> NO_TAC) >>
  Cases_on `inst.inst_opcode = INVOKE` >- simp[] >>
  disj2_tac >> rw[] >> CCONTR_TAC >> gvs[] >>
  `~v.vs_halted` by (first_x_assum irule >> qexists_tac `s'` >> simp[]) >>
  gvs[]
QED

(*
 * Helper: run_block returning OK implies vs_inst_idx = 0.
 *
 * WHY THIS IS TRUE: When run_block returns OK, a terminator executed.
 * JMP/JNZ use jump_to which sets vs_inst_idx := 0.
 *)
Theorem run_block_OK_inst_idx_0:
  !fuel ctx bb s v. run_block fuel ctx bb s = OK v ==> v.vs_inst_idx = 0
Proof
  ho_match_mp_tac (cj 1 run_block_ind) >>
  qexists_tac `\fuel ctx fn s. T` >> rw[] >>
  rpt strip_tac >>
  qpat_x_assum `run_block _ _ _ _ = _` mp_tac >>
  simp[Once run_block_def] >>
  gvs[AllCaseEqs()] >> rw[] >> gvs[] >>
  (* Terminator case: must be JMP/JNZ returning OK *)
  qpat_x_assum `is_terminator _` mp_tac >> simp[is_terminator_def] >>
  Cases_on `inst.inst_opcode` >> gvs[is_terminator_def] >>
  qpat_x_assum `step_inst _ _ = _` mp_tac >>
  simp[step_inst_def, jump_to_def] >>
  gvs[AllCaseEqs(), PULL_EXISTS] >> rw[] >> gvs[]
QED

(* step_inst returns Error for INVOKE (it's handled by run_block instead) *)
Theorem step_inst_OK_not_INVOKE:
  step_inst inst s = OK s' ==> inst.inst_opcode <> INVOKE
Proof
  strip_tac >> strip_tac >> gvs[step_inst_def]
QED

Theorem step_inst_Halt_not_INVOKE:
  step_inst inst s = Halt v ==> inst.inst_opcode <> INVOKE
Proof
  strip_tac >> strip_tac >> gvs[step_inst_def]
QED

Theorem step_inst_Abort_not_INVOKE:
  step_inst inst s = Abort a v ==> inst.inst_opcode <> INVOKE
Proof
  strip_tac >> strip_tac >> gvs[step_inst_def]
QED

Theorem step_inst_IntRet_not_INVOKE:
  step_inst inst s = IntRet vals v ==> inst.inst_opcode <> INVOKE
Proof
  strip_tac >> strip_tac >> gvs[step_inst_def]
QED

(* extract_venom_result preserves vs_halted *)
Triviality extract_venom_result_preserves_halted:
  extract_venom_result s ov ro rs rr = SOME (out, s') ==>
  s'.vs_halted = s.vs_halted
Proof
  simp[extract_venom_result_def, AllCaseEqs()] >> rw[] >> gvs[] >>
  pairarg_tac >> gvs[]
QED

(* step_inst OK preserves vs_halted: no OK-returning instruction modifies it *)
Theorem step_inst_OK_preserves_halted:
  step_inst inst s = OK s' ==> s'.vs_halted = s.vs_halted
Proof
  Cases_on `inst.inst_opcode` >>
  simp[step_inst_def, AllCaseEqs()] >> rw[] >>
  gvs[exec_pure1_def, exec_pure2_def, exec_pure3_def,
      exec_read0_def, exec_read1_def, exec_write2_def,
      update_var_def, AllCaseEqs(), jump_to_def,
      mstore_def, mload_def, sstore_def, sload_def,
      tstore_def, tload_def, write_memory_with_expansion_def,
      mcopy_def, exec_alloca_def,
      exec_ext_call_def, exec_delegatecall_def, exec_create_def] >>
  imp_res_tac extract_venom_result_preserves_halted >> gvs[update_var_def]
QED

(* Bridge: For non-INVOKE blocks, run_block unfolds through block_step.
   This connects the new run_block (which handles INVOKE inline) to the
   old block_step abstraction used by pass correctness proofs. *)
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
  simp[] >>
  Cases_on `step_inst inst s` >> simp[] >>
  Cases_on `is_terminator inst.inst_opcode` >> simp[]
QED

(* ==========================================================================
   FIND Lemmas (stdlib gaps — candidates for HOL4 upstream)
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

(* When two blocks share the same INVOKE instruction at the current index,
   both run_blocks follow the identical INVOKE dispatch path. They either
   produce the same terminal result or both continue at the same next state. *)
Theorem run_block_invoke_cases:
  !fuel ctx bb1 bb2 s inst.
    get_instruction bb1 s.vs_inst_idx = SOME inst /\
    get_instruction bb2 s.vs_inst_idx = SOME inst /\
    inst.inst_opcode = INVOKE ==>
    (* Either both produce the same terminal result *)
    (run_block fuel ctx bb1 s = run_block fuel ctx bb2 s) \/
    (* Or both continue at next_inst s' *)
    (?s'. run_block fuel ctx bb1 s = run_block fuel ctx bb1 (next_inst s') /\
          run_block fuel ctx bb2 s = run_block fuel ctx bb2 (next_inst s') /\
          s'.vs_inst_idx = s.vs_inst_idx /\
          s'.vs_halted = s.vs_halted)
Proof
  rw[] >>
  qabbrev_tac `r1 = run_block fuel ctx bb1 s` >>
  qabbrev_tac `r2 = run_block fuel ctx bb2 s` >>
  `r1 = (case decode_invoke inst of
           NONE => Error "invoke: bad operand format"
         | SOME (callee_name, arg_ops) =>
             case lookup_function callee_name ctx.ctx_functions of
               NONE => Error "invoke: function not found"
             | SOME callee_fn =>
                 case eval_operands arg_ops s of
                   NONE => Error "invoke: undefined argument"
                 | SOME args =>
                     case setup_callee callee_fn args s of
                       NONE => Error "invoke: empty function"
                     | SOME callee_s =>
                         case run_function fuel ctx callee_fn callee_s of
                           IntRet vals callee_s' =>
                             (case bind_outputs inst.inst_outputs vals
                                     (merge_callee_state s callee_s') of
                               SOME s' => run_block fuel ctx bb1 (next_inst s')
                             | NONE => Error "invoke: return arity mismatch")
                         | Halt s' => Halt s'
                         | Abort a s' => Abort a s'
                         | Error e => Error e
                         | OK _ => Error "invoke: callee did not return")` by
    (qunabbrev_tac `r1` >> simp[Once run_block_def]) >>
  `r2 = (case decode_invoke inst of
           NONE => Error "invoke: bad operand format"
         | SOME (callee_name, arg_ops) =>
             case lookup_function callee_name ctx.ctx_functions of
               NONE => Error "invoke: function not found"
             | SOME callee_fn =>
                 case eval_operands arg_ops s of
                   NONE => Error "invoke: undefined argument"
                 | SOME args =>
                     case setup_callee callee_fn args s of
                       NONE => Error "invoke: empty function"
                     | SOME callee_s =>
                         case run_function fuel ctx callee_fn callee_s of
                           IntRet vals callee_s' =>
                             (case bind_outputs inst.inst_outputs vals
                                     (merge_callee_state s callee_s') of
                               SOME s' => run_block fuel ctx bb2 (next_inst s')
                             | NONE => Error "invoke: return arity mismatch")
                         | Halt s' => Halt s'
                         | Abort a s' => Abort a s'
                         | Error e => Error e
                         | OK _ => Error "invoke: callee did not return")` by
    (qunabbrev_tac `r2` >> simp[Once run_block_def]) >>
  Cases_on `decode_invoke inst` >> gvs[] >>
  rename1 `SOME di` >> Cases_on `di` >>
  rename1 `SOME (callee_name, arg_ops)` >>
  Cases_on `lookup_function callee_name ctx.ctx_functions` >> gvs[] >>
  rename1 `SOME callee_fn` >>
  Cases_on `eval_operands arg_ops s` >> gvs[] >>
  rename1 `SOME args` >>
  Cases_on `setup_callee callee_fn args s` >> gvs[] >>
  rename1 `SOME callee_s` >>
  Cases_on `run_function fuel ctx callee_fn callee_s` >> gvs[] >>
  rename1 `IntRet vals callee_s'` >>
  Cases_on `bind_outputs inst.inst_outputs vals (merge_callee_state s callee_s')` >>
  gvs[] >>
  DISJ2_TAC >> qexists_tac `x` >> simp[next_inst_def] >>
  fs[bind_outputs_def, merge_callee_state_def] >>
  pop_assum (SUBST1_TAC o SYM) >>
  (* FOLDL update_var preserves both vs_inst_idx and vs_halted *)
  `!l acc. acc.vs_inst_idx = s.vs_inst_idx /\ acc.vs_halted = s.vs_halted ==>
     (FOLDL (\s' (out,val). update_var out val s') acc l).vs_inst_idx = s.vs_inst_idx /\
     (FOLDL (\s' (out,val). update_var out val s') acc l).vs_halted = s.vs_halted`
    suffices_by simp[] >>
  Induct >> simp[] >> Cases >> simp[update_var_def]
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


