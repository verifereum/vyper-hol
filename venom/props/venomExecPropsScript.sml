(*
 * Venom Execution Properties (Statements Only)
 *
 * Re-exports theorems from venomExecProofs via ACCEPT_TAC.
 * After step_inst refactor: step_inst_base handles individual opcodes,
 * step_inst fuel ctx handles all opcodes including INVOKE.
 *)

Theory venomExecProps
Ancestors
  venomExecProofs

(* ==========================================================================
   bool_to_word Properties
   ========================================================================== *)

Theorem bool_to_word_T:
  bool_to_word T = 1w
Proof
  ACCEPT_TAC venomExecProofsTheory.bool_to_word_T
QED

Theorem bool_to_word_F:
  bool_to_word F = 0w
Proof
  ACCEPT_TAC venomExecProofsTheory.bool_to_word_F
QED

(* ==========================================================================
   step_inst_base Behavior Lemmas
   ========================================================================== *)

Theorem step_iszero_value:
  !s cond_op out id cond.
    eval_operand cond_op s = SOME cond ==>
    step_inst_base <| inst_id := id; inst_opcode := ISZERO;
                 inst_operands := [cond_op]; inst_outputs := [out] |> s =
    OK (update_var out (bool_to_word (cond = 0w)) s)
Proof
  ACCEPT_TAC venomExecProofsTheory.step_iszero_value
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
  ACCEPT_TAC venomExecProofsTheory.step_assert_behavior
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
  ACCEPT_TAC venomExecProofsTheory.step_revert_behavior
QED

Theorem step_jmp_behavior:
  !s lbl id.
    step_inst_base <| inst_id := id; inst_opcode := JMP;
                 inst_operands := [Label lbl]; inst_outputs := [] |> s =
    OK (jump_to lbl s)
Proof
  ACCEPT_TAC venomExecProofsTheory.step_jmp_behavior
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
  ACCEPT_TAC venomExecProofsTheory.step_jnz_behavior
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
  ACCEPT_TAC venomExecProofsTheory.block_step_increments_idx
QED

Theorem run_block_OK_not_halted:
  !fuel ctx bb s v. run_block fuel ctx bb s = OK v ==> ~v.vs_halted
Proof
  ACCEPT_TAC venomExecProofsTheory.run_block_OK_not_halted
QED

Theorem run_block_OK_inst_idx_0:
  !fuel ctx bb s v. run_block fuel ctx bb s = OK v ==> v.vs_inst_idx = 0
Proof
  ACCEPT_TAC venomExecProofsTheory.run_block_OK_inst_idx_0
QED

Theorem run_block_ok_sets_prev_bb:
  !fuel ctx bb s s'.
    run_block fuel ctx bb s = OK s' ==>
    s'.vs_prev_bb <> NONE
Proof
  ACCEPT_TAC venomExecProofsTheory.run_block_ok_sets_prev_bb
QED

Theorem step_inst_preserves_prev_bb:
  !fuel ctx inst s s'.
    step_inst fuel ctx inst s = OK s' /\
    ~is_terminator inst.inst_opcode ==>
    s'.vs_prev_bb = s.vs_prev_bb
Proof
  ACCEPT_TAC venomExecProofsTheory.step_inst_preserves_prev_bb
QED

(* ==========================================================================
   Lookup Helpers
   ========================================================================== *)

Theorem lookup_block_MEM:
  !lbl bbs bb.
    lookup_block lbl bbs = SOME bb ==> MEM bb bbs
Proof
  ACCEPT_TAC venomExecProofsTheory.lookup_block_MEM
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
  ACCEPT_TAC venomExecProofsTheory.block_step_prefix_same
QED

(* ==========================================================================
   step_inst_base Result Properties
   ========================================================================== *)

Theorem step_inst_base_OK_preserves_halted:
  step_inst_base inst s = OK s' ==> s'.vs_halted = s.vs_halted
Proof
  ACCEPT_TAC venomExecProofsTheory.step_inst_base_OK_preserves_halted
QED

(* Backward-compat alias *)
Theorem step_inst_OK_preserves_halted:
  step_inst_base inst s = OK s' ==> s'.vs_halted = s.vs_halted
Proof
  ACCEPT_TAC venomExecProofsTheory.step_inst_base_OK_preserves_halted
QED

Theorem step_inst_base_OK_not_INVOKE:
  step_inst_base inst s = OK s' ==> inst.inst_opcode <> INVOKE
Proof
  ACCEPT_TAC venomExecProofsTheory.step_inst_base_OK_not_INVOKE
QED

Theorem step_inst_base_Halt_not_INVOKE:
  step_inst_base inst s = Halt v ==> inst.inst_opcode <> INVOKE
Proof
  ACCEPT_TAC venomExecProofsTheory.step_inst_base_Halt_not_INVOKE
QED

Theorem step_inst_base_Abort_not_INVOKE:
  step_inst_base inst s = Abort a v ==> inst.inst_opcode <> INVOKE
Proof
  ACCEPT_TAC venomExecProofsTheory.step_inst_base_Abort_not_INVOKE
QED

Theorem step_inst_base_IntRet_not_INVOKE:
  step_inst_base inst s = IntRet vals v ==> inst.inst_opcode <> INVOKE
Proof
  ACCEPT_TAC venomExecProofsTheory.step_inst_base_IntRet_not_INVOKE
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
  ACCEPT_TAC venomExecProofsTheory.run_block_block_step
QED

(* ==========================================================================
   Lookup Function Properties
   ========================================================================== *)

Theorem lookup_function_MEM:
  !name fns fn. lookup_function name fns = SOME fn ==> MEM fn fns
Proof
  ACCEPT_TAC venomInstTheory.lookup_function_MEM
QED

(* ==========================================================================
   Shared block-level semantic theorems
   ========================================================================== *)

Theorem step_terminator_preserves_vars:
  !fuel ctx inst s s'.
    step_inst fuel ctx inst s = OK s' /\
    is_terminator inst.inst_opcode ==>
    !v. lookup_var v s' = lookup_var v s
Proof
  ACCEPT_TAC venomExecProofsTheory.step_terminator_preserves_vars
QED

Theorem MEM_lookup_block:
  !lbl bbs (bb:basic_block).
    MEM bb bbs /\ bb.bb_label = lbl /\
    ALL_DISTINCT (MAP (\bb. bb.bb_label) bbs) ==>
    lookup_block lbl bbs = SOME bb
Proof
  ACCEPT_TAC venomExecProofsTheory.MEM_lookup_block
QED

Theorem extract_labels_eq_map:
  !ops lbls. EVERY (\op. IS_SOME (get_label op)) ops /\
    extract_labels ops = SOME lbls ==>
    MAP (THE o get_label) ops = lbls
Proof
  ACCEPT_TAC venomExecProofsTheory.extract_labels_eq_map
QED

Theorem step_inst_base_term_succs:
  !inst s s'.
    inst_wf inst /\ is_terminator inst.inst_opcode /\
    step_inst_base inst s = OK s' /\ ~s'.vs_halted ==>
    MEM s'.vs_current_bb (get_successors inst)
Proof
  ACCEPT_TAC venomExecProofsTheory.step_inst_base_term_succs
QED

Theorem run_block_ok_nonempty:
  !fuel ctx bb s v. s.vs_inst_idx = 0 /\ run_block fuel ctx bb s = OK v ==>
    bb.bb_instructions <> []
Proof
  ACCEPT_TAC venomExecProofsTheory.run_block_ok_nonempty
QED

Theorem run_block_current_bb_in_succs:
  !fuel ctx bb s s1.
    EVERY inst_wf bb.bb_instructions /\
    (!i. i < LENGTH bb.bb_instructions - 1 ==>
       ~is_terminator (EL i bb.bb_instructions).inst_opcode) /\
    bb.bb_instructions <> [] /\
    s.vs_inst_idx = 0 /\
    run_block fuel ctx bb s = OK s1 ==>
    MEM s1.vs_current_bb (bb_succs bb)
Proof
  ACCEPT_TAC venomExecProofsTheory.run_block_current_bb_in_succs
QED

Theorem step_inst_base_term_prev_bb:
  !inst s s'.
    is_terminator inst.inst_opcode /\
    step_inst_base inst s = OK s' ==>
    s'.vs_prev_bb = SOME s.vs_current_bb
Proof
  ACCEPT_TAC venomExecProofsTheory.step_inst_base_term_prev_bb
QED

Theorem run_block_ok_prev_bb:
  !fuel ctx bb s s1.
    EVERY inst_wf bb.bb_instructions /\
    (!i. i < LENGTH bb.bb_instructions - 1 ==>
       ~is_terminator (EL i bb.bb_instructions).inst_opcode) /\
    bb.bb_instructions <> [] /\
    s.vs_inst_idx = 0 /\
    run_block fuel ctx bb s = OK s1 ==>
    s1.vs_prev_bb = SOME s.vs_current_bb
Proof
  ACCEPT_TAC venomExecProofsTheory.run_block_ok_prev_bb
QED

Theorem run_block_preserves_non_output_vars:
  !fuel ctx bb s s'.
    run_block fuel ctx bb s = OK s' ==>
    !v. ~MEM v (FLAT (MAP (\i. i.inst_outputs) bb.bb_instructions)) ==>
    lookup_var v s' = lookup_var v s
Proof
  ACCEPT_TAC venomExecProofsTheory.run_block_preserves_non_output_vars
QED

Theorem run_block_same_insts:
  !fuel ctx bb1 bb2 s.
    s.vs_inst_idx < LENGTH bb1.bb_instructions /\
    LENGTH bb2.bb_instructions = LENGTH bb1.bb_instructions /\
    (!i. s.vs_inst_idx <= i /\ i < LENGTH bb1.bb_instructions ==>
      EL i bb1.bb_instructions = EL i bb2.bb_instructions) ==>
    run_block fuel ctx bb1 s = run_block fuel ctx bb2 s
Proof
  ACCEPT_TAC venomExecProofsTheory.run_block_same_insts
QED

Theorem fuel_mono:
  (!n m ctx inst s r.
     step_inst n ctx inst s = r /\ (!e. r <> Error e) /\ n <= m ==>
     step_inst m ctx inst s = r) /\
  (!n m ctx bb s r.
     run_block n ctx bb s = r /\ (!e. r <> Error e) /\ n <= m ==>
     run_block m ctx bb s = r) /\
  (!n m ctx fn s r.
     run_function n ctx fn s = r /\ (!e. r <> Error e) /\ n <= m ==>
     run_function m ctx fn s = r)
Proof
  ACCEPT_TAC venomExecProofsTheory.fuel_mono
QED
