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
   block_step / exec_block Properties
   ========================================================================== *)

Theorem block_step_increments_idx:
  !bb s v.
    block_step bb s = (OK v, F)
    ==>
    v.vs_inst_idx = SUC s.vs_inst_idx
Proof
  ACCEPT_TAC venomExecProofsTheory.block_step_increments_idx
QED

Theorem exec_block_OK_not_halted:
  !fuel ctx bb s v. exec_block fuel ctx bb s = OK v ==> ~v.vs_halted
Proof
  ACCEPT_TAC venomExecProofsTheory.exec_block_OK_not_halted
QED

Theorem exec_block_OK_inst_idx_0:
  !fuel ctx bb s v. exec_block fuel ctx bb s = OK v ==> v.vs_inst_idx = 0
Proof
  ACCEPT_TAC venomExecProofsTheory.exec_block_OK_inst_idx_0
QED

Theorem exec_block_ok_sets_prev_bb:
  !fuel ctx bb s s'.
    exec_block fuel ctx bb s = OK s' ==>
    s'.vs_prev_bb <> NONE
Proof
  ACCEPT_TAC venomExecProofsTheory.exec_block_ok_sets_prev_bb
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

Theorem FIND_MEM:
  !P l x. FIND P l = SOME x ==> MEM x l
Proof
  ACCEPT_TAC venomExecProofsTheory.FIND_MEM
QED

Theorem FIND_P:
  !P l x. FIND P l = SOME x ==> P x
Proof
  ACCEPT_TAC venomExecProofsTheory.FIND_P
QED

Theorem lookup_block_MEM:
  !lbl bbs bb.
    lookup_block lbl bbs = SOME bb ==> MEM bb bbs
Proof
  ACCEPT_TAC venomExecProofsTheory.lookup_block_MEM
QED

Theorem lookup_block_label:
  !lbl bbs bb.
    lookup_block lbl bbs = SOME bb ==> bb.bb_label = lbl
Proof
  ACCEPT_TAC venomExecProofsTheory.lookup_block_label
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

(* For non-INVOKE blocks, exec_block unfolds through block_step *)
Theorem exec_block_block_step:
  !fuel ctx bb s.
    EVERY (\inst. inst.inst_opcode <> INVOKE) bb.bb_instructions ==>
    exec_block fuel ctx bb s =
      let (r, t) = block_step bb s in
      case r of
        OK s' => if t then (if s'.vs_halted then Halt s' else OK s')
                 else exec_block fuel ctx bb s'
      | Halt s' => Halt s'
      | Abort a s' => Abort a s'
      | Error e => Error e
      | IntRet vals s' => IntRet vals s'
Proof
  ACCEPT_TAC venomExecProofsTheory.exec_block_block_step
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

Theorem step_inst_preserves_labels_always:
  !fuel ctx inst s s'.
    step_inst fuel ctx inst s = OK s' ==> s'.vs_labels = s.vs_labels
Proof
  ACCEPT_TAC venomExecProofsTheory.step_inst_preserves_labels_always
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

Theorem exec_block_ok_nonempty:
  !fuel ctx bb s v. s.vs_inst_idx = 0 /\ exec_block fuel ctx bb s = OK v ==>
    bb.bb_instructions <> []
Proof
  ACCEPT_TAC venomExecProofsTheory.exec_block_ok_nonempty
QED

Theorem exec_block_current_bb_in_succs:
  !fuel ctx bb s s1.
    EVERY inst_wf bb.bb_instructions /\
    (!i. i < LENGTH bb.bb_instructions - 1 ==>
       ~is_terminator (EL i bb.bb_instructions).inst_opcode) /\
    bb.bb_instructions <> [] /\
    s.vs_inst_idx = 0 /\
    exec_block fuel ctx bb s = OK s1 ==>
    MEM s1.vs_current_bb (bb_succs bb)
Proof
  ACCEPT_TAC venomExecProofsTheory.exec_block_current_bb_in_succs
QED

Theorem step_inst_base_term_prev_bb:
  !inst s s'.
    is_terminator inst.inst_opcode /\
    step_inst_base inst s = OK s' ==>
    s'.vs_prev_bb = SOME s.vs_current_bb
Proof
  ACCEPT_TAC venomExecProofsTheory.step_inst_base_term_prev_bb
QED

Theorem exec_block_ok_prev_bb:
  !fuel ctx bb s s1.
    EVERY inst_wf bb.bb_instructions /\
    (!i. i < LENGTH bb.bb_instructions - 1 ==>
       ~is_terminator (EL i bb.bb_instructions).inst_opcode) /\
    bb.bb_instructions <> [] /\
    s.vs_inst_idx = 0 /\
    exec_block fuel ctx bb s = OK s1 ==>
    s1.vs_prev_bb = SOME s.vs_current_bb
Proof
  ACCEPT_TAC venomExecProofsTheory.exec_block_ok_prev_bb
QED

Theorem exec_block_preserves_non_output_vars:
  !fuel ctx bb s s'.
    exec_block fuel ctx bb s = OK s' ==>
    !v. ~MEM v (FLAT (MAP (\i. i.inst_outputs) bb.bb_instructions)) ==>
    lookup_var v s' = lookup_var v s
Proof
  ACCEPT_TAC venomExecProofsTheory.exec_block_preserves_non_output_vars
QED

Theorem exec_block_same_insts:
  !fuel ctx bb1 bb2 s.
    s.vs_inst_idx < LENGTH bb1.bb_instructions /\
    LENGTH bb2.bb_instructions = LENGTH bb1.bb_instructions /\
    (!i. s.vs_inst_idx <= i /\ i < LENGTH bb1.bb_instructions ==>
      EL i bb1.bb_instructions = EL i bb2.bb_instructions) ==>
    exec_block fuel ctx bb1 s = exec_block fuel ctx bb2 s
Proof
  ACCEPT_TAC venomExecProofsTheory.exec_block_same_insts
QED

Theorem fuel_mono:
  (!n m ctx inst s r.
     step_inst n ctx inst s = r /\ (!e. r <> Error e) /\ n <= m ==>
     step_inst m ctx inst s = r) /\
  (!n m ctx bb s r.
     exec_block n ctx bb s = r /\ (!e. r <> Error e) /\ n <= m ==>
     exec_block m ctx bb s = r) /\
  (!n m ctx fn s r.
     run_blocks n ctx fn s = r /\ (!e. r <> Error e) /\ n <= m ==>
     run_blocks m ctx fn s = r)
Proof
  ACCEPT_TAC venomExecProofsTheory.fuel_mono
QED

Theorem step_inst_base_nonerr_var_fdom:
  !inst s x.
    inst_wf inst /\
    ~MEM inst.inst_opcode [NOP; PHI; STOP; SINK; INVALID;
      CALLER; ADDRESS; CALLVALUE; GAS; GASLIMIT;
      ORIGIN; GASPRICE; COINBASE; TIMESTAMP; NUMBER; PREVRANDAO; CHAINID;
      SELFBALANCE; BASEFEE; BLOBBASEFEE; CALLDATASIZE; RETURNDATASIZE;
      CODESIZE; MEMTOP] /\
    MEM (Var x) inst.inst_operands /\
    (!e. step_inst_base inst s <> Error e) ==>
    x IN FDOM s.vs_vars
Proof
  ACCEPT_TAC venomExecProofsTheory.step_inst_base_nonerr_var_fdom
QED

Theorem step_inst_base_fdom:
  !inst s s'.
    step_inst_base inst s = OK s' /\
    inst_wf inst /\
    ~is_terminator inst.inst_opcode ==>
    FDOM s'.vs_vars = FDOM s.vs_vars UNION set inst.inst_outputs
Proof
  ACCEPT_TAC venomExecProofsTheory.step_inst_base_fdom
QED

Theorem step_inst_fdom:
  !fuel ctx inst s s'.
    step_inst fuel ctx inst s = OK s' /\
    inst_wf inst /\
    ~is_terminator inst.inst_opcode ==>
    FDOM s'.vs_vars = FDOM s.vs_vars UNION set inst.inst_outputs
Proof
  ACCEPT_TAC venomExecProofsTheory.step_inst_fdom
QED

Theorem bind_outputs_fdom:
  !outs vals s s'.
    bind_outputs outs vals s = SOME s' ==>
    FDOM s'.vs_vars = FDOM s.vs_vars UNION set outs
Proof
  ACCEPT_TAC venomExecProofsTheory.bind_outputs_fdom
QED

(* Non-INVOKE step_inst is context-independent *)
Theorem step_inst_ctx_irrel:
  !fuel ctx1 ctx2 inst s.
    inst.inst_opcode <> INVOKE ==>
    step_inst fuel ctx1 inst s = step_inst fuel ctx2 inst s
Proof
  rw[Once venomExecSemanticsTheory.step_inst_def] >>
  rw[Once venomExecSemanticsTheory.step_inst_def]
QED

(* Non-terminator at idx < LENGTH means SUC idx < LENGTH *)
Theorem non_terminator_not_last:
  !bb idx.
    bb_well_formed bb /\ idx < LENGTH bb.bb_instructions /\
    ~is_terminator (EL idx bb.bb_instructions).inst_opcode ==>
    SUC idx < LENGTH bb.bb_instructions
Proof
  rpt strip_tac >> fs[venomWfTheory.bb_well_formed_def] >>
  `idx <> PRE (LENGTH bb.bb_instructions)` by (
    strip_tac >>
    `LAST bb.bb_instructions = EL idx bb.bb_instructions` by
      metis_tac[listTheory.LAST_EL] >>
    metis_tac[]) >>
  simp[]
QED

(* setup_callee gives a clean initial callee state *)
Theorem setup_callee_props:
  !fn args s cs.
    setup_callee fn args s = SOME cs ==>
    cs.vs_inst_idx = 0 /\ FDOM cs.vs_vars = {} /\
    fn_entry_label fn = SOME cs.vs_current_bb
Proof
  simp[venomExecSemanticsTheory.setup_callee_def] >>
  rpt strip_tac >> gvs[] >>
  simp[venomInstTheory.fn_entry_label_def,
       venomInstTheory.entry_block_def]
QED

(* ===== Layer 2: Block chaining in run_blocks ===== *)

(* One step of run_blocks: if exec_block produces OK (not halted),
   run_blocks continues at the next block. *)
Theorem run_blocks_step:
  ∀ fuel ctx fn bb ss ss'.
    lookup_block ss.vs_current_bb fn.fn_blocks = SOME bb ∧
    exec_block fuel ctx bb (ss with vs_inst_idx := 0) = OK ss' ∧
    ¬ss'.vs_halted
    ⇒
    run_blocks (SUC fuel) ctx fn ss = run_blocks fuel ctx fn ss'
Proof ACCEPT_TAC run_blocks_step_proof
QED

(* Two blocks chained: block A produces OK, run_blocks continues *)
Theorem run_blocks_two_blocks:
  ∀ fuel ctx fn bb_A ss ss_mid result.
    lookup_block ss.vs_current_bb fn.fn_blocks = SOME bb_A ∧
    exec_block fuel ctx bb_A (ss with vs_inst_idx := 0) = OK ss_mid ∧
    ¬ss_mid.vs_halted ∧
    run_blocks fuel ctx fn ss_mid = result
    ⇒
    run_blocks (SUC fuel) ctx fn ss = result
Proof ACCEPT_TAC run_blocks_two_blocks_proof
QED

(* Terminal: exec_block produces OK with halted → run_blocks returns Halt *)
Theorem run_blocks_halt:
  ∀ fuel ctx fn bb ss ss'.
    lookup_block ss.vs_current_bb fn.fn_blocks = SOME bb ∧
    exec_block fuel ctx bb (ss with vs_inst_idx := 0) = OK ss' ∧
    ss'.vs_halted
    ⇒
    run_blocks (SUC fuel) ctx fn ss = Halt ss'
Proof ACCEPT_TAC run_blocks_halt_proof
QED

(* Terminal: exec_block produces Abort → run_blocks returns Abort *)
Theorem run_blocks_abort:
  ∀ fuel ctx fn bb ss a ss'.
    lookup_block ss.vs_current_bb fn.fn_blocks = SOME bb ∧
    exec_block fuel ctx bb (ss with vs_inst_idx := 0) = Abort a ss'
    ⇒
    run_blocks (SUC fuel) ctx fn ss = Abort a ss'
Proof ACCEPT_TAC run_blocks_abort_proof
QED

(* exec_block preserves vs_labels: helper with measure *)
Theorem exec_block_preserves_labels_aux[local]:
  !n fuel ctx bb s s'.
    n = LENGTH bb.bb_instructions - s.vs_inst_idx /\
    exec_block fuel ctx bb s = OK s' ==> s'.vs_labels = s.vs_labels
Proof
  Induct_on `n` >>
  rpt strip_tac >>
  pop_assum mp_tac >>
  simp[Once venomExecSemanticsTheory.exec_block_def] >>
  Cases_on `get_instruction bb s.vs_inst_idx` >> simp[] >>
  Cases_on `step_inst fuel ctx x s` >> simp[] >>
  gvs[AllCaseEqs()] >>
  rpt strip_tac >> gvs[] >>
  imp_res_tac step_inst_preserves_labels_always >> gvs[] >>
  (* base: n=0 contradicts get_instruction = SOME *)
  TRY (fs[venomInstTheory.get_instruction_def] >> NO_TAC) >>
  (* step: apply IH *)
  first_x_assum (qspecl_then [`fuel`,`ctx`,`bb`,
    `v with vs_inst_idx := SUC s.vs_inst_idx`, `s'`] mp_tac) >>
  imp_res_tac venomExecSemanticsTheory.step_inst_preserves_inst_idx >>
  gvs[venomInstTheory.get_instruction_def]
QED

Theorem exec_block_preserves_labels:
  !fuel ctx bb s s'.
    exec_block fuel ctx bb s = OK s' ==> s'.vs_labels = s.vs_labels
Proof
  metis_tac[exec_block_preserves_labels_aux]
QED

(* run_blocks preserves vs_labels *)
Theorem run_blocks_preserves_labels:
  !fuel ctx fn s s'.
    run_blocks fuel ctx fn s = OK s' ==> s'.vs_labels = s.vs_labels
Proof
  Induct_on `fuel` >>
  simp[Once venomExecSemanticsTheory.run_blocks_def] >>
  rpt strip_tac >>
  gvs[AllCaseEqs()] >>
  imp_res_tac exec_block_preserves_labels >> gvs[] >>
  metis_tac[]
QED
