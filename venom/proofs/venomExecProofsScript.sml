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
  venomExecSemantics venomInst venomInstProofs venomState venomWf rich_list list finite_map

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
   block_step / exec_block Properties
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

Theorem exec_block_OK_not_halted:
  !fuel ctx bb s v. exec_block fuel ctx bb s = OK v ==> ~v.vs_halted
Proof
  ho_match_mp_tac (cj 2 run_defs_ind) >>
  qexists_tac `\fuel ctx inst s. T` >>
  qexists_tac `\fuel ctx fn s. T` >> simp[] >>
  rpt gen_tac >> strip_tac >>
  simp[Once exec_block_def] >>
  Cases_on `get_instruction bb s.vs_inst_idx` >> simp[] >>
  rename1 `SOME inst` >>
  Cases_on `step_inst fuel ctx inst s` >> simp[] >>
  rw[] >> gvs[]
QED

Theorem exec_block_OK_inst_idx_0:
  !fuel ctx bb s v. exec_block fuel ctx bb s = OK v ==> v.vs_inst_idx = 0
Proof
  ho_match_mp_tac (cj 2 run_defs_ind) >>
  qexists_tac `\fuel ctx inst s. T` >>
  qexists_tac `\fuel ctx fn s. T` >> simp[] >>
  rpt gen_tac >> strip_tac >>
  simp[Once exec_block_def] >>
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

(* exec_block OK implies prev_bb was set by jump_to (JMP/JNZ/DJMP) *)
Theorem exec_block_ok_sets_prev_bb:
  !fuel ctx bb s s'.
    exec_block fuel ctx bb s = OK s' ==>
    s'.vs_prev_bb <> NONE
Proof
  ho_match_mp_tac (cj 2 run_defs_ind) >>
  qexists_tac `\fuel ctx inst s. T` >>
  qexists_tac `\fuel ctx fn s. T` >> simp[] >>
  rpt gen_tac >> strip_tac >>
  simp[Once exec_block_def] >>
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

(* bind_outputs preserves vs_prev_bb *)
Triviality foldl_update_var_prev_bb:
  !kvs s.
    (FOLDL (\s' (k,v). update_var k v s') s kvs).vs_prev_bb =
    s.vs_prev_bb
Proof
  Induct >> simp[] >> Cases >> simp[update_var_def]
QED

Triviality bind_outputs_prev_bb:
  bind_outputs outs vals s = SOME s' ==> s'.vs_prev_bb = s.vs_prev_bb
Proof
  rw[bind_outputs_def, AllCaseEqs()] >> simp[foldl_update_var_prev_bb]
QED

(* step_inst OK preserves vs_prev_bb for non-terminators (including INVOKE) *)
Theorem step_inst_preserves_prev_bb:
  !fuel ctx inst s s'.
    step_inst fuel ctx inst s = OK s' /\
    ~is_terminator inst.inst_opcode ==>
    s'.vs_prev_bb = s.vs_prev_bb
Proof
  rpt strip_tac >>
  Cases_on `inst.inst_opcode = INVOKE`
  >- ((* INVOKE: step_inst unfolds to run_blocks + bind_outputs + merge_callee *)
      qpat_x_assum `step_inst _ _ _ _ = _` mp_tac >>
      simp[Once step_inst_def] >>
      gvs[AllCaseEqs()] >> rw[] >>
      imp_res_tac bind_outputs_prev_bb >>
      gvs[merge_callee_state_def])
  >> (* non-INVOKE: step_inst = step_inst_base *)
     `step_inst fuel ctx inst s = step_inst_base inst s`
       by metis_tac[step_inst_non_invoke] >>
     gvs[] >>
     qpat_x_assum `step_inst_base _ _ = _` mp_tac >>
     simp[step_inst_base_def] >>
     Cases_on `inst.inst_opcode` >> gvs[is_terminator_def] >>
     simp[exec_pure2_def, exec_pure1_def, exec_pure3_def,
          exec_read0_def, exec_read1_def, exec_write2_def,
          exec_ext_call_def, exec_delegatecall_def,
          exec_create_def, exec_alloca_def,
          extract_venom_result_def] >>
     strip_tac >> gvs[AllCaseEqs()] >>
     rpt (pairarg_tac >> gvs[AllCaseEqs()]) >>
     gvs[update_var_def, mstore_def, mstore8_def, sstore_def, tstore_def,
         write_memory_with_expansion_def, mcopy_def, revert_state_def]
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
      mstore_def, mstore8_def, mload_def, sstore_def, sload_def,
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
  rw[block_step_def, LET_THM] >>
  simp[Once exec_block_def] >>
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

Theorem FIND_MEM:
  !P l x. FIND P l = SOME x ==> MEM x l
Proof
  Induct_on `l` >> simp[FIND_thm] >> rw[] >> metis_tac[]
QED

Theorem FIND_P:
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

(* lookup_block returns a block whose label matches the query *)
Theorem lookup_block_label:
  !lbl bbs bb.
    lookup_block lbl bbs = SOME bb ==> bb.bb_label = lbl
Proof
  rw[lookup_block_def] >> drule FIND_P >> simp[]
QED

Theorem exec_block_invoke_cases:
  !fuel ctx bb1 bb2 s inst.
    get_instruction bb1 s.vs_inst_idx = SOME inst /\
    get_instruction bb2 s.vs_inst_idx = SOME inst /\
    inst.inst_opcode = INVOKE ==>
    (exec_block fuel ctx bb1 s = exec_block fuel ctx bb2 s) \/
    (?s'. exec_block fuel ctx bb1 s = exec_block fuel ctx bb1 (next_inst s') /\
          exec_block fuel ctx bb2 s = exec_block fuel ctx bb2 (next_inst s') /\
          s'.vs_inst_idx = s.vs_inst_idx /\
          s'.vs_halted = s.vs_halted)
Proof
  rpt gen_tac >> strip_tac >>
  qabbrev_tac `res = step_inst fuel ctx inst s` >>
  `exec_block fuel ctx bb1 s =
    case res of
      OK s' =>
        if is_terminator inst.inst_opcode then
          if s'.vs_halted then Halt s' else OK s'
        else exec_block fuel ctx bb1 (s' with vs_inst_idx := SUC s.vs_inst_idx)
    | IntRet v s' => IntRet v s'
    | Halt s' => Halt s'
    | Abort a s' => Abort a s'
    | Error e => Error e`
    by simp[Once exec_block_def, Abbr `res`] >>
  `exec_block fuel ctx bb2 s =
    case res of
      OK s' =>
        if is_terminator inst.inst_opcode then
          if s'.vs_halted then Halt s' else OK s'
        else exec_block fuel ctx bb2 (s' with vs_inst_idx := SUC s.vs_inst_idx)
    | IntRet v s' => IntRet v s'
    | Halt s' => Halt s'
    | Abort a s' => Abort a s'
    | Error e => Error e`
    by simp[Once exec_block_def, Abbr `res`] >>
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

(* ==========================================================================
   Shared block-level semantic theorems
   ========================================================================== *)

(* Terminator OK preserves vs_vars *)
Theorem step_terminator_preserves_vars:
  !fuel ctx inst s s'.
    step_inst fuel ctx inst s = OK s' /\
    is_terminator inst.inst_opcode ==>
    !v. lookup_var v s' = lookup_var v s
Proof
  rpt strip_tac >>
  `inst.inst_opcode <> INVOKE` by (
    Cases_on `inst.inst_opcode` >> fs[is_terminator_def]) >>
  fs[step_inst_non_invoke] >>
  Cases_on `inst.inst_opcode` >> fs[is_terminator_def] >>
  fs[step_inst_base_def, LET_THM] >>
  rpt (BasicProvers.PURE_FULL_CASE_TAC >>
       fs[jump_to_def, halt_state_def, revert_state_def,
          set_returndata_def, lookup_var_def]) >>
  rw[]
QED

(* step_inst ALWAYS preserves vs_labels (both terminator and non-terminator) *)
Theorem step_inst_preserves_labels_always:
  !fuel ctx inst s s'.
    step_inst fuel ctx inst s = OK s' ==> s'.vs_labels = s.vs_labels
Proof
  rpt strip_tac >>
  Cases_on `is_terminator inst.inst_opcode`
  >- (
    `inst.inst_opcode <> INVOKE` by (
      Cases_on `inst.inst_opcode` >> fs[is_terminator_def]) >>
    fs[step_inst_non_invoke] >>
    Cases_on `inst.inst_opcode` >> fs[is_terminator_def] >>
    fs[step_inst_base_def, LET_THM] >>
    rpt (BasicProvers.PURE_FULL_CASE_TAC >>
         fs[jump_to_def, halt_state_def, revert_state_def,
            set_returndata_def]) >>
    rw[])
  >- metis_tac[step_preserves_labels]
QED

(* MEM + ALL_DISTINCT labels ==> lookup_block finds the block *)
Theorem MEM_lookup_block:
  !lbl bbs (bb:basic_block).
    MEM bb bbs /\ bb.bb_label = lbl /\
    ALL_DISTINCT (MAP (\bb. bb.bb_label) bbs) ==>
    lookup_block lbl bbs = SOME bb
Proof
  Induct_on `bbs` >> simp[lookup_block_def, FIND_thm] >>
  rpt strip_tac >> gvs[MEM_MAP] >> rw[] >> gvs[lookup_block_def]
QED

Theorem extract_labels_eq_map:
  !ops lbls. EVERY (\op. IS_SOME (get_label op)) ops /\
    extract_labels ops = SOME lbls ==>
    MAP (THE o get_label) ops = lbls
Proof
  Induct >> rw[extract_labels_def] >>
  Cases_on `h` >> fs[get_label_def, extract_labels_def] >>
  Cases_on `extract_labels ops` >> fs[]
QED

(* After a well-formed terminator executes OK without halting,
   vs_current_bb is in get_successors of that instruction. *)
Theorem step_inst_base_term_succs:
  !inst s s'.
    inst_wf inst /\ is_terminator inst.inst_opcode /\
    step_inst_base inst s = OK s' /\ ~s'.vs_halted ==>
    MEM s'.vs_current_bb (get_successors inst)
Proof
  rpt strip_tac >>
  Cases_on `inst.inst_opcode` >>
  fs[is_terminator_def] >>
  fs[step_inst_base_def, inst_wf_def, get_successors_def,
     get_label_def, AllCaseEqs(), jump_to_def, is_terminator_def] >>
  gvs[]
  >- (Cases_on `c` >> fs[get_label_def])
  >- (Cases_on `c` >> fs[get_label_def])
  >- (
    `MAP (THE o get_label) label_ops = labels` by
      metis_tac[extract_labels_eq_map] >>
    `FILTER IS_SOME (MAP get_label label_ops) = MAP get_label label_ops` by
      simp[FILTER_EQ_ID, EVERY_MAP] >>
    `MAP THE (MAP get_label label_ops) = labels` by
      fs[MAP_MAP_o] >>
    Cases_on `IS_SOME (get_label sel)` >> asm_rewrite_tac[MAP, MEM] >>
    fs[MEM_EL] >> metis_tac[MEM_EL])
QED

(* After a terminator step_inst_base returns OK,
   vs_prev_bb = SOME (input vs_current_bb).
   Only JMP/JNZ/DJMP return OK; all use jump_to which sets this. *)
Theorem step_inst_base_term_prev_bb:
  !inst s s'.
    is_terminator inst.inst_opcode /\
    step_inst_base inst s = OK s' ==>
    s'.vs_prev_bb = SOME s.vs_current_bb
Proof
  rpt strip_tac >>
  Cases_on `inst.inst_opcode` >>
  fs[is_terminator_def] >>
  fs[step_inst_base_def, AllCaseEqs(), jump_to_def] >>
  gvs[]
QED

(* exec_block OK with vs_inst_idx=0 implies nonempty block *)
Theorem exec_block_ok_nonempty:
  !fuel ctx bb s v. s.vs_inst_idx = 0 /\ exec_block fuel ctx bb s = OK v ==>
    bb.bb_instructions <> []
Proof
  rpt gen_tac >> strip_tac >>
  spose_not_then assume_tac >>
  `bb.bb_instructions = []` by fs[] >>
  qpat_x_assum `exec_block _ _ _ _ = OK _` mp_tac >>
  simp[Once exec_block_def, get_instruction_def]
QED

(* After exec_block OK, vs_current_bb is in bb_succs bb *)
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
  rpt strip_tac >>
  `!n fuel ctx s.
     n = LENGTH bb.bb_instructions - s.vs_inst_idx /\
     s.vs_inst_idx <= LENGTH bb.bb_instructions /\
     exec_block fuel ctx bb s = OK s1 ==>
     MEM s1.vs_current_bb (bb_succs bb)`
    suffices_by (
      disch_then (qspecl_then
        [`LENGTH bb.bb_instructions`, `fuel`, `ctx`, `s`] mp_tac) >>
      simp[]) >>
  completeInduct_on `n` >> rpt strip_tac >>
  qabbrev_tac `i = s'.vs_inst_idx` >>
  Cases_on `i >= LENGTH bb.bb_instructions`
  >- (
    qpat_x_assum `exec_block _ _ _ _ = _` mp_tac >>
    ONCE_REWRITE_TAC[exec_block_def] >>
    simp[get_instruction_def]
  ) >>
  `i < LENGTH bb.bb_instructions` by fs[] >>
  qpat_x_assum `exec_block _ _ _ _ = _` mp_tac >>
  ONCE_REWRITE_TAC[exec_block_def] >>
  simp[get_instruction_def] >>
  Cases_on `step_inst fuel' ctx' (EL i bb.bb_instructions) s'` >>
  gvs[]
  >- (
    strip_tac >>
    Cases_on `is_terminator (EL i bb.bb_instructions).inst_opcode` >> gvs[]
    >- (
      Cases_on `v.vs_halted` >> gvs[] >>
      `~(i < LENGTH bb.bb_instructions - 1)` by metis_tac[] >>
      `i = PRE (LENGTH bb.bb_instructions)` by fs[] >> gvs[] >>
      `inst_wf (EL (PRE (LENGTH bb.bb_instructions)) bb.bb_instructions)` by
        (fs[EVERY_EL]) >>
      `(EL (PRE (LENGTH bb.bb_instructions)) bb.bb_instructions).inst_opcode
         <> INVOKE` by
        (CCONTR_TAC >> gvs[is_terminator_def]) >>
      `step_inst_base
         (EL (PRE (LENGTH bb.bb_instructions)) bb.bb_instructions) s' = OK s1` by
        gvs[step_inst_non_invoke] >>
      drule_all step_inst_base_term_succs >> strip_tac >>
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

(* After exec_block OK, vs_prev_bb = SOME (initial vs_current_bb).
   Terminators (JMP/JNZ/DJMP) all use jump_to which sets vs_prev_bb. *)
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
  rpt strip_tac >>
  `!n fuel ctx s'.
     n = LENGTH bb.bb_instructions - s'.vs_inst_idx /\
     s'.vs_inst_idx <= LENGTH bb.bb_instructions /\
     s'.vs_current_bb = s.vs_current_bb /\
     exec_block fuel ctx bb s' = OK s1 ==>
     s1.vs_prev_bb = SOME s.vs_current_bb`
    suffices_by (
      disch_then (qspecl_then
        [`LENGTH bb.bb_instructions`, `fuel`, `ctx`, `s`] mp_tac) >>
      simp[]) >>
  completeInduct_on `n` >> rpt strip_tac >>
  qabbrev_tac `i = s'.vs_inst_idx` >>
  Cases_on `i >= LENGTH bb.bb_instructions`
  >- (
    qpat_x_assum `exec_block _ _ _ _ = _` mp_tac >>
    ONCE_REWRITE_TAC[exec_block_def] >>
    simp[get_instruction_def]
  ) >>
  `i < LENGTH bb.bb_instructions` by fs[] >>
  qpat_x_assum `exec_block _ _ _ _ = _` mp_tac >>
  ONCE_REWRITE_TAC[exec_block_def] >>
  simp[get_instruction_def] >>
  Cases_on `step_inst fuel' ctx' (EL i bb.bb_instructions) s'` >>
  gvs[]
  >- (
    strip_tac >>
    Cases_on `is_terminator (EL i bb.bb_instructions).inst_opcode` >> gvs[]
    >- (
      Cases_on `v.vs_halted` >> gvs[] >>
      `~(i < LENGTH bb.bb_instructions - 1)` by metis_tac[] >>
      `i = PRE (LENGTH bb.bb_instructions)` by fs[] >> gvs[] >>
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
        (drule_all step_preserves_control_flow >> simp[]) >>
      qpat_x_assum `!m. m < _ ==> _`
        (qspec_then `LENGTH bb.bb_instructions - SUC i` mp_tac) >>
      impl_tac >- simp[Abbr `i`] >>
      disch_then (qspecl_then [`fuel'`, `ctx'`,
        `v with vs_inst_idx := SUC i`] mp_tac) >>
      simp[]
    )
  )
QED

(* ==========================================================================
   Variable Preservation Across Block Execution

   If a variable v is not in ANY instruction's outputs within a block,
   then exec_block preserves lookup_var v.
   ========================================================================== *)

Theorem exec_block_preserves_non_output_vars:
  !fuel ctx bb s s'.
    exec_block fuel ctx bb s = OK s' ==>
    !v. ~MEM v (FLAT (MAP (\i. i.inst_outputs) bb.bb_instructions)) ==>
    lookup_var v s' = lookup_var v s
Proof
  rpt gen_tac >> strip_tac >> gen_tac >> strip_tac >>
  (* Strong induction on remaining instructions *)
  `!n f c st st'.
     n = LENGTH bb.bb_instructions - st.vs_inst_idx /\
     exec_block f c bb st = OK st' ==>
     lookup_var v st' = lookup_var v st`
    suffices_by (
      disch_then (qspecl_then
        [`LENGTH bb.bb_instructions - s.vs_inst_idx`,
         `fuel`, `ctx`, `s`, `s'`] mp_tac) >>
      simp[]) >>
  completeInduct_on `n` >> rw[] >>
  qabbrev_tac `idx = st.vs_inst_idx` >>
  (* Case split: idx past end or within block *)
  Cases_on `idx >= LENGTH bb.bb_instructions`
  >- (
    qpat_x_assum `exec_block _ _ _ _ = _` mp_tac >>
    ONCE_REWRITE_TAC[exec_block_def] >>
    simp[get_instruction_def]
  ) >>
  `idx < LENGTH bb.bb_instructions` by fs[] >>
  qpat_x_assum `exec_block _ _ _ _ = _` mp_tac >>
  ONCE_REWRITE_TAC[exec_block_def] >>
  simp[get_instruction_def] >>
  Cases_on `step_inst f c (EL idx bb.bb_instructions) st` >> gvs[] >>
  Cases_on `is_terminator (EL idx bb.bb_instructions).inst_opcode` >> gvs[]
  >- (
    (* Terminator: halted contradicts OK, so st' = v' *)
    Cases_on `v'.vs_halted` >> gvs[] >>
    metis_tac[step_terminator_preserves_vars]
  ) >>
  (* Non-terminator: step preserves v, then IH *)
  strip_tac >>
  `~MEM v (EL idx bb.bb_instructions).inst_outputs` by (
    fs[MEM_FLAT, MEM_MAP] >> metis_tac[MEM_EL]) >>
  `lookup_var v v' = lookup_var v st` by
    metis_tac[step_preserves_non_output_vars] >>
  `lookup_var v st' = lookup_var v (v' with vs_inst_idx := SUC idx)` by (
    first_x_assum (qspec_then `LENGTH bb.bb_instructions - SUC idx` mp_tac) >>
    (impl_tac >- simp[Abbr `idx`]) >>
    disch_then (qspecl_then [`f`, `c`,
      `v' with vs_inst_idx := SUC idx`, `st'`] mp_tac) >>
    simp[]) >>
  fs[lookup_var_def]
QED

(* ==========================================================================
   Block Equivalence Under Shared Instructions

   If two blocks agree on all instructions from current index onwards
   (within bb1's range), then exec_block gives the same result.
   ========================================================================== *)

Theorem exec_block_same_insts:
  !fuel ctx bb1 bb2 s.
    s.vs_inst_idx < LENGTH bb1.bb_instructions /\
    LENGTH bb2.bb_instructions = LENGTH bb1.bb_instructions /\
    (!i. s.vs_inst_idx <= i /\ i < LENGTH bb1.bb_instructions ==>
      EL i bb1.bb_instructions = EL i bb2.bb_instructions) ==>
    exec_block fuel ctx bb1 s = exec_block fuel ctx bb2 s
Proof
  rpt gen_tac >> strip_tac >>
  `!n f c st.
     n = LENGTH bb1.bb_instructions - st.vs_inst_idx /\
     st.vs_inst_idx < LENGTH bb1.bb_instructions /\
     (!i. st.vs_inst_idx <= i /\ i < LENGTH bb1.bb_instructions ==>
       EL i bb1.bb_instructions = EL i bb2.bb_instructions) ==>
     exec_block f c bb1 st = exec_block f c bb2 st`
    suffices_by (
      disch_then (qspecl_then
        [`LENGTH bb1.bb_instructions - s.vs_inst_idx`,
         `fuel`, `ctx`, `s`] mp_tac) >> simp[]) >>
  completeInduct_on `n` >> rw[] >>
  qabbrev_tac `idx = st.vs_inst_idx` >>
  `idx < LENGTH bb2.bb_instructions` by simp[Abbr `idx`] >>
  `EL idx bb1.bb_instructions = EL idx bb2.bb_instructions` by (
    first_x_assum (qspec_then `idx` mp_tac) >> simp[Abbr `idx`]) >>
  (* Expand exec_block on both sides; both see the same instruction *)
  ONCE_REWRITE_TAC[exec_block_def] >>
  simp[get_instruction_def] >>
  (* Case split on step_inst result — common to both sides *)
  Cases_on `step_inst f c (EL idx bb2.bb_instructions) st` >> simp[] >>
  (* OK case: check terminator *)
  Cases_on `is_terminator (EL idx bb2.bb_instructions).inst_opcode` >>
  simp[] >>
  (* Non-terminator: apply IH or show idx was last instruction *)
  Cases_on `SUC idx < LENGTH bb1.bb_instructions`
  >- (
    qpat_x_assum `!m. m < _ ==> _` (qspec_then
      `LENGTH bb1.bb_instructions - SUC idx` mp_tac) >>
    (impl_tac >- simp[Abbr `idx`]) >>
    disch_then (qspecl_then [`f`, `c`,
      `v with vs_inst_idx := SUC idx`] mp_tac) >>
    simp[Abbr `idx`]) >>
  (* idx was last instruction: both blocks have no instruction at SUC idx *)
  `~(SUC idx < LENGTH bb2.bb_instructions)` by simp[] >>
  simp[Once exec_block_def, get_instruction_def] >>
  simp[Once exec_block_def, get_instruction_def]
QED

(* ==========================================================================
   Fuel Monotonicity
   ==========================================================================
   If a computation terminates with result R (not Error) using fuel n,
   then it also terminates with R using any fuel m >= n.
   This is the key compositionality property for simulation proofs where
   the transformed program may use different fuel than the original.
   ========================================================================== *)

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
  (* Reshape for run_defs_ind: P(fuel, ctx, X, s) = !m r. ... *)
  `(!fuel ctx inst s.
      !m r. step_inst fuel ctx inst s = r /\ (!e. r <> Error e) /\
             fuel <= m ==> step_inst m ctx inst s = r) /\
   (!fuel ctx bb s.
      !m r. exec_block fuel ctx bb s = r /\ (!e. r <> Error e) /\
             fuel <= m ==> exec_block m ctx bb s = r) /\
   (!fuel ctx fn s.
      !m r. run_blocks fuel ctx fn s = r /\ (!e. r <> Error e) /\
             fuel <= m ==> run_blocks m ctx fn s = r)`
    suffices_by (rpt strip_tac >> res_tac >> simp[]) >>
  ho_match_mp_tac run_defs_ind >> rpt conj_tac
  (* --- step_inst case --- *)
  >- (
    rpt gen_tac >> strip_tac >> rpt gen_tac >> strip_tac >>
    Cases_on `inst.inst_opcode = INVOKE`
    >- (
      qpat_x_assum `step_inst _ _ _ _ = _` mp_tac >>
      ASM_REWRITE_TAC[step_inst_def] >>
      BasicProvers.every_case_tac >> gvs[] >> strip_tac >> gvs[] >>
      (* Derive run_blocks m = run_blocks fuel for the callee *)
      first_x_assum (qspecl_then [`(q, r')`, `q`, `r'`, `x'`, `x`, `x''`] mp_tac) >>
      simp[] >>
      disch_then (qspecl_then [`m`, `run_blocks fuel ctx x' x''`] mp_tac) >>
      simp[] >> strip_tac >> fs[] >> gvs[]
    )
    >- gvs[step_inst_non_invoke]
  )
  (* --- exec_block case --- *)
  >- (
    rpt gen_tac >> strip_tac >> rpt gen_tac >> strip_tac >>
    qpat_x_assum `exec_block _ _ _ _ = _` mp_tac >>
    simp[Once exec_block_def] >>
    Cases_on `get_instruction bb s.vs_inst_idx`
    >- (simp[] >> strip_tac >> gvs[]) >>
    rename1 `SOME inst` >> simp[] >>
    (* Derive step_inst fuel_mono from step_inst IH *)
    `!si_r. step_inst fuel ctx inst s = si_r /\ (!e. si_r <> Error e) ==>
            step_inst m ctx inst s = si_r` by
      (rpt strip_tac >>
       qpat_x_assum `!inst'. _ ==> _` (qspec_then `inst` mp_tac) >> simp[] >>
       disch_then (qspecl_then [`m`, `si_r`] mp_tac) >> simp[]) >>
    Cases_on `step_inst fuel ctx inst s` >> simp[]
    >- (
      `step_inst m ctx inst s = OK v` by
        (first_x_assum (qspec_then `OK v` mp_tac) >> simp[]) >>
      Cases_on `is_terminator inst.inst_opcode` >> simp[]
      >- (strip_tac >> gvs[] >> simp[Once exec_block_def])
      >- (
        strip_tac >> simp[Once exec_block_def] >>
        (* Use exec_block continuation IH *)
        qpat_x_assum `!inst' s''. _ /\ _ /\ _ ==> _`
          (qspecl_then [`inst`, `v`] mp_tac) >> simp[] >>
        disch_then (qspecl_then [`m`, `r`] mp_tac) >> simp[]
      )
    )
    >- (`step_inst m ctx inst s = Halt v` by
          (first_x_assum (qspec_then `Halt v` mp_tac) >> simp[]) >>
        strip_tac >> gvs[] >> simp[Once exec_block_def])
    >- (`step_inst m ctx inst s = Abort a v` by
          (first_x_assum (qspec_then `Abort a v` mp_tac) >> simp[]) >>
        strip_tac >> gvs[] >> simp[Once exec_block_def])
    >- (`step_inst m ctx inst s = IntRet l v` by
          (first_x_assum (qspec_then `IntRet l v` mp_tac) >> simp[]) >>
        strip_tac >> gvs[] >> simp[Once exec_block_def])
  )
  (* --- run_blocks case --- *)
  >- (
    rpt gen_tac >> strip_tac >> rpt gen_tac >> strip_tac >>
    Cases_on `fuel`
    >- gvs[run_blocks_def] >>
    rename1 `SUC fuel'` >>
    (* Expand source run_blocks assumption, simplify case SUC *)
    qpat_x_assum `run_blocks _ _ _ _ = _`
      (fn th => assume_tac (SIMP_RULE (srw_ss()) []
        (ONCE_REWRITE_RULE [run_blocks_def] th))) >>
    Cases_on `lookup_block s.vs_current_bb fn.fn_blocks` >> fs[] >>
    rename1 `SOME bb` >>
    (* Case split on exec_block to learn what r is *)
    Cases_on `exec_block fuel' ctx bb (s with vs_inst_idx := 0)` >> gvs[]
    (* -- OK case -- *)
    >- (
      Cases_on `v.vs_halted` >> gvs[]
      (* halted: r = Halt v *)
      >- (
        Cases_on `m` >- gvs[] >> rename1 `SUC m''` >>
        `exec_block m'' ctx bb (s with vs_inst_idx := 0) = OK v` by
          (first_x_assum (qspec_then `m''` mp_tac) >> simp[]) >>
        simp[Once run_blocks_def]
      )
      (* not halted: r = run_blocks fuel' ctx fn v *)
      >- (
        Cases_on `m` >- gvs[] >> rename1 `SUC m''` >>
        `exec_block m'' ctx bb (s with vs_inst_idx := 0) = OK v` by
          (first_x_assum (qspec_then `m''` mp_tac) >> simp[]) >>
        simp[Once run_blocks_def] >>
        (* Use run_blocks recursive IH *)
        first_x_assum (qspec_then `v` mp_tac) >> simp[] >>
        disch_then (qspec_then `m''` mp_tac) >> simp[]
      )
    )
    (* -- Halt case: r = Halt v -- *)
    >- (
      Cases_on `m` >- gvs[] >> rename1 `SUC m''` >>
      `exec_block m'' ctx bb (s with vs_inst_idx := 0) = Halt v` by
        (first_x_assum (qspec_then `m''` mp_tac) >> simp[]) >>
      simp[Once run_blocks_def]
    )
    (* -- Abort case -- *)
    >- (
      Cases_on `m` >- gvs[] >> rename1 `SUC m''` >>
      `exec_block m'' ctx bb (s with vs_inst_idx := 0) = Abort a v` by
        (first_x_assum (qspec_then `m''` mp_tac) >> simp[]) >>
      simp[Once run_blocks_def]
    )
    (* -- IntRet case -- *)
    >- (
      Cases_on `m` >- gvs[] >> rename1 `SUC m''` >>
      `exec_block m'' ctx bb (s with vs_inst_idx := 0) = IntRet l v` by
        (first_x_assum (qspec_then `m''` mp_tac) >> simp[]) >>
      simp[Once run_blocks_def]
    )
  )
QED


(* ==========================================================================
   Operand FDOM Properties
   ========================================================================== *)



(* For non-excluded opcodes with inst_wf:
   if a Var operand is not in FDOM (eval returns NONE), step_inst_base returns Error.
   Contrapositive: non-Error implies all Var operands are in FDOM. *)
Triviality eval_operands_mem_none[local]:
  !ops s op. MEM op ops /\ eval_operand op s = NONE ==>
    eval_operands ops s = NONE
Proof
  Induct >> simp[eval_operands_def] >>
  rpt gen_tac >> strip_tac >>
  Cases_on `op = h` >> gvs[] >>
  BasicProvers.TOP_CASE_TAC >> simp[] >>
  BasicProvers.TOP_CASE_TAC >> simp[] >>
  metis_tac[optionTheory.NOT_NONE_SOME]
QED



(* General: if eval_operands returns NONE for the full operand list,
   step_inst_base returns Error for non-excluded opcodes.
   Note: DJMP/OFFSET excluded because they don't eval all operands via
   eval_operands (DJMP uses extract_labels, OFFSET has Label operand).
   JMP/PARAM/ALLOCA also excluded because their operands are Lit/Label only. *)
(* Split into two parts to stay under 5s per tactic step *)

(* Part 1: "uniform" opcodes that go through exec_pure/read/write wrappers *)
Triviality step_inst_base_operands_none_uniform[local]:
  !inst s.
    MEM inst.inst_opcode [ADD; SUB; MUL; Div; SDIV; Mod; SMOD; Exp;
      ADDMOD; MULMOD; EQ; LT; GT; SLT; SGT; ISZERO;
      AND; OR; XOR; NOT; SHL; SHR; SAR; SIGNEXTEND; BYTE;
      MLOAD; MSTORE; MSTORE8; SLOAD; SSTORE; TLOAD; TSTORE;
      BLOCKHASH; BLOBHASH; BALANCE; CALLDATALOAD;
      EXTCODESIZE; EXTCODEHASH; ILOAD; DLOAD] /\
    inst_wf inst /\
    eval_operands inst.inst_operands s = NONE ==>
    ?e. step_inst_base inst s = Error e
Proof
  rpt strip_tac >> gvs[MEM] >>
  gvs[inst_wf_def, LENGTH_EQ_NUM_compute,
      step_inst_base_def,
      exec_pure1_def, exec_pure2_def, exec_pure3_def,
      exec_read1_def, exec_write2_def,
      eval_operands_def, eval_operand_def, lookup_var_def] >>
  BasicProvers.every_case_tac >> gvs[]
QED

(* Part 2: custom opcodes with inline operand handling.
   JNZ excluded: its Label operands cause eval_operands=NONE but
   step_inst_base only evaluates the condition, so it can succeed. *)
Triviality step_inst_base_operands_none_custom[local]:
  !inst s.
    MEM inst.inst_opcode [MCOPY; ISTORE; RET; RETURN; REVERT;
      ASSIGN; INVOKE; CALLDATACOPY; RETURNDATACOPY; CODECOPY;
      EXTCODECOPY; SHA3; CALL; STATICCALL; DELEGATECALL;
      CREATE; CREATE2; SELFDESTRUCT; ASSERT; ASSERT_UNREACHABLE;
      DLOADBYTES] /\
    inst_wf inst /\
    eval_operands inst.inst_operands s = NONE ==>
    ?e. step_inst_base inst s = Error e
Proof
  rpt strip_tac >> gvs[MEM] >>
  gvs[inst_wf_def, LENGTH_EQ_NUM_compute,
      step_inst_base_def,
      eval_operands_def, eval_operand_def, lookup_var_def] >>
  BasicProvers.every_case_tac >> gvs[]
QED

(* Part 3: LOG — needs special handling because inst_wf gives parametric-length
   operand list (Lit tc :: rest with LENGTH rest = w2n tc + 2).
   The key insight: eval_operand (Lit tc) s = SOME tc always, so
   eval_operands returning NONE means some element of rest evals to NONE.
   step_inst_base for LOG evaluates all of rest, so it must hit the NONE and error. *)
Triviality step_inst_base_operands_none_log[local]:
  !inst s.
    inst.inst_opcode = LOG /\
    inst_wf inst /\
    eval_operands inst.inst_operands s = NONE ==>
    ?e. step_inst_base inst s = Error e
Proof
  rpt strip_tac >>
  gvs[inst_wf_def] >>
  (* Now: inst.inst_operands = Lit tc :: rest, LENGTH rest = w2n tc + 2,
     eval_operands (Lit tc :: rest) s = NONE *)
  (* Lit tc always evaluates, so eval_operands rest s = NONE *)
  gvs[eval_operands_def, eval_operand_def] >>
  (* rest has length >= 2, so destructure it *)
  `?h1 h2 tl. rest = h1 :: h2 :: tl` by
    (Cases_on `rest` >> gvs[] >>
     Cases_on `t` >> gvs[]) >>
  gvs[step_inst_base_def, eval_operands_def] >>
  BasicProvers.every_case_tac >> gvs[]
QED

Triviality step_inst_base_operands_none[local]:
  !inst s.
    inst_wf inst /\
    ~MEM inst.inst_opcode [NOP; PHI; STOP; SINK; INVALID;
      CALLER; ADDRESS; CALLVALUE; GAS; GASLIMIT;
      ORIGIN; GASPRICE; COINBASE; TIMESTAMP; NUMBER; PREVRANDAO; CHAINID;
      SELFBALANCE; BASEFEE; BLOBBASEFEE; CALLDATASIZE; RETURNDATASIZE;
      CODESIZE; MSIZE;
      DJMP; JMP; JNZ; PARAM; ALLOCA; OFFSET] /\
    eval_operands inst.inst_operands s = NONE ==>
    ?e. step_inst_base inst s = Error e
Proof
  rpt strip_tac >>
  Cases_on `inst.inst_opcode` >> gvs[MEM] >>
  metis_tac[step_inst_base_operands_none_uniform,
            step_inst_base_operands_none_custom,
            step_inst_base_operands_none_log, MEM]
QED

Theorem step_inst_base_nonerr_var_fdom:
  !inst s x.
    inst_wf inst /\
    ~MEM inst.inst_opcode [NOP; PHI; STOP; SINK; INVALID;
      CALLER; ADDRESS; CALLVALUE; GAS; GASLIMIT;
      ORIGIN; GASPRICE; COINBASE; TIMESTAMP; NUMBER; PREVRANDAO; CHAINID;
      SELFBALANCE; BASEFEE; BLOBBASEFEE; CALLDATASIZE; RETURNDATASIZE;
      CODESIZE; MSIZE] /\
    MEM (Var x) inst.inst_operands /\
    (!e. step_inst_base inst s <> Error e) ==>
    x IN FDOM s.vs_vars
Proof
  SPOSE_NOT_THEN STRIP_ASSUME_TAC >>
  `eval_operand (Var x) s = NONE` by
    simp[eval_operand_def, lookup_var_def, finite_mapTheory.flookup_thm] >>
  qpat_x_assum `!e. _ <> _` mp_tac >> simp[] >>
  imp_res_tac eval_operands_mem_none >>
  (* DJMP: Var x is sel => eval NONE => Error;
     Var x in label_ops => contradicts EVERY IS_SOME get_label *)
  Cases_on `inst.inst_opcode = DJMP` >-
    (gvs[inst_wf_def] >>
     (* gvs splits MEM: subgoals with sel=Var x close via step_inst_base *)
     TRY (gvs[step_inst_base_def, eval_operand_def, lookup_var_def] >> NO_TAC) >>
     (* remaining: MEM Var x label_ops contradicts EVERY IS_SOME get_label *)
     gvs[listTheory.EVERY_MEM] >> res_tac >> fs[get_label_def]) >>
  (* JMP/PARAM/ALLOCA: no Var operands possible *)
  Cases_on `inst.inst_opcode = JMP` >-
    gvs[inst_wf_def, LENGTH_EQ_NUM_compute, MEM] >>
  Cases_on `inst.inst_opcode = PARAM` >-
    gvs[inst_wf_def, LENGTH_EQ_NUM_compute, MEM] >>
  Cases_on `inst.inst_opcode = ALLOCA` >-
    gvs[inst_wf_def, LENGTH_EQ_NUM_compute, MEM] >>
  (* OFFSET: Var x must be offset_op, eval_operand NONE => Error *)
  Cases_on `inst.inst_opcode = OFFSET` >-
    gvs[inst_wf_def, LENGTH_EQ_NUM_compute, MEM, step_inst_base_def,
        exec_pure2_def] >>
  (* JNZ: ops = [c; Label l1; Label l2], only Var is c, eval_operand c NONE => Error *)
  Cases_on `inst.inst_opcode = JNZ` >-
    (gvs[inst_wf_def, LENGTH_EQ_NUM_compute, MEM, step_inst_base_def,
        eval_operand_def, lookup_var_def] >>
     BasicProvers.every_case_tac >> gvs[]) >>
  (* All other opcodes: use step_inst_base_operands_none *)
  `~MEM inst.inst_opcode [NOP; PHI; STOP; SINK; INVALID;
      CALLER; ADDRESS; CALLVALUE; GAS; GASLIMIT;
      ORIGIN; GASPRICE; COINBASE; TIMESTAMP; NUMBER; PREVRANDAO; CHAINID;
      SELFBALANCE; BASEFEE; BLOBBASEFEE; CALLDATASIZE; RETURNDATASIZE;
      CODESIZE; MSIZE; DJMP; JMP; JNZ; PARAM; ALLOCA; OFFSET]` by
    gvs[MEM] >>
  drule_all step_inst_base_operands_none >> metis_tac[]
QED

(* ==========================================================================
   FDOM Monotonicity for step_inst_base

   After a successful non-terminator step_inst_base:
   1. All existing FDOM vars remain in FDOM
   2. All inst_outputs are in FDOM
   Combined: FDOM s'.vs_vars = FDOM s.vs_vars ∪ set inst.inst_outputs

   Proof by opcode case split, grouped to stay under 5s per step.
   Every non-terminator opcode with outputs uses update_var, giving |+.
   Every non-terminator opcode without outputs preserves vs_vars.
   ========================================================================== *)

(* Helper: update_var adds output to FDOM and preserves existing *)
Triviality update_var_fdom[local]:
  !x v s. FDOM (update_var x v s).vs_vars = x INSERT FDOM s.vs_vars
Proof
  simp[update_var_def, finite_mapTheory.FDOM_FUPDATE]
QED

(* Helper: FOLDL update_var adds all outputs *)
Triviality foldl_update_var_fdom[local]:
  !kvs s.
    FDOM (FOLDL (\s' (k,v). update_var k v s') s kvs).vs_vars =
    FDOM s.vs_vars UNION set (MAP FST kvs)
Proof
  Induct >> simp[pairTheory.FORALL_PROD] >>
  rpt gen_tac >> simp[update_var_def, finite_mapTheory.FDOM_FUPDATE] >>
  simp[pred_setTheory.EXTENSION] >> metis_tac[]
QED

(* extract_venom_result preserves vs_vars *)
Triviality extract_venom_result_preserves_vars[local]:
  !s out ro rs r output s'.
    extract_venom_result s out ro rs r = SOME (output, s') ==>
    s'.vs_vars = s.vs_vars
Proof
  rpt gen_tac >>
  simp[extract_venom_result_def] >>
  BasicProvers.every_case_tac >> simp[] >>
  strip_tac >> gvs[]
QED

(* All groups share this tactic pattern *)
fun prove_fdom_group opcode_list = prove(
  ``!inst s s'.
     MEM inst.inst_opcode ^opcode_list /\
     inst_wf inst /\ step_inst_base inst s = OK s' ==>
     FDOM s'.vs_vars = FDOM s.vs_vars UNION set inst.inst_outputs``,
  rpt strip_tac >> gvs[MEM] >>
  gvs[inst_wf_def, LENGTH_EQ_NUM_compute,
      step_inst_base_def, exec_pure2_def, exec_pure1_def, exec_pure3_def,
      exec_read0_def, exec_read1_def, exec_write2_def,
      exec_alloca_def,
      mstore_def, mstore8_def, sstore_def, tstore_def] >>
  BasicProvers.every_case_tac >>
  gvs[update_var_def, finite_mapTheory.FDOM_FUPDATE] >>
  simp[pred_setTheory.EXTENSION] >> metis_tac[]);

val step_inst_base_fdom_pure2 = prove_fdom_group
  ``[ADD; SUB; MUL; Div; SDIV; Mod; SMOD; Exp;
     ADDMOD; MULMOD; EQ; LT; GT; SLT; SGT;
     AND; OR; XOR; SHL; SHR; SAR; SIGNEXTEND; BYTE]``;

val step_inst_base_fdom_pure1 = prove_fdom_group
  ``[ISZERO; NOT]``;

val step_inst_base_fdom_read0 = prove_fdom_group
  ``[CALLER; ADDRESS; CALLVALUE; GAS; GASLIMIT;
     ORIGIN; GASPRICE; COINBASE; TIMESTAMP; NUMBER; PREVRANDAO; CHAINID;
     SELFBALANCE; BASEFEE; BLOBBASEFEE; CALLDATASIZE; RETURNDATASIZE;
     CODESIZE; MSIZE]``;

val step_inst_base_fdom_read1 = prove_fdom_group
  ``[MLOAD; SLOAD; TLOAD; ILOAD; DLOAD;
     CALLDATALOAD; BALANCE; BLOCKHASH; BLOBHASH;
     EXTCODESIZE; EXTCODEHASH]``;

val step_inst_base_fdom_write2 = prove_fdom_group
  ``[MSTORE; MSTORE8; SSTORE; TSTORE; ISTORE]``;

(* Zero-output group needs a different tactic: the state changes are
   to memory/storage/logs, not vs_vars, so record accessor simp suffices *)
val step_inst_base_fdom_no_output = prove(
  ``!inst s s'.
     MEM inst.inst_opcode [NOP; MCOPY; LOG; CALLDATACOPY; CODECOPY;
       RETURNDATACOPY; EXTCODECOPY; DLOADBYTES;
       ASSERT; ASSERT_UNREACHABLE] /\
     inst_wf inst /\ step_inst_base inst s = OK s' ==>
     FDOM s'.vs_vars = FDOM s.vs_vars UNION set inst.inst_outputs``,
  rpt strip_tac >> gvs[MEM] >>
  gvs[inst_wf_def, LENGTH_EQ_NUM_compute, step_inst_base_def] >>
  BasicProvers.every_case_tac >>
  gvs[mstore_def, sstore_def, tstore_def,
      mcopy_def, write_memory_with_expansion_def]);

val step_inst_base_fdom_custom1 = prove_fdom_group
  ``[ASSIGN; PHI; SHA3; PARAM; ALLOCA; OFFSET]``;

(* External calls: extract_venom_result preserves vs_vars, then update_var adds output *)
val step_inst_base_fdom_external = prove(
  ``!inst s s'.
     MEM inst.inst_opcode [CALL; STATICCALL; DELEGATECALL; CREATE; CREATE2] /\
     inst_wf inst /\ step_inst_base inst s = OK s' ==>
     FDOM s'.vs_vars = FDOM s.vs_vars UNION set inst.inst_outputs``,
  rpt strip_tac >> gvs[MEM] >>
  gvs[inst_wf_def, LENGTH_EQ_NUM_compute, step_inst_base_def] >>
  BasicProvers.every_case_tac >>
  gvs[exec_ext_call_def, exec_delegatecall_def, exec_create_def] >>
  BasicProvers.every_case_tac >> gvs[] >>
  imp_res_tac extract_venom_result_preserves_vars >> gvs[] >>
  gvs[update_var_def, finite_mapTheory.FDOM_FUPDATE] >>
  simp[pred_setTheory.EXTENSION] >> metis_tac[]);

(* INVOKE: step_inst_base returns Error, so premise is vacuously false *)
val step_inst_base_fdom_invoke = prove(
  ``!inst s s'.
     inst.inst_opcode = INVOKE /\
     inst_wf inst /\ step_inst_base inst s = OK s' ==>
     FDOM s'.vs_vars = FDOM s.vs_vars UNION set inst.inst_outputs``,
  rpt strip_tac >> gvs[step_inst_base_def]);

(* Main theorem: combine all parts *)
Theorem step_inst_base_fdom:
  !inst s s'.
    step_inst_base inst s = OK s' /\
    inst_wf inst /\
    ~is_terminator inst.inst_opcode ==>
    FDOM s'.vs_vars = FDOM s.vs_vars UNION set inst.inst_outputs
Proof
  rpt strip_tac >>
  Cases_on `inst.inst_opcode` >> gvs[is_terminator_def] >>
  metis_tac[step_inst_base_fdom_pure2,
            step_inst_base_fdom_pure1,
            step_inst_base_fdom_read0,
            step_inst_base_fdom_read1,
            step_inst_base_fdom_write2,
            step_inst_base_fdom_no_output,
            step_inst_base_fdom_custom1,
            step_inst_base_fdom_external,
            step_inst_base_fdom_invoke,
            MEM]
QED

(* bind_outputs FDOM: outputs added to vs_vars *)
Theorem bind_outputs_fdom:
  !outs vals s s'.
    bind_outputs outs vals s = SOME s' ==>
    FDOM s'.vs_vars = FDOM s.vs_vars UNION set outs
Proof
  simp[bind_outputs_def] >> rpt strip_tac >>
  BasicProvers.every_case_tac >> gvs[] >>
  metis_tac[foldl_update_var_fdom, listTheory.MAP_ZIP]
QED

(* Lift to step_inst: covers both INVOKE and non-INVOKE *)
Theorem step_inst_fdom:
  !fuel ctx inst s s'.
    step_inst fuel ctx inst s = OK s' /\
    inst_wf inst /\
    ~is_terminator inst.inst_opcode ==>
    FDOM s'.vs_vars = FDOM s.vs_vars UNION set inst.inst_outputs
Proof
  rpt strip_tac >>
  Cases_on `inst.inst_opcode = INVOKE`
  >- (
    (* INVOKE case: merge_callee preserves vs_vars, bind_outputs adds outputs *)
    gvs[Once step_inst_def] >>
    BasicProvers.every_case_tac >> gvs[] >>
    imp_res_tac bind_outputs_fdom >>
    gvs[merge_callee_state_def])
  >- (
    (* Non-INVOKE: delegate to step_inst_base_fdom *)
    `step_inst_base inst s = OK s'` by gvs[step_inst_non_invoke] >>
    metis_tac[step_inst_base_fdom])
QED

(* Well-formed terminators have no outputs. *)
Theorem terminator_no_outputs:
  !inst. inst_wf inst /\ is_terminator inst.inst_opcode ==>
    inst.inst_outputs = []
Proof
  rw[inst_wf_def] >> Cases_on `inst.inst_opcode` >> gvs[is_terminator_def]
QED

(* IS_SOME(lookup_var v s) is monotone across step_inst OK.
   Non-terminator: step_inst_fdom says FDOM grows.
   Terminator: step_terminator_preserves_vars says all vars preserved. *)
Theorem step_inst_lookup_mono:
  !fuel ctx inst s s' v.
    step_inst fuel ctx inst s = OK s' /\ inst_wf inst /\
    IS_SOME (lookup_var v s) ==>
    IS_SOME (lookup_var v s')
Proof
  rpt strip_tac >>
  Cases_on `is_terminator inst.inst_opcode`
  >- (`lookup_var v s' = lookup_var v s`
        by metis_tac[step_terminator_preserves_vars] >> gvs[])
  >> (Cases_on `MEM v inst.inst_outputs`
      >- (drule_all step_inst_fdom >> strip_tac >>
          fs[lookup_var_def, FLOOKUP_DEF])
      >> (`lookup_var v s' = lookup_var v s` by
            metis_tac[step_preserves_non_output_vars] >>
          gvs[]))
QED

(* IS_SOME(lookup_var v s) is monotone across exec_block OK.
   Proof by strong induction on remaining instructions,
   same structure as exec_block_preserves_non_output_vars. *)
Theorem exec_block_lookup_mono:
  !fuel ctx bb s s' v.
    exec_block fuel ctx bb s = OK s' /\
    EVERY inst_wf bb.bb_instructions /\
    IS_SOME (lookup_var v s) ==>
    IS_SOME (lookup_var v s')
Proof
  rpt gen_tac >> strip_tac >>
  `!n f c st st'.
     n = LENGTH bb.bb_instructions - st.vs_inst_idx /\
     EVERY inst_wf bb.bb_instructions /\
     exec_block f c bb st = OK st' /\
     IS_SOME (lookup_var v st) ==>
     IS_SOME (lookup_var v st')`
    suffices_by (
      disch_then (qspecl_then
        [`LENGTH bb.bb_instructions - s.vs_inst_idx`,
         `fuel`, `ctx`, `s`, `s'`] mp_tac) >> simp[]) >>
  completeInduct_on `n` >> rw[] >>
  qabbrev_tac `idx = st.vs_inst_idx` >>
  Cases_on `idx >= LENGTH bb.bb_instructions`
  >- (qpat_x_assum `exec_block _ _ _ _ = _` mp_tac >>
      ONCE_REWRITE_TAC[exec_block_def] >> simp[get_instruction_def]) >>
  `idx < LENGTH bb.bb_instructions` by fs[] >>
  qpat_x_assum `exec_block _ _ _ _ = _` mp_tac >>
  ONCE_REWRITE_TAC[exec_block_def] >> simp[get_instruction_def] >>
  Cases_on `step_inst f c (EL idx bb.bb_instructions) st` >> gvs[] >>
  `inst_wf (EL idx bb.bb_instructions)` by fs[EVERY_EL] >>
  Cases_on `is_terminator (EL idx bb.bb_instructions).inst_opcode` >> gvs[]
  >- (Cases_on `v'.vs_halted` >> gvs[] >>
      metis_tac[step_inst_lookup_mono]) >>
  strip_tac >>
  `IS_SOME (lookup_var v v')` by metis_tac[step_inst_lookup_mono] >>
  `IS_SOME (lookup_var v (v' with vs_inst_idx := SUC idx))` by
    fs[lookup_var_def] >>
  first_x_assum (qspec_then `LENGTH bb.bb_instructions - SUC idx` mp_tac) >>
  (impl_tac >- simp[Abbr `idx`]) >>
  disch_then (qspecl_then [`f`, `c`,
    `v' with vs_inst_idx := SUC idx`, `st'`] mp_tac) >>
  simp[]
QED

(* exec_block_output_defined: if v is in outputs of some instruction in bb,
   exec_block OK from inst_idx=0 implies IS_SOME(lookup_var v s').
   NOTE: proof goes in mem2varCorrectness locally due to build iteration speed.
   It depends on step_inst_lookup_mono, exec_block_lookup_mono,
   step_inst_fdom, and terminator_no_outputs above. *)

(* ALL_DISTINCT distributes through FLAT: each member is ALL_DISTINCT *)
Triviality all_distinct_flat_mem:
  !ls l. ALL_DISTINCT (FLAT ls) /\ MEM l ls ==> ALL_DISTINCT l
Proof
  Induct >> simp[] >> rpt strip_tac >> gvs[ALL_DISTINCT_APPEND]
QED

(* Same instruction record at two positions in same block ⟹ same index.
   Uses fn_inst_ids_distinct (part of wf_function). *)
Theorem inst_ids_el_eq:
  !fn bb j idx.
    fn_inst_ids_distinct fn /\ MEM bb fn.fn_blocks /\
    j < LENGTH bb.bb_instructions /\
    idx < LENGTH bb.bb_instructions /\
    EL j bb.bb_instructions = EL idx bb.bb_instructions ==>
    j = idx
Proof
  rpt strip_tac >>
  fs[fn_inst_ids_distinct_def] >>
  `MEM (MAP (\i. i.inst_id) bb.bb_instructions)
       (MAP (\bb. MAP (\i. i.inst_id) bb.bb_instructions) fn.fn_blocks)` by
    (simp[MEM_MAP] >> metis_tac[]) >>
  `ALL_DISTINCT (MAP (\i. i.inst_id) bb.bb_instructions)` by
    metis_tac[all_distinct_flat_mem] >>
  `ALL_DISTINCT bb.bb_instructions` by metis_tac[ALL_DISTINCT_MAP] >>
  metis_tac[ALL_DISTINCT_EL_IMP]
QED

(* ===== CFG path / dominance helpers ===== *)

Theorem is_fn_path_rtc:
  !fn path. is_fn_path fn path /\ path <> [] ==>
    (fn_cfg_edge fn)^* (HD path) (LAST path)
Proof
  Induct_on `path` >> simp[is_fn_path_def] >>
  rpt strip_tac >> Cases_on `path` >> gvs[is_fn_path_def] >>
  irule (CONJUNCT2 (SPEC_ALL relationTheory.RTC_RULES)) >>
  qexists_tac `h'` >> simp[]
QED

Theorem rtc_to_fn_path:
  !fn x y. (fn_cfg_edge fn)^* x y ==>
    ?path. is_fn_path fn path /\ path <> [] /\ HD path = x /\ LAST path = y
Proof
  gen_tac >> ho_match_mp_tac relationTheory.RTC_INDUCT >> rw[]
  >- (qexists_tac `[x]` >> simp[is_fn_path_def])
  >- (qexists_tac `x::path` >> Cases_on `path` >> gvs[is_fn_path_def])
QED

Theorem is_fn_path_prefix:
  !fn path d. is_fn_path fn path /\ MEM d path ==>
    ?pre. is_fn_path fn (pre ++ [d]) /\ HD (pre ++ [d]) = HD path
Proof
  Induct_on `path` >> simp[] >> rpt strip_tac >> gvs[]
  >- (qexists_tac `[]` >> simp[is_fn_path_def])
  >- (Cases_on `path` >> gvs[is_fn_path_def]
      >- (qexists_tac `[h]` >> simp[is_fn_path_def])
      >- (first_x_assum (qspecl_then [`fn`, `d`] mp_tac) >> simp[] >>
          strip_tac >> qexists_tac `h::pre` >>
          Cases_on `pre` >> gvs[is_fn_path_def]))
QED

Theorem fn_dominates_dom_reachable:
  !fn d n. fn_dominates fn d n ==> fn_reachable fn d
Proof
  rw[fn_dominates_def, fn_reachable_def] >>
  qexists_tac `entry` >> simp[] >>
  drule rtc_to_fn_path >> strip_tac >>
  `MEM d path` by (first_x_assum irule >> simp[] >> metis_tac[]) >>
  drule_all is_fn_path_prefix >> strip_tac >>
  drule is_fn_path_rtc >>
  simp[listTheory.APPEND_eq_NIL]
QED

Theorem is_fn_path_snoc:
  !fn path lbl. is_fn_path fn path /\ path <> [] /\
    fn_cfg_edge fn (LAST path) lbl ==>
    is_fn_path fn (path ++ [lbl])
Proof
  Induct_on `path` >> simp[is_fn_path_def] >>
  rpt strip_tac >> Cases_on `path` >> gvs[is_fn_path_def]
QED

Theorem fn_dominates_predecessor:
  !fn d n p.
    fn_dominates fn d n /\ d <> n /\
    fn_cfg_edge fn p n /\ fn_reachable fn p ==>
    fn_dominates fn d p
Proof
  rw[fn_dominates_def] >> rpt strip_tac >>
  `is_fn_path fn (path ++ [n])` by (
    irule is_fn_path_snoc >> simp[]) >>
  `MEM d (path ++ [n])` by (
    first_x_assum (qspec_then `path ++ [n]` mp_tac) >>
    impl_tac >- (
      simp[listTheory.LAST_APPEND_CONS] >>
      Cases_on `path` >> gvs[]) >>
    simp[]) >>
  gvs[listTheory.MEM_APPEND]
QED

(* ===== General wf_function helpers ===== *)

Theorem same_label_same_block:
  !f bb1 bb2.
    wf_function f /\ MEM bb1 f.fn_blocks /\ MEM bb2 f.fn_blocks /\
    bb1.bb_label = bb2.bb_label ==>
    bb1 = bb2
Proof
  rpt strip_tac >>
  `ALL_DISTINCT (MAP (\b. b.bb_label) f.fn_blocks)` by
    fs[wf_function_def, fn_labels_def] >>
  `lookup_block bb1.bb_label f.fn_blocks = SOME bb1` by
    (irule MEM_lookup_block >> simp[]) >>
  `lookup_block bb1.bb_label f.fn_blocks = SOME bb2` by
    (irule MEM_lookup_block >> gvs[]) >>
  gvs[]
QED

Theorem wf_function_bb_well_formed:
  !fn bb. wf_function fn /\ MEM bb fn.fn_blocks ==> bb_well_formed bb
Proof simp[wf_function_def] >> metis_tac[]
QED

Theorem fn_inst_wf_every_bb:
  !fn bb. fn_inst_wf fn /\ MEM bb fn.fn_blocks ==>
    EVERY inst_wf bb.bb_instructions
Proof simp[fn_inst_wf_def] >> metis_tac[EVERY_MEM]
QED

Theorem phi_before_non_phi:
  !bb i idx.
    bb_well_formed bb /\
    i < LENGTH bb.bb_instructions /\
    idx < LENGTH bb.bb_instructions /\
    (EL i bb.bb_instructions).inst_opcode = PHI /\
    (EL idx bb.bb_instructions).inst_opcode <> PHI ==>
    i < idx
Proof
  rpt strip_tac >>
  CCONTR_TAC >> fs[arithmeticTheory.NOT_LESS] >>
  `idx = i \/ idx < i` by DECIDE_TAC
  >- gvs[]
  >- (fs[bb_well_formed_def] >> metis_tac[])
QED

(* ===== FDOM monotonicity helpers ===== *)

Theorem lookup_var_fdom:
  !x s s'.
    lookup_var x s' = lookup_var x s /\ x IN FDOM s.vs_vars ==>
    x IN FDOM s'.vs_vars
Proof
  rw[lookup_var_def] >>
  `FLOOKUP s.vs_vars x <> NONE` by metis_tac[flookup_thm] >>
  Cases_on `FLOOKUP s.vs_vars x` >> gvs[flookup_thm]
QED

Theorem fn_reachable_step:
  !f lbl lbl'.
    fn_reachable f lbl /\ fn_cfg_edge f lbl lbl' ==>
    fn_reachable f lbl'
Proof
  rpt strip_tac >>
  qpat_x_assum `fn_reachable _ _`
    (strip_assume_tac o REWRITE_RULE[fn_reachable_def]) >>
  simp[fn_reachable_def] >>
  metis_tac[relationTheory.RTC_CASES2]
QED

(* ===== Layer 2: Block chaining in run_blocks ===== *)

Theorem run_blocks_step_proof:
  ∀ fuel ctx fn bb ss ss'.
    lookup_block ss.vs_current_bb fn.fn_blocks = SOME bb ∧
    exec_block fuel ctx bb (ss with vs_inst_idx := 0) = OK ss' ∧
    ¬ss'.vs_halted
    ⇒
    run_blocks (SUC fuel) ctx fn ss = run_blocks fuel ctx fn ss'
Proof
  rw[] >> simp[Once run_blocks_def]
QED

Theorem run_blocks_two_blocks_proof:
  ∀ fuel ctx fn bb_A ss ss_mid result.
    lookup_block ss.vs_current_bb fn.fn_blocks = SOME bb_A ∧
    exec_block fuel ctx bb_A (ss with vs_inst_idx := 0) = OK ss_mid ∧
    ¬ss_mid.vs_halted ∧
    run_blocks fuel ctx fn ss_mid = result
    ⇒
    run_blocks (SUC fuel) ctx fn ss = result
Proof
  rw[] >> rw[Once run_blocks_def]
QED

Theorem run_blocks_halt_proof:
  ∀ fuel ctx fn bb ss ss'.
    lookup_block ss.vs_current_bb fn.fn_blocks = SOME bb ∧
    exec_block fuel ctx bb (ss with vs_inst_idx := 0) = OK ss' ∧
    ss'.vs_halted
    ⇒
    run_blocks (SUC fuel) ctx fn ss = Halt ss'
Proof
  rw[] >> rw[Once run_blocks_def]
QED

Theorem run_blocks_abort_proof:
  ∀ fuel ctx fn bb ss a ss'.
    lookup_block ss.vs_current_bb fn.fn_blocks = SOME bb ∧
    exec_block fuel ctx bb (ss with vs_inst_idx := 0) = Abort a ss'
    ⇒
    run_blocks (SUC fuel) ctx fn ss = Abort a ss'
Proof
  rw[] >> rw[Once run_blocks_def]
QED
