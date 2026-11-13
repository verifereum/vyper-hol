(*
 * Running Blocks with a Common Instruction Prefix
 *
 * Two blocks whose instructions share a prefix run alike, modulo the
 * variables N that the prefix doesn't read, when their tails do. For
 * passes that rewrite only a block's tail, and for their output checkers.
 *
 * TOP-LEVEL:
 *   exec_block_common_prefix - exec_block from any index in the prefix
 *   run_block_common_prefix  - run_block, when neither tail starts with a PHI
 *)
Theory blockPrefixEquiv
Ancestors
  stateEquiv stateEquivProps execEquivParamProps execEquivParamBase
  execEquivProofs venomExecProofs venomExecSemantics venomState venomInst
  venomInstProps list rich_list pred_set finite_map

(* ===== Variable lookup across state updates ===== *)

Theorem lookup_var_set_inst_idx:
  !x u i. lookup_var x (u with vs_inst_idx := i) = lookup_var x u
Proof
  simp[lookup_var_def]
QED

Theorem lookup_var_update_var_same:
  !x w u. lookup_var x (update_var x w u) = SOME w
Proof
  simp[lookup_var_def, update_var_def, FLOOKUP_UPDATE]
QED

Theorem lookup_var_update_var_other:
  !x y w u. x <> y ==> lookup_var x (update_var y w u) = lookup_var x u
Proof
  simp[lookup_var_def, update_var_def, FLOOKUP_UPDATE]
QED

Theorem jump_to_set_inst_idx:
  !l u i. jump_to l (u with vs_inst_idx := i) = jump_to l u
Proof
  simp[jump_to_def]
QED

(* ===== state_equiv facts ===== *)

Theorem state_equiv_halted:
  state_equiv N s1 s2 ==> s1.vs_halted = s2.vs_halted
Proof
  rw[state_equiv_def, execution_equiv_def] >>
  `(execution_frame s1).vs_halted = (execution_frame s2).vs_halted`
    by asm_rewrite_tac[] >>
  fs[stateFrameTheory.execution_frame_def]
QED

Theorem state_equiv_update_right:
  state_equiv N s1 s2 /\ x IN N ==> state_equiv N s1 (update_var x w s2)
Proof
  rw[state_equiv_def, execution_equiv_def, update_var_def, lookup_var_def,
     FLOOKUP_UPDATE] >>
  rw[] >> gvs[lookup_var_def]
QED

Theorem state_equiv_lookup:
  state_equiv N s1 s2 /\ x NOTIN N ==> lookup_var x s1 = lookup_var x s2
Proof
  rw[state_equiv_def, execution_equiv_def]
QED

(* A terminator's OK result ends the block alike on both sides. *)
Theorem terminator_ok_related:
  state_equiv N s1 s2 ==>
  lift_result (state_equiv N) (execution_equiv N) (execution_equiv N)
    (if s1.vs_halted then Halt s1 else OK s1)
    (if s2.vs_halted then Halt s2 else OK s2)
Proof
  strip_tac >> imp_res_tac state_equiv_halted >>
  rw[lift_result_def, state_equiv_implies_execution_equiv]
QED

(* ===== Blocks with a common prefix ===== *)

(* Two blocks that share an instruction prefix run alike through it, from
   any index in it: P is an invariant of the source block's states along the
   prefix, and the last hypothesis covers the two tails. *)
Theorem exec_block_common_prefix:
  !N P pre t1 t2 bb1 bb2 fuel ctx.
    bb1.bb_instructions = pre ++ t1 /\ bb2.bb_instructions = pre ++ t2 /\
    (!inst x. MEM inst pre /\ MEM (Var x) inst.inst_operands ==> x NOTIN N) /\
    (!i s s'. i < LENGTH pre /\ P i s /\
       step_inst fuel ctx (EL i pre) s = OK s' /\
       ~is_terminator (EL i pre).inst_opcode ==>
       P (SUC i) (s' with vs_inst_idx := SUC i)) /\
    (!s1 s2. state_equiv N s1 s2 /\ s1.vs_inst_idx = LENGTH pre /\
       P (LENGTH pre) s1 ==>
       lift_result (state_equiv N) (execution_equiv N) (execution_equiv N)
         (exec_block fuel ctx bb1 s1) (exec_block fuel ctx bb2 s2)) ==>
    !n s1 s2. n = LENGTH pre - s1.vs_inst_idx /\
      s1.vs_inst_idx <= LENGTH pre /\ state_equiv N s1 s2 /\
      P s1.vs_inst_idx s1 ==>
      lift_result (state_equiv N) (execution_equiv N) (execution_equiv N)
        (exec_block fuel ctx bb1 s1) (exec_block fuel ctx bb2 s2)
Proof
  rpt gen_tac >> strip_tac >> Induct >> rpt strip_tac
  >- (`s1.vs_inst_idx = LENGTH pre` by simp[] >> metis_tac[]) >>
  `s1.vs_inst_idx < LENGTH pre` by simp[] >>
  `s2.vs_inst_idx = s1.vs_inst_idx` by fs[state_equiv_def] >>
  qabbrev_tac `i = s1.vs_inst_idx` >>
  qabbrev_tac `inst = EL i pre` >>
  `MEM inst pre` by simp[Abbr `inst`, EL_MEM] >>
  `lift_result (state_equiv N) (execution_equiv N) (execution_equiv N)
     (step_inst fuel ctx inst s1) (step_inst fuel ctx inst s2)`
    by (irule step_inst_preserves_R >>
        simp[state_equiv_execution_equiv_valid_state_rel] >>
        metis_tac[state_equiv_lookup]) >>
  ONCE_REWRITE_TAC [exec_block_def] >>
  simp[get_instruction_def, EL_APPEND1] >>
  Cases_on `step_inst fuel ctx inst s1` >>
  Cases_on `step_inst fuel ctx inst s2` >> gvs[lift_result_def] >>
  IF_CASES_TAC >- simp[terminator_ok_related] >>
  simp[] >>
  qpat_x_assum `!s1 s2. n = _ /\ _ ==> _` irule >>
  simp[state_equiv_inst_idx] >>
  fs[Abbr `inst`] >>
  qpat_x_assum `!i s s'. _` irule >> simp[] >> metis_tac[]
QED

Theorem eval_phis_append_non_phi:
  !pre t s. (t = [] \/ (HD t).inst_opcode <> PHI) ==>
    eval_phis s (pre ++ t) = eval_phis s pre /\
    phi_prefix_length (pre ++ t) = phi_prefix_length pre
Proof
  Induct >> rpt gen_tac >> disch_tac
  >- (Cases_on `t` >> gvs[eval_phis_def, phi_prefix_length_def]) >>
  first_x_assum drule >> strip_tac >>
  simp[eval_phis_def, phi_prefix_length_def]
QED

Theorem phi_prefix_length_non_phi:
  !l k. k < LENGTH l /\ (EL k l).inst_opcode <> PHI ==>
        phi_prefix_length l <= k
Proof
  Induct >> rw[phi_prefix_length_def] >> Cases_on `k` >> gvs[] >>
  first_x_assum irule >> simp[]
QED

(* run_block of two blocks with a common prefix and non-PHI tails. *)
Theorem run_block_common_prefix:
  !N P pre t1 t2 bb1 bb2 fuel ctx s1 s2.
    bb1.bb_instructions = pre ++ t1 /\ bb2.bb_instructions = pre ++ t2 /\
    (t1 = [] \/ (HD t1).inst_opcode <> PHI) /\
    (t2 = [] \/ (HD t2).inst_opcode <> PHI) /\
    (!inst x. MEM inst pre /\ MEM (Var x) inst.inst_operands ==> x NOTIN N) /\
    (!i s s'. i < LENGTH pre /\ P i s /\
       step_inst fuel ctx (EL i pre) s = OK s' /\
       ~is_terminator (EL i pre).inst_opcode ==>
       P (SUC i) (s' with vs_inst_idx := SUC i)) /\
    (!s1 s2. state_equiv N s1 s2 /\ s1.vs_inst_idx = LENGTH pre /\
       P (LENGTH pre) s1 ==>
       lift_result (state_equiv N) (execution_equiv N) (execution_equiv N)
         (exec_block fuel ctx bb1 s1) (exec_block fuel ctx bb2 s2)) /\
    (!s. P (phi_prefix_length pre) s) /\
    state_equiv N s1 s2 ==>
    lift_result (state_equiv N) (execution_equiv N) (execution_equiv N)
      (run_block fuel ctx bb1 s1) (run_block fuel ctx bb2 s2)
Proof
  rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
  `EVERY (\inst. inst.inst_opcode = PHI ==>
            !x. MEM (Var x) inst.inst_operands ==>
                lookup_var x s1 = lookup_var x s2) pre`
    by (simp[EVERY_MEM] >> metis_tac[state_equiv_lookup]) >>
  `s1.vs_prev_bb = s2.vs_prev_bb` by fs[state_equiv_def] >>
  assume_tac (Q.SPEC `N` state_equiv_execution_equiv_valid_state_rel) >>
  `!s. eval_phis s (pre ++ t1) = eval_phis s pre /\
       phi_prefix_length (pre ++ t1) = phi_prefix_length pre /\
       eval_phis s (pre ++ t2) = eval_phis s pre /\
       phi_prefix_length (pre ++ t2) = phi_prefix_length pre`
    by metis_tac[eval_phis_append_non_phi] >>
  simp[run_block_def] >>
  qspecl_then [`s1`, `pre`] strip_assume_tac eval_phis_ok_or_error_defs >>
  simp[]
  >- (drule_all eval_phis_agreement >> strip_tac >> simp[] >>
      `state_equiv N s' s2'` by metis_tac[eval_phis_preserves_R_ok] >>
      qspecl_then [`N`, `P`, `pre`, `t1`, `t2`, `bb1`, `bb2`, `fuel`, `ctx`]
        mp_tac exec_block_common_prefix >>
      impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC) >>
      disch_then (qspecl_then [`LENGTH pre - phi_prefix_length pre`,
        `s' with vs_inst_idx := phi_prefix_length pre`,
        `s2' with vs_inst_idx := phi_prefix_length pre`] mp_tac) >>
      simp[state_equiv_inst_idx, phi_prefix_length_le]) >>
  drule_all eval_phis_error_agreement >> strip_tac >> simp[lift_result_def]
QED
