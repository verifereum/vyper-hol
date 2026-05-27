(*
 * Revert-to-Assert: Correctness Proofs
 *
 * Proves rta_pass_correct by instantiating resolving_block_sim_function.
 *)

Theory rtaCorrectnessProofs
Ancestors
  rtaDefs crossBlockSimProofs crossBlockSimProps crossBlockSimDefs
  passSimulationDefs passSimulationProofs
  execEquivParamProofs execEquivParamBase
  stateEquiv stateEquivProps
  venomExecSemantics venomExecProofs venomExecProps
  venomInst venomState
  pred_set arithmetic
Libs
  BasicProvers

val rveq = VAR_EQ_TAC;

(* ===== Easy helpers ===== *)

(* lift_result implies resolving_block_sim (avoids unfolding defs in rich contexts) *)
Triviality lift_result_resolving_block_sim:
  !R_ok R_term bbs1 bbs2 r1 r2.
    lift_result R_ok R_term R_term r1 r2 ==>
    resolving_block_sim R_ok R_term bbs1 bbs2 r1 r2
Proof
  rpt strip_tac >>
  rw[resolving_block_sim_def] >> qexists_tac `0` >>
  rw[resolves_to_def]
QED

(* Boundary lemma: OK v resolves to r2 in one step if lift_result holds after
   running one block. Encapsulates resolves_to_def expansion so consumer proofs
   never need to unfold it (avoiding ∀fuel ctx variable mismatch). *)
Triviality resolves_to_step_ok:
  !R_ok R_term bbs1 bbs2 v r2 bb.
    ~v.vs_halted /\ lookup_block v.vs_current_bb bbs1 = SOME bb /\
    (!fuel ctx. lift_result R_ok R_term R_term (run_block_entry fuel ctx bb v) r2)
    ==> resolves_to R_ok R_term bbs1 bbs2 (SUC 0) (OK v) r2
Proof
  rpt strip_tac >>
  PURE_ONCE_REWRITE_TAC[resolves_to_def] >>
  DISJ2_TAC >> DISJ1_TAC >>
  qexists_tac `v` >> qexists_tac `bb` >> simp[] >>
  gen_tac >> gen_tac >>
  PURE_ONCE_REWRITE_TAC[resolves_to_def] >>
  first_x_assum irule >> simp[]
QED

(* transform_block preserves label *)
Triviality transform_block_label:
  !fn bb. (transform_block fn bb).bb_label = bb.bb_label
Proof
  rw[transform_block_def]
QED

(* transform_function = function_map_transform *)
Triviality transform_function_is_fmt:
  !fn. transform_function fn = function_map_transform (transform_block fn) fn
Proof
  rw[transform_function_def, function_map_transform_def]
QED

(* Any element of fresh_vars_in_function is a fresh_iszero_var *)
Triviality fresh_vars_are_iszero_vars:
  !fn x. x IN fresh_vars_in_function fn ==>
    ?id. x = fresh_iszero_var id
Proof
  rw[fresh_vars_in_function_def, PULL_EXISTS] >>
  fs[fresh_vars_in_block_def, PULL_EXISTS] >>
  metis_tac[]
QED

(* Context-level version *)
Triviality fresh_vars_ctx_are_iszero_vars:
  !ctx x. x IN fresh_vars_in_context ctx ==>
    ?id. x = fresh_iszero_var id
Proof
  rw[fresh_vars_in_context_def, PULL_EXISTS] >>
  metis_tac[fresh_vars_are_iszero_vars]
QED

(* Operand agreement: fresh vars not in original operands *)
Triviality rta_operand_agreement:
  !fn bb inst x.
    fresh_vars_not_in_function fn /\
    MEM bb fn.fn_blocks /\ MEM inst bb.bb_instructions /\
    MEM (Var x) inst.inst_operands
  ==>
    !s1 s2. state_equiv (fresh_vars_in_function fn) s1 s2 ==>
      lookup_var x s1 = lookup_var x s2
Proof
  rw[state_equiv_def, execution_equiv_def] >>
  first_x_assum irule >>
  CCONTR_TAC >> fs[] >>
  imp_res_tac fresh_vars_are_iszero_vars >>
  fs[fresh_vars_not_in_function_def, fresh_vars_not_in_block_def] >>
  metis_tac[]
QED

(* Identity block sim: when transform doesn't change the block *)
Triviality identity_block_sim:
  !R_ok R_term bbs1 bbs2 fuel ctx bb s.
    (!s. R_ok s s) /\ (!s. R_term s s) /\
    transform_block fn bb = bb
  ==>
    resolving_block_sim R_ok R_term bbs1 bbs2
      (exec_block fuel ctx bb s) (exec_block fuel ctx bb s)
Proof
  rw[resolving_block_sim_def] >>
  qexists_tac `0` >>
  rw[resolves_to_def] >>
  metis_tac[lift_result_refl_proof]
QED

(* ===== Per-block resolving_block_sim ===== *)

(* transform_jnz always produces non-empty lists *)
Triviality transform_jnz_nonempty:
  !fn inst x. transform_jnz fn inst = SOME x ==> x <> []
Proof
  rw[transform_jnz_def] >>
  BasicProvers.every_case_tac >> fs[] >>
  rw[transform_pattern1_def, transform_pattern2_def, LET_THM]
QED

(* Helper: LENGTH of transform_block_insts >= LENGTH of original *)
Triviality transform_block_insts_length:
  !insts fn. LENGTH insts <= LENGTH (transform_block_insts fn insts)
Proof
  Induct >> rw[transform_block_insts_def] >>
  Cases_on `transform_jnz fn h` >> simp[] >>
  imp_res_tac transform_jnz_nonempty >> Cases_on `x` >> fs[] >>
  first_x_assum (qspec_then `fn` mp_tac) >> simp[]
QED

(* Index alignment: instructions before first transformed JNZ are identical *)
Triviality transform_block_insts_index:
  !insts fn idx.
    idx < LENGTH insts /\
    (!j. j < idx ==> transform_jnz fn (EL j insts) = NONE)
  ==>
    EL idx (transform_block_insts fn insts) =
      (case transform_jnz fn (EL idx insts) of
         NONE => EL idx insts
       | SOME new_insts => HD new_insts)
Proof
  Induct >> rw[transform_block_insts_def] >>
  Cases_on `idx` >> fs[]
  >- (Cases_on `transform_jnz fn h` >> simp[] >>
      imp_res_tac transform_jnz_nonempty >> Cases_on `x` >> fs[])
  >- (
    `transform_jnz fn h = NONE` by (
      first_x_assum (qspec_then `0` mp_tac) >> simp[]) >>
    simp[] >>
    last_x_assum match_mp_tac >> simp[] >>
    rpt strip_tac >> first_x_assum (qspec_then `SUC j` mp_tac) >> simp[]
  )
QED

(* Running a simple revert block from index 0 *)
Triviality run_revert_block:
  !bb fuel ctx st.
    is_simple_revert_block bb /\ st.vs_inst_idx = 0 /\ ~st.vs_halted ==>
    exec_block fuel ctx bb st =
      Abort Revert_abort (revert_state (set_returndata [] st))
Proof
  rw[is_simple_revert_block_def] >>
  simp[Once exec_block_def, get_instruction_def] >>
  `EL 0 bb.bb_instructions = HD bb.bb_instructions` by
    (Cases_on `bb.bb_instructions` >> fs[]) >>
  simp[step_inst_non_invoke, step_inst_base_def, eval_operand_def]
QED

(* Combined bridge: run_block_entry directly to Abort result.
   Avoids two-step bridging (run_block_entry→exec_block→Abort) inside ∀fuel ctx
   scope, which causes syntactic mismatch. *)
Triviality run_revert_block_entry:
  !bb fuel ctx st.
    is_simple_revert_block bb /\
    EVERY (\inst. inst.inst_opcode <> PHI) bb.bb_instructions /\
    st.vs_inst_idx = 0 /\ ~st.vs_halted
  ==>
    run_block_entry fuel ctx bb st =
      Abort Revert_abort (revert_state (set_returndata [] st))
Proof
  rpt strip_tac >>
  (* run_block_entry = exec_block when no PHIs *)
  `run_block_entry fuel ctx bb st =
     exec_block fuel ctx bb (st with vs_inst_idx := 0)` by
    metis_tac[run_block_no_phis_eq_exec_block] >>
  (* exec_block matches run_revert_block *)
  `(st with vs_inst_idx := 0).vs_inst_idx = 0` by simp[] >>
  mp_tac (Q.SPECL [`bb`, `fuel`, `ctx`, `st with vs_inst_idx := 0`] run_revert_block) >>
  simp[]
QED

(* When all instructions have transform_jnz = NONE, block is unchanged *)
Triviality all_none_transform_block_insts:
  !insts fn.
    (!j. j < LENGTH insts ==> transform_jnz fn (EL j insts) = NONE) ==>
    transform_block_insts fn insts = insts
Proof
  Induct >> rw[transform_block_insts_def] >>
  `transform_jnz fn h = NONE` by (first_x_assum (qspec_then `0` mp_tac) >> simp[]) >>
  simp[] >> first_x_assum match_mp_tac >>
  rpt strip_tac >> first_x_assum (qspec_then `SUC j` mp_tac) >> simp[]
QED

(* Structural decomposition: when transform_jnz fires at idx, the transformed list
   has the prefix unchanged, then the replacement, then the rest *)
Triviality transform_block_insts_split:
  !insts fn idx new_insts.
    idx < LENGTH insts /\
    (!j. j < idx ==> transform_jnz fn (EL j insts) = NONE) /\
    transform_jnz fn (EL idx insts) = SOME new_insts
  ==>
    transform_block_insts fn insts =
      TAKE idx insts ++ new_insts ++ transform_block_insts fn (DROP (SUC idx) insts)
Proof
  Induct >> rw[transform_block_insts_def] >>
  Cases_on `idx` >> fs[] >>
  `transform_jnz fn h = NONE` by (first_x_assum (qspec_then `0` mp_tac) >> simp[]) >>
  simp[] >>
  last_x_assum match_mp_tac >> simp[] >>
  rpt strip_tac >> first_x_assum (qspec_then `SUC j` mp_tac) >> simp[]
QED

(* No invoke for instructions in a block that's in the function *)
Triviality no_invoke_mem_inst:
  !fn bb inst.
    no_invoke_in_function fn /\ MEM bb fn.fn_blocks /\
    MEM inst bb.bb_instructions ==>
    inst.inst_opcode <> INVOKE
Proof
  rw[no_invoke_in_function_def] >>
  fs[listTheory.EVERY_MEM] >> metis_tac[]
QED

(* Structural decomposition of transform_jnz = SOME *)
Triviality transform_jnz_SOME:
  !fn inst x.
    transform_jnz fn inst = SOME x ==>
    inst.inst_opcode = JNZ /\
    ?cond_op if_nonzero if_zero.
      inst.inst_operands = [cond_op; Label if_nonzero; Label if_zero] /\
      ((is_revert_label fn if_nonzero /\
        x = transform_pattern1 inst cond_op if_zero) \/
       (~is_revert_label fn if_nonzero /\
        is_revert_label fn if_zero /\
        x = transform_pattern2 inst cond_op if_nonzero))
Proof
  rw[transform_jnz_def] >>
  BasicProvers.every_case_tac >> fs[]
QED

(* A fresh_iszero_var for an instruction in the function is in fresh *)
Triviality fresh_iszero_var_in_fresh:
  !fn fresh bb inst cond_op if_nonzero if_zero.
    fresh_vars_in_function fn SUBSET fresh /\
    MEM bb fn.fn_blocks /\
    MEM inst bb.bb_instructions /\
    transform_jnz fn inst <> NONE /\
    inst.inst_operands = [cond_op; Label if_nonzero; Label if_zero] /\
    is_revert_label fn if_nonzero
  ==>
    fresh_iszero_var inst.inst_id IN fresh
Proof
  rw[SUBSET_DEF] >> first_x_assum irule >>
  rw[fresh_vars_in_function_def, PULL_EXISTS] >>
  qexists_tac `bb` >> simp[] >>
  rw[fresh_vars_in_block_def, PULL_EXISTS] >>
  metis_tac[]
QED

(* Helper: execution_equiv holds when states differ only at a fresh var *)
Triviality execution_equiv_update_fresh:
  !fresh x v s1 s2.
    x IN fresh /\ execution_equiv fresh s1 s2
  ==>
    execution_equiv fresh (update_var x v s1) s2
Proof
  rw[execution_equiv_def, update_var_def, lookup_var_def] >>
  rpt strip_tac >> simp[finite_mapTheory.FLOOKUP_UPDATE] >>
  rw[] >> metis_tac[]
QED

(* Helper: state_equiv holds when states differ only at a fresh var *)
Triviality state_equiv_update_fresh:
  !fresh x v s1 s2.
    x IN fresh /\ state_equiv fresh s1 s2
  ==>
    state_equiv fresh (update_var x v s1) s2
Proof
  rw[state_equiv_def, update_var_def, execution_equiv_def, lookup_var_def] >>
  rpt strip_tac >> simp[finite_mapTheory.FLOOKUP_UPDATE] >>
  rw[] >> metis_tac[]
QED

(* When transform_jnz fires at index idx, the transformed list is at least
   idx + LENGTH replacement long *)
Triviality transform_block_insts_length_at:
  !insts fn idx new_insts.
    idx < LENGTH insts /\
    (!j. j < idx ==> transform_jnz fn (EL j insts) = NONE) /\
    transform_jnz fn (EL idx insts) = SOME new_insts
  ==>
    idx + LENGTH new_insts <= LENGTH (transform_block_insts fn insts)
Proof
  Induct
  \\ rw[transform_block_insts_def]
  \\ Cases_on `idx`
  \\ fs[]
  (* Remaining: idx = SUC n *)
  \\ `transform_jnz fn h = NONE` by (first_x_assum (qspec_then `0` mp_tac) \\ simp[])
  \\ simp[]
  \\ first_x_assum (qspecl_then [`fn`, `n`, `new_insts`] mp_tac)
  \\ simp[]
  \\ impl_tac
  >- (rpt strip_tac \\ first_x_assum (qspec_then `SUC j` mp_tac) \\ simp[])
  \\ simp[]
QED

(* EL at offset k from the split point gives new_insts[k] *)
Triviality transform_block_insts_EL:
  !insts fn idx new_insts k.
    idx < LENGTH insts /\
    (!j. j < idx ==> transform_jnz fn (EL j insts) = NONE) /\
    transform_jnz fn (EL idx insts) = SOME new_insts /\
    k < LENGTH new_insts
  ==>
    EL (idx + k) (transform_block_insts fn insts) = EL k new_insts
Proof
  rpt strip_tac >>
  `transform_block_insts fn insts =
    TAKE idx insts ++ new_insts ++ transform_block_insts fn (DROP (SUC idx) insts)` by (
    irule transform_block_insts_split >> simp[]
  ) >>
  simp[listTheory.EL_APPEND_EQN, listTheory.LENGTH_TAKE]
QED

(* step_inst_base for JNZ: general form (inst as variable) *)
Triviality step_jnz_general:
  !inst cond_op if_nz if_z st cond.
    inst.inst_opcode = JNZ /\
    inst.inst_operands = [cond_op; Label if_nz; Label if_z] /\
    eval_operand cond_op st = SOME cond
  ==>
    step_inst_base inst st =
      if cond <> 0w then OK (jump_to if_nz st) else OK (jump_to if_z st)
Proof
  rw[step_inst_base_def, eval_operand_def]
QED

(* step_inst_base for JNZ when eval_operand fails *)
Triviality step_jnz_eval_none:
  !inst cond_op if_nz if_z st.
    inst.inst_opcode = JNZ /\
    inst.inst_operands = [cond_op; Label if_nz; Label if_z] /\
    eval_operand cond_op st = NONE
  ==>
    ?e. step_inst_base inst st = Error e
Proof
  rw[step_inst_base_def, eval_operand_def]
QED

(* step_inst_base for ISZERO when eval_operand fails *)
Triviality step_iszero_eval_none:
  !id cond_op out st.
    eval_operand cond_op st = NONE
  ==>
    ?e. step_inst_base (mk_iszero_inst id cond_op out) st = Error e
Proof
  rw[step_inst_base_def, mk_iszero_inst_def, exec_pure1_def, eval_operand_def]
QED

(* step_inst_base for ASSERT when eval_operand fails *)
Triviality step_assert_eval_none:
  !id cond_op st.
    eval_operand cond_op st = NONE
  ==>
    ?e. step_inst_base (mk_assert_inst id cond_op) st = Error e
Proof
  rw[step_inst_base_def, mk_assert_inst_def, eval_operand_def]
QED

(* OK/OK simulation when states differ only by a fresh variable update.
   jump_to overrides vs_inst_idx, vs_prev_bb, vs_current_bb, so
   the update_var and vs_inst_idx change are invisible to state_equiv. *)
Triviality ok_ok_fresh_var_sim:
  !fresh bbs1 bbs2 lbl tmp v st k.
    tmp IN fresh ==>
    resolving_block_sim (state_equiv fresh) (execution_equiv fresh) bbs1 bbs2
      (OK (jump_to lbl st))
      (OK (jump_to lbl (update_var tmp v st with vs_inst_idx := k)))
Proof
  rpt strip_tac >>
  irule lift_result_resolving_block_sim >>
  simp[lift_result_def, state_equiv_def, jump_to_def, update_var_def,
       execution_equiv_def, lookup_var_def, finite_mapTheory.FLOOKUP_UPDATE] >>
  rw[] >> metis_tac[]
QED

(* Revert resolution with fresh var: original jumps to revert label,
   transformed already Aborted with an extra fresh var update.
   Combines revert_resolves_to + execution_equiv proof. *)
Triviality revert_fresh_var_sim:
  !fn bbs2 revert_lbl st tmp v k fresh.
    ~st.vs_halted /\
    is_revert_label fn revert_lbl /\
    tmp IN fresh
  ==>
    resolving_block_sim (state_equiv fresh) (execution_equiv fresh)
      fn.fn_blocks bbs2
      (OK (jump_to revert_lbl st))
      (Abort Revert_abort (revert_state (set_returndata []
        (update_var tmp v st with vs_inst_idx := k))))
Proof
  rpt strip_tac >>
  rw[resolving_block_sim_def] >>
  qexists_tac `SUC 0` >>
  irule resolves_to_step_ok >>
  conj_tac >- simp[jump_to_def] >>
  `?rbb. lookup_block revert_lbl fn.fn_blocks = SOME rbb /\
         is_simple_revert_block rbb` by (
    fs[is_revert_label_def] >>
    Cases_on `lookup_block revert_lbl fn.fn_blocks` >> fs[]
  ) >>
  qexists_tac `rbb` >> simp[] >>
  conj_tac >- (
    (* ∀fuel ctx. lift_result ... *)
    rpt strip_tac >>
    `EVERY (\inst. inst.inst_opcode <> PHI) rbb.bb_instructions` by (
      fs[is_simple_revert_block_def] >> Cases_on `rbb.bb_instructions` >> fs[]) >>
    (* Prove what run_block_entry returns *)
    `run_block_entry fuel ctx rbb (jump_to revert_lbl st) =
       Abort Revert_abort (revert_state (set_returndata [] (jump_to revert_lbl st)))` by (
      match_mp_tac run_revert_block_entry >> simp[jump_to_def]
    ) >>
    (* Now expand lift_result, jump_to, execution_equiv, etc. *)
    simp[lift_result_def, jump_to_def, execution_equiv_def, revert_state_def,
         set_returndata_def, update_var_def, lookup_var_def,
         finite_mapTheory.FLOOKUP_UPDATE] >>
    rw[] >> metis_tac[]
  ) >>
  simp[jump_to_def]
QED

(* Revert resolution: when original jumps to a revert label,
   and transformed already Aborted, we get resolving_block_sim via resolves_to 1 *)
Triviality revert_resolves_to:
  !fn bbs2 revert_lbl st st2 fresh.
    ~st.vs_halted /\
    is_revert_label fn revert_lbl /\
    execution_equiv fresh
      (revert_state (set_returndata []
        (st with <| vs_prev_bb := SOME st.vs_current_bb;
                    vs_current_bb := revert_lbl; vs_inst_idx := 0 |>)))
      st2
  ==>
    resolving_block_sim (state_equiv fresh) (execution_equiv fresh)
      fn.fn_blocks bbs2
      (OK (jump_to revert_lbl st))
      (Abort Revert_abort st2)
Proof
  rpt strip_tac >>
  rw[resolving_block_sim_def] >>
  qexists_tac `SUC 0` >>
  irule resolves_to_step_ok >>
  conj_tac >- simp[jump_to_def] >>
  `?rbb. lookup_block revert_lbl fn.fn_blocks = SOME rbb /\
         is_simple_revert_block rbb` by (
    fs[is_revert_label_def] >>
    Cases_on `lookup_block revert_lbl fn.fn_blocks` >> fs[]
  ) >>
  qexists_tac `rbb` >> simp[] >>
  conj_tac >- (
    rpt strip_tac >>
    `EVERY (\inst. inst.inst_opcode <> PHI) rbb.bb_instructions` by (
      fs[is_simple_revert_block_def] >> Cases_on `rbb.bb_instructions` >> fs[]) >>
    (* Prove what run_block_entry returns *)
    `run_block_entry fuel ctx rbb (jump_to revert_lbl st) =
       Abort Revert_abort (revert_state (set_returndata [] (jump_to revert_lbl st)))` by (
      match_mp_tac run_revert_block_entry >> simp[jump_to_def]
    ) >>
    (* Expand lift_result, normalize both goal and assumption, use execution_equiv assumption *)
    fs[lift_result_def, jump_to_def, revert_state_def, set_returndata_def,
       Excl "run_block_def", Excl "run_block_entry_def", Excl "eval_phis_def",
       Excl "phi_prefix_length_def", Excl "eval_one_phi_def", Excl "run_blocks_def"]
  ) >>
  simp[jump_to_def]
QED

(* Pattern 1 transformed block execution: ISZERO+ASSERT+(JMP or Abort)
   When cond=0w: ISZERO→1w, ASSERT passes, JMP→if_zero
   When cond≠0w: ISZERO→0w, ASSERT fails→Abort *)
Triviality pattern1_transformed_execution:
  !bb st fuel ctx id cond_op tmp if_zero cond.
    EL st.vs_inst_idx bb.bb_instructions = mk_iszero_inst id cond_op tmp /\
    EL (SUC st.vs_inst_idx) bb.bb_instructions =
      mk_assert_inst (id + 1) (Var tmp) /\
    EL (SUC (SUC st.vs_inst_idx)) bb.bb_instructions =
      mk_jmp_inst (id + 2) if_zero /\
    st.vs_inst_idx + 3 <= LENGTH bb.bb_instructions /\
    eval_operand cond_op st = SOME cond /\
    ~st.vs_halted
  ==>
    exec_block fuel ctx bb st =
      if cond = 0w then
        OK (jump_to if_zero (update_var tmp 1w st
              with vs_inst_idx := SUC (SUC st.vs_inst_idx)))
      else
        Abort Revert_abort (revert_state (set_returndata []
          (update_var tmp 0w st with vs_inst_idx := SUC st.vs_inst_idx)))
Proof
  rpt strip_tac >>
  (* Step 1: ISZERO — evaluate step_inst_base *)
  imp_res_tac step_iszero_value >>
  (* Step 2: ASSERT — establish eval_operand for fresh var *)
  `eval_operand (Var tmp) (update_var tmp (bool_to_word (cond = 0w)) st
     with vs_inst_idx := SUC st.vs_inst_idx) =
   SOME (bool_to_word (cond = 0w))` by
    simp[eval_operand_def, lookup_var_def, update_var_def,
         finite_mapTheory.FLOOKUP_UPDATE] >>
  imp_res_tac step_assert_behavior >>
  (* Case split on cond, then unfold exec_block *)
  Cases_on `cond = 0w` >> fs[bool_to_word_def]
  (* cond = 0w: ISZERO→1w, ASSERT passes, JMP to if_zero *)
  >- (
    ONCE_REWRITE_TAC [exec_block_def] >>
    simp[get_instruction_def, mk_iszero_inst_def,
         step_inst_non_invoke, is_terminator_def] >> fs[] >>
    ONCE_REWRITE_TAC [exec_block_def] >>
    simp[get_instruction_def, mk_assert_inst_def,
         step_inst_non_invoke, is_terminator_def] >> fs[] >>
    ONCE_REWRITE_TAC [exec_block_def] >>
    simp[get_instruction_def, mk_jmp_inst_def,
         step_inst_non_invoke, step_jmp_behavior, is_terminator_def,
         jump_to_def, update_var_def]
  )
  (* cond <> 0w: ISZERO→0w, ASSERT fails→Abort *)
  >- (
    ONCE_REWRITE_TAC [exec_block_def] >>
    simp[get_instruction_def, mk_iszero_inst_def,
         step_inst_non_invoke, is_terminator_def] >> fs[] >>
    ONCE_REWRITE_TAC [exec_block_def] >>
    simp[get_instruction_def, mk_assert_inst_def,
         step_inst_non_invoke, is_terminator_def] >> fs[]
  )
QED

(* Pattern 1 full simulation: resolving_block_sim for the JNZ→ISZERO+ASSERT+JMP case.
   Establishes both exec_block results separately, then closes by case split. *)
Triviality pattern1_sim:
  !fn fresh bb inst cond_op if_zero if_nonzero st fuel ctx cond.
    Abbrev (inst = EL st.vs_inst_idx bb.bb_instructions) /\
    inst.inst_opcode = JNZ /\
    inst.inst_operands = [cond_op; Label if_nonzero; Label if_zero] /\
    is_revert_label fn if_nonzero /\
    transform_jnz fn inst = SOME (transform_pattern1 inst cond_op if_zero) /\
    eval_operand cond_op st = SOME cond /\
    MEM bb fn.fn_blocks /\
    fresh_vars_in_function fn SUBSET fresh /\
    fresh_vars_not_in_function fn /\
    no_invoke_in_function fn /\
    st.vs_inst_idx < LENGTH bb.bb_instructions /\
    (!j. j < st.vs_inst_idx ==>
         transform_jnz fn (EL j bb.bb_instructions) = NONE) /\
    ~st.vs_halted
  ==>
    resolving_block_sim (state_equiv fresh) (execution_equiv fresh)
      fn.fn_blocks (MAP (transform_block fn) fn.fn_blocks)
      (exec_block fuel ctx bb st)
      (exec_block fuel ctx (transform_block fn bb) st)
Proof
  rpt strip_tac >>
  qabbrev_tac `tmp = fresh_iszero_var inst.inst_id` >>
  `MEM inst bb.bb_instructions` by metis_tac[listTheory.MEM_EL, Abbr `inst`] >>
  (* Establish original exec_block result *)
  imp_res_tac step_jnz_general >>
  `inst.inst_opcode <> INVOKE` by (
    irule no_invoke_mem_inst >> metis_tac[]) >>
  `exec_block fuel ctx bb st =
     if cond <> 0w then OK (jump_to if_nonzero st)
     else OK (jump_to if_zero st)` by (
    ONCE_REWRITE_TAC [exec_block_def] >>
    simp[get_instruction_def, step_inst_non_invoke,
         is_terminator_def, jump_to_def, update_var_def] >>
    Cases_on `cond = 0w` >> simp[]
  ) >>
  (* Establish transformed exec_block result *)
  `st.vs_inst_idx + 3 <= LENGTH (transform_block_insts fn bb.bb_instructions)` by (
    `st.vs_inst_idx + LENGTH (transform_pattern1 inst cond_op if_zero) <=
       LENGTH (transform_block_insts fn bb.bb_instructions)` suffices_by
      simp[transform_pattern1_def, LET_THM] >>
    irule transform_block_insts_length_at >> simp[Abbr `inst`]
  ) >>
  `EL st.vs_inst_idx (transform_block_insts fn bb.bb_instructions) =
     mk_iszero_inst inst.inst_id cond_op tmp` by (
    `EL (st.vs_inst_idx + 0) (transform_block_insts fn bb.bb_instructions) =
      EL 0 (transform_pattern1 inst cond_op if_zero)` by (
      irule transform_block_insts_EL >>
      simp[Abbr `inst`, transform_pattern1_def, LET_THM]) >>
    fs[transform_pattern1_def, LET_THM, Abbr `tmp`]
  ) >>
  `EL (SUC st.vs_inst_idx) (transform_block_insts fn bb.bb_instructions) =
     mk_assert_inst (inst.inst_id + 1) (Var tmp)` by (
    `EL (st.vs_inst_idx + 1) (transform_block_insts fn bb.bb_instructions) =
      EL 1 (transform_pattern1 inst cond_op if_zero)` by (
      irule transform_block_insts_EL >>
      simp[Abbr `inst`, transform_pattern1_def, LET_THM]) >>
    pop_assum mp_tac >>
    `st.vs_inst_idx + 1 = SUC st.vs_inst_idx` by simp[] >>
    pop_assum (fn th => PURE_REWRITE_TAC [th]) >>
    simp[transform_pattern1_def, LET_THM, Abbr `tmp`]
  ) >>
  `EL (SUC (SUC st.vs_inst_idx)) (transform_block_insts fn bb.bb_instructions) =
     mk_jmp_inst (inst.inst_id + 2) if_zero` by (
    `EL (st.vs_inst_idx + 2) (transform_block_insts fn bb.bb_instructions) =
      EL 2 (transform_pattern1 inst cond_op if_zero)` by (
      irule transform_block_insts_EL >>
      simp[Abbr `inst`, transform_pattern1_def, LET_THM]) >>
    pop_assum mp_tac >>
    `st.vs_inst_idx + 2 = SUC (SUC st.vs_inst_idx)` by simp[] >>
    pop_assum (fn th => PURE_REWRITE_TAC [th]) >>
    simp[transform_pattern1_def, LET_THM]
  ) >>
  `exec_block fuel ctx (transform_block fn bb) st =
     if cond = 0w then
       OK (jump_to if_zero (update_var tmp 1w st
             with vs_inst_idx := SUC (SUC st.vs_inst_idx)))
     else
       Abort Revert_abort (revert_state (set_returndata []
         (update_var tmp 0w st with vs_inst_idx := SUC st.vs_inst_idx)))` by (
    simp[transform_block_def] >>
    qspecl_then
      [`bb with bb_instructions := transform_block_insts fn bb.bb_instructions`,
       `st`, `fuel`, `ctx`, `inst.inst_id`, `cond_op`, `tmp`, `if_zero`, `cond`]
      mp_tac pattern1_transformed_execution >>
    simp[]
  ) >>
  (* Case split and close *)
  (* Substitute exec_block results into the goal before case splitting *)
  qpat_x_assum `exec_block fuel ctx bb st = _` (fn th => REWRITE_TAC [th]) >>
  qpat_x_assum `exec_block fuel ctx (transform_block fn bb) st = _`
    (fn th => REWRITE_TAC [th]) >>
  (* Drop EL and step_inst_base assumptions that cause simp loops *)
  ntac 3 (pop_assum kall_tac) >> (* EL facts *)
  qpat_x_assum `st.vs_inst_idx + 3 <= _` kall_tac >>
  qpat_x_assum `step_inst_base _ _ = _` kall_tac >>
  qpat_x_assum `inst.inst_opcode <> INVOKE` kall_tac >>
  `tmp IN fresh` by (
    simp[Abbr `tmp`] >>
    qspecl_then [`fn`, `fresh`, `bb`, `inst`, `cond_op`, `if_nonzero`, `if_zero`]
      mp_tac fresh_iszero_var_in_fresh >> simp[]
  ) >>
  Cases_on `cond = 0w`
  >- (
    simp[] >> irule ok_ok_fresh_var_sim >> simp[]
  )
  >- (
    simp[] >> irule revert_fresh_var_sim >> simp[]
  )
QED

(* Generalized per-block sim for arbitrary vs_inst_idx *)
Triviality rta_per_block_sim_gen:
  !n fn fresh bb fuel ctx s.
    n = LENGTH bb.bb_instructions - s.vs_inst_idx /\
    fresh_vars_in_function fn SUBSET fresh /\
    fresh_vars_not_in_function fn /\
    no_invoke_in_function fn /\
    MEM bb fn.fn_blocks /\
    (!j. j < s.vs_inst_idx ==> transform_jnz fn (EL j bb.bb_instructions) = NONE) /\
    ~s.vs_halted
  ==>
    resolving_block_sim (state_equiv fresh) (execution_equiv fresh)
      fn.fn_blocks (MAP (transform_block fn) fn.fn_blocks)
      (exec_block fuel ctx bb s)
      (exec_block fuel ctx (transform_block fn bb) s)
Proof
  Induct_on `n` >> rpt strip_tac >>
  rename1 `exec_block fuel ctx bb st`
  (* === Base case: 0 = LENGTH - idx, i.e. idx >= LENGTH === *)
  >- (
    `~(st.vs_inst_idx < LENGTH bb.bb_instructions)` by simp[] >>
    `~(st.vs_inst_idx < LENGTH (transform_block_insts fn bb.bb_instructions))` by (
      `transform_block_insts fn bb.bb_instructions = bb.bb_instructions` by (
        irule all_none_transform_block_insts >>
        rpt strip_tac >>
        Cases_on `j < st.vs_inst_idx` >- metis_tac[] >>
        fs[transform_jnz_def, get_instruction_def]
      ) >> simp[]
    ) >>
    simp[Once exec_block_def, get_instruction_def] >>
    simp[transform_block_def, Once exec_block_def, get_instruction_def] >>
    rw[resolving_block_sim_def] >> qexists_tac `0` >>
    rw[resolves_to_def, lift_result_def]
  )
  (* === Step case: SUC n = LENGTH - idx, i.e. idx < LENGTH === *)
  >- (
    `st.vs_inst_idx < LENGTH bb.bb_instructions` by simp[] >>
    `st.vs_inst_idx < LENGTH (transform_block_insts fn bb.bb_instructions)` by
      metis_tac[transform_block_insts_length, LESS_LESS_EQ_TRANS] >>
    `EL st.vs_inst_idx (transform_block_insts fn bb.bb_instructions) =
      (case transform_jnz fn (EL st.vs_inst_idx bb.bb_instructions) of
         NONE => EL st.vs_inst_idx bb.bb_instructions
       | SOME new_insts => HD new_insts)` by (
      irule transform_block_insts_index >> simp[]
    ) >>
    qabbrev_tac `inst = EL st.vs_inst_idx bb.bb_instructions` >>
    `inst.inst_opcode <> INVOKE` by (
      irule no_invoke_mem_inst >> metis_tac[listTheory.MEM_EL]
    ) >>
    (* Case split on transform_jnz BEFORE unfolding exec_block *)
    Cases_on `transform_jnz fn inst`
    >- (
      (* transform_jnz = NONE: same instruction on both sides *)
      simp[transform_block_def] >>
      ONCE_REWRITE_TAC [exec_block_def] >>
      simp[get_instruction_def] >>
      simp[step_inst_non_invoke] >>
      Cases_on `step_inst_base inst st` >> simp[]
      >- (
        rename1 `step_inst_base inst st = OK st'` >>
        Cases_on `is_terminator inst.inst_opcode`
        >- (
          simp[] >>
          Cases_on `st'.vs_halted` >> simp[]
          >- (rw[resolving_block_sim_def] >> qexists_tac `0` >>
              rw[resolves_to_def, lift_result_def, execution_equiv_refl])
          >- (rw[resolving_block_sim_def] >> qexists_tac `0` >>
              rw[resolves_to_def, lift_result_def, state_equiv_refl])
        )
        >- (
          (* non-terminator, OK: use IH *)
          simp[] >>
          `~st'.vs_halted` by metis_tac[step_inst_base_OK_preserves_halted] >>
          qpat_x_assum `!fn fresh bb fuel ctx s. _` (qspecl_then
            [`fn`, `fresh`, `bb`, `fuel`, `ctx`,
             `st' with vs_inst_idx := SUC st.vs_inst_idx`] mp_tac) >>
          simp[] >>
          impl_tac
          >- (
            rpt strip_tac >>
            Cases_on `j < st.vs_inst_idx` >- metis_tac[] >>
            `j = st.vs_inst_idx` by fs[] >> fs[Abbr`inst`]
          )
          >- simp[transform_block_def]
        )
      )
      >- (rw[resolving_block_sim_def] >> qexists_tac `0` >>
          rw[resolves_to_def, lift_result_def, execution_equiv_refl])
      >- (rw[resolving_block_sim_def] >> qexists_tac `0` >>
          rw[resolves_to_def, lift_result_def, execution_equiv_refl])
      >- (rw[resolving_block_sim_def] >> qexists_tac `0` >>
          rw[resolves_to_def, lift_result_def, execution_equiv_refl])
      >- (rw[resolving_block_sim_def] >> qexists_tac `0` >>
          rw[resolves_to_def, lift_result_def])
    )
    >- (
      (* transform_jnz = SOME x: JNZ transformation case *)
      imp_res_tac transform_jnz_SOME
      (* === Pattern 1: is_revert_label fn if_nonzero === *)
      >- (
        `MEM inst bb.bb_instructions` by metis_tac[listTheory.MEM_EL, Abbr `inst`] >>
        (* Use pattern1_sim for the eval_operand = SOME case *)
        Cases_on `eval_operand cond_op st`
        >- (
          (* eval_operand = NONE: both sides Error *)
          simp[transform_block_def] >>
          ONCE_REWRITE_TAC [exec_block_def] >>
          simp[get_instruction_def] >>
          fs[] >>
          simp[transform_pattern1_def, LET_THM] >>
          `?e. step_inst_base inst st = Error e` by
            metis_tac[step_jnz_eval_none] >>
          `?e. step_inst_base
            (mk_iszero_inst inst.inst_id cond_op (fresh_iszero_var inst.inst_id))
            st = Error e` by
            metis_tac[step_iszero_eval_none] >>
          simp[step_inst_non_invoke, mk_iszero_inst_def] >>
          rw[resolving_block_sim_def] >> qexists_tac `0` >>
          rw[resolves_to_def, lift_result_def]
        )
        >- (
          (* eval_operand = SOME: use pattern1_sim directly *)
          rename1 `eval_operand cond_op st = SOME cond` >>
          qspecl_then
            [`fn`, `fresh`, `bb`, `inst`, `cond_op`, `if_zero`, `if_nonzero`,
             `st`, `fuel`, `ctx`, `cond`]
            mp_tac pattern1_sim >>
          simp[markerTheory.Abbrev_def]
        )
      )
      (* === Pattern 2: is_revert_label fn if_zero === *)
      >- (
        simp[transform_block_def] >>
        ONCE_REWRITE_TAC [exec_block_def] >>
        simp[get_instruction_def] >>
        fs[] >>
        simp[step_inst_non_invoke, is_terminator_def] >>
        `MEM inst bb.bb_instructions` by metis_tac[listTheory.MEM_EL, Abbr `inst`] >>
        fs[] >>
        simp[transform_pattern2_def, LET_THM] >>
        Cases_on `eval_operand cond_op st`
        >- (
          `?e. step_inst_base inst st = Error e` by metis_tac[step_jnz_eval_none] >>
          `?e. step_inst_base (mk_assert_inst inst.inst_id cond_op) st = Error e` by
            metis_tac[step_assert_eval_none] >>
          simp[step_inst_non_invoke, mk_assert_inst_def] >>
          rw[resolving_block_sim_def] >> qexists_tac `0` >>
          rw[resolves_to_def, lift_result_def]
        )
        >- (
          rename1 `eval_operand cond_op st = SOME cond` >>
          imp_res_tac step_jnz_general >> simp[] >>
          simp[mk_assert_inst_def, step_inst_non_invoke, is_terminator_def] >>
          imp_res_tac step_assert_behavior >> fs[] >>
          Cases_on `cond = 0w`
          >- (
            (* cond = 0w: ASSERT fails, original jumps to revert label *)
            fs[bool_to_word_def] >>
            `~(jump_to if_zero st).vs_halted` by simp[jump_to_def] >>
            fs[] >>
            irule revert_resolves_to >> simp[] >>
            simp[execution_equiv_def, revert_state_def, set_returndata_def,
                 lookup_var_def, jump_to_def]
          )
          >- (
            (* cond <> 0w: ASSERT passes, JMP to if_nonzero *)
            fs[] >>
            ONCE_REWRITE_TAC [exec_block_def] >>
            simp[get_instruction_def] >>
            `st.vs_inst_idx + 2 <= LENGTH (transform_block_insts fn bb.bb_instructions)` by (
              `st.vs_inst_idx + LENGTH (transform_pattern2 inst cond_op if_nonzero) <=
                 LENGTH (transform_block_insts fn bb.bb_instructions)` suffices_by
                simp[transform_pattern2_def, LET_THM] >>
              irule transform_block_insts_length_at >> simp[Abbr `inst`]
            ) >>
            simp[] >>
            `EL (SUC st.vs_inst_idx) (transform_block_insts fn bb.bb_instructions) =
               mk_jmp_inst (inst.inst_id + 1) if_nonzero` by (
              `EL (st.vs_inst_idx + 1) (transform_block_insts fn bb.bb_instructions) =
                EL 1 (transform_pattern2 inst cond_op if_nonzero)` by (
                irule transform_block_insts_EL >>
                simp[Abbr `inst`, transform_pattern2_def, LET_THM]) >>
              pop_assum mp_tac >>
              `st.vs_inst_idx + 1 = SUC st.vs_inst_idx` by simp[] >>
              pop_assum (fn th => PURE_REWRITE_TAC [th]) >>
              simp[transform_pattern2_def, LET_THM]
            ) >>
            simp[mk_jmp_inst_def, step_inst_non_invoke, step_jmp_behavior,
                 is_terminator_def, jump_to_def] >>
            rw[resolving_block_sim_def] >> qexists_tac `0` >>
            rw[resolves_to_def, lift_result_def, state_equiv_refl]
          )
        )
      )
    )
  )
QED

(* Main per-block sim: specialization to vs_inst_idx = 0 *)
Triviality rta_per_block_sim:
  !fn fresh.
    fresh_vars_in_function fn SUBSET fresh /\
    fresh_vars_not_in_function fn /\
    no_invoke_in_function fn
  ==>
    !bb fuel ctx s.
      MEM bb fn.fn_blocks /\ s.vs_inst_idx = 0 /\ ~s.vs_halted ==>
      resolving_block_sim (state_equiv fresh) (execution_equiv fresh)
        fn.fn_blocks (MAP (transform_block fn) fn.fn_blocks)
        (exec_block fuel ctx bb s)
        (exec_block fuel ctx (transform_block fn bb) s)
Proof
  rpt strip_tac >>
  irule rta_per_block_sim_gen >> simp[]
QED

(* ===== PHI prefix preservation by transform_block_insts ===== *)

(* transform_jnz returns NONE for non-JNZ instructions *)
Triviality transform_jnz_not_jnz:
  !fn inst. inst.inst_opcode <> JNZ ==> transform_jnz fn inst = NONE
Proof
  rw[transform_jnz_def]
QED

(* PHI instructions are untouched by transform_jnz *)
Triviality transform_jnz_phi:
  !fn inst. inst.inst_opcode = PHI ==> transform_jnz fn inst = NONE
Proof
  rw[transform_jnz_def]
QED

(* transform_jnz output never contains PHI *)
Triviality transform_jnz_output_no_phis:
  !fn inst new_insts.
    transform_jnz fn inst = SOME new_insts ==>
    EVERY (\i. i.inst_opcode <> PHI) new_insts
Proof
  rw[transform_jnz_def] >>
  BasicProvers.every_case_tac >> fs[] >>
  rw[transform_pattern1_def, transform_pattern2_def, LET_THM,
     mk_iszero_inst_def, mk_assert_inst_def, mk_jmp_inst_def]
QED

(* phi_prefix_length is preserved by transform_block_insts *)
Triviality transform_block_insts_phi_prefix_length:
  !fn insts. phi_prefix_length (transform_block_insts fn insts) = phi_prefix_length insts
Proof
  Induct_on `insts` >> rpt strip_tac >>
  simp[Once transform_block_insts_def] >>
  Cases_on `h.inst_opcode = PHI`
  >- (
    (* h is PHI: transform_jnz gives NONE, h stays, phi_prefix = SUC on both sides *)
    `transform_jnz fn h = NONE` by simp[transform_jnz_phi] >>
    simp[phi_prefix_length_def]
  ) >>
  (* h is not PHI: phi_prefix_length of (h::insts) = 0 *)
  simp[phi_prefix_length_def] >>
  Cases_on `transform_jnz fn h` >> simp[]
  >- (
    (* NONE: h stays as-is, phi_prefix of (h :: rest) = 0 since h not PHI *)
    simp[phi_prefix_length_def]
  ) >>
  (* SOME x: replace h with x. First element of x is not PHI. *)
  imp_res_tac transform_jnz_nonempty >>
  Cases_on `x`
  >- (
    (* x = [] is impossible since x ≠ [] *)
    fs[]
  ) >>
  (* x = h'::t; h' is ISZERO/ASSERT/JMP, never PHI *)
  `EVERY (\i. i.inst_opcode <> PHI) (h'::t)` by (
    metis_tac[transform_jnz_output_no_phis]) >>
  fs[phi_prefix_length_def]
QED

(* Elements in the PHI prefix are preserved by transform_block_insts *)
Triviality transform_block_insts_phi_prefix_el:
  !fn insts i.
    i < phi_prefix_length insts ==>
    EL i (transform_block_insts fn insts) = EL i insts
Proof
  Induct_on `insts` >> rpt strip_tac
  >- (
    (* base case: phi_prefix_length [] = 0, so i < 0 is impossible *)
    fs[phi_prefix_length_def] >> Cases_on `i` >> fs[]
  ) >>
  Cases_on `h.inst_opcode = PHI`
  >- (
    (* h is PHI: transform_jnz gives NONE, h stays unchanged *)
    `transform_jnz fn h = NONE` by simp[transform_jnz_phi] >>
    simp[Once transform_block_insts_def, phi_prefix_length_def] >>
    Cases_on `i` >> simp[] >> fs[phi_prefix_length_def]
  ) >>
  (* h is not PHI: phi_prefix_length = 0, contradiction with i < 0 *)
  fs[phi_prefix_length_def] >> Cases_on `i` >> fs[]
QED

(* key lemma: eval_phis gives same result for original and transformed instructions *)
Triviality eval_phis_transform_block_insts:
  !fn s insts.
    eval_phis s (transform_block_insts fn insts) = eval_phis s insts
Proof
  rpt strip_tac >>
  match_mp_tac (GSYM eval_phis_same_phi_prefix) >>
  simp[transform_block_insts_phi_prefix_length] >>
  rpt strip_tac >>
  irule transform_block_insts_phi_prefix_el >> simp[]
QED

(* transform_block_insts preserves no_phis *)
Triviality transform_block_insts_no_phis:
  !fn insts.
    EVERY (\i. i.inst_opcode <> PHI) insts ==>
    EVERY (\i. i.inst_opcode <> PHI) (transform_block_insts fn insts)
Proof
  Induct_on `insts` >> rw[transform_block_insts_def] >>
  Cases_on `transform_jnz fn h` >> gvs[] >>
  drule transform_jnz_output_no_phis >> simp[]
QED

(* transform_jnz = NONE for all instructions before phi_prefix_length point *)
Triviality transform_jnz_none_before_phi_prefix:
  !fn insts j.
    j < phi_prefix_length insts ==>
    transform_jnz fn (EL j insts) = NONE
Proof
  Induct_on `insts` >> rpt strip_tac
  >- (
    (* base: phi_prefix_length [] = 0, i < 0 impossible *)
    fs[phi_prefix_length_def] >> Cases_on `j` >> fs[]
  ) >>
  Cases_on `h.inst_opcode = PHI`
  >- (
    (* h is PHI: transform_jnz fn h = NONE; for j=0 use transform_jnz_phi,
       for SUC j use IH *)
    simp[phi_prefix_length_def] >> Cases_on `j`
    >- simp[transform_jnz_phi]
    >- (fs[phi_prefix_length_def] >> first_x_assum drule >> simp[])
  ) >>
  (* h not PHI: phi_prefix_length = 0, contradiction with j < 0 *)
  fs[phi_prefix_length_def] >> Cases_on `j` >> fs[]
QED

(* ===== Bridge: exec_block-level sim → run_block_entry-level sim ===== *)

(* eval_phis_preserves_halted is now in venomExecProofsTheory *)

Theorem rta_run_block_entry_sim:
  !fn fresh bb fuel ctx s.
    fresh_vars_in_function fn SUBSET fresh /\
    fresh_vars_not_in_function fn /\
    no_invoke_in_function fn /\
    MEM bb fn.fn_blocks /\
    s.vs_inst_idx = 0 /\ ~s.vs_halted
  ==>
    resolving_block_sim (state_equiv fresh) (execution_equiv fresh)
      fn.fn_blocks (MAP (transform_block fn) fn.fn_blocks)
      (run_block_entry fuel ctx bb s)
      (run_block_entry fuel ctx (transform_block fn bb) s)
Proof
  qx_gen_tac `fn` >> qx_gen_tac `fresh` >> qx_gen_tac `bb` >>
  qx_gen_tac `fuel` >> qx_gen_tac `ctx` >> qx_gen_tac `st` >>
  strip_tac >>
  DISJ_CASES_TAC (Q.SPECL [`st`, `bb.bb_instructions`] eval_phis_ok_or_error_defs) >-
    (* OK case: eval_phis st bb.bb_instructions = OK s_phi *)
    (first_x_assum (qx_choose_then `s_phi` assume_tac) >>
     fs[] >>
     `~s_phi.vs_halted` by metis_tac[eval_phis_preserves_halted] >>
     `eval_phis st (transform_block fn bb).bb_instructions = OK s_phi` by
       simp[transform_block_def, eval_phis_transform_block_insts] >>
     `phi_prefix_length (transform_block fn bb).bb_instructions =
       phi_prefix_length bb.bb_instructions` by
       simp[transform_block_def, transform_block_insts_phi_prefix_length] >>
     `run_block_entry fuel ctx bb st =
       exec_block fuel ctx bb
         (s_phi with vs_inst_idx := phi_prefix_length bb.bb_instructions)` by
       metis_tac[run_block_entry_eval_phis_OK] >>
     `run_block_entry fuel ctx (transform_block fn bb) st =
       exec_block fuel ctx (transform_block fn bb)
         (s_phi with vs_inst_idx := phi_prefix_length (transform_block fn bb).bb_instructions)` by
       metis_tac[run_block_entry_eval_phis_OK] >>
     pop_assum (fn th => PURE_ONCE_REWRITE_TAC[th]) >>
     pop_assum (fn th => PURE_ONCE_REWRITE_TAC[th]) >>
     fs[] >>
     irule rta_per_block_sim_gen >> simp[] >>
     metis_tac[transform_jnz_none_before_phi_prefix]) >>
  (* Error case: eval_phis st bb.bb_instructions = Error e *)
  first_x_assum (qx_choose_then `e` assume_tac) >>
  fs[] >>
  `eval_phis st (transform_block fn bb).bb_instructions = Error e` by
    simp[transform_block_def, eval_phis_transform_block_insts] >>
  `run_block_entry fuel ctx bb st = Error e` by
    metis_tac[run_block_entry_eval_phis_Error] >>
  `run_block_entry fuel ctx (transform_block fn bb) st = Error e` by
    metis_tac[run_block_entry_eval_phis_Error] >>
  irule lift_result_resolving_block_sim >>
  simp[lift_result_def]
QED

(* ===== Context-level lookup lemmas ===== *)

Triviality lookup_function_transform:
  !entry fns fn.
    lookup_function entry fns = SOME fn ==>
    lookup_function entry (MAP transform_function fns) = SOME (transform_function fn)
Proof
  Induct_on `fns` >> rw[lookup_function_def] >>
  pop_assum mp_tac >>
  PURE_ONCE_REWRITE_TAC[listTheory.FIND_thm] >> simp[] >>
  `(transform_function h).fn_name = h.fn_name` by
    simp[transform_function_def] >>
  Cases_on `h.fn_name = entry` >> simp[] >> rw[] >>
  fs[lookup_function_def]
QED

(* ===== Main theorem ===== *)

Theorem rta_pass_correct_proof:
  !ctx entry.
    fresh_vars_not_in_context ctx /\
    no_invoke_in_context ctx /\
    lookup_function entry ctx.ctx_functions <> NONE
  ==>
    let ctx' = transform_context ctx in
    let fresh = fresh_vars_in_context ctx in
    ?fn fn'.
      lookup_function entry ctx.ctx_functions = SOME fn /\
      lookup_function entry ctx'.ctx_functions = SOME fn' /\
      !s. s.vs_inst_idx = 0 /\ ~s.vs_halted ==>
          pass_correct (state_equiv fresh) (execution_equiv fresh) (execution_equiv fresh)
            (\fuel. run_blocks fuel ctx fn s)
            (\fuel. run_blocks fuel ctx fn' s)
Proof
  rw[LET_THM] >>
  (* Unpack fn from lookup *)
  Cases_on `lookup_function entry ctx.ctx_functions` >> fs[] >>
  rename1 `lookup_function entry ctx.ctx_functions = SOME fn` >>
  qexists_tac `transform_function fn` >>
  conj_tac >- (
    rw[transform_context_def] >>
    irule lookup_function_transform >> simp[]
  ) >>
  (* transform_function = function_map_transform *)
  `transform_function fn = function_map_transform (transform_block fn) fn` by
    simp[transform_function_is_fmt] >>
  (* Collect preconditions for _v2 *)
  imp_res_tac lookup_function_MEM >>
  `fresh_vars_not_in_function fn` by fs[fresh_vars_not_in_context_def] >>
  `no_invoke_in_function fn` by
    fs[no_invoke_in_context_def, listTheory.EVERY_MEM] >>
  `fresh_vars_in_function fn SUBSET fresh_vars_in_context ctx` by (
    rw[fresh_vars_in_context_def, SUBSET_DEF, PULL_EXISTS] >>
    metis_tac[]
  ) >>
  (* Establish _v2 conclusion *)
  `!ctx' s. s.vs_inst_idx = 0 /\ ~s.vs_halted ==>
    ((?fuel. terminates (run_blocks fuel ctx' fn s)) <=>
     (?fuel'. terminates (run_blocks fuel' ctx'
        (function_map_transform (transform_block fn) fn) s))) /\
    (!fuel fuel'.
       terminates (run_blocks fuel ctx' fn s) /\
       terminates (run_blocks fuel' ctx'
         (function_map_transform (transform_block fn) fn) s) ==>
       lift_result (state_equiv (fresh_vars_in_context ctx))
         (execution_equiv (fresh_vars_in_context ctx))
         (execution_equiv (fresh_vars_in_context ctx))
         (run_blocks fuel ctx' fn s)
         (run_blocks fuel' ctx'
           (function_map_transform (transform_block fn) fn) s))` by (
    qspecl_then [`state_equiv (fresh_vars_in_context ctx)`,
                 `execution_equiv (fresh_vars_in_context ctx)`,
                 `fn`, `transform_block fn`]
      mp_tac resolving_block_sim_function_v2 >>
    simp[LET_THM] >>
    impl_tac >- (
      rpt conj_tac
      >- simp[state_equiv_execution_equiv_valid_state_rel_proof]
      >- metis_tac[state_equiv_trans]
      >- metis_tac[execution_equiv_trans]
      >- simp[transform_block_label]
      >- (rw[function_map_transform_def] >> metis_tac[rta_run_block_entry_sim])
      >- (
        rpt gen_tac >> strip_tac >>
        rpt gen_tac >> strip_tac >>
        fs[state_equiv_def, execution_equiv_def] >>
        first_x_assum irule >>
        CCONTR_TAC >> fs[] >>
        imp_res_tac fresh_vars_ctx_are_iszero_vars >>
        fs[fresh_vars_not_in_function_def, fresh_vars_not_in_block_def] >>
        metis_tac[]
      )
      >- metis_tac[run_blocks_fuel_mono]
      >- metis_tac[run_blocks_fuel_mono]
    ) >>
    metis_tac[]
  ) >>
  (* Prove pass_correct *)
  rw[pass_correct_def]
QED
