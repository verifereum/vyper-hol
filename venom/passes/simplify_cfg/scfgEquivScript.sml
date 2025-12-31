(* 
 * Simplify-CFG Equivalence Lemmas
 *
 * Basic equivalence facts and state-operation preservation for CFG transforms.
 *)

Theory scfgEquiv
Ancestors
  scfgDefs stateEquiv venomSem venomState venomInst finite_map

(* ===== Equivalence Basics ===== *)

Theorem state_equiv_cfg_refl:
  !s. state_equiv_cfg s s
Proof
  rw[state_equiv_cfg_def, var_equiv_def]
QED

Theorem state_equiv_cfg_sym:
  !s1 s2. state_equiv_cfg s1 s2 ==> state_equiv_cfg s2 s1
Proof
  rw[state_equiv_cfg_def, var_equiv_def]
QED

Theorem state_equiv_cfg_trans:
  !s1 s2 s3.
    state_equiv_cfg s1 s2 /\ state_equiv_cfg s2 s3 ==> state_equiv_cfg s1 s3
Proof
  rw[state_equiv_cfg_def, var_equiv_def] >> metis_tac[]
QED

Theorem state_equiv_cfg_ctrl_eq:
  !s1 s2.
    state_equiv_cfg s1 s2 /\
    s1.vs_current_bb = s2.vs_current_bb /\
    s1.vs_prev_bb = s2.vs_prev_bb /\
    s1.vs_inst_idx = s2.vs_inst_idx ==>
    s1 = s2
Proof
  Cases_on `s1` >> Cases_on `s2` >>
  rw[state_equiv_cfg_def, var_equiv_def, lookup_var_def] >>
  simp[finite_mapTheory.fmap_eq_flookup, venomStateTheory.venom_state_11]
QED

Theorem result_equiv_cfg_refl:
  !r. result_equiv_cfg r r
Proof
  Cases >> rw[result_equiv_cfg_def, state_equiv_cfg_refl]
QED

Theorem result_equiv_cfg_sym:
  !r1 r2. result_equiv_cfg r1 r2 ==> result_equiv_cfg r2 r1
Proof
  Cases >> Cases >> rw[result_equiv_cfg_def, state_equiv_cfg_sym]
QED

Theorem result_equiv_cfg_trans:
  !r1 r2 r3. result_equiv_cfg r1 r2 /\ result_equiv_cfg r2 r3 ==> result_equiv_cfg r1 r3
Proof
  Cases >> Cases >> Cases >>
  simp[result_equiv_cfg_def] >> metis_tac[state_equiv_cfg_trans]
QED

Theorem run_function_equiv_cfg_refl:
  !fn s. run_function_equiv_cfg fn fn s
Proof
  rw[run_function_equiv_cfg_def]
  >- (qexists_tac `fuel` >> simp[result_equiv_cfg_refl])
  >- (qexists_tac `fuel'` >> simp[result_equiv_cfg_refl])
QED

Theorem run_function_equiv_cfg_trans:
  !fn1 fn2 fn3 s.
    run_function_equiv_cfg fn1 fn2 s /\
    run_function_equiv_cfg fn2 fn3 s ==> run_function_equiv_cfg fn1 fn3 s
Proof
  rw[run_function_equiv_cfg_def] >> metis_tac[result_equiv_cfg_trans]
QED

(* ===== Operand Evaluation under state_equiv_cfg ===== *)

Theorem eval_operand_state_equiv_cfg:
  !op s1 s2.
    state_equiv_cfg s1 s2 ==> eval_operand op s1 = eval_operand op s2
Proof
  Cases_on `op` >>
  rw[eval_operand_def, state_equiv_cfg_def, var_equiv_def]
QED

(* ===== Result Equivalence for Operand Execution ===== *)

Theorem exec_binop_result_equiv_cfg:
  !f inst s1 s2.
    state_equiv_cfg s1 s2 ==>
    result_equiv_cfg (exec_binop f inst s1) (exec_binop f inst s2)
Proof
  rw[exec_binop_def] >>
  simp[eval_operand_state_equiv_cfg] >>
  rpt (CASE_TAC >> gvs[result_equiv_cfg_def]) >>
  irule update_var_state_equiv_cfg >> simp[]
QED

Theorem exec_unop_result_equiv_cfg:
  !f inst s1 s2.
    state_equiv_cfg s1 s2 ==>
    result_equiv_cfg (exec_unop f inst s1) (exec_unop f inst s2)
Proof
  rw[exec_unop_def] >>
  simp[eval_operand_state_equiv_cfg] >>
  rpt (CASE_TAC >> gvs[result_equiv_cfg_def]) >>
  irule update_var_state_equiv_cfg >> simp[]
QED

Theorem exec_modop_result_equiv_cfg:
  !f inst s1 s2.
    state_equiv_cfg s1 s2 ==>
    result_equiv_cfg (exec_modop f inst s1) (exec_modop f inst s2)
Proof
  rw[exec_modop_def] >>
  simp[eval_operand_state_equiv_cfg] >>
  rpt (CASE_TAC >> gvs[result_equiv_cfg_def]) >>
  irule update_var_state_equiv_cfg >> simp[]
QED

(* ===== Instruction Stepping Preserves state_equiv_cfg ===== *)

Theorem step_inst_state_equiv_cfg:
  !inst s1 s2.
    state_equiv_cfg s1 s2 /\
    (inst.inst_opcode = PHI ==> s1.vs_prev_bb = s2.vs_prev_bb)
  ==>
    result_equiv_cfg (step_inst inst s1) (step_inst inst s2)
Proof
  rpt strip_tac >>
  Cases_on `inst.inst_opcode` >>
  simp[step_inst_def, result_equiv_cfg_def,
       exec_binop_result_equiv_cfg, exec_unop_result_equiv_cfg,
       exec_modop_result_equiv_cfg,
       eval_operand_state_equiv_cfg, update_var_state_equiv_cfg,
       mstore_state_equiv_cfg, sstore_state_equiv_cfg, tstore_state_equiv_cfg,
       write_memory_with_expansion_state_equiv_cfg, jump_to_state_equiv_cfg,
       halt_state_state_equiv_cfg, revert_state_state_equiv_cfg,
       state_equiv_cfg_refl] >>
  gvs[AllCaseEqs(), result_equiv_cfg_def]
QED

(* ===== State Operations Preserve state_equiv_cfg ===== *)

Theorem update_var_state_equiv_cfg:
  !x v s1 s2.
    state_equiv_cfg s1 s2 ==>
    state_equiv_cfg (update_var x v s1) (update_var x v s2)
Proof
  rw[state_equiv_cfg_def, var_equiv_def, update_var_def, lookup_var_def, FLOOKUP_UPDATE]
QED

Theorem mstore_state_equiv_cfg:
  !offset v s1 s2.
    state_equiv_cfg s1 s2 ==>
    state_equiv_cfg (mstore offset v s1) (mstore offset v s2)
Proof
  rw[state_equiv_cfg_def, var_equiv_def, mstore_def, lookup_var_def]
QED

Theorem sstore_state_equiv_cfg:
  !key v s1 s2.
    state_equiv_cfg s1 s2 ==>
    state_equiv_cfg (sstore key v s1) (sstore key v s2)
Proof
  rw[state_equiv_cfg_def, var_equiv_def, sstore_def, lookup_var_def]
QED

Theorem tstore_state_equiv_cfg:
  !key v s1 s2.
    state_equiv_cfg s1 s2 ==>
    state_equiv_cfg (tstore key v s1) (tstore key v s2)
Proof
  rw[state_equiv_cfg_def, var_equiv_def, tstore_def, lookup_var_def]
QED

Theorem write_memory_with_expansion_state_equiv_cfg:
  !offset bytes s1 s2.
    state_equiv_cfg s1 s2 ==>
    state_equiv_cfg (write_memory_with_expansion offset bytes s1)
                    (write_memory_with_expansion offset bytes s2)
Proof
  rw[state_equiv_cfg_def, var_equiv_def, write_memory_with_expansion_def, lookup_var_def]
QED

Theorem jump_to_state_equiv_cfg:
  !lbl1 lbl2 s1 s2.
    state_equiv_cfg s1 s2 ==>
    state_equiv_cfg (jump_to lbl1 s1) (jump_to lbl2 s2)
Proof
  rw[state_equiv_cfg_def, var_equiv_def, jump_to_def, lookup_var_def]
QED

Theorem halt_state_state_equiv_cfg:
  !s1 s2.
    state_equiv_cfg s1 s2 ==>
    state_equiv_cfg (halt_state s1) (halt_state s2)
Proof
  rw[state_equiv_cfg_def, var_equiv_def, halt_state_def, lookup_var_def]
QED

Theorem revert_state_state_equiv_cfg:
  !s1 s2.
    state_equiv_cfg s1 s2 ==>
    state_equiv_cfg (revert_state s1) (revert_state s2)
Proof
  rw[state_equiv_cfg_def, var_equiv_def, revert_state_def, lookup_var_def]
QED

Theorem next_inst_state_equiv_cfg:
  !s1 s2.
    state_equiv_cfg s1 s2 ==>
    state_equiv_cfg (next_inst s1) (next_inst s2)
Proof
  rw[state_equiv_cfg_def, var_equiv_def, next_inst_def, lookup_var_def]
QED

(* ===== Block-Level Equivalence Helpers ===== *)

Theorem block_has_no_phi_inst:
  !bb inst.
    block_has_no_phi bb /\
    MEM inst bb.bb_instructions ==> inst.inst_opcode <> PHI
Proof
  rw[block_has_no_phi_def, block_has_phi_def] >> metis_tac[]
QED

Theorem run_block_no_phi_equiv_cfg:
  !fn bb s1 s2.
    block_has_no_phi bb /\
    state_equiv_cfg s1 s2 /\
    s1.vs_inst_idx = s2.vs_inst_idx
  ==>
    result_equiv_cfg (run_block fn bb s1) (run_block fn bb s2)
Proof
  ho_match_mp_tac run_block_ind >>
  rpt gen_tac >> strip_tac >>
  rpt strip_tac >>
  simp[Once run_block_def] >>
  Cases_on `step_in_block fn bb s1` >> Cases_on `q` >> simp[] >>
  strip_tac >>
  qpat_x_assum `step_in_block fn bb s1 = (OK v,r)` mp_tac >>
  simp[step_in_block_def] >>
  Cases_on `get_instruction bb s1.vs_inst_idx` >> simp[] >>
  rename1 `get_instruction bb _ = SOME inst` >>
  qpat_x_assum `get_instruction bb _ = SOME inst` mp_tac >>
  simp[get_instruction_def] >> strip_tac >>
  `MEM inst bb.bb_instructions` by metis_tac[MEM_EL] >>
  `inst.inst_opcode <> PHI` by
    (irule block_has_no_phi_inst >> simp[]) >>
  `result_equiv_cfg (step_inst inst s1) (step_inst inst s2)` by
    (irule step_inst_state_equiv_cfg >> simp[]) >>
  Cases_on `step_inst inst s1` >>
  Cases_on `step_inst inst s2` >>
  gvs[result_equiv_cfg_def] >>
  rename1 `step_inst inst s1 = OK v1` >>
  rename1 `step_inst inst s2 = OK v2` >>
  Cases_on `is_terminator inst.inst_opcode` >>
  gvs[result_equiv_cfg_def]
  >- (
    qexists_tac `OK v2` >>
    simp[result_equiv_cfg_def]
  )
  >- (
    `state_equiv_cfg (next_inst v1) (next_inst v2)` by
      (irule next_inst_state_equiv_cfg >> simp[result_equiv_cfg_def]) >>
    `v1.vs_inst_idx = s1.vs_inst_idx` by
      (drule_all step_inst_preserves_inst_idx >> simp[]) >>
    `v2.vs_inst_idx = s2.vs_inst_idx` by
      (drule_all step_inst_preserves_inst_idx >> simp[]) >>
    first_x_assum (qspecl_then [`next_inst v1`, `next_inst v2`] mp_tac) >>
    simp[next_inst_def]
  )
QED

Theorem run_block_state_equiv_cfg:
  !fn bb s1 s2.
    state_equiv_cfg s1 s2 /\
    s1.vs_prev_bb = s2.vs_prev_bb /\
    s1.vs_inst_idx = s2.vs_inst_idx
  ==>
    result_equiv_cfg (run_block fn bb s1) (run_block fn bb s2)
Proof
  ho_match_mp_tac run_block_ind >>
  rpt gen_tac >> strip_tac >>
  rpt strip_tac >>
  simp[Once run_block_def] >>
  Cases_on `step_in_block fn bb s1` >> Cases_on `q` >> simp[] >>
  strip_tac >>
  qpat_x_assum `step_in_block fn bb s1 = (OK v,r)` mp_tac >>
  simp[step_in_block_def] >>
  Cases_on `get_instruction bb s1.vs_inst_idx` >> simp[] >>
  rename1 `get_instruction bb _ = SOME inst` >>
  qpat_x_assum `get_instruction bb _ = SOME inst` mp_tac >>
  simp[get_instruction_def] >> strip_tac >>
  `result_equiv_cfg (step_inst inst s1) (step_inst inst s2)` by
    (irule step_inst_state_equiv_cfg >> simp[]) >>
  Cases_on `step_inst inst s1` >>
  Cases_on `step_inst inst s2` >>
  gvs[result_equiv_cfg_def] >>
  rename1 `step_inst inst s1 = OK v1` >>
  rename1 `step_inst inst s2 = OK v2` >>
  Cases_on `is_terminator inst.inst_opcode` >>
  gvs[result_equiv_cfg_def]
  >- (
    qexists_tac `OK v2` >>
    simp[result_equiv_cfg_def]
  )
  >- (
    `state_equiv_cfg (next_inst v1) (next_inst v2)` by
      (irule next_inst_state_equiv_cfg >> simp[result_equiv_cfg_def]) >>
    `v1.vs_inst_idx = s1.vs_inst_idx` by
      (drule_all step_inst_preserves_inst_idx >> simp[]) >>
    `v2.vs_inst_idx = s2.vs_inst_idx` by
      (drule_all step_inst_preserves_inst_idx >> simp[]) >>
    first_x_assum (qspecl_then [`next_inst v1`, `next_inst v2`] mp_tac) >>
    simp[next_inst_def]
  )
QED

Theorem run_block_drop_equiv_cfg:
  !fn bb pref suff s k.
    bb.bb_instructions = pref ++ suff /\
    s.vs_inst_idx = LENGTH pref + k /\
    k <= LENGTH suff
  ==>
    result_equiv_cfg
      (run_block fn bb s)
      (run_block fn (bb with bb_instructions := suff) (s with vs_inst_idx := k))
Proof
  completeInduct_on `LENGTH suff - k` >>
  rpt strip_tac >>
  Cases_on `k = LENGTH suff`
  >- (
    simp[Once run_block_def, step_in_block_def, get_instruction_def,
         result_equiv_cfg_def] >>
    simp[LENGTH_APPEND] >>
    fs[]
  )
  >- (
    `k < LENGTH suff` by simp[] >>
    simp[Once run_block_def, step_in_block_def] >>
    `get_instruction bb (LENGTH pref + k) = SOME (EL k suff)` by (
      simp[get_instruction_def, LENGTH_APPEND] >>
      `LENGTH pref + k < LENGTH pref + LENGTH suff` by simp[] >>
      simp[EL_APPEND2]
    ) >>
    `get_instruction (bb with bb_instructions := suff) k = SOME (EL k suff)` by
      (simp[get_instruction_def] >> simp[]) >>
    simp[] >>
    `state_equiv_cfg s (s with vs_inst_idx := k)` by
      simp[state_equiv_cfg_def, var_equiv_def, lookup_var_def] >>
    `result_equiv_cfg (step_inst (EL k suff) s)
                      (step_inst (EL k suff) (s with vs_inst_idx := k))` by
      (irule step_inst_state_equiv_cfg >> simp[]) >>
    Cases_on `step_inst (EL k suff) s` >>
    Cases_on `step_inst (EL k suff) (s with vs_inst_idx := k)` >>
    gvs[result_equiv_cfg_def]
    >- (
      rename1 `step_inst _ _ = OK v1` >>
      rename1 `step_inst _ _ = OK v2` >>
      Cases_on `is_terminator (EL k suff).inst_opcode`
      >- (
        qexists_tac `OK v2` >>
        simp[result_equiv_cfg_def]
      )
      >- (
        `state_equiv_cfg (next_inst v1) (next_inst v2)` by
          (irule next_inst_state_equiv_cfg >> simp[result_equiv_cfg_def]) >>
        `v1.vs_inst_idx = s.vs_inst_idx` by
          (drule_all step_inst_preserves_inst_idx >> simp[]) >>
        `v2.vs_inst_idx = (s with vs_inst_idx := k).vs_inst_idx` by
          (drule_all step_inst_preserves_inst_idx >> simp[]) >>
        `v1.vs_prev_bb = s.vs_prev_bb` by
          (drule_all step_inst_preserves_prev_bb >> simp[]) >>
        `v2.vs_prev_bb = (s with vs_inst_idx := k).vs_prev_bb` by
          (drule_all step_inst_preserves_prev_bb >> simp[]) >>
        `result_equiv_cfg
           (run_block fn bb (next_inst v1))
           (run_block fn (bb with bb_instructions := suff)
                      ((next_inst v1) with vs_inst_idx := k + 1))` by (
          first_x_assum (qspec_then `k + 1` mp_tac) >>
          simp[arithmeticTheory.ADD1, LENGTH_APPEND] >>
          disch_then irule >>
          simp[next_inst_def, arithmeticTheory.ADD1]
        ) >>
        `result_equiv_cfg
           (run_block fn (bb with bb_instructions := suff)
                      ((next_inst v1) with vs_inst_idx := k + 1))
           (run_block fn (bb with bb_instructions := suff) (next_inst v2))` by (
          irule run_block_state_equiv_cfg >>
          simp[next_inst_def, arithmeticTheory.ADD1]
        ) >>
        irule result_equiv_cfg_trans >>
        qexists_tac `run_block fn (bb with bb_instructions := suff)
                      ((next_inst v1) with vs_inst_idx := k + 1)` >>
        simp[]
      )
    )
    >- (qexists_tac `Halt v2` >> gvs[result_equiv_cfg_def])
    >- (qexists_tac `Revert v2` >> gvs[result_equiv_cfg_def])
    >- (qexists_tac `Error e2` >> gvs[result_equiv_cfg_def])
  )
QED

Theorem run_block_fn_irrelevant:
  !fn1 bb s fn2. run_block fn1 bb s = run_block fn2 bb s
Proof
  ho_match_mp_tac run_block_ind >> rpt strip_tac >>
  simp[Once run_block_def, step_in_block_def] >>
  CONV_TAC (RHS_CONV (ONCE_REWRITE_CONV [run_block_def])) >>
  simp[step_in_block_def] >>
  rpt (CASE_TAC >> simp[]) >>
  rpt strip_tac >> first_x_assum irule >> simp[step_in_block_def]
QED

Theorem run_block_ok_inst_idx:
  !fn bb s s'.
    run_block fn bb s = OK s' /\ ~s'.vs_halted ==> s'.vs_inst_idx = 0
Proof
  ho_match_mp_tac run_block_ind >> rpt strip_tac >>
  qpat_x_assum `run_block _ _ _ = OK _` mp_tac >>
  simp[Once run_block_def] >>
  Cases_on `step_in_block fn bb s` >> Cases_on `q` >> simp[] >>
  Cases_on `v.vs_halted` >> simp[] >>
  Cases_on `r` >> simp[]
  >- (
    qpat_x_assum `step_in_block fn bb s = (OK v,T)` mp_tac >>
    simp[step_in_block_def] >>
    Cases_on `get_instruction bb s.vs_inst_idx` >> simp[] >>
    gvs[AllCaseEqs()] >>
    strip_tac >>
    qpat_x_assum `is_terminator _` mp_tac >>
    simp[is_terminator_def] >>
    Cases_on `x.inst_opcode` >> simp[step_inst_def] >>
    strip_tac >> gvs[AllCaseEqs(), jump_to_def]
  )
  >- (
    first_x_assum (qspecl_then [`OK v`, `F`, `v`] mp_tac) >> simp[]
  )
QED

val _ = export_theory();
