(*
 * DFT Block Simulation — Infrastructure
 *
 * Key lemma: independent_commute_eq — bilateral-independent non-terminator
 * instructions produce identical final states when executed in either order.
 *)

Theory dftBlockSim
Ancestors
  dftDefs dftCommutation passSharedProps passSharedTransfer
  passSharedField venomExecSemantics venomExecProps venomEffects venomInstProofs
  venomState finite_map venomInst stateEquiv stateEquivProps
  passSimulationDefs venomInstProps pred_set sorting passSharedFrame
  vfmState venomWf

(* ================================================================
   1. step_inst preserves vs_allocas for non-alloca ops
   ================================================================ *)

Theorem step_inst_preserves_allocas:
  !fuel ctx inst s s'.
    step_inst fuel ctx inst s = OK s' /\
    ~is_alloca_op inst.inst_opcode /\
    ~is_terminator inst.inst_opcode /\
    ~is_ext_call_op inst.inst_opcode ==>
    s'.vs_allocas = s.vs_allocas
Proof
  rpt strip_tac >>
  Cases_on `inst.inst_opcode = INVOKE`
  >- (
    (* INVOKE case: merge_callee_state keeps caller's allocas,
       bind_outputs only does update_var which preserves allocas *)
    gvs[step_inst_def, AllCaseEqs()] >>
    `!pairs ss. (FOLDL (\s' (out,val). update_var out val s') ss pairs
      ).vs_allocas = ss.vs_allocas` by
      (Induct >> rw[] >> Cases_on `h` >> simp[update_var_def]) >>
    gvs[bind_outputs_def, AllCaseEqs(), merge_callee_state_def])
  >>
  gvs[step_inst_non_invoke] >>
  qpat_x_assum `step_inst_base _ _ = _` mp_tac >>
  simp[step_inst_base_def, exec_pure1_def, exec_pure2_def,
       exec_pure3_def, exec_read0_def, exec_read1_def,
       exec_write2_def] >>
  Cases_on `inst.inst_opcode` >>
  gvs[is_terminator_def, is_alloca_op_def, is_ext_call_op_def] >>
  rpt strip_tac >>
  gvs[AllCaseEqs(), update_var_def, mstore_def, mstore8_def, sstore_def,
      tstore_def, write_memory_with_expansion_def, mcopy_def,
      halt_state_def, revert_state_def, set_returndata_def, jump_to_def]
QED

Theorem step_inst_preserves_alloca_next:
  !fuel ctx inst s s'.
    step_inst fuel ctx inst s = OK s' /\
    ~is_alloca_op inst.inst_opcode /\
    ~is_terminator inst.inst_opcode /\
    ~is_ext_call_op inst.inst_opcode /\
    inst.inst_opcode <> INVOKE ==>
    s'.vs_alloca_next = s.vs_alloca_next
Proof
  rpt strip_tac >>
  gvs[step_inst_non_invoke] >>
  qpat_x_assum `step_inst_base _ _ = _` mp_tac >>
  simp[step_inst_base_def, exec_pure1_def, exec_pure2_def,
       exec_pure3_def, exec_read0_def, exec_read1_def,
       exec_write2_def] >>
  Cases_on `inst.inst_opcode` >>
  gvs[is_terminator_def, is_alloca_op_def, is_ext_call_op_def] >>
  rpt strip_tac >>
  gvs[AllCaseEqs(), update_var_def, mstore_def, mstore8_def, sstore_def,
      tstore_def, write_memory_with_expansion_def, mcopy_def,
      halt_state_def, revert_state_def, set_returndata_def, jump_to_def]
QED

(* ================================================================
   2. commute_equiv + allocas + alloca_next + vars → full equality
   ================================================================ *)

Theorem commute_equiv_allocas_vars_eq:
  !defs s1 s2.
    commute_equiv defs s1 s2 /\
    s1.vs_allocas = s2.vs_allocas /\
    s1.vs_alloca_next = s2.vs_alloca_next /\
    (!w. w IN defs ==> lookup_var w s1 = lookup_var w s2) ==>
    s1 = s2
Proof
  rw[commute_equiv_def, venom_state_component_equality, fmap_eq_flookup] >>
  simp[GSYM lookup_var_def] >> rename1 `lookup_var w` >>
  Cases_on `w IN defs` >> metis_tac[]
QED

(* ================================================================
   3. Operand variables membership
   ================================================================ *)

Theorem mem_var_operand_vars:
  !x ops. MEM (Var x) ops ==> MEM x (operand_vars ops)
Proof
  Induct_on `ops` >> rw[operand_vars_def] >>
  gvs[operand_var_def] >>
  Cases_on `h` >> gvs[operand_var_def]
QED

(* ================================================================
   4. eval_operand preserved by step on non-output vars
   ================================================================ *)

Theorem eval_operand_step_pres:
  !fuel ctx inst s s' op.
    step_inst fuel ctx inst s = OK s' /\
    ~is_terminator inst.inst_opcode /\
    (!x. op = Var x ==> ~MEM x inst.inst_outputs) ==>
    eval_operand op s' = eval_operand op s
Proof
  rpt strip_tac >> Cases_on `op` >> gvs[eval_operand_def]
  >- metis_tac[step_preserves_non_output_vars]
  >> metis_tac[step_preserves_labels]
QED

(* ================================================================
   5. Effect field preservation from effects_independent
   ================================================================ *)

Theorem effects_independent_write_read_disjoint:
  !op1 op2.
    effects_independent op1 op2 ==>
    DISJOINT (write_effects op1) (read_effects op2) /\
    DISJOINT (write_effects op2) (read_effects op1) /\
    DISJOINT (write_effects op1) (write_effects op2)
Proof
  simp[effects_independent_def] >> rpt strip_tac >>
  metis_tac[DISJOINT_SYM, SUBSET_DEF, IN_UNION, DISJOINT_DEF, EXTENSION]
QED

(* ================================================================
   6. Context + effect field agreement wrapper
   ================================================================ *)

Theorem step_pres_all_applied:
  !fuel ctx inst s s'.
    step_inst fuel ctx inst s = OK s' /\
    ~is_terminator inst.inst_opcode /\ ~is_alloca_op inst.inst_opcode /\
    ~is_ext_call_op inst.inst_opcode /\ inst.inst_opcode <> INVOKE ==>
    s'.vs_call_ctx = s.vs_call_ctx /\
    s'.vs_tx_ctx = s.vs_tx_ctx /\
    s'.vs_block_ctx = s.vs_block_ctx /\
    s'.vs_data_section = s.vs_data_section /\
    s'.vs_code = s.vs_code /\
    s'.vs_prev_hashes = s.vs_prev_hashes /\
    s'.vs_labels = s.vs_labels /\
    s'.vs_params = s.vs_params /\
    s'.vs_prev_bb = s.vs_prev_bb /\
    (Eff_MEMORY NOTIN write_effects inst.inst_opcode ==>
      s'.vs_memory = s.vs_memory) /\
    (Eff_TRANSIENT NOTIN write_effects inst.inst_opcode ==>
      s'.vs_transient = s.vs_transient) /\
    (Eff_BALANCE NOTIN write_effects inst.inst_opcode /\
     Eff_STORAGE NOTIN write_effects inst.inst_opcode ==>
      s'.vs_accounts = s.vs_accounts) /\
    (Eff_IMMUTABLES NOTIN write_effects inst.inst_opcode ==>
      s'.vs_immutables = s.vs_immutables) /\
    (Eff_RETURNDATA NOTIN write_effects inst.inst_opcode ==>
      s'.vs_returndata = s.vs_returndata) /\
    (Eff_LOG NOTIN write_effects inst.inst_opcode ==>
      s'.vs_logs = s.vs_logs)
Proof
  rpt strip_tac >>
  drule_all step_inst_preserves_all >> strip_tac >> gvs[]
QED

(* ================================================================
   7. Eligible write constraints — certain effects are never written
      by non-terminator, non-alloca, non-ext_call, non-INVOKE ops.
   ================================================================ *)

Theorem eligible_write_constraints[local]:
  !op. ~is_terminator op /\ ~is_alloca_op op /\
       ~is_ext_call_op op /\ op <> INVOKE ==>
       Eff_BALANCE NOTIN write_effects op /\
       Eff_EXTCODE NOTIN write_effects op /\
       Eff_RETURNDATA NOTIN write_effects op
Proof
  Cases >> EVAL_TAC
QED

(* ================================================================
   7b. Account sub-field preservation for eligible instructions.
       SSTORE is the only eligible op that writes Eff_STORAGE,
       and it only modifies .storage — balance, nonce, code are
       always preserved by eligible ops.
   ================================================================ *)

Theorem step_inst_preserves_account_bnc[local]:
  !fuel ctx inst s s'.
    step_inst fuel ctx inst s = OK s' /\
    ~is_terminator inst.inst_opcode /\ ~is_alloca_op inst.inst_opcode /\
    ~is_ext_call_op inst.inst_opcode /\ inst.inst_opcode <> INVOKE ==>
    !addr. (s'.vs_accounts addr).balance = (s.vs_accounts addr).balance /\
           (s'.vs_accounts addr).nonce = (s.vs_accounts addr).nonce /\
           (s'.vs_accounts addr).code = (s.vs_accounts addr).code
Proof
  rpt gen_tac >> strip_tac >> gen_tac >>
  Cases_on `Eff_STORAGE IN write_effects inst.inst_opcode`
  >- (
    (* Only SSTORE writes STORAGE among eligible ops *)
    `inst.inst_opcode = SSTORE` by (
      Cases_on `inst.inst_opcode` >>
      gvs[is_terminator_def, is_alloca_op_def, is_ext_call_op_def,
          write_effects_def, all_effects_def, empty_effects_def]) >>
    gvs[step_inst_non_invoke, step_inst_base_def, exec_write2_def,
        AllCaseEqs()] >>
    simp[sstore_def, lookup_account_def, LET_THM,
         combinTheory.APPLY_UPDATE_THM] >>
    rw[])
  >- (
    (* No STORAGE write: full vs_accounts preserved *)
    `Eff_BALANCE NOTIN write_effects inst.inst_opcode` by
      metis_tac[eligible_write_constraints] >>
    imp_res_tac step_pres_all_applied >> gvs[])
QED

(* Effect-free account-reading ops: exactly BALANCE/SELFBALANCE/EXTCODESIZE/EXTCODEHASH *)
Triviality effect_free_account_read_opcodes[local]:
  !op. is_effect_free_op op /\
    (Eff_BALANCE IN read_effects op \/ Eff_EXTCODE IN read_effects op) ==>
    op = BALANCE \/ op = SELFBALANCE \/ op = EXTCODESIZE \/ op = EXTCODEHASH
Proof Cases >> EVAL_TAC
QED

(* Account-reading opcodes: output values depend only on
   account sub-fields (balance/nonce/code) and call_ctx,
   NOT on full vs_accounts record equality. *)
Triviality account_read_output_agree[local]:
  !inst s1 s2 r1 r2 w.
    step_inst_base inst s1 = OK r1 /\
    step_inst_base inst s2 = OK r2 /\
    (inst.inst_opcode = BALANCE \/ inst.inst_opcode = SELFBALANCE \/
     inst.inst_opcode = EXTCODESIZE \/ inst.inst_opcode = EXTCODEHASH) /\
    (!op. MEM op inst.inst_operands ==>
          eval_operand op s1 = eval_operand op s2) /\
    (!addr. (s1.vs_accounts addr).balance =
            (s2.vs_accounts addr).balance /\
            (s1.vs_accounts addr).nonce =
            (s2.vs_accounts addr).nonce /\
            (s1.vs_accounts addr).code =
            (s2.vs_accounts addr).code) /\
    s1.vs_call_ctx = s2.vs_call_ctx /\
    MEM w inst.inst_outputs ==>
    lookup_var w r1 = lookup_var w r2
Proof
  rpt strip_tac >> gvs[] >>
  gvs[step_inst_base_def, exec_read0_def, exec_read1_def,
      AllCaseEqs(), update_var_def, lookup_var_def,
      FLOOKUP_UPDATE, lookup_account_def] >>
  (* EXTCODEHASH: account_empty tautology on s2's own fields *)
  gvs[account_empty_def] >> metis_tac[]
QED

(* Non-effect-free eligible ops preserve all vars.
   These ops (MSTORE, SSTORE, MCOPY, LOG, ASSERT, etc.) modify
   side-effect fields only — vs_vars is untouched. *)
Theorem step_non_effect_free_preserves_all_vars[local]:
  !fuel ctx inst s s'.
    step_inst fuel ctx inst s = OK s' /\
    ~is_effect_free_op inst.inst_opcode /\
    ~is_terminator inst.inst_opcode /\
    ~is_alloca_op inst.inst_opcode /\
    ~is_ext_call_op inst.inst_opcode /\
    inst.inst_opcode <> INVOKE ==>
    !v. lookup_var v s' = lookup_var v s
Proof
  rpt strip_tac >>
  gvs[step_inst_non_invoke] >>
  qpat_x_assum `step_inst_base _ _ = _` mp_tac >>
  simp[step_inst_base_def] >>
  Cases_on `inst.inst_opcode` >>
  gvs[is_effect_free_op_def, is_terminator_def,
      is_alloca_op_def, is_ext_call_op_def] >>
  simp[exec_write2_def] >>
  rpt strip_tac >> gvs[AllCaseEqs()] >>
  gvs[lookup_var_def, mcopy_def, mstore_def, mstore8_def,
      sstore_def, tstore_def, write_memory_with_expansion_def,
      halt_state_def, revert_state_def, set_returndata_def] >>
  rpt (CHANGED_TAC (rpt (pairarg_tac >> gvs[])))
QED

(* ================================================================
   8. Output var agreement across independent instructions
      If inst_a writes w, and inst_b is independent from inst_a,
      then lookup_var w agrees in both execution orders.
   ================================================================ *)

Theorem output_var_agree_across_independent:
  !fuel ctx inst_a inst_b ss va vb sab sba w.
    step_inst fuel ctx inst_a ss = OK va /\
    step_inst fuel ctx inst_b ss = OK vb /\
    step_inst fuel ctx inst_b va = OK sab /\
    step_inst fuel ctx inst_a vb = OK sba /\
    DISJOINT (set inst_a.inst_outputs) (set inst_b.inst_outputs) /\
    DISJOINT (set inst_b.inst_outputs)
             (set (operand_vars inst_a.inst_operands)) /\
    effects_independent inst_a.inst_opcode inst_b.inst_opcode /\
    ~is_terminator inst_a.inst_opcode /\ ~is_terminator inst_b.inst_opcode /\
    ~is_alloca_op inst_a.inst_opcode /\ ~is_alloca_op inst_b.inst_opcode /\
    ~is_ext_call_op inst_a.inst_opcode /\ ~is_ext_call_op inst_b.inst_opcode /\
    inst_a.inst_opcode <> INVOKE /\ inst_b.inst_opcode <> INVOKE /\
    MEM w inst_a.inst_outputs ==>
    lookup_var w sab = lookup_var w sba
Proof
  rpt strip_tac >>
  (* Step 1: lookup_var w sab = lookup_var w va
     (inst_b doesn't write w, so it preserves w) *)
  `~MEM w inst_b.inst_outputs` by (
    gvs[DISJOINT_DEF, EXTENSION] >> metis_tac[]) >>
  `lookup_var w sab = lookup_var w va` by
    metis_tac[step_preserves_non_output_vars] >>
  (* Step 2: lookup_var w va = lookup_var w sba
     Both are inst_a applied to states that agree on inst_a's inputs *)
  `step_inst_base inst_a ss = OK va` by gvs[step_inst_non_invoke] >>
  `step_inst_base inst_a vb = OK sba` by gvs[step_inst_non_invoke] >>
  `lookup_var w va = lookup_var w sba` suffices_by simp[] >>
  (* Establish all prerequisites for output_determined_vars *)
  `!op. MEM op inst_a.inst_operands ==>
        eval_operand op ss = eval_operand op vb` by (
    rpt strip_tac >>
    Cases_on `op` >> gvs[eval_operand_def]
    >- (rename1 `lookup_var vn` >>
      `~MEM vn inst_b.inst_outputs` by (
        `MEM vn (operand_vars inst_a.inst_operands)` by
          metis_tac[mem_var_operand_vars] >>
        gvs[DISJOINT_DEF, EXTENSION] >> metis_tac[]) >>
      metis_tac[step_preserves_non_output_vars])
    >> metis_tac[step_preserves_labels]) >>
  `!w'. MEM w' inst_a.inst_outputs ==>
        lookup_var w' ss = lookup_var w' vb` by (
    rpt strip_tac >>
    `~MEM w' inst_b.inst_outputs` by (
      gvs[DISJOINT_DEF, EXTENSION] >> metis_tac[]) >>
    metis_tac[step_preserves_non_output_vars]) >>
  (* Get field preservation for inst_b step specifically *)
  mp_tac (Q.SPECL [`fuel`, `ctx`, `inst_b`, `ss`, `vb`]
            step_pres_all_applied) >>
  simp[] >> strip_tac >>
  imp_res_tac effects_independent_write_read_disjoint >>
  `!e. e IN read_effects inst_a.inst_opcode ==>
       e NOTIN write_effects inst_b.inst_opcode` by
    (gvs[DISJOINT_DEF, EXTENSION] >> metis_tac[]) >>
  (* Account sub-field preservation: inst_b always preserves
     balance, nonce, code even when it writes STORAGE *)
  `!addr. (vb.vs_accounts addr).balance =
          (ss.vs_accounts addr).balance /\
          (vb.vs_accounts addr).nonce =
          (ss.vs_accounts addr).nonce /\
          (vb.vs_accounts addr).code =
          (ss.vs_accounts addr).code` by
    metis_tac[step_inst_preserves_account_bnc] >>
  (* Storage sub-field: if STORAGE read by inst_a, then
     STORAGE not written by inst_b, so full accounts preserved *)
  `Eff_STORAGE IN read_effects inst_a.inst_opcode ==>
   !addr. (ss.vs_accounts addr).storage =
          (vb.vs_accounts addr).storage` by (
    strip_tac >>
    `Eff_STORAGE NOTIN write_effects inst_b.inst_opcode` by res_tac >>
    `Eff_BALANCE NOTIN write_effects inst_b.inst_opcode` by
      metis_tac[eligible_write_constraints] >>
    `vb.vs_accounts = ss.vs_accounts` by gvs[] >> gvs[]) >>
  (* Memory: if read by inst_a, not written by inst_b *)
  `Eff_MEMORY IN read_effects inst_a.inst_opcode ==>
   ss.vs_memory = vb.vs_memory` by (strip_tac >> res_tac >> gvs[]) >>
  (* Case split: effect-free uses output_determined_vars,
     non-effect-free eligible ops don't modify vs_vars *)
  (* NOP: step returns state unchanged, so trivially equal *)
  Cases_on `inst_a.inst_opcode = NOP`
  >- (
    `step_inst fuel ctx inst_a ss = OK ss` by
      metis_tac[step_nop_identity] >>
    `step_inst fuel ctx inst_a vb = OK vb` by
      metis_tac[step_nop_identity] >>
    gvs[]) >>
  Cases_on `is_effect_free_op inst_a.inst_opcode`
  >- (
    (* Account-reading opcodes need special handling because SSTORE
       modifies .storage but preserves .balance/.nonce/.code.
       The generic theorem demands full vs_accounts equality which
       fails for BALANCE × SSTORE pairs. *)
    Cases_on `Eff_BALANCE IN read_effects inst_a.inst_opcode \/
              Eff_EXTCODE IN read_effects inst_a.inst_opcode`
    >- (
      (* inst_a ∈ {BALANCE, SELFBALANCE, EXTCODESIZE, EXTCODEHASH}.
         Prove output agreement directly from sub-field preservation. *)
      irule account_read_output_agree >> simp[] >>
      metis_tac[effect_free_account_read_opcodes])
    >- (
      (* No account-reading effects: generic theorem applies *)
      irule step_inst_base_effect_free_output_determined_vars >>
      qexistsl_tac [`inst_a`, `ss`, `vb`] >>
      rpt conj_tac >> gvs[] >>
      TRY (res_tac >> gvs[] >> NO_TAC) >>
      Cases_on `Eff_STORAGE IN read_effects inst_a.inst_opcode`
      >- (
        `Eff_STORAGE NOTIN write_effects inst_b.inst_opcode` by res_tac >>
        `Eff_BALANCE NOTIN write_effects inst_b.inst_opcode` by
          metis_tac[eligible_write_constraints] >>
        `vb.vs_accounts = ss.vs_accounts` by gvs[] >> gvs[])
      >- gvs[]))
  >> (
    (* Non-effect-free: all vars preserved *)
    `!v. lookup_var v va = lookup_var v ss` by
      metis_tac[step_non_effect_free_preserves_all_vars] >>
    `!v. lookup_var v sba = lookup_var v vb` by
      metis_tac[step_non_effect_free_preserves_all_vars] >>
    gvs[])
QED

(* ================================================================
   9. Independent instructions commute with state equality
   ================================================================ *)

Theorem independent_commute_eq:
  !fuel ctx inst1 inst2 ss v1 v2 s12 s21.
    step_inst fuel ctx inst1 ss = OK v1 /\
    step_inst fuel ctx inst2 ss = OK v2 /\
    step_inst fuel ctx inst2 v1 = OK s12 /\
    step_inst fuel ctx inst1 v2 = OK s21 /\
    DISJOINT (set (inst_defs inst1)) (set (inst_uses inst2)) /\
    DISJOINT (set (inst_defs inst2)) (set (inst_uses inst1)) /\
    DISJOINT (set (inst_defs inst1)) (set (inst_defs inst2)) /\
    effects_independent inst1.inst_opcode inst2.inst_opcode /\
    abort_compatible inst1.inst_opcode inst2.inst_opcode /\
    ~is_terminator inst1.inst_opcode /\ ~is_terminator inst2.inst_opcode /\
    ~is_alloca_op inst1.inst_opcode /\ ~is_alloca_op inst2.inst_opcode /\
    ~is_ext_call_op inst1.inst_opcode /\ ~is_ext_call_op inst2.inst_opcode /\
    inst1.inst_opcode <> INVOKE /\ inst2.inst_opcode <> INVOKE ==>
    s12 = s21
Proof
  rpt strip_tac >>
  (* A: commute_equiv *)
  `commute_equiv (set (inst_defs inst1) UNION set (inst_defs inst2)) s12 s21` by (
    mp_tac (Q.SPECL [`fuel`, `ctx`, `inst1`, `inst2`, `ss`]
                      effects_independent_commute) >> simp[LET_THM]) >>
  (* B: vs_allocas *)
  `s12.vs_allocas = s21.vs_allocas` by (
    `v1.vs_allocas = ss.vs_allocas` by metis_tac[step_inst_preserves_allocas] >>
    `s12.vs_allocas = ss.vs_allocas` by metis_tac[step_inst_preserves_allocas] >>
    `v2.vs_allocas = ss.vs_allocas` by metis_tac[step_inst_preserves_allocas] >>
    `s21.vs_allocas = ss.vs_allocas` by metis_tac[step_inst_preserves_allocas] >>
    simp[]) >>
  (* B2: vs_alloca_next *)
  `s12.vs_alloca_next = s21.vs_alloca_next` by (
    `v1.vs_alloca_next = ss.vs_alloca_next` by metis_tac[step_inst_preserves_alloca_next] >>
    `s12.vs_alloca_next = ss.vs_alloca_next` by metis_tac[step_inst_preserves_alloca_next] >>
    `v2.vs_alloca_next = ss.vs_alloca_next` by metis_tac[step_inst_preserves_alloca_next] >>
    `s21.vs_alloca_next = ss.vs_alloca_next` by metis_tac[step_inst_preserves_alloca_next] >>
    simp[]) >>
  (* C: vars in defs agree *)
  `!w. w IN (set (inst_defs inst1) UNION set (inst_defs inst2)) ==>
       lookup_var w s12 = lookup_var w s21` by (
    rw[IN_UNION] >> gvs[inst_defs_def]
    >- ((* w in inst1.inst_outputs — use output_var_agree with inst_a=inst1 *)
      irule output_var_agree_across_independent >>
      MAP_EVERY qexists_tac [`ctx`, `fuel`, `inst1`, `inst2`, `ss`, `v1`, `v2`] >>
      gvs[inst_defs_def, inst_uses_def])
    >- ((* w in inst2.inst_outputs — use output_var_agree with inst_a=inst2, inst_b=inst1
           Note: sab=s21, sba=s12 in the swapped version *)
      `lookup_var w s21 = lookup_var w s12` suffices_by simp[] >>
      irule output_var_agree_across_independent >>
      MAP_EVERY qexists_tac [`ctx`, `fuel`, `inst2`, `inst1`, `ss`, `v2`, `v1`] >>
      gvs[inst_defs_def, inst_uses_def] >>
      metis_tac[effects_independent_def, DISJOINT_SYM])) >>
  (* D: Assemble *)
  irule commute_equiv_allocas_vars_eq >>
  simp[] >>
  qexists_tac `set (inst_defs inst1) UNION set (inst_defs inst2)` >>
  simp[]
QED

(* ================================================================
   10. Extended commutation: allows INVOKE on one side.
       Key helpers for INVOKE × pure commutation.
   ================================================================ *)

(* FOLDL update_var preserves all non-vs_vars fields *)
Theorem foldl_update_var_field[local]:
  !pairs (ss:venom_state).
    (FOLDL (\s' (out,val). update_var out val s') ss pairs).vs_alloca_next =
    ss.vs_alloca_next /\
    (FOLDL (\s' (out,val). update_var out val s') ss pairs).vs_allocas =
    ss.vs_allocas
Proof
  Induct >> rw[] >> Cases_on `h` >> simp[update_var_def]
QED

(* Pure, effect-free, non-INVOKE step_inst_base either leaves state
   unchanged with no outputs, or adds exactly one update_var *)
Theorem pure_step_structure:
  !inst ss v2.
    step_inst_base inst ss = OK v2 /\
    inst_wf inst /\
    ~is_terminator inst.inst_opcode /\
    ~is_alloca_op inst.inst_opcode /\
    ~is_ext_call_op inst.inst_opcode /\
    inst.inst_opcode <> INVOKE /\
    write_effects inst.inst_opcode = {} /\
    read_effects inst.inst_opcode = {} ==>
    (inst.inst_outputs = [] /\ v2 = ss) \/
    (?out val. inst.inst_outputs = [out] /\ v2 = update_var out val ss)
Proof
  rpt strip_tac >>
  Cases_on `inst.inst_opcode` >>
  gvs[is_terminator_def, is_alloca_op_def, is_ext_call_op_def,
      write_effects_def, read_effects_def] >>
  gvs[step_inst_base_def, exec_pure1_def, exec_pure2_def, exec_pure3_def,
      exec_read0_def, exec_read1_def, inst_wf_def, AllCaseEqs()] >>
  metis_tac[]
QED

(* Output agreement for pure, empty-effect, non-INVOKE opcodes.
   Generalizes step_inst_base_effect_free_output_determined_vars to
   also cover ASSERT, ASSERT_UNREACHABLE, NOP (which are not effect_free). *)
Theorem pure_step_output_agree[local]:
  !inst s1 s2 r1 r2.
    step_inst_base inst s1 = OK r1 /\
    step_inst_base inst s2 = OK r2 /\
    ~is_terminator inst.inst_opcode /\
    ~is_alloca_op inst.inst_opcode /\
    ~is_ext_call_op inst.inst_opcode /\
    inst.inst_opcode <> INVOKE /\
    write_effects inst.inst_opcode = {} /\
    read_effects inst.inst_opcode = {} /\
    (!op. MEM op inst.inst_operands ==> eval_operand op s1 = eval_operand op s2) /\
    (!w. MEM w inst.inst_outputs ==> lookup_var w s1 = lookup_var w s2) /\
    s1.vs_prev_bb = s2.vs_prev_bb /\
    s1.vs_params = s2.vs_params /\
    s1.vs_call_ctx = s2.vs_call_ctx /\ s1.vs_tx_ctx = s2.vs_tx_ctx /\
    s1.vs_block_ctx = s2.vs_block_ctx /\
    s1.vs_data_section = s2.vs_data_section /\
    s1.vs_code = s2.vs_code /\
    s1.vs_prev_hashes = s2.vs_prev_hashes ==>
    !w. MEM w inst.inst_outputs ==> lookup_var w r1 = lookup_var w r2
Proof
  rpt strip_tac >>
  gvs[step_inst_base_def] >>
  Cases_on `inst.inst_opcode` >>
  gvs[is_terminator_def, is_alloca_op_def, is_ext_call_op_def,
      write_effects_def, read_effects_def] >>
  gvs[exec_pure1_def, exec_pure2_def, exec_pure3_def,
      exec_read0_def, exec_read1_def, AllCaseEqs()] >>
  gvs[update_var_def, lookup_var_def, FLOOKUP_UPDATE] >>
  (* PHI: resolve_phi gives MEM val_op operands, so eval_operand agrees *)
  imp_res_tac resolve_phi_MEM >> res_tac >> gvs[]
QED

(* effects_independent INVOKE op ==> op is pure with empty effects *)
Theorem invoke_independent_empty_effects[local]:
  !op. effects_independent INVOKE op ==>
    op <> INVOKE /\ write_effects op = {} /\ read_effects op = {}
Proof Cases >> EVAL_TAC
QED

(* FOLDL update_var only modifies vs_vars *)
Triviality foldl_update_var_only_vars:
  !pairs s. ?f.
    FOLDL (\s' (out,v). update_var out v s') s pairs = s with vs_vars := f
Proof
  Induct
  >- (rw[] >> qexists_tac `s.vs_vars` >> simp[venom_state_component_equality])
  >> gen_tac >> PairCases_on `h` >> simp[] >> gen_tac >>
     first_x_assum (qspec_then `update_var h0 h1 s` strip_assume_tac) >>
     qexists_tac `f` >> simp[] >> gvs[update_var_def]
QED

(* INVOKE preserves structural fields (prev_bb, params, contexts, etc.) *)
Theorem invoke_preserves_structural[local]:
  !fuel ctx inst s s'.
    step_inst fuel ctx inst s = OK s' /\
    inst.inst_opcode = INVOKE ==>
    s'.vs_prev_bb = s.vs_prev_bb /\
    s'.vs_params = s.vs_params /\
    s'.vs_call_ctx = s.vs_call_ctx /\
    s'.vs_tx_ctx = s.vs_tx_ctx /\
    s'.vs_block_ctx = s.vs_block_ctx /\
    s'.vs_data_section = s.vs_data_section /\
    s'.vs_code = s.vs_code /\
    s'.vs_prev_hashes = s.vs_prev_hashes /\
    s'.vs_labels = s.vs_labels
Proof
  rpt strip_tac >>
  gvs[Once step_inst_def, AllCaseEqs(), bind_outputs_def] >>
  qspecl_then [`ZIP (inst.inst_outputs, vals)`,
               `merge_callee_state s callee_s'`]
    strip_assume_tac foldl_update_var_only_vars >>
  gvs[merge_callee_state_def]
QED

(* Case 1 of invoke commutation: inst2 has no outputs *)
Triviality invoke_commute_case_nil:
  !fuel ctx inst1 inst2 ss v1 s12 s21.
    step_inst fuel ctx inst1 ss = OK v1 /\
    step_inst fuel ctx inst2 ss = OK ss /\
    step_inst fuel ctx inst2 v1 = OK s12 /\
    step_inst fuel ctx inst1 ss = OK s21 /\
    inst_wf inst1 /\ inst_wf inst2 /\
    inst1.inst_opcode = INVOKE /\
    inst2.inst_outputs = [] /\
    DISJOINT (set (inst_defs inst1)) (set (inst_defs inst2)) /\
    DISJOINT (set (inst_defs inst2)) (set (inst_uses inst1)) /\
    DISJOINT (set (inst_defs inst1)) (set (inst_uses inst2)) /\
    effects_independent inst1.inst_opcode inst2.inst_opcode /\
    ~is_terminator inst1.inst_opcode /\ ~is_terminator inst2.inst_opcode /\
    ~is_alloca_op inst1.inst_opcode /\ ~is_alloca_op inst2.inst_opcode /\
    ~is_ext_call_op inst1.inst_opcode /\ ~is_ext_call_op inst2.inst_opcode /\
    commute_equiv (set (inst_defs inst1) UNION set (inst_defs inst2)) s12 s21 /\
    s12.vs_allocas = v1.vs_allocas /\
    s12.vs_alloca_next = v1.vs_alloca_next /\
    (!w. MEM w (inst_defs inst1) ==> lookup_var w s12 = lookup_var w v1) ==>
    s12 = s21
Proof
  rpt strip_tac >>
  `s21 = v1` by gvs[] >>
  gvs[] >>
  `s12.vs_allocas = s21.vs_allocas` by
    metis_tac[step_inst_preserves_allocas] >>
  `s12.vs_alloca_next = s21.vs_alloca_next` by
    metis_tac[step_inst_preserves_alloca_next] >>
  irule commute_equiv_allocas_vars_eq >>
  simp[] >>
  qexists_tac `set (inst_defs inst1) UNION set (inst_defs inst2)` >>
  simp[] >> rpt strip_tac >>
  gvs[IN_UNION, inst_defs_def]
QED

(* Case 2 of invoke commutation: inst2 has one output *)
Triviality invoke_commute_case_cons:
  !fuel ctx inst1 inst2 ss v1 out val s12 s21.
    step_inst fuel ctx inst1 ss = OK v1 /\
    step_inst fuel ctx inst2 ss = OK (update_var out val ss) /\
    step_inst fuel ctx inst2 v1 = OK s12 /\
    step_inst fuel ctx inst1 (update_var out val ss) = OK s21 /\
    inst_wf inst1 /\ inst_wf inst2 /\
    inst1.inst_opcode = INVOKE /\
    inst2.inst_outputs = [out] /\
    DISJOINT (set (inst_defs inst1)) (set (inst_defs inst2)) /\
    DISJOINT (set (inst_defs inst2)) (set (inst_uses inst1)) /\
    DISJOINT (set (inst_defs inst1)) (set (inst_uses inst2)) /\
    effects_independent inst1.inst_opcode inst2.inst_opcode /\
    ~is_terminator inst1.inst_opcode /\ ~is_terminator inst2.inst_opcode /\
    ~is_alloca_op inst1.inst_opcode /\ ~is_alloca_op inst2.inst_opcode /\
    ~is_ext_call_op inst1.inst_opcode /\ ~is_ext_call_op inst2.inst_opcode /\
    commute_equiv (set (inst_defs inst1) UNION set (inst_defs inst2)) s12 s21 /\
    s12.vs_allocas = v1.vs_allocas /\
    s12.vs_alloca_next = v1.vs_alloca_next /\
    (!w. MEM w (inst_defs inst1) ==> lookup_var w s12 = lookup_var w v1) /\
    lookup_var out s12 = lookup_var out (update_var out val ss) ==>
    s12 = s21
Proof
  rpt strip_tac >>
  (* step_inst_ok_frame: inst1 over update_var = update_var over inst1 *)
  qspecl_then [`fuel`, `ctx`, `inst1`, `ss`, `v1`, `out`, `val`]
    mp_tac step_inst_ok_frame >>
  (impl_tac >- (
    simp[] >>
    gvs[DISJOINT_DEF, EXTENSION, inst_defs_def, inst_uses_def] >>
    metis_tac[mem_var_operand_vars])) >>
  strip_tac >>
  (* s21 = update_var out val v1 *)
  gvs[] >>
  irule commute_equiv_allocas_vars_eq >>
  simp[update_var_def] >>
  qexists_tac `set (inst_defs inst1) UNION set (inst_defs inst2)` >>
  simp[] >> rpt strip_tac >> gvs[IN_UNION, inst_defs_def]
  >- (
    (* w in inst1.inst_outputs: lookup_var w s12 = lookup_var w (update_var out val v1) *)
    `lookup_var w s12 = lookup_var w v1` by metis_tac[] >>
    gvs[update_var_def, lookup_var_def, FLOOKUP_UPDATE] >>
    gvs[DISJOINT_DEF, EXTENSION, inst_defs_def] >> metis_tac[])
  >> (
    (* w = out: lookup_var out s12 = lookup_var out (update_var out val v1) *)
    gvs[update_var_def, lookup_var_def, FLOOKUP_UPDATE])
QED

(* Standalone invoke commutation: INVOKE × pure-empty-effect.
   Delegates to case_nil and case_cons trivialities. *)
Theorem invoke_commute_eq[local]:
  !fuel ctx inst1 inst2 ss v1 v2 s12 s21.
    step_inst fuel ctx inst1 ss = OK v1 /\
    step_inst fuel ctx inst2 ss = OK v2 /\
    step_inst fuel ctx inst2 v1 = OK s12 /\
    step_inst fuel ctx inst1 v2 = OK s21 /\
    inst_wf inst1 /\ inst_wf inst2 /\
    inst1.inst_opcode = INVOKE /\
    DISJOINT (set (inst_defs inst1)) (set (inst_uses inst2)) /\
    DISJOINT (set (inst_defs inst2)) (set (inst_uses inst1)) /\
    DISJOINT (set (inst_defs inst1)) (set (inst_defs inst2)) /\
    effects_independent inst1.inst_opcode inst2.inst_opcode /\
    abort_compatible inst1.inst_opcode inst2.inst_opcode /\
    ~is_terminator inst1.inst_opcode /\ ~is_terminator inst2.inst_opcode /\
    ~is_alloca_op inst1.inst_opcode /\ ~is_alloca_op inst2.inst_opcode /\
    ~is_ext_call_op inst1.inst_opcode /\ ~is_ext_call_op inst2.inst_opcode ==>
    s12 = s21
Proof
  rpt strip_tac >>
  (* 1: inst2 pure with empty effects *)
  `inst2.inst_opcode <> INVOKE /\
   write_effects inst2.inst_opcode = {} /\
   read_effects inst2.inst_opcode = {}` by
    (irule invoke_independent_empty_effects >> gvs[]) >>
  (* 2: structural fields preserved by INVOKE *)
  `v1.vs_prev_bb = ss.vs_prev_bb /\ v1.vs_params = ss.vs_params /\
   v1.vs_call_ctx = ss.vs_call_ctx /\ v1.vs_tx_ctx = ss.vs_tx_ctx /\
   v1.vs_block_ctx = ss.vs_block_ctx /\ v1.vs_data_section = ss.vs_data_section /\
   v1.vs_code = ss.vs_code /\ v1.vs_prev_hashes = ss.vs_prev_hashes /\
   v1.vs_labels = ss.vs_labels` by
    (irule invoke_preserves_structural >> simp[] >> metis_tac[]) >>
  (* 3: commute_equiv *)
  `commute_equiv (set (inst_defs inst1) UNION set (inst_defs inst2))
     s12 s21` by (
    mp_tac (Q.SPECL [`fuel`, `ctx`, `inst1`, `inst2`, `ss`]
                      effects_independent_commute) >> simp[LET_THM]) >>
  (* 4-5: step_inst_base reductions *)
  `step_inst_base inst2 ss = OK v2` by gvs[step_inst_non_invoke] >>
  `step_inst_base inst2 v1 = OK s12` by gvs[step_inst_non_invoke] >>
  (* 6-7: allocas preserved *)
  `s12.vs_allocas = v1.vs_allocas` by
    metis_tac[step_inst_preserves_allocas] >>
  `s12.vs_alloca_next = v1.vs_alloca_next` by
    metis_tac[step_inst_preserves_alloca_next] >>
  (* 8: operand agreement *)
  `!op. MEM op inst2.inst_operands ==>
        eval_operand op v1 = eval_operand op ss` by (
    rpt strip_tac >>
    qspecl_then [`fuel`, `ctx`, `inst1`, `ss`, `v1`, `op`]
      mp_tac eval_operand_step_pres >>
    (impl_tac >- (simp[] >>
      gvs[DISJOINT_DEF, EXTENSION, inst_uses_def, inst_defs_def] >>
      metis_tac[mem_var_operand_vars])) >> simp[]) >>
  (* 9: output var agreement (inst1 preserves inst2's outputs) *)
  `!w. MEM w inst2.inst_outputs ==>
        lookup_var w v1 = lookup_var w ss` by (
    rpt strip_tac >>
    qspecl_then [`fuel`, `ctx`, `inst1`, `ss`, `v1`]
      mp_tac step_preserves_non_output_vars >>
    simp[] >>
    gvs[DISJOINT_DEF, EXTENSION, inst_defs_def] >> metis_tac[]) >>
  (* 10: inst2 output vars agree between s12 and v2 *)
  `!w. MEM w inst2.inst_outputs ==> lookup_var w s12 = lookup_var w v2` by (
    rpt strip_tac >> irule pure_step_output_agree >>
    MAP_EVERY qexists_tac [`inst2`, `v1`, `ss`] >> simp[]) >>
  (* 11: inst1 defs preserved through inst2 *)
  `!w. MEM w (inst_defs inst1) ==> lookup_var w s12 = lookup_var w v1` by (
    rpt strip_tac >>
    qspecl_then [`fuel`, `ctx`, `inst2`, `v1`, `s12`]
      mp_tac step_preserves_non_output_vars >>
    simp[] >>
    gvs[DISJOINT_DEF, EXTENSION, inst_defs_def] >> metis_tac[]) >>
  (* 12: Dispatch via pure_step_structure *)
  qspecl_then [`inst2`, `ss`, `v2`] mp_tac pure_step_structure >>
  simp[] >> strip_tac >> gvs[]
  >- (irule invoke_commute_case_nil >>
      simp[] >> metis_tac[])
  >> (irule invoke_commute_case_cons >>
      simp[] >> metis_tac[])
QED

Theorem independent_commute_eq_ext:
  !fuel ctx inst1 inst2 ss v1 v2 s12 s21.
    step_inst fuel ctx inst1 ss = OK v1 /\
    step_inst fuel ctx inst2 ss = OK v2 /\
    step_inst fuel ctx inst2 v1 = OK s12 /\
    step_inst fuel ctx inst1 v2 = OK s21 /\
    inst_wf inst1 /\ inst_wf inst2 /\
    DISJOINT (set (inst_defs inst1)) (set (inst_uses inst2)) /\
    DISJOINT (set (inst_defs inst2)) (set (inst_uses inst1)) /\
    DISJOINT (set (inst_defs inst1)) (set (inst_defs inst2)) /\
    effects_independent inst1.inst_opcode inst2.inst_opcode /\
    abort_compatible inst1.inst_opcode inst2.inst_opcode /\
    ~is_terminator inst1.inst_opcode /\ ~is_terminator inst2.inst_opcode /\
    ~is_alloca_op inst1.inst_opcode /\ ~is_alloca_op inst2.inst_opcode /\
    ~is_ext_call_op inst1.inst_opcode /\ ~is_ext_call_op inst2.inst_opcode ==>
    s12 = s21
Proof
  rpt strip_tac >>
  Cases_on `inst1.inst_opcode = INVOKE`
  >- (
    qspecl_then [`fuel`, `ctx`, `inst1`, `inst2`, `ss`, `v1`, `v2`, `s12`, `s21`]
      mp_tac invoke_commute_eq >> simp[])
  >> Cases_on `inst2.inst_opcode = INVOKE`
  >- (
    `effects_independent inst2.inst_opcode inst1.inst_opcode` by (
      gvs[effects_independent_def]) >>
    `abort_compatible inst2.inst_opcode inst1.inst_opcode` by (
      gvs[abort_compatible_def]) >>
    `s21 = s12` suffices_by simp[] >>
    qspecl_then [`fuel`, `ctx`, `inst2`, `inst1`, `ss`, `v2`, `v1`, `s21`, `s12`]
      mp_tac invoke_commute_eq >>
    simp[DISJOINT_SYM])
  >> (
    qspecl_then [`fuel`, `ctx`, `inst1`, `inst2`, `ss`, `v1`, `v2`, `s12`, `s21`]
      mp_tac independent_commute_eq >> simp[])
QED

(* ================================================================
   11. Effect-free commutativity: effect-free instructions with
       disjoint data deps produce identical states in either order.
       Handles memory-only-read pairs ({MLOAD,ILOAD,SHA3,MEMTOP}^2) that are
       NOT effects_independent but still commute.
   ================================================================ *)

(* Key insight: is_effect_free_op instructions only modify output variables
   (step_effect_free_state_equiv). So two such instructions commute when
   data-independent, because:
   (1) Each reads the same operand values regardless of order
   (2) Each preserves all state fields
   (3) update_var calls commute when outputs are disjoint *)

(*
 * Helper: extract field equalities from state_equiv without
 * expanding the whole definition (avoids fs explosion).
 *)
Triviality state_equiv_fields:
  !vars s1 s2. state_equiv vars s1 s2 ==>
    s1.vs_memory = s2.vs_memory /\
    s1.vs_transient = s2.vs_transient /\
    (s1.vs_halted <=> s2.vs_halted) /\
    s1.vs_returndata = s2.vs_returndata /\
    s1.vs_accounts = s2.vs_accounts /\
    s1.vs_call_ctx = s2.vs_call_ctx /\
    s1.vs_tx_ctx = s2.vs_tx_ctx /\
    s1.vs_block_ctx = s2.vs_block_ctx /\
    s1.vs_logs = s2.vs_logs /\
    s1.vs_immutables = s2.vs_immutables /\
    s1.vs_data_section = s2.vs_data_section /\
    s1.vs_labels = s2.vs_labels /\
    s1.vs_code = s2.vs_code /\
    s1.vs_params = s2.vs_params /\
    s1.vs_prev_hashes = s2.vs_prev_hashes /\
    s1.vs_allocas = s2.vs_allocas /\
    s1.vs_alloca_next = s2.vs_alloca_next /\
    s1.vs_current_bb = s2.vs_current_bb /\
    s1.vs_inst_idx = s2.vs_inst_idx /\
    s1.vs_prev_bb = s2.vs_prev_bb /\
    (!v. v NOTIN vars ==> lookup_var v s1 = lookup_var v s2)
Proof
  rw[state_equiv_def, execution_equiv_def]
QED

(* effect-free ops are not INVOKE, so step_inst = step_inst_base *)
Triviality effect_free_step_eq_base[local]:
  !inst. is_effect_free_op inst.inst_opcode ==>
    !fuel ctx s. step_inst fuel ctx inst s = step_inst_base inst s
Proof
  rpt strip_tac >> simp[Once step_inst_def] >>
  `inst.inst_opcode <> INVOKE` by
    (Cases_on `inst.inst_opcode` >> gvs[is_effect_free_op_def]) >>
  simp[]
QED

(* Strengthen state_equiv by filling in the excluded variables *)
Theorem state_equiv_fill_vars:
  !vars s1 s2.
    state_equiv vars s1 s2 /\
    (!v. v IN vars ==> lookup_var v s1 = lookup_var v s2) ==>
    state_equiv {} s1 s2
Proof
  rw[state_equiv_def, execution_equiv_def] >> metis_tac[]
QED

(* Effect-free step output is determined by state_equiv-preserved state.
   For non-NOP effect-free inst, if s1 and s2 agree on everything except
   some vars disjoint from inst_uses, then output values agree. *)
Triviality effect_free_output_determined[local]:
  !fuel ctx inst s1 s2 r1 r2 excl.
    step_inst fuel ctx inst s1 = OK r1 /\
    step_inst fuel ctx inst s2 = OK r2 /\
    is_effect_free_op inst.inst_opcode /\
    inst.inst_opcode <> NOP /\
    state_equiv excl s1 s2 /\
    DISJOINT excl (set (inst_uses inst)) ==>
    !v. MEM v inst.inst_outputs ==> lookup_var v r1 = lookup_var v r2
Proof
  rpt strip_tac >>
  imp_res_tac effect_free_step_eq_base >> gvs[] >>
  qspecl_then [`inst`, `s1`, `s2`, `r1`, `r2`] mp_tac
    step_inst_base_effect_free_output_determined_vars >>
  impl_tac >- (
    imp_res_tac state_equiv_fields >>
    rpt conj_tac >> gvs[]
    >- (rpt strip_tac >> irule eval_operand_equiv >>
        qexists_tac `excl` >> simp[] >>
        rpt strip_tac >> gvs[DISJOINT_DEF, EXTENSION, inst_uses_def] >>
        metis_tac[mem_var_operand_vars])
    >> metis_tac[]) >>
  metis_tac[]
QED

Theorem effect_free_commute_eq:
  !fuel ctx inst1 inst2 ss v1 v2 s12 s21.
    step_inst fuel ctx inst1 ss = OK v1 /\
    step_inst fuel ctx inst2 ss = OK v2 /\
    step_inst fuel ctx inst2 v1 = OK s12 /\
    step_inst fuel ctx inst1 v2 = OK s21 /\
    is_effect_free_op inst1.inst_opcode /\
    is_effect_free_op inst2.inst_opcode /\
    DISJOINT (set (inst_defs inst1)) (set (inst_uses inst2)) /\
    DISJOINT (set (inst_defs inst2)) (set (inst_uses inst1)) /\
    DISJOINT (set (inst_defs inst1)) (set (inst_defs inst2)) /\
    ~is_terminator inst1.inst_opcode /\ ~is_terminator inst2.inst_opcode ==>
    s12 = s21
Proof
  rpt strip_tac >>
  (* Step 1: Get state_equiv from each effect-free step *)
  `state_equiv (set inst1.inst_outputs) ss v1` by
    metis_tac[step_effect_free_state_equiv] >>
  `state_equiv (set inst2.inst_outputs) ss v2` by
    metis_tac[step_effect_free_state_equiv] >>
  `state_equiv (set inst2.inst_outputs) v1 s12` by
    metis_tac[step_effect_free_state_equiv] >>
  `state_equiv (set inst1.inst_outputs) v2 s21` by
    metis_tac[step_effect_free_state_equiv] >>
  (* Handle NOP: identity step, so trivially commutes *)
  Cases_on `inst1.inst_opcode = NOP`
  >- (imp_res_tac step_nop_identity >> gvs[]) >>
  Cases_on `inst2.inst_opcode = NOP`
  >- (imp_res_tac step_nop_identity >> gvs[]) >>
  (* Step 2: Chain state_equivs to get state_equiv (outs1 ∪ outs2) s12 s21 *)
  qabbrev_tac `both = set inst1.inst_outputs UNION set inst2.inst_outputs` >>
  `state_equiv both ss s12` by
    (irule state_equiv_trans >> qexists_tac `v1` >>
     metis_tac[state_equiv_subset, SUBSET_UNION]) >>
  `state_equiv both ss s21` by
    (irule state_equiv_trans >> qexists_tac `v2` >>
     metis_tac[state_equiv_subset, SUBSET_UNION]) >>
  `state_equiv both s12 s21` by
    metis_tac[state_equiv_sym, state_equiv_trans] >>
  (* Step 3: Strengthen to state_equiv {} by filling in excluded vars *)
  irule state_equiv_empty_eq >>
  irule state_equiv_fill_vars >>
  qexists_tac `both` >> simp[] >>
  rpt strip_tac >> gvs[inst_defs_def, Abbr `both`]
  (* v in inst1.outs *)
  >- (`v NOTIN set inst2.inst_outputs` by
        (gvs[DISJOINT_DEF, EXTENSION] >> metis_tac[]) >>
      (* lookup_var v s12 = lookup_var v v1 *)
      `lookup_var v s12 = lookup_var v v1` by
        (qpat_x_assum `state_equiv (set inst2.inst_outputs) v1 s12` mp_tac >>
         simp[state_equiv_def, execution_equiv_def] >> metis_tac[]) >>
      (* lookup_var v v1 = lookup_var v s21 via output_determined *)
      `lookup_var v v1 = lookup_var v s21` by
        (qspecl_then [`fuel`, `ctx`, `inst1`, `ss`, `v2`, `v1`, `s21`,
                      `set inst2.inst_outputs`] mp_tac
           effect_free_output_determined >>
         simp[] >> metis_tac[DISJOINT_SYM]) >>
      simp[])
  (* v in inst2.outs: symmetric *)
  >> (`v NOTIN set inst1.inst_outputs` by
        (gvs[DISJOINT_DEF, EXTENSION] >> metis_tac[]) >>
      `lookup_var v s21 = lookup_var v v2` by
        (qpat_x_assum `state_equiv (set inst1.inst_outputs) v2 s21` mp_tac >>
         simp[state_equiv_def, execution_equiv_def] >> metis_tac[]) >>
      `lookup_var v v2 = lookup_var v s12` by
        (qspecl_then [`fuel`, `ctx`, `inst2`, `ss`, `v1`, `v2`, `s12`,
                      `set inst1.inst_outputs`] mp_tac
           effect_free_output_determined >>
         simp[] >> metis_tac[DISJOINT_SYM]) >>
      simp[])
QED


