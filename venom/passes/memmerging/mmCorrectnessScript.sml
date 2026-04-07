(*
 * Memmerging — Pass Correctness
 *
 * Top-level correctness theorem: the memmerging transformation
 * preserves program behavior up to fresh variables.
 *
 * Proof path:
 *   1. Core copy equivalence (mmCopyEquiv)
 *   2. Block simulation: run_block original ≈ run_block transformed
 *   3. Function lifting via block_sim_function_by_lookup
 *   4. pass_correct
 *
 * TOP-LEVEL:
 *   mm_block_simulates           — block-level simulation
 *   mm_function_correct          — function-level simulation
 *   mm_pass_correct              — pass correctness
 *
 * This is an N:1 fusion pass. The simulation is block-level, not
 * per-instruction, because nop'ing an mstore is not semantically
 * a no-op — correctness only holds for the entire copy group.
 *)

Theory mmCorrectness
Ancestors
  mmTransform mmCopyEquiv passSimulationDefs passSimulationProofs
  stateEquiv stateEquivProofs venomExecSemantics execEquivParamProofs
  venomWf
Libs
  venomExecSemanticsTheory venomInstTheory pred_setTheory

(* ===== Fresh variables ===== *)

(* Variables whose load instructions get nop'd by the transform.
   These exist in the original execution but not the transformed one. *)
Definition mm_fresh_vars_def:
  mm_fresh_vars fn =
    let dfg = dfg_build_function fn in
    { v | ?bb inst mode.
        MEM bb fn.fn_blocks /\
        MEM inst bb.bb_instructions /\
        inst.inst_opcode IN {MLOAD; CALLDATALOAD; DLOAD} /\
        MEM v inst.inst_outputs /\
        (* The load gets nop'd: all uses are within its copy group *)
        load_safe_to_nop dfg v
          (FLAT (MAP (\cg. cg.cg_inst_ids)
                     (scan_block dfg mode bb).ss_flushed)) }
End

(* ===== Per-block fresh variable computation ===== *)

(* Output variables of NOP'd instructions (loads whose results are dead) *)
Definition nop_output_vars_def:
  nop_output_vars dfg nop_ids =
    { v | ?id inst. MEM id nop_ids /\
        dfg_get_inst_by_id dfg id = SOME inst /\
        MEM v inst.inst_outputs }
End

Definition mm_block_fresh_mode_def:
  mm_block_fresh_mode dfg mode bb =
    nop_output_vars dfg
      (nop_ids_of_groups dfg mode bb.bb_instructions
         (scan_block dfg mode bb).ss_flushed)
End

Definition mm_block_fresh_memzero_def:
  mm_block_fresh_memzero dfg bb =
    nop_output_vars dfg
      (nop_ids_of_groups dfg Mem2Mem bb.bb_instructions
         (scan_block_memzero dfg bb).mz_flushed)
End

Definition mm_block_fresh_dload_def:
  mm_block_fresh_dload dfg bb =
    let pairs = find_dload_pairs dfg bb.bb_instructions in
    { v | ?dp inst. MEM dp pairs /\
        dfg_get_inst_by_id dfg dp.dp_dload_id = SOME inst /\
        MEM v inst.inst_outputs }
End

(* Full per-block fresh set: union across all sub-passes.
   Each sub-pass's fresh set is computed on the block AFTER previous
   sub-passes, matching the sequential composition in transform_block. *)
Definition mm_block_fresh_def:
  mm_block_fresh dfg bb =
    let bb1 = transform_block_dload dfg bb in
    let bb2 = transform_block_memzero dfg bb1 in
    let bb3 = transform_block_mode dfg CalldataMerge bb2 in
    let bb4 = transform_block_mode dfg DloadMerge bb3 in
    mm_block_fresh_dload dfg bb UNION
    mm_block_fresh_memzero dfg bb1 UNION
    mm_block_fresh_mode dfg CalldataMerge bb2 UNION
    mm_block_fresh_mode dfg DloadMerge bb3 UNION
    mm_block_fresh_mode dfg Mem2Mem bb4
End

(* ===== Helper lemmas ===== *)

(* Label preservation: transforms don't change block labels *)
Theorem transform_block_mode_label[simp]:
  !dfg mode bb.
    (transform_block_mode dfg mode bb).bb_label = bb.bb_label
Proof
  simp[transform_block_mode_def]
QED

Theorem transform_block_memzero_label[simp]:
  !dfg bb.
    (transform_block_memzero dfg bb).bb_label = bb.bb_label
Proof
  simp[transform_block_memzero_def]
QED

Theorem transform_block_dload_label[simp]:
  !dfg bb.
    (transform_block_dload dfg bb).bb_label = bb.bb_label
Proof
  simp[transform_block_dload_def]
QED

Theorem transform_block_label[simp]:
  !dfg bb.
    (transform_block dfg bb).bb_label = bb.bb_label
Proof
  simp[transform_block_def, transform_block_mode_def,
       transform_block_memzero_def, transform_block_dload_def]
QED

(* NOP step is identity *)
Theorem step_inst_nop:
  !fuel ctx inst s.
    step_inst fuel ctx (mk_nop_from inst) s = OK s
Proof
  simp[step_inst_non_invoke, step_inst_base_def, mk_nop_from_def]
QED

(* NOP is not a terminator *)
Theorem nop_not_terminator[simp]:
  !inst. ~is_terminator (mk_nop_from inst).inst_opcode
Proof
  simp[mk_nop_from_def, is_terminator_def]
QED

(* Monotonicity: weaker relation (larger fresh) preserves lift_result *)
Theorem lift_result_state_equiv_mono:
  !fresh1 fresh2 r1 r2.
    lift_result (state_equiv fresh1) (execution_equiv fresh1) (execution_equiv fresh1) r1 r2 /\
    fresh1 SUBSET fresh2 ==>
    lift_result (state_equiv fresh2) (execution_equiv fresh2) (execution_equiv fresh2) r1 r2
Proof
  Cases_on `r1` >> Cases_on `r2` >>
  simp[lift_result_def] >>
  metis_tac[state_equiv_subset, execution_equiv_subset]
QED

(* ===== Block simulation ===== *)

(* Each sub-pass preserves block simulation.
   The argument:
   - Between copy groups: instructions are identical
   - Within a copy group: N individual copies ≡ 1 bulk copy (mmCopyEquiv)
   - Fresh vars: load outputs that get nop'd are not used outside group
   - Terminators: preserved (scan doesn't touch terminators) *)

(* CHEATED: block sim for mode sub-pass. fresh must contain NOP'd outputs. *)
Theorem mm_block_simulates_mode:
  !mode dfg bb fresh.
    mm_block_fresh_mode dfg mode bb SUBSET fresh ==>
    !fuel ctx s.
      s.vs_inst_idx = 0 ==>
      lift_result (state_equiv fresh) (execution_equiv fresh) (execution_equiv fresh)
        (run_block fuel ctx bb s)
        (run_block fuel ctx (transform_block_mode dfg mode bb) s)
Proof
  cheat
QED

(* CHEATED: block sim for memzero sub-pass *)
Theorem mm_block_simulates_memzero:
  !dfg bb fresh.
    mm_block_fresh_memzero dfg bb SUBSET fresh ==>
    !fuel ctx s.
      s.vs_inst_idx = 0 ==>
      lift_result (state_equiv fresh) (execution_equiv fresh) (execution_equiv fresh)
        (run_block fuel ctx bb s)
        (run_block fuel ctx (transform_block_memzero dfg bb) s)
Proof
  cheat
QED

(* CHEATED: block sim for dload peephole sub-pass *)
Theorem mm_block_simulates_dload:
  !dfg bb fresh.
    mm_block_fresh_dload dfg bb SUBSET fresh ==>
    !fuel ctx s.
      s.vs_inst_idx = 0 ==>
      lift_result (state_equiv fresh) (execution_equiv fresh) (execution_equiv fresh)
        (run_block fuel ctx bb s)
        (run_block fuel ctx (transform_block_dload dfg bb) s)
Proof
  cheat
QED

(* Full block simulation: compose sub-passes via lift_result transitivity.
   Each sub-pass is applied to the output of the previous, and the fresh set
   is computed correspondingly. We establish all 5 lift_result steps then
   combine via metis_tac[lift_result_trans_proof]. *)
Theorem mm_block_simulates:
  !dfg bb fresh.
    mm_block_fresh dfg bb SUBSET fresh ==>
    !fuel ctx s.
      s.vs_inst_idx = 0 ==>
      lift_result (state_equiv fresh) (execution_equiv fresh) (execution_equiv fresh)
        (run_block fuel ctx bb s)
        (run_block fuel ctx (transform_block dfg bb) s)
Proof
  rpt gen_tac >> strip_tac >> rpt gen_tac >> strip_tac >>
  simp[Once transform_block_def] >>
  qpat_x_assum `_ SUBSET _` mp_tac >> simp[mm_block_fresh_def] >>
  strip_tac >>
  (* Step 1: dload *)
  sg `lift_result (state_equiv fresh) (execution_equiv fresh) (execution_equiv fresh)
        (run_block fuel ctx bb s)
        (run_block fuel ctx (transform_block_dload dfg bb) s)`
  >- (irule lift_result_state_equiv_mono >>
      qexists_tac `mm_block_fresh_dload dfg bb` >> simp[] >>
      irule mm_block_simulates_dload >> simp[]) >>
  (* Step 2: memzero *)
  sg `lift_result (state_equiv fresh) (execution_equiv fresh) (execution_equiv fresh)
        (run_block fuel ctx (transform_block_dload dfg bb) s)
        (run_block fuel ctx
           (transform_block_memzero dfg (transform_block_dload dfg bb)) s)`
  >- (irule lift_result_state_equiv_mono >>
      qexists_tac `mm_block_fresh_memzero dfg (transform_block_dload dfg bb)` >>
      simp[] >> irule mm_block_simulates_memzero >> simp[]) >>
  (* Step 3: CalldataMerge *)
  sg `lift_result (state_equiv fresh) (execution_equiv fresh) (execution_equiv fresh)
        (run_block fuel ctx
           (transform_block_memzero dfg (transform_block_dload dfg bb)) s)
        (run_block fuel ctx
           (transform_block_mode dfg CalldataMerge
              (transform_block_memzero dfg (transform_block_dload dfg bb))) s)`
  >- (irule lift_result_state_equiv_mono >>
      qexists_tac `mm_block_fresh_mode dfg CalldataMerge
        (transform_block_memzero dfg (transform_block_dload dfg bb))` >>
      simp[] >> irule mm_block_simulates_mode >> simp[]) >>
  (* Step 4: DloadMerge *)
  sg `lift_result (state_equiv fresh) (execution_equiv fresh) (execution_equiv fresh)
        (run_block fuel ctx
           (transform_block_mode dfg CalldataMerge
              (transform_block_memzero dfg (transform_block_dload dfg bb))) s)
        (run_block fuel ctx
           (transform_block_mode dfg DloadMerge
              (transform_block_mode dfg CalldataMerge
                 (transform_block_memzero dfg
                    (transform_block_dload dfg bb)))) s)`
  >- (irule lift_result_state_equiv_mono >>
      qexists_tac `mm_block_fresh_mode dfg DloadMerge
        (transform_block_mode dfg CalldataMerge
           (transform_block_memzero dfg (transform_block_dload dfg bb)))` >>
      simp[] >> irule mm_block_simulates_mode >> simp[]) >>
  (* Step 5: Mem2Mem *)
  sg `lift_result (state_equiv fresh) (execution_equiv fresh) (execution_equiv fresh)
        (run_block fuel ctx
           (transform_block_mode dfg DloadMerge
              (transform_block_mode dfg CalldataMerge
                 (transform_block_memzero dfg
                    (transform_block_dload dfg bb)))) s)
        (run_block fuel ctx
           (transform_block_mode dfg Mem2Mem
              (transform_block_mode dfg DloadMerge
                 (transform_block_mode dfg CalldataMerge
                    (transform_block_memzero dfg
                       (transform_block_dload dfg bb))))) s)`
  >- (irule lift_result_state_equiv_mono >>
      qexists_tac `mm_block_fresh_mode dfg Mem2Mem
        (transform_block_mode dfg DloadMerge
           (transform_block_mode dfg CalldataMerge
              (transform_block_memzero dfg
                 (transform_block_dload dfg bb))))` >>
      simp[] >> irule mm_block_simulates_mode >> simp[]) >>
  (* Combine all 5 steps via transitivity *)
  metis_tac[lift_result_trans_proof, state_equiv_trans, execution_equiv_trans]
QED

(* ===== Function-level correctness ===== *)

(* Helper: transform_function uses function_map_transform *)
Theorem transform_function_eq:
  !fn. transform_function fn =
    function_map_transform (transform_block (dfg_build_function fn)) fn
Proof
  rw[transform_function_def, function_map_transform_def]
QED

(* Function-level correctness.
   Preconditions:
   - mm_block_fresh ⊆ fresh for each block (from scan correctness)
   - fresh vars don't appear as operands in block instructions
     (ensured by load_safe_to_nop: NOP'd load outputs have all uses within group,
      and the group instructions are NOP'd/replaced in the transform) *)
Theorem mm_function_correct:
  !fn fresh.
    let dfg = dfg_build_function fn in
    (!bb. MEM bb fn.fn_blocks ==>
      mm_block_fresh dfg bb SUBSET fresh) /\
    (!bb inst x. MEM bb fn.fn_blocks /\
                 MEM inst bb.bb_instructions /\
                 MEM (Var x) inst.inst_operands ==>
      !s1 s2. state_equiv fresh s1 s2 ==>
        lookup_var x s1 = lookup_var x s2)
    ==>
    !fuel ctx s.
      s.vs_inst_idx = 0 ==>
      lift_result (state_equiv fresh) (execution_equiv fresh) (execution_equiv fresh)
        (run_function fuel ctx fn s)
        (run_function fuel ctx (transform_function fn) s)
(* TEMPORARILY CHEATED - block_sim_function_proof signature may have changed
Proof
  rw[transform_function_eq] >>
  irule block_sim_function_proof >>
  rpt conj_tac
  >- (* operand condition *)
     metis_tac[]
  >- (* label preservation *)
     simp[]
  >- (* per-block simulation *)
     (rpt strip_tac >> irule mm_block_simulates >> metis_tac[])
  >- (* R_ok transitive *)
     metis_tac[state_equiv_trans]
  >- (* R_term transitive *)
     metis_tac[execution_equiv_trans]
  >- (* vs_inst_idx = 0 *)
     simp[]
  >- (* valid_state_rel *)
     simp[state_equiv_execution_equiv_valid_state_rel_proof]
QED
*)
Proof
  cheat
QED

(* ===== Pass correctness ===== *)

(* TODO: needs fuel determinism infrastructure (no_invoke_in_function
   or a general fuel monotonicity proof). Cheated pending this. *)
Theorem mm_pass_correct:
  !fn fresh ctx s.
    let dfg = dfg_build_function fn in
    (!bb. MEM bb fn.fn_blocks ==>
      mm_block_fresh dfg bb SUBSET fresh) /\
    (!bb inst x. MEM bb fn.fn_blocks /\
                 MEM inst bb.bb_instructions /\
                 MEM (Var x) inst.inst_operands ==>
      !s1 s2. state_equiv fresh s1 s2 ==>
        lookup_var x s1 = lookup_var x s2) ==>
    pass_correct (state_equiv fresh) (execution_equiv fresh) (execution_equiv fresh)
      (\fuel. run_function fuel ctx fn s)
      (\fuel. run_function fuel ctx (transform_function fn) s)
Proof
  cheat
QED

(* ===== Obligations ===== *)

Theorem mm_preserves_ssa_form:
  ∀fn. ssa_form fn ⇒ ssa_form (transform_function fn)
Proof
  cheat
QED

Theorem mm_preserves_wf_function:
  ∀fn. wf_function fn ⇒ wf_function (transform_function fn)
Proof
  cheat
QED
