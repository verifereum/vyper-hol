(*
 * SSA Construction Block-Level Correctness
 *
 * This theory proves block-level correctness of SSA construction.
 * Executing a block in non-SSA form gives equivalent results to
 * executing the transformed block in SSA form.
 *
 * ============================================================================
 * STRUCTURE OVERVIEW
 * ============================================================================
 *
 * KEY LEMMAS:
 *   - step_inst_ssa_equiv        : Single instruction preserves equiv
 *   - step_in_block_ssa_equiv    : Single step preserves equiv
 *   - run_block_ssa_equiv        : Block execution preserves equiv
 *
 * HELPER THEOREMS:
 *   - exec_binop_ssa_equiv       : Binary ops preserve equiv
 *   - exec_unop_ssa_equiv        : Unary ops preserve equiv
 *
 * ============================================================================
 *)

Theory ssaBlock
Ancestors
  ssaDefs ssaTransform ssaStateEquiv ssaWellFormed
  venomState venomInst venomSem list finite_map

(* ==========================================================================
   Binary/Unary/Mod Operations Preserve SSA Equivalence
   ========================================================================== *)

(* Helper: eval_operand with renamed operand gives same result *)
Theorem eval_renamed_operand:
  !vm s_orig s_ssa ns op.
    ssa_state_equiv vm s_orig s_ssa /\
    (!v. FLOOKUP vm v = SOME (ssa_var_name v (stack_top ns v)) \/
         (FLOOKUP vm v = NONE /\ stack_top ns v = 0)) ==>
    eval_operand op s_orig = eval_operand (rename_operand ns op) s_ssa
Proof
  rpt strip_tac >>
  Cases_on `op` >> fs[rename_operand_def, eval_operand_def] >>
  fs[ssa_state_equiv_def, var_map_equiv_def] >>
  first_x_assum (qspec_then `s` mp_tac) >>
  strip_tac >> fs[ssa_var_name_def]
QED

(* Helper: exec_binop never returns Halt *)
Theorem exec_binop_not_halt:
  !f inst s r. exec_binop f inst s <> Halt r
Proof
  rw[exec_binop_def] >> rpt (CASE_TAC >> gvs[])
QED

(* Helper: exec_unop never returns Halt *)
Theorem exec_unop_not_halt:
  !f inst s r. exec_unop f inst s <> Halt r
Proof
  rw[exec_unop_def] >> rpt (CASE_TAC >> gvs[])
QED

(* Helper: exec_modop never returns Halt *)
Theorem exec_modop_not_halt:
  !f inst s r. exec_modop f inst s <> Halt r
Proof
  rw[exec_modop_def] >> rpt (CASE_TAC >> gvs[])
QED

(* Helper: Binary operation preserves SSA equivalence.
   The SSA output variable must be fresh (not used elsewhere in the mapping).
   In SSA construction, this is guaranteed by using version numbers. *)
Theorem exec_binop_ssa_equiv:
  !f inst inst_ssa s_orig s_ssa vm r_orig.
    ssa_state_equiv vm s_orig s_ssa /\
    inst_ssa.inst_operands = MAP (ssa_operand vm) inst.inst_operands /\
    inst_ssa.inst_opcode = inst.inst_opcode /\
    (case inst.inst_outputs of
       [out] => ?ssa_out.
         inst_ssa.inst_outputs = [ssa_out] /\
         (* Freshness: ssa_out not used by any other mapping *)
         (!v. v <> out ==> FLOOKUP vm v <> SOME ssa_out) /\
         (!v. v <> out /\ FLOOKUP vm v = NONE ==> v <> ssa_out)
     | _ => inst_ssa.inst_outputs = inst.inst_outputs) /\
    exec_binop f inst s_orig = OK r_orig ==>
    ?r_ssa vm'.
      exec_binop f inst_ssa s_ssa = OK r_ssa /\
      ssa_state_equiv vm' r_orig r_ssa
Proof
  rw[exec_binop_def] >>
  Cases_on `inst.inst_operands` >> fs[] >>
  Cases_on `t` >> fs[] >>
  Cases_on `t'` >> fs[] >>
  gvs[AllCaseEqs()] >>
  (* Use eval_operand_ssa_equiv *)
  `eval_operand h s_orig = eval_operand (ssa_operand vm h) s_ssa` by
    (irule eval_operand_ssa_equiv >> simp[]) >>
  `eval_operand h' s_orig = eval_operand (ssa_operand vm h') s_ssa` by
    (irule eval_operand_ssa_equiv >> simp[]) >>
  gvs[] >>
  (* Provide witnesses *)
  qexists_tac `vm |+ (out, ssa_out)` >>
  irule update_var_ssa_equiv >> simp[]
QED

(* Helper: Unary operation preserves SSA equivalence *)
Theorem exec_unop_ssa_equiv:
  !f inst inst_ssa s_orig s_ssa vm r_orig.
    ssa_state_equiv vm s_orig s_ssa /\
    inst_ssa.inst_operands = MAP (ssa_operand vm) inst.inst_operands /\
    inst_ssa.inst_opcode = inst.inst_opcode /\
    (case inst.inst_outputs of
       [out] => ?ssa_out.
         inst_ssa.inst_outputs = [ssa_out] /\
         (!v. v <> out ==> FLOOKUP vm v <> SOME ssa_out) /\
         (!v. v <> out /\ FLOOKUP vm v = NONE ==> v <> ssa_out)
     | _ => inst_ssa.inst_outputs = inst.inst_outputs) /\
    exec_unop f inst s_orig = OK r_orig ==>
    ?r_ssa vm'.
      exec_unop f inst_ssa s_ssa = OK r_ssa /\
      ssa_state_equiv vm' r_orig r_ssa
Proof
  rw[exec_unop_def] >>
  Cases_on `inst.inst_operands` >> fs[] >>
  Cases_on `t` >> fs[] >>
  gvs[AllCaseEqs()] >>
  `eval_operand h s_orig = eval_operand (ssa_operand vm h) s_ssa` by
    (irule eval_operand_ssa_equiv >> simp[]) >>
  gvs[] >>
  qexists_tac `vm |+ (out, ssa_out)` >>
  irule update_var_ssa_equiv >> simp[]
QED

(* Helper: Modular operation preserves SSA equivalence *)
Theorem exec_modop_ssa_equiv:
  !f inst inst_ssa s_orig s_ssa vm r_orig.
    ssa_state_equiv vm s_orig s_ssa /\
    inst_ssa.inst_operands = MAP (ssa_operand vm) inst.inst_operands /\
    inst_ssa.inst_opcode = inst.inst_opcode /\
    (case inst.inst_outputs of
       [out] => ?ssa_out.
         inst_ssa.inst_outputs = [ssa_out] /\
         (!v. v <> out ==> FLOOKUP vm v <> SOME ssa_out) /\
         (!v. v <> out /\ FLOOKUP vm v = NONE ==> v <> ssa_out)
     | _ => inst_ssa.inst_outputs = inst.inst_outputs) /\
    exec_modop f inst s_orig = OK r_orig ==>
    ?r_ssa vm'.
      exec_modop f inst_ssa s_ssa = OK r_ssa /\
      ssa_state_equiv vm' r_orig r_ssa
Proof
  rw[exec_modop_def] >>
  Cases_on `inst.inst_operands` >> fs[] >>
  Cases_on `t` >> fs[] >>
  Cases_on `t'` >> fs[] >>
  Cases_on `t` >> fs[] >>
  gvs[AllCaseEqs()] >>
  `eval_operand h s_orig = eval_operand (ssa_operand vm h) s_ssa` by
    (irule eval_operand_ssa_equiv >> simp[]) >>
  `eval_operand h' s_orig = eval_operand (ssa_operand vm h') s_ssa` by
    (irule eval_operand_ssa_equiv >> simp[]) >>
  `eval_operand h'' s_orig = eval_operand (ssa_operand vm h'') s_ssa` by
    (irule eval_operand_ssa_equiv >> simp[]) >>
  gvs[] >>
  qexists_tac `vm |+ (out, ssa_out)` >>
  irule update_var_ssa_equiv >> simp[]
QED

(* ==========================================================================
   Instruction Step Equivalence
   ========================================================================== *)

(* KEY LEMMA: Transform of instruction is well-formed for equivalence.
   The freshness conditions ensure the SSA output variable doesn't collide
   with other mappings in vm. In practice, SSA construction uses versioned
   names like "x:1" that are guaranteed fresh. *)
Definition inst_ssa_compatible_def:
  inst_ssa_compatible vm inst inst_ssa <=>
    inst_ssa.inst_opcode = inst.inst_opcode /\
    inst_ssa.inst_operands = MAP (ssa_operand vm) inst.inst_operands /\
    (case inst.inst_outputs of
       [] => inst_ssa.inst_outputs = []
     | [out] =>
         let ssa_out = case FLOOKUP vm out of SOME x => x | NONE => out in
         inst_ssa.inst_outputs = [ssa_out] /\
         (* Freshness: ssa_out not used by any other mapping *)
         (!v. v <> out ==> FLOOKUP vm v <> SOME ssa_out) /\
         (* ssa_out doesn't collide with other unmapped variables *)
         (!v. v <> out /\ FLOOKUP vm v = NONE ==> v <> ssa_out)
     | _ => T)  (* Multi-output not fully handled *)
End

(* Helper: inst_ssa_compatible implies freshness for output *)
Theorem inst_ssa_compatible_output_fresh:
  !vm inst inst_ssa out.
    inst_ssa_compatible vm inst inst_ssa /\
    inst.inst_outputs = [out] ==>
    ?ssa_out.
      inst_ssa.inst_outputs = [ssa_out] /\
      (!v. v <> out ==> FLOOKUP vm v <> SOME ssa_out) /\
      (!v. v <> out /\ FLOOKUP vm v = NONE ==> v <> ssa_out)
Proof
  rw[inst_ssa_compatible_def] >>
  Cases_on `FLOOKUP vm out` >> gvs[] >>
  metis_tac[]
QED

(* Helper: ASSERT_UNREACHABLE halting conditions *)
Theorem step_inst_assert_unreachable_halt:
  !inst s r.
    inst.inst_opcode = ASSERT_UNREACHABLE /\
    step_inst inst s = Halt r ==>
    ?cond_op cond.
      inst.inst_operands = [cond_op] /\
      eval_operand cond_op s = SOME cond /\
      cond <> 0w /\
      r = halt_state s
Proof
  rpt strip_tac >>
  fs[step_inst_def] >>
  Cases_on `inst.inst_operands` >> gvs[AllCaseEqs()] >>
  Cases_on `t` >> gvs[AllCaseEqs()] >>
  Cases_on `eval_operand h s` >> gvs[AllCaseEqs()] >>
  qexistsl_tac [`h`, `a`] >> gvs[]
QED

(* KEY LEMMA: Non-PHI instruction step that returns Halt.
   When the original instruction halts, the SSA version also halts
   with an equivalent state. *)
Theorem step_inst_halt_ssa_equiv:
  !inst inst_ssa s_orig s_ssa vm r_orig.
    ssa_state_equiv vm s_orig s_ssa /\
    inst_ssa_compatible vm inst inst_ssa /\
    step_inst inst s_orig = Halt r_orig ==>
    ?r_ssa.
      step_inst inst_ssa s_ssa = Halt r_ssa /\
      ssa_state_equiv vm r_orig r_ssa
Proof
  rpt strip_tac >>
  fs[inst_ssa_compatible_def] >>
  Cases_on `inst.inst_opcode` >>
  gvs[step_inst_def, exec_binop_not_halt, exec_unop_not_halt,
      exec_modop_not_halt, AllCaseEqs()] >>
  TRY (irule halt_state_ssa_equiv >> simp[]) >>
  TRY (
    rename1 `eval_operand cond_op s_orig = SOME cond` >>
    qexists_tac `halt_state s_ssa` >>
    conj_tac >- (
      qexists_tac `cond` >>
      `eval_operand cond_op s_orig =
       eval_operand (ssa_operand vm cond_op) s_ssa` by
        (irule eval_operand_ssa_equiv >> simp[]) >>
      gvs[]
    ) >>
    irule halt_state_ssa_equiv >> simp[]
  ) >>
  rpt (CASE_TAC >> gvs[AllCaseEqs()])
QED

(* Helper: exec_binop never returns Revert *)
Theorem exec_binop_not_revert:
  !f inst s r. exec_binop f inst s <> Revert r
Proof
  rw[exec_binop_def] >> rpt (CASE_TAC >> gvs[])
QED

(* Helper: exec_unop never returns Revert *)
Theorem exec_unop_not_revert:
  !f inst s r. exec_unop f inst s <> Revert r
Proof
  rw[exec_unop_def] >> rpt (CASE_TAC >> gvs[])
QED

(* Helper: exec_modop never returns Revert *)
Theorem exec_modop_not_revert:
  !f inst s r. exec_modop f inst s <> Revert r
Proof
  rw[exec_modop_def] >> rpt (CASE_TAC >> gvs[])
QED

(* Helper: RETURNDATACOPY revert conditions *)
Theorem step_inst_returndatacopy_revert:
  !inst s r.
    inst.inst_opcode = RETURNDATACOPY /\
    step_inst inst s = Revert r ==>
    ?op_size op_offset op_destOffset size_val offset destOffset.
      inst.inst_operands = [op_size; op_offset; op_destOffset] /\
      eval_operand op_size s = SOME size_val /\
      eval_operand op_offset s = SOME offset /\
      eval_operand op_destOffset s = SOME destOffset /\
      w2n offset + w2n size_val > LENGTH s.vs_returndata /\
      r = revert_state s
Proof
  rpt strip_tac >>
  fs[step_inst_def] >>
  Cases_on `inst.inst_operands` >> gvs[AllCaseEqs()] >>
  Cases_on `t` >> gvs[AllCaseEqs()] >>
  Cases_on `t'` >> gvs[AllCaseEqs()] >>
  Cases_on `t''` >> gvs[AllCaseEqs()] >>
  qexistsl_tac [`h`, `h'`, `h''`, `size_val`, `offset`, `destOffset`] >>
  gvs[]
QED

(* KEY LEMMA: Non-PHI instruction step that returns Revert.
   Similar to step_inst_halt_ssa_equiv but for Revert results. *)
Theorem step_inst_revert_ssa_equiv:
  !inst inst_ssa s_orig s_ssa vm r_orig.
    ssa_state_equiv vm s_orig s_ssa /\
    inst_ssa_compatible vm inst inst_ssa /\
    step_inst inst s_orig = Revert r_orig ==>
    ?r_ssa.
      step_inst inst_ssa s_ssa = Revert r_ssa /\
      ssa_state_equiv vm r_orig r_ssa
Proof
  rpt strip_tac >>
  fs[inst_ssa_compatible_def] >>
  Cases_on `inst.inst_opcode` >>
  (* RETURNDATACOPY out-of-bounds case *)
  TRY (
    `inst.inst_opcode = RETURNDATACOPY` by simp[] >>
    drule_all step_inst_returndatacopy_revert >> strip_tac >>
    qexists_tac `revert_state s_ssa` >>
    conj_tac >- (
      simp[step_inst_def] >>
      rpt (CASE_TAC >> gvs[AllCaseEqs()]) >>
      qexists_tac `size_val` >>
      qexists_tac `offset` >>
      qexists_tac `destOffset` >>
      `eval_operand op_size s_orig =
       eval_operand (ssa_operand vm op_size) s_ssa` by
        (irule eval_operand_ssa_equiv >> simp[]) >>
      `eval_operand op_offset s_orig =
       eval_operand (ssa_operand vm op_offset) s_ssa` by
        (irule eval_operand_ssa_equiv >> simp[]) >>
      `eval_operand op_destOffset s_orig =
       eval_operand (ssa_operand vm op_destOffset) s_ssa` by
        (irule eval_operand_ssa_equiv >> simp[]) >>
      gvs[ssa_state_equiv_def]
    ) >>
    irule revert_state_ssa_equiv >> simp[]
  ) >>
  gvs[step_inst_def, exec_binop_not_revert, exec_unop_not_revert,
      exec_modop_not_revert, AllCaseEqs()] >>
  (* REVERT / ASSERT (cond=0) cases *)
  TRY (irule revert_state_ssa_equiv >> simp[]) >>
  TRY (
    rename1 `eval_operand cond_op s_orig = SOME cond` >>
    qexists_tac `revert_state s_ssa` >>
    conj_tac >- (
      qexists_tac `cond` >>
      `eval_operand cond_op s_orig =
       eval_operand (ssa_operand vm cond_op) s_ssa` by
        (irule eval_operand_ssa_equiv >> simp[]) >>
      gvs[]
    ) >>
    irule revert_state_ssa_equiv >> simp[]
  ) >>
  rpt (CASE_TAC >> gvs[AllCaseEqs()]) >>
  TRY (metis_tac[step_inst_returndatacopy_revert, eval_operand_ssa_equiv,
                 revert_state_ssa_equiv, ssa_state_equiv_def])
QED

(* ==========================================================================
   Instruction Result Equivalence with Same VM
   ========================================================================== *)

(* Helper: exec_binop gives ssa_result_equiv with SAME vm.
 * The output variable is determined by vm via inst_ssa_compatible pattern.
 * Requires LENGTH inst.inst_outputs <= 1 (Venom instructions have at most 1 output). *)
Theorem exec_binop_result_ssa_equiv:
  !f inst inst_ssa s_orig s_ssa vm.
    ssa_state_equiv vm s_orig s_ssa /\
    inst_ssa.inst_operands = MAP (ssa_operand vm) inst.inst_operands /\
    LENGTH inst.inst_outputs <= 1 /\
    (case inst.inst_outputs of
       [] => inst_ssa.inst_outputs = []
     | [out] =>
         let ssa_out = case FLOOKUP vm out of SOME x => x | NONE => out in
         inst_ssa.inst_outputs = [ssa_out] /\
         (!v. v <> out ==> FLOOKUP vm v <> SOME ssa_out) /\
         (FLOOKUP vm ssa_out = NONE ==>
          FLOOKUP vm out = NONE \/ FLOOKUP vm out = SOME out)
     | _ => T) ==>
    ssa_result_equiv vm (exec_binop f inst s_orig) (exec_binop f inst_ssa s_ssa)
Proof
  rw[exec_binop_def] >>
  (* Case split on operands *)
  Cases_on `inst.inst_operands` >> fs[ssa_result_equiv_def] >>
  Cases_on `t` >> fs[ssa_result_equiv_def] >>
  Cases_on `t'` >> fs[ssa_result_equiv_def] >>
  (* Now have exactly 2 operands *)
  `eval_operand h s_orig = eval_operand (ssa_operand vm h) s_ssa` by
    (irule eval_operand_ssa_equiv >> simp[]) >>
  `eval_operand h' s_orig = eval_operand (ssa_operand vm h') s_ssa` by
    (irule eval_operand_ssa_equiv >> simp[]) >>
  gvs[] >>
  (* Case split on operand evaluation *)
  Cases_on `eval_operand (ssa_operand vm h) s_ssa` >> gvs[ssa_result_equiv_def] >>
  Cases_on `eval_operand (ssa_operand vm h') s_ssa` >> gvs[ssa_result_equiv_def] >>
  (* Case split on outputs - LENGTH <= 1 means [] or [out] only *)
  Cases_on `inst.inst_outputs` >> gvs[ssa_result_equiv_def] >>
  Cases_on `t` >> gvs[ssa_result_equiv_def] >>
  (* Single output case - use ssa_state_equiv_update_same_vm *)
  irule ssa_state_equiv_update_same_vm >> gvs[]
QED

(* Helper: exec_unop gives ssa_result_equiv with SAME vm.
 * Requires LENGTH inst.inst_outputs <= 1 (Venom instructions have at most 1 output). *)
Theorem exec_unop_result_ssa_equiv:
  !f inst inst_ssa s_orig s_ssa vm.
    ssa_state_equiv vm s_orig s_ssa /\
    inst_ssa.inst_operands = MAP (ssa_operand vm) inst.inst_operands /\
    LENGTH inst.inst_outputs <= 1 /\
    (case inst.inst_outputs of
       [] => inst_ssa.inst_outputs = []
     | [out] =>
         let ssa_out = case FLOOKUP vm out of SOME x => x | NONE => out in
         inst_ssa.inst_outputs = [ssa_out] /\
         (!v. v <> out ==> FLOOKUP vm v <> SOME ssa_out) /\
         (FLOOKUP vm ssa_out = NONE ==>
          FLOOKUP vm out = NONE \/ FLOOKUP vm out = SOME out)
     | _ => T) ==>
    ssa_result_equiv vm (exec_unop f inst s_orig) (exec_unop f inst_ssa s_ssa)
Proof
  rw[exec_unop_def] >>
  Cases_on `inst.inst_operands` >> fs[ssa_result_equiv_def] >>
  Cases_on `t` >> fs[ssa_result_equiv_def] >>
  `eval_operand h s_orig = eval_operand (ssa_operand vm h) s_ssa` by
    (irule eval_operand_ssa_equiv >> simp[]) >>
  gvs[] >>
  Cases_on `eval_operand (ssa_operand vm h) s_ssa` >> gvs[ssa_result_equiv_def] >>
  (* Case split on outputs - LENGTH <= 1 means [] or [out] only *)
  Cases_on `inst.inst_outputs` >> gvs[ssa_result_equiv_def] >>
  Cases_on `t` >> gvs[ssa_result_equiv_def] >>
  irule ssa_state_equiv_update_same_vm >> gvs[]
QED

(* Helper: exec_modop gives ssa_result_equiv with SAME vm.
 * Requires LENGTH inst.inst_outputs <= 1 (Venom instructions have at most 1 output). *)
Theorem exec_modop_result_ssa_equiv:
  !f inst inst_ssa s_orig s_ssa vm.
    ssa_state_equiv vm s_orig s_ssa /\
    inst_ssa.inst_operands = MAP (ssa_operand vm) inst.inst_operands /\
    LENGTH inst.inst_outputs <= 1 /\
    (case inst.inst_outputs of
       [] => inst_ssa.inst_outputs = []
     | [out] =>
         let ssa_out = case FLOOKUP vm out of SOME x => x | NONE => out in
         inst_ssa.inst_outputs = [ssa_out] /\
         (!v. v <> out ==> FLOOKUP vm v <> SOME ssa_out) /\
         (FLOOKUP vm ssa_out = NONE ==>
          FLOOKUP vm out = NONE \/ FLOOKUP vm out = SOME out)
     | _ => T) ==>
    ssa_result_equiv vm (exec_modop f inst s_orig) (exec_modop f inst_ssa s_ssa)
Proof
  rw[exec_modop_def] >>
  Cases_on `inst.inst_operands` >> fs[ssa_result_equiv_def] >>
  Cases_on `t` >> fs[ssa_result_equiv_def] >>
  Cases_on `t'` >> fs[ssa_result_equiv_def] >>
  Cases_on `t` >> fs[ssa_result_equiv_def] >>
  `eval_operand h s_orig = eval_operand (ssa_operand vm h) s_ssa` by
    (irule eval_operand_ssa_equiv >> simp[]) >>
  `eval_operand h' s_orig = eval_operand (ssa_operand vm h') s_ssa` by
    (irule eval_operand_ssa_equiv >> simp[]) >>
  `eval_operand h'' s_orig = eval_operand (ssa_operand vm h'') s_ssa` by
    (irule eval_operand_ssa_equiv >> simp[]) >>
  gvs[] >>
  Cases_on `eval_operand (ssa_operand vm h) s_ssa` >> gvs[ssa_result_equiv_def] >>
  Cases_on `eval_operand (ssa_operand vm h') s_ssa` >> gvs[ssa_result_equiv_def] >>
  Cases_on `eval_operand (ssa_operand vm h'') s_ssa` >> gvs[ssa_result_equiv_def] >>
  (* Case split on outputs - LENGTH <= 1 means [] or [out] only *)
  Cases_on `inst.inst_outputs` >> gvs[ssa_result_equiv_def] >>
  Cases_on `t` >> gvs[ssa_result_equiv_def] >>
  irule ssa_state_equiv_update_same_vm >> gvs[]
QED

(* Helper: ssa_result_equiv for Error cases (trivially true) *)
Theorem ssa_result_equiv_error:
  !vm e1 e2. ssa_result_equiv vm (Error e1) (Error e2)
Proof
  rw[ssa_result_equiv_def]
QED

(* Helper: expand option-pair case to nested cases. *)
Theorem option_pair_case:
  !x y e f.
    (case (x,y) of (SOME a, SOME b) => f a b | _ => e) =
    (case x of NONE => e | SOME a => case y of NONE => e | SOME b => f a b)
Proof
  Cases_on `x` >> Cases_on `y` >> simp[]
QED

(* Helper: expand option-triple case to nested cases. *)
Theorem option_triple_case:
  !x y z e f.
    (case (x,y,z) of
       (NONE,v3) => e
     | (SOME a,NONE,v9) => e
     | (SOME a,SOME b,NONE) => e
     | (SOME a,SOME b,SOME c) => f a b c) =
    (case x of
       NONE => e
     | SOME a =>
         case y of
           NONE => e
         | SOME b =>
             case z of
               NONE => e
             | SOME c => f a b c)
Proof
  Cases_on `x` >> Cases_on `y` >> Cases_on `z` >> simp[]
QED

(* Helper: collapse []/singleton/longer list cases into singleton/default. *)
Theorem case_list_singleton:
  !xs e f.
    (case xs of [] => e | [x] => f x | x::y::zs => e) =
    (case xs of [x] => f x | _ => e)
Proof
  Cases_on `xs` >> simp[] >>
  Cases_on `t` >> simp[] >>
  Cases_on `t'` >> simp[]
QED

(* Helper: finishing tactic for output preconditions.
   When goal has form:
   case inst.inst_outputs of [] => ... | [out] => ... /\ cond | ... => T
   and assumption 3 has the compatible form, need to case split *)
Theorem inst_ssa_compatible_outputs_equiv:
  !vm inst inst_ssa out.
    inst_ssa_compatible vm inst inst_ssa /\ inst.inst_outputs = [out] ==>
    inst_ssa.inst_outputs = [case FLOOKUP vm out of NONE => out | SOME x => x] /\
    (!v. v <> out ==> FLOOKUP vm v <> SOME (case FLOOKUP vm out of NONE => out | SOME x => x)) /\
    (FLOOKUP vm (case FLOOKUP vm out of NONE => out | SOME x => x) = NONE ==>
     FLOOKUP vm out = NONE \/ FLOOKUP vm out = SOME out)
Proof
  rw[inst_ssa_compatible_def] >>
  Cases_on `FLOOKUP vm out` >> gvs[]
QED

(* Helper: Single-output update with a known value preserves ssa_result_equiv. *)
Theorem single_output_result_ssa_equiv:
  !inst inst_ssa s_orig s_ssa vm val_orig val_ssa err.
    ssa_state_equiv vm s_orig s_ssa /\
    inst_ssa_compatible vm inst inst_ssa /\
    LENGTH inst.inst_outputs <= 1 /\
    val_orig = val_ssa ==>
    ssa_result_equiv vm
      (case inst.inst_outputs of
         [out] => OK (update_var out val_orig s_orig)
       | _ => Error err)
      (case inst_ssa.inst_outputs of
         [out] => OK (update_var out val_ssa s_ssa)
       | _ => Error err)
Proof
  rpt strip_tac >>
  Cases_on `inst.inst_outputs` >| [
    (Cases_on `inst_ssa.inst_outputs` >>
     fs[inst_ssa_compatible_def] >>
     gvs[ssa_result_equiv_def]),
    (Cases_on `t` >| [
       (drule_all inst_ssa_compatible_outputs_equiv >> strip_tac >>
        gvs[ssa_result_equiv_def] >>
        irule ssa_state_equiv_update_same_vm >> gvs[]),
       gvs[ssa_result_equiv_def]
     ])
  ]
QED

(* Helper: MLOAD gives ssa_result_equiv with SAME vm.
 * Follows the same pattern as exec_binop_result_ssa_equiv. *)
Theorem mload_result_ssa_equiv:
  !inst inst_ssa s_orig s_ssa vm.
    ssa_state_equiv vm s_orig s_ssa /\
    inst_ssa.inst_operands = MAP (ssa_operand vm) inst.inst_operands /\
    LENGTH inst.inst_outputs <= 1 /\
    (case inst.inst_outputs of
       [] => inst_ssa.inst_outputs = []
     | [out] =>
         let ssa_out = case FLOOKUP vm out of SOME x => x | NONE => out in
         inst_ssa.inst_outputs = [ssa_out] /\
         (!v. v <> out ==> FLOOKUP vm v <> SOME ssa_out) /\
         (FLOOKUP vm ssa_out = NONE ==>
          FLOOKUP vm out = NONE \/ FLOOKUP vm out = SOME out)
     | _ => T) ==>
    ssa_result_equiv vm
      (case inst.inst_operands of
         [] => Error "mload requires 1 operand"
       | [op1] =>
         (case eval_operand op1 s_orig of
            NONE => Error "undefined operand"
          | SOME addr =>
            case inst.inst_outputs of
              [] => Error "mload requires single output"
            | [out] => OK (update_var out (mload (w2n addr) s_orig) s_orig)
            | out::v6::v7 => Error "mload requires single output")
       | op1::v9::v10 => Error "mload requires 1 operand")
      (case inst_ssa.inst_operands of
         [] => Error "mload requires 1 operand"
       | [op1] =>
         (case eval_operand op1 s_ssa of
            NONE => Error "undefined operand"
          | SOME addr =>
            case inst_ssa.inst_outputs of
              [] => Error "mload requires single output"
            | [out] => OK (update_var out (mload (w2n addr) s_ssa) s_ssa)
            | out::v6::v7 => Error "mload requires single output")
       | op1::v9::v10 => Error "mload requires 1 operand")
Proof
  rw[] >>
  qpat_x_assum `inst_ssa.inst_operands = _` (fn th => ONCE_REWRITE_TAC [th]) >>

  (* Case split on operands - use fs to preserve subgoals *)
  Cases_on `inst.inst_operands` >> fs[ssa_result_equiv_def] >>
  Cases_on `t` >> fs[ssa_result_equiv_def] >>
  (* Establish operand equivalence *)
  `eval_operand h s_orig = eval_operand (ssa_operand vm h) s_ssa` by
    (irule eval_operand_ssa_equiv >> simp[]) >>
  Cases_on `eval_operand (ssa_operand vm h) s_ssa` >> fs[ssa_result_equiv_def] >> gvs[] >>
  (* Case split on outputs *)
  Cases_on `inst.inst_outputs` >> fs[ssa_result_equiv_def] >> gvs[] >>
  Cases_on `t` >> fs[ssa_result_equiv_def] >> gvs[] >>
  (* Establish mload equality from ssa_state_equiv *)
  `mload (w2n x) s_orig = mload (w2n x) s_ssa` by fs[ssa_state_equiv_def, mload_def] >>
  pop_assum (fn eq => simp_tac std_ss [eq]) >>
  (* Use ssa_state_equiv_update_same_vm *)
  irule ssa_state_equiv_update_same_vm >>
  Cases_on `FLOOKUP vm h'` >> gvs[]
QED

(* Helper: SLOAD gives ssa_result_equiv with SAME vm. *)
Theorem sload_result_ssa_equiv:
  !inst inst_ssa s_orig s_ssa vm.
    ssa_state_equiv vm s_orig s_ssa /\
    inst_ssa.inst_operands = MAP (ssa_operand vm) inst.inst_operands /\
    LENGTH inst.inst_outputs <= 1 /\
    (case inst.inst_outputs of
       [] => inst_ssa.inst_outputs = []
     | [out] =>
         let ssa_out = case FLOOKUP vm out of SOME x => x | NONE => out in
         inst_ssa.inst_outputs = [ssa_out] /\
         (!v. v <> out ==> FLOOKUP vm v <> SOME ssa_out) /\
         (FLOOKUP vm ssa_out = NONE ==>
          FLOOKUP vm out = NONE \/ FLOOKUP vm out = SOME out)
     | _ => T) ==>
    ssa_result_equiv vm
      (case inst.inst_operands of
         [] => Error "sload requires 1 operand"
       | [op1] =>
         (case eval_operand op1 s_orig of
            NONE => Error "undefined operand"
          | SOME key =>
            case inst.inst_outputs of
              [] => Error "sload requires single output"
            | [out] => OK (update_var out (sload key s_orig) s_orig)
            | out::v6::v7 => Error "sload requires single output")
       | op1::v9::v10 => Error "sload requires 1 operand")
      (case inst_ssa.inst_operands of
         [] => Error "sload requires 1 operand"
       | [op1] =>
         (case eval_operand op1 s_ssa of
            NONE => Error "undefined operand"
          | SOME key =>
            case inst_ssa.inst_outputs of
              [] => Error "sload requires single output"
            | [out] => OK (update_var out (sload key s_ssa) s_ssa)
            | out::v6::v7 => Error "sload requires single output")
       | op1::v9::v10 => Error "sload requires 1 operand")
Proof
  rw[] >>
  qpat_x_assum `inst_ssa.inst_operands = _` (fn th => ONCE_REWRITE_TAC [th]) >>

  Cases_on `inst.inst_operands` >> fs[ssa_result_equiv_def] >>
  Cases_on `t` >> fs[ssa_result_equiv_def] >>
  `eval_operand h s_orig = eval_operand (ssa_operand vm h) s_ssa` by
    (irule eval_operand_ssa_equiv >> simp[]) >>
  Cases_on `eval_operand (ssa_operand vm h) s_ssa` >> fs[ssa_result_equiv_def] >> gvs[] >>
  Cases_on `inst.inst_outputs` >> fs[ssa_result_equiv_def] >> gvs[] >>
  Cases_on `t` >> fs[ssa_result_equiv_def] >> gvs[] >>
  `sload x s_orig = sload x s_ssa` by fs[ssa_state_equiv_def, sload_def] >>
  pop_assum (fn eq => simp_tac std_ss [eq]) >>
  irule ssa_state_equiv_update_same_vm >>
  Cases_on `FLOOKUP vm h'` >> gvs[]
QED

(* Helper: TLOAD gives ssa_result_equiv with SAME vm. *)
Theorem tload_result_ssa_equiv:
  !inst inst_ssa s_orig s_ssa vm.
    ssa_state_equiv vm s_orig s_ssa /\
    inst_ssa.inst_operands = MAP (ssa_operand vm) inst.inst_operands /\
    LENGTH inst.inst_outputs <= 1 /\
    (case inst.inst_outputs of
       [] => inst_ssa.inst_outputs = []
     | [out] =>
         let ssa_out = case FLOOKUP vm out of SOME x => x | NONE => out in
         inst_ssa.inst_outputs = [ssa_out] /\
         (!v. v <> out ==> FLOOKUP vm v <> SOME ssa_out) /\
         (FLOOKUP vm ssa_out = NONE ==>
          FLOOKUP vm out = NONE \/ FLOOKUP vm out = SOME out)
     | _ => T) ==>
    ssa_result_equiv vm
      (case inst.inst_operands of
         [] => Error "tload requires 1 operand"
       | [op1] =>
         (case eval_operand op1 s_orig of
            NONE => Error "undefined operand"
          | SOME key =>
            case inst.inst_outputs of
              [] => Error "tload requires single output"
            | [out] => OK (update_var out (tload key s_orig) s_orig)
            | out::v6::v7 => Error "tload requires single output")
       | op1::v9::v10 => Error "tload requires 1 operand")
      (case inst_ssa.inst_operands of
         [] => Error "tload requires 1 operand"
       | [op1] =>
         (case eval_operand op1 s_ssa of
            NONE => Error "undefined operand"
          | SOME key =>
            case inst_ssa.inst_outputs of
              [] => Error "tload requires single output"
            | [out] => OK (update_var out (tload key s_ssa) s_ssa)
            | out::v6::v7 => Error "tload requires single output")
       | op1::v9::v10 => Error "tload requires 1 operand")
Proof
  rw[] >>
  qpat_x_assum `inst_ssa.inst_operands = _` (fn th => ONCE_REWRITE_TAC [th]) >>

  Cases_on `inst.inst_operands` >> fs[ssa_result_equiv_def] >>
  Cases_on `t` >> fs[ssa_result_equiv_def] >>
  `eval_operand h s_orig = eval_operand (ssa_operand vm h) s_ssa` by
    (irule eval_operand_ssa_equiv >> simp[]) >>
  Cases_on `eval_operand (ssa_operand vm h) s_ssa` >> fs[ssa_result_equiv_def] >> gvs[] >>
  Cases_on `inst.inst_outputs` >> fs[ssa_result_equiv_def] >> gvs[] >>
  Cases_on `t` >> fs[ssa_result_equiv_def] >> gvs[] >>
  `tload x s_orig = tload x s_ssa` by fs[ssa_state_equiv_def, tload_def] >>
  pop_assum (fn eq => simp_tac std_ss [eq]) >>
  irule ssa_state_equiv_update_same_vm >>
  Cases_on `FLOOKUP vm h'` >> gvs[]
QED

(* Helper: MSTORE gives ssa_result_equiv with SAME vm.
 * Store operations have no output variable, so vm is unchanged.
 * Note: case structure matches expanded form from gvs[AllCaseEqs()] *)
Theorem mstore_result_ssa_equiv:
  !inst inst_ssa s_orig s_ssa vm.
    ssa_state_equiv vm s_orig s_ssa /\
    inst_ssa.inst_operands = MAP (ssa_operand vm) inst.inst_operands ==>
    ssa_result_equiv vm
      (case inst.inst_operands of
         [] => Error "mstore requires 2 operands"
       | [op_val] => Error "mstore requires 2 operands"
       | [op_val; op_addr] =>
           (case eval_operand op_val s_orig of
              NONE => Error "undefined operand"
            | SOME value =>
                case eval_operand op_addr s_orig of
                  NONE => Error "undefined operand"
                | SOME addr => OK (mstore (w2n addr) value s_orig))
       | op_val::op_addr::v12::v13 => Error "mstore requires 2 operands")
      (case inst_ssa.inst_operands of
         [] => Error "mstore requires 2 operands"
       | [op_val] => Error "mstore requires 2 operands"
       | [op_val; op_addr] =>
           (case eval_operand op_val s_ssa of
              NONE => Error "undefined operand"
            | SOME value =>
                case eval_operand op_addr s_ssa of
                  NONE => Error "undefined operand"
                | SOME addr => OK (mstore (w2n addr) value s_ssa))
       | op_val::op_addr::v12::v13 => Error "mstore requires 2 operands")
Proof
  rw[] >>
  qpat_x_assum `inst_ssa.inst_operands = _` (fn th => ONCE_REWRITE_TAC [th]) >>

  Cases_on `inst.inst_operands` >> fs[ssa_result_equiv_def] >>
  Cases_on `t` >> fs[ssa_result_equiv_def] >>
  Cases_on `t'` >> fs[ssa_result_equiv_def] >>
  `eval_operand h s_orig = eval_operand (ssa_operand vm h) s_ssa` by
    (irule eval_operand_ssa_equiv >> simp[]) >>
  `eval_operand h' s_orig = eval_operand (ssa_operand vm h') s_ssa` by
    (irule eval_operand_ssa_equiv >> simp[]) >>
  gvs[] >>
  Cases_on `eval_operand (ssa_operand vm h) s_ssa` >> gvs[ssa_result_equiv_def] >>
  Cases_on `eval_operand (ssa_operand vm h') s_ssa` >> gvs[ssa_result_equiv_def] >>
  irule mstore_ssa_equiv >> simp[]
QED

(* Helper: SSTORE gives ssa_result_equiv with SAME vm. *)
Theorem sstore_result_ssa_equiv:
  !inst inst_ssa s_orig s_ssa vm.
    ssa_state_equiv vm s_orig s_ssa /\
    inst_ssa.inst_operands = MAP (ssa_operand vm) inst.inst_operands ==>
    ssa_result_equiv vm
      (case inst.inst_operands of
         [] => Error "sstore requires 2 operands"
       | [op_val] => Error "sstore requires 2 operands"
       | [op_val; op_key] =>
           (case eval_operand op_val s_orig of
              NONE => Error "undefined operand"
            | SOME value =>
                case eval_operand op_key s_orig of
                  NONE => Error "undefined operand"
                | SOME key => OK (sstore key value s_orig))
       | op_val::op_key::v12::v13 => Error "sstore requires 2 operands")
      (case inst_ssa.inst_operands of
         [] => Error "sstore requires 2 operands"
       | [op_val] => Error "sstore requires 2 operands"
       | [op_val; op_key] =>
           (case eval_operand op_val s_ssa of
              NONE => Error "undefined operand"
            | SOME value =>
                case eval_operand op_key s_ssa of
                  NONE => Error "undefined operand"
                | SOME key => OK (sstore key value s_ssa))
       | op_val::op_key::v12::v13 => Error "sstore requires 2 operands")
Proof
  rw[] >>
  qpat_x_assum `inst_ssa.inst_operands = _` (fn th => ONCE_REWRITE_TAC [th]) >>

  Cases_on `inst.inst_operands` >> fs[ssa_result_equiv_def] >>
  Cases_on `t` >> fs[ssa_result_equiv_def] >>
  Cases_on `t'` >> fs[ssa_result_equiv_def] >>
  `eval_operand h s_orig = eval_operand (ssa_operand vm h) s_ssa` by
    (irule eval_operand_ssa_equiv >> simp[]) >>
  `eval_operand h' s_orig = eval_operand (ssa_operand vm h') s_ssa` by
    (irule eval_operand_ssa_equiv >> simp[]) >>
  gvs[] >>
  Cases_on `eval_operand (ssa_operand vm h) s_ssa` >> gvs[ssa_result_equiv_def] >>
  Cases_on `eval_operand (ssa_operand vm h') s_ssa` >> gvs[ssa_result_equiv_def] >>
  irule sstore_ssa_equiv >> simp[]
QED

(* Helper: TSTORE gives ssa_result_equiv with SAME vm. *)
Theorem tstore_result_ssa_equiv:
  !inst inst_ssa s_orig s_ssa vm.
    ssa_state_equiv vm s_orig s_ssa /\
    inst_ssa.inst_operands = MAP (ssa_operand vm) inst.inst_operands ==>
    ssa_result_equiv vm
      (case inst.inst_operands of
         [] => Error "tstore requires 2 operands"
       | [op_val] => Error "tstore requires 2 operands"
       | [op_val; op_key] =>
           (case eval_operand op_val s_orig of
              NONE => Error "undefined operand"
            | SOME value =>
                case eval_operand op_key s_orig of
                  NONE => Error "undefined operand"
                | SOME key => OK (tstore key value s_orig))
       | op_val::op_key::v12::v13 => Error "tstore requires 2 operands")
      (case inst_ssa.inst_operands of
         [] => Error "tstore requires 2 operands"
       | [op_val] => Error "tstore requires 2 operands"
       | [op_val; op_key] =>
           (case eval_operand op_val s_ssa of
              NONE => Error "undefined operand"
            | SOME value =>
                case eval_operand op_key s_ssa of
                  NONE => Error "undefined operand"
                | SOME key => OK (tstore key value s_ssa))
       | op_val::op_key::v12::v13 => Error "tstore requires 2 operands")
Proof
  rw[] >>
  qpat_x_assum `inst_ssa.inst_operands = _` (fn th => ONCE_REWRITE_TAC [th]) >>

  Cases_on `inst.inst_operands` >> fs[ssa_result_equiv_def] >>
  Cases_on `t` >> fs[ssa_result_equiv_def] >>
  Cases_on `t'` >> fs[ssa_result_equiv_def] >>
  `eval_operand h s_orig = eval_operand (ssa_operand vm h) s_ssa` by
    (irule eval_operand_ssa_equiv >> simp[]) >>
  `eval_operand h' s_orig = eval_operand (ssa_operand vm h') s_ssa` by
    (irule eval_operand_ssa_equiv >> simp[]) >>
  gvs[] >>
  Cases_on `eval_operand (ssa_operand vm h) s_ssa` >> gvs[ssa_result_equiv_def] >>
  Cases_on `eval_operand (ssa_operand vm h') s_ssa` >> gvs[ssa_result_equiv_def] >>
  irule tstore_ssa_equiv >> simp[]
QED

(* Helper: ASSERT gives ssa_result_equiv with SAME vm. *)
Theorem assert_result_ssa_equiv:
  !inst inst_ssa s_orig s_ssa vm.
    ssa_state_equiv vm s_orig s_ssa /\
    inst_ssa.inst_operands = MAP (ssa_operand vm) inst.inst_operands ==>
    ssa_result_equiv vm
      (case inst.inst_operands of
         [cond_op] =>
           (case eval_operand cond_op s_orig of
              SOME cond =>
                if cond = 0w then Revert (revert_state s_orig)
                else OK s_orig
            | NONE => Error "undefined operand")
       | _ => Error "assert requires 1 operand")
      (case inst_ssa.inst_operands of
         [cond_op] =>
           (case eval_operand cond_op s_ssa of
              SOME cond =>
                if cond = 0w then Revert (revert_state s_ssa)
                else OK s_ssa
            | NONE => Error "undefined operand")
       | _ => Error "assert requires 1 operand")
Proof
  rw[] >>
  qpat_x_assum `inst_ssa.inst_operands = _` (fn th => ONCE_REWRITE_TAC [th]) >>
  Cases_on `inst.inst_operands` >> fs[ssa_result_equiv_def] >>
  Cases_on `t` >> fs[ssa_result_equiv_def] >>
  `eval_operand h s_orig = eval_operand (ssa_operand vm h) s_ssa` by
    (irule eval_operand_ssa_equiv >> simp[]) >>
  Cases_on `eval_operand (ssa_operand vm h) s_ssa` >> fs[ssa_result_equiv_def] >> gvs[] >>
  Cases_on `x = 0w` >> gvs[ssa_result_equiv_def] >>
  irule revert_state_ssa_equiv >> simp[]
QED

(* Helper: ASSERT_UNREACHABLE gives ssa_result_equiv with SAME vm. *)
Theorem assert_unreachable_result_ssa_equiv:
  !inst inst_ssa s_orig s_ssa vm.
    ssa_state_equiv vm s_orig s_ssa /\
    inst_ssa.inst_operands = MAP (ssa_operand vm) inst.inst_operands ==>
    ssa_result_equiv vm
      (case inst.inst_operands of
         [cond_op] =>
           (case eval_operand cond_op s_orig of
              SOME cond =>
                if cond <> 0w then Halt (halt_state s_orig)
                else OK s_orig
            | NONE => Error "undefined operand")
       | _ => Error "assert_unreachable requires 1 operand")
      (case inst_ssa.inst_operands of
         [cond_op] =>
           (case eval_operand cond_op s_ssa of
              SOME cond =>
                if cond <> 0w then Halt (halt_state s_ssa)
                else OK s_ssa
            | NONE => Error "undefined operand")
       | _ => Error "assert_unreachable requires 1 operand")
Proof
  rw[] >>
  qpat_x_assum `inst_ssa.inst_operands = _` (fn th => ONCE_REWRITE_TAC [th]) >>
  Cases_on `inst.inst_operands` >> fs[ssa_result_equiv_def] >>
  Cases_on `t` >> fs[ssa_result_equiv_def] >>
  `eval_operand h s_orig = eval_operand (ssa_operand vm h) s_ssa` by
    (irule eval_operand_ssa_equiv >> simp[]) >>
  Cases_on `eval_operand (ssa_operand vm h) s_ssa` >> fs[ssa_result_equiv_def] >> gvs[] >>
  Cases_on `x <> 0w` >> gvs[ssa_result_equiv_def] >>
  irule halt_state_ssa_equiv >> simp[]
QED

(* Helper: BLOCKHASH gives ssa_result_equiv with SAME vm. *)
Theorem blockhash_result_ssa_equiv:
  !inst inst_ssa s_orig s_ssa vm.
    ssa_state_equiv vm s_orig s_ssa /\
    inst_ssa.inst_operands = MAP (ssa_operand vm) inst.inst_operands /\
    LENGTH inst.inst_outputs <= 1 /\
    (case inst.inst_outputs of
       [] => inst_ssa.inst_outputs = []
     | [out] =>
         let ssa_out = case FLOOKUP vm out of SOME x => x | NONE => out in
         inst_ssa.inst_outputs = [ssa_out] /\
         (!v. v <> out ==> FLOOKUP vm v <> SOME ssa_out) /\
         (FLOOKUP vm ssa_out = NONE ==>
          FLOOKUP vm out = NONE \/ FLOOKUP vm out = SOME out)
     | _ => T) ==>
    ssa_result_equiv vm
      (case inst.inst_operands of
         [] => Error "blockhash requires 1 operand"
       | [op1] =>
         (case eval_operand op1 s_orig of
            NONE => Error "undefined operand"
          | SOME blocknum =>
              case inst.inst_outputs of
                [] => Error "blockhash requires single output"
              | [out] => OK (update_var out (s_orig.vs_block_ctx.bc_blockhash (w2n blocknum)) s_orig)
              | out::v6::v7 => Error "blockhash requires single output")
       | op1::v9::v10 => Error "blockhash requires 1 operand")
      (case inst_ssa.inst_operands of
         [] => Error "blockhash requires 1 operand"
       | [op1] =>
         (case eval_operand op1 s_ssa of
            NONE => Error "undefined operand"
          | SOME blocknum =>
              case inst_ssa.inst_outputs of
                [] => Error "blockhash requires single output"
              | [out] => OK (update_var out (s_ssa.vs_block_ctx.bc_blockhash (w2n blocknum)) s_ssa)
              | out::v6::v7 => Error "blockhash requires single output")
       | op1::v9::v10 => Error "blockhash requires 1 operand")
Proof
  rw[] >>
  qpat_x_assum `inst_ssa.inst_operands = _` (fn th => ONCE_REWRITE_TAC [th]) >>

  Cases_on `inst.inst_operands` >| [
    gvs[ssa_result_equiv_def],
    (Cases_on `t` >| [
        (`eval_operand h s_orig = eval_operand (ssa_operand vm h) s_ssa` by
           (irule eval_operand_ssa_equiv >> simp[]) >>
        Cases_on `eval_operand (ssa_operand vm h) s_ssa` >>
        fs[ssa_result_equiv_def] >> gvs[] >>
        Cases_on `inst.inst_outputs` >> fs[ssa_result_equiv_def] >> gvs[] >>
        Cases_on `t` >> fs[ssa_result_equiv_def] >> gvs[] >>
        `s_orig.vs_block_ctx = s_ssa.vs_block_ctx` by fs[ssa_state_equiv_def] >>
        pop_assum (fn eq => simp_tac std_ss [eq]) >>
        irule ssa_state_equiv_update_same_vm >>
        Cases_on `FLOOKUP vm h'` >> gvs[]),
       gvs[ssa_result_equiv_def]
     ])
  ]
QED

(* Helper: BALANCE gives ssa_result_equiv with SAME vm. *)
Theorem balance_result_ssa_equiv:
  !inst inst_ssa s_orig s_ssa vm.
    ssa_state_equiv vm s_orig s_ssa /\
    inst_ssa.inst_operands = MAP (ssa_operand vm) inst.inst_operands /\
    LENGTH inst.inst_outputs <= 1 /\
    (case inst.inst_outputs of
       [] => inst_ssa.inst_outputs = []
     | [out] =>
         let ssa_out = case FLOOKUP vm out of SOME x => x | NONE => out in
         inst_ssa.inst_outputs = [ssa_out] /\
         (!v. v <> out ==> FLOOKUP vm v <> SOME ssa_out) /\
         (FLOOKUP vm ssa_out = NONE ==>
          FLOOKUP vm out = NONE \/ FLOOKUP vm out = SOME out)
     | _ => T) ==>
    ssa_result_equiv vm
      (case inst.inst_operands of
         [] => Error "balance requires 1 operand"
       | [op1] =>
         (case eval_operand op1 s_orig of
            NONE => Error "undefined operand"
          | SOME addr =>
              case inst.inst_outputs of
                [] => Error "balance requires single output"
              | [out] =>
                  OK
                    (update_var out
                       (n2w (lookup_account (w2w addr) s_orig.vs_accounts).balance)
                       s_orig)
              | out::v6::v7 => Error "balance requires single output")
       | op1::v9::v10 => Error "balance requires 1 operand")
      (case inst_ssa.inst_operands of
         [] => Error "balance requires 1 operand"
       | [op1] =>
         (case eval_operand op1 s_ssa of
            NONE => Error "undefined operand"
          | SOME addr =>
              case inst_ssa.inst_outputs of
                [] => Error "balance requires single output"
              | [out] =>
                  OK
                    (update_var out
                       (n2w (lookup_account (w2w addr) s_ssa.vs_accounts).balance)
                       s_ssa)
              | out::v6::v7 => Error "balance requires single output")
       | op1::v9::v10 => Error "balance requires 1 operand")
Proof
  rw[] >>
  qpat_x_assum `inst_ssa.inst_operands = _` (fn th => ONCE_REWRITE_TAC [th]) >>

  Cases_on `inst.inst_operands` >| [
    gvs[ssa_result_equiv_def],
    (Cases_on `t` >| [
        (`eval_operand h s_orig = eval_operand (ssa_operand vm h) s_ssa` by
           (irule eval_operand_ssa_equiv >> simp[]) >>
        Cases_on `eval_operand (ssa_operand vm h) s_ssa` >>
        fs[ssa_result_equiv_def] >> gvs[] >>
        Cases_on `inst.inst_outputs` >> fs[ssa_result_equiv_def] >> gvs[] >>
        Cases_on `t` >> fs[ssa_result_equiv_def] >> gvs[] >>
        `s_orig.vs_accounts = s_ssa.vs_accounts` by fs[ssa_state_equiv_def] >>
        pop_assum (fn eq => simp_tac std_ss [eq]) >>
        irule ssa_state_equiv_update_same_vm >>
        Cases_on `FLOOKUP vm h'` >> gvs[]),
       gvs[ssa_result_equiv_def]
     ])
  ]
QED

(* Helper: CALLDATALOAD gives ssa_result_equiv with SAME vm. *)
Theorem calldataload_result_ssa_equiv:
  !inst inst_ssa s_orig s_ssa vm.
    ssa_state_equiv vm s_orig s_ssa /\
    inst_ssa.inst_operands = MAP (ssa_operand vm) inst.inst_operands /\
    LENGTH inst.inst_outputs <= 1 /\
    (case inst.inst_outputs of
       [] => inst_ssa.inst_outputs = []
     | [out] =>
         let ssa_out = case FLOOKUP vm out of SOME x => x | NONE => out in
         inst_ssa.inst_outputs = [ssa_out] /\
         (!v. v <> out ==> FLOOKUP vm v <> SOME ssa_out) /\
         (FLOOKUP vm ssa_out = NONE ==>
          FLOOKUP vm out = NONE \/ FLOOKUP vm out = SOME out)
     | _ => T) ==>
    ssa_result_equiv vm
      (case inst.inst_operands of
         [] => Error "calldataload requires 1 operand"
       | [op1] =>
         (case eval_operand op1 s_orig of
            NONE => Error "undefined operand"
          | SOME offset =>
              case inst.inst_outputs of
                [] => Error "calldataload requires single output"
              | [out] =>
                  OK
                    (update_var out
                       (word_of_bytes T (0w:bytes32)
                          (TAKE 32
                             (DROP (w2n offset) s_orig.vs_call_ctx.cc_calldata ++
                              REPLICATE 32 0w))) s_orig)
              | out::v6::v7 => Error "calldataload requires single output")
       | op1::v9::v10 => Error "calldataload requires 1 operand")
      (case inst_ssa.inst_operands of
         [] => Error "calldataload requires 1 operand"
       | [op1] =>
         (case eval_operand op1 s_ssa of
            NONE => Error "undefined operand"
          | SOME offset =>
              case inst_ssa.inst_outputs of
                [] => Error "calldataload requires single output"
              | [out] =>
                  OK
                    (update_var out
                       (word_of_bytes T (0w:bytes32)
                          (TAKE 32
                             (DROP (w2n offset) s_ssa.vs_call_ctx.cc_calldata ++
                              REPLICATE 32 0w))) s_ssa)
              | out::v6::v7 => Error "calldataload requires single output")
       | op1::v9::v10 => Error "calldataload requires 1 operand")
Proof
  rw[] >>
  qpat_x_assum `inst_ssa.inst_operands = _` (fn th => ONCE_REWRITE_TAC [th]) >>

  Cases_on `inst.inst_operands` >| [
    gvs[ssa_result_equiv_def],
    (Cases_on `t` >| [
        (`eval_operand h s_orig = eval_operand (ssa_operand vm h) s_ssa` by
           (irule eval_operand_ssa_equiv >> simp[]) >>
        Cases_on `eval_operand (ssa_operand vm h) s_ssa` >>
        fs[ssa_result_equiv_def] >> gvs[] >>
        Cases_on `inst.inst_outputs` >> fs[ssa_result_equiv_def] >> gvs[] >>
        Cases_on `t` >> fs[ssa_result_equiv_def] >> gvs[] >>
        `s_orig.vs_call_ctx = s_ssa.vs_call_ctx` by fs[ssa_state_equiv_def] >>
        pop_assum (fn eq => simp_tac std_ss [eq]) >>
        irule ssa_state_equiv_update_same_vm >>
        Cases_on `FLOOKUP vm h'` >> gvs[]),
       gvs[ssa_result_equiv_def]
     ])
  ]
QED

(* Helper: SHA3 gives ssa_result_equiv with SAME vm. *)
Theorem sha3_result_ssa_equiv:
  !inst inst_ssa s_orig s_ssa vm.
    ssa_state_equiv vm s_orig s_ssa /\
    inst_ssa_compatible vm inst inst_ssa /\
    LENGTH inst.inst_outputs <= 1 ==>
    ssa_result_equiv vm
      (case inst.inst_operands of
         [] => Error "sha3 requires 2 operands"
       | [op_size] => Error "sha3 requires 2 operands"
       | [op_size; op_offset] =>
         (case eval_operand op_size s_orig of
            NONE => Error "undefined operand"
          | SOME size_val =>
              case eval_operand op_offset s_orig of
                NONE => Error "undefined operand"
              | SOME offset =>
                  case inst.inst_outputs of
                    [] => Error "sha3 requires single output"
                  | [out] =>
                      OK
                        (update_var out
                           (word_of_bytes T 0w
                              (Keccak_256_w64
                                 (TAKE (w2n size_val)
                                    (DROP (w2n offset) s_orig.vs_memory ++
                                     REPLICATE (w2n size_val) 0w)))) s_orig)
                  | out::v6::v7 => Error "sha3 requires single output")
       | op_size::op_offset::v10::v11 => Error "sha3 requires 2 operands")
      (case inst_ssa.inst_operands of
         [] => Error "sha3 requires 2 operands"
       | [op_size] => Error "sha3 requires 2 operands"
       | [op_size; op_offset] =>
         (case eval_operand op_size s_ssa of
            NONE => Error "undefined operand"
          | SOME size_val =>
              case eval_operand op_offset s_ssa of
                NONE => Error "undefined operand"
              | SOME offset =>
                  case inst_ssa.inst_outputs of
                    [] => Error "sha3 requires single output"
                  | [out] =>
                      OK
                        (update_var out
                           (word_of_bytes T 0w
                              (Keccak_256_w64
                                 (TAKE (w2n size_val)
                                    (DROP (w2n offset) s_ssa.vs_memory ++
                                     REPLICATE (w2n size_val) 0w)))) s_ssa)
                  | out::v6::v7 => Error "sha3 requires single output")
       | op_size::op_offset::v10::v11 => Error "sha3 requires 2 operands")
Proof
  rpt strip_tac >>
  `inst_ssa.inst_operands = MAP (ssa_operand vm) inst.inst_operands` by
    fs[inst_ssa_compatible_def] >>
  Cases_on `inst.inst_operands` >| [
    gvs[inst_ssa_compatible_def, ssa_result_equiv_def],
    (Cases_on `t` >| [
       gvs[inst_ssa_compatible_def, ssa_result_equiv_def],
       (Cases_on `t'` >| [
          (simp[] >>
           `eval_operand h s_orig = eval_operand (ssa_operand vm h) s_ssa` by
             (irule eval_operand_ssa_equiv >> simp[]) >>
           `eval_operand h' s_orig = eval_operand (ssa_operand vm h') s_ssa` by
             (irule eval_operand_ssa_equiv >> simp[]) >>
           Cases_on `eval_operand (ssa_operand vm h) s_ssa` >>
           gvs[ssa_result_equiv_def] >>
           Cases_on `eval_operand (ssa_operand vm h') s_ssa` >>
           gvs[ssa_result_equiv_def] >>
           Cases_on `inst.inst_outputs` >| [
             gvs[inst_ssa_compatible_def, ssa_result_equiv_def],
             (Cases_on `t` >| [
                (drule_all inst_ssa_compatible_outputs_equiv >> strip_tac >>
                 gvs[ssa_result_equiv_def] >>
                 `s_orig.vs_memory = s_ssa.vs_memory` by fs[ssa_state_equiv_def] >>
                 pop_assum (fn eq => simp_tac std_ss [eq]) >>
                 irule ssa_state_equiv_update_same_vm >>
                 gvs[]),
                gvs[ssa_result_equiv_def]
              ])
           ]),
          gvs[inst_ssa_compatible_def, ssa_result_equiv_def]
        ])
     ])
  ]
QED

(* Helper: SHA3_64 gives ssa_result_equiv with SAME vm. *)
Theorem sha3_64_result_ssa_equiv:
  !inst inst_ssa s_orig s_ssa vm.
    ssa_state_equiv vm s_orig s_ssa /\
    inst_ssa_compatible vm inst inst_ssa /\
    LENGTH inst.inst_outputs <= 1 ==>
    ssa_result_equiv vm
      (case inst.inst_operands of
         [] => Error "sha3_64 requires 2 operands"
       | [op2] => Error "sha3_64 requires 2 operands"
       | [op2; op1] =>
         (case eval_operand op1 s_orig of
            NONE => Error "undefined operand"
          | SOME v1 =>
              case eval_operand op2 s_orig of
                NONE => Error "undefined operand"
              | SOME v2 =>
                  case inst.inst_outputs of
                    [] => Error "sha3_64 requires single output"
                  | [out] =>
                      OK
                        (update_var out
                           (word_of_bytes T 0w
                              (Keccak_256_w64
                                 (word_to_bytes v1 T ++ word_to_bytes v2 T)))
                           s_orig)
                  | out::v6::v7 => Error "sha3_64 requires single output")
       | op2::op1::v10::v11 => Error "sha3_64 requires 2 operands")
      (case inst_ssa.inst_operands of
         [] => Error "sha3_64 requires 2 operands"
       | [op2] => Error "sha3_64 requires 2 operands"
       | [op2; op1] =>
         (case eval_operand op1 s_ssa of
            NONE => Error "undefined operand"
          | SOME v1 =>
              case eval_operand op2 s_ssa of
                NONE => Error "undefined operand"
              | SOME v2 =>
                  case inst_ssa.inst_outputs of
                    [] => Error "sha3_64 requires single output"
                  | [out] =>
                      OK
                        (update_var out
                           (word_of_bytes T 0w
                              (Keccak_256_w64
                                 (word_to_bytes v1 T ++ word_to_bytes v2 T)))
                           s_ssa)
                  | out::v6::v7 => Error "sha3_64 requires single output")
       | op2::op1::v10::v11 => Error "sha3_64 requires 2 operands")
Proof
  rpt strip_tac >>
  `inst_ssa.inst_operands = MAP (ssa_operand vm) inst.inst_operands` by
    fs[inst_ssa_compatible_def] >>
  Cases_on `inst.inst_operands` >| [
    gvs[inst_ssa_compatible_def, ssa_result_equiv_def],
    (Cases_on `t` >| [
       gvs[inst_ssa_compatible_def, ssa_result_equiv_def],
       (Cases_on `t'` >| [
          (simp[] >>
           `eval_operand h s_orig = eval_operand (ssa_operand vm h) s_ssa` by
             (irule eval_operand_ssa_equiv >> simp[]) >>
           `eval_operand h' s_orig = eval_operand (ssa_operand vm h') s_ssa` by
             (irule eval_operand_ssa_equiv >> simp[]) >>
           Cases_on `eval_operand (ssa_operand vm h') s_ssa` >>
           gvs[ssa_result_equiv_def] >>
           Cases_on `eval_operand (ssa_operand vm h) s_ssa` >>
           gvs[ssa_result_equiv_def] >>
           Cases_on `inst.inst_outputs` >| [
             gvs[inst_ssa_compatible_def, ssa_result_equiv_def],
             (Cases_on `t` >| [
                (drule_all inst_ssa_compatible_outputs_equiv >> strip_tac >>
                 gvs[ssa_result_equiv_def] >>
                 `s_orig.vs_memory = s_ssa.vs_memory` by fs[ssa_state_equiv_def] >>
                 pop_assum (fn eq => simp_tac std_ss [eq]) >>
                 irule ssa_state_equiv_update_same_vm >>
                 gvs[]),
                gvs[ssa_result_equiv_def]
              ])
           ]),
          gvs[inst_ssa_compatible_def, ssa_result_equiv_def]
        ])
     ])
  ]
QED

(* Helper: CALLDATACOPY gives ssa_result_equiv with SAME vm. *)
Theorem calldatacopy_result_ssa_equiv:
  !inst inst_ssa s_orig s_ssa vm.
    ssa_state_equiv vm s_orig s_ssa /\
    inst_ssa.inst_operands = MAP (ssa_operand vm) inst.inst_operands ==>
    ssa_result_equiv vm
      (case inst.inst_operands of
         [] => Error "calldatacopy requires 3 operands"
       | [op_size] => Error "calldatacopy requires 3 operands"
       | [op_size; op_offset] => Error "calldatacopy requires 3 operands"
       | [op_size; op_offset; op_destOffset] =>
         (case eval_operand op_size s_orig of
            NONE => Error "undefined operand"
          | SOME size_val =>
              case eval_operand op_offset s_orig of
                NONE => Error "undefined operand"
              | SOME offset =>
                  case eval_operand op_destOffset s_orig of
                    NONE => Error "undefined operand"
                  | SOME destOffset =>
                      OK
                        (write_memory_with_expansion (w2n destOffset)
                           (TAKE (w2n size_val)
                              (DROP (w2n offset) s_orig.vs_call_ctx.cc_calldata ++
                               REPLICATE (w2n size_val) 0w)) s_orig))
       | op_size::op_offset::op_destOffset::v10 => Error "calldatacopy requires 3 operands")
      (case inst_ssa.inst_operands of
         [] => Error "calldatacopy requires 3 operands"
       | [op_size] => Error "calldatacopy requires 3 operands"
       | [op_size; op_offset] => Error "calldatacopy requires 3 operands"
       | [op_size; op_offset; op_destOffset] =>
         (case eval_operand op_size s_ssa of
            NONE => Error "undefined operand"
          | SOME size_val =>
              case eval_operand op_offset s_ssa of
                NONE => Error "undefined operand"
              | SOME offset =>
                  case eval_operand op_destOffset s_ssa of
                    NONE => Error "undefined operand"
                  | SOME destOffset =>
                      OK
                        (write_memory_with_expansion (w2n destOffset)
                           (TAKE (w2n size_val)
                              (DROP (w2n offset) s_ssa.vs_call_ctx.cc_calldata ++
                               REPLICATE (w2n size_val) 0w)) s_ssa))
       | op_size::op_offset::op_destOffset::v10 => Error "calldatacopy requires 3 operands")
Proof
  rw[] >>
  qpat_x_assum `inst_ssa.inst_operands = _` (fn th => ONCE_REWRITE_TAC [th]) >>

  simp[option_triple_case] >>
  Cases_on `inst.inst_operands` >| [
    gvs[ssa_result_equiv_def],
    (Cases_on `t` >| [
       gvs[ssa_result_equiv_def],
       (Cases_on `t'` >| [
          gvs[ssa_result_equiv_def],
          (rename1 `h''::t_tail` >>
           Cases_on `t_tail` >| [
             (`eval_operand h s_orig = eval_operand (ssa_operand vm h) s_ssa` by
                (irule eval_operand_ssa_equiv >> simp[]) >>
              `eval_operand h' s_orig = eval_operand (ssa_operand vm h') s_ssa` by
                (irule eval_operand_ssa_equiv >> simp[]) >>
              `eval_operand h'' s_orig = eval_operand (ssa_operand vm h'') s_ssa` by
                (irule eval_operand_ssa_equiv >> simp[]) >>
              gvs[] >>
              Cases_on `eval_operand (ssa_operand vm h) s_ssa` >>
              gvs[ssa_result_equiv_def] >>
              Cases_on `eval_operand (ssa_operand vm h') s_ssa` >>
              gvs[ssa_result_equiv_def] >>
              Cases_on `eval_operand (ssa_operand vm h'') s_ssa` >>
              gvs[ssa_result_equiv_def, AllCaseEqs()] >>
              `s_orig.vs_call_ctx = s_ssa.vs_call_ctx` by fs[ssa_state_equiv_def] >>
              pop_assum (fn eq => simp_tac std_ss [eq]) >>
              irule write_memory_with_expansion_ssa_equiv >>
              simp[]),
             gvs[ssa_result_equiv_def]
           ])
        ])
     ])
  ]
QED

(* Helper: RETURNDATACOPY gives ssa_result_equiv with SAME vm. *)
Theorem returndatacopy_result_ssa_equiv:
  !inst inst_ssa s_orig s_ssa vm.
    ssa_state_equiv vm s_orig s_ssa /\
    inst_ssa.inst_operands = MAP (ssa_operand vm) inst.inst_operands ==>
    ssa_result_equiv vm
      (case inst.inst_operands of
         [] => Error "returndatacopy requires 3 operands"
       | [op_size] => Error "returndatacopy requires 3 operands"
       | [op_size; op_offset] => Error "returndatacopy requires 3 operands"
       | [op_size; op_offset; op_destOffset] =>
         (case eval_operand op_size s_orig of
            NONE => Error "undefined operand"
          | SOME size_val =>
              case eval_operand op_offset s_orig of
                NONE => Error "undefined operand"
              | SOME offset =>
                  case eval_operand op_destOffset s_orig of
                    NONE => Error "undefined operand"
                  | SOME destOffset =>
                      if w2n offset + w2n size_val > LENGTH s_orig.vs_returndata then
                        Revert (revert_state s_orig)
                      else
                        OK
                          (write_memory_with_expansion (w2n destOffset)
                             (TAKE (w2n size_val)
                                (DROP (w2n offset) s_orig.vs_returndata)) s_orig))
       | op_size::op_offset::op_destOffset::v10 => Error "returndatacopy requires 3 operands")
      (case inst_ssa.inst_operands of
         [] => Error "returndatacopy requires 3 operands"
       | [op_size] => Error "returndatacopy requires 3 operands"
       | [op_size; op_offset] => Error "returndatacopy requires 3 operands"
       | [op_size; op_offset; op_destOffset] =>
         (case eval_operand op_size s_ssa of
            NONE => Error "undefined operand"
          | SOME size_val =>
              case eval_operand op_offset s_ssa of
                NONE => Error "undefined operand"
              | SOME offset =>
                  case eval_operand op_destOffset s_ssa of
                    NONE => Error "undefined operand"
                  | SOME destOffset =>
                      if w2n offset + w2n size_val > LENGTH s_ssa.vs_returndata then
                        Revert (revert_state s_ssa)
                      else
                        OK
                          (write_memory_with_expansion (w2n destOffset)
                             (TAKE (w2n size_val)
                                (DROP (w2n offset) s_ssa.vs_returndata)) s_ssa))
       | op_size::op_offset::op_destOffset::v10 => Error "returndatacopy requires 3 operands")
Proof
  rw[] >>
  qpat_x_assum `inst_ssa.inst_operands = _` (fn th => ONCE_REWRITE_TAC [th]) >>

  simp[option_triple_case] >>
  Cases_on `inst.inst_operands` >| [
    gvs[ssa_result_equiv_def],
    (Cases_on `t` >| [
       gvs[ssa_result_equiv_def],
       (Cases_on `t'` >| [
          gvs[ssa_result_equiv_def],
          (rename1 `h''::t_tail` >>
           Cases_on `t_tail` >| [
             (`eval_operand h s_orig = eval_operand (ssa_operand vm h) s_ssa` by
                (irule eval_operand_ssa_equiv >> simp[]) >>
              `eval_operand h' s_orig = eval_operand (ssa_operand vm h') s_ssa` by
                (irule eval_operand_ssa_equiv >> simp[]) >>
              `eval_operand h'' s_orig = eval_operand (ssa_operand vm h'') s_ssa` by
                (irule eval_operand_ssa_equiv >> simp[]) >>
              gvs[] >>
              Cases_on `eval_operand (ssa_operand vm h) s_ssa` >>
              gvs[ssa_result_equiv_def] >>
              Cases_on `eval_operand (ssa_operand vm h') s_ssa` >>
              gvs[ssa_result_equiv_def] >>
              Cases_on `eval_operand (ssa_operand vm h'') s_ssa` >>
              gvs[ssa_result_equiv_def, AllCaseEqs()] >>
              `s_orig.vs_returndata = s_ssa.vs_returndata` by fs[ssa_state_equiv_def] >>
              pop_assum (fn eq => simp_tac std_ss [eq]) >>
              simp[LET_DEF] >>
              CASE_TAC >| [
                (gvs[ssa_result_equiv_def] >>
                 irule revert_state_ssa_equiv >> simp[]),
                (gvs[ssa_result_equiv_def] >>
                 irule write_memory_with_expansion_ssa_equiv >> simp[])
              ]),
             gvs[ssa_result_equiv_def]
           ])
        ])
     ])
  ]
QED

(* Helper: ASSIGN gives ssa_result_equiv with SAME vm.
 * ASSIGN has one operand and one output variable. *)
Theorem assign_result_ssa_equiv:
  !inst inst_ssa s_orig s_ssa vm.
    ssa_state_equiv vm s_orig s_ssa /\
    inst_ssa.inst_operands = MAP (ssa_operand vm) inst.inst_operands /\
    LENGTH inst.inst_outputs <= 1 /\
    (case inst.inst_outputs of
       [] => inst_ssa.inst_outputs = []
     | [out] =>
         let ssa_out = case FLOOKUP vm out of SOME x => x | NONE => out in
         inst_ssa.inst_outputs = [ssa_out] /\
         (!v. v <> out ==> FLOOKUP vm v <> SOME ssa_out) /\
         (FLOOKUP vm ssa_out = NONE ==>
          FLOOKUP vm out = NONE \/ FLOOKUP vm out = SOME out)
     | _ => T) ==>
    ssa_result_equiv vm
      (case inst.inst_operands of
         [] => Error "assign requires 1 operand and single output"
       | op1::ops =>
           case inst.inst_outputs of
             [] => Error "assign requires 1 operand and single output"
           | [out] =>
               (case ops of
                  [] =>
                    (case eval_operand op1 s_orig of
                       SOME v => OK (update_var out v s_orig)
                     | NONE => Error "undefined operand")
                | _ => Error "assign requires 1 operand and single output")
           | _ => Error "assign requires 1 operand and single output")
      (case inst_ssa.inst_operands of
         [] => Error "assign requires 1 operand and single output"
       | op1::ops =>
           case inst_ssa.inst_outputs of
             [] => Error "assign requires 1 operand and single output"
           | [out] =>
               (case ops of
                  [] =>
                    (case eval_operand op1 s_ssa of
                       SOME v => OK (update_var out v s_ssa)
                     | NONE => Error "undefined operand")
                | _ => Error "assign requires 1 operand and single output")
           | _ => Error "assign requires 1 operand and single output")
Proof
  rw[] >>
  qpat_x_assum `inst_ssa.inst_operands = _` (fn th => ONCE_REWRITE_TAC [th]) >>
  Cases_on `inst.inst_operands` >> fs[ssa_result_equiv_def] >>
  Cases_on `t` >> fs[ssa_result_equiv_def] >>
  Cases_on `inst.inst_outputs` >> fs[ssa_result_equiv_def] >>
  Cases_on `t` >> fs[ssa_result_equiv_def] >>
  (* Now have [h] operand and [h'] output *)
  `eval_operand h s_orig = eval_operand (ssa_operand vm h) s_ssa` by
    (irule eval_operand_ssa_equiv >> simp[]) >>
  gvs[] >>
  Cases_on `eval_operand (ssa_operand vm h) s_ssa` >> gvs[ssa_result_equiv_def] >>
  irule ssa_state_equiv_update_same_vm >>
  Cases_on `FLOOKUP vm h'` >> gvs[]
QED

(* Helper: JMP gives ssa_result_equiv with SAME vm.
 * Labels are not renamed in SSA, so jump targets match. *)
Theorem jmp_result_ssa_equiv:
  !inst inst_ssa s_orig s_ssa vm.
    ssa_state_equiv vm s_orig s_ssa /\
    inst_ssa.inst_operands = MAP (ssa_operand vm) inst.inst_operands ==>
    ssa_result_equiv vm
      (case inst.inst_operands of
         [Label target] => OK (jump_to target s_orig)
       | _ => Error "jmp requires label operand")
      (case inst_ssa.inst_operands of
         [Label target] => OK (jump_to target s_ssa)
       | _ => Error "jmp requires label operand")
Proof
  rw[] >>
  qpat_x_assum `inst_ssa.inst_operands = _` (fn th => ONCE_REWRITE_TAC [th]) >>
  (* Case split on operand count: [] vs [h] vs h::h'::t' *)
  Cases_on `inst.inst_operands` >> simp[ssa_result_equiv_def] >>
  Cases_on `t` >> simp[ssa_result_equiv_def] >>
  (* Case split on operand type: Lit, Var, Label *)
  Cases_on `h` >> simp[ssa_operand_def, ssa_result_equiv_def] >>
  (* Lit cases solved. Var cases need CASE_TAC for FLOOKUP expansion *)
  rpt (CASE_TAC >> simp[ssa_result_equiv_def]) >>
  (* Label singleton case needs jump_to_ssa_equiv *)
  irule jump_to_ssa_equiv >> simp[]
QED

(* Helper: JNZ gives ssa_result_equiv with SAME vm.
 * The condition operand is transformed, but labels are unchanged. *)
Theorem jnz_result_ssa_equiv:
  !inst inst_ssa s_orig s_ssa vm.
    ssa_state_equiv vm s_orig s_ssa /\
    inst_ssa.inst_operands = MAP (ssa_operand vm) inst.inst_operands ==>
    ssa_result_equiv vm
      (case inst.inst_operands of
         [cond_op; Label if_nonzero; Label if_zero] =>
           (case eval_operand cond_op s_orig of
              SOME cond =>
                if cond <> 0w then OK (jump_to if_nonzero s_orig)
                else OK (jump_to if_zero s_orig)
            | NONE => Error "undefined condition")
       | _ => Error "jnz requires cond and 2 labels")
      (case inst_ssa.inst_operands of
         [cond_op; Label if_nonzero; Label if_zero] =>
           (case eval_operand cond_op s_ssa of
              SOME cond =>
                if cond <> 0w then OK (jump_to if_nonzero s_ssa)
                else OK (jump_to if_zero s_ssa)
            | NONE => Error "undefined condition")
       | _ => Error "jnz requires cond and 2 labels")
Proof
  rpt strip_tac >>
  qpat_x_assum `inst_ssa.inst_operands = _` (fn th => ONCE_REWRITE_TAC [th]) >>
  (* Initial setup *)
  simp[ssa_operand_def, ssa_result_equiv_def] >>
  (* Split on inst.inst_operands: [] case closes, h::t case simplifies *)
  CASE_TAC >> simp[ssa_result_equiv_def] >> simp[] >>
  (* CASE_TAC picks eval_operand h s_orig and splits NONE/SOME *)
  CASE_TAC >> simp[ssa_operand_def, ssa_result_equiv_def] >>
  (* For both NONE and SOME cases, use eval_operand_ssa_equiv *)
  drule_all eval_operand_ssa_equiv >> strip_tac >> gvs[] >>
  (* Continue case splitting on t, then use jump_to_ssa_equiv for OK cases *)
  rpt (CASE_TAC >> simp[ssa_operand_def, ssa_result_equiv_def]) >>
  irule jump_to_ssa_equiv >> simp[]
QED

(* KEY LEMMA: Non-PHI instruction step gives ssa_result_equiv with SAME vm.
 * This is stronger than step_inst_non_phi_ssa_equiv which uses ?vm'.
 * The proof works because inst_ssa_compatible determines the output mapping
 * such that ssa_state_equiv vm is preserved after update_var.
 *
 * PROOF VERIFIED INTERACTIVELY (Dec 2025):
 * After opcode case split + simp[] (NOT gvs[AllCaseEqs()]), goals have form exec_*_result.
 * Each category proven via:
 * - Binop/unop/modop: irule exec_*_result_ssa_equiv + output/FLOOKUP case splits
 * - Load: irule mload/sload/tload_result_ssa_equiv + output/FLOOKUP case splits
 * - Store: irule mstore/sstore/tstore_result_ssa_equiv (no outputs)
 * - JMP/JNZ/ASSIGN: Use dedicated result-equivalence lemmas
 * - Halt/Revert: simp[ssa_result_equiv_def] + irule halt/revert_state_ssa_equiv
 * - Error/NOP/PHI: simp[ssa_result_equiv_def]
 *)
Theorem step_inst_result_ssa_equiv:
  !inst inst_ssa s_orig s_ssa vm.
    ssa_state_equiv vm s_orig s_ssa /\
    inst_ssa_compatible vm inst inst_ssa /\
    inst.inst_opcode <> PHI /\
    LENGTH inst.inst_outputs <= 1 ==>
    ssa_result_equiv vm
      (step_inst inst s_orig)
      (step_inst inst_ssa s_ssa)
Proof
  let
    val output_case_tac =
      Cases_on `inst.inst_outputs` >| [
        fs[inst_ssa_compatible_def],
        (Cases_on `t` >| [
           (drule_all inst_ssa_compatible_outputs_equiv >> strip_tac >> gvs[]),
           gvs[]
         ])
      ]
    val outputs_ok_tac =
      `case inst.inst_outputs of
         [] => inst_ssa.inst_outputs = []
       | [out] =>
           let ssa_out = case FLOOKUP vm out of SOME x => x | NONE => out in
           inst_ssa.inst_outputs = [ssa_out] /\
           (!v. v <> out ==> FLOOKUP vm v <> SOME ssa_out) /\
           (FLOOKUP vm ssa_out = NONE ==>
            FLOOKUP vm out = NONE \/ FLOOKUP vm out = SOME out)
       | _ => T` by output_case_tac
    fun result4_forward lemma =
      `inst_ssa.inst_operands = MAP (ssa_operand vm) inst.inst_operands` by
        fs[inst_ssa_compatible_def] >>
      outputs_ok_tac >>
      irule lemma >>
      conj_tac >- fs[] >>
      conj_tac >- fs[] >>
      conj_tac >- fs[] >>
      fs[] >> NO_TAC
    fun result2_forward lemma =
      irule lemma >>
      conj_tac >- fs[] >>
      fs[inst_ssa_compatible_def] >> NO_TAC
    fun result3_forward lemma =
      irule lemma >>
      conj_tac >- fs[] >>
      conj_tac >- fs[] >>
      fs[] >> NO_TAC
    val binop_tac = result4_forward exec_binop_result_ssa_equiv
    val unop_tac = result4_forward exec_unop_result_ssa_equiv
    val modop_tac = result4_forward exec_modop_result_ssa_equiv
    val mload_tac = result4_forward mload_result_ssa_equiv
    val sload_tac = result4_forward sload_result_ssa_equiv
    val tload_tac = result4_forward tload_result_ssa_equiv
    val load_tac = FIRST [mload_tac, sload_tac, tload_tac]
    val store_tac =
      `inst_ssa.inst_operands = MAP (ssa_operand vm) inst.inst_operands` by
        fs[inst_ssa_compatible_def] >>
      simp[mstore_result_ssa_equiv, sstore_result_ssa_equiv,
           tstore_result_ssa_equiv] >> NO_TAC
    val assert_tac =
      `inst_ssa.inst_operands = MAP (ssa_operand vm) inst.inst_operands` by
        fs[inst_ssa_compatible_def] >>
      qpat_x_assum `inst_ssa.inst_operands = _` (fn th => ONCE_REWRITE_TAC [th]) >>
      Cases_on `inst.inst_operands` >> fs[ssa_result_equiv_def] >>
      Cases_on `t` >> fs[ssa_result_equiv_def] >>
      `eval_operand h s_orig = eval_operand (ssa_operand vm h) s_ssa` by
        (irule eval_operand_ssa_equiv >> simp[]) >>
      Cases_on `eval_operand (ssa_operand vm h) s_ssa` >> fs[ssa_result_equiv_def] >> gvs[] >>
      Cases_on `x = 0w` >> gvs[ssa_result_equiv_def] >>
      irule revert_state_ssa_equiv >> simp[] >> NO_TAC
    val assert_unreachable_tac =
      `inst_ssa.inst_operands = MAP (ssa_operand vm) inst.inst_operands` by
        fs[inst_ssa_compatible_def] >>
      qpat_x_assum `inst_ssa.inst_operands = _` (fn th => ONCE_REWRITE_TAC [th]) >>
      Cases_on `inst.inst_operands` >> fs[ssa_result_equiv_def] >>
      Cases_on `t` >> fs[ssa_result_equiv_def] >>
      `eval_operand h s_orig = eval_operand (ssa_operand vm h) s_ssa` by
        (irule eval_operand_ssa_equiv >> simp[]) >>
      Cases_on `eval_operand (ssa_operand vm h) s_ssa` >> fs[ssa_result_equiv_def] >> gvs[] >>
      Cases_on `x <> 0w` >> gvs[ssa_result_equiv_def] >>
      irule halt_state_ssa_equiv >> simp[] >> NO_TAC
    val blockhash_tac = result4_forward blockhash_result_ssa_equiv
    val balance_tac = result4_forward balance_result_ssa_equiv
    val calldataload_tac = result4_forward calldataload_result_ssa_equiv
    val sha3_tac = result3_forward sha3_result_ssa_equiv
    val sha3_64_tac = result3_forward sha3_64_result_ssa_equiv
    val calldatacopy_tac =
      `inst_ssa.inst_operands = MAP (ssa_operand vm) inst.inst_operands` by
        fs[inst_ssa_compatible_def] >>
      simp[calldatacopy_result_ssa_equiv] >> NO_TAC
    val returndatacopy_tac =
      `inst_ssa.inst_operands = MAP (ssa_operand vm) inst.inst_operands` by
        fs[inst_ssa_compatible_def] >>
      simp[returndatacopy_result_ssa_equiv] >> NO_TAC
    (* JMP/JNZ: unfold operand mapping and re-run the lemma proof directly. *)
    val jmp_tac =
      fs[inst_ssa_compatible_def] >>
      Cases_on `inst.inst_operands` >> simp[ssa_result_equiv_def] >>
      Cases_on `t` >> simp[ssa_result_equiv_def] >>
      Cases_on `h` >> simp[ssa_operand_def, ssa_result_equiv_def] >>
      rpt (CASE_TAC >> simp[ssa_result_equiv_def]) >>
      irule jump_to_ssa_equiv >> simp[] >> NO_TAC
    val jnz_tac =
      fs[inst_ssa_compatible_def] >>
      simp[ssa_operand_def, ssa_result_equiv_def] >>
      CASE_TAC >> simp[ssa_result_equiv_def] >> simp[] >>
      CASE_TAC >> simp[ssa_operand_def, ssa_result_equiv_def] >>
      drule_all eval_operand_ssa_equiv >> strip_tac >> gvs[] >>
      rpt (CASE_TAC >> simp[ssa_operand_def, ssa_result_equiv_def]) >>
      irule jump_to_ssa_equiv >> simp[] >> NO_TAC
    val assign_tac = result4_forward assign_result_ssa_equiv
    (* Output-only ops: use value equality under ssa_state_equiv. *)
    val state_out_tac =
      irule single_output_result_ssa_equiv >>
      fs[inst_ssa_compatible_def, ssa_state_equiv_def] >> NO_TAC
    (* NOP: OK states are equivalent under the same vm. *)
    val nop_tac = simp[ssa_result_equiv_def] >> NO_TAC
    (* Halt/Revert: Goal is ssa_result_equiv vm (Halt ...) (Halt ...).
     * First expand ssa_result_equiv_def to get ssa_state_equiv goal,
     * then apply halt/revert_state_ssa_equiv. *)
    val halt_tac = simp[ssa_result_equiv_def] >> irule halt_state_ssa_equiv >> simp[] >> NO_TAC
    val revert_tac = simp[ssa_result_equiv_def] >> irule revert_state_ssa_equiv >> simp[] >> NO_TAC
    (* Error cases: ssa_result_equiv_def for Error-Error gives T *)
    val error_tac = simp[ssa_result_equiv_def]
  in
    rpt strip_tac >>
    `inst_ssa.inst_opcode = inst.inst_opcode` by fs[inst_ssa_compatible_def] >>
    Cases_on `inst.inst_opcode` >>
    simp[step_inst_def] >>
    pop_assum (fn eq => simp_tac std_ss [eq]) >>
    FIRST [
      state_out_tac,
      sha3_tac,
      sha3_64_tac,
      nop_tac,
      jmp_tac,
      jnz_tac,
      FIRST [binop_tac, unop_tac, modop_tac, load_tac, store_tac,
             assert_tac, assert_unreachable_tac, blockhash_tac, balance_tac,
             calldataload_tac, calldatacopy_tac, returndatacopy_tac,
             assign_tac,
             halt_tac, revert_tac, error_tac, all_tac]
    ]
  end
QED

(* KEY LEMMA: Non-PHI instruction step preserves SSA equivalence (single-output). *)
Theorem step_inst_non_phi_ssa_equiv:
  !inst inst_ssa s_orig s_ssa vm r_orig.
    ssa_state_equiv vm s_orig s_ssa /\
    inst_ssa_compatible vm inst inst_ssa /\
    inst.inst_opcode <> PHI /\
    LENGTH inst.inst_outputs <= 1 /\
    step_inst inst s_orig = OK r_orig ==>
    ?r_ssa vm'.
      step_inst inst_ssa s_ssa = OK r_ssa /\
      ssa_state_equiv vm' r_orig r_ssa
Proof
  rpt strip_tac >>
  `ssa_result_equiv vm (step_inst inst s_orig) (step_inst inst_ssa s_ssa)` by
    (irule step_inst_result_ssa_equiv >> simp[]) >>
  Cases_on `step_inst inst_ssa s_ssa` >| [
    (rename1 `OK r_ssa` >>
     qexists_tac `r_ssa` >> qexists_tac `vm` >> gvs[ssa_result_equiv_def]),
    gvs[ssa_result_equiv_def],
    gvs[ssa_result_equiv_def],
    gvs[ssa_result_equiv_def]
  ]
QED

(* ==========================================================================
   Block Execution Equivalence
   ========================================================================== *)

(* Helper: next_inst preserves ssa_state_equiv *)
Theorem next_inst_ssa_equiv:
  !vm s_orig s_ssa.
    ssa_state_equiv vm s_orig s_ssa ==>
    ssa_state_equiv vm (next_inst s_orig) (next_inst s_ssa)
Proof
  rw[ssa_state_equiv_def, var_map_equiv_def, next_inst_def, lookup_var_def]
QED

(* Block step preserves SSA equivalence - Result version
 *
 * PROOF SKETCH:
 * 1. Unfold step_in_block_def in both states
 * 2. Since s_orig.vs_inst_idx = s_ssa.vs_inst_idx (from ssa_state_equiv),
 *    get_instruction returns the same index in both blocks
 * 3. Use inst_ssa_compatible to establish relationship between instructions
 * 4. Apply step_inst_result_ssa_equiv (requires non-PHI assumption)
 * 5. For matching result types: ssa_result_equiv propagates
 * 6. is_terminator is the same since inst_ssa.inst_opcode = inst.inst_opcode
 * 7. For non-terminator case, next_inst preserves ssa_state_equiv
 *)
Theorem step_in_block_ssa_result_equiv:
  !fn bb bb_ssa s_orig s_ssa vm.
    ssa_state_equiv vm s_orig s_ssa /\
    LENGTH bb_ssa.bb_instructions = LENGTH bb.bb_instructions /\
    (!idx. idx < LENGTH bb.bb_instructions ==>
           inst_ssa_compatible vm
             (EL idx bb.bb_instructions)
             (EL idx bb_ssa.bb_instructions)) /\
    (!idx. idx < LENGTH bb.bb_instructions ==>
           (EL idx bb.bb_instructions).inst_opcode <> PHI) /\
    (!idx. idx < LENGTH bb.bb_instructions ==>
           LENGTH (EL idx bb.bb_instructions).inst_outputs <= 1) ==>
    ssa_result_equiv vm
      (FST (step_in_block fn bb s_orig))
      (FST (step_in_block fn bb_ssa s_ssa)) /\
    SND (step_in_block fn bb s_orig) = SND (step_in_block fn bb_ssa s_ssa)
Proof
  rpt strip_tac >>
  simp[step_in_block_def] >>
  (* Establish inst_idx equality from ssa_state_equiv *)
  `s_orig.vs_inst_idx = s_ssa.vs_inst_idx` by fs[ssa_state_equiv_def] >>
  (* Case split on get_instruction result - creates 4 subgoals *)
  Cases_on `get_instruction bb s_orig.vs_inst_idx` >> simp[] >>
  gvs[get_instruction_def] >>
  (* Now handle both NONE and SOME cases *)
  TRY (
    (* NONE case: both blocks return Error "block not terminated" *)
    `s_ssa.vs_inst_idx >= LENGTH bb_ssa.bb_instructions` by simp[] >>
    simp[ssa_result_equiv_def] >> NO_TAC
  ) >>
  (* SOME x case: x = EL s_orig.vs_inst_idx bb.bb_instructions *)
  (* gvs should have unified x with the EL expression *)
  `s_ssa.vs_inst_idx < LENGTH bb_ssa.bb_instructions` by simp[] >>
  simp[] >>
  (* Get inst_ssa_compatible, non-PHI, and LENGTH <= 1 *)
  `inst_ssa_compatible vm (EL s_ssa.vs_inst_idx bb.bb_instructions)
                          (EL s_ssa.vs_inst_idx bb_ssa.bb_instructions)`
    by (first_x_assum (qspec_then `s_ssa.vs_inst_idx` mp_tac) >> simp[]) >>
  `(EL s_ssa.vs_inst_idx bb.bb_instructions).inst_opcode <> PHI`
    by (first_x_assum (qspec_then `s_ssa.vs_inst_idx` mp_tac) >> simp[]) >>
  `LENGTH (EL s_ssa.vs_inst_idx bb.bb_instructions).inst_outputs <= 1`
    by (first_x_assum (qspec_then `s_ssa.vs_inst_idx` mp_tac) >> simp[]) >>
  (* Get opcode equality for is_terminator *)
  `(EL s_ssa.vs_inst_idx bb.bb_instructions).inst_opcode =
   (EL s_ssa.vs_inst_idx bb_ssa.bb_instructions).inst_opcode`
    by fs[inst_ssa_compatible_def] >>
  (* Apply step_inst_result_ssa_equiv *)
  `ssa_result_equiv vm
     (step_inst (EL s_ssa.vs_inst_idx bb.bb_instructions) s_orig)
     (step_inst (EL s_ssa.vs_inst_idx bb_ssa.bb_instructions) s_ssa)`
    by (irule step_inst_result_ssa_equiv >> simp[]) >>
  (* Case split on step_inst results - they must match by ssa_result_equiv *)
  Cases_on `step_inst (EL s_ssa.vs_inst_idx bb.bb_instructions) s_orig` >>
  Cases_on `step_inst (EL s_ssa.vs_inst_idx bb_ssa.bb_instructions) s_ssa` >>
  fs[ssa_result_equiv_def] >>
  (* OK-OK case: need to handle is_terminator branch *)
  TRY (
    (* For OK-OK: case split on is_terminator *)
    Cases_on `is_terminator (EL s_ssa.vs_inst_idx bb_ssa.bb_instructions).inst_opcode` >>
    simp[ssa_result_equiv_def] >>
    (* Non-terminator case needs next_inst_ssa_equiv *)
    TRY (irule next_inst_ssa_equiv >> simp[]) >>
    NO_TAC
  ) >>
  (* Contradictory cases (OK vs Halt/Revert/Error) eliminated by ssa_result_equiv_def *)
  simp[]
QED

(* TOP-LEVEL: Full block execution preserves SSA equivalence
 *
 * This is the key theorem: running equivalent blocks with equivalent states
 * produces equivalent results. Uses strong induction on remaining instructions.
 *
 * The run_block function terminates because:
 * - Each non-terminator step increments inst_idx
 * - The measure (LENGTH bb.bb_instructions - s.vs_inst_idx) decreases
 * - Terminator instructions exit immediately
 *
 * We use the same measure for induction. *)
(* NOTE: This theorem is correct but the proof is complex due to the need
 * to carry bb_ssa through the induction while inducting on bb/s_orig.
 * The key insight is that step_in_block_ssa_result_equiv gives us:
 * 1. ssa_result_equiv for the step results
 * 2. SND equality (is_terminator flag)
 * Then for OK-OK case:
 * - vs_halted is equal (from ssa_state_equiv)
 * - is_terminator is equal (SND equality)
 * - For recursive case: apply IH with measure (LENGTH - inst_idx) decreasing
 *   because step_in_block increments inst_idx via next_inst for non-terminators *)
(* Proof strategy: Use recInduct on run_block for the block we're proving
 * ssa_result_equiv about. The IH gives us the result for recursive calls. *)
Theorem run_block_ssa_equiv:
  !fn bb s_orig bb_ssa s_ssa vm.
    ssa_state_equiv vm s_orig s_ssa /\
    LENGTH bb_ssa.bb_instructions = LENGTH bb.bb_instructions /\
    (!idx. idx < LENGTH bb.bb_instructions ==>
           inst_ssa_compatible vm
             (EL idx bb.bb_instructions)
             (EL idx bb_ssa.bb_instructions)) /\
    (!idx. idx < LENGTH bb.bb_instructions ==>
           (EL idx bb.bb_instructions).inst_opcode <> PHI) /\
    (!idx. idx < LENGTH bb.bb_instructions ==>
           LENGTH (EL idx bb.bb_instructions).inst_outputs <= 1) ==>
    ssa_result_equiv vm (run_block fn bb s_orig) (run_block fn bb_ssa s_ssa)
Proof
  recInduct run_block_ind >>
  rpt gen_tac >> strip_tac >> rpt gen_tac >> strip_tac >>
  simp[Once run_block_def] >>
  Cases_on `step_in_block fn bb s` >>
  Cases_on `q` >> gvs[] >| [
    (* OK case *)
    qspecl_then [`fn`, `bb`, `bb_ssa`, `s`, `s_ssa`, `vm`]
      mp_tac step_in_block_ssa_result_equiv >> simp[] >> strip_tac >>
    simp[Once run_block_def] >>
    Cases_on `step_in_block fn bb_ssa s_ssa` >> gvs[ssa_result_equiv_def] >>
    Cases_on `q` >> gvs[ssa_result_equiv_def] >>
    `v.vs_halted = v'.vs_halted` by fs[ssa_state_equiv_def] >>
    Cases_on `v.vs_halted` >> gvs[ssa_result_equiv_def] >-
    (* vs_halted = T: halted case, close with run_block unfolding *)
    simp[Once run_block_def, ssa_result_equiv_def] >>
    (* vs_halted = F: continue with terminator check *)
    Cases_on `r` >> gvs[ssa_result_equiv_def] >-
    (* r = T: terminator, close with run_block unfolding *)
    simp[Once run_block_def, ssa_result_equiv_def] >>
    (* r = F: Non-terminator recursive case, apply IH *)
    simp[] >>
    CONV_TAC (RAND_CONV (ONCE_REWRITE_CONV [run_block_def])) >>
    simp[] >>
    CONV_TAC (RATOR_CONV (RAND_CONV (ONCE_REWRITE_CONV [GSYM run_block_def]))) >>
    first_assum irule >> simp[]
    ,
    (* Halt case *)
    qspecl_then [`fn`, `bb`, `bb_ssa`, `s`, `s_ssa`, `vm`]
      mp_tac step_in_block_ssa_result_equiv >> simp[] >> strip_tac >>
    simp[Once run_block_def] >>
    Cases_on `step_in_block fn bb_ssa s_ssa` >> gvs[ssa_result_equiv_def] >>
    Cases_on `q` >> gvs[ssa_result_equiv_def]
    ,
    (* Revert case *)
    qspecl_then [`fn`, `bb`, `bb_ssa`, `s`, `s_ssa`, `vm`]
      mp_tac step_in_block_ssa_result_equiv >> simp[] >> strip_tac >>
    simp[Once run_block_def] >>
    Cases_on `step_in_block fn bb_ssa s_ssa` >> gvs[ssa_result_equiv_def] >>
    Cases_on `q` >> gvs[ssa_result_equiv_def]
    ,
    (* Error case *)
    qspecl_then [`fn`, `bb`, `bb_ssa`, `s`, `s_ssa`, `vm`]
      mp_tac step_in_block_ssa_result_equiv >> simp[] >> strip_tac >>
    simp[Once run_block_def] >>
    Cases_on `step_in_block fn bb_ssa s_ssa` >> gvs[ssa_result_equiv_def] >>
    Cases_on `q` >> gvs[ssa_result_equiv_def]
  ]
QED
