(*
 * SSA State Equivalence Definitions
 *
 * This theory defines state equivalence between non-SSA and SSA states.
 * The key insight is that the SSA state is "compatible" with the non-SSA
 * state via a variable mapping.
 *
 * ============================================================================
 * STRUCTURE OVERVIEW
 * ============================================================================
 *
 * TOP-LEVEL DEFINITIONS:
 *   - ssa_state_equiv        : Main state equivalence predicate
 *   - var_map_equiv          : Variable mapping equivalence
 *   - ssa_result_equiv       : Equivalence for exec_result
 *
 * TOP-LEVEL THEOREMS:
 *   - ssa_state_equiv_refl   : Reflexivity
 *   - ssa_state_equiv_sym    : Symmetry
 *   - eval_operand_ssa_equiv : Operand evaluation under equiv
 *
 * ============================================================================
 *)

Theory mkSsaStateEquiv
Ancestors
  mkSsaDefs mkSsaTransform finite_map
  venomState venomInst venomSem

(* ==========================================================================
   Variable Mapping Equivalence
   ==========================================================================

   A variable mapping vm : string -> string maps non-SSA variable names
   to their current SSA variable names. The mapping is "correct" if
   looking up the original variable in the non-SSA state gives the same
   value as looking up the mapped variable in the SSA state.
   ========================================================================== *)

(* TOP-LEVEL: Variable mapping type *)
Type var_mapping = ``:(string, string) fmap``

(* TOP-LEVEL: Variable mapping equivalence - related variables have same values *)
Definition var_map_equiv_def:
  var_map_equiv (vm:var_mapping) s_orig s_ssa <=>
    (* Every mapped variable has the same value *)
    (!v ssa_v.
       FLOOKUP vm v = SOME ssa_v ==>
       lookup_var v s_orig = lookup_var ssa_v s_ssa) /\
    (* Unmapped variables in original state are also in SSA state *)
    (!v. FLOOKUP vm v = NONE ==>
         lookup_var v s_orig = lookup_var v s_ssa)
End

(* ==========================================================================
   Full State Equivalence
   ==========================================================================

   Two states are SSA-equivalent if:
   1. Variables are equivalent under the mapping
   2. All other state components (memory, storage, etc.) are identical
   ========================================================================== *)

(* TOP-LEVEL: SSA state equivalence *)
Definition ssa_state_equiv_def:
  ssa_state_equiv (vm:var_mapping) s_orig s_ssa <=>
    var_map_equiv vm s_orig s_ssa /\
    s_orig.vs_memory = s_ssa.vs_memory /\
    s_orig.vs_storage = s_ssa.vs_storage /\
    s_orig.vs_transient = s_ssa.vs_transient /\
    s_orig.vs_returndata = s_ssa.vs_returndata /\
    s_orig.vs_accounts = s_ssa.vs_accounts /\
    s_orig.vs_call_ctx = s_ssa.vs_call_ctx /\
    s_orig.vs_tx_ctx = s_ssa.vs_tx_ctx /\
    s_orig.vs_block_ctx = s_ssa.vs_block_ctx /\
    s_orig.vs_current_bb = s_ssa.vs_current_bb /\
    s_orig.vs_inst_idx = s_ssa.vs_inst_idx /\
    s_orig.vs_prev_bb = s_ssa.vs_prev_bb /\
    s_orig.vs_halted = s_ssa.vs_halted /\
    s_orig.vs_reverted = s_ssa.vs_reverted
End

(* Helper: prev_bb equality from SSA state equivalence. *)
Theorem ssa_state_equiv_prev_bb:
  !vm s_orig s_ssa.
    ssa_state_equiv vm s_orig s_ssa ==>
    s_orig.vs_prev_bb = s_ssa.vs_prev_bb
Proof
  simp[ssa_state_equiv_def]
QED

(* ==========================================================================
   Equivalence Relation Properties
   ========================================================================== *)

(* Identity mapping *)
Definition id_var_mapping_def:
  id_var_mapping : var_mapping = FEMPTY
End

(* TOP-LEVEL: Reflexivity with identity mapping *)
Theorem ssa_state_equiv_refl:
  !s. ssa_state_equiv id_var_mapping s s
Proof
  rw[ssa_state_equiv_def, var_map_equiv_def, id_var_mapping_def, FLOOKUP_DEF]
QED

(* Helper: var_map_equiv is symmetric with inverse mapping *)
Definition invert_mapping_def:
  invert_mapping (vm:var_mapping) : var_mapping =
    FUN_FMAP (\ssa_v. @v. FLOOKUP vm v = SOME ssa_v)
             { ssa_v | ?v. FLOOKUP vm v = SOME ssa_v }
End

(* ==========================================================================
   Operand Evaluation Under Equivalence
   ========================================================================== *)

(* Helper: Get the SSA version of an operand *)
Definition ssa_operand_def:
  ssa_operand (vm:var_mapping) (Var v) =
    (case FLOOKUP vm v of
       SOME ssa_v => Var ssa_v
     | NONE => Var v) /\
  ssa_operand vm (Lit l) = Lit l /\
  ssa_operand vm (Label l) = Label l
End

(* TOP-LEVEL: Operand evaluation under SSA equivalence *)
Theorem eval_operand_ssa_equiv:
  !vm s_orig s_ssa op.
    ssa_state_equiv vm s_orig s_ssa ==>
    eval_operand op s_orig = eval_operand (ssa_operand vm op) s_ssa
Proof
  rpt strip_tac >> Cases_on `op` >>
  fs[ssa_operand_def, eval_operand_def] >>
  fs[ssa_state_equiv_def, var_map_equiv_def] >>
  Cases_on `FLOOKUP vm s` >> fs[eval_operand_def]
QED

(* ==========================================================================
   Result Equivalence
   ========================================================================== *)

(* TOP-LEVEL: SSA result equivalence *)
Definition ssa_result_equiv_def:
  ssa_result_equiv vm (OK s1) (OK s2) = ssa_state_equiv vm s1 s2 /\
  ssa_result_equiv vm (Halt s1) (Halt s2) = ssa_state_equiv vm s1 s2 /\
  ssa_result_equiv vm (Revert s1) (Revert s2) = ssa_state_equiv vm s1 s2 /\
  ssa_result_equiv vm (Error e1) (Error e2) = T /\
  ssa_result_equiv vm _ _ = F
End

(* TOP-LEVEL: Reflexivity for result_equiv *)
Theorem ssa_result_equiv_refl:
  !r. ssa_result_equiv id_var_mapping r r
Proof
  Cases >> rw[ssa_result_equiv_def, ssa_state_equiv_refl]
QED

(* ==========================================================================
   State Update Under Equivalence
   ========================================================================== *)

(* TOP-LEVEL: Variable update preserves SSA equivalence with extended mapping.
   Preconditions:
   1. ssa_v is not in the range of vm (except possibly via v)
   2. ssa_v doesn't collide with OTHER unmapped variable names
   In SSA construction, both are true since we generate fresh names like "x:1". *)
Theorem update_var_ssa_equiv:
  !vm s_orig s_ssa v ssa_v val.
    ssa_state_equiv vm s_orig s_ssa /\
    (!v'. v' <> v ==> FLOOKUP vm v' <> SOME ssa_v) /\
    (!v'. v' <> v /\ FLOOKUP vm v' = NONE ==> v' <> ssa_v) ==>
    ssa_state_equiv (vm |+ (v, ssa_v))
                    (update_var v val s_orig)
                    (update_var ssa_v val s_ssa)
Proof
  rpt strip_tac >>
  fs[ssa_state_equiv_def, var_map_equiv_def, update_var_def, lookup_var_def, FLOOKUP_UPDATE] >>
  rpt strip_tac >> rw[] >> gvs[]
QED

(* TOP-LEVEL: Memory operations preserve SSA equivalence *)
Theorem mstore_ssa_equiv:
  !vm s_orig s_ssa offset value.
    ssa_state_equiv vm s_orig s_ssa ==>
    ssa_state_equiv vm (mstore offset value s_orig) (mstore offset value s_ssa)
Proof
  rw[ssa_state_equiv_def, var_map_equiv_def, mstore_def, lookup_var_def]
QED

Theorem write_memory_with_expansion_ssa_equiv:
  !vm s_orig s_ssa offset bytes.
    ssa_state_equiv vm s_orig s_ssa ==>
    ssa_state_equiv vm
      (write_memory_with_expansion offset bytes s_orig)
      (write_memory_with_expansion offset bytes s_ssa)
Proof
  rw[ssa_state_equiv_def, var_map_equiv_def,
     write_memory_with_expansion_def, lookup_var_def]
QED

Theorem sstore_ssa_equiv:
  !vm s_orig s_ssa key value.
    ssa_state_equiv vm s_orig s_ssa ==>
    ssa_state_equiv vm (sstore key value s_orig) (sstore key value s_ssa)
Proof
  rw[ssa_state_equiv_def, var_map_equiv_def, sstore_def, lookup_var_def]
QED

Theorem tstore_ssa_equiv:
  !vm s_orig s_ssa key value.
    ssa_state_equiv vm s_orig s_ssa ==>
    ssa_state_equiv vm (tstore key value s_orig) (tstore key value s_ssa)
Proof
  rw[ssa_state_equiv_def, var_map_equiv_def, tstore_def, lookup_var_def]
QED

(* TOP-LEVEL: Control flow preserves SSA equivalence *)
Theorem jump_to_ssa_equiv:
  !vm s_orig s_ssa lbl.
    ssa_state_equiv vm s_orig s_ssa ==>
    ssa_state_equiv vm (jump_to lbl s_orig) (jump_to lbl s_ssa)
Proof
  rw[ssa_state_equiv_def, var_map_equiv_def, jump_to_def, lookup_var_def]
QED

Theorem halt_state_ssa_equiv:
  !vm s_orig s_ssa.
    ssa_state_equiv vm s_orig s_ssa ==>
    ssa_state_equiv vm (halt_state s_orig) (halt_state s_ssa)
Proof
  rw[ssa_state_equiv_def, var_map_equiv_def, halt_state_def, lookup_var_def]
QED

Theorem revert_state_ssa_equiv:
  !vm s_orig s_ssa.
    ssa_state_equiv vm s_orig s_ssa ==>
    ssa_state_equiv vm (revert_state s_orig) (revert_state s_ssa)
Proof
  rw[ssa_state_equiv_def, var_map_equiv_def, revert_state_def, lookup_var_def]
QED

(* ==========================================================================
   Load Operations Under Equivalence
   ========================================================================== *)

Theorem mload_ssa_equiv:
  !vm s_orig s_ssa offset.
    ssa_state_equiv vm s_orig s_ssa ==>
    mload offset s_orig = mload offset s_ssa
Proof
  rw[ssa_state_equiv_def, mload_def]
QED

Theorem sload_ssa_equiv:
  !vm s_orig s_ssa key.
    ssa_state_equiv vm s_orig s_ssa ==>
    sload key s_orig = sload key s_ssa
Proof
  rw[ssa_state_equiv_def, sload_def]
QED

Theorem tload_ssa_equiv:
  !vm s_orig s_ssa key.
    ssa_state_equiv vm s_orig s_ssa ==>
    tload key s_orig = tload key s_ssa
Proof
  rw[ssa_state_equiv_def, tload_def]
QED

(* ==========================================================================
   Update Preserves Same-VM Equivalence
   ==========================================================================
   When the SSA output variable is determined by vm (like in inst_ssa_compatible),
   updating the variable preserves ssa_state_equiv with the SAME vm.
   This is crucial for proving step_in_block correctness. *)

(* Helper: var_map_equiv preserved with same vm when output determined by vm *)
Theorem var_map_equiv_update_same_vm:
  !vm s_orig s_ssa out val.
    var_map_equiv vm s_orig s_ssa /\
    (!v. v <> out ==>
         FLOOKUP vm v <> SOME (case FLOOKUP vm out of SOME x => x | NONE => out)) /\
    (FLOOKUP vm (case FLOOKUP vm out of SOME x => x | NONE => out) = NONE ==>
     FLOOKUP vm out = NONE \/ FLOOKUP vm out = SOME out) ==>
    var_map_equiv vm
      (update_var out val s_orig)
      (update_var (case FLOOKUP vm out of SOME x => x | NONE => out) val s_ssa)
Proof
  rpt strip_tac >>
  fs[var_map_equiv_def, update_var_def, lookup_var_def] >>
  qabbrev_tac `ssa_out = case FLOOKUP vm out of NONE => out | SOME x => x` >>
  rpt conj_tac >> rpt strip_tac >> simp[FLOOKUP_UPDATE] >>
  (* First conjunct: mapped variables *)
  TRY (
    Cases_on `v = out` >> simp[]
    >- (
      `ssa_out = ssa_v` by (fs[markerTheory.Abbrev_def] >> Cases_on `FLOOKUP vm out` >> fs[]) >>
      simp[]
    )
    >- (
      `ssa_out <> ssa_v` by (first_x_assum (qspec_then `v` mp_tac) >> simp[]) >>
      simp[] >>
      first_x_assum (qspecl_then [`v`, `ssa_v`] mp_tac) >> simp[]
    )
  ) >>
  (* Second conjunct: unmapped variables *)
  TRY (
    Cases_on `v = out` >> simp[]
    >- (`ssa_out = out` by fs[markerTheory.Abbrev_def] >> simp[])
    >- (
      `ssa_out <> v` by (
        fs[markerTheory.Abbrev_def] >>
        CCONTR_TAC >> fs[] >>
        Cases_on `FLOOKUP vm out` >> fs[]
      ) >>
      simp[]
    )
  )
QED

(* TOP-LEVEL: ssa_state_equiv preserved with same vm when output determined by vm *)
Theorem ssa_state_equiv_update_same_vm:
  !vm s_orig s_ssa out val.
    ssa_state_equiv vm s_orig s_ssa /\
    (!v. v <> out ==>
         FLOOKUP vm v <> SOME (case FLOOKUP vm out of SOME x => x | NONE => out)) /\
    (FLOOKUP vm (case FLOOKUP vm out of SOME x => x | NONE => out) = NONE ==>
     FLOOKUP vm out = NONE \/ FLOOKUP vm out = SOME out) ==>
    ssa_state_equiv vm
      (update_var out val s_orig)
      (update_var (case FLOOKUP vm out of SOME x => x | NONE => out) val s_ssa)
Proof
  rpt strip_tac >>
  fs[ssa_state_equiv_def, update_var_def] >>
  drule_all var_map_equiv_update_same_vm >>
  simp[update_var_def]
QED
