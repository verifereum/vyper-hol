(*
 * Assembly → Bytecode Correctness
 *
 * Proves that asm execution produces the same result as
 * vfmExecution$run on the assembled bytecode (assemble prog).
 *
 * Key insight: both use the same label offsets (compute_label_offsets).
 * The asm interpreter pushes concrete byte offsets for labels and maps
 * them back to asm indices for jumps. The EVM interpreter uses byte
 * offsets directly. At each step, stacks/memory/storage are identical.
 *
 * The bisimulation invariant is asm_evm_rel, which says:
 *   - stacks identical
 *   - memory identical
 *   - PC related by asm_pc_to_offset (sum of instruction sizes)
 *
 * Modulo gas (asm interpreter ignores gas entirely).
 *
 * TOP-LEVEL:
 *   asm_bytecode_step   — single step correspondence
 *   asm_bytecode_sim    — forward simulation (asm terminates ⇒ EVM matches)
 *   offset_to_pc_inverse — structural: byte offset → asm index inverse
 *   label_offset_consistent — labels resolve to correct byte offsets
 *)

Theory asmToBytecode
Ancestors
  codegenRel

(* ===== Well-formedness for asm programs ===== *)

(* All labels in the program are unique *)
Definition asm_labels_unique_def:
  asm_labels_unique prog ⇔
    ALL_DISTINCT (FILTER IS_SOME
      (MAP (λinst. case inst of AsmLabel l => SOME l | _ => NONE) prog))
End

(* All jump targets resolve to valid JUMPDEST instructions *)
Definition asm_jumps_valid_def:
  asm_jumps_valid prog ⇔
    let (_, offsets) = compute_label_offsets prog in
    let otp = build_offset_to_pc prog in
    ∀lbl off pc.
      FLOOKUP offsets lbl = SOME off ∧
      FLOOKUP otp off = SOME pc ∧
      pc < LENGTH prog ⇒
      (∃l. EL pc prog = AsmLabel l)
End

(* Data section is at the end and not reachable by execution *)
Definition asm_data_at_end_def:
  asm_data_at_end prog ⇔
    ∀i. i < LENGTH prog ⇒
      (case EL i prog of
         AsmDataHeader _ => ∀j. j ≥ i ∧ j < LENGTH prog ⇒
           (case EL j prog of
              AsmDataHeader _ => T | AsmDataItem _ => T
            | AsmDataLabel _ => T | _ => F)
       | _ => T)
End

Definition asm_wf_def:
  asm_wf prog ⇔
    asm_labels_unique prog ∧
    asm_jumps_valid prog ∧
    asm_data_at_end prog
End

(* ===== Step Correspondence ===== *)

(* Single step: if asm takes one step producing AsmOK, the EVM
   can take one or more steps on the assembled bytecode reaching
   a related state.

   "one or more" because a single asm instruction may correspond to
   multiple EVM bytes (e.g. PUSH2 is 3 bytes but one asm instruction).

   Modulo gas: assumes sufficient gas for each EVM step. *)
Theorem asm_bytecode_step:
  ∀prog label_offsets otp as es inst.
    asm_wf prog ∧
    (_, label_offsets) = compute_label_offsets prog ∧
    otp = build_offset_to_pc prog ∧
    asm_evm_rel prog as es ∧
    as.as_pc < LENGTH prog ∧
    inst = EL as.as_pc prog ⇒
    ∀as'.
      asm_step label_offsets otp inst as = AsmOK as' ⇒
      ∃es'. asm_evm_rel prog as' es'
      (* NOTE: es' is reachable from es via EVM steps on assemble prog.
         The full proof will connect es' to step/run, currently cheated. *)
Proof
  cheat
QED

(* ===== Forward Simulation ===== *)

(* If asm execution halts, EVM execution of the assembled bytecode
   also halts with a corresponding result.

   Direction: asm terminates ⇒ EVM terminates with matching result.
   The converse would require reasoning about gas.

   Assumes sufficient gas on the EVM side (modulo gas).
   If run_asm returns AsmError ("out of fuel" or invalid),
   no conclusion about EVM is drawn. *)
Theorem asm_bytecode_sim:
  ∀fuel prog as es.
    asm_wf prog ∧
    asm_evm_rel prog as es ⇒
    (* Halt: asm halts cleanly ⇒ EVM halts cleanly *)
    (∀as'. run_asm fuel prog as = AsmHalt as' ⇒
       ∃es'. run es = SOME (INR NONE, es') ∧
             asm_evm_rel prog as' es') ∧
    (* Revert: asm reverts ⇒ EVM reverts *)
    (∀as'. run_asm fuel prog as = AsmRevert as' ⇒
       ∃es'. run es = SOME (INR (SOME Reverted), es') ∧
             asm_evm_rel prog as' es') ∧
    (* Fault: asm faults ⇒ EVM faults (non-revert exception) *)
    (∀as'. run_asm fuel prog as = AsmFault as' ⇒
       ∃es' exc. run es = SOME (INR (SOME exc), es') ∧
                 exc ≠ Reverted ∧
                 asm_evm_rel prog as' es')
Proof
  cheat
QED

(* ===== Offset Map Properties ===== *)

(* build_offset_to_pc is left-inverse of asm_pc_to_offset at
   instruction boundaries: byte_offset → asm_index round-trips *)
Theorem offset_to_pc_inverse:
  ∀prog pc.
    pc ≤ LENGTH prog ⇒
    FLOOKUP (build_offset_to_pc prog) (asm_pc_to_offset prog pc) =
      SOME pc
Proof
  cheat
QED

(* compute_label_offsets agrees with asm_pc_to_offset for labels:
   the byte offset assigned to a label matches its position *)
Theorem label_offset_consistent:
  ∀prog i lbl.
    i < LENGTH prog ∧ EL i prog = AsmLabel lbl ⇒
    FLOOKUP (SND (compute_label_offsets prog)) lbl =
      SOME (asm_pc_to_offset prog i)
Proof
  cheat
QED
