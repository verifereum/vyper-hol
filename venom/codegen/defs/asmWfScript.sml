(*
 * Assembly Program Well-formedness
 *
 * Predicates ensuring an asm_inst program is suitable for execution
 * and assembly to EVM bytecode.
 *
 * TOP-LEVEL:
 *   asm_wf             — combined well-formedness predicate
 *   asm_labels_unique   — all labels are distinct
 *   asm_jumps_valid     — jump targets resolve to JUMPDEST
 *   asm_data_at_end     — data section unreachable
 *   is_data_inst        — classify data-section instructions
 *)

Theory asmWf
Ancestors
  symbolResolve

(* ===== Data Instruction Classification ===== *)

Definition is_data_inst_def:
  is_data_inst (AsmDataHeader _) = T ∧
  is_data_inst (AsmDataItem _) = T ∧
  is_data_inst (AsmDataLabel _) = T ∧
  is_data_inst _ = F
End

(* ===== Label Uniqueness ===== *)

(* All labels in the program are unique *)
Definition asm_labels_unique_def:
  asm_labels_unique prog ⇔
    ALL_DISTINCT (FILTER IS_SOME
      (MAP (λinst. case inst of AsmLabel l => SOME l | _ => NONE) prog))
End

(* ===== Jump Target Validity ===== *)

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

(* ===== Data Section Placement ===== *)

(* Data section is at the end and not reachable by execution *)
Definition asm_data_at_end_def:
  asm_data_at_end prog ⇔
    ∀i. i < LENGTH prog ⇒
      (case EL i prog of
         AsmDataHeader _ => ∀j. j ≥ i ∧ j < LENGTH prog ⇒
           is_data_inst (EL j prog)
       | _ => T)
End

(* ===== Encoding Well-formedness ===== *)

(* All opcodes encode to valid bytes and label offsets fit symbol_size *)
Definition asm_encoding_wf_def:
  asm_encoding_wf prog ⇔
    let (_, offsets) = compute_label_offsets prog in
    (∀i name. i < LENGTH prog ∧ EL i prog = AsmOp name ⇒
       IS_SOME (evm_opcode_byte name)) ∧
    (∀lbl off. FLOOKUP offsets lbl = SOME off ⇒
       LENGTH (encode_num_bytes off) ≤ symbol_size) ∧
    (∀i lbl d off. i < LENGTH prog ∧ EL i prog = AsmPushOfst lbl d ∧
       FLOOKUP offsets lbl = SOME off ⇒
       LENGTH (encode_num_bytes (off + d)) ≤ symbol_size)
End

(* ===== Combined Well-formedness ===== *)

Definition asm_wf_def:
  asm_wf prog ⇔
    asm_labels_unique prog ∧
    asm_jumps_valid prog ∧
    asm_data_at_end prog ∧
    asm_encoding_wf prog
End
