(*
 * Assembly → Bytecode Correctness — Theorem Statements
 *
 * Properties of asm→bytecode lowering. States that asm execution
 * produces the same result as vfmExecution$run on the assembled
 * bytecode (assemble prog).
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
 *   - code = assemble prog, parsed = parse_code thereof
 *
 * Modulo gas (asm interpreter ignores gas entirely).
 *
 * TOP-LEVEL:
 *   asm_bytecode_step_ok     — single step: AsmOK → EVM continues
 *   asm_bytecode_step_halt   — single step: AsmHalt → EVM halts
 *   asm_bytecode_step_revert — single step: AsmRevert → EVM reverts
 *   asm_bytecode_sim         — forward simulation (asm terminates ⇒ EVM matches)
 *
 * STRUCTURAL:
 *   offset_to_pc_inverse     — byte offset → asm index round-trips
 *   label_offset_consistent  — labels resolve to correct byte offsets
 *   encode_inst_length       — encode_inst produces asm_inst_size bytes
 *   encode_at                — bytes at offset match encode_inst
 *   assemble_parse_correct   — parse_code gives right opname at each position
 *)

Theory asmToBytecodeProps
Ancestors
  codegenRel

(* ===== Structural Properties ===== *)

(* build_offset_to_pc is left-inverse of asm_pc_to_offset at
   instruction boundaries: byte_offset → asm_index round-trips.
   Requires positive instruction size at pc so later entries don't
   overwrite (AsmDataHeader has size 0 but is never executed). *)
Theorem offset_to_pc_inverse:
  ∀prog pc.
    pc < LENGTH prog ∧
    0 < asm_inst_size (EL pc prog) ⇒
    FLOOKUP (build_offset_to_pc prog) (asm_pc_to_offset prog pc) =
      SOME pc
Proof
  cheat
QED

(* compute_label_offsets agrees with asm_pc_to_offset for labels:
   the byte offset assigned to a label matches its position.
   Requires the label name is unique after position i
   (no later AsmLabel or AsmDataHeader with the same name). *)
Theorem label_offset_consistent:
  ∀prog i lbl.
    i < LENGTH prog ∧ EL i prog = AsmLabel lbl ∧
    (∀j. i < j ∧ j < LENGTH prog ⇒
       EL j prog ≠ AsmLabel lbl ∧
       (∀l. EL j prog = AsmDataHeader l ⇒ l ≠ lbl)) ⇒
    FLOOKUP (SND (compute_label_offsets prog)) lbl =
      SOME (asm_pc_to_offset prog i)
Proof
  cheat
QED

(* encode_inst produces exactly asm_inst_size bytes when
   the encoding well-formedness conditions hold. *)
Theorem encode_inst_length:
  ∀offsets inst.
    (∀name. inst = AsmOp name ⇒ IS_SOME (evm_opcode_byte name)) ∧
    (∀lbl off. FLOOKUP offsets lbl = SOME off ⇒
       LENGTH (encode_num_bytes off) ≤ symbol_size) ∧
    (∀lbl d off. inst = AsmPushOfst lbl d ∧
       FLOOKUP offsets lbl = SOME off ⇒
       LENGTH (encode_num_bytes (off + d)) ≤ symbol_size) ⇒
    LENGTH (encode_inst offsets inst) = asm_inst_size inst
Proof
  cheat
QED

(* Bytes at offset asm_pc_to_offset in assemble prog match encode_inst.
   This bridges the asm instruction index to the EVM byte position. *)
Theorem encode_at:
  ∀prog offsets i.
    i < LENGTH prog ∧
    (_, offsets) = compute_label_offsets prog ∧
    asm_encoding_wf prog ⇒
    TAKE (asm_inst_size (EL i prog))
      (DROP (asm_pc_to_offset prog i) (assemble prog)) =
    encode_inst offsets (EL i prog)
Proof
  cheat
QED

(* parse_code on assembled bytecode yields the correct opname at each
   non-data instruction boundary. This connects the asm instruction
   to what the EVM step function will dispatch on.

   Existentially quantified over the opname: the proof must show
   which opname parse_opcode selects for each encode_inst output. *)
Theorem assemble_parse_correct:
  ∀prog i.
    asm_wf prog ∧
    i < LENGTH prog ∧
    ¬ is_data_inst (EL i prog) ⇒
    ∃op.
      FLOOKUP (parse_code 0 FEMPTY (assemble prog))
              (asm_pc_to_offset prog i) = SOME op ∧
      opcode op ≼ encode_inst (SND (compute_label_offsets prog))
                              (EL i prog)
Proof
  cheat
QED

(* ===== Step Correspondence ===== *)

(* Single step (continuation): if asm takes one step producing AsmOK,
   the EVM takes one step on the assembled bytecode reaching a related
   state. 1 asm instruction = 1 EVM instruction (both step once).

   Modulo gas: assumes sufficient gas for the EVM step. *)
Theorem asm_bytecode_step_ok:
  ∀prog as es.
    asm_wf prog ∧
    asm_evm_rel prog as es ∧
    sufficient_gas es ∧
    as.as_pc < LENGTH prog ∧
    ¬ is_data_inst (EL as.as_pc prog) ⇒
    let label_offsets = SND (compute_label_offsets prog) in
    let otp = build_offset_to_pc prog in
    let inst = EL as.as_pc prog in
    ∀as'.
      asm_step label_offsets otp inst as = AsmOK as' ⇒
      ∃es'. step es = (INL (), es') ∧
            asm_evm_rel prog as' es'
Proof
  cheat
QED

(* Single step (halt): asm produces AsmHalt ⇒ EVM finishes cleanly *)
Theorem asm_bytecode_step_halt:
  ∀prog as es.
    asm_wf prog ∧
    asm_evm_rel prog as es ∧
    sufficient_gas es ∧
    as.as_pc < LENGTH prog ∧
    ¬ is_data_inst (EL as.as_pc prog) ⇒
    let label_offsets = SND (compute_label_offsets prog) in
    let otp = build_offset_to_pc prog in
    let inst = EL as.as_pc prog in
    ∀as'.
      asm_step label_offsets otp inst as = AsmHalt as' ⇒
      ∃es'. step es = (INR NONE, es') ∧
            asm_evm_rel prog as' es'
Proof
  cheat
QED

(* Single step (revert): asm produces AsmRevert ⇒ EVM reverts *)
Theorem asm_bytecode_step_revert:
  ∀prog as es.
    asm_wf prog ∧
    asm_evm_rel prog as es ∧
    sufficient_gas es ∧
    as.as_pc < LENGTH prog ∧
    ¬ is_data_inst (EL as.as_pc prog) ⇒
    let label_offsets = SND (compute_label_offsets prog) in
    let otp = build_offset_to_pc prog in
    let inst = EL as.as_pc prog in
    ∀as'.
      asm_step label_offsets otp inst as = AsmRevert as' ⇒
      ∃es' exc. step es = (INR (SOME exc), es') ∧
                exc = Reverted ∧
                asm_evm_rel prog as' es'
Proof
  cheat
QED

(* ===== Forward Simulation ===== *)

(* If asm execution halts (via asm_steps), EVM execution of the
   assembled bytecode also halts with a corresponding result.

   Uses asm_steps (step-counted) for natural composition with
   gen_fn_simulation. Direction: asm terminates ⇒ EVM terminates.

   label_offsets and offset_to_pc are derived from prog
   (compute_label_offsets, build_offset_to_pc). They appear as
   parameters because gen_fn_simulation also parameterizes over them.

   Gas condition: sufficient_gas is necessary but not sufficient.
   The full proof requires gas sufficiency across all steps.
   Exact formulation refined during proof. *)
Theorem asm_bytecode_sim:
  ∀n prog label_offsets offset_to_pc as es.
    asm_wf prog ∧
    label_offsets = SND (compute_label_offsets prog) ∧
    offset_to_pc = build_offset_to_pc prog ∧
    asm_evm_rel prog as es ∧
    sufficient_gas es ⇒
    (* Halt: asm halts cleanly ⇒ EVM halts cleanly *)
    (∀as'. asm_steps label_offsets offset_to_pc prog n as =
             AsmHalt as' ⇒
       ∃es'. run es = SOME (INR NONE, es') ∧
             asm_evm_rel prog as' es') ∧
    (* Revert: asm reverts ⇒ EVM reverts *)
    (∀as'. asm_steps label_offsets offset_to_pc prog n as =
             AsmRevert as' ⇒
       ∃es'. run es = SOME (INR (SOME Reverted), es') ∧
             asm_evm_rel prog as' es') ∧
    (* Fault: asm faults ⇒ EVM faults (non-revert exception) *)
    (∀as'. asm_steps label_offsets offset_to_pc prog n as =
             AsmFault as' ⇒
       ∃es' exc. run es = SOME (INR (SOME exc), es') ∧
                 exc ≠ Reverted ∧
                 asm_evm_rel prog as' es')
Proof
  cheat
QED
