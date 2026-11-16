(* Proof fragments for the immutable malformed joint decoder declaration.
   Inputs are the stripped immutable antecedent and a descriptor equation.
   No theorem is declared here; abiDecodeJoint owns the public contracts. *)
structure abiDecodeJointRejectCasesLib =
struct
open HolKernel boolLib bossLib
open abiMalformedAllocatedPrimitiveJointTheory abiMalformedAllocatedBytesJointTheory
     exprSimAbiDecodePrimitiveOwnedTheory abiDecoderBytestringCasesTheory
     abiDecodePtrComplexGuardJointTheory abiDecoderComplexGuardTheory
     abiDecodePtrRejectChecksTheory abiValidAllocatedObservationsTheory
     abiDecoderComplexExecuteTheory abiDecoderContractTheory
     venomStateTheory vyperABITheory contractABITheory listTheory

val primitive_tac =
  drule_all abi_decode_scalar_source_shape >> strip_tac >>
  qpat_assum `type_memory_bytes ce ty = 32`
    (fn th => rule_assum_tac (PURE_REWRITE_RULE [th])) >>
  `bytes = TAKE 32 (DROP p xs)` by simp[] >>
  qpat_assum `bytes = TAKE 32 (DROP p xs)`
    (fn th => rule_assum_tac (PURE_REWRITE_RULE [th])) >>
  `p + 32 <= L` by fs[] >>
  drule_at (Pat `abi_malformed_entry`) abi_malformed_allocated_primitive_joint >>
  disch_then drule_all >> simp[]

val bytes_tac =
  `is_dynamic (vyper_to_abi_type env ty)` by
    (drule abi_decoder_bytestring_cases >> disch_then drule >> strip_tac >>
     gvs[vyper_to_abi_type_def, vyper_base_to_abi_type_def, is_dynamic_def]) >>
  `bytes = DROP p xs` by simp[] >>
  qpat_assum `bytes = DROP p xs`
    (fn th => rule_assum_tac (PURE_REWRITE_RULE [th])) >>
  drule_at (Pat `abi_malformed_entry`) abi_malformed_allocated_bytes_joint >>
  disch_then drule_all >> simp[]

(* Requires the actual guard compilation and Abort Revert_abort run equations.
   Observation transport is at the very same index-normalized endpoint. *)
val guard_abort_tac =
  drule_all abi_decoder_complex_guard_code >> strip_tac >>
  `EVERY (\i. abi_decoder_reentry_opcode i.inst_opcode)
     (emitted_insts st guard_end)` by fs[EVERY_MEM] >>
  drule_all abi_decode_revert_witness >> strip_tac >>
  drule_all abi_valid_allocated_revert_observations >> strip_tac >>
  drule_all abi_decode_complex_guard_abort_joint >>
  disch_then (qspec_then `PG` strip_assume_tac) >>
  qexistsl_tac [`u with vs_inst_idx := j`, `G'`, `tn'`] >> simp[]

(* On a DecComplex goal, expose the actual guard execution.  The revert
   branch closes; the not-revert branch remains for reflected recursion. *)
val complex_guard_split_tac =
  drule abi_decoder_complex_trace >> strip_tac >>
  rename1 `abi_decode_complex_head_guard pos hi _ st = ((),guard_end)` >>
  `abi_decode_source_opcode MLOAD` by simp[abi_decode_source_opcode_def] >>
  drule_all abi_decoder_complex_code >> strip_tac >>
  Cases_on `?u. run_inst_seq (emitted_insts st guard_end) s = Abort Revert_abort u`
  >- (pop_assum (qx_choose_then `u` assume_tac) >> guard_abort_tac)
end
