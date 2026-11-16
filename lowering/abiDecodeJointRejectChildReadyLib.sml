(* Operational preparation only, at the actual member-setup endpoint.
   No semantic child IH or parent restoration after a child is proved here.
   Invoke after MemberSetupLib.success, while the raw run to t is retained.
   Additional incoming facts: fn_inst_ids_distinct func, alloca_history func s,
   lo <= s.vs_alloca_next, op_prov G hi = NONE, op_taint tn hi = {}.
   The setup inputs are those documented in MemberSetupLib (arbitrary ao,vo).
   normalize with MemberSetupLib.normalized_success only AFTER readiness. *)
structure abiDecodeJointRejectChildReadyLib =
struct
open HolKernel boolLib bossLib
open abiDecoderMemberCodeTheory abiDecoderContractTheory
     entryDecoderHistoryFrameTheory abiMalformedRecursiveInterfaceTheory
     decoderGhostFramePtrTheory stateFrameTheory venomStateTheory
     bodyPtrDefsTheory abiDecoderReentryTheory exprLoweringPropsTheory
     loweringStateRelDefsTheory ptrDisciplineTheory

val readiness =
  `abi_decode_source_opcode MLOAD` by simp[abi_decode_source_opcode_def] >>
  drule_all abi_decode_member_setup_shape >> strip_tac >>
  `EVERY (\i. ~is_terminator i.inst_opcode) (emitted_insts st en)` by
    fs[listTheory.EVERY_CONJ] >>
  `alloca_history func (t with vs_inst_idx := LENGTH en.cs_current_insts)` by
    (irule entry_straight_line_alloca_history >> metis_tac[]) >>
  `lo <= t.vs_alloca_next /\ ~t.vs_halted /\
   t.vs_current_bb = en.cs_current_bb` by
    fs[state_frame_def, venom_state_component_equality] >>
  `(!x. hi = Var x ==> not_fresh_at st x)` by
    (Cases_on `hi` >>
     fs[abi_malformed_entry_def, listTheory.EVERY_DEF,
        abi_decoder_operand_live_def, abi_decoder_older_vars_def, not_fresh_at_def]) >>
  `op_prov G' hi = NONE /\ op_taint tn' hi = {}` by
    (Cases_on `hi` >> fs[op_prov_def, op_taint_def] >> metis_tac[]) >>
  `ptr_covers G' tn' output t outsz` by
    (irule ptr_covers_frame >> qexistsl_tac [`G`, `s`, `tn`] >> metis_tac[]);

val one_step =
  strip_tac >> abiDecodeJointRejectMemberSetupLib.inputs >>
  abiDecodeJointRejectMemberSetupLib.split
  >- (disj1_tac >> abiDecodeJointRejectMemberSetupLib.abort) >>
  disj2_tac >> abiDecodeJointRejectMemberSetupLib.success >>
  readiness >> abiDecodeJointRejectMemberSetupLib.source_window >>
  abiDecodeJointRejectMemberSetupLib.prepend_success >>
  abiDecodeJointRejectMemberSetupLib.normalized_success;
end
