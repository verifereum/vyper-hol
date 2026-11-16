(* Same-endpoint successful-child restoration only. No child execution or
   semantic applicability is derived here. The input success conjunction is
   exactly C's result (abiValidAllocatedJoint), with child start en, end
   child_end, destination d+vo and size type_memory_bytes ce ty. Setup facts
   are the successful MemberSetup/ChildReady interface at u,G1,tn1.
   Compiler equations remain actual setup/child/tail equations; scratch sets
   are never replaced by arbitrary sets.

   Apply the exposed phases separately (each stays within ordinary tactic
   limits). The validation executes MemberSetup/ChildReady from incoming
   parent invariants, then conditions on C at its returned endpoint. Parent
   pos/hi cleanliness is needed only BEFORE setup; setup_clean transports it
   using the actual setup's old-ghost preservation. No independent outgoing
   preservation facts may be assumed. The temporary subject-named check is
   removed before ML-only publication; its source and build are persisted in
   the component dossier. *)
structure abiDecodeJointRejectChildRestoreLib =
struct
open HolKernel boolLib bossLib
open abiDecoderMemberConsTheory abiDecoderContractTheory
     abiMalformedRecursiveInterfaceTheory abiMalformedMemberSetupTheory
     abiValidAllocatedContractTheory abiDecoderReentryTheory
     decoderGhostFramePtrTheory exprLoweringPropsTheory
     bodyPtrDefsTheory ptrDisciplineTheory venomStateTheory listTheory
     loweringStateRelDefsTheory

val compiler_bounds =
  `abi_decode_source_opcode MLOAD` by simp[abi_decode_source_opcode_def] >>
  drule_all abi_decoder_member_cons_code >> strip_tac >>
  `abi_malformed_scratch_sites en child_end func SUBSET
     abi_malformed_scratch_sites st final func /\
   abi_malformed_scratch_sites child_end final func SUBSET
     abi_malformed_scratch_sites st final func` by
    (conj_tac >> irule abi_malformed_scratch_sites_nested >> simp[] >> decide_tac) >>
  `local_ptrs_reserved cenv child_end` by
    (irule local_ptrs_reserved_next_var >> qexists_tac `st` >>
     fs[abi_malformed_entry_def] >> decide_tac);

(* MemberSetup preserves all old operand ghosts, so the original parent
   position (not merely the freshly computed child position) stays clean. *)
val setup_clean =
  `(!x. pos = Var x ==> not_fresh_at st x) /\
   (!x. hi = Var x ==> not_fresh_at st x)` by
    (Cases_on `pos` >> Cases_on `hi` >>
     fs[abi_malformed_entry_def, EVERY_DEF, abi_decoder_operand_live_def,
        abi_decoder_older_vars_def, not_fresh_at_def]) >>
  `op_prov G1 pos = NONE /\ op_taint tn1 pos = {} /\
   op_prov G1 hi = NONE /\ op_taint tn1 hi = {}` by
    (Cases_on `pos` >> Cases_on `hi` >>
     fs[op_prov_def, op_taint_def] >> metis_tac[]);

val resources =
  qhdtm_assum `abi_valid_allocated_post`
    (strip_assume_tac o PURE_REWRITE_RULE [abi_valid_allocated_post_def]) >>
  `abi_malformed_resource_post ctx func cenv cx es st.cs_next_var
    (abi_malformed_scratch_sites st final func) dstid u v` by
    (irule abi_malformed_resource_weaken >>
     qexistsl_tac [`en.cs_next_var`, `abi_malformed_scratch_sites en child_end func`] >>
     simp[]) >>
  `abi_malformed_resource_post ctx func cenv cx es st.cs_next_var
    (abi_malformed_scratch_sites st final func) dstid s v` by
    (irule abi_malformed_resource_trans >> qexists_tac `u` >> simp[]);

val reentry =
  `abi_malformed_entry H ctx func cenv cx es child_end
    (abi_malformed_scratch_sites child_end final func) dstid live
    (Var source) hi pos (Var output) B L xs p d outsz v` by
    (irule abi_malformed_aggregate_reentry >> simp[] >>
     qexistsl_tac [`s`, `abi_malformed_scratch_sites st final func`, `st`] >>
     simp[] >> decide_tac);

val parent_live =
  `abi_decoder_operand_live en.cs_next_var (Var output) /\
   abi_decoder_operand_live en.cs_next_var pos /\
   abi_decoder_operand_live en.cs_next_var hi` by
    (fs[abi_malformed_entry_def, EVERY_DEF] >>
     metis_tac[abi_decoder_operand_live_mono]);

val coverage =
  `lookup_var output s = SOME (n2w d) /\
   lookup_var output v = SOME (n2w d) /\
   abi_decoder_operand_live st.cs_next_var (Var output)` by
    fs[abi_malformed_entry_def, EVERY_DEF, eval_operand_def] >>
  `lookup_var output u = SOME (n2w d)` by
    (qpat_assum `abi_malformed_resource_post _ _ _ _ _ st.cs_next_var _ _ s u`
       (mp_tac o cj 6 o PURE_REWRITE_RULE [abi_malformed_resource_post_def]) >>
     disch_then (qspecl_then [`Var output`, `n2w d`] mp_tac) >>
     simp[eval_operand_def]) >>
  `FLOOKUP G2 output = FLOOKUP G1 output /\
   op_taint tn2 (Var output) = op_taint tn1 (Var output)` by
    (qpat_assum `!x. abi_decoder_operand_live en.cs_next_var (Var x) ==> _`
       (qspec_then `output` mp_tac) >> simp[]) >>
  `ptr_covers G2 tn2 output v outsz` by
    (irule ptr_covers_frame >> qexistsl_tac [`G1`, `u`, `tn1`] >> simp[]);

val clean =
  `op_prov G2 pos = NONE /\ op_taint tn2 pos = {} /\
   op_prov G2 hi = NONE /\ op_taint tn2 hi = {}` by
    (Cases_on `pos` >> Cases_on `hi` >>
     fs[op_prov_def, op_taint_def, abi_decoder_operand_live_def] >> metis_tac[]);

end
