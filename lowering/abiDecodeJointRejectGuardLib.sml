(* Guard handoff fragments for the immutable malformed decoder goal. *)
structure abiDecodeJointRejectGuardLib =
struct
open HolKernel boolLib bossLib
open abiDecoderCoherenceTheory abiDecoderMemberInfosTheory
     abiMalformedBoundedContractTheory abiMalformedParentAggregateTheory
     abiDecodePtrComplexGuardJointTheory abiDecoderContractTheory
     exprLoweringTheory compileEnvTheory wordsTheory listTheory
     abiEncoderTheory vyperASTTheory vyperABITheory
open abiDecodePtrMemberFrameTheory decoderGhostFramePtrTheory
     entryDecoderHistoryFrameTheory abiDecoderReentryTheory
     abiMalformedRecursiveInterfaceTheory abiValidAllocatedComplexTheory
     abiDecoderComplexGuardTheory abiDecoderComplexHeadTheory
     exprLoweringPropsTheory localPtrsPropsTheory ghostPcTransportPtrTheory
     ptrDisciplineTheory loweringStateRelDefsTheory venomStateTheory
     abiMalformedMemberSetupTheory

val head_bound_tac =
  Cases_on `ty`
  >~ [`abi_decoder_coherent ce env sf (TupleT _) tv`]
  >- (gvs[abi_decoder_coherent_tuple_iff, abi_decoder_tuple_infos] >>
      drule abi_decoder_member_infos_layout >> strip_tac >>
      drule_all abi_malformed_tuple_capacity >> strip_tac >> fs[arithmeticTheory.ADD_COMM])
  >~ [`abi_decoder_coherent ce env sf (StructT _) tv`]
  >- (gvs[abi_decoder_coherent_struct_iff] >>
      drule abi_decoder_struct_infos >> strip_tac >> gvs[] >>
      fs[MAP_MAP_o, combinTheory.o_DEF, pairTheory.LAMBDA_PROD] >>
      drule abi_decoder_member_infos_layout >> strip_tac >>
      drule (abi_malformed_struct_capacity |> Q.INST
        [`args` |-> `MAP (\(name,ty,sz). (name,ty)) fields`]
        |> SRULE [MAP_MAP_o, combinTheory.o_DEF, pairTheory.LAMBDA_PROD]) >>
      disch_then drule_all >> strip_tac >>
      fs[arithmeticTheory.ADD_COMM, MAP_MAP_o, combinTheory.o_DEF, pairTheory.LAMBDA_PROD])
  >~ [`abi_decoder_coherent ce env sf (ArrayT _ _) tv`]
  >- (gvs[abi_decoder_coherent_array_iff] >>
      rename1 `ArrayT child bound` >> Cases_on `bound` >>
      gvs[abi_decoder_fixed_array_infos, Once type_to_abi_dec_info_def] >>
      drule_all abi_malformed_array_capacity >> strip_tac >>
      `LIST_REL (abi_decoder_coherent ce env sf)
         (REPLICATE n child) (REPLICATE n tv')` by
        simp[rich_listTheory.LIST_REL_REPLICATE_same] >>
      `!k. SUM (MAP abi_member_head_size
        (MAP (vyper_to_abi_type env) (REPLICATE k child))) =
        k * abi_member_head_size (vyper_to_abi_type env child)` by
        (Induct >> simp[arithmeticTheory.MULT_CLAUSES]) >>
      drule abi_decoder_member_infos_layout >> fs[arithmeticTheory.ADD_COMM])
  >~ [`abi_decoder_coherent ce env sf (BaseT _) tv`]
  >- (rename1 `BaseT bt` >> Cases_on `bt` >> gvs[type_to_abi_dec_info_def] >>
      rename1 `BytesT bd` >> Cases_on `bd` >> gvs[type_to_abi_dec_info_def]) >>
  qpat_x_assum `type_to_abi_dec_info _ _ _ = DecComplex _ _` mp_tac >>
  simp[type_to_abi_dec_info_def]

(* The descriptor head is bounded from coherence and malformed capacities,
   not from validity of the (malformed) parent. *)
(* Call after the head-bound assertion, keeping constructor arithmetic and
   execution as separately instrumented proof steps. *)
val run_tac =
  `guard_end.cs_next_var <= ceiling.cs_next_var` by decide_tac >>
  drule_all abi_malformed_aggregate_guard_run >> strip_tac >> gvs[] >>
  drule_all abi_decode_complex_guard_success_joint >>
  disch_then (qspec_then `PG` strip_assume_tac);

val frame_tac =
  `not_fresh_at st source /\ not_fresh_at st output` by
    fs[abi_malformed_entry_def, EVERY_DEF, abi_decoder_operand_live_def,
       abi_decoder_older_vars_def, not_fresh_at_def] >>
  `ptr_covers G' tn' output t (type_memory_bytes ce ty)` by
    (irule ptr_covers_frame >> qexistsl_tac [`G`, `s`, `tn`] >> simp[]) >>
  `abi_decode_ptr_window G' tn' t source (n2w B) L` by
    (irule abi_decode_ptr_window_frame >> qexistsl_tac [`G`, `s`, `tn`] >> simp[]) >>
  `alloca_inv s` by fs[abi_malformed_entry_def, stmt_state_rel_def] >>
  drule abi_decoder_complex_guard_code >> strip_tac >>
  drule abi_decode_complex_head_guard_shape >> strip_tac >>
  `EVERY (\i. ~is_terminator i.inst_opcode) (emitted_insts st guard_end)` by
    fs[EVERY_MEM] >>
  drule_all entry_straight_line_alloca_history >> strip_tac;

val reentry_tac =
  `local_ptrs_reserved cenv guard_end` by
    (irule local_ptrs_reserved_next_var >> qexists_tac `st` >>
     fs[abi_malformed_entry_def]) >>
  `abi_malformed_scratch_sites guard_end en func SUBSET
     abi_malformed_scratch_sites st en func` by
    (irule abi_malformed_scratch_sites_nested >> simp[]) >>
  `abi_malformed_entry H0 ctx func cenv cx es guard_end
    (abi_malformed_scratch_sites guard_end en func) dstid live
    (Var source) hi pos (Var output) B L xs p d (type_memory_bytes ce ty)
    (t with vs_inst_idx := LENGTH guard_end.cs_current_insts)` by
    (simp[abi_malformed_entry_inst_idx] >>
     irule abi_malformed_aggregate_reentry >> simp[] >>
     qexistsl_tac [`s`, `abi_malformed_scratch_sites st en func`, `st`] >> simp[]);

val normalize_tac =
  qmatch_asmsub_abbrev_tac `OK u` >>
  `u.vs_accounts = s.vs_accounts /\ u.vs_transient = s.vs_transient /\
   u.vs_call_ctx = s.vs_call_ctx /\ u.vs_immutables = s.vs_immutables /\
   u.vs_memory = s.vs_memory /\ u.vs_allocas = s.vs_allocas /\
   u.vs_alloca_next = s.vs_alloca_next /\
   u.vs_inst_idx = LENGTH guard_end.cs_current_insts /\
   u.vs_current_bb = guard_end.cs_current_bb /\ ~u.vs_halted` by
    (qpat_x_assum `t = s with vs_vars := _` mp_tac >>
     simp[Abbr `u`, venom_state_component_equality]) >>
  `abi_malformed_resource_post ctx func cenv cx es st.cs_next_var
     (abi_malformed_scratch_sites st en func) dstid s u /\
   fresh_vars_wrt ceiling u /\ allocas_from lo u /\ lo <= u.vs_alloca_next /\
   ptr_covers G' tn' output u (type_memory_bytes ce ty) /\
   abi_decode_ptr_window G' tn' u source (n2w B) L /\
   (!x. not_fresh_at st x ==> lookup_var x u = lookup_var x s /\
      FLOOKUP G' x = FLOOKUP G x /\ op_taint tn' (Var x) = op_taint tn (Var x))` by
    (fs[Abbr `u`, abi_malformed_resource_post_inst_idx,
      fresh_vars_wrt_def, allocas_from_def, ptr_covers_inst_idx,
      abi_decode_ptr_window_def, lookup_var_def] >> metis_tac[]);

val operands_tac =
  `(!x. pos = Var x ==> not_fresh_at st x) /\
   (!x. hi = Var x ==> not_fresh_at st x)` by
    (Cases_on `pos` >> Cases_on `hi` >>
     fs[abi_malformed_entry_def, EVERY_DEF, abi_decoder_operand_live_def,
        abi_decoder_older_vars_def, not_fresh_at_def]) >>
  `op_prov G' pos = NONE /\ op_prov G' hi = NONE /\
   op_taint tn' pos = {} /\ op_taint tn' hi = {}` by
    (Cases_on `pos` >> Cases_on `hi` >>
     fs[op_prov_def, op_taint_def] >> metis_tac[]);

(* Input: the exact non-Revert DecComplex residual after
   abiDecodeJointRejectCasesLib.complex_guard_split_tac.  This also handles
   both disjuncts of failed validity/admissibility exposed by that fragment.
   Output: original rejection goal remains, with one u,G',tn' chosen before
   D/explicit, a uniform OK prefix, normalized aggregate entry, source window,
   destination coverage, original resource post, freshness/history, unchanged
   four observations, old-variable/ghost frame, and untainted pos/hi.

   NOT discharged here: reflected member traversal from this u,G',tn', child
   IH adaptation/resource restoration, malformed-parent contradiction, and
   every DecDynArray case.  This is a guard handoff, not a malformed API.
   Usage after complex_guard_split_tac:
     `FOLDR (\(_,asz,_) acc. asz + acc) 0 l < dimword (:256)` by head_bound_tac >>
     run_tac >> frame_tac >> reentry_tac >> normalize_tac >> operands_tac
   Keep these as separate proof steps, not one opaque aggregate tactic: the
   constructor arithmetic and transport each have their own bounded check.
   Exact residual evidence: C3.4.2.1 dossier. No validation theorem exported. *)
end
