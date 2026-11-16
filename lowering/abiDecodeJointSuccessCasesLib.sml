(* Tactic fragments for the immutable allocation-backed joint decoder.
   No theorem is registered here; the publication join owns the declarations. *)
structure abiDecodeJointSuccessCasesLib =
struct
open HolKernel boolLib bossLib
open abiDecoderCoherenceTheory abiValidAllocatedContractTheory
     abiValidAllocatedJointTheory abiValidAllocatedPrimitiveJointTheory
     abiValidAllocatedBytesJointTheory

val C = ``\ty tv.
 !v ctx func cenv cx es st en source hi pos output B L xs p d dstid live ceiling s H0.
 abi_valid_allocated_entry H0 ce env sf ty tv v ctx func cenv cx es
  st en (Var source) hi pos (Var output) B L xs p d dstid live ceiling s ==>
 !G tn PG lo.
 ~ctx_has_dalloca ctx /\
 abi_decode_ptr_window G tn s source (n2w B) L /\
 ptr_covers G tn output s (type_memory_bytes ce ty) /\
 op_prov G pos = NONE /\ op_prov G hi = NONE /\
 op_taint tn pos = {} /\ op_taint tn hi = {} /\
 allocas_from lo s /\ lo <= s.vs_alloca_next /\ alloca_history func s ==>
 ?u G' tn'.
 abi_valid_allocated_post tv v ctx func cenv cx es st en ceiling dstid
   d (type_memory_bytes ce ty) s u /\
 u.vs_accounts = s.vs_accounts /\ u.vs_transient = s.vs_transient /\
 u.vs_call_ctx = s.vs_call_ctx /\ u.vs_immutables = s.vs_immutables /\
 (!D explicit. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG)
   (s,G,tn) [] (OK u,G',tn')) /\
 ptr_covers G' tn' output u (type_memory_bytes ce ty) /\
 abi_decode_ptr_window G' tn' u source (n2w B) L /\
 (!mem. mem_agree_outside tn'.t_mem u.vs_memory mem ==> val_in_memory tv v d mem) /\
 (!x. abi_decoder_operand_live st.cs_next_var (Var x) ==>
   FLOOKUP G' x = FLOOKUP G x /\ op_taint tn' (Var x) = op_taint tn (Var x)) /\
 tn'.t_stor = tn.t_stor /\ tn'.t_trans = tn.t_trans /\ tn'.t_imm = tn.t_imm /\
 (!a. ~(d <= a /\ a < d+type_memory_bytes ce ty) /\
   ~abi_malformed_site_range (abi_malformed_scratch_sites st en func) s u a 1 ==>
   (a IN tn'.t_mem <=> a IN tn.t_mem)) /\
 alloca_history func u /\ allocas_from lo u /\ lo <= u.vs_alloca_next``;

val induction =
 qsuff_tac `!ce env sf ty tv. abi_decoder_coherent ce env sf ty tv ==> (^C) ty tv` >-
 (BETA_TAC >> strip_tac >> strip_tac >>
  `abi_decoder_coherent ce env sf ty tv` by fs[abi_valid_allocated_entry_def] >>
  first_x_assum drule >> disch_then drule >> simp[]) >>
 ho_match_mp_tac abi_decoder_coherent_strongind >> rpt conj_tac;

val parameters = BETA_TAC >> rpt gen_tac >> disch_tac >> rpt gen_tac >> strip_tac;

val primitive =
 parameters >>
 drule_all abi_valid_allocated_primitive_joint_observations >>
 disch_then (qspec_then `PG` strip_assume_tac) >>
 qhdtm_assum `abi_valid_allocated_entry`
   (assume_tac o CONJUNCT1 o PURE_REWRITE_RULE [abi_valid_allocated_entry_def]) >>
 drule_all abiDecoderWordTypedTheory.abi_decoder_primitive_cases >> strip_tac >>
 qexistsl_tac [`t`, `G'`, `tn'`] >>
 fs[abiDecodePtrMemberFrameTheory.abi_decode_ptr_window_def] >> metis_tac[];

val bytes =
 parameters >> drule_all abi_valid_allocated_bytes_joint_observations >>
 disch_then (qspec_then `PG` strip_assume_tac) >>
 qexistsl_tac [`t`, `G'`, `tn'`] >> simp[];

val base =
 rpt gen_tac >> strip_tac >>
 Cases_on `?n. BaseT bt = BaseT (BytesT (Dynamic n)) \/ BaseT bt = BaseT (StringT n)` >-
 (pop_assum (qx_choose_then `n` assume_tac) >> bytes) >>
 `?clamp. type_to_abi_dec_info sf ce (BaseT bt) = DecPrimWord clamp` by
 (Cases_on `bt` >> gvs[exprLoweringTheory.type_to_abi_dec_info_def] >>
  rename1 `BytesT bound` >> Cases_on `bound` >> gvs[exprLoweringTheory.type_to_abi_dec_info_def]) >>
 primitive;

val flag =
 rpt gen_tac >> strip_tac >>
 `?clamp. type_to_abi_dec_info sf ce (FlagT nsid) = DecPrimWord clamp` by
   simp[exprLoweringTheory.type_to_abi_dec_info_def] >> primitive;

val tuple =
 rpt gen_tac >> strip_tac >> irule abi_valid_allocated_joint_tuple >>
 fs[listTheory.LIST_REL_CONJ, SF ETA_ss];

val struct_case =
 rpt gen_tac >> strip_tac >> irule abi_valid_allocated_joint_struct >>
 fs[listTheory.LIST_REL_CONJ, SF ETA_ss];

val array =
 rpt gen_tac >> strip_tac >> Cases_on `bound` >-
 (irule abi_valid_allocated_joint_fixed_array >> simp[]) >>
 reverse (Cases_on `is_abi_dynamic ce.ce_struct_fields ty \/
     dec_info_needs_clamp (type_to_abi_dec_info sf ce ty)`) >-
 (irule abi_valid_allocated_joint_bulk >> fs[exprLoweringTheory.type_to_abi_dec_info_def]);

(* Leaves only the recursive Dynamic branch, with its generalized child IH. *)
val routine_cases =
 reverse (induction >- base >- flag) >- struct_case >- tuple >> array;

end
