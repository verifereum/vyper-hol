(* First-child semantic applicability, not a recursive decoder API.

   VALIDATION BOUNDARY (C3.4.2.4.1)
   The closed subject-local check derives first_child_semantic from the exact
   complex-root inputs and constructor-local C/R hypotheses. Tuple projection
   keeps the paired LIST_REL; struct projection descends BOTH deleted maps;
   fixed arrays lift the one child pair through REPLICATE. No all-children IH,
   independent child endpoint, or child_pos<=L premise is assumed.

   Assembly interface (local assertions, not exported decoder contracts):
   - selected_bytes converts actual selected validity/admissibility to the
     DROP-based semantic entry, deriving child_pos<=L only on success;
   - root_layout transports an arbitrary local relation P beside coherence;
   - first_guard, first_projection root_layout, first_bounds,
     first_setup setup_ready, first_entry_finish run as SEPARATE phases,
     to retain ordinary per-tactic bounds;
   - setup_ready is the local assertion checked with ChildReadyLib.one_step;
   - selected_child consumes the literal exact C/R pair at that SAME child;
   - first_child_semantic C R RESULT first_child_entry selected_child combines
     the entry assertion and selected-child assertion. It retains the entire
     exact success endpoint conjunction or the uniform four-world-field abort.
   C/R/RESULT are local quotations, not HOL constants. All assertion statements
   and their phase invocations are persisted before temporary check removal:
   TO_extcall_case-L0026-20261116T200412239912Z_m0164_t001 (lines 1-260),
   TO_extcall_case-L0026-20261116T200412239912Z_m0166_t001 (260-365).
   Passing extracted-procedure build:
   TO_extcall_case-L0026-20261116T200412239912Z_m0163_t001.
   No parent restoration, later-member fold or dynamic recursion is established.
*)
structure abiDecodeJointRejectChildSemanticLib =
struct
open HolKernel boolLib bossLib
open abiMalformedMemberReflectionTheory abiValidAllocatedSourceTheory
     abiVyperAdmissibleTheory

(* coherent ce/env/sf child; xs length/head bound and child_pos selection equation;
   selected bytes valid and admissible. Result: semantic DROP entry data.
   In particular child_pos<=L is DERIVED only in this success branch. *)
val selected_bytes =
  drule_all abi_malformed_member_reflection >> strip_tac >>
  drule_all abi_valid_source_member_position >> strip_tac >>
  `abi_vyper_admissible env ty (dec (vyper_to_abi_type env ty) (DROP child_pos xs))` by
    metis_tac[] >>
  drule_all abi_vyper_admissible_convert >> strip_tac;

open abiDecoderCoherenceTheory abiDecoderMemberInfosTheory abiMalformedBoundedContractTheory
     abiEncoderTheory exprLoweringTheory compileEnvTheory valueEncodingTheory
     valueEncodingTypingTheory vyperABITheory contractABITheory vyperTypeSystemTheory
     abiDecoderMembersTheory listTheory rich_listTheory arithmeticTheory wordsTheory

val inhabited_members =
  Induct >> Cases_on `vs` >> simp[has_type_def] >> metis_tac[];

(* Constructor projection, retaining layout ce and descending both struct maps.
   Zero fixed arrays require no child inhabitant. *)
val root_layout =
 `!tys vs. has_types (vyper_to_abi_types env tys) vs ==>
    EVERY (\ty. ?av. has_type (vyper_to_abi_type env ty) av) tys` by inhabited_members >>
 Cases_on `ty`
 >~ [`abi_decoder_coherent ce env sf (TupleT _) tv`]
 >- (gvs[abi_decoder_coherent_tuple_iff, abi_decoder_tuple_infos] >>
     drule abi_decoder_member_infos_layout >> strip_tac >>
     drule_all abi_malformed_tuple_capacity >> strip_tac >>
     `EVERY (\child. ?av. has_type (vyper_to_abi_type env child) av) l'` by
       (Cases_on `av` >> fs[has_type_def] >> first_x_assum drule >> simp[]) >>
     `LIST_REL (P env sf) l' tvs` by metis_tac[] >>
     qexistsl_tac [`sf`, `env`, `l'`, `tvs`] >>
     fs[abi_decoder_header_def, type_memory_size_def, assignable_type_def])
 >~ [`abi_decoder_coherent ce env sf (StructT _) tv`]
 >- (gvs[abi_decoder_coherent_struct_iff] >>
     drule abi_decoder_struct_infos >> strip_tac >> gvs[] >>
     fs[MAP_MAP_o, combinTheory.o_DEF, pairTheory.LAMBDA_PROD] >>
     drule abi_decoder_member_infos_layout >> strip_tac >>
     drule (abi_malformed_struct_capacity |> Q.INST
       [`args` |-> `MAP (\(name,ty,sz). (name,ty)) fields`] |>
       SRULE [MAP_MAP_o, combinTheory.o_DEF, pairTheory.LAMBDA_PROD]) >>
     disch_then drule_all >> strip_tac >>
     `LENGTH (MAP (\(name,ty,sz). name) fields) = LENGTH tvs` by
       (drule LIST_REL_LENGTH >> simp[]) >>
     drule type_memory_size_fields_zip >> strip_tac >>
     `EVERY (\child. ?av. has_type (vyper_to_abi_type (env \\ p) child) av)
       (MAP (\(name,ty,sz). ty) fields)` by
       (`!tys vs. has_types (vyper_to_abi_types (env \\ p) tys) vs ==>
          EVERY (\ty. ?av. has_type (vyper_to_abi_type (env \\ p) ty) av) tys` by inhabited_members >>
        qpat_x_assum `has_type _ av` mp_tac >> simp[Once vyper_to_abi_type_def] >>
        Cases_on `av` >> simp[has_type_def] >> strip_tac >>
        first_x_assum drule >> simp[vyper_to_abi_types_MAP, MAP_MAP_o,
          combinTheory.o_DEF, pairTheory.LAMBDA_PROD]) >>
     `LIST_REL (P (env \\ p) (sf \\ nsid_to_string p))
       (MAP (\(name,ty,sz). ty) fields) tvs` by
       (first_x_assum irule >> simp[] >> metis_tac[]) >>
     qexistsl_tac [`sf \\ nsid_to_string p`, `env \\ p`,
       `MAP (\(name,ty,sz). ty) fields`, `tvs`] >>
     fs[abi_decoder_header_def, type_memory_size_def, assignable_type_def,
       MAP_MAP_o, combinTheory.o_DEF, pairTheory.LAMBDA_PROD, EVERY_MAP] >>
     gvs[MAP_MAP_o, combinTheory.o_DEF, pairTheory.LAMBDA_PROD, EVERY_MAP])
 >~ [`abi_decoder_coherent ce env sf (ArrayT _ _) tv`]
 >- (gvs[abi_decoder_coherent_array_iff] >> rename1 `ArrayT child bound` >>
     Cases_on `bound` >> gvs[abi_decoder_fixed_array_infos, Once type_to_abi_dec_info_def] >>
     drule_all abi_malformed_array_capacity >> strip_tac >>
     `EVERY (\child. ?av. has_type (vyper_to_abi_type env child) av) (REPLICATE n child)` by
       (qpat_x_assum `has_type _ av` mp_tac >> simp[Once vyper_to_abi_type_def] >>
        Cases_on `av` >> simp[has_type_def] >> strip_tac >> fs[] >>
        `has_types (vyper_to_abi_types env (REPLICATE n child)) l` by
          fs[vyper_to_abi_types_MAP, map_replicate] >> first_x_assum drule >> simp[]) >>
     `type_memory_size_list (REPLICATE n tv') = n * type_memory_size tv'` by
       (POP_ASSUM_LIST (K all_tac) >> Induct_on `n` >> simp[type_memory_size_def, MULT_CLAUSES]) >>
     `P env sf child tv'` by metis_tac[] >>
     qexistsl_tac [`sf`, `env`, `REPLICATE n child`, `REPLICATE n tv'`] >>
     simp[LIST_REL_REPLICATE_same, EVERY_REPLICATE] >>
     fs[abi_decoder_header_def, type_memory_size_def, assignable_type_def,
       map_replicate, SUM_REPLICATE] >>
     drule abi_decoder_coherent_header >> simp[abi_decoder_header_def] >> strip_tac >> gvs[])
 >~ [`abi_decoder_coherent ce env sf (BaseT _) tv`]
 >- (rename1 `BaseT bt` >> Cases_on `bt` >> gvs[type_to_abi_dec_info_def] >>
     rename1 `BytesT bd` >> Cases_on `bd` >> gvs[type_to_abi_dec_info_def]) >>
 qpat_x_assum `type_to_abi_dec_info _ _ _ = DecComplex _ _` mp_tac >>
 simp[type_to_abi_dec_info_def];

open abiDecoderContractTheory abiDecoderDynamicTheory
     abiValidAllocatedContractTheory abiMalformedRecursiveInterfaceTheory
     abiMalformedParentAggregateTheory abiDecoderComplexExecuteTheory
     abiDecoderMemberConsTheory abiDecoderOffsetTheory
     abiDecodePtrComplexGuardJointTheory abiMalformedMemberSetupTheory
     abiDecodePtrMemberJointTheory abiDecodePtrMemberFrameTheory
     abiValidAllocatedComplexTheory abiDecoderComplexHeadTheory
     entryDecoderHistoryFrameTheory decoderGhostFramePtrTheory abiDecoderReentryTheory
     localPtrsPropsTheory ghostPcTransportPtrTheory ptrDisciplineTheory
     loweringStateRelDefsTheory bodyPtrDefsTheory stateFrameTheory fragGasOriginPtrTheory
     valueEncodingPropsTheory exprLoweringPropsTheory venomStateTheory
     exprSimAbiDecodePrimitiveOwnedTheory abiDecodeRangesTheory

(* Exact C/R hypotheses are supplied by the constructor induction, for the
   same child/env/sf. This procedure consumes them, not a weaker CHILD callback.
   The success branch derives the DROP-based semantic entry; the failure branch
   uses the exact rejection IH. Both choose endpoints before D/explicit. *)
val selected_child =
 BETA_TAC >> strip_tac >>
 Cases_on `vyper_decode_valid_enc (vyper_to_abi_type env ty)
   (if is_dynamic (vyper_to_abi_type env ty) then DROP child_pos xs
    else TAKE (static_length (vyper_to_abi_type env ty)) (DROP child_pos xs)) /\
 abi_vyper_admissible env ty (dec (vyper_to_abi_type env ty)
   (if is_dynamic (vyper_to_abi_type env ty) then DROP child_pos xs
    else TAKE (static_length (vyper_to_abi_type env ty)) (DROP child_pos xs)))`
 >- (pop_assum strip_assume_tac >> selected_bytes >>
     `abi_valid_allocated_entry H0 ce env sf ty tv v ctx func cenv cx es
       st en (Var source) hi pos (Var output) B L xs child_pos d dstid live ceiling s` by
       simp[abi_valid_allocated_entry_def] >>
     qpat_x_assum `!v ctx func cenv cx es st en source hi pos output B L xs p d dstid live ceiling s H0. _`
       (drule_then (qspecl_then [`G`, `tn`, `PG`, `lo`] mp_tac)) >>
     (impl_tac >- simp[]) >> strip_tac >> disj2_tac >>
     qexistsl_tac [`v`, `u`, `G'`, `tn'`] >> simp[]) >>
 disj1_tac >> first_x_assum irule >> simp[] >> metis_tac[];

(* Parameters are the checked local root_layout and setup_ready assertions.
   No theorem is manufactured or exported by this ML procedure. *)
val first_guard =
 strip_tac >>
 drule abi_decoder_complex_trace >> strip_tac >>
 `middle = guard_end` by metis_tac[pairTheory.PAIR_EQ] >>
 qpat_x_assum `middle = guard_end` SUBST_ALL_TAC >>
 `abi_decode_source_opcode MLOAD` by simp[abi_decode_source_opcode_def] >>
 drule_all abi_decoder_complex_code >> strip_tac >>
 `FOLDR (\(_,asz,_) acc. asz + acc) 0 l < dimword(:256)` by
    abiDecodeJointRejectGuardLib.head_bound_tac >>
 abiDecodeJointRejectGuardLib.run_tac >>
 abiDecodeJointRejectGuardLib.frame_tac >>
 abiDecodeJointRejectGuardLib.reentry_tac >>
 abiDecodeJointRejectGuardLib.normalize_tac >>
 abiDecodeJointRejectGuardLib.operands_tac;

fun first_projection root_layout_th =
 `?sf1 env1 tys tvs.
   l = abi_decoder_member_infos sf1 ce tys /\
   LIST_REL (abi_decoder_coherent ce env1 sf1) tys tvs /\ LIST_REL (P env1 sf1) tys tvs /\
   type_memory_bytes ce ty = SUM (MAP (type_memory_bytes ce) tys) /\
   type_memory_size_list tvs < dimword(:256) /\ EVERY (assignable_type env1) tys /\
   EVERY (\child. ?av. has_type (vyper_to_abi_type env1 child) av) tys /\
   EVERY (\child. abi_size_bound sf1 child < dimword(:256)) tys` by
   (irule root_layout_th >> qexistsl_tac [`b`, `env`, `sf`, `tv`] >> simp[] >> metis_tac[]) >>
 Cases_on `tys` >- gvs[abi_decoder_member_infos_def] >>
 Cases_on `tvs` >> fs[LIST_REL_def, EVERY_DEF] >>
 rename1 `LIST_REL (abi_decoder_coherent ce env1 sf1) tailtys tailtvs` >>
 rename1 `abi_decoder_coherent ce env1 sf1 child childtv` >>
 abiDecodeJointRejectInitialMemberLib.first_code_tac;

val first_bounds =
 `p + abi_member_head_size (vyper_to_abi_type env1 child) <= L` by
   (qpat_assum `abi_decoder_coherent ce env1 sf1 child childtv` mp_tac >>
    disch_then (assume_tac o MATCH_MP abi_decoder_coherent_header) >>
    fs[abi_decoder_member_infos_def, abi_decoder_header_def]) >>
 `p + (if dec_info_needs_offset (type_to_abi_dec_info sf1 ce child)
       then 32 else 0) <= L` by
   (qpat_assum `abi_decoder_coherent ce env1 sf1 child childtv` mp_tac >>
    disch_then (assume_tac o MATCH_MP abi_decoder_coherent_dynamic) >>
    fs[abi_decoder_needs_offset_iff, abiDecodeRangesTheory.abi_member_head_size_def] >>
    Cases_on `is_dynamic (vyper_to_abi_type env1 child)` >> fs[] >>
    IF_CASES_TAC >> decide_tac) >>
 `type_memory_size childtv < dimword(:256)` by fs[type_memory_size_def] >>
 `fn_has_code middle end_st func` by metis_tac[fragExecTheory.fn_has_code_split] >>
 `type_memory_bytes ce child <= SUM (MAP (type_memory_bytes ce) tailtys) + type_memory_bytes ce child` by simp[];

fun first_setup setup_ready_th =
 drule_all (setup_ready_th |> Q.INST [`ao` |-> `0`, `vo` |-> `0`] |> SRULE []) >>
 strip_tac >- metis_tac[];

val first_entry_finish =
 `abi_malformed_scratch_sites middle end_st func SUBSET
    abi_malformed_scratch_sites guard_end en func` by
    (irule abi_malformed_scratch_sites_nested >> decide_tac) >>
 `abi_malformed_entry H0 ctx func cenv cx es middle
    (abi_malformed_scratch_sites middle end_st func) dstid live
    (Var source) hi (FST ops) (SND ops) B L xs
    (p + if dec_info_needs_offset (type_to_abi_dec_info sf1 ce child)
         then abi_head_word (DROP p xs) else 0) d (type_memory_bytes ce child) u'` by
   (qpat_x_assum `abi_malformed_entry _ _ _ _ _ _ middle _ _ _ _ _ _ _ _ _ _ _ _ _ _` mp_tac >>
    simp_tac bool_ss [abi_malformed_entry_def] >>
    fs[pred_setTheory.SUBSET_DEF] >> metis_tac[]) >>
 `LENGTH xs = L` by
   (qpat_assum `abi_malformed_entry _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _` mp_tac >>
    POP_ASSUM_LIST (K all_tac) >>
    rw[abi_malformed_entry_def, abi_malformed_allocated_window_def] >>
    metis_tac[valueEncodingPropsTheory.LENGTH_mem_bytes_at]) >>
 `(case type_to_abi_dec_info sf1 ce child of
    DecPrimWord clamp =>
     (p + if dec_info_needs_offset (type_to_abi_dec_info sf1 ce child)
          then abi_head_word (DROP p xs) else 0)+32 <= L | _ => T)` by
   (Cases_on `type_to_abi_dec_info sf1 ce child` >> simp[] >>
    drule_all abi_decode_scalar_source_shape >> strip_tac >>
    fs[dec_info_needs_offset_def, abi_member_head_size_def]) >>
 disj2_tac >>
 qexistsl_tac [`u'`, `G''`, `tn''`, `sf1`, `env1`, `child`, `childtv`,
   `tailtys`, `tailtvs`, `ops`, `middle`, `end_st`, `out`] >>
 fs[] >> metis_tac[];

(* C, R and RESULT are the literal exact local quotations used by the joint
   induction, not HOL definitions. Keep C/R intact during witness forwarding:
   rewriting under their binders would erase fixed coherence/size premises. *)
fun first_child_semantic C R RESULT entry_th selected_th =
 BETA_TAC >> strip_tac >>
 mp_tac (entry_th |> Q.INST
   [`P` |-> `\env sf child childtv. (^C) ce env sf child childtv /\ (^R) ce env sf child childtv`] |> SPEC_ALL |> BETA_RULE) >>
 (impl_tac >- (asm_rewrite_tac[] >> qexists_tac `av` >> asm_rewrite_tac[])) >>
 strip_tac >- (disj1_tac >> qexistsl_tac [`v`, `G2`, `tn2`] >> asm_rewrite_tac[]) >>
 `(^RESULT) ce env1 child childtv ctx func cenv cx es middle child_end ceiling dstid
    source hi (FST ops) out B L xs child_pos d u G1 tn1 PG lo` by
   (BETA_TAC >>
    irule (selected_th |> Q.INST [`ao` |-> `0`] |> BETA_RULE |> REWRITE_RULE [ADD_CLAUSES]) >>
    (conj_tac >- (qexists_tac `av'` >> first_assum ACCEPT_TAC)) >>
    rpt (conj_tac >- first_assum ACCEPT_TAC) >>
    qexistsl_tac [`H0`, `hi`, `live`, `p`, `FST ops`, `sf1`] >>
    rpt conj_tac >> first_assum ACCEPT_TAC) >>
 disj2_tac >>
 qexistsl_tac [`u`, `G1`, `tn1`, `sf1`, `env1`, `child`, `childtv`,
   `tailtys`, `tailtvs`, `ops`, `middle`, `child_end`, `out`, `child_pos`] >>
 rpt (conj_tac >- first_assum ACCEPT_TAC) >>
 (conj_tac >- (qexists_tac `av'` >> first_assum ACCEPT_TAC)) >>
 rpt (conj_tac >- first_assum ACCEPT_TAC) >>
 first_assum (ACCEPT_TAC o BETA_RULE);
end
