(* First-member initialization only; no recursive child execution.

   Checked use from the immutable malformed root's nonempty DecComplex branch:
   - expose abi_decoder_complex_trace/code and identify guard_end;
   - use RejectGuardLib.head_bound_tac, run_tac, frame_tac, reentry_tac,
     normalize_tac, operands_tac at the actual non-reverting guard;
   - first_layout_tac exposes sf1/env1/child/childtv/tailtys/tailtvs and
     derives the zero-offset head and destination bounds;
   - first_code_tac exposes the actual (ops,middle) setup compilation,
     code inclusion and next-var ceiling bound;
   - the resulting context supplies every input of RejectMemberSetupLib.one_step
     at guard_end, ao=vo=0. Its abort and OK alternatives share the actual
     incoming path. No child validity, inhabitation or child IH is assumed.

   first_layout_tac expects the parent variables and guarded head sum named
   ce/env/sf/ty/tv/b/l/p/L. first_code_tac additionally expects the actual
   nonempty compile_abi_decode_members_to_buf equation, code inclusion and
   the whole compilation ceiling; guard_end is the incoming compile state.
   These are proof procedures, not a second decoder contract.

   Closed temporary validation (removed before publication):
   initial_layout, initial_bounds, initial_setup_inputs, initial_setup_exercised.
   Exact 200-line input/output source is persisted in tool output
   TO_extcall_case-L0023-20261116T165637568820Z_m0067_t002;
   its passing ordinary build is m0067_t001 of the same run.
   The full setup-input conjunction is at lines 66-88; the exercised
   abort/OK result is at lines 170-189. Recursive child IH application and
   post-child parent restoration are deliberately not established here. *)
structure abiDecodeJointRejectInitialMemberLib =
struct
open HolKernel boolLib bossLib
open abiDecoderCoherenceTheory abiDecoderMemberInfosTheory
     abiDecoderMemberConsTheory abiDecoderDynamicTheory abiDecoderOffsetTheory
     abiDecoderComplexExecuteTheory abiDecoderMemberSetupTheory
     abiEncoderTheory exprLoweringTheory compileEnvTheory
     valueEncodingTheory valueEncodingTypingTheory vyperABITheory
     listTheory rich_listTheory wordsTheory

(* A coherent complex descriptor exposes its actual semantic member list.
   Layout ce is retained even for the deleted struct maps. *)
val layout_tac =
  Cases_on `ty`
  >~ [`abi_decoder_coherent ce env sf (TupleT _) tv`]
  >- (gvs[abi_decoder_coherent_tuple_iff, abi_decoder_tuple_infos] >>
      drule abi_decoder_member_infos_layout >> strip_tac >>
      qexistsl_tac [`sf`, `env`, `l'`, `tvs`] >>
      fs[abi_decoder_header_def, type_memory_size_def])
  >~ [`abi_decoder_coherent ce env sf (StructT _) tv`]
  >- (gvs[abi_decoder_coherent_struct_iff] >>
      drule abi_decoder_struct_infos >> strip_tac >> gvs[] >>
      fs[MAP_MAP_o, combinTheory.o_DEF, pairTheory.LAMBDA_PROD] >>
      drule abi_decoder_member_infos_layout >> strip_tac >>
      `LENGTH (MAP (\(name,ty,sz). name) fields) = LENGTH tvs` by
        (drule LIST_REL_LENGTH >> simp[]) >>
      drule type_memory_size_fields_zip >> strip_tac >>
      qexistsl_tac [`sf \\ nsid_to_string p`, `env \\ p`,
        `MAP (\(name,ty,sz). ty) fields`, `tvs`] >>
      fs[abi_decoder_header_def, type_memory_size_def,
         MAP_MAP_o, combinTheory.o_DEF, pairTheory.LAMBDA_PROD])
  >~ [`abi_decoder_coherent ce env sf (ArrayT _ _) tv`]
  >- (gvs[abi_decoder_coherent_array_iff] >>
      rename1 `ArrayT child bound` >> Cases_on `bound` >>
      gvs[abi_decoder_fixed_array_infos, Once type_to_abi_dec_info_def] >>
      qexistsl_tac [`sf`, `env`, `REPLICATE n child`, `REPLICATE n tv'`] >>
      simp[LIST_REL_REPLICATE_same] >>
      fs[abi_decoder_header_def, type_memory_size_def, map_replicate, SUM_REPLICATE] >>
      drule abi_decoder_coherent_header >>
      simp[abi_decoder_header_def] >> strip_tac >> gvs[])
  >~ [`abi_decoder_coherent ce env sf (BaseT _) tv`]
  >- (rename1 `BaseT bt` >> Cases_on `bt` >> gvs[type_to_abi_dec_info_def] >>
      rename1 `BytesT bd` >> Cases_on `bd` >> gvs[type_to_abi_dec_info_def]) >>
  qpat_x_assum `type_to_abi_dec_info _ _ _ = DecComplex _ _` mp_tac >>
  simp[type_to_abi_dec_info_def];

(* Inputs: coherent parent, its complex descriptor equation, l <> [],
   and the guarded p+headsum<=L.  No child validity is used. *)
val first_layout_tac =
  `?sf1 env1 tys tvs.
     l = abi_decoder_member_infos sf1 ce tys /\
     LIST_REL (abi_decoder_coherent ce env1 sf1) tys tvs /\
     type_memory_bytes ce ty = SUM (MAP (type_memory_bytes ce) tys)` by
    (qpat_assum `abi_decoder_coherent ce env sf ty tv` mp_tac >>
     qpat_assum `type_to_abi_dec_info sf ce ty = DecComplex b l` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >> rpt strip_tac >> layout_tac) >>
  Cases_on `tys` >- gvs[abi_decoder_member_infos_def] >>
  Cases_on `tvs` >> fs[LIST_REL_def] >>
  rename1 `LIST_REL (abi_decoder_coherent ce env1 sf1) tailtys tailtvs` >>
  rename1 `abi_decoder_coherent ce env1 sf1 child childtv` >>
  `type_memory_bytes ce child <= type_memory_bytes ce ty` by fs[] >>
  `p + (if dec_info_needs_offset (type_to_abi_dec_info sf1 ce child)
        then 32 else 0) <= L` by
    (drule abi_decoder_coherent_header >> strip_tac >>
     drule abi_decoder_coherent_dynamic >> strip_tac >>
     fs[abi_decoder_member_infos_def, abi_decoder_header_def,
        abi_decoder_needs_offset_iff, abiDecodeRangesTheory.abi_member_head_size_def] >>
     Cases_on `is_dynamic (vyper_to_abi_type env1 child)` >> fs[] >>
     IF_CASES_TAC >> decide_tac);

val first_code_tac =
  drule abi_decoder_member_cons_trace >> strip_tac >>
  drule_all abi_decoder_member_cons_code >> strip_tac >>
  `middle.cs_next_var <= ceiling.cs_next_var` by decide_tac >>
  `fn_has_code guard_end middle func` by
    (metis_tac[fragExecTheory.fn_has_code_split]);
end
