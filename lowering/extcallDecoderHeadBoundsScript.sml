Theory extcallDecoderHeadBounds
Ancestors
  abiDecoderCoherence abiDecoderMemberInfos abiCanonicalHeadSize abiDecodeRanges
  valueEncodingProps vyperABI vyperValue contractABI arithmetic words list

Theorem decoder_member_head_sum[local]:
  !tys tvs. LIST_REL (\ty tv.
    abi_member_head_size (vyper_to_abi_type env ty) <= type_memory_size tv) tys tvs ==>
  SUM (MAP abi_member_head_size (MAP (vyper_to_abi_type env) tys)) <=
    type_memory_size_list tvs
Proof
  Induct >> Cases_on `tvs` >> simp[valueEncodingTheory.type_memory_size_def] >>
  rpt strip_tac >> first_x_assum drule >> decide_tac
QED

Theorem decoder_struct_memory_sum[local]:
  !names tvs. LENGTH names = LENGTH tvs ==>
  type_memory_size_fields (ZIP (names,tvs)) = type_memory_size_list tvs
Proof
  Induct >> Cases_on `tvs` >> simp[valueEncodingTheory.type_memory_size_def]
QED

Theorem extcall_decoder_member_head_bound:
  !ce env sf ty tv. abi_decoder_coherent ce env sf ty tv ==>
  abi_member_head_size (vyper_to_abi_type env ty) <= type_memory_size tv
Proof
  ho_match_mp_tac abi_decoder_coherent_ind >> rpt conj_tac
  >- suspend "base"
  >- suspend "flag"
  >- suspend "array"
  >- suspend "tuple"
  >> suspend "struct"
QED

Resume extcall_decoder_member_head_bound[base]:
  rpt strip_tac >> Cases_on `bt` >>
  gvs[abi_decoder_header_def, abi_member_head_size_def,
    vyper_to_abi_type_def, vyper_base_to_abi_type_def, is_dynamic_def,
    valueEncodingTheory.type_memory_size_def] >>
  Cases_on `b` >> gvs[vyper_base_to_abi_type_def, is_dynamic_def,
    valueEncodingTheory.type_memory_size_def, static_length_def]
QED

Resume extcall_decoder_member_head_bound[flag]:
  rpt strip_tac >> gvs[abi_decoder_header_def, abi_member_head_size_def,
    vyper_to_abi_type_def, is_dynamic_def, static_length_def,
    valueEncodingTheory.type_memory_size_def]
QED

Resume extcall_decoder_member_head_bound[array]:
  rpt strip_tac >>
  `0 < type_slot_size tv /\ 0 < bound_length bound` by
    (qpat_x_assum `abi_decoder_header _ _ _ _` mp_tac >>
     simp[abi_decoder_header_def, Once evaluate_type_def, AllCaseEqs()]) >>
  Cases_on `is_dynamic (vyper_to_abi_type env (ArrayT ty bound))`
  >- (simp[abi_member_head_size_def, type_memory_size_slots] >>
      Cases_on `bound` >> gvs[type_slot_size_def, vyperASTTheory.bound_length_def] >>
      simp[MULT_POS]) >>
  gvs[abi_decoder_header_def, abi_member_head_size_def]
QED

Resume extcall_decoder_member_head_bound[tuple]:
  rpt strip_tac >> drule decoder_member_head_sum >> strip_tac >>
  Cases_on `is_dynamic (vyper_to_abi_type env (TupleT tys))`
  >- (`32 <= SUM (MAP abi_member_head_size (MAP (vyper_to_abi_type env) tys))` by
        (irule canonical_dynamic_head_sum >>
         gvs[vyper_to_abi_type_def, is_dynamic_def,
           abiDecoderMembersTheory.vyper_to_abi_types_MAP]) >>
      gvs[abi_member_head_size_def, valueEncodingTheory.type_memory_size_def]) >>
  gvs[abi_decoder_header_def, abi_member_head_size_def]
QED

Resume extcall_decoder_member_head_bound[struct]:
  rpt strip_tac >>
  `LENGTH args = LENGTH tvs` by metis_tac[LIST_REL_LENGTH, LENGTH_MAP] >>
  drule decoder_member_head_sum >> strip_tac >>
  `type_memory_size_fields (ZIP (MAP FST args,tvs)) = type_memory_size_list tvs` by
    (irule decoder_struct_memory_sum >> simp[]) >>
  Cases_on `is_dynamic (vyper_to_abi_type env (StructT nsid))`
  >- (`32 <= SUM (MAP abi_member_head_size
          (MAP (vyper_to_abi_type (env \\ nsid)) (MAP SND args)))` by
        (irule canonical_dynamic_head_sum >>
         gvs[vyper_to_abi_type_def, is_dynamic_def,
           abiDecoderMembersTheory.vyper_to_abi_types_MAP]) >>
      gvs[abi_member_head_size_def, valueEncodingTheory.type_memory_size_def]) >>
  gvs[abi_decoder_header_def, abi_member_head_size_def]
QED

Finalise extcall_decoder_member_head_bound

Theorem extcall_decoder_members_head_bound:
  !tys tvs. LIST_REL (abi_decoder_coherent ce env sf) tys tvs ==>
  SUM (MAP abi_member_head_size (MAP (vyper_to_abi_type env) tys)) <=
    type_memory_size_list tvs
Proof
  rpt strip_tac >> irule decoder_member_head_sum >>
  qpat_x_assum `LIST_REL _ _ _` mp_tac >>
  match_mp_tac LIST_REL_mono >> rpt strip_tac >>
  drule extcall_decoder_member_head_bound >> simp[]
QED

Theorem extcall_decoder_tuple_head_bound:
  abi_decoder_coherent ce env sf (TupleT tys) (TupleTV tvs) ==>
  SUM (MAP abi_member_head_size (MAP (vyper_to_abi_type env) tys)) <=
    type_memory_bytes ce (TupleT tys)
Proof
  simp[abi_decoder_coherent_tuple_iff] >> strip_tac >>
  drule extcall_decoder_members_head_bound >>
  gvs[abi_decoder_header_def, valueEncodingTheory.type_memory_size_def]
QED

Theorem extcall_decoder_struct_head_bound:
  abi_decoder_coherent ce env sf (StructT nsid) atv /\
  FLOOKUP env nsid = SOME (StructArgs args) ==>
  SUM (MAP abi_member_head_size
    (MAP (vyper_to_abi_type (env \\ nsid)) (MAP SND args))) <=
    type_memory_bytes ce (StructT nsid)
Proof
  simp[abi_decoder_coherent_struct_iff] >> rpt strip_tac >> gvs[] >>
  qpat_x_assum `LIST_REL _ _ tvs` assume_tac >>
  `LENGTH (MAP (\(name,ty,sz). (name,ty)) fields) = LENGTH tvs` by
    metis_tac[LIST_REL_LENGTH, LENGTH_MAP] >>
  drule extcall_decoder_members_head_bound >>
  gvs[abi_decoder_header_def, valueEncodingTheory.type_memory_size_def,
    decoder_struct_memory_sum]
QED

Theorem extcall_decoder_head_nonwrap:
  headsz <= outsz /\ d + outsz < dimword (:256) ==>
  headsz < dimword (:256)
Proof
  decide_tac
QED

Theorem extcall_decoder_array_head_product_bound:
  abi_decoder_coherent ce env sf (ArrayT ty (Dynamic maxn))
    (ArrayTV tv (Dynamic maxn)) /\ c <= maxn /\
  d + type_memory_bytes ce (ArrayT ty (Dynamic maxn)) < dimword (:256) ==>
  32 + c * abi_member_head_size (vyper_to_abi_type env ty) < dimword (:256)
Proof
  strip_tac >>
  `abi_decoder_coherent ce env sf ty tv` by
    gvs[abi_decoder_coherent_array_iff] >>
  drule extcall_decoder_member_head_bound >> strip_tac >>
  `c * abi_member_head_size (vyper_to_abi_type env ty) <= maxn * type_memory_size tv` by
    (irule LESS_MONO_MULT2 >> simp[]) >>
  qpat_assum `abi_decoder_coherent _ _ _ (ArrayT _ _) _`
    (mp_tac o MATCH_MP abi_decoder_coherent_header) >>
  simp[abi_decoder_header_def, valueEncodingTheory.type_memory_size_def] >>
  strip_tac >> decide_tac
QED

(* A range guard cannot mistake a once-wrapped endpoint for a forward one. *)
Theorem extcall_decoder_guard_endpoint_bound:
  !a q H modulus:num. a <= H /\ H < modulus /\ q < modulus /\
    a <= (a+q) MOD modulus /\ (a+q) MOD modulus <= H ==> a+q <= H
Proof
  rpt strip_tac >> Cases_on `a+q < modulus`
  >- gvs[LESS_MOD] >>
  `(a+q) MOD modulus = a+q-modulus` by
    (irule MOD_UNIQUE >> qexists_tac `1` >> simp[] >> decide_tac) >>
  decide_tac
QED
