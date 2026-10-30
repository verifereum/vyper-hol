(* A typed canonical sequence view shared by tuples, structs and fixed arrays. *)
Theory abiDecoderMembers
Ancestors
  abiDecoderCoherence abiDecoderTypedContract abiDecoderContract abiDecodeRanges
  vyperABI vyperValue vyperTyping vyperTypeDefaults contractABI
  compileEnv valueEncoding list arithmetic

Definition abi_decoder_members_def:
  abi_decoder_members ce env sf [] [] [] [] = T /\
  abi_decoder_members ce env sf (ty::tys) (tv::tvs) (av::avs) (v::vs) =
    (abi_decoder_coherent ce env sf ty tv /\
     abi_decoder_metadata ce env ty tv (type_to_abi_dec_info ce.ce_struct_fields ce ty) av v /\
     abi_decoder_members ce env sf tys tvs avs vs) /\
  abi_decoder_members ce env sf _ _ _ _ = F
End

Theorem abi_decoder_members_lengths:
  !tys tvs avs vs. abi_decoder_members ce env sf tys tvs avs vs ==>
  LENGTH tys = LENGTH tvs /\ LENGTH tys = LENGTH avs /\ LENGTH tys = LENGTH vs
Proof
  Induct_on `tys` >> rpt gen_tac >> Cases_on `tvs` >> Cases_on `avs` >> Cases_on `vs` >>
  simp[abi_decoder_members_def] >> metis_tac[]
QED

Theorem abi_decoder_members_append:
  !pretys pretvs preavs prevs.
  LENGTH pretys = LENGTH pretvs /\ LENGTH pretys = LENGTH preavs /\ LENGTH pretys = LENGTH prevs ==>
  (abi_decoder_members ce env sf (pretys ++ tys) (pretvs ++ tvs) (preavs ++ avs) (prevs ++ vs) <=>
   abi_decoder_members ce env sf pretys pretvs preavs prevs /\
   abi_decoder_members ce env sf tys tvs avs vs)
Proof
  Induct_on `pretys` >> rpt gen_tac >>
  Cases_on `pretvs` >> Cases_on `preavs` >> Cases_on `prevs` >>
  simp[abi_decoder_members_def, CONJ_ASSOC]
QED

Theorem abi_decoder_members_relations:
  !tys tvs avs vs. abi_decoder_members ce env sf tys tvs avs vs ==>
  LIST_REL (abi_decoder_coherent ce env sf) tys tvs /\
  LIST_REL value_has_type tvs vs /\ LIST_REL has_type (MAP (vyper_to_abi_type env) tys) avs /\
  abi_to_vyper_list env tys avs = SOME vs /\
  MAP type_memory_size tvs = MAP (type_memory_bytes ce) tys
Proof
  Induct_on `tys` >> rpt gen_tac >> Cases_on `tvs` >> Cases_on `avs` >> Cases_on `vs` >>
  simp[abi_decoder_members_def] >> rpt strip_tac >>
  first_x_assum drule_all >> strip_tac >>
  qpat_assum `abi_decoder_metadata _ _ _ _ _ _ _`
    (MAP_EVERY assume_tac o CONJUNCTS o PURE_REWRITE_RULE [abi_decoder_metadata_def]) >>
  asm_simp_tac (srw_ss()) [Once abi_to_vyper_def]
QED

Theorem abi_decoder_members_intro:
  !tys tvs avs vs.
  LIST_REL (abi_decoder_coherent ce env sf) tys tvs /\
  LIST_REL value_has_type tvs vs /\ has_types (MAP (vyper_to_abi_type env) tys) avs /\
  abi_to_vyper_list env tys avs = SOME vs ==>
  abi_decoder_members ce env sf tys tvs avs vs
Proof
  Induct_on `tys` >> rpt gen_tac >> Cases_on `tvs` >> Cases_on `avs` >> Cases_on `vs` >>
  simp[abi_decoder_members_def, has_types_LIST_REL] >>
  rpt strip_tac >> gvs[Once abi_to_vyper_def, AllCaseEqs(), Excl "enc_def"] >>
  FIRST [irule abi_decoder_coherent_root_metadata >> simp[] >> qexists_tac `sf` >> simp[],
    first_x_assum irule >> simp[has_types_LIST_REL]]
QED

Theorem vyper_to_abi_types_MAP:
  !tys. vyper_to_abi_types env tys = MAP (vyper_to_abi_type env) tys
Proof
  Induct >> simp[]
QED

Theorem abi_decoder_tuple_members:
  abi_decoder_coherent ce env sf (TupleT tys) (TupleTV tvs) /\
  abi_decoder_metadata ce env (TupleT tys) (TupleTV tvs) di (ListV avs) (ArrayV (TupleV vs)) ==>
  abi_decoder_members ce env sf tys tvs avs vs
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  `LIST_REL (abi_decoder_coherent ce env sf) tys tvs` by fs[abi_decoder_coherent_tuple_iff] >>
  qpat_assum `abi_decoder_metadata _ _ _ _ _ _ _`
    (MAP_EVERY assume_tac o CONJUNCTS o PURE_REWRITE_RULE [abi_decoder_metadata_def]) >>
  `has_types (MAP (vyper_to_abi_type env) tys) avs` by
    fs[Once vyper_to_abi_type_def, Once has_type_def, vyper_to_abi_types_MAP] >>
  `abi_to_vyper_list env tys avs = SOME vs` by
    (qpat_x_assum `abi_to_vyper env (TupleT _) _ = _` mp_tac >>
     simp[Once abi_to_vyper_def, AllCaseEqs()]) >>
  irule abi_decoder_members_intro >> fs[Once value_has_type_def, values_have_types_LIST_REL]
QED
