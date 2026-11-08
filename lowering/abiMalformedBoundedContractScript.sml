(* Independent ABI-capacity premise for malformed constructor contracts. *)
Theory abiMalformedBoundedContract
Ancestors
  abiMalformedConstructorInduction abiMalformedParentContracts
  abiDecoderCoherence abiDecoderMemberInfos abiCallerAbiShape abiCallerAbiBound
  extcallReturnInterface abiDecoderLayoutBounds compileEnv exprLowering
  abiDecodeRanges vyperABI valueEncoding contractABI words list arithmetic

Definition abi_malformed_bounded_type_contract_def:
  abi_malformed_bounded_type_contract ce env sf ty tv <=>
    !di ctx func cenv cx es st en base_op hi src dst outsz.
      type_to_abi_dec_info sf ce ty = di /\
      compile_abi_decode_to_buf dst src MLOAD base_op hi di st = ((),en) /\
      (?av. has_type (vyper_to_abi_type env ty) av) /\
      assignable_type env ty /\ type_memory_size tv < dimword (:256) /\
      abi_size_bound sf ty < dimword (:256) /\
      fn_inst_ids_distinct func /\ fn_has_code st en func /\
      type_memory_bytes ce ty <= outsz ==>
      abi_malformed_constructor env ty di ctx func cenv cx es st en
        base_op hi src dst outsz
End

Theorem abi_malformed_unbounded_implies_bounded:
  abi_malformed_type_contract ce env sf ty tv ==>
  abi_malformed_bounded_type_contract ce env sf ty tv
Proof
  simp[abi_malformed_type_contract_def, abi_malformed_bounded_type_contract_def]
QED

Theorem abi_malformed_return_root_bound:
  expr_body_pre cenv cx env
    (Call ann (ExtCall stat skip (fname,arg_types,ret_type) opts) args dflt) es ==>
  abi_size_bound cenv.ce_struct_fields
    (if needs_external_call_wrap ret_type then TupleT [ret_type] else ret_type)
      < dimword (:256)
Proof
  strip_tac >> drule extcall_return_type_bounds >> strip_tac >>
  fs[dimword_def] >> decide_tac
QED

Theorem abi_malformed_coherent_shape_and_bound:
  !ce env sf ty tv. abi_decoder_coherent ce env sf ty tv ==>
    abi_caller_abi_shape sf env ty /\ abi_caller_abi_bound sf env ty
Proof
  ho_match_mp_tac abi_decoder_coherent_strongind >>
  rpt conj_tac >> rpt gen_tac >> strip_tac
  >- simp[abi_caller_abi_shape_base, abi_caller_abi_bound_base]
  >- (simp[abi_caller_abi_shape_def, abi_caller_abi_bound_def,
       is_abi_dynamic_def, abi_static_size_def, abi_size_bound_def,
       vyper_is_dynamic_def, vyper_abi_size_bound_def,
       vyper_to_abi_type_def, is_dynamic_def])
  >- metis_tac[abi_caller_abi_shape_array, abi_caller_abi_bound_array]
  >- (conj_tac
      >- (irule abi_caller_abi_shape_tuple >>
          fs[LIST_REL_EL_EQN, EVERY_EL] >> metis_tac[])
      >> irule abi_caller_abi_bound_tuple >>
      fs[LIST_REL_EL_EQN, EVERY_EL] >> metis_tac[])
  >> conj_tac
  >- (irule abi_caller_abi_shape_struct >> goal_assum (drule_at Any) >>
      goal_assum (drule_at Any) >> simp[] >>
      fs[LIST_REL_EL_EQN, EVERY_EL] >> metis_tac[])
  >> irule abi_caller_abi_bound_struct >> goal_assum (drule_at Any) >>
     goal_assum (drule_at Any) >> simp[] >>
     fs[LIST_REL_EL_EQN, EVERY_EL] >> metis_tac[]
QED

Theorem abi_malformed_coherent_member_capacity:
  abi_decoder_coherent ce env sf ty tv ==>
  abi_member_head_size (vyper_to_abi_type env ty) <=
    abi_embedded_static_size sf ty +
      (if is_abi_dynamic sf ty then abi_size_bound sf ty else 0) /\
  abi_size_bound sf ty <=
    abi_embedded_static_size sf ty +
      (if is_abi_dynamic sf ty then abi_size_bound sf ty else 0)
Proof
  strip_tac >> drule abi_malformed_coherent_shape_and_bound >>
  simp[abi_caller_abi_shape_def, abi_caller_abi_bound_def,
       abi_embedded_static_size_def, abi_member_head_size_def] >>
  strip_tac >> Cases_on `is_dynamic (vyper_to_abi_type env ty)` >> gvs[]
QED

Theorem abi_malformed_members_capacity:
  !tys tvs. LIST_REL (abi_decoder_coherent ce env sf) tys tvs ==>
  SUM (MAP abi_member_head_size (MAP (vyper_to_abi_type env) tys)) <=
    SUM (MAP (\ty. abi_embedded_static_size sf ty +
      (if is_abi_dynamic sf ty then abi_size_bound sf ty else 0)) tys) /\
  (!ty. MEM ty tys ==> abi_size_bound sf ty <=
    SUM (MAP (\ty. abi_embedded_static_size sf ty +
      (if is_abi_dynamic sf ty then abi_size_bound sf ty else 0)) tys))
Proof
  Induct_on `tys` >> gen_tac >> Cases_on `tvs` >> simp[] >> strip_tac >>
  first_x_assum drule >> strip_tac >>
  drule abi_malformed_coherent_member_capacity >> strip_tac >>
  conj_tac >- metis_tac[LESS_EQ_LESS_EQ_MONO] >>
  qx_gen_tac `ty` >> strip_tac
  >- (gvs[] >> irule LESS_EQ_TRANS >>
      goal_assum (drule_at Any) >> simp[]) >>
  first_x_assum drule >> strip_tac >>
  irule LESS_EQ_TRANS >> goal_assum (drule_at Any) >> simp[]
QED

Theorem abi_malformed_tuple_capacity:
  LIST_REL (abi_decoder_coherent ce env sf) tys tvs /\
  abi_size_bound sf (TupleT tys) < limit ==>
  SUM (MAP abi_member_head_size (MAP (vyper_to_abi_type env) tys)) < limit /\
  EVERY (\ty. abi_size_bound sf ty < limit) tys
Proof
  strip_tac >> drule abi_malformed_members_capacity >>
  fs[Once abi_size_bound_def, EVERY_MEM] >> metis_tac[LESS_EQ_LESS_TRANS]
QED

Theorem abi_malformed_struct_capacity:
  FLOOKUP sf (nsid_to_string nsid) = SOME fields /\
  MAP (\(name,ty,sz). (name,ty)) fields = args /\
  LIST_REL (abi_decoder_coherent ce (env \\ nsid) (sf \\ nsid_to_string nsid))
    (MAP SND args) tvs /\
  abi_size_bound sf (StructT nsid) < limit ==>
  SUM (MAP abi_member_head_size (MAP (vyper_to_abi_type (env \\ nsid))
    (MAP SND args))) < limit /\
  EVERY (\ty. abi_size_bound (sf \\ nsid_to_string nsid) ty < limit) (MAP SND args)
Proof
  strip_tac >> drule_all abi_caller_struct_map_field_types >> strip_tac >>
  `abi_size_bound sf (StructT nsid) =
   SUM (MAP (\ty. abi_embedded_static_size (sf \\ nsid_to_string nsid) ty +
      (if is_abi_dynamic (sf \\ nsid_to_string nsid) ty
       then abi_size_bound (sf \\ nsid_to_string nsid) ty else 0)) (MAP SND args))` by
    simp[Once abi_size_bound_def] >>
  drule abi_malformed_members_capacity >> strip_tac >>
  fs[EVERY_MEM] >> metis_tac[LESS_EQ_LESS_TRANS]
QED

Theorem abi_malformed_array_capacity:
  abi_decoder_coherent ce env sf ty tv /\
  abi_size_bound sf (ArrayT ty bound) < limit ==>
  (case bound of Fixed n => n | Dynamic n => n) *
    abi_member_head_size (vyper_to_abi_type env ty) < limit /\
  (0 < (case bound of Fixed n => n | Dynamic n => n) ==>
    abi_size_bound sf ty < limit)
Proof
  strip_tac >> drule abi_malformed_coherent_member_capacity >> strip_tac >>
  Cases_on `bound` >> fs[Once abi_size_bound_def] >>
  qmatch_asmsub_abbrev_tac `abi_member_head_size _ <= contribution` >>
  `n * contribution < limit` by decide_tac >>
  `abi_member_head_size (vyper_to_abi_type env ty) <= contribution /\
   abi_size_bound sf ty <= contribution` by fs[Abbr `contribution`] >>
  (conj_tac
   >- (irule LESS_EQ_LESS_TRANS >> qexists_tac `n * contribution` >> simp[]) >>
   strip_tac >> irule LESS_EQ_LESS_TRANS >> qexists_tac `n * contribution` >>
   simp[] >> irule LESS_EQ_TRANS >> qexists_tac `contribution` >> simp[] >>
   Cases_on `n` >> fs[MULT_CLAUSES])
QED

Theorem abi_malformed_return_child_bound:
  expr_body_pre cenv cx env
    (Call ann (ExtCall stat skip (fname,arg_types,ret_type) opts) args dflt) es /\
  abi_decoder_coherent cenv tenv cenv.ce_struct_fields ret_type tv ==>
  abi_size_bound cenv.ce_struct_fields ret_type < dimword (:256)
Proof
  strip_tac >> drule abi_malformed_return_root_bound >>
  Cases_on `needs_external_call_wrap ret_type` >> simp[] >> strip_tac >>
  drule abi_malformed_coherent_member_capacity >> strip_tac >>
  fs[Once abi_size_bound_def] >> metis_tac[LESS_EQ_LESS_TRANS]
QED

Theorem abi_malformed_zero_fixed_contract:
  abi_decoder_coherent ce env sf (ArrayT ty (Fixed 0)) (ArrayTV tv (Fixed 0)) ==>
  abi_malformed_bounded_type_contract ce env sf (ArrayT ty (Fixed 0))
    (ArrayTV tv (Fixed 0))
Proof
  strip_tac >> simp[abi_malformed_bounded_type_contract_def] >> rpt strip_tac >>
  `type_to_abi_dec_info sf ce (ArrayT ty (Fixed 0)) =
    DecComplex (is_abi_dynamic ce.ce_struct_fields ty) []` by
    simp[Once type_to_abi_dec_info_def] >>
  gvs[] >> irule abiMalformedConstructorContractTheory.abi_malformed_empty_constructor >>
  metis_tac[]
QED
