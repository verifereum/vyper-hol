(* Uniform source-coherent owned calldata decoder endpoint. *)
Theory calldataUniformOwnedEndpoint
Ancestors
  calldataNonbulkOwnedEndpoint calldataCoherentOwnedEndpoint
  abiDecoderCoherence calldataSourceMemberFold exprLowering list arithmetic

Theorem calldata_coherent_child_contract:
  unit_alloca_budget ctx < dimword (:256) /\
  abi_decoder_coherent ce env sf ty tv ==>
  calldata_member_child_contract ce env sf ctx fn site limit_st ty tv
Proof
  strip_tac >>
  qpat_x_assum `abi_decoder_coherent _ _ _ _ _` mp_tac >>
  map_every qid_spec_tac [`tv`,`ty`,`sf`,`env`,`ce`] >>
  ho_match_mp_tac abi_decoder_coherent_strongind >>
  rpt conj_tac
  >- simp[calldata_base_child_contract]
  >- simp[calldata_flag_child_contract]
  >- suspend "array"
  >- suspend "tuple"
  >> suspend "struct"
QED
Resume calldata_coherent_child_contract[array]:
  rpt gen_tac >> strip_tac >> Cases_on `bound`
  >- (irule calldata_fixed_child_contract >> asm_rewrite_tac[]) >>
  rename1 `Dynamic maxn` >>
  Cases_on `is_abi_dynamic ce.ce_struct_fields ty \/
    dec_info_needs_clamp (type_to_abi_dec_info sf ce ty)`
  >- (irule calldata_nonbulk_array_child_contract >>
      asm_rewrite_tac[] >>
      simp[Once abi_decoder_coherent_cases]) >>
  irule calldata_bulk_child_contract >>
  asm_rewrite_tac[] >>
  simp[Once type_to_abi_dec_info_def] >>
  gvs[]
QED
Resume calldata_coherent_child_contract[tuple]:
  rpt gen_tac >> strip_tac >>
  irule calldata_tuple_child_contract >>
  fs[LIST_REL_EL_EQN] >> metis_tac[]
QED
Resume calldata_coherent_child_contract[struct]:
  rpt gen_tac >> strip_tac >>
  irule calldata_struct_child_contract >>
  fs[LIST_REL_EL_EQN, EL_MAP] >> metis_tac[]
QED
Finalise calldata_coherent_child_contract
