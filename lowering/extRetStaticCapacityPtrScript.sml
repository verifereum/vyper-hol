Theory extRetStaticCapacityPtr
Ancestors
  extRetStaticFrameMetadataPtr returnMetadataPtr vyperABI contractABI
  valueEncoding valueEncodingProofs vyperValue vyperTypeDefaults list rich_list finite_map

Theorem evaluated_abi_dynamic:
  (!tenv ty tv. evaluate_type tenv ty = SOME tv ==>
    is_dynamic (vyper_to_abi_type tenv ty) = vyper_is_dynamic tenv ty) /\
  (!tenv ts acc tvs. evaluate_types tenv ts acc = SOME tvs ==>
    any_dynamic (vyper_to_abi_types tenv ts) = vyper_any_dynamic tenv ts)
Proof
  ho_match_mp_tac evaluate_type_ind >> rpt conj_tac >> rpt gen_tac >>
  simp[evaluate_type_def, vyper_is_dynamic_def, AllCaseEqs(), PULL_EXISTS] >>
  rpt strip_tac >> gvs[vyper_is_dynamic_def]
  >~ [`ArrayT ty bd`] >- (Cases_on `bd` >> gvs[vyper_is_dynamic_def])
QED

Theorem static_abi_memory_size_mutual[local]:
  (!tenv ty tv. evaluate_type tenv ty = SOME tv /\
     ~is_dynamic (vyper_to_abi_type tenv ty) ==>
     vyper_abi_size_bound tenv ty = type_memory_size tv) /\
  (!tenv ts acc tvs. evaluate_types tenv ts acc = SOME tvs /\
     ~any_dynamic (vyper_to_abi_types tenv ts) ==>
     vyper_abi_size_bound_list tenv ts + type_memory_size_list acc =
       type_memory_size_list tvs)
Proof
  ho_match_mp_tac evaluate_type_ind >> rpt conj_tac >> rpt gen_tac >>
  simp[evaluate_type_def, vyper_abi_size_bound_def, type_memory_size_def,
       vyper_is_dynamic_def, AllCaseEqs(), PULL_EXISTS] >>
  rpt strip_tac >> gvs[vyper_abi_size_bound_def, type_memory_size_def,
    vyper_is_dynamic_def]
  >~ [`ArrayT ty bd`]
  >- (Cases_on `bd` >> gvs[vyper_abi_size_bound_def, type_memory_size_def] >>
      drule (cj 1 evaluated_abi_dynamic) >> simp[])
  >~ [`ZIP (MAP FST args,tvs)`]
  >- (drule evaluate_types_length >> simp[] >> strip_tac >>
      simp[type_memory_size_list_sum, type_memory_size_fields_sum,
           GSYM MAP_MAP_o, MAP_ZIP])
  >~ [`REVERSE acc`]
  >- simp[type_memory_size_list_sum, MAP_REVERSE, SUM_REVERSE]
  >> drule (cj 1 evaluated_abi_dynamic) >> simp[]
QED

Theorem evaluated_static_abi_memory_size:
  !tenv ty tv. evaluate_type tenv ty = SOME tv /\
    ~is_dynamic (vyper_to_abi_type tenv ty) ==>
    vyper_abi_size_bound tenv ty = type_memory_size tv
Proof
  metis_tac[static_abi_memory_size_mutual]
QED

Theorem external_frame_abicopy_capacity:
  set_external_package_target target
    (package_external_fn tops use_trans keys
      (mut, nr, rr, name, args, defaults, ret, fbody)) =
    (lbl, cenv0, pos, cds, payable, nr', key, ut, view, fbody', rt) /\
  compile_register_positional_args cenv0 pos off st = (cenv, sa) /\
  same_frame cenv next /\ source_typing_ok tops am tx /\
  assignable_type (type_env tops) ret /\ ret <> NoneT /\
  next.ce_ret_enc_info = AbiCopy m ==>
  m = next.ce_max_return_size
Proof
  strip_tac >> drule_all external_frame_abicopy_layout >> strip_tac >>
  drule source_typing_distinct_type_keys >> strip_tac >>
  drule_all external_frame_return_size >>
  drule_all evaluated_static_abi_memory_size >> simp[]
QED
