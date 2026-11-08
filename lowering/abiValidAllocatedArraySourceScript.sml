(* Source navigation for allocation-backed dynamic-array success. *)
Theory abiValidAllocatedArraySource
Ancestors
  abiValidAllocatedSource abiValidAggregateHeads abiDecoderValidArraySetupInputs
  abiValidMembers abiDecoderCoherence abiDecoderStruct vyperABIRoundtrip
  abiDecodeRanges abiEncoder vyperABI vyperValue valueEncoding
  contractABI words list rich_list arithmetic

Theorem abi_valid_allocated_array_source_view:
  abi_decoder_coherent ce env sf ty tv /\ LENGTH xs = L /\
  vyper_decode_valid_enc (Array NONE (vyper_to_abi_type env ty)) (DROP p xs) /\
  abi_to_vyper env (ArrayT ty (Dynamic maxn))
    (dec (Array NONE (vyper_to_abi_type env ty)) (DROP p xs)) = SOME v ==>
  ?vs. v = ArrayV (DynArrayV vs) /\
    abi_head_word (DROP p xs) = LENGTH vs /\ LENGTH vs <= maxn /\
    p+32 <= L /\
    p+32+LENGTH vs * abi_member_head_size (vyper_to_abi_type env ty) <= L /\
    vyper_decode_valid_enc_tuple
      (REPLICATE (LENGTH vs) (vyper_to_abi_type env ty))
      (DROP (p+32) xs) (DROP (p+32) xs) /\
    abi_to_vyper_list env (REPLICATE (LENGTH vs) ty)
      (abi_decode_members (REPLICATE (LENGTH vs) (vyper_to_abi_type env ty))
        (DROP (p+32) xs) (DROP (p+32) xs)) = SOME vs
Proof
  strip_tac >> drule abi_valid_dynamic_array_view >> strip_tac >>
  qpat_assum `dec (Array NONE _) _ = _`
    (fn th => RULE_ASSUM_TAC (PURE_REWRITE_RULE [th])) >>
  `evaluate_type env ty = SOME tv` by
    (drule abi_decoder_coherent_header >> simp[abi_decoder_header_def]) >>
  fs[Once abi_to_vyper_def, compatible_bound_def, make_array_value_def,
     AllCaseEqs(), Excl "dec_def", Excl "vyper_decode_valid_enc_def"] >>
  rename1 `abi_to_vyper_list env _ _ = SOME vs` >>
  `LENGTH vs = abi_head_word (DROP p xs)` by
    (drule abi_to_vyper_list_lengths >> simp[]) >>
  qexists_tac `vs` >>
  gvs[DROP_DROP_T, LENGTH_DROP, Excl "dec_def", Excl "vyper_decode_valid_enc_def"] >>
  decide_tac
QED

Theorem abi_valid_allocated_array_member:
  vyper_decode_valid_enc_tuple (REPLICATE n (vyper_to_abi_type env ty)) raw_bytes hds /\
  abi_to_vyper_list env (REPLICATE n ty)
    (abi_decode_members (REPLICATE n (vyper_to_abi_type env ty)) raw_bytes hds) = SOME vs /\
  j < n ==>
  vyper_decode_valid_enc (vyper_to_abi_type env ty)
    (abi_decode_member_bytes (vyper_to_abi_type env ty) raw_bytes
      (DROP (j * abi_member_head_size (vyper_to_abi_type env ty)) hds)) /\
  abi_to_vyper env ty
    (dec (vyper_to_abi_type env ty)
      (abi_decode_member_bytes (vyper_to_abi_type env ty) raw_bytes
        (DROP (j * abi_member_head_size (vyper_to_abi_type env ty)) hds))) = SOME (EL j vs)
Proof
  strip_tac >>
  `REPLICATE n (vyper_to_abi_type env ty) =
    REPLICATE j (vyper_to_abi_type env ty) ++
      vyper_to_abi_type env ty :: REPLICATE (n-SUC j) (vyper_to_abi_type env ty)` by
    (irule abi_decoder_replicate_member >> simp[]) >>
  `vyper_decode_valid_enc_tuple
    (vyper_to_abi_type env ty :: REPLICATE (n-SUC j) (vyper_to_abi_type env ty))
    raw_bytes (DROP (j * abi_member_head_size (vyper_to_abi_type env ty)) hds)` by
    (qpat_assum `REPLICATE n _ = _`
       (fn th => qhdtm_assum `vyper_decode_valid_enc_tuple`
         (mp_tac o PURE_REWRITE_RULE [th])) >>
     disch_then (mp_tac o MATCH_MP abi_valid_members_suffix) >>
     simp[map_replicate, SUM_REPLICATE]) >>
  conj_tac >- (drule abi_valid_member_cons >> simp[]) >>
  drule abi_to_vyper_list_EL >> strip_tac >>
  first_x_assum (qspec_then `j` mp_tac) >>
  simp[EL_REPLICATE, abi_decode_array_member_EL]
QED

Theorem abi_valid_allocated_array_child_position:
  abi_decoder_coherent ce env sf ty tv /\ LENGTH xs = L /\
  p+32+n*abi_member_head_size (vyper_to_abi_type env ty) <= L /\
  vyper_decode_valid_enc_tuple (REPLICATE n (vyper_to_abi_type env ty))
    (DROP (p+32) xs) (DROP (p+32) xs) /\
  abi_to_vyper_list env (REPLICATE n ty)
    (abi_decode_members (REPLICATE n (vyper_to_abi_type env ty))
      (DROP (p+32) xs) (DROP (p+32) xs)) = SOME vs /\ j < n /\
  q = p+32 + (if dec_info_needs_offset (type_to_abi_dec_info sf ce ty)
    then abi_head_word (DROP (p+32+j*abi_member_head_size (vyper_to_abi_type env ty)) xs)
    else j*abi_member_head_size (vyper_to_abi_type env ty)) ==>
  q <= L /\
  vyper_decode_valid_enc (vyper_to_abi_type env ty) (DROP q xs) /\
  abi_to_vyper env ty (dec (vyper_to_abi_type env ty) (DROP q xs)) = SOME (EL j vs) /\
  (is_dynamic (vyper_to_abi_type env ty) \/
    q + static_length (vyper_to_abi_type env ty) <= L)
Proof
  strip_tac >>
  `p+32+j*abi_member_head_size (vyper_to_abi_type env ty) +
    abi_member_head_size (vyper_to_abi_type env ty) <= L` by
    (`SUC j * abi_member_head_size (vyper_to_abi_type env ty) <=
      n * abi_member_head_size (vyper_to_abi_type env ty)` by
      (irule LESS_MONO_MULT2 >> decide_tac) >>
     qpat_x_assum `SUC j * _ <= _` mp_tac >>
     simp_tac bool_ss [MULT_CLAUSES] >> decide_tac) >>
  drule_all abi_valid_allocated_array_member >> strip_tac >>
  fs[DROP_DROP_T] >>
  mp_tac (Q.INST [`p` |-> `p+32`,
    `ao` |-> `j*abi_member_head_size (vyper_to_abi_type env ty)`, `q` |-> `q`]
    abi_valid_source_member_position) >>
  (impl_tac >- simp[]) >>
  strip_tac >> gvs[]
QED

(* Parent coherence supplies output capacity independently of ABI capacity. *)
Theorem abi_valid_allocated_array_memory_size:
  abi_decoder_coherent ce env sf (ArrayT ty (Dynamic maxn))
    (ArrayTV tv (Dynamic maxn)) ==>
  type_memory_bytes ce (ArrayT ty (Dynamic maxn)) =
    32 + maxn * type_memory_size tv
Proof
  strip_tac >> drule abi_decoder_coherent_header >>
  simp[abi_decoder_header_def, type_memory_size_def]
QED

Theorem abi_valid_allocated_array_output_bounds:
  abi_decoder_coherent ce env sf (ArrayT ty (Dynamic maxn))
    (ArrayTV tv (Dynamic maxn)) /\
  n <= maxn /\ outsz = type_memory_bytes ce (ArrayT ty (Dynamic maxn)) ==>
  32 + n * type_memory_size tv <= outsz /\
  (!k. k < n ==> d+32+k*type_memory_size tv+type_memory_size tv <= d+outsz)
Proof
  strip_tac >> drule abi_valid_allocated_array_memory_size >> strip_tac >>
  `n * type_memory_size tv <= maxn * type_memory_size tv` by
    (irule LESS_MONO_MULT2 >> simp[]) >>
  conj_tac >- decide_tac >>
  rpt strip_tac >>
  `SUC k * type_memory_size tv <= n * type_memory_size tv` by
    (irule LESS_MONO_MULT2 >> decide_tac) >>
  qpat_x_assum `SUC k * _ <= _` mp_tac >>
  qpat_x_assum `n * _ <= _` mp_tac >>
  simp_tac bool_ss [MULT_CLAUSES] >> decide_tac
QED
