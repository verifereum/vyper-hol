(* Canonical and typed inputs for recursive array initialization. *)
Theory abiDecoderRecursiveArrayFacts
Ancestors
  abiDecoderCoherence abiDecoderTypedContract abiDecoderArrayInvariant abiDecoderReentry
  abiDecoderArrayInitReentry abiDecoderContract abiDecoderPrimitiveArrayReentryInit
  abiCanonicalArrayLoad abiDecodeRanges compileEnv valueEncoding vyperABI
  vyperTyping vyperValue contractABI venomState words list arithmetic

Theorem abi_decoder_array_capacity_arithmetic:
  !n sz limit:num. 0 < sz /\ 1 + n * sz < limit ==> n < limit
Proof
  rpt strip_tac >> Cases_on `sz` >> gvs[MULT_CLAUSES] >> decide_tac
QED

Theorem abi_decoder_coherent_array_capacity:
  abi_decoder_coherent ce env sf (ArrayT ty (Dynamic maxn)) (ArrayTV tv (Dynamic maxn)) ==>
  maxn < dimword (:256)
Proof
  strip_tac >>
  `evaluate_type env (ArrayT ty (Dynamic maxn)) = SOME (ArrayTV tv (Dynamic maxn))` by
    metis_tac[abi_decoder_coherent_header, abi_decoder_header_def] >>
  `0 < type_slot_size tv /\ type_slot_size (ArrayTV tv (Dynamic maxn)) < dimword (:256)` by
    (qpat_x_assum `evaluate_type env (ArrayT _ _) = _` mp_tac >>
     simp[Once evaluate_type_def, AllCaseEqs()]) >>
  irule abi_decoder_array_capacity_arithmetic >> qexists_tac `type_slot_size tv` >>
  fs[type_slot_size_def]
QED

Theorem abi_decoder_array_encoding_head_bound:
  has_type (Array NONE aty) (ListV avs) ==>
  32 + LENGTH avs * abi_member_head_size aty <= LENGTH (enc (Array NONE aty) (ListV avs))
Proof
  strip_tac >> drule canonical_array_length >> simp_tac bool_ss [] >> strip_tac >> decide_tac
QED

Theorem abi_decoder_array_pre_observations:
  abi_decoder_recursive_pre ce env sf (ArrayT ty (Dynamic maxn)) (ArrayTV tv (Dynamic maxn))
    di (ListV avs) (ArrayV (DynArrayV vs)) st last src dst opc hi sb d b cap
    (abi_decoder_prune_vars st.cs_next_var initial) ==>
  abi_decoder_coherent ce env sf (ArrayT ty (Dynamic maxn)) (ArrayTV tv (Dynamic maxn)) /\
  abi_decoder_metadata ce env (ArrayT ty (Dynamic maxn)) (ArrayTV tv (Dynamic maxn))
    (type_to_abi_dec_info ce.ce_struct_fields ce (ArrayT ty (Dynamic maxn)))
    (ListV avs) (ArrayV (DynArrayV vs)) /\
  abi_decoder_ranges opc hi src dst sb
    (LENGTH (enc (Array NONE (vyper_to_abi_type env ty)) (ListV avs)))
    d (type_memory_bytes ce (ArrayT ty (Dynamic maxn))) b cap initial /\
  mem_bytes_at sb (LENGTH (enc (Array NONE (vyper_to_abi_type env ty)) (ListV avs)))
    (abi_decode_source opc initial) = enc (Array NONE (vyper_to_abi_type env ty)) (ListV avs) /\
  abi_decoder_operand_live st.cs_next_var src /\ abi_decoder_operand_live st.cs_next_var dst /\
  abi_decoder_operand_live st.cs_next_var hi
Proof
  strip_tac >> qpat_assum `abi_decoder_recursive_pre _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _`
    (MAP_EVERY assume_tac o CONJUNCTS o PURE_REWRITE_RULE [abi_decoder_recursive_pre_def]) >>
  drule abi_decoder_pre_pruned_operands >> strip_tac >>
  qpat_assum `abi_decoder_pre _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _`
    (MAP_EVERY assume_tac o CONJUNCTS o PURE_REWRITE_RULE [abi_decoder_pre_def]) >>
  `abi_decoder_ranges opc hi src dst sb
    (LENGTH (enc (Array NONE (vyper_to_abi_type env ty)) (ListV avs)))
    d (type_memory_bytes ce (ArrayT ty (Dynamic maxn))) b cap initial` by
    (qpat_x_assum `abi_decoder_ranges _ _ _ _ _ _ _ _ _ _ _` mp_tac >>
     asm_simp_tac bool_ss [abi_decoder_prune_ranges, Once vyper_to_abi_type_def]) >>
  asm_simp_tac bool_ss [] >>
  fs[abi_decoder_prune_source, Once vyper_to_abi_type_def, Excl "enc_def"]
QED

Theorem abi_decoder_recursive_array_init_inputs:
  abi_decoder_coherent ce env sf (ArrayT ty (Dynamic maxn)) (ArrayTV tv (Dynamic maxn)) /\
  abi_decoder_metadata ce env (ArrayT ty (Dynamic maxn)) (ArrayTV tv (Dynamic maxn))
    parent_di (ListV avs) (ArrayV (DynArrayV vs)) /\
  abi_decoder_ranges opc hi src dst sb
    (LENGTH (enc (Array NONE (vyper_to_abi_type env ty)) (ListV avs)))
    d (type_memory_bytes ce (ArrayT ty (Dynamic maxn))) b cap initial /\
  mem_bytes_at sb (LENGTH (enc (Array NONE (vyper_to_abi_type env ty)) (ListV avs)))
    (abi_decode_source opc initial) = enc (Array NONE (vyper_to_abi_type env ty)) (ListV avs) ==>
  abi_decode_source_opcode opc /\ eval_operand src initial = SOME (n2w sb) /\
  eval_operand dst initial = SOME (n2w d) /\ d < dimword (:256) /\
  abi_decode_load opc (n2w sb:bytes32) initial = n2w (LENGTH vs) /\
  LENGTH vs <= maxn /\ maxn < dimword (:256) /\
  (hi = Lit 0w \/ ?h. eval_operand hi initial = SOME (n2w h) /\
    sb + 32 + LENGTH vs * abi_embedded_static_size ce.ce_struct_fields ty <= h /\
    h < dimword (:256)) /\ (d + 32 <= b \/ b + cap <= d)
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  drule abi_decoder_dynarray_values >> strip_tac >>
  drule abi_decoder_coherent_array_capacity >> strip_tac >>
  `abi_decoder_coherent ce env sf ty tv` by fs[abi_decoder_coherent_array_iff] >>
  `abi_embedded_static_size ce.ce_struct_fields ty = abi_member_head_size (vyper_to_abi_type env ty)`
    by metis_tac[abi_decoder_coherent_header, abi_decoder_header_def] >>
  `32 + LENGTH vs * abi_embedded_static_size ce.ce_struct_fields ty <=
    LENGTH (enc (Array NONE (vyper_to_abi_type env ty)) (ListV avs))` by
    (drule abi_decoder_array_encoding_head_bound >> asm_simp_tac bool_ss []) >>
  qpat_assum `abi_decoder_ranges _ _ _ _ _ _ _ _ _ _ _`
    (MAP_EVERY assume_tac o CONJUNCTS o PURE_REWRITE_RULE [abi_decoder_ranges_def]) >>
  drule_all canonical_dynamic_array_count_load >> strip_tac >>
  `d < dimword (:256)` by decide_tac >>
  SUBGOAL_THEN ``d + 32 <= b \/ b + cap <= d`` assume_tac
  >- (qpat_x_assum `d + type_memory_bytes ce (ArrayT ty (Dynamic maxn)) <= b \/ _` mp_tac >>
      simp_tac bool_ss [Once type_memory_bytes_def] >> strip_tac >> decide_tac) >>
  SUBGOAL_THEN ``hi = Lit 0w \/ ?h. eval_operand hi initial = SOME (n2w h) /\
    sb + 32 + LENGTH (vs:vyperValue$value list) * abi_embedded_static_size ce.ce_struct_fields ty <= h /\
    h < dimword (:256)`` assume_tac
  >- (Cases_on `hi = Lit 0w` >- simp[] >>
      qpat_x_assum `hi = Lit 0w \/ _` mp_tac >> asm_simp_tac bool_ss [] >> strip_tac >>
      qexists_tac `h` >> asm_simp_tac bool_ss [] >>
      qpat_x_assum `32 + LENGTH vs * abi_embedded_static_size ce.ce_struct_fields ty <= _` mp_tac >>
      asm_simp_tac bool_ss [] >> decide_tac) >>
  asm_simp_tac bool_ss [] >> metis_tac[]
QED

val () = List.app (fn (n,th) =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th) in
    if null (Thm.hyp th) andalso null axioms andalso
       List.all (fn s => s = "DISK_THM") oracles then
      print ("ABI_DECODER_RECURSIVE_ARRAY_FACTS_KERNEL_CLOSED " ^ n ^ "\n")
    else raise Fail ("ABI recursive array facts not kernel closed: " ^ n)
  end) (DB.thms "abiDecoderRecursiveArrayFacts");
