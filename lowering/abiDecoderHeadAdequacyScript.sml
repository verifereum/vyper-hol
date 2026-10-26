(* The child-head bound required by bounded dynamic-array pointer execution. *)
Theory abiDecoderHeadAdequacy
Ancestors
  abiCanonicalHeadSize abiDecoderCoherence abiDecodeRanges vyperABI vyperValue
  valueEncoding contractABI words arithmetic

Theorem base_abi_type_not_array[local]:
  !bt bound aty. vyper_base_to_abi_type bt <> Array bound aty
Proof
  Cases >> simp[vyper_base_to_abi_type_def] >>
  rename1 `vyper_base_to_abi_type (BytesT bd)` >> Cases_on `bd` >>
  simp[vyper_base_to_abi_type_def]
QED

Theorem evaluated_positive_type_excludes_empty_abi_array:
  evaluate_type env ty = SOME tv /\ 0 < type_slot_size tv ==>
  !elem. vyper_to_abi_type env ty <> Array (SOME 0) elem
Proof
  Cases_on `ty` >> simp[vyper_to_abi_type_def, AllCaseEqs()] >|
  [simp[base_abi_type_not_array],
   rename1 `evaluate_type env (ArrayT elem bound)` >> Cases_on `bound` >>
   gvs[vyper_to_abi_type_def, Once evaluate_type_def, type_slot_size_def,
       AllCaseEqs()] >> CCONTR_TAC >> gvs[type_slot_size_def]]
QED

Theorem abi_decoder_positive_child_head_adequate:
  abi_decoder_coherent ce env sf ty tv /\ 0 < type_slot_size tv /\
  has_type (vyper_to_abi_type env ty) av ==>
  abi_embedded_static_size ce.ce_struct_fields ty <=
    LENGTH (enc (vyper_to_abi_type env ty) av)
Proof
  strip_tac >> drule abi_decoder_coherent_header >>
  simp_tac bool_ss [abi_decoder_header_def] >> strip_tac >>
  `!elem. vyper_to_abi_type env ty <> Array (SOME 0) elem` by
    (drule_all evaluated_positive_type_excludes_empty_abi_array >> simp[]) >>
  Cases_on `is_dynamic (vyper_to_abi_type env ty)`
  >- (drule_all canonical_dynamic_encoding_head_min >>
      simp[abi_member_head_size_def]) >>
  drule_all (cj 1 enc_has_static_length) >> simp[abi_member_head_size_def]
QED

Theorem abi_decoder_array_child_head_adequate:
  abi_decoder_coherent ce env sf (ArrayT ty bound) (ArrayTV tv bound) /\
  has_type (vyper_to_abi_type env ty) av ==>
  abi_embedded_static_size ce.ce_struct_fields ty <=
    LENGTH (enc (vyper_to_abi_type env ty) av)
Proof
  strip_tac >>
  `abi_decoder_coherent ce env sf ty tv` by
    gvs[abi_decoder_coherent_array_iff] >>
  `evaluate_type env (ArrayT ty bound) = SOME (ArrayTV tv bound)` by
    metis_tac[abi_decoder_coherent_header, abi_decoder_header_def] >>
  `0 < type_slot_size tv` by
    (qpat_x_assum `evaluate_type env (ArrayT ty bound) = _` mp_tac >>
     simp[Once evaluate_type_def, AllCaseEqs()]) >>
  drule_all abi_decoder_positive_child_head_adequate >> simp[]
QED

val () = List.app (fn (n,th) =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th) in
    if null (Thm.hyp th) andalso null axioms andalso
       List.all (fn s => s = "DISK_THM") oracles then
      print ("ABI_DECODER_HEAD_ADEQUACY_KERNEL_CLOSED " ^ n ^ "\n")
    else raise Fail ("ABI decoder child-head adequacy not kernel closed: " ^ n)
  end) (DB.thms "abiDecoderHeadAdequacy");
