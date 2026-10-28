Theory abiEncoderSourcePrimitive
Ancestors
  abiEncoderSourceAggregate abiEncoderOpenInput vyperABI vyperTyping
  valueEncoding compileEnv contractABI vyperMisc vyperValue

Theorem abi_encoder_copy32_word:
  abi_encoder_open_input (AbiCopy 32) ct rv sb cap mem ==>
  abi_encoder_open_input AbiPrimWord ct rv sb cap mem
Proof
  simp[Once abi_encoder_open_input_cases] >> strip_tac >>
  irule abiEncoderOpenInputTheory.word >> gvs[]
QED

Theorem abi_encoder_word_source_shape:
  is_word_type ty /\ evaluate_type env ty = SOME tv ==>
  ~is_dynamic (vyper_to_abi_type env ty) /\ type_memory_size tv = 32
Proof
  Cases_on `ty` >> simp[is_word_type_def]
  >- (rename1 `BaseT bt` >> Cases_on `bt` >>
      rw[is_word_type_def, evaluate_type_def, vyper_base_to_abi_type_def,
         is_dynamic_def, type_memory_size_def] >>
      gvs[type_memory_size_def] >>
      rename1 `BytesT bound` >> Cases_on `bound` >>
      gvs[is_word_type_def, evaluate_type_def, vyper_base_to_abi_type_def,
          is_dynamic_def, type_memory_size_def])
  >> rw[evaluate_type_def, vyper_to_abi_type_def, AllCaseEqs(),
        is_dynamic_def, type_memory_size_def] >> gvs[type_memory_size_def]
QED

Theorem source_rep_primitive:
  is_word_type ty ==> ?ct. source_rep env ty AbiPrimWord ct
Proof
  strip_tac >> Cases_on `?tv. evaluate_type env ty = SOME tv`
  >- (pop_assum (qx_choose_then `tv` assume_tac) >>
      drule_all abi_encoder_word_source_shape >> strip_tac >>
      drule_all source_rep_static_copy >>
      disch_then (qx_choose_then `ct` assume_tac) >>
      drule_all source_rep_metadata >> strip_tac >>
      qexists_tac `ct` >> simp[source_rep_def] >> rpt strip_tac >>
      drule_all source_rep_transport >> strip_tac >>
      qexists_tac `rv` >> simp[] >>
      irule abi_encoder_copy32_word >> gvs[])
  >> qexists_tac `vyper_to_abi_type env ty` >> simp[source_rep_def] >>
  metis_tac[]
QED

val _ = List.app (fn (name,th) =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th) in
    if List.all (fn s => s = "DISK_THM") oracles andalso null axioms then
      print ("ENCODER_SOURCE_PRIMITIVE_AUDIT_OK " ^ name ^ "\n")
    else raise Fail ("source primitive admission dependency: " ^ name)
  end)
  [("copy32_word", abi_encoder_copy32_word),
   ("word_shape", abi_encoder_word_source_shape),
   ("primitive", source_rep_primitive)];
