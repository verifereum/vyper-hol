(* Struct correctness retains distinct full and descending compiler maps. *)
Theory abiDecoderCorrectStruct
Ancestors
  abiDecoderCorrect abiDecoderStruct abiDecoderComplexExecute abiDecoderMemberInfos
  abiDecoderEffect abiDecoderCoherence abiDecoderReentry abiDecoderTypedContract
  abiDecoderContract abiStaticListProps fragExec compileEnv valueEncoding valueEncodingProps
  vyperABI vyperTyping venomState words list

Theorem abi_decoder_correct_struct:
  FLOOKUP env nsid = SOME (StructArgs args) /\
  LIST_REL (abi_decoder_correct ce (env \\ nsid) (sf \\ nsid_to_string nsid))
    (MAP SND args) tvs ==>
  abi_decoder_correct ce env sf (StructT nsid) (StructTV (ZIP (MAP FST args,tvs)))
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  `LENGTH tvs = LENGTH args` by metis_tac[LIST_REL_LENGTH, LENGTH_MAP] >>
  simp_tac bool_ss [abi_decoder_correct_def] >> rpt gen_tac >>
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  drule_all abi_decoder_struct_inputs >> strip_tac >> gvs[Excl "enc_def"] >>
  (drule abi_decoder_struct_infos >> strip_tac >>
  qpat_x_assum `compile_abi_decode_to_buf _ _ _ _ _ _ = _` mp_tac >>
  asm_simp_tac bool_ss [] >> strip_tac >>
  mp_tac (Q.INST [`st` |-> `start`, `final` |-> `end_st`,
    `env` |-> `env \\ nsid`, `sf` |-> `sf \\ nsid_to_string nsid`,
    `tys` |-> `MAP SND (args:(string # vyperAST$type) list)`,
    `vs` |-> `MAP SND (fields:(string # value) list)`,
    `dyn` |-> `EXISTS (is_abi_dynamic ce.ce_struct_fields)
      (MAP SND (args:(string # vyperAST$type) list))`]
    abi_decoder_complex_execute) >>
  impl_tac >- asm_simp_tac bool_ss [] >> strip_tac >>
  rename1 `tuple_in_memory (MAP SND fields) tvs d actual.vs_memory` >>
  `fields_in_memory fields (ZIP (MAP FST args,tvs)) d actual.vs_memory` by
    (irule static_fields_memory_zip >> fs[Once value_has_type_def]) >>
  qexists_tac `actual` >> asm_simp_tac bool_ss [val_in_memory_struct])
QED
