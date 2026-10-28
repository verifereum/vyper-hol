(* TOP-LEVEL: a named struct's complete memory layout projects to the
   recursive field encoding under the same source cycle guard. *)
Theory abiMemoryTypedStruct
Ancestors
  abiMemoryTypedDefs abiMemoryEncoding abiFieldSource abiFieldPackedStaticSizes
  memoryValueDefs memoryValueAbiTuple sourceAbiTypingLists valueEncoding
  vyperABI vyperValue vyperTyping vyperTypeValues
  contractABI list pair finite_map arithmetic

Theorem abi_memory_typed_struct_fields:
  !env args tvs fields avs entries source span mem.
    LIST_REL (\ty tv. evaluate_type env ty = SOME tv) (MAP SND args) tvs /\
    memory_fields_rel (ZIP (MAP FST args,tvs)) fields source mem /\
    struct_has_type (ZIP (MAP FST args,tvs)) fields /\
    vyper_to_abi_list env (MAP SND args) (MAP SND fields) = SOME avs /\
    type_memory_size_list tvs <= span /\ abi_typed_fields env (MAP SND args) entries ==>
    abi_memory_encoding (AbiComplex entries) source span mem
      (enc (Tuple (vyper_to_abi_types env (MAP SND args))) (ListV avs))
Proof
  rpt gen_tac >> strip_tac >>
  `LENGTH args = LENGTH tvs` by (drule LIST_REL_LENGTH >> simp[]) >>
  `LENGTH (MAP FST args) = LENGTH tvs` by simp[] >>
  qpat_x_assum `LENGTH (MAP FST args) = LENGTH tvs`
    (ASSUME_TAC o CONJUNCT1 o CONJUNCT2 o MATCH_MP MAP_ZIP) >>
  drule memory_fields_rel_tuple >> DISCH_TAC >>
  drule struct_has_type_tuple >> DISCH_TAC >>
  qpat_assum `MAP SND (ZIP (MAP FST args,tvs)) = tvs`
    (fn th => RULE_ASSUM_TAC (PURE_REWRITE_RULE [th])) >>
  `LIST_REL (\ty av. ~is_dynamic ty ==> LENGTH (enc ty av) = static_length ty)
     (MAP (vyper_to_abi_type env) (MAP SND args)) avs` by
    (qspecl_then [`MAP SND args`, `env`, `tvs`, `MAP SND fields`, `avs`, `source`, `mem`]
       mp_tac memory_tuple_source_static_sizes >> simp[]) >>
  drule enc_tuple_head_size >> DISCH_TAC >>
  asm_simp_tac bool_ss [source_abi_types_map] >> irule abi_memory_encoding_complex >>
  qpat_x_assum `abi_typed_fields env (MAP SND args) entries`
    (mp_tac o REWRITE_RULE [abi_typed_fields_def]) >>
  disch_then (qspecl_then [`tvs`, `MAP SND fields`, `avs`, `source`, `span`, `mem`] mp_tac) >>
  simp[]
QED

val () = List.app (fn (name,th) =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th)
  in if null axioms andalso null (Thm.hyp th) andalso
      List.all (fn s => s = "DISK_THM") oracles
    then () else raise Fail ("unclosed typed ABI struct fields: " ^ name)
  end) (DB.thms "abiMemoryTypedStruct")
