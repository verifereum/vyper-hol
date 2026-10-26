(* Positional struct inputs for the shared complex decoder.
   TOP-LEVEL: abi_decoder_struct_inputs.
   Helpers: conversion shape, member alignment and field memory size. *)
Theory abiDecoderStructInputs
Ancestors
  abiDecoderPreObservations abiDecoderStructMembers abiDecoderMembers abiDecoderMemberInfos
  abiDecoderCoherence abiDecoderTypedContract abiDecoderContract abiDecoderReentry
  compileEnv valueEncoding vyperABI contractABI venomState words list pair

Theorem abi_decoder_struct_values:
  abi_to_vyper env (StructT nsid) av = SOME v ==>
  ?avs fields. av = ListV avs /\ v = StructV fields
Proof
  Cases_on `av` >> simp[Once abi_to_vyper_def, AllCaseEqs()] >> metis_tac[]
QED

Theorem type_memory_size_fields_zip:
  !names tvs. LENGTH names = LENGTH tvs ==>
    type_memory_size_fields (ZIP (names,tvs)) = type_memory_size_list tvs
Proof
  Induct >> Cases_on `tvs` >> simp[type_memory_size_def]
QED

Theorem abi_decoder_struct_members_at:
  abi_decoder_coherent ce env sf (StructT nsid) (StructTV (ZIP (MAP FST args,tvs))) /\
  FLOOKUP env nsid = SOME (StructArgs args) /\ LENGTH tvs = LENGTH args /\
  abi_decoder_metadata ce env (StructT nsid) (StructTV (ZIP (MAP FST args,tvs)))
    di (ListV avs) (StructV fields) ==>
  abi_decoder_members ce (env \\ nsid) (sf \\ nsid_to_string nsid)
    (MAP SND args) tvs avs (MAP SND fields)
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  drule_all abi_decoder_struct_members >> strip_tac >>
  rename1 `StructTV (ZIP (MAP FST args,tvs)) = StructTV (ZIP (MAP FST args,actual_tvs))` >>
  drule abi_decoder_members_lengths >> strip_tac >>
  `ZIP (MAP FST args,tvs) = ZIP (MAP FST args,actual_tvs)` by fs[] >>
  `MAP SND (ZIP (MAP FST args,tvs)) = MAP SND (ZIP (MAP FST args,actual_tvs))`
    by asm_simp_tac bool_ss [] >>
  gvs[MAP_ZIP]
QED

Theorem abi_decoder_struct_field_types:
  abi_decoder_coherent ce env sf (StructT nsid) tv /\
  FLOOKUP env nsid = SOME (StructArgs args) ==>
  ?cfields. FLOOKUP sf (nsid_to_string nsid) = SOME cfields /\
    MAP (FST o SND) cfields = MAP SND args
Proof
  simp_tac bool_ss [abi_decoder_coherent_struct_iff] >> strip_tac >> gvs[] >>
  `!fs:(string # vyperAST$type # num) list.
    MAP (FST o SND) fs = MAP SND (MAP (\(name,ty,sz). (name,ty)) fs)` by
    (Induct >> simp[FORALL_PROD, combinTheory.o_DEF]) >>
  metis_tac[]
QED

Theorem abi_decoder_struct_inputs:
  FLOOKUP env nsid = SOME (StructArgs args) /\ LENGTH tvs = LENGTH args /\
  abi_decoder_recursive_pre ce env sf (StructT nsid) (StructTV (ZIP (MAP FST args,tvs)))
    di av v st last src dst opc hi sb d b cap (abi_decoder_prune_vars st.cs_next_var initial) ==>
  ?cfields avs fields.
    FLOOKUP sf (nsid_to_string nsid) = SOME cfields /\
    MAP (FST o SND) cfields = MAP SND args /\
    av = ListV avs /\ v = StructV fields /\
    value_has_type (StructTV (ZIP (MAP FST args,tvs))) (StructV fields) /\
    abi_decoder_members ce (env \\ nsid) (sf \\ nsid_to_string nsid)
      (MAP SND args) tvs avs (MAP SND fields) /\
    type_memory_bytes ce (StructT nsid) = SUM (MAP (type_memory_bytes ce) (MAP SND args)) /\
    abi_decoder_ranges opc hi src dst sb
      (LENGTH (enc (Tuple (MAP (vyper_to_abi_type (env \\ nsid)) (MAP SND args))) (ListV avs)))
      d (SUM (MAP (type_memory_bytes ce) (MAP SND args))) b cap initial /\
    mem_bytes_at sb
      (LENGTH (enc (Tuple (MAP (vyper_to_abi_type (env \\ nsid)) (MAP SND args))) (ListV avs)))
      (abi_decode_source opc initial) =
        enc (Tuple (MAP (vyper_to_abi_type (env \\ nsid)) (MAP SND args))) (ListV avs) /\
    abi_decoder_operand_live st.cs_next_var src /\ abi_decoder_operand_live st.cs_next_var dst /\
    abi_decoder_operand_live st.cs_next_var hi
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  drule abi_decoder_pre_observations >> strip_tac >>
  qpat_assum `abi_decoder_metadata _ _ _ _ _ _ _`
    (MAP_EVERY assume_tac o CONJUNCTS o PURE_REWRITE_RULE [abi_decoder_metadata_def]) >>
  drule abi_decoder_struct_values >> strip_tac >> gvs[Excl "enc_def"] >>
  drule_all abi_decoder_struct_members_at >> strip_tac >>
  drule abi_decoder_members_relations >> strip_tac >>
  drule abi_decoder_member_infos_layout >> strip_tac >>
  `type_memory_size_fields (ZIP (MAP FST args,tvs)) = type_memory_size_list tvs` by
    (irule type_memory_size_fields_zip >> simp[]) >>
  `type_memory_bytes ce (StructT nsid) = SUM (MAP (type_memory_bytes ce) (MAP SND args))` by
    fs[Once type_memory_size_def, Excl "enc_def"] >>
  drule_all abi_decoder_struct_field_types >> strip_tac >>
  qexists_tac `cfields` >>
  gvs[Once vyper_to_abi_type_def, vyper_to_abi_types_MAP, Excl "enc_def"]
QED

val () = List.app (fn (n,th) =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th) in
    if null (Thm.hyp th) andalso null axioms andalso
       List.all (fn s => s = "DISK_THM") oracles then
      print ("ABI_DECODER_STRUCT_INPUTS_KERNEL_CLOSED " ^ n ^ "\n")
    else raise Fail ("ABI struct inputs not kernel closed: " ^ n)
  end) (DB.thms "abiDecoderStructInputs");
