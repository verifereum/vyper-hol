(* Default struct input follows both deleted maps through recursive members. *)
Theory abiEmptyStructInput
Ancestors
  abiEmptyAggregateInput abiEmptyInputLeaves abiEmptyInputTransport
  abiDecoderCoherence abiDecoderMembers abiDecoderMemberInfos abiDecoderStructInputs
  abiEncoderInput compileEnv exprLowering valueEncoding vyperABI
  contractABI finite_map words list rich_list pair combin arithmetic

Theorem abi_empty_struct_default_value:
  LENGTH args = LENGTH tvs ==>
  default_to_abi (StructTV (ZIP (MAP FST args,tvs))) = ListV (default_to_abi_list tvs)
Proof
  simp[default_to_abi_def, default_to_abi_fields_MAP, default_to_abi_list_MAP,
    MAP_MAP_o, MAP_ZIP]
QED

Theorem abi_empty_struct_memory_size:
  abi_decoder_header ce env (StructT nsid) (StructTV (ZIP (MAP FST args,tvs))) /\
  LIST_REL (abi_decoder_coherent ce (env \\ nsid) (sf \\ nsid_to_string nsid))
    (MAP SND args) tvs ==>
  type_memory_bytes ce (StructT nsid) = type_memory_bytes ce (TupleT (MAP SND args))
Proof
  strip_tac >> drule abi_decoder_member_infos_layout >> strip_tac >>
  `LENGTH (MAP FST args) = LENGTH tvs` by
    (imp_res_tac LIST_REL_LENGTH >> fs[]) >>
  fs[abi_decoder_header_def, type_memory_size_def, type_memory_size_fields_zip] >>
  CONV_TAC (RAND_CONV (ONCE_REWRITE_CONV [type_memory_bytes_def])) >>
  CONV_TAC (DEPTH_CONV ETA_CONV) >>
  asm_rewrite_tac[]
QED

Theorem abi_empty_struct_descriptor:
  is_abi_dynamic ce.ce_struct_fields (StructT nsid) /\
  FLOOKUP sf (nsid_to_string nsid) = SOME fields ==>
  type_to_abi_enc_info sf ce (StructT nsid) =
    AbiComplex (MAP (\ty.
      (type_to_abi_enc_info (sf \\ nsid_to_string nsid) ce ty,
       abi_embedded_static_size ce.ce_struct_fields ty, type_memory_bytes ce ty,
       is_abi_dynamic ce.ce_struct_fields ty)) (MAP (FST o SND) fields))
Proof
  strip_tac >> asm_simp_tac (srw_ss())
    [Once type_to_abi_enc_info_def, LET_THM, MAP_MAP_o] >>
  irule MAP_CONG >> simp[FORALL_PROD, o_DEF]
QED

Theorem abi_empty_struct_default_input:
  FLOOKUP env nsid = SOME (StructArgs args) /\
  FLOOKUP sf (nsid_to_string nsid) = SOME fields /\
  MAP (\(name,ty,sz). (name,ty)) fields = args /\
  EVERY (\(name,ty,sz). sz = type_memory_bytes ce ty) fields /\
  LIST_REL (\ty tv.
    abi_decoder_coherent ce (env \\ nsid) (sf \\ nsid_to_string nsid) ty tv /\
    (has_type (vyper_to_abi_type (env \\ nsid) ty) (default_to_abi tv) ==>
      abi_encoder_input (type_to_abi_enc_info (sf \\ nsid_to_string nsid) ce ty)
        (vyper_to_abi_type (env \\ nsid) ty) (default_to_abi tv)
        0 (type_memory_bytes ce ty) [])) (MAP SND args) tvs /\
  abi_decoder_header ce env (StructT nsid) (StructTV (ZIP (MAP FST args,tvs))) /\
  has_type (vyper_to_abi_type env (StructT nsid))
    (default_to_abi (StructTV (ZIP (MAP FST args,tvs)))) ==>
  abi_encoder_input (type_to_abi_enc_info sf ce (StructT nsid))
    (vyper_to_abi_type env (StructT nsid))
    (default_to_abi (StructTV (ZIP (MAP FST args,tvs))))
    0 (type_memory_bytes ce (StructT nsid)) []
Proof
  simp_tac bool_ss [LIST_REL_CONJ] >> strip_tac >>
  RULE_ASSUM_TAC (CONV_RULE (DEPTH_CONV ETA_CONV)) >>
  `abi_decoder_coherent ce env sf (StructT nsid)
     (StructTV (ZIP (MAP FST args,tvs)))` by
    (irule struct_case >> asm_rewrite_tac[] >>
     qexists_tac `fields` >> asm_rewrite_tac[]) >>
  Cases_on `is_dynamic (vyper_to_abi_type env (StructT nsid))`
  >- (`is_abi_dynamic ce.ce_struct_fields (StructT nsid)` by fs[abi_decoder_header_def] >>
      `LENGTH args = LENGTH tvs` by (imp_res_tac LIST_REL_LENGTH >> fs[]) >>
      drule_all abi_empty_struct_default_value >> strip_tac >>
      drule_all abi_empty_struct_memory_size >> strip_tac >>
      drule_all abi_decoder_struct_field_types >> strip_tac >>
      `MAP (FST o SND) fields = MAP SND args` by gvs[] >>
      drule_all abi_empty_struct_descriptor >> strip_tac >>
      asm_simp_tac bool_ss [vyper_to_abi_type_def] >>
      mp_tac (Q.INST [`tys` |-> `MAP SND (args:(string # vyperAST$type) list)`,
        `tvs` |-> `tvs`,
        `env` |-> `env \\ nsid`, `sf` |-> `sf \\ nsid_to_string nsid`,
        `at` |-> `Tuple (vyper_to_abi_types (env \\ nsid)
          (MAP SND (args:(string # vyperAST$type) list)))`, `p` |-> `0`]
        abi_empty_members_zero) >>
      impl_tac
      >- (fs[abi_encoder_tuple_type_def, LIST_REL_CONJ, vyper_to_abi_type_def] >>
          CONV_TAC (DEPTH_CONV ETA_CONV) >> gvs[has_type_def]) >> simp[]) >>
  irule abi_empty_coherent_static_input >> simp[abi_empty_memory_observation]
QED

val () = List.app (fn (n,th) =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th) in
    if null (Thm.hyp th) andalso null axioms andalso
       List.all (fn s => s = "DISK_THM") oracles then
      print ("ABI_EMPTY_STRUCT_INPUT_KERNEL_CLOSED " ^ n ^ "\n")
    else raise Fail ("ABI Empty struct input not kernel closed: " ^ n)
  end) (DB.thms "abiEmptyStructInput");
