(* Coherent heterogeneous members supply canonical child inputs.
   TOP-LEVEL: abi_decoder_member_pre.
   Helpers: member metadata, source slices and output cell bounds. *)
Theory abiDecoderMemberInputs
Ancestors
  abiDecoderMembers abiDecoderMemberSlice abiDecoderArrayChildSource
  abiDecoderCoherence abiDecoderTypedContract abiDecoderContract abiDecoderDynamic
  abiDecodeRanges vyperABI compileEnv valueEncoding contractABI
  venomState words list rich_list arithmetic

Theorem abi_decoder_members_child_facts:
  abi_decoder_members ce env sf pretys pretvs preavs prevs /\
  abi_decoder_members ce env sf (ty::tys) (tv::tvs) (av::avs) (v::vs) ==>
  abi_decoder_coherent ce env sf ty tv /\
  abi_decoder_metadata ce env ty tv (type_to_abi_dec_info ce.ce_struct_fields ce ty) av v /\
  has_types (MAP (vyper_to_abi_type env) (pretys ++ ty::tys)) (preavs ++ av::avs) /\
  LENGTH pretys = LENGTH preavs /\
  type_memory_size tv = type_memory_bytes ce ty
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  mp_tac (Q.SPECL [`pretys`, `pretvs`, `preavs`, `prevs`] abi_decoder_members_relations) >>
  impl_tac >- asm_simp_tac bool_ss [] >> strip_tac >>
  mp_tac (Q.SPECL [`ty::tys`, `tv::tvs`, `av::avs`, `v::vs`] abi_decoder_members_relations) >>
  impl_tac >- asm_simp_tac bool_ss [] >> strip_tac >>
  `LENGTH pretys = LENGTH preavs` by metis_tac[LIST_REL_LENGTH, LENGTH_MAP] >>
  `abi_decoder_coherent ce env sf ty tv /\
   abi_decoder_metadata ce env ty tv (type_to_abi_dec_info ce.ce_struct_fields ce ty) av v`
    by fs[Once abi_decoder_members_def] >>
  asm_simp_tac (srw_ss()) [MAP_APPEND, has_types_LIST_REL, LIST_REL_APPEND_EQ] >>
  fs[abi_decoder_metadata_def]
QED

Theorem abi_decoder_member_source:
  abi_decoder_members ce env sf pretys pretvs preavs prevs /\
  abi_decoder_members ce env sf (ty::tys) (tv::tvs) (av::avs) (v::vs) /\
  mem_bytes_at sb (LENGTH (enc (Tuple (MAP (vyper_to_abi_type env) (pretys ++ ty::tys)))
    (ListV (preavs ++ av::avs)))) (abi_decode_source opc s) =
    enc (Tuple (MAP (vyper_to_abi_type env) (pretys ++ ty::tys))) (ListV (preavs ++ av::avs)) ==>
  mem_bytes_at (sb + abi_tuple_child_offset (MAP (vyper_to_abi_type env) (pretys ++ ty::tys))
      (preavs ++ av::avs) (LENGTH pretys))
    (LENGTH (enc (vyper_to_abi_type env ty) av)) (abi_decode_source opc s) =
    enc (vyper_to_abi_type env ty) av /\
  abi_tuple_child_offset (MAP (vyper_to_abi_type env) (pretys ++ ty::tys))
    (preavs ++ av::avs) (LENGTH pretys) + LENGTH (enc (vyper_to_abi_type env ty) av) <=
    LENGTH (enc (Tuple (MAP (vyper_to_abi_type env) (pretys ++ ty::tys)))
      (ListV (preavs ++ av::avs))) /\
  SUM (MAP (type_memory_bytes ce) pretys) + type_memory_bytes ce ty <=
    SUM (MAP (type_memory_bytes ce) (pretys ++ ty::tys))
Proof
  strip_tac >> mp_tac abi_decoder_members_child_facts >>
  impl_tac >- asm_simp_tac bool_ss [] >> strip_tac >>
  `LENGTH (MAP (vyper_to_abi_type env) pretys) = LENGTH preavs` by simp[] >>
  qpat_x_assum `has_types _ _` mp_tac >>
  simp_tac bool_ss [MAP_APPEND, MAP] >> strip_tac >>
  qpat_x_assum `mem_bytes_at sb _ _ = _` mp_tac >>
  simp_tac bool_ss [MAP_APPEND, MAP] >> strip_tac >>
  drule_all abi_tuple_child_offset_source >> strip_tac >>
  drule_all abi_tuple_child_offset_ranges >> strip_tac >>
  gvs[MAP_APPEND, SUM_APPEND, Excl "enc_def"]
QED

Theorem abi_decoder_member_pre:
  abi_decoder_members ce env sf pretys pretvs preavs prevs /\
  abi_decoder_members ce env sf (ty::tys) (tv::tvs) (av::avs) (v::vs) /\
  abi_decoder_ranges opc hi src dst sb
    (LENGTH (enc (Tuple (MAP (vyper_to_abi_type env) (pretys ++ ty::tys)))
      (ListV (preavs ++ av::avs))))
    d (SUM (MAP (type_memory_bytes ce) (pretys ++ ty::tys))) b cap s /\
  mem_bytes_at sb (LENGTH (enc (Tuple (MAP (vyper_to_abi_type env) (pretys ++ ty::tys)))
    (ListV (preavs ++ av::avs)))) (abi_decode_source opc s) =
    enc (Tuple (MAP (vyper_to_abi_type env) (pretys ++ ty::tys))) (ListV (preavs ++ av::avs)) /\
  fresh_vars_wrt child_st s /\ abi_decoder_reservation child_st.cs_next_id last b cap s /\
  eval_operand childsrc s = SOME (n2w (sb + abi_tuple_child_offset
    (MAP (vyper_to_abi_type env) (pretys ++ ty::tys)) (preavs ++ av::avs) (LENGTH pretys))) /\
  eval_operand childdst s = SOME (n2w (d + SUM (MAP (type_memory_bytes ce) pretys))) ==>
  abi_decoder_recursive_pre ce env sf ty tv (type_to_abi_dec_info sf ce ty) av v
    child_st last childsrc childdst opc hi
    (sb + abi_tuple_child_offset (MAP (vyper_to_abi_type env) (pretys ++ ty::tys))
      (preavs ++ av::avs) (LENGTH pretys))
    (d + SUM (MAP (type_memory_bytes ce) pretys)) b cap s
Proof
  strip_tac >> mp_tac abi_decoder_members_child_facts >>
  impl_tac >- asm_simp_tac bool_ss [] >> strip_tac >>
  mp_tac abi_decoder_member_source >> impl_tac >- asm_simp_tac bool_ss [] >> strip_tac >>
  asm_simp_tac bool_ss [abi_decoder_recursive_pre_def, abi_decoder_pre_def] >>
  irule abi_decoder_subwindow_ranges >> asm_simp_tac bool_ss [] >>
  qexistsl_tac [`d`, `dst`,
    `LENGTH (enc (Tuple (MAP (vyper_to_abi_type env) (pretys ++ ty::tys)))
      (ListV (preavs ++ av::avs)))`,
    `SUM (MAP (type_memory_bytes ce) (pretys ++ ty::tys))`, `sb`, `src`] >>
  asm_simp_tac arith_ss [GSYM ADD_ASSOC] >> gvs[Excl "enc_def"] >> decide_tac
QED

val () = List.app (fn (n,th) =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th) in
    if null (Thm.hyp th) andalso null axioms andalso
       List.all (fn s => s = "DISK_THM") oracles then
      print ("ABI_DECODER_MEMBER_INPUTS_KERNEL_CLOSED " ^ n ^ "\n")
    else raise Fail ("ABI member inputs not kernel closed: " ^ n)
  end) (DB.thms "abiDecoderMemberInputs");
