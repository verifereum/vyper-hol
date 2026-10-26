(* Match compiler member lists and offsets with coherent semantic layouts.
   TOP-LEVEL: tuple/fixed/struct info adapters and abi_decoder_member_infos_layout.
   Helper: concatenate typed canonical member views. *)
Theory abiDecoderMemberInfos
Ancestors
  abiDecoderMembers abiDecoderCoherence abiDecodeRanges exprLowering compileEnv
  valueEncoding vyperABI contractABI finite_map list rich_list arithmetic pair

Definition abi_decoder_member_infos_def:
  abi_decoder_member_infos (sf:string |-> (string # vyperAST$type # num) list) ce tys =
    MAP (\ty. (type_to_abi_dec_info sf ce ty,
      abi_embedded_static_size ce.ce_struct_fields ty, type_memory_bytes ce ty)) tys
End

Theorem abi_decoder_tuple_infos:
  type_to_abi_dec_info sf ce (TupleT tys) =
    DecComplex (EXISTS (is_abi_dynamic ce.ce_struct_fields) tys)
      (abi_decoder_member_infos sf ce tys)
Proof
  simp[Once type_to_abi_dec_info_def, abi_decoder_member_infos_def]
QED

Theorem abi_decoder_fixed_array_infos:
  type_to_abi_dec_info sf ce (ArrayT ty (Fixed n)) =
    DecComplex (is_abi_dynamic ce.ce_struct_fields ty)
      (abi_decoder_member_infos sf ce (REPLICATE n ty))
Proof
  simp[Once type_to_abi_dec_info_def, abi_decoder_member_infos_def,
    REPLICATE_GENLIST, MAP_GENLIST, combinTheory.o_DEF]
QED

Theorem abi_decoder_struct_infos:
  FLOOKUP sf (nsid_to_string nsid) = SOME fields ==>
  type_to_abi_dec_info sf ce (StructT nsid) =
    DecComplex (EXISTS (is_abi_dynamic ce.ce_struct_fields) (MAP (FST o SND) fields))
      (abi_decoder_member_infos (sf \\ nsid_to_string nsid) ce (MAP (FST o SND) fields))
Proof
  strip_tac >> simp[Once type_to_abi_dec_info_def, abi_decoder_member_infos_def, MAP_MAP_o] >>
  irule MAP_CONG >> simp[FORALL_PROD, combinTheory.o_DEF]
QED

Theorem abi_decoder_member_infos_layout:
  !tys tvs. LIST_REL (abi_decoder_coherent ce env sf) tys tvs ==>
  FOLDR (\(_,asz,_) acc. asz + acc) 0 (abi_decoder_member_infos sf ce tys) =
    SUM (MAP abi_member_head_size (MAP (vyper_to_abi_type env) tys)) /\
  type_memory_size_list tvs = SUM (MAP (type_memory_bytes ce) tys)
Proof
  Induct_on `tys` >> rpt gen_tac >> Cases_on `tvs` >>
  simp[abi_decoder_member_infos_def, type_memory_size_def] >> strip_tac >>
  first_x_assum drule_all >> strip_tac >>
  drule abi_decoder_coherent_header >> strip_tac >>
  gvs[abi_decoder_member_infos_def, abi_decoder_header_def, type_memory_size_def]
QED

Theorem abi_decoder_members_join:
  abi_decoder_members ce env sf pretys pretvs preavs prevs /\
  abi_decoder_members ce env sf tys tvs avs vs ==>
  abi_decoder_members ce env sf (pretys ++ tys) (pretvs ++ tvs) (preavs ++ avs) (prevs ++ vs)
Proof
  strip_tac >>
  mp_tac (Q.SPECL [`pretys`, `pretvs`, `preavs`, `prevs`] abi_decoder_members_lengths) >>
  impl_tac >- asm_simp_tac bool_ss [] >> strip_tac >>
  mp_tac (Q.SPECL [`pretys`, `pretvs`, `preavs`, `prevs`] abi_decoder_members_append) >>
  gvs[]
QED

val () = List.app (fn (n,th) =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th) in
    if null (Thm.hyp th) andalso null axioms andalso
       List.all (fn s => s = "DISK_THM") oracles then
      print ("ABI_DECODER_MEMBER_INFOS_KERNEL_CLOSED " ^ n ^ "\n")
    else raise Fail ("ABI member infos not kernel closed: " ^ n)
  end) (DB.thms "abiDecoderMemberInfos");
