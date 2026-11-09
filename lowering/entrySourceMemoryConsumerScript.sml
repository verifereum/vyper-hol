(* Source-valued postcondition at the very decoder endpoint witness. *)
Theory entrySourceMemoryConsumer
Ancestors
  entryNormalizedMemory entryCanonicalEmptyWindow calldataSourceMemberFold
  abiDecoderValidContract valueEncodingTyping vyperABI valueEncoding

Theorem entry_member_success_original_value:
  abi_decoder_valid_pre ce env sf ty tv bytes nv first src dst CALLDATALOAD
    (Lit 0w) (Lit 0w) 0 sb p b reserve_cap ready /\
  value_has_type tv v /\
  vyper_to_abi env ty v = SOME (dec (vyper_to_abi_type env ty) bytes) /\
  calldata_member_success ctx fn site limit_st first last p len tv nv ready out scratch ==>
  calldata_member_success ctx fn site limit_st first last p len tv v ready out scratch
Proof
  strip_tac >>
  `val_in_memory tv nv p out.vs_memory` by fs[calldata_member_success_def] >>
  `val_in_memory tv v p out.vs_memory` by
    (irule entry_valid_pre_original_memory >> metis_tac[]) >>
  gvs[calldata_member_success_def] >> metis_tac[value_has_type_val_wf]
QED

Theorem entry_canonical_suffix_success_original_value:
  has_types (pre ++ vyper_to_abi_type env ty::post) (pvs ++ av::rest) /\
  LENGTH pre = LENGTH pvs /\ is_dynamic (vyper_to_abi_type env ty) /\
  bs = enc (Tuple (pre ++ vyper_to_abi_type env ty::post)) (ListV (pvs ++ av::rest)) /\
  LENGTH bs < dimword (:256) /\
  k = abi_decode_member_offset (vyper_to_abi_type env ty) bs
        (SUM (MAP abi_member_head_size pre)) /\
  abi_decoder_valid_pre ce env sf ty tv (DROP k bs) nv first src dst CALLDATALOAD
    (Lit 0w) (Lit 0w) 0 sb p b reserve_cap ready /\
  value_has_type tv v /\
  vyper_to_abi env ty v = SOME (dec (vyper_to_abi_type env ty) (DROP k bs)) /\
  calldata_member_success ctx fn site limit_st first last p len tv nv ready out scratch ==>
  abi_decode_member_bytes (vyper_to_abi_type env ty) bs
    (DROP (SUM (MAP abi_member_head_size pre)) bs) = DROP k bs /\
  k + LENGTH (DROP k bs) = LENGTH bs /\
  calldata_member_success ctx fn site limit_st first last p len tv v ready out scratch
Proof
  strip_tac >> drule_all entry_canonical_dynamic_member_bound >>
  simp_tac bool_ss [LET_THM] >> strip_tac >>
  drule_all entry_member_success_original_value >> strip_tac >>
  metis_tac[]
QED

val () = List.app (fn th =>
  let val (oracles, axioms) = Tag.dest_tag (Thm.tag th)
  in if null axioms andalso null (Thm.hyp th) andalso
        List.all (fn name => name = "DISK_THM") oracles
     then () else raise Fail "entry source memory consumer inherited admission"
  end) [entry_member_success_original_value, entry_canonical_suffix_success_original_value];
