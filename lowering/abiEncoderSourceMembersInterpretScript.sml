(* Branch-indexed core contracts for the common list generator. *)
Theory abiEncoderSourceMembersInterpret
Ancestors
  abiEncoderSourceMembersEntry abiEncoderMemberSourceContract abiEncoderMemberSpine
  abiDecoderLoop pair

Definition abi_encoder_source_members_child_pre_def:
  abi_encoder_source_members_child_pre resources (dyn,value,cursor) c s <=>
    if dyn then abi_encoder_member_dynamic_pre value resources cursor c s
    else abi_encoder_member_core_pre value resources c s
End

Definition abi_encoder_source_members_child_post_def:
  abi_encoder_source_members_child_post (ctx,func) resources (dyn,value,cursor) c s t <=>
    if dyn then abi_encoder_member_dynamic_post (ctx,func) value resources cursor c s t
    else abi_encoder_member_core_post (ctx,func) value resources c s t
End

Theorem abi_encoder_source_members_child_run:
  !y c r. abi_encoder_spine_core_code func c /\
    abi_encoder_source_members_child_pre resources y c r ==>
    ?u. abi_decode_sim ctx func r u /\
      abi_encoder_source_members_child_post (ctx,func) resources y c r u
Proof
  rpt gen_tac >> PairCases_on `y` >> Cases_on `y0` >>
  simp_tac bool_ss [abi_encoder_source_members_child_pre_def,
    abi_encoder_source_members_child_post_def] >>
  rpt strip_tac
  >- (irule abi_encoder_member_source_dynamic_run >> asm_rewrite_tac []) >>
  irule abi_encoder_member_source_core_run >> asm_rewrite_tac []
QED

val _ = List.app (fn th =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th) in
    if List.all (fn s => s = "DISK_THM") oracles andalso null axioms andalso null (Thm.hyp th)
    then () else raise Fail "source interpretation has an admission, axiom or hypothesis"
  end) [abi_encoder_source_members_child_run];
