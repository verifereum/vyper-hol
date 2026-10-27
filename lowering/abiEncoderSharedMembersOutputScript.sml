(* Rich observations from the generator's supplied static child endpoint. *)
Theory abiEncoderSharedMembersOutput
Ancestors
  abiEncoderSharedMemberContract abiEncoderMemberSpineCompat abiEncoderSharedContract
  abiEncoderChildContext abiEncoderMemberSpine abiEncoderAddressReach
  compileEnv venomState list arithmetic

Theorem abi_encoder_shared_member_static_output:
  compile_abi_encode_child dst src ei F offset dp st = (out,en) /\
  fn_has_code st en func /\
  (st.cs_blocks = en.cs_blocks \/
    !bb. lookup_block en.cs_current_bb func.fn_blocks = SOME bb ==>
      phi_prefix_length bb.bb_instructions = 0) /\
  abi_encoder_shared_input (ei,at,av) (st,src,dst) (sb,source_cap)
    (d,output_size) (first,last,b,cap) initial /\
  en.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st initial /\
  ~initial.vs_halted /\ initial.vs_current_bb = st.cs_current_bb /\
  initial.vs_inst_idx = LENGTH st.cs_current_insts /\
  abi_encoder_spine_child_output
    (abi_encoder_spine_shared_post (ctx,func) (at,av,sb,source_cap,d+offset)
      (first,last,b,cap,limit_st))
    (ei,F,dst,src,offset,dp,st,en,out) initial actual ==>
  abi_encoder_shared_endpoint (ctx,func) (st,en,out,limit_st)
    (first,last,b,cap) (at,av,d+offset) initial actual
Proof
  simp_tac bool_ss [abi_encoder_spine_child_output_def, abi_encoder_spine_shared_post_def] >>
  disch_then (MAP_EVERY strip_assume_tac o CONJUNCTS) >>
  drule_all abi_encoder_static_child_structural_context >> strip_tac >>
  gvs[] >> drule abi_encoder_emit_address_shape >> strip_tac >>
  `p.cs_next_var <= limit_st.cs_next_var` by decide_tac >>
  `eval_operand dst initial = SOME (n2w d)` by fs[abi_encoder_shared_input_def] >>
  drule_all abi_encoder_spine_static_shared_transport >> simp[]
QED

val _ = List.app (fn th =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th) in
    if List.all (fn s => s = "DISK_THM") oracles andalso null axioms andalso null (Thm.hyp th)
    then () else raise Fail "shared output admission, axiom or hypothesis"
  end) [abi_encoder_shared_member_static_output];
