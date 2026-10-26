(* Word, bulk-copy and empty-composite encoders append one straight-line fragment. *)
Theory abiEncoderLeafCode
Ancestors
  abiEncoderAdmissible abiEncoder abiDecoderContract emitHelperProps exprLoweringProps
  compileEnv emitHelper venomInst words list rich_list

Theorem abi_encode_static_leaf_shape:
  compile_abi_encode_to_buf dst src ei st = (out,st') /\ abi_encoder_static_leaf ei ==>
  st'.cs_blocks = st.cs_blocks /\ st'.cs_current_bb = st.cs_current_bb /\ inst_extends st st' /\
  EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode) (emitted_insts st st')
Proof
  Cases_on `ei` >> simp_tac (srw_ss()) [abi_encoder_static_leaf_def] >> strip_tac >> gvs[] >>
  qpat_x_assum `compile_abi_encode_to_buf _ _ _ _ = _` mp_tac >>
  simp[Once compile_abi_encode_child_def, compile_abi_encode_static_def,
    comp_bind_def, comp_ignore_bind_def, comp_return_def, emit_op_def, emit_void_def,
    fresh_var_def, fresh_id_def, emit_def] >>
  rpt (pairarg_tac >> gvs[]) >> strip_tac >> gvs[] >>
  simp[inst_extends_def, emitted_insts_def] >> pure_rewrite_tac [GSYM APPEND_ASSOC] >>
  simp[DROP_LENGTH_APPEND, mk_inst_def, is_terminator_def]
QED

val () = List.app (fn (n,th) =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th) in
    if null (Thm.hyp th) andalso null axioms andalso
       List.all (fn s => s = "DISK_THM") oracles then
      print ("ABI_ENCODER_LEAF_CODE_KERNEL_CLOSED " ^ n ^ "\n")
    else raise Fail ("ABI encoder leaf code not kernel closed: " ^ n)
  end) (DB.thms "abiEncoderLeafCode");
