(* Finish a real recursive encoding without disturbing its method-ID prefix. *)
Theory abiBuiltinEncodeCompose
Ancestors
  abiBuiltinEncodeFinish abiBuiltinEncodeCode abiEncoderComplexCompose
  abiDecoderEffect abiDecoderAllocation abiDecoderFrame abiDecoderContract abiDecoderLoop
  abiDecoderReentry fragExec compileEnv venomState words list arithmetic

Theorem abi_builtin_encode_prefix_frame:
  abi_decoder_effect first last lo hi next limit_st (p+32+mid_size) len b cap s t /\
  (p+32+mid_size+len <= b \/ b+cap <= p) ==>
  mem_bytes_at (p+32) mid_size t.vs_memory = mem_bytes_at (p+32) mid_size s.vs_memory
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  qpat_assum `abi_decoder_effect _ _ _ _ _ _ _ _ _ _ _ _`
    (MAP_EVERY assume_tac o CONJUNCTS o PURE_REWRITE_RULE [abi_decoder_effect_def]) >>
  irule abi_decode_footprint_frame_slice >> qexists_tac `[(p+32+mid_size,len);(b,cap)]` >>
  asm_simp_tac (srw_ss()) [abi_footprint_disjoint_def] >> decide_tac
QED

Theorem abi_builtin_encode_compose:
  abi_decoder_effect first last ready.cs_next_id body_end.cs_next_id ready.cs_next_var
    limit_st (p+32+mid_size) len b cap initial encoded /\
  mem_bytes_at (p+32+mid_size) len encoded.vs_memory = bytes /\
  eval_operand buf initial = SOME (n2w p) /\ abi_decoder_operand_live ready.cs_next_var buf /\
  eval_operand encoded_len encoded = SOME (n2w len) /\
  abi_builtin_encode_finish buf encoded_len mid_size body_end = ((),final) /\
  fn_has_code body_end final func /\ ready.cs_next_var <= body_end.cs_next_var /\
  body_end.cs_next_id <= final.cs_next_id /\
  p < dimword (:256) /\ (p+32+mid_size+len <= b \/ b+cap <= p) /\
  final.cs_next_var <= limit_st.cs_next_var /\
  ~encoded.vs_halted /\ encoded.vs_current_bb = body_end.cs_current_bb /\
  encoded.vs_inst_idx = LENGTH body_end.cs_current_insts /\ abi_decode_sim ctx func initial encoded ==>
  ?actual. eval_operand buf actual = SOME (n2w p) /\ mload p actual = n2w (len+mid_size) /\
    mem_bytes_at (p+32+mid_size) len actual.vs_memory = bytes /\
    mem_bytes_at (p+32) mid_size actual.vs_memory = mem_bytes_at (p+32) mid_size initial.vs_memory /\
    abi_decoder_effect first last ready.cs_next_id final.cs_next_id ready.cs_next_var
      limit_st p (32+mid_size+len) b cap initial actual /\
    actual.vs_current_bb = final.cs_current_bb /\ actual.vs_inst_idx = LENGTH final.cs_current_insts /\
    ~actual.vs_halted /\ abi_decode_sim ctx func initial actual
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  drule_all abi_builtin_encode_prefix_frame >> strip_tac >>
  qpat_assum `abi_decoder_effect _ _ _ _ _ _ _ _ _ _ _ _`
    (MAP_EVERY assume_tac o CONJUNCTS o PURE_REWRITE_RULE [abi_decoder_effect_def]) >>
  `~initial.vs_halted` by fs[] >>
  `eval_operand buf encoded = SOME (n2w p)` by
    (first_x_assum irule >> asm_simp_tac bool_ss []) >>
  `abi_decoder_operand_live body_end.cs_next_var buf` by
    (irule abi_decoder_operand_live_mono >> qexists_tac `ready.cs_next_var` >> asm_simp_tac bool_ss []) >>
  mp_tac (Q.INST [`st` |-> `body_end`, `initial` |-> `encoded:venom_state`,
    `output_size` |-> `32+mid_size+len:num`, `lo` |-> `ready.cs_next_id`,
    `hi` |-> `final.cs_next_id`] abi_builtin_encode_finish) >>
  impl_tac >- (asm_simp_tac (srw_ss()) [] >> decide_tac) >> strip_tac >>
  `abi_decoder_effect first last ready.cs_next_id body_end.cs_next_id ready.cs_next_var
     limit_st p (32+mid_size+len) b cap initial encoded` by
    (irule abi_decoder_effect_widen >>
     qexistsl_tac [`p+32+mid_size`, `body_end.cs_next_id`, `ready.cs_next_id`,
       `ready.cs_next_var`, `len`] >> asm_simp_tac (srw_ss()) [] >> decide_tac) >>
  `abi_decoder_effect first last ready.cs_next_id final.cs_next_id ready.cs_next_var
     limit_st p (32+mid_size+len) b cap initial actual` by
    (drule_all abi_decoder_effect_sequence >> simp[]) >>
  qexists_tac `actual` >> asm_simp_tac (srw_ss()) [] >>
  irule abi_decode_sim_trans >> qexists_tac `encoded` >> asm_simp_tac bool_ss []
QED

val () = List.app (fn (n,th) =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th) in
    if null (Thm.hyp th) andalso null axioms andalso
       List.all (fn s => s = "DISK_THM") oracles then
      print ("ABI_BUILTIN_ENCODE_COMPOSE_KERNEL_CLOSED " ^ n ^ "\n")
    else raise Fail ("ABI builtin encoder composition not kernel closed: " ^ n)
  end) (DB.thms "abiBuiltinEncodeCompose");
