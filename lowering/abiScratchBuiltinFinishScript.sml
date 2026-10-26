(* Execute the builtin length store with physical scratch ownership.
   TOP-LEVEL: abi_scratch_builtin_finish preserves completed payload/prefix
   bytes and records the actual register and allocator-preserving write. *)
Theory abiScratchBuiltinFinish
Ancestors
  abiBuiltinEncodeFinish abiScratchLeafEffect abiScratchEncoderContract
  abiDecoderFrame abiDecoderFrameCompose abiDecoderDynamicLoopSetup abiDecoderReentry
  abiDecoderContract abiDecoderLoop compileEnv venomState words list arithmetic

Theorem abi_scratch_builtin_finish:
  abi_builtin_encode_finish buf encoded_len mid_size st = ((),final) /\ fn_has_code st final func /\
  eval_operand buf initial = SOME (n2w p) /\ eval_operand encoded_len initial = SOME (n2w len) /\
  abi_decoder_operand_live st.cs_next_var buf /\ p < dimword (:256) /\ 32 <= output_size /\
  abi_decoder_budget first last b cap initial /\
  final.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st initial /\
  ~initial.vs_halted /\ initial.vs_current_bb = st.cs_current_bb /\
  initial.vs_inst_idx = LENGTH st.cs_current_insts ==>
  ?actual. eval_operand buf actual = SOME (n2w p) /\ mload p actual = n2w (len+mid_size) /\
    (!q n. p+32 <= q ==> mem_bytes_at q n actual.vs_memory = mem_bytes_at q n initial.vs_memory) /\
    abi_scratch_effect first last lo hi st.cs_next_var limit_st p output_size b cap initial actual /\
    actual.vs_current_bb = final.cs_current_bb /\ actual.vs_inst_idx = LENGTH final.cs_current_insts /\
    ~actual.vs_halted /\ abi_decode_sim ctx func initial actual
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  drule_all abi_builtin_encode_finish_reach >> disch_then (qspec_then `ctx` strip_assume_tac) >>
  `abi_decode_frame p output_size initial actual` by
    (irule abi_decode_frame_widen >> qexistsl_tac [`p`, `32`] >> asm_simp_tac (srw_ss()) []) >>
  `actual.vs_halted = initial.vs_halted` by simp[] >>
  `abi_scratch_effect first last lo hi st.cs_next_var limit_st p output_size b cap initial actual` by
    (irule abi_scratch_leaf_effect >> asm_simp_tac bool_ss [] >> first_assum ACCEPT_TAC) >>
  qexists_tac `actual` >> asm_simp_tac bool_ss [] >>
  qpat_assum `abi_decode_frame p 32 initial actual`
    (MAP_EVERY assume_tac o CONJUNCTS o PURE_REWRITE_RULE [abi_decode_frame_def]) >>
  rpt strip_tac >> first_x_assum irule >> asm_simp_tac (srw_ss()) []
QED

val () = List.app (fn (n,th) =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th) in
    if null (Thm.hyp th) andalso null axioms andalso
       List.all (fn s => s = "DISK_THM") oracles then
      print ("ABI_SCRATCH_BUILTIN_FINISH_KERNEL_CLOSED " ^ n ^ "\n")
    else raise Fail ("ABI scratch builtin length store not kernel closed: " ^ n)
  end) (DB.thms "abiScratchBuiltinFinish");
