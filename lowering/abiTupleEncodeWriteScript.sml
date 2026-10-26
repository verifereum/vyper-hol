(* Actual tuple writes establish complete child input, including zero-sized
   copies. The memory-input relation is transported, rather than weakened. *)
Theory abiTupleEncodeWrite
Ancestors
  abiTupleEncodeInput abiBuiltinEncodeFinishSequence abiBuiltinEncodeWordStageReach
  abiBuiltinEncodeWordStageCode abiEncoderInput abiEncoderInputFrame abiEncoderWrites abiEncoderBytesCopy
  abiDecoderReentry abiDecoderContract abiDecoderGuards abiDecoderFrameCompose
  compileEnv context emitHelper emitHelperProps exprLoweringProps valueEncoding valueEncodingProps
  venomState venomExecSemantics words list arithmetic

Theorem abi_tuple_encode_word_write:
  is_word_type ty /\ emit_void MSTORE [dst;op] st = ((),final) /\
  eval_operand dst s = SOME (n2w d) /\ d < dimword (:256) /\ fresh_vars_wrt limit_st s /\
  abi_tuple_encode_input sf ce ty at av op next lo hi s ==>
  ?actual. run_inst_seq (emitted_insts st final) s = OK actual /\ inst_extends st final /\
    abi_encoder_input (type_to_abi_enc_info sf ce ty) at av d (type_memory_bytes ce ty) actual.vs_memory /\
    fresh_vars_wrt limit_st actual /\ abi_decode_frame d (type_memory_bytes ce ty) s actual /\
    actual.vs_allocas = s.vs_allocas /\ actual.vs_alloca_next = s.vs_alloca_next /\
    actual.vs_halted = s.vs_halted /\ (!op. eval_operand op actual = eval_operand op s)
Proof
  strip_tac >> gvs[abi_tuple_encode_input_def] >>
  drule_all abi_builtin_store_sequence >> strip_tac >>
  `abi_encoder_input (type_to_abi_enc_info sf ce ty) at av d 32 (mstore d w s).vs_memory` by
    (drule_all abi_builtin_encode_staged_word_input >> simp[]) >>
  drule abi_builtin_encode_word_info >> strip_tac >>
  qexists_tac `mstore d w s` >> fs[]
QED

Theorem abi_tuple_encode_copy_write:
  ~is_word_type ty /\ compile_copy_memory dst op (type_memory_bytes ce ty) st = ((),final) /\
  eval_operand dst s = SOME (n2w d) /\ d < dimword (:256) /\ fresh_vars_wrt limit_st s /\
  abi_tuple_encode_input sf ce ty at av op next lo hi s ==>
  ?actual. run_inst_seq (emitted_insts st final) s = OK actual /\ inst_extends st final /\
    abi_encoder_input (type_to_abi_enc_info sf ce ty) at av d (type_memory_bytes ce ty) actual.vs_memory /\
    fresh_vars_wrt limit_st actual /\ abi_decode_frame d (type_memory_bytes ce ty) s actual /\
    actual.vs_allocas = s.vs_allocas /\ actual.vs_alloca_next = s.vs_alloca_next /\
    actual.vs_halted = s.vs_halted /\ (!op. eval_operand op actual = eval_operand op s)
Proof
  strip_tac >> qpat_x_assum `abi_tuple_encode_input _ _ _ _ _ _ _ _ _ _` mp_tac >>
  asm_simp_tac bool_ss [abi_tuple_encode_input_def] >>
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  qpat_x_assum `?sb source_cap. eval_operand op s = SOME (n2w sb) /\ _`
    (qx_choose_then `sb` (qx_choose_then `source_cap`
      (MAP_EVERY assume_tac o CONJUNCTS))) >>
  `abi_encoder_input (type_to_abi_enc_info sf ce ty) at av sb
     (type_memory_bytes ce ty) s.vs_memory` by
    (irule abi_encoder_input_capacity >> qexists_tac `source_cap` >> asm_rewrite_tac[]) >>
  Cases_on `type_memory_bytes ce ty = 0`
  >- (gvs[compile_copy_memory_def, comp_return_def] >>
      `abi_encoder_input (type_to_abi_enc_info sf ce ty) at av d 0 s.vs_memory` by
        (drule abi_encoder_input_relocate >>
         disch_then (qspecl_then [`d`, `s.vs_memory`] mp_tac) >> simp[mem_bytes_at_def]) >>
      qexists_tac `s` >> simp[emitted_insts_def, run_inst_seq_def, inst_extends_def, abi_decode_frame_def]) >>
  `emit_void MCOPY [dst;op;Lit (n2w (type_memory_bytes ce ty))] st = ((),final)` by
    (Cases_on `type_memory_bytes ce ty` >> gvs[compile_copy_memory_def]) >>
  mp_tac (Q.INST [`src` |-> `op`, `dst` |-> `dst`,
    `len` |-> `Lit (n2w (type_memory_bytes ce ty))`, `cnt` |-> `type_memory_bytes ce ty`,
    `db` |-> `d`, `st'` |-> `final`] abi_encoder_emit_copy) >>
  impl_tac >- asm_simp_tac (srw_ss()) [eval_operand_def] >> strip_tac >>
  `abi_decode_frame d (type_memory_bytes ce ty) s (mcopy d sb (type_memory_bytes ce ty) s)` by
    (simp_tac bool_ss [abi_decode_frame_def] >> conj_tac
     >- (rpt strip_tac >> irule mcopy_mem_bytes_at_disjoint >> asm_simp_tac bool_ss []) >> simp[]) >>
  `abi_encoder_input (type_to_abi_enc_info sf ce ty) at av d (type_memory_bytes ce ty)
    (mcopy d sb (type_memory_bytes ce ty) s).vs_memory` by
    (drule abi_encoder_input_mcopy >> simp[]) >>
  qexists_tac `mcopy d sb (type_memory_bytes ce ty) s` >>
  asm_simp_tac (srw_ss()) [abi_encoder_copy_eval]
QED

Theorem abi_tuple_encode_write:
  (if is_word_type ty then emit_void MSTORE [dst;op]
   else compile_copy_memory dst op (type_memory_bytes ce ty)) st = ((),final) /\
  eval_operand dst s = SOME (n2w d) /\ d < dimword (:256) /\ fresh_vars_wrt limit_st s /\
  abi_tuple_encode_input sf ce ty at av op next lo hi s ==>
  ?actual. run_inst_seq (emitted_insts st final) s = OK actual /\ inst_extends st final /\
    abi_encoder_input (type_to_abi_enc_info sf ce ty) at av d (type_memory_bytes ce ty) actual.vs_memory /\
    fresh_vars_wrt limit_st actual /\ abi_decode_frame d (type_memory_bytes ce ty) s actual /\
    actual.vs_allocas = s.vs_allocas /\ actual.vs_alloca_next = s.vs_alloca_next /\
    actual.vs_halted = s.vs_halted /\ (!op. eval_operand op actual = eval_operand op s)
Proof
  Cases_on `is_word_type ty` >> asm_simp_tac bool_ss [] >> strip_tac >>
  FIRST [drule_all abi_tuple_encode_word_write >> simp[], drule_all abi_tuple_encode_copy_write >> simp[]]
QED

val () = List.app (fn (n,th) =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th) in
    if null (Thm.hyp th) andalso null axioms andalso
       List.all (fn s => s = "DISK_THM") oracles then
      print ("ABI_TUPLE_ENCODE_WRITE_KERNEL_CLOSED " ^ n ^ "\n")
    else raise Fail ("ABI tuple encoder write not kernel closed: " ^ n)
  end) (DB.thms "abiTupleEncodeWrite");
