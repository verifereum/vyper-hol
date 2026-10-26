(* Static encoder leaves produce the semantic ABI encoding from complete input.
   No correctness property of an emitted fragment is an input premise. *)
Theory abiEncoderInputLeaves
Ancestors
  abiEncoderInput abiEncoderLeaves abiEncoderSourceChecks abiDecoderContract
  abiEncoder emitHelper compileEnv valueEncoding contractABI venomState venomExecSemantics
  words list

Theorem abi_encoder_copy_input_sequence:
  compile_abi_encode_to_buf dst src (AbiCopy sz) st = (out,st') /\
  abi_encoder_input (AbiCopy sz) at av sb cap s.vs_memory /\
  eval_operand src s = SOME (n2w sb) /\ eval_operand dst s = SOME (n2w db) /\
  sb < dimword (:256) /\ db < dimword (:256) /\ sz < dimword (:256) /\
  fresh_vars_wrt st s ==>
  ?actual. run_inst_seq (emitted_insts st st') s = OK actual /\
    mem_bytes_at db (LENGTH (enc at av)) actual.vs_memory = enc at av /\
    eval_operand out actual = SOME (n2w (LENGTH (enc at av))) /\
    abi_decode_frame db (LENGTH (enc at av)) s actual /\ fresh_vars_wrt st' actual /\
    (!op w. eval_operand op s = SOME w ==> eval_operand op actual = SOME w)
Proof
  strip_tac >>
  qpat_assum `abi_encoder_input _ _ _ _ _ _`
    (MAP_EVERY assume_tac o CONJUNCTS o REWRITE_RULE [abi_encoder_input_copy_iff]) >>
  `LENGTH (enc at av) = sz` by
    (drule_all (cj 1 enc_has_static_length) >> simp[]) >>
  drule_all abi_encode_copy_sequence >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts st st') s = OK actual` >>
  qexists_tac `actual` >> asm_simp_tac bool_ss []
QED

Theorem abi_encoder_word_input_sequence:
  compile_abi_encode_to_buf dst src AbiPrimWord st = (out,st') /\
  abi_encoder_input AbiPrimWord at av sb cap s.vs_memory /\
  eval_operand src s = SOME (n2w sb) /\ eval_operand dst s = SOME (n2w db) /\
  sb < dimword (:256) /\ db < dimword (:256) /\ fresh_vars_wrt st s ==>
  ?actual. run_inst_seq (emitted_insts st st') s = OK actual /\
    mem_bytes_at db (LENGTH (enc at av)) actual.vs_memory = enc at av /\
    eval_operand out actual = SOME (n2w (LENGTH (enc at av))) /\
    abi_decode_frame db (LENGTH (enc at av)) s actual /\ fresh_vars_wrt st' actual /\
    (!op w. eval_operand op s = SOME w ==> eval_operand op actual = SOME w)
Proof
  strip_tac >>
  qpat_assum `abi_encoder_input _ _ _ _ _ _`
    (MAP_EVERY assume_tac o CONJUNCTS o REWRITE_RULE [abi_encoder_input_word_iff]) >>
  `LENGTH (enc at av) = 32` by
    (drule_all (cj 1 enc_has_static_length) >> simp[]) >>
  drule_all abi_encode_word_sequence >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts st st') s = OK actual` >>
  qexists_tac `actual` >> asm_simp_tac (srw_ss()) []
QED

Theorem abi_encoder_input_excludes_uninitialized_sparse_defaults:
  ~abi_encoder_input (AbiCopy 32)
    (vyper_to_abi_type FEMPTY (ArrayT (BaseT (UintT 256)) (Fixed 1)))
    (ListV [NumV 0]) 0 cap abi_encoder_sparse_probe_memory
Proof
  metis_tac[abi_encoder_input_copy_iff, abi_encoder_sparse_probe_window]
QED

val () = List.app (fn (n,th) =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th) in
    if null (Thm.hyp th) andalso null axioms andalso
       List.all (fn s => s = "DISK_THM") oracles then
      print ("ABI_ENCODER_INPUT_LEAVES_KERNEL_CLOSED " ^ n ^ "\n")
    else raise Fail ("ABI encoder input leaf not kernel closed: " ^ n)
  end) (DB.thms "abiEncoderInputLeaves");
