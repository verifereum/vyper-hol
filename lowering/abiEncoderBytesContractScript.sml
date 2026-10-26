(* The bytes/string source contract supplies live data; the encoder supplies padding. *)
Theory abiEncoderBytesContract
Ancestors
  abiEncoderInput abiEncoderMemory abiEncoderRounding abiDecoderContract
  valueEncoding contractABI byte words list rich_list arithmetic

Theorem abi_encoder_bytes_contract_dimindex[simp,local]: dimindex (:256) = 256
Proof
  CONV_TAC fcpLib.INDEX_CONV
QED

Theorem abi_encoder_bytes_padded_length:
  cnt+32+(contractABI$ceil32 cnt-cnt) = 32+contractABI$ceil32 cnt
Proof
  mp_tac abi_encoder_ceil32_bounds >> strip_tac >> decide_tac
QED

Theorem abi_encoder_bytes_encoding:
  at = Bytes NONE \/ at = String ==>
  enc at (BytesV bs) = word_to_bytes (n2w (LENGTH bs):bytes32) T ++
    bs ++ REPLICATE (contractABI$ceil32 (LENGTH bs)-LENGTH bs) 0w /\
  LENGTH (enc at (BytesV bs)) = 32+contractABI$ceil32 (LENGTH bs)
Proof
  strip_tac >> gvs[Once enc_def, enc_number_def, LET_THM, abi_encoder_bytes_padded_length]
QED

Theorem abi_encoder_bytes_input_memory:
  abi_encoder_input (AbiBytestring maxlen) at (BytesV bs) sb cap s.vs_memory /\
  (sb+(32+LENGTH bs) <= db \/ db+(32+contractABI$ceil32 (LENGTH bs)) <= sb) ==>
  mem_bytes_at db (LENGTH (enc at (BytesV bs)))
    (mcopy db sb (32+LENGTH bs) (mstore (db+contractABI$ceil32 (LENGTH bs)) 0w s)).vs_memory =
    enc at (BytesV bs)
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  qpat_assum `abi_encoder_input _ _ _ _ _ _`
    (qx_choose_then `payload` (MAP_EVERY assume_tac o CONJUNCTS) o
      REWRITE_RULE [abi_encoder_input_bytes_iff]) >>
  `payload = bs` by
    (qpat_x_assum `contractABI$BytesV bs = BytesV payload` mp_tac >>
     simp_tac (srw_ss()) [EQ_SYM_EQ]) >>
  qpat_x_assum `payload = bs` SUBST_ALL_TAC >>
  mp_tac (Q.INST [`bs` |-> `bs:byte list`] abi_encoder_bytes_encoding) >>
  impl_tac >- asm_simp_tac bool_ss [] >> strip_tac >>
  mp_tac (Q.INST [`cnt` |-> `LENGTH (bs:byte list)`] abi_encoder_ceil32_bounds) >> strip_tac >>
  `contractABI$ceil32 (LENGTH bs) <= LENGTH bs+32` by decide_tac >>
  mp_tac (Q.INST [`rounded` |-> `contractABI$ceil32 (LENGTH (bs:byte list))`] abi_encoder_bytes_zero_copy) >>
  impl_tac >- asm_simp_tac bool_ss [] >>
  asm_simp_tac bool_ss []
QED

val () = List.app (fn (n,th) =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th) in
    if null (Thm.hyp th) andalso null axioms andalso
       List.all (fn s => s = "DISK_THM") oracles then
      print ("ABI_ENCODER_BYTES_CONTRACT_KERNEL_CLOSED " ^ n ^ "\n")
    else raise Fail ("ABI encoder bytes contract not kernel closed: " ^ n)
  end) (DB.thms "abiEncoderBytesContract");
