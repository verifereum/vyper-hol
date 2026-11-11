(* Boundary probes for empty, aligned and partial final bytes words. *)
Theory abiDecoderBytesEdges
Ancestors
  abiDecoderBytes abiDecoderBytesRuntime abiDecoderBytesMemory
  abiDecoderBytesPrefix abiDecoderBytesPhases abiDecoderContract abiEncoder
  compileEnv emitHelper venomExecSemantics venomState valueEncoding words arithmetic list

Theorem abi_decode_bytes_round_empty:
  32*((0+31) DIV 32) = 0
Proof
  EVAL_TAC
QED

Theorem abi_decode_bytes_round_aligned:
  32*((32*k+31) DIV 32) = 32*k
Proof
  simp[ADD_DIV_RWT]
QED

Theorem abi_decode_bytes_round_unaligned:
  0 < r /\ r < 32 ==>
  32*((32*k+r+31) DIV 32) = 32*(k+1)
Proof
  strip_tac >>
  `32*k+r+31 = 32*(k+1)+(r-1)` by decide_tac >>
  asm_rewrite_tac[] >> simp[ADD_DIV_RWT] >>
  irule LESS_DIV_EQ_ZERO >> decide_tac
QED

Theorem abi_decode_bytes_empty_writes:
  32 <= cap /\ (a+32 <= d \/ d+cap <= a) ==>
  mem_bytes_at d 32 (mcopy d a 32 (mstore d 0w s)).vs_memory =
    mem_bytes_at a 32 s.vs_memory /\
  abi_decode_frame d cap s (mcopy d a 32 (mstore d 0w s)) /\
  mem_bytes_at (d+32) 0 (mcopy d a 32 (mstore d 0w s)).vs_memory = []
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >> conj_tac
  >- (mp_tac (Q.INST [`q` |-> `0`, `c` |-> `0`]
        abi_decode_bytes_store_copy_prefix) >> simp[] >> metis_tac[]) >>
  conj_tac
  >- (mp_tac (Q.INST [`q` |-> `0`, `c` |-> `0`]
        abi_decode_bytes_store_copy_frame) >> simp[]) >>
  simp[mem_bytes_at_def]
QED

Theorem abi_decode_bytes_aligned_padding:
  mem_bytes_at (d+32+32*k) 0
    (mcopy d a (32+32*k) (mstore (d+32*k) 0w s)).vs_memory = []
Proof
  simp[mem_bytes_at_def]
QED

Theorem abi_decode_bytes_unaligned_padding:
  0 < r /\ r < 32 ==>
  mem_bytes_at (d+32+(32*k+r)) (32-r)
    (mcopy d a (32+(32*k+r)) (mstore (d+32*(k+1)) 0w s)).vs_memory =
  REPLICATE (32-r) 0w
Proof
  strip_tac >>
  `32-r = 32*(k+1)-(32*k+r)` by decide_tac >>
  asm_rewrite_tac[] >> irule abi_decode_bytes_store_copy_padding >> decide_tac
QED

Theorem abi_decode_bytes_rounded_capacity_frame:
  c <= n ==>
  abi_decode_frame d (abi_decode_bytes_copy_size n) s
    (mcopy d a (32+c) (mstore (d+32*((c+31) DIV 32)) 0w s))
Proof
  strip_tac >> irule abi_decode_bytes_store_copy_frame >>
  simp[abi_decode_bytes_copy_size_def, abi_decode_bytes_round_bounds] >>
  drule abi_decode_bytes_round_capacity >> simp[]
QED

(* A sentinel bound removes guards, not the syntactic-base copy choice. *)
Theorem abi_decode_bytes_sentinel_base_branches:
  abi_decode_source_opcode opc ==>
  (compile_abi_decode_to_buf dst pos opc (Lit 0w) (Lit 0w) (DecBytestring n) =
    do cnt <- abi_decode_count_guard opc pos n;
       emit_void (abi_decode_copy_opcode opc)
         [dst; pos; Lit (n2w (abi_decode_bytes_copy_size n))]
    od) /\
  (base_op <> Lit 0w ==>
   compile_abi_decode_to_buf dst pos opc base_op (Lit 0w) (DecBytestring n) =
    do addr <- compile_abi_dec_addr base_op pos;
       cnt <- abi_decode_count_guard opc addr n;
       abi_decode_bytes_runtime_tail dst addr cnt
    od)
Proof
  strip_tac >> simp[abi_decode_bytes_sentinel, compile_abi_dec_addr_def,
                   comp_bind_def, comp_return_def, FUN_EQ_THM]
QED
