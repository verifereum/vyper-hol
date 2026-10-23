(* Closed source/layout probes, deliberately not decoder execution claims.

   Interface inventory for recursive decoding:
   - type_to_abi_dec_info_def already gives constructor equations for word,
     bytes/string, fixed/dynamic arrays, tuples, structs and flags. Its child
     triples contain (decoder, ABI embedded head size, MEMORY capacity size).
   - evaluate_abi_encode_bytes_def converts typed source values with
     vyper_to_abi before contractABI.enc; it does not assume decoding succeeds.
   - kwarg_buffer_rel expresses the resolved, well-formed memory payload,
     allocation backing/extent and SSA pointer. It can represent these types
     without successful execution in its definition. It does NOT describe
     source calldata or a recursive decoder's source cursor.

   Missing GENERIC contracts (not claimed by these concrete examples):
   1. Under evaluate_type/val_wf, conversion to ABI preserves each constructor,
      and descriptor ABI head sizes agree with enc's actual child heads.
      Structs must relate resolved field order and ce_struct_fields offsets;
      flags must relate the member count to the clamp. Neither follows from
      the AST shape alone when compiler environments are arbitrary.
   2. Encoding child extraction at an arbitrary nonzero container base:
      static heads advance by embedded ABI size; dynamic heads contain an
      offset relative to that container's base. Dynamic-array element offsets
      are relative to the base AFTER its length word. Prove no-wrap/bounds
      using the encoded length before converting natural offsets to words.
   3. Resolved type_memory_size <= type_memory_bytes, with memory child
      addresses advancing by CAPACITY size (bytes use padded maximum length),
      not by ABI head size or actual encoded length. This requires a coherent
      type/struct environment, especially for named structures.
   4. Establishing kwarg_buffer_rel additionally needs runtime decoder success,
      val_wf, backing and framing; these probes establish none of those for
      recursive execution. A counted-loop prefix proof remains necessary.

   Probe dimensions: uint256 head/memory=32/32; Bytes[10] embedded head=32,
   tail=32+ceil32(actual length), memory=64; mixed tuple head=64,memory=96;
   DynArray[Bytes[10],3] element ABI stride=32,memory stride=64,buffer=224.
   Zero-length bytes and arrays retain their ABI length word. *)
Theory abiSourceLayoutProbe
Ancestors typedKwargBufferProps vyperABI vyperValue exprLowering compileEnv valueEncoding
Libs wordsLib

Definition probe_word_def:
  probe_word (n:num) = word_to_bytes (n2w n : bytes32) T
End

Definition probe_bytes_ty_def:
  probe_bytes_ty = BaseT (BytesT (Dynamic 10))
End

Definition probe_mixed_ty_def:
  probe_mixed_ty = TupleT [BaseT (UintT 256); probe_bytes_ty]
End

Definition probe_array_ty_def:
  probe_array_ty = ArrayT probe_bytes_ty (Dynamic 3)
End

Theorem source_word_encoding:
  evaluate_abi_encode_bytes FEMPTY (BaseT (UintT 256)) (IntV 7) =
    INL (probe_word 7)
Proof
  EVAL_TAC
QED

Theorem source_bytes_encoding:
  evaluate_abi_encode_bytes FEMPTY probe_bytes_ty (BytesV [42w;43w]) =
    INL (probe_word 2 ++ [42w;43w] ++ REPLICATE 30 0w) /\
  evaluate_abi_encode_bytes FEMPTY probe_bytes_ty (BytesV []) =
    INL (probe_word 0)
Proof
  EVAL_TAC
QED

(* The mixed head occupies 64 ABI bytes, whereas its memory children
   occupy 32 and 64 bytes. The ABI tail starts relative to the tuple. *)
Theorem source_mixed_encoding:
  evaluate_abi_encode_bytes FEMPTY probe_mixed_ty
    (ArrayV (TupleV [IntV 7; BytesV [42w;43w]])) =
    INL (probe_word 7 ++ probe_word 64 ++ probe_word 2 ++
      [42w;43w] ++ REPLICATE 30 0w)
Proof
  EVAL_TAC
QED

(* Dynamic element offsets are based AFTER the length word, not at the
   array's length. Empty bytes still occupy one ABI length word. *)
Theorem source_dynamic_array_encoding:
  evaluate_abi_encode_bytes FEMPTY probe_array_ty
    (ArrayV (DynArrayV [BytesV []; BytesV [42w;43w]])) =
    INL (probe_word 2 ++ probe_word 64 ++ probe_word 96 ++
      probe_word 0 ++ probe_word 2 ++ [42w;43w] ++ REPLICATE 30 0w) /\
  evaluate_abi_encode_bytes FEMPTY probe_array_ty
    (ArrayV (DynArrayV [])) = INL (probe_word 0)
Proof
  EVAL_TAC
QED

Theorem primitive_decoder_layout:
  type_to_abi_dec_info cenv.ce_struct_fields cenv (BaseT (UintT 256)) =
    DecPrimWord NoClamp /\
  abi_embedded_static_size cenv.ce_struct_fields (BaseT (UintT 256)) = 32 /\
  type_memory_bytes cenv (BaseT (UintT 256)) = 32 /\
  evaluate_type cenv.ce_type_env (BaseT (UintT 256)) =
    SOME (BaseTV (UintT 256))
Proof
  simp[type_to_abi_dec_info_def, type_to_abi_clamp_def,
       abi_embedded_static_size_def, is_abi_dynamic_def, abi_static_size_def,
       type_memory_bytes_def, evaluate_type_def, type_slot_size_def]
QED

Theorem compound_decoder_layout:
  type_to_abi_dec_info cenv.ce_struct_fields cenv probe_bytes_ty =
    DecBytestring 10 /\
  type_to_abi_dec_info cenv.ce_struct_fields cenv probe_mixed_ty =
    DecComplex T [(DecPrimWord NoClamp,32,32);(DecBytestring 10,32,64)] /\
  type_to_abi_dec_info cenv.ce_struct_fields cenv probe_array_ty =
    DecDynArray (DecBytestring 10) 32 64 T 3 /\
  type_memory_bytes cenv probe_bytes_ty = 64 /\
  type_memory_bytes cenv probe_mixed_ty = 96 /\
  type_memory_bytes cenv probe_array_ty = 224 /\
  evaluate_type cenv.ce_type_env probe_mixed_ty =
    SOME (TupleTV [BaseTV (UintT 256);BaseTV (BytesT (Dynamic 10))]) /\
  evaluate_type cenv.ce_type_env probe_array_ty =
    SOME (ArrayTV (BaseTV (BytesT (Dynamic 10))) (Dynamic 3))
Proof
  simp[probe_bytes_ty_def, probe_mixed_ty_def, probe_array_ty_def,
       type_to_abi_dec_info_def, type_to_abi_clamp_def,
       abi_embedded_static_size_def, is_abi_dynamic_def, abi_static_size_def,
       type_memory_bytes_def, evaluate_type_def, type_slot_size_def] >> EVAL_TAC
QED

(* A real source tuple supplies the nonzero head position (36 in calldata
   after a four-byte selector); its array tail begins at 4+64=68.
   Element heads are based at 100, yielding targets 164 and 196. *)
Theorem source_array_nonzero_head:
  evaluate_abi_encode_bytes FEMPTY
    (TupleT [BaseT (UintT 256);probe_array_ty])
    (ArrayV (TupleV [IntV 7;
      ArrayV (DynArrayV [BytesV [];BytesV [42w;43w]])])) =
    INL (probe_word 7 ++ probe_word 64 ++ probe_word 2 ++
      probe_word 64 ++ probe_word 96 ++ probe_word 0 ++
      probe_word 2 ++ [42w;43w] ++ REPLICATE 30 0w)
Proof
  EVAL_TAC
QED

Theorem source_array_child_positions:
  evaluate_abi_encode_bytes FEMPTY
    (TupleT [BaseT (UintT 256);probe_array_ty])
    (ArrayV (TupleV [IntV 7;
      ArrayV (DynArrayV [BytesV [];BytesV [42w;43w]])])) = INL bs ==>
  TAKE 32 (DROP 36 (REPLICATE 4 0w ++ bs)) = probe_word 64 /\
  TAKE 32 (DROP 100 (REPLICATE 4 0w ++ bs)) = probe_word 64 /\
  TAKE 32 (DROP 132 (REPLICATE 4 0w ++ bs)) = probe_word 96 /\
  TAKE 32 (DROP 164 (REPLICATE 4 0w ++ bs)) = probe_word 0 /\
  TAKE 32 (DROP 196 (REPLICATE 4 0w ++ bs)) = probe_word 2
Proof
  simp[source_array_nonzero_head] >> strip_tac >> gvs[] >> EVAL_TAC
QED

(* Typed-buffer payloads use memory strides, not ABI head strides. *)
Theorem source_array_memory_positions:
  val_in_memory (ArrayTV (BaseTV (BytesT (Dynamic 10))) (Dynamic 3))
    (ArrayV (DynArrayV [BytesV [];BytesV [42w;43w]])) addr mem <=>
  mem_word_at addr mem = 2w /\
  val_in_memory (BaseTV (BytesT (Dynamic 10))) (BytesV [])
    (addr + 32) mem /\
  val_in_memory (BaseTV (BytesT (Dynamic 10))) (BytesV [42w;43w])
    (addr + 96) mem
Proof
  `word_size 10 = 1` by EVAL_TAC >>
  simp[val_in_memory_def, type_memory_size_def]
QED

Theorem typed_array_buffer_payload:
  kwarg_buffer_rel func cenv p probe_array_ty
    (ArrayV (DynArrayV vs)) ss ==>
  ?w. lookup_var p ss = SOME w /\
    val_wf (ArrayTV (BaseTV (BytesT (Dynamic 10))) (Dynamic 3))
      (ArrayV (DynArrayV vs)) /\
    val_in_memory (ArrayTV (BaseTV (BytesT (Dynamic 10))) (Dynamic 3))
      (ArrayV (DynArrayV vs)) (w2n w) ss.vs_memory /\
    w2n w + 224 <= ss.vs_alloca_next
Proof
  simp[kwarg_buffer_rel_def, compound_decoder_layout] >> metis_tac[]
QED

val _ = List.app (fn (name, th) =>
  if List.all (fn s => s = "DISK_THM") (#1 (Tag.dest_tag (Thm.tag th)))
     andalso null (#2 (Tag.dest_tag (Thm.tag th))) then ()
  else raise Fail ("unexpected oracle in abiSourceLayoutProbe: " ^ name))
  (DB.thms "abiSourceLayoutProbe");
