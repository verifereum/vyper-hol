Theory bodyPtrBytestringBuiltinsRuntime
Ancestors
  bodyPtrBytestringBuiltinsPtrFrame bodyPtrDefs valueEncodingProofs

Theorem order_ptr_runtime_tx_obstruction:
  order_ptr_cx.txn.block_number = 0 /\
  ~tx_env_ok order_ptr_cx.txn
Proof
  EVAL_TAC
QED

Theorem order_ptr_runtime_no_state_rel:
  ~state_rel func order_ptr_env order_ptr_cx es s
Proof
  simp[compileEnvTheory.state_rel_def,
       compileEnvTheory.call_ctx_rel_def,
       order_ptr_runtime_tx_obstruction]
QED

(* Separate witness constants preserve the checked zero-block experiment. *)
Definition order_runtime_cx_def:
  order_runtime_cx = order_ptr_cx with txn :=
    order_ptr_cx.txn with <|block_number := 1; block_hashes := [0w]|>
End

Definition order_runtime_start_def:
  order_runtime_start = order_ptr_start with vs_block_ctx :=
    order_ptr_start.vs_block_ctx with bc_number := 1w
End

Theorem order_runtime_tx_ok:
  tx_env_ok order_runtime_cx.txn
Proof
  EVAL_TAC
QED

Theorem order_runtime_call_context:
  call_ctx_rel order_runtime_cx.txn order_runtime_start.vs_call_ctx
    order_runtime_start.vs_tx_ctx order_runtime_start.vs_block_ctx
Proof
  EVAL_TAC >> rw[] >> gvs[]
QED

Theorem order_runtime_array_wf:
  val_wf (ArrayTV (BaseTV AddressT) (Dynamic 2))
    (ArrayV (DynArrayV [AddressV 1w; AddressV 2w]))
Proof
  EVAL_TAC
QED

Theorem order_runtime_array_memory:
  val_in_memory (ArrayTV (BaseTV AddressT) (Dynamic 2))
    (ArrayV (DynArrayV [AddressV 1w; AddressV 2w]))
    128 order_runtime_start.vs_memory
Proof
  simp_tac pure_ss [order_runtime_start_def,
    venomStateTheory.venom_state_accfupds, combinTheory.K_THM] >>
  simp[valueEncodingTheory.val_in_memory_def,
       valueEncodingTheory.type_memory_size_def,
       valueEncodingPropsTheory.mem_word_at_eq_mload,
       bodyPtrBytestringBuiltinsPtrRunTheory.order_ptr_start_array] >>
  simp[valueEncodingTheory.typed_val_to_w256_def,
       GSYM valueEncodingProofsTheory.word_to_bytes_w2w_address,
       byteTheory.word_of_bytes_be_def,
       vfmTypesTheory.word_to_bytes_word_of_bytes_256, wordsTheory.w2w_n2w]
QED
