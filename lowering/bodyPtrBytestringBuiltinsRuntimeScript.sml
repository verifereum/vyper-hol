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

Theorem order_runtime_local_ptrs:
  local_ptrs_rel func order_ptr_env order_ptr_source.scopes order_runtime_start
Proof
  simp[compileEnvTheory.local_ptrs_rel_def,
       compileEnvTheory.local_region_def,
       bodyPtrBytestringBuiltinsPtrFrameTheory.order_ptr_source_def,
       bodyPtrBytestringBuiltinsOrderProbeTheory.order_probe_scopes_def,
       bodyPtrBytestringBuiltinsPtrRunTheory.order_ptr_env_def,
       vyperStateTheory.lookup_scopes_def,
       finite_mapTheory.FLOOKUP_UPDATE] >>
  rw[] >> gvs[] >> qexists_tac `128w` >>
  simp[wordsTheory.w2n_n2w, wordsTheory.dimword_def,
       venomMemPropsTheory.dimindex_256,
       order_runtime_array_wf, order_runtime_array_memory,
       valueEncodingTheory.type_memory_size_def] >>
  simp[compileEnvTheory.local_backed_def, order_runtime_start_def,
       bodyPtrBytestringBuiltinsPtrRunTheory.order_ptr_start_def,
       bodyPtrBytestringBuiltinsOrderRunTheory.order_run_start_def,
       venomStateTheory.init_venom_state_def, venomStateTheory.lookup_var_def,
       finite_mapTheory.FLOOKUP_UPDATE]
QED

Theorem order_runtime_state_rel:
  state_rel func order_ptr_env order_runtime_cx order_ptr_source order_runtime_start
Proof
  simp[compileEnvTheory.state_rel_def, order_runtime_local_ptrs,
       order_runtime_call_context] >>
  EVAL_TAC >> rw[] >> gvs[]
QED
