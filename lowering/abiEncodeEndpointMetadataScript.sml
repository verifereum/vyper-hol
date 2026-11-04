Theory abiEncodeEndpointMetadata
Ancestors
  exprSimAggregateLayout exprSimHyps abiEncodeListSupplier
  compileEnv valueEncoding valueEncodingProps words arithmetic

(* Endpoint layout facts use the abstract environment invariant, not a
   build_compile_env premise.  ABI plan/head metadata is audited separately. *)
Theorem abi_encode_endpoint_memory_layout:
  expr_sim_inv ce cx env es /\
  evaluate_type (get_tenv cx) ty = SOME tv ==>
  type_memory_bytes ce ty = type_memory_size tv /\
  type_memory_bytes ce ty MOD 32 = 0
Proof
  strip_tac >> drule_all expr_sim_inv_memory_size >> strip_tac >>
  simp[type_memory_size_aligned]
QED

Theorem abi_encode_endpoint_memory_bound:
  expr_body_pre ce cx env e es /\
  evaluate_type (get_tenv cx) (expr_type e) = SOME tv /\
  ~is_word_type (expr_type e) ==>
  type_memory_bytes ce (expr_type e) < dimword (:256)
Proof
  strip_tac >> drule_all expr_body_pre_copy_ok >> strip_tac >>
  gvs[wordsTheory.dimword_def] >> decide_tac
QED
