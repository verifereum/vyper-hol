Theory exprPtrUnwrapTypedSize
Ancestors
  exprSimFieldLayout exprSimProps valueEncodingProps valueEncoding
  compileEnv loweringPosts

(* Size equality is supplied by the forcing precondition, not inferred
   from an arbitrary allocation's rounding. *)
Theorem unwrap_typed_buffer_bytes:
  type_memory_bytes cenv t = type_memory_size tv ==>
  type_memory_bytes cenv t = 32 * type_slot_size tv
Proof
  simp[type_memory_size_slots]
QED

Theorem unwrap_typed_buffer_count:
  type_memory_bytes cenv t = type_memory_size tv ==>
  (type_memory_bytes cenv t + 31) DIV 32 = type_slot_size tv
Proof
  simp[slot_count_of_memory_size]
QED

Theorem unwrap_typed_buffer_count_bound:
  type_memory_size tv < 2**64 ==> type_slot_size tv < 2**256
Proof
  simp[type_memory_size_slots] >> decide_tac
QED

Theorem unwrap_typed_buffer_store_bound:
  val_wf tv v /\ type_memory_bytes cenv t = type_memory_size tv ==>
  val_store_size tv v <= type_memory_bytes cenv t
Proof
  metis_tac[val_store_size_le]
QED

Theorem unwrap_storage_evaluated_type:
  storage_holds cx transient t result w es s ==>
  ?tv. evaluate_type (get_tenv cx) t = SOME tv
Proof
  simp[storage_holds_def] >> metis_tac[]
QED
