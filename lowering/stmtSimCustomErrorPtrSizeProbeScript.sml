Theory stmtSimCustomErrorPtrSizeProbe
Ancestors
  bodyCustomErrorWindowBounds valueEncodingProps compileEnv valueEncoding
  vyperValue arithmetic list loweringPosts bodyPtrDefs

(* Diagnostic consequences of the existing environment agreement theorem.
   In particular storage slots in this semantics are not packed. *)
Theorem custom_error_unwrap_slot_count[local]:
  expr_sim_inv ce cx env es /\
  evaluate_type (get_tenv cx) ty = SOME tv ==>
  type_memory_bytes ce ty = 32 * type_slot_size tv /\
  (type_memory_bytes ce ty + 31) DIV 32 = type_slot_size tv
Proof
  strip_tac >> drule_all custom_error_expr_inv_memory_size >>
  simp[cj 1 type_memory_size_slots, ADD_DIV_RWT]
QED

Theorem custom_error_unwrap_sizes_examples[local]:
  MAP (\n. type_memory_bytes ce (BaseT (BytesT (Dynamic n)))) [0;1;32;33] =
    [32;64;64;96] /\
  type_memory_bytes ce (TupleT []) = 0 /\
  type_memory_bytes ce (ArrayT (BaseT (UintT 256)) (Fixed 0)) = 0 /\
  type_memory_bytes ce (ArrayT (BaseT (UintT 256)) (Fixed 2)) = 64 /\
  type_memory_bytes ce (ArrayT (BaseT (UintT 256)) (Dynamic 2)) = 96
Proof
  simp[type_memory_bytes_def]
QED

(* The only representation-type exception in vv_holds is already memory:
   it never reaches allocation/materialisation. *)
Theorem custom_error_nonmemory_unwrap_size[local]:
  vv_post ctx fn ce cx e es sa sm s0 ee raw (LocatedValue ty p) s /\
  p.ptr_location <> LocMemory /\ expr_sim_inv ce cx env es /\
  evaluate_type (get_tenv cx) (post_value_type ce e) = SOME tv ==>
  type_memory_bytes ce ty = type_memory_size tv /\
  type_memory_bytes ce ty = 32 * type_slot_size tv /\
  (type_memory_bytes ce ty + 31) DIV 32 = type_slot_size tv
Proof
  strip_tac >>
  `ty = post_value_type ce e` by gvs[vv_post_def, vv_holds_def] >>
  gvs[] >> drule_all custom_error_expr_inv_memory_size >>
  simp[cj 1 type_memory_size_slots, ADD_DIV_RWT]
QED
