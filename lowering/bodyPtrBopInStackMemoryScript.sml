Theory bodyPtrBopInStackMemory
Ancestors bodyPtrDefs loweringPosts context

(* A stack aggregate is a memory pointer. Normalize only its representation
   facts; the compiler still consumes the original value/place unchanged. *)
Theorem membership_stack_memory_holds:
  ~is_word_type ty /\
  vv_holds cenv cx ty tv (StackValue ann op) es s ==>
  vv_holds cenv cx ty tv (LocatedValue ty (mk_ptr op LocMemory)) es s
Proof
  simp[vv_holds_def, mk_ptr_def, expr_val_rel_def] >> metis_tac[]
QED

Theorem membership_stack_memory_at:
  ~is_word_type ty /\
  vv_at cenv cx ty sa sb es tv (StackValue ann op) s ==>
  vv_at cenv cx ty sa sb es tv (LocatedValue ty (mk_ptr op LocMemory)) s
Proof
  simp[vv_at_def, mk_ptr_def, expr_val_at_def] >> metis_tac[]
QED

Theorem membership_stack_memory_ptr:
  ~is_word_type ty /\
  ptr_vv_ok cx ty tv (StackValue ann op) es G tn s ==>
  ptr_vv_ok cx ty tv (LocatedValue ty (mk_ptr op LocMemory)) es G tn s
Proof
  simp[ptr_vv_ok_def, mk_ptr_def, ptr_val_ok_def] >> metis_tac[]
QED
