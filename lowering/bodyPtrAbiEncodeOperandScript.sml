(* Positive-read operand elimination.  Zero-footprint values are deliberately
   excluded: their operand need not have provenance or even be a Var. *)
Theory bodyPtrAbiEncodeOperand
Ancestors
  bodyPtrDefs representationCleanPtr ptrCoverage venomExecSemantics venomState
  words finite_map

Theorem ptr_mem_ok_positive_operand:
  ptr_mem_ok cx t v op G tn s /\
  evaluate_type (get_tenv cx) t = SOME tv /\
  eval_operand op s = SOME w /\ val_footprint tv v <> 0 ==>
  ?x b sz. op = Var x /\ FLOOKUP G x = SOME (b,sz) /\
    b <= w2n w /\ w2n w + val_store_size tv v <= b+sz
Proof
  simp[ptr_mem_ok_def] >> metis_tac[]
QED

Theorem ptr_val_ok_positive_store_covers:
  ptr_val_ok cx t v op G tn s /\ ~is_word_type t /\
  evaluate_type (get_tenv cx) t = SOME tv /\
  eval_operand op s = SOME w /\ val_footprint tv v <> 0 ==>
  ?x. op = Var x /\ lookup_var x s = SOME w /\
    ptr_covers G tn x s (val_store_size tv v)
Proof
  rpt strip_tac >>
  `ptr_mem_ok cx t v op G tn s` by fs[ptr_val_ok_def] >>
  drule_all ptr_mem_ok_positive_operand >> strip_tac >> gvs[] >>
  fs[ptr_val_ok_def, eval_operand_def] >>
  simp[ptr_covers_def] >> metis_tac[]
QED

(* Instantiation obligations (not additional assumptions on the generic facts):
   loweringPosts.val_footprint_def gives 32+LENGTH bs for BytesV at dynamic
   BytesT, and 32+LENGTH str for StringV at StringT, hence positive even for
   empty payload.  Caller must still establish evaluate_type and the value's
   matching constructor.  For arrays and primitive words the default branch
   is type_memory_size tv: positivity needs the evaluated array layout's
   length header or the primitive layout's 32-byte size, respectively.
   ptr_val_ok does not give ptr_mem_ok for word types: word staging must
   establish the temporary allocation's memory provenance separately.
   These facts do not imply memory-byte cleanliness, no-wrap, or window_input.
   representationCleanPtr.ptr_val_ok_read_covers already covers any m bounded
   by val_footprint; the corollary above instead exposes full val_store_size
   and the exact lookup, directly from ptr_mem_ok's stronger provenance bound.
*)
