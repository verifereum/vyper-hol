(* Representation boundaries shared by string revert encoders. *)
Theory reasonRepresentationPtr
Ancestors
  bodyPtrDefs representationCleanPtr exprSimProps compileEnv valueEncoding loweringPosts
  venomState venomExecSemantics ptrDiscipline words vyperValue

Theorem ptr_mem_ok_string_region:
  ptr_mem_ok cx t (StringV str) op G tn s /\
  evaluate_type (get_tenv cx) t = SOME (BaseTV (StringT n)) /\
  eval_operand op s = SOME w ==>
  ?x b sz. op = Var x /\ FLOOKUP G x = SOME (b,sz) /\
    b <= w2n w /\
    w2n w + (32 + 32 * word_size (LENGTH str)) <= b + sz
Proof
  simp[ptr_mem_ok_def] >> rpt strip_tac >>
  first_x_assum drule >> disch_then drule >>
  simp[val_footprint_def, val_store_size_def]
QED

Theorem ptr_mem_ok_string_head_clean:
  ptr_mem_ok cx t (StringV str) op G tn s /\
  evaluate_type (get_tenv cx) t = SOME (BaseTV (StringT n)) /\
  eval_operand op s = SOME w ==>
  !i. w2n w <= i /\ i < w2n w + 32 ==> i NOTIN tn.t_mem
Proof
  simp[ptr_mem_ok_def] >> rpt strip_tac >>
  first_x_assum drule >> disch_then drule >> strip_tac >>
  drule robust_val_in_memory_string_clean >>
  disch_then strip_assume_tac >> metis_tac[]
QED

Theorem ptr_val_ok_string_covers:
  ptr_val_ok cx t (StringV str) op G tn s /\
  evaluate_type (get_tenv cx) t = SOME (BaseTV (StringT n)) /\
  ~is_word_type t /\ eval_operand op s = SOME w ==>
  ?x. op = Var x /\
      ptr_covers G tn x s (32 + 32 * word_size (LENGTH str))
Proof
  simp[ptr_val_ok_def] >> rpt strip_tac >> gvs[] >>
  drule_all ptr_mem_ok_string_region >> strip_tac >> gvs[] >>
  simp[ptr_covers_def] >>
  gvs[eval_operand_def] >> metis_tac[]
QED

Theorem ptr_vv_ok_string_storage_head_clean:
  ptr_vv_ok cx t tv (LocatedValue t' p) es G tn s /\
  evaluate_type (get_tenv cx) t = SOME (BaseTV (StringT n)) /\
  eval_operand p.ptr_operand s = SOME w /\ b < 32 ==>
  (p.ptr_location = LocStorage ==> (w,b) NOTIN tn.t_stor) /\
  (p.ptr_location = LocTransient ==> (w,b) NOTIN tn.t_trans)
Proof
  simp[ptr_vv_ok_def] >> rpt strip_tac >>
  first_x_assum (qspecl_then [`w`, `BaseTV (StringT n)`, `w`, `b`] mp_tac) >>
  simp[type_slot_size_def, dead_bytes_def, dyn_bytes_dead_def]
QED
