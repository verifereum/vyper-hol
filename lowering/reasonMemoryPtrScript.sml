(* Memory-source boundaries shared by reason-bearing raise and assert. *)
Theory reasonMemoryPtr
Ancestors bodyPtrDefs ptrDiscipline venomState exprLowering compileEnv

Theorem reason_ptr_mem_ok_transport:
  ptr_mem_ok cx ty v op G tn s /\
  eval_operand op s = SOME w /\ eval_operand op t = SOME w /\
  op_prov G' op = op_prov G op /\
  (!tv mem. evaluate_type (get_tenv cx) ty = SOME tv /\
    mem_agree_outside tn'.t_mem t.vs_memory mem ==>
    val_in_memory tv v (w2n w) mem) ==>
  ptr_mem_ok cx ty v op G' tn' t
Proof
  strip_tac >> simp[ptr_mem_ok_def] >> rpt gen_tac >> strip_tac >>
  strip_tac >>
  qpat_x_assum `ptr_mem_ok _ _ _ _ _ _ _` mp_tac >>
  simp[ptr_mem_ok_def] >>
  strip_tac >>
  Cases_on `op` >> gvs[op_prov_def] >> metis_tac[]
QED

Theorem reason_memory_unwrap_identity:
  ~is_word_type ty /\ p.ptr_location = LocMemory ==>
  unwrap_value cenv (LocatedValue ty p) sa = (p.ptr_operand,sa)
Proof
  simp[unwrap_value_def, comp_return_def]
QED
