Theory bodyAbiTupleSlotUnwrapShapeMods
Ancestors
  exprLowering exprLoweringProps exprPtrUnwrapEnsureShape exprPtrUnwrapAllocation
  compileEnv venomInst

Theorem abi_tuple_slot_unwrap_output_mods:
  ~is_word_type ty /\
  (p.ptr_location = LocStorage \/ p.ptr_location = LocTransient) /\
  unwrap_value ce (LocatedValue ty p) a = (Var out,c) /\
  local_ptrs_reserved ce se /\ se.cs_next_var <= a.cs_next_var ==>
  out = STRING #"%" (toString a.cs_next_var) /\
  not_local_ptr ce scopes out
Proof
  disch_then (CONJUNCTS_THEN2 assume_tac
    (CONJUNCTS_THEN2 assume_tac strip_assume_tac)) >>
  `compile_ensure_in_memory p.ptr_operand p.ptr_location
     (type_memory_bytes ce ty) ((type_memory_bytes ce ty + 31) DIV 32)
     ce.ce_is_ctor ce.ce_imm_alloca a = (Var out,c)` by
    (qpat_x_assum `unwrap_value _ _ _ = _` mp_tac >>
     qpat_x_assum `_ = LocStorage \/ _ = LocTransient` strip_assume_tac >>
     simp[unwrap_value_def]) >>
  drule_all ensure_slot_memory_split >> strip_tac >>
  drule unwrap_alloc_generated_code >> strip_tac >>
  gvs[] >>
  irule local_ptrs_reserved_fresh >>
  qexists_tac `se` >> simp[]
QED
