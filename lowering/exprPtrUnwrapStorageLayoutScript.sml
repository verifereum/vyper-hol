(* Compiler-only dimensions of the allocating storage forcing suffix. *)
Theory exprPtrUnwrapStorageLayout
Ancestors
  exprPtrUnwrapEnsureShape exprPtrUnwrapTypedSize exprSimStorageCopy copyExecution
  exprLoweringProps emitHelperProps emitHelper compileEnv context loweringHalt
  exprLowering arithmetic

Theorem unwrap_slot_alloc_strict_id[local]:
  compile_alloc_buffer nb sa = (buf,mid) ==> sa.cs_next_id < mid.cs_next_id
Proof
  simp[compile_alloc_buffer_def, comp_bind_def, comp_return_def, emit_op_def,
    comp_ignore_bind_def, fresh_var_def, fresh_id_def, emit_def] >>
  rpt strip_tac >> gvs[]
QED

Theorem unwrap_slot_ensure_strict_id:
  (loc = LocStorage \/ loc = LocTransient) /\
  compile_ensure_in_memory src loc nb n ctor imm sa = (op,sb) ==>
  sa.cs_next_id < sb.cs_next_id
Proof
  disch_then (CONJUNCTS_THEN2 assume_tac strip_assume_tac) >>
  drule_all ensure_slot_memory_split >> strip_tac >>
  drule unwrap_slot_alloc_strict_id >> disch_tac >>
  Cases_on `n=1`
  >- (gvs[comp_bind_def, emit_op_def, emit_void_def, comp_return_def,
        comp_ignore_bind_def, fresh_var_def, fresh_id_def, emit_def]) >>
  gvs[] >> drule_at (Pat `compile_slot_to_memory _ _ _ _ _ = _`)
    compile_slot_to_memory_boundary >> simp[] >> strip_tac >> decide_tac
QED

Theorem unwrap_slot_ensure_layout:
  unwrap_value cenv (LocatedValue t p) sm = (op,sb) /\
  p.ptr_location = slot_loc tr /\ ~is_word_type t ==>
  compile_ensure_in_memory p.ptr_operand (slot_loc tr)
    (type_memory_bytes cenv t) ((type_memory_bytes cenv t+31) DIV 32)
    cenv.ce_is_ctor cenv.ce_imm_alloca sm = (op,sb) /\
  sm.cs_next_id < sb.cs_next_id
Proof
  strip_tac >>
  `compile_ensure_in_memory p.ptr_operand (slot_loc tr)
    (type_memory_bytes cenv t) ((type_memory_bytes cenv t+31) DIV 32)
    cenv.ce_is_ctor cenv.ce_imm_alloca sm = (op,sb)` by
    (Cases_on `tr` >> gvs[unwrap_value_def, loweringPostsTheory.slot_loc_def]) >>
  simp[] >> irule unwrap_slot_ensure_strict_id >>
  goal_assum (drule_at (Pat `compile_ensure_in_memory _ _ _ _ _ _ _ = _`)) >>
  Cases_on `tr` >> simp[loweringPostsTheory.slot_loc_def]
QED
