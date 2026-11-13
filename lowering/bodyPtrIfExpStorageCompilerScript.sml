Theory bodyPtrIfExpStorageCompiler
Ancestors
  copyExecution loweringHalt fragExec context compileEnv

(* The copy aliases return a label, discarded by ensure-memory. Keep
   capacity independent of the loop count, including the zero-count case. *)
Theorem ifexp_ensure_memory_slot_loop_parts:
  (loc = LocStorage \/ loc = LocTransient) /\ n <> 1 /\
  compile_ensure_in_memory src loc capacity n is_ctor imm sb = (dst,sd) /\
  fn_has_code sb sd fn ==>
  ?buf cs.
    compile_alloc_buffer capacity sb = (buf,cs) /\
    dst = buf.buf_operand /\
    sd = slot_copy_final cs src dst n
           (if loc = LocStorage then SLOAD else TLOAD) /\
    fn_has_code sb cs fn /\ fn_has_code cs sd fn /\
    sb.cs_next_var <= cs.cs_next_var /\
    sb.cs_next_id <= cs.cs_next_id
Proof
  rpt strip_tac >>
  Cases_on `compile_alloc_buffer capacity sb` >>
  rename1 `compile_alloc_buffer capacity sb = (buf,cs)` >>
  qexistsl_tac [`buf`, `cs`] >>
  drule compile_alloc_buffer_parts >> strip_tac >>
  drule compile_alloc_buffer_extends >> strip_tac >>
  `sd = slot_copy_final cs src dst n
          (if loc = LocStorage then SLOAD else TLOAD) /\
   dst = buf.buf_operand` by
    (gvs[compile_ensure_in_memory_def, comp_bind_def,
         comp_ignore_bind_def, comp_return_def,
         compile_storage_to_memory_def, compile_transient_to_memory_def,
         GSYM compile_slot_to_memory_def, compile_slot_to_memory_shape]) >>
  `cs_extends cs sd` by metis_tac[slot_copy_extends] >>
  drule_all fn_has_code_split >> strip_tac >> simp[]
QED
