Theory frameAllocationEffects
Ancestors
  venomMemProps ptrDiscipline codegenRel venomExecSemantics venomState
  finite_map pred_set list

(* Memory preservation already lives in venomMemProps; expose only the
   complementary allocator effect here. *)
Theorem exec_alloca_preserves_fmp:
  exec_alloca inst s sz = OK post ==> post.vs_fmp = s.vs_fmp
Proof
  simp[exec_alloca_def, AllCaseEqs(), update_var_def] >>
  rpt strip_tac >> gvs[]
QED

Theorem alloca_step_writes:
  inst.inst_opcode = ALLOCA ==> step_writes inst s post = []
Proof
  simp[step_writes_def, source_memory_write_ranges_def]
QED

Theorem alloca_fresh_site_tainted:
  inst.inst_opcode = ALLOCA /\
  aid NOTIN FDOM s.vs_allocas /\
  FLOOKUP post.vs_allocas aid = SOME (b,sz) /\
  b <= byte /\ byte < b + sz ==>
  byte IN (step_taint inst s post tn).t_mem
Proof
  simp[step_taint_def, mem_taint_def, alloca_step_writes, range_bytes_def,
       new_site_bytes_def] >> metis_tac[]
QED
