(* Full byte frames for bounded writes into compiler-owned allocations.
   Allocation-site separation also covers reuse of an existing ALLOCA. *)
Theory bodyIntCallWriteFrame
Ancestors
  localPtrsProps compileEnv venomMemDefs venomState venomInst venomWf
  finite_map list arithmetic

Theorem allocated_write_local_bytes:
  alloca_inv s /\ fn_inst_ids_distinct func /\
  local_ptrs_rel func cenv scopes s /\
  MEM inst (fn_insts func) /\ inst.inst_outputs = [q] /\
  not_local_ptr cenv scopes q /\
  FLOOKUP s.vs_allocas inst.inst_id = SOME (b,asz) /\
  b <= dst /\ dst + len <= b + asz /\
  (!a k. a + k <= dst \/ dst + len <= a ==>
    mem_bytes_at a k t.vs_memory = mem_bytes_at a k s.vs_memory) ==>
  (!n lo sz. local_region cenv scopes s n lo sz ==>
    mem_bytes_at lo sz t.vs_memory = mem_bytes_at lo sz s.vs_memory)
Proof
  strip_tac >> rpt gen_tac >> strip_tac >>
  drule_all local_ptrs_rel_alloca_disjoint >>
  simp[compileEnvTheory.regions_disjoint_def] >> strip_tac >>
  qpat_x_assum `!a k. _` irule >> decide_tac
QED
