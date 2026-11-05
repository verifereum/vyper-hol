(* Same-endpoint semantic interface for completed storage copies. *)
Theory exprSimPtrTopLevelStorageSemantic
Ancestors
  exprSimPtrTopLevelStorageEnsure exprSimCopy exprSimStorageCopy
  exprLoweringProps compileEnv valueEncoding

Theorem toplevel_copy_prefix_state_rel:
  stmt_state_rel ctx fn cenv cx es u /\
  local_ptrs_reserved cenv st /\
  copy_prefix loc a b n u n t /\
  (!x. not_fresh_at st x ==> lookup_var x t = lookup_var x u) /\
  LENGTH u.vs_memory <= LENGTH t.vs_memory /\
  MEM inst (fn_insts fn) /\ inst.inst_opcode = ALLOCA /\
  FLOOKUP u.vs_allocas inst.inst_id = SOME (b,32*n) /\
  (!name lb len. local_region cenv es.scopes u name lb len ==>
    regions_disjoint b (32*n) lb len) ==>
  stmt_state_rel ctx fn cenv cx es t
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  irule copy_buffer_state_rel_frame >>
  qexistsl_tac [`b`, `inst`, `u`, `st`, `32*n`] >>
  gvs[copy_prefix_def, regions_disjoint_def] >> metis_tac[]
QED
