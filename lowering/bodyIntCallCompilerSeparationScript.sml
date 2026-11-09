Theory bodyIntCallCompilerSeparation
Ancestors
  bodyIntCallCompilerClosure bodyIntCallCompilerInterval localPtrsProps
  compileEnv venomState venomExecSemantics venomMemDefs

(* A live local's backing ALLOCA cannot belong to a fresh compiler interval. *)
Theorem intcall_interval_local_backing_id:
  intcall_compiler_interval a.cs_next_var a b /\
  fn_has_code a b func /\ fn_inst_ids_distinct func /\
  local_ptrs_reserved ce a /\
  FLOOKUP ce.ce_vars name = SOME (PtrVar (Var p) sz) /\
  MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\
  inst.inst_outputs = [p] /\
  a.cs_next_id <= aid /\ aid < b.cs_next_id ==>
  aid <> inst.inst_id
Proof
  rpt strip_tac >>
  gvs[intcall_compiler_interval_def] >>
  qpat_x_assum `!func n. _ ==> _`
    (qspecl_then [`func`, `inst.inst_id`] mp_tac) >>
  (impl_tac >- simp[]) >>
  disch_then (qx_choose_then `other` strip_assume_tac) >>
  `other = inst` by metis_tac[fn_inst_ids_distinct_inj] >>
  gvs[] >>
  gvs[local_ptrs_reserved_def, not_fresh_at_def] >>
  metis_tac[]
QED

Theorem intcall_interval_local_separation:
  intcall_compiler_interval a.cs_next_var a b /\
  fn_has_code a b func /\ fn_inst_ids_distinct func /\
  local_ptrs_reserved ce a /\ local_ptrs_rel func ce scopes t /\
  alloca_inv t /\ local_region ce scopes t name lo sz /\
  FLOOKUP t.vs_allocas aid = SOME (off,asz) /\
  a.cs_next_id <= aid /\ aid < b.cs_next_id ==>
  regions_disjoint lo sz off asz
Proof
  rw[local_region_def] >>
  fs[local_ptrs_rel_def] >> first_x_assum drule_all >> strip_tac >>
  gvs[local_backed_def]
  >- (`aid <> inst.inst_id` by
        (irule intcall_interval_local_backing_id >> metis_tac[]) >>
      fs[alloca_inv_def, allocas_non_overlapping_def] >>
      qpat_x_assum `!a1 a2 b1 sz1 b2 sz2. _`
        (qspecl_then [`aid`, `inst.inst_id`] mp_tac) >>
      simp[compileEnvTheory.regions_disjoint_def]) >>
  metis_tac[]
QED
