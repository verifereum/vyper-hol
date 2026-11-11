(* Unwrap copies use the actual allocation base, including loop re-entry. *)
Theory bodyIntCallReuseUnwrap
Ancestors
  bodyIntCallReuseAllocation bodyIntCallReuseHeldFrame
  bodyIntCallStageUnwrapCopy bodyIntCallStorageTyped bodyIntCallHeldImmutableCopy
  bodyIntCallHeldArgs bodyIntCallHeldFrame bodyIntCallStageUnwrapRead
  exprSimCopy exprSimStorageCopy exprSimProps exprLoweringProps
  loweringPosts loweringHalt compileEnv context venomState venomInst
  finite_map words freshWrites

Theorem intcall_reuse_copy_frame:
  stmt_state_rel ctx func ce cx es u /\ local_ptrs_reserved ce sm /\
  MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\
  FLOOKUP u.vs_allocas inst.inst_id = SOME (b,nb) /\
  (!name lb sz. local_region ce es.scopes u name lb sz ==>
    b+nb <= lb \/ lb+sz <= b) /\
  copy_static z = copy_static u /\ LENGTH u.vs_memory <= LENGTH z.vs_memory /\
  (!x. not_fresh_at sm x ==> lookup_var x z = lookup_var x u) /\
  (!off len. off+len <= b \/ b+nb <= off ==>
    mem_bytes_at off len z.vs_memory = mem_bytes_at off len u.vs_memory) /\
  intcall_held_args ce cx a sa es s H /\
  local_ptrs_rel func ce es.scopes s /\ local_ptrs_reserved ce sa /\
  (!aid entry. FLOOKUP s.vs_allocas aid = SOME entry ==>
    FLOOKUP u.vs_allocas aid = SOME entry) /\
  (!x. not_fresh_at sa x ==> lookup_var x u = lookup_var x s) /\
  u.vs_memory = s.vs_memory /\ u.vs_labels = s.vs_labels /\
  contract_storage u = contract_storage s /\
  contract_transient u = contract_transient s /\
  (!aid lb sz. FLOOKUP s.vs_allocas aid = SOME (lb,sz) /\ aid < sa.cs_next_id ==>
    lb+sz <= b \/ b+nb <= lb) /\
  (!name lb sz. local_region ce es.scopes s name lb sz ==>
    lb+sz <= b \/ b+nb <= lb) /\
  sa.cs_next_var <= sm.cs_next_var /\
  sa.cs_next_var <= sn.cs_next_var /\ sa.cs_next_id <= sn.cs_next_id ==>
  stmt_state_rel ctx func ce cx es z /\ wb_frame ce es sa s z /\
  intcall_held_args ce cx a sn es z H
Proof
  strip_tac >> conj_tac
  >- (irule copy_buffer_state_rel_frame >>
      qexistsl_tac [`b`,`inst`,`u`,`sm`,`nb`] >> simp[] >>
      metis_tac[arithmeticTheory.ADD_COMM]) >>
  drule copy_static_fields >> strip_tac >>
  `!x. not_fresh_at sa x ==> lookup_var x z = lookup_var x s` by
    metis_tac[not_fresh_at_mono] >>
  irule intcall_held_outside_write_frame >> simp[] >>
  conj_tac >- (qexistsl_tac [`b`,`nb`] >> simp[] >>
    conj_tac >- metis_tac[] >>
    conj_tac >- metis_tac[] >>
    rpt strip_tac >> simp[]) >>
  gvs[contract_storage_def, contract_transient_def] >>
  qexists_tac `func` >> simp[]
QED
