(* Resource transport after mutation; semantic source updates are explicit. *)
Theory bodyIntCallFamStmtMutationResource
Ancestors
  bodyIntCallJointContract bodyIntCallWriteAuthorization
  loweringPosts compileEnv venomState

Theorem intcall_joint_res_mutation:
  intcall_frame_ok fp /\ intcall_joint_res fp ce env es sa s /\
  stmt_state_rel fp.jc_ctx fp.jc_func ce fp.jc_cx ee u /\
  expr_sim_inv ce fp.jc_cx env' ee /\
  ce_locals_declared ce env' /\ locals_alloc_ok ce env' /\
  local_ptrs_reserved ce sb /\
  (!x. not_fresh_at sa x ==> not_fresh_at sb x) /\
  (!x. not_fresh_at sa x ==> lookup_var x u = lookup_var x s) /\
  allocas_above fp.jc_lo u /\ s.vs_alloca_next <= u.vs_alloca_next /\
  (!a k. fp.jc_prot a k ==>
    mem_bytes_at a k u.vs_memory = mem_bytes_at a k s.vs_memory) /\
  (!op. fp.jc_reserved op ==> eval_operand op u = eval_operand op s) /\
  (!n p k. local_region ce ee.scopes u n p k ==>
           local_region ce es.scopes s n p k) /\
  (!bw cap. fp.jc_rb = SOME (bw,cap) /\ ce.ce_is_ctor ==>
    !nm tv iv io.
      FLOOKUP ce.ce_module_vars (ce.ce_module,nm) = SOME (ImmutableLoc io) /\
      FLOOKUP (case ALOOKUP ee.immutables fp.jc_cx.txn.target of
                 NONE => FEMPTY
               | SOME imms => get_source_immutables ce.ce_module imms) nm =
        SOME (tv,iv) ==>
      regions_disjoint io (type_memory_size tv) (w2n bw) cap) ==>
  intcall_joint_res fp ce env' ee sb u
Proof
  pure_rewrite_tac [intcall_joint_res_def, intcall_expr_res_def] >> strip_tac >>
  rpt conj_tac >> simp[]
  >- metis_tac[arithmeticTheory.ADD_COMM]
  >- (fs[intcall_frame_ok_def] >> metis_tac[])
  >- (fs[ret_pc_ok_def] >> metis_tac[])
  >- (Cases_on `fp.jc_rb` >> fs[return_buf_frame_def] >>
      PairCases_on `x` >> fs[return_buf_frame_def] >> metis_tac[arithmeticTheory.LESS_EQ_TRANS]) >>
  gvs[]
QED

Theorem intcall_local_region_protected:
  intcall_frame_ok fp /\ intcall_joint_res fp ce env es sa s /\
  local_region ce es.scopes s n p k /\ fp.jc_prot a z ==>
  regions_disjoint a z p k
Proof
  strip_tac >>
  irule (INST_TYPE [alpha |-> ``:string``] provenance_protected_regions) >>
  fs[intcall_frame_ok_def, intcall_joint_res_def, intcall_expr_res_def] >>
  qexists_tac `fp.jc_prot` >>
  qexistsl_tac [`local_region ce es.scopes s`, `fp.jc_lo`, `n`, `fp.jc_staged`] >>
  simp[] >> metis_tac[arithmeticTheory.ADD_COMM]
QED
