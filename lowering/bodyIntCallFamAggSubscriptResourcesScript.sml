(* Resource projections for the nonrecursive subscript suffixes. *)
Theory bodyIntCallFamAggSubscriptResources
Ancestors
  bodyIntCallJointAggCore bodyIntCallJointContract exprSimMapKey
  exprSimCopy intCallFrame freshWrites venomState compileEnv
  exprLoweringProps exprBopSimProps

(* A fixed-source suffix changing only variables and framed memory. *)
Theorem intcall_joint_res_memory_frame:
  intcall_frame_ok fp /\ intcall_joint_res fp ce env es sa s /\
  stmt_state_rel fp.jc_ctx fp.jc_func ce fp.jc_cx es u /\
  sa.cs_next_var <= sb.cs_next_var /\
  (u with <|vs_vars := s.vs_vars; vs_memory := s.vs_memory|>) = s /\
  (!x. not_fresh_at sa x ==> lookup_var x u = lookup_var x s) /\
  (!a k. fp.jc_prot a k ==>
     mem_bytes_at a k u.vs_memory = mem_bytes_at a k s.vs_memory) ==>
  intcall_joint_res fp ce env es sb u
Proof
  rpt strip_tac >>
  `u.vs_allocas = s.vs_allocas /\ u.vs_alloca_next = s.vs_alloca_next /\
   u.vs_labels = s.vs_labels` by fs[venom_state_component_equality] >>
  `allocas_above fp.jc_lo u` by
    (fs[intcall_joint_res_def, allocas_above_def] >> metis_tac[]) >>
  `!n b k. local_region ce es.scopes u n b k <=>
            local_region ce es.scopes s n b k` by
    (rpt gen_tac >> irule copy_buffer_local_region_frame >>
     qexists_tac `sa` >> fs[intcall_joint_res_def]) >>
  irule intcall_joint_res_frame >> simp[] >>
  qexistsl_tac [`s`, `sa`] >> simp[] >>
  rpt strip_tac >> Cases_on `op` >>
  gvs[intcall_joint_res_def, eval_operand_def, lookup_var_def] >> metis_tac[]
QED

Theorem intcall_joint_res_mstore:
  intcall_frame_ok fp /\ intcall_joint_res fp ce env es sa s /\
  stmt_state_rel fp.jc_ctx fp.jc_func ce fp.jc_cx es (mstore dst w s) /\
  sa.cs_next_var <= sb.cs_next_var /\
  (!a k. fp.jc_prot a k ==> regions_disjoint a k dst 32) ==>
  intcall_joint_res fp ce env es sb (mstore dst w s)
Proof
  rpt strip_tac >> irule intcall_joint_res_memory_frame >> simp[] >>
  qexistsl_tac [`s`, `sa`] >> simp[] >>
  conj_tac
  >- (rpt strip_tac >>
      irule valueEncodingPropsTheory.mstore_mem_bytes_at_disjoint >>
      fs[regions_disjoint_def]) >>
  simp[venomStateTheory.mstore_def, lookup_var_def]
QED

Theorem intcall_joint_res_readonly:
  intcall_frame_ok fp /\ intcall_joint_res fp ce env es sa s /\
  sa.cs_next_var <= sb.cs_next_var /\
  (u with vs_vars := s.vs_vars) = s /\
  (!x. not_fresh_at sa x ==> lookup_var x u = lookup_var x s) ==>
  intcall_joint_res fp ce env es sb u
Proof
  rpt strip_tac >>
  `stmt_state_rel fp.jc_ctx fp.jc_func ce fp.jc_cx es u` by
    (irule exprSimHashTheory.hash_readonly_state_rel >>
     qexistsl_tac [`s`, `sa`] >> fs[intcall_joint_res_def]) >>
  irule intcall_joint_res_memory_frame >> simp[] >>
  qexistsl_tac [`s`, `sa`] >>
  fs[venom_state_component_equality]
QED
