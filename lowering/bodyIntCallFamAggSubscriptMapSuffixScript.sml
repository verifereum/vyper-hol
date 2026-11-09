(* Joint resources for mapping-key scratch stores. *)
Theory bodyIntCallFamAggSubscriptMapSuffix
Ancestors
  bodyIntCallFamAggSubscriptResources bodyIntCallJointContract
  bodyIntCallJointAggCore exprSimAlloc intCallFrame compileEnv
  exprLoweringProps venomState venomInst

(* A store contained in an allocated scratch region preserves the resources.
   The allocation invariant authorizes it above the protected frontier. *)
Theorem intcall_allocated_mstore_res:
  intcall_frame_ok fp /\ intcall_joint_res fp ce env es sa s /\
  sa.cs_next_var <= sb.cs_next_var /\
  MEM inst (fn_insts fp.jc_func) /\ inst.inst_opcode = ALLOCA /\
  FLOOKUP s.vs_allocas inst.inst_id = SOME (b,sz) /\
  b <= dst /\ dst + 32 <= b + sz /\
  (!name lb len. local_region ce es.scopes s name lb len ==>
     regions_disjoint b sz lb len) ==>
  intcall_joint_res fp ce env es sb (mstore dst w s)
Proof
  rpt strip_tac >>
  `fp.jc_lo <= b` by
    (fs[intcall_joint_res_def, allocas_above_def] >> metis_tac[]) >>
  `stmt_state_rel fp.jc_ctx fp.jc_func ce fp.jc_cx es (mstore dst w s)` by
    (irule literal_mstore_state_rel >>
     reverse conj_tac >- fs[intcall_joint_res_def] >>
     qexistsl_tac [`b`, `inst`, `sz`] >>
     fs[regions_disjoint_def] >> metis_tac[]) >>
  irule intcall_joint_res_mstore >>
  simp[] >> conj_tac
  >- (fs[intcall_frame_ok_def, regions_disjoint_def] >>
      rpt strip_tac >>
      qpat_x_assum `!a k. fp.jc_prot a k ==> a + k <= fp.jc_lo` drule >>
      decide_tac) >>
  qexists_tac `sa` >> simp[]
QED

Theorem intcall_allocated_mstore_run:
  intcall_frame_ok fp /\ intcall_joint_res fp ce env es sa s /\
  emit_void MSTORE [ptr_op; value_op] sa = ((),sb) /\
  eval_operand ptr_op s = SOME addr /\ eval_operand value_op s = SOME w /\
  MEM inst (fn_insts fp.jc_func) /\ inst.inst_opcode = ALLOCA /\
  FLOOKUP s.vs_allocas inst.inst_id = SOME (b,sz) /\
  b <= w2n addr /\ w2n addr + 32 <= b + sz /\
  (!name lb len. local_region ce es.scopes s name lb len ==>
     regions_disjoint b sz lb len) ==>
  ?t. run_inst_seq (emitted_insts sa sb) s = OK t /\
      intcall_joint_res fp ce env es sb t /\
      (t with vs_memory := s.vs_memory) = s
Proof
  rpt strip_tac >>
  drule emitHelperPropsTheory.emitted_insts_emit_void >> strip_tac >>
  qexists_tac `mstore (w2n addr) w s` >>
  conj_tac
  >- (drule_all exprSimLiteralBufferTheory.literal_emit_mstore_run >> simp[]) >>
  reverse conj_tac >- simp[mstore_def] >>
  irule intcall_allocated_mstore_res >> simp[] >>
  conj_tac
  >- (qexistsl_tac [`b`, `inst`, `sz`] >> simp[] >> metis_tac[]) >>
  qexists_tac `sa` >> simp[]
QED

(* Allocate the hash scratch region and initialize its first word. *)
Theorem intcall_alloc_header_run:
  intcall_frame_ok fp /\ intcall_joint_res fp ce env es sa s /\
  compile_alloc_buffer cap sa = (buf,sm) /\
  emit_void MSTORE [buf.buf_operand; value_op] sm = ((),sh) /\
  fn_has_code sa sm fp.jc_func /\ fn_inst_ids_distinct fp.jc_func /\
  32 <= cap /\ cap < dimword (:256) /\
  (!x. value_op = Var x ==> not_fresh_at sa x) /\
  eval_operand value_op s = SOME w ==>
  ?t addr. run_inst_seq (emitted_insts sa sh) s = OK t /\
    intcall_joint_res fp ce env es sh t /\
    eval_operand buf.buf_operand t = SOME addr /\
    FLOOKUP t.vs_allocas sa.cs_next_id = SOME (w2n addr,cap) /\
    w2n addr + cap < dimword (:256) /\
    (!name b len. local_region ce es.scopes t name b len ==>
       regions_disjoint (w2n addr) cap b len)
Proof
  rpt strip_tac >>
  `stmt_state_rel fp.jc_ctx fp.jc_func ce fp.jc_cx es s /\
   local_ptrs_reserved ce sa` by fs[intcall_joint_res_def] >>
  drule_all exprSimAllocTheory.buffer_alloc_code >> strip_tac >>
  drule_all exprSimMapKeyTheory.hash_alloc_capacity_mstore_frame >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts sa sh) s = OK header` >>
  qpat_x_assum `stmt_state_rel _ _ _ _ _ header` kall_tac >>
  drule_all exprSimAllocTheory.literal_alloc_buffer_run >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts sa sm) s = OK allocated` >>
  rename1 `eval_operand buf.buf_operand allocated = SOME allocated_addr` >>
  drule_all intcall_joint_res_alloc >> strip_tac >>
  `allocated.vs_labels = s.vs_labels` by
    (drule_all exprSimAllocTheory.hash_alloc_buffer_labels >> simp[]) >>
  `eval_operand value_op allocated = SOME w` by
    (Cases_on `value_op` >> gvs[eval_operand_def] >> metis_tac[]) >>
  `?u. run_inst_seq (emitted_insts sm sh) allocated = OK u /\
       intcall_joint_res fp ce env es sh u /\
       (u with vs_memory := allocated.vs_memory) = allocated` by
    (irule intcall_allocated_mstore_run >> simp[] >>
     qexistsl_tac [`allocated_addr`, `w2n allocated_addr`,
       `mk_inst sa.cs_next_id ALLOCA [Lit (n2w cap)]
          [STRING #"%" (toString sa.cs_next_var)]`,
       `buf.buf_operand`, `cap`, `value_op`, `w`] >>
     simp[venomInstTheory.mk_inst_def] >> metis_tac[]) >>

  drule_all loweringHaltTheory.compile_alloc_buffer_insts >> strip_tac >>
  `sm.cs_current_insts = sa.cs_current_insts ++ emitted_insts sa sm` by
    simp[emitted_insts_def, rich_listTheory.DROP_LENGTH_APPEND] >>
  drule_all emitHelperPropsTheory.emitted_insts_emit_void >> strip_tac >>
  `run_inst_seq (emitted_insts sa sh) s = OK u` by
    ( `run_inst_seq (emitted_insts sa sh) s =
        run_inst_seq (emitted_insts sm sh) allocated` by
        (irule (cj 1 run_inst_seq_chain) >> simp[]) >> simp[]) >>
  gvs[] >> goal_assum (drule_at Any) >> simp[] >> metis_tac[]
QED
