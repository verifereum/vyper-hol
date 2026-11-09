(* Counted stages of the fresh mapping scratch allocation. *)
Theory bodyIntCallFamAggSubscriptScratchStages
Ancestors
  bodyIntCallFamAggSubscriptScratch bodyIntCallFamAggSubscriptStore
  bodyIntCallJointAggCore bodyIntCallJointContract exprSimAlloc exprSimMapKey
  exprSimProps exprSimCopy fragGasMode fragExec compileEnv context
  emitHelperProps exprLoweringProps venomState venomInst intCallFrame
  emitHelper stmtSimAugAssignPlaceMemory

Theorem intcall_alloc_word_cont:
  intcall_frame_ok fp /\ intcall_joint_res fp ce env es sa s /\
  compile_alloc_buffer cap sa = (buf,sm) /\
  emit_void MSTORE [buf.buf_operand; value_op] sm = ((),sh) /\
  fn_has_code sa sm fp.jc_func /\ fn_has_code sm sh fp.jc_func /\
  fn_inst_ids_distinct fp.jc_func /\ 32 <= cap /\ cap < dimword (:256) /\
  (!x. value_op = Var x ==> not_fresh_at sa x) /\
  eval_operand value_op s = SOME w /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?u addr. gas_marked_path F fp.jc_ctx fp.jc_func s 0 (OK u) /\
    intcall_expr_cont fp ce env es sa s es sh u /\
    eval_operand buf.buf_operand u = SOME addr /\
    FLOOKUP u.vs_allocas sa.cs_next_id = SOME (w2n addr,cap) /\
    w2n addr + cap < dimword (:256) /\
    (!n lb len. local_region ce es.scopes s n lb len ==>
      regions_disjoint (w2n addr) cap lb len) /\
    (?x. buf.buf_operand = Var x /\ not_fresh_at sh x)
Proof
  rpt gen_tac >> strip_tac >>
  drule_all intcall_alloc_landing >> strip_tac >>
  rename1 `intcall_expr_cont fp ce env es sa s es sm allocated` >>
  rename1 `eval_operand buf.buf_operand allocated = SOME addr` >>
  drule_all buffer_alloc_code >> strip_tac >>
  drule emitted_insts_emit_void >> strip_tac >>
  `sa.cs_next_var <= sm.cs_next_var` by
    (drule loweringHaltTheory.compile_alloc_buffer_parts >> simp[]) >>
  `!n lb len. local_region ce es.scopes s n lb len ==>
       regions_disjoint (w2n addr) cap lb len` by
    (rpt strip_tac >>
     qpat_x_assum `!name b len. local_region _ _ allocated _ _ _ ==> _` irule >>
     qexists_tac `n` >> irule local_region_frame_fwd >>
     qexistsl_tac [`s`, `sa`, `es.scopes`] >>
     fs[intcall_expr_cont_def, intcall_joint_res_def] >> metis_tac[]) >>
  `eval_operand value_op allocated = SOME w` by
    (`allocated.vs_labels = s.vs_labels` by
       (drule aug_place_marked_path_labels >> simp[]) >>
     Cases_on `value_op` >> gvs[eval_operand_def] >>
     fs[intcall_expr_cont_def] >> metis_tac[]) >>
  `gas_marked_path F fp.jc_ctx fp.jc_func allocated 0
      (OK (mstore (w2n addr) w allocated with
        vs_inst_idx := LENGTH sh.cs_current_insts)) /\
   intcall_expr_cont fp ce env es sa s es sh
      (mstore (w2n addr) w allocated with
        vs_inst_idx := LENGTH sh.cs_current_insts)` by
    (irule intcall_allocated_mstore_landing >> simp[] >>
     conj_tac >- fs[intcall_expr_cont_def, intcall_joint_res_def,
                    stmt_state_rel_def] >>
     reverse conj_tac
     >- (qexistsl_tac [`buf.buf_operand`, `sm`, `value_op`] >> simp[]) >>
     qexistsl_tac [`w2n addr`,
       `mk_inst sa.cs_next_id ALLOCA [Lit (n2w cap)]
         [STRING #"%" (toString sa.cs_next_var)]`, `cap`] >>
     simp[mk_inst_def] >> conj_tac
     >- (fs[regions_disjoint_def] >> metis_tac[]) >>
     conj_tac >- (fs[regions_disjoint_def] >> metis_tac[]) >>
     fs[intcall_expr_cont_def, intcall_joint_res_def, allocas_above_def] >>
     qpat_x_assum `!aid b sz. FLOOKUP allocated.vs_allocas aid = SOME (b,sz) ==> _`
       drule >> simp[]) >>
  `gas_marked_path F fp.jc_ctx fp.jc_func s 0
      (OK (mstore (w2n addr) w allocated with
        vs_inst_idx := LENGTH sh.cs_current_insts))` by
    (drule_all gas_marked_path_then >> simp[]) >>
  qexistsl_tac [`mstore (w2n addr) w allocated with
    vs_inst_idx := LENGTH sh.cs_current_insts`, `addr`] >>
  gvs[eval_operand_def, lookup_var_def, mstore_def, not_fresh_at_def] >>
  gvs[]
QED
