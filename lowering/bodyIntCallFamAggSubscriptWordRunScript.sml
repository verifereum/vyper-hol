(* Supplied raw execution of an allocation and its first scratch word. *)
Theory bodyIntCallFamAggSubscriptWordRun
Ancestors
  bodyIntCallFamAggSubscriptAllocRun bodyIntCallFamAggSubscriptStoreRun
  bodyIntCallFamAggSubscriptRunCuts bodyIntCallJointContract
  exprSimAlloc exprSimProps exprSimCopy exprSimLiteralBuffer exprLoweringProps
  loweringHalt emitHelperProps compileEnv context venomState venomInst
  intCallFrame

Theorem intcall_alloc_word_run_cont:
  intcall_frame_ok fp /\ intcall_expr_res fp ce env es sa s /\
  compile_alloc_buffer cap sa = (buf,sm) /\
  emit_void MSTORE [buf.buf_operand; value_op] sm = ((),sh) /\
  fn_has_code sa sm fp.jc_func /\ fn_has_code sm sh fp.jc_func /\
  fn_inst_ids_distinct fp.jc_func /\ 32 <= cap /\ cap < dimword (:256) /\
  (!x. value_op = Var x ==> not_fresh_at sa x) /\
  eval_operand value_op s = SOME w /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  run_inst_seq (emitted_insts sa sh) s = OK t ==>
  intcall_expr_cont fp ce env es sa s es sh
    (t with vs_inst_idx := LENGTH sh.cs_current_insts) /\
  ?addr. eval_operand buf.buf_operand t = SOME addr /\
    FLOOKUP t.vs_allocas sa.cs_next_id = SOME (w2n addr,cap) /\
    w2n addr + cap < dimword (:256) /\
    (!n lb len. local_region ce es.scopes s n lb len ==>
      regions_disjoint (w2n addr) cap lb len) /\
    (?x. buf.buf_operand = Var x /\ not_fresh_at sh x)
Proof
  rpt gen_tac >> strip_tac >>
  drule buffer_alloc_code >> strip_tac >>
  drule compile_alloc_buffer_insts >> strip_tac >>
  drule emitted_insts_emit_void >> strip_tac >>
  `sm.cs_current_insts = sa.cs_current_insts ++ emitted_insts sa sm` by
    simp[emitted_insts_def, DROP_PREFIX] >>
  `sh.cs_current_insts = sm.cs_current_insts ++ emitted_insts sm sh` by simp[] >>
  `EVERY (\i. ~is_terminator i.inst_opcode) (emitted_insts sm sh)` by
    simp[mk_inst_def, is_terminator_def] >>
  drule_all subscript_run_split >> strip_tac >>
  drule_all intcall_alloc_run_cont >> strip_tac >>
  rename1 `eval_operand buf.buf_operand mid = SOME addr` >>
  `sa.cs_next_var <= sm.cs_next_var` by
    (drule compile_alloc_buffer_parts >> simp[]) >>
  `!n lb len. local_region ce es.scopes s n lb len ==>
      regions_disjoint (w2n addr) cap lb len` by
    (rpt strip_tac >> first_x_assum irule >> qexists_tac `n` >>
     irule local_region_frame_fwd >>
     qexistsl_tac [`s`, `sa`, `es.scopes`] >>
     fs[intcall_expr_cont_def, intcall_expr_res_def,
        local_region_def, lookup_var_def] >> metis_tac[]) >>
  drule_all bodyIntCallJointAggCoreTheory.intcall_alloc_run_frame >> strip_tac >>
  `eval_operand value_op (mid with vs_inst_idx := LENGTH sm.cs_current_insts) = SOME w` by
    (Cases_on `value_op` >> gvs[eval_operand_def, lookup_var_def] >>
     fs[intcall_expr_cont_def, lookup_var_def, venom_state_component_equality] >>
     metis_tac[]) >>
  `eval_operand buf.buf_operand (mid with vs_inst_idx := LENGTH sm.cs_current_insts) =
   SOME addr` by simp[eval_operand_def, lookup_var_def] >>
  `MEM (mk_inst sa.cs_next_id ALLOCA [Lit (n2w cap)]
    [STRING #"%" (toString sa.cs_next_var)]) (fn_insts fp.jc_func) /\
   (mk_inst sa.cs_next_id ALLOCA [Lit (n2w cap)]
    [STRING #"%" (toString sa.cs_next_var)]).inst_opcode = ALLOCA /\
   sa.cs_next_id <= sa.cs_next_id /\ w2n addr <= w2n addr /\
   w2n addr + 32 <= w2n addr + cap /\
   FLOOKUP (mid with vs_inst_idx := LENGTH sm.cs_current_insts).vs_allocas
     sa.cs_next_id = SOME (w2n addr,cap)` by simp[venomInstTheory.mk_inst_def] >>
  qabbrev_tac `ai = mk_inst sa.cs_next_id ALLOCA [Lit (n2w cap)]
    [STRING #"%" (toString sa.cs_next_var)]` >>
  `sa.cs_next_id <= ai.inst_id /\
   FLOOKUP (mid with vs_inst_idx := LENGTH sm.cs_current_insts).vs_allocas
     ai.inst_id = SOME (w2n addr,cap)` by simp[Abbr `ai`, mk_inst_def] >>
  drule_all intcall_scratch_store_run_cont >> simp[] >> strip_tac >>
  drule_all literal_emit_mstore_run >> strip_tac >>
  `t.vs_vars = mid.vs_vars /\ t.vs_allocas = mid.vs_allocas` by
    fs[venom_state_component_equality, mstore_def] >>
  qexists_tac `addr` >> gvs[lookup_var_def, eval_operand_def, not_fresh_at_def] >>
  first_assum ACCEPT_TAC
QED
