(* Join semantic return correctness with all-fuel memory safety. *)
Theory internalReturnBufferMem
Ancestors
  internalReturnBufferValue internalReturnBufferSafety runFromGasPathMem
  stmtSimDefs loweringStateRelDefs loweringPosts fragExec valueEncoding
  valueCopyBytes exprLoweringProps
  compileEnv vyperState venomState finite_map list arithmetic

Theorem compile_internal_return_buffer_path_mem:
  compile_return_unlock cenv sa = ((),su) /\
  compile_internal_return cenv (SOME src) rpc cenv.ce_returns_count
    ty sty ets (SOME dst) su = ((),sb) /\
  cenv.ce_returns_count = 0 /\
  (!x. src = Var x ==> not_fresh_at sa x) /\
  (!x. dst = Var x ==> not_fresh_at sa x) /\
  (!x. rpc = Var x ==> not_fresh_at sa x) /\
  (!x. cenv.ce_imm_alloca = SOME (Var x) ==> not_fresh_at sa x) /\
  evaluate_type (get_tenv cx) ty = SOME tv /\
  evaluate_type (get_tenv cx) sty = SOME stv /\
  value_has_type tv v /\ val_wf tv v /\ value_has_type stv v /\
  type_memory_bytes cenv ty = type_memory_size tv /\ ~is_word_type ty /\
  (sty = ty \/ is_bytestring_type sty /\ is_bytestring_type ty) /\
  w2n bw + type_memory_size tv + 64 < dimword (:256) /\
  (cenv.ce_is_ctor ==> !name itv iv off.
     FLOOKUP cenv.ce_module_vars (cenv.ce_module,name) =
       SOME (ImmutableLoc off) /\
     FLOOKUP (case ALOOKUP es.immutables cx.txn.target of NONE => FEMPTY
       | SOME imms => get_source_immutables cenv.ce_module imms) name =
       SOME (itv,iv) ==>
     regions_disjoint off (type_memory_size itv) (w2n bw)
       (type_memory_size tv)) /\
  fn_has_code sa sb func /\ fn_has_code sa su func /\ fn_has_code su sb func /\
  stmt_state_rel ctx func cenv cx (es with scopes := []) s /\
  expr_val_rel cx sty v src s /\ eval_operand src s = SOME sw /\
  eval_operand dst s = SOME bw /\ eval_operand rpc s = SOME pc /\
  (val_store_size stv v = 0 \/
   w2n sw + val_store_size stv v <= s.vs_alloca_next) /\
  w2n bw + type_memory_size tv <= s.vs_alloca_next /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?n r. gas_path_mem ctx func s n r /\
    intret_mem_q func cenv cx tv bw v (es with scopes := []) r
Proof
  strip_tac >>
  `~is_word_type sty` by metis_tac[is_bytestring_word_type] >>
  `val_in_memory stv v (w2n sw) s.vs_memory` by fs[expr_val_rel_def] >>
  `~s.vs_call_ctx.cc_static` by fs[stmt_state_rel_def, state_rel_def] >>
  `type_memory_size tv + 64 < dimword (:256)` by decide_tac >>
  `frag_exec ctx sa sb
     (\s. stmt_state_rel ctx func cenv cx (es with scopes := []) s /\
          expr_val_rel cx sty v src s /\ eval_operand dst s = SOME bw /\
          ?pc. eval_operand rpc s = SOME pc)
     (\s. F) (intret_mem_q func cenv cx tv bw v (es with scopes := []))` by
    (irule compile_internal_return_buffer_value_frag >> metis_tac[]) >>
  pop_assum mp_tac >> simp[frag_exec_def] >>
  disch_then (qspec_then `func` mp_tac) >>
  disch_then (qspec_then `s` mp_tac) >>
  (impl_tac >- metis_tac[]) >> strip_tac >>
  `!fuel. mem_safe_run fuel ctx func s` by
    (qpat_x_assum `compile_internal_return _ _ _ _ _ _ _ _ _ = _` mp_tac >>
     simp[] >> strip_tac >>
     irule compile_internal_return_buffer_mem_safe >> simp[] >>
     goal_assum (drule_at (Pat `compile_return_unlock _ _ = _`)) >>
     goal_assum (drule_at (Pat `compile_internal_return _ _ _ _ _ _ _ _ _ = _`)) >>
     metis_tac[ADD_COMM]) >>
  metis_tac[run_from_gas_path_mem]
QED
