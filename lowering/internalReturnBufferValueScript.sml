(* Compatible caller-buffer returns reuse the exact S1 epilogue frame. *)
Theory internalReturnBufferValue
Ancestors
  intCallReturnMem exprSimAggregateLoops valueCopyBytes stmtLowering loweringPosts fragExec
  compileEnv valueEncoding vyperState venomState list finite_map

Theorem internal_return_buffer_source_code[local]:
  (sty = ty \/ is_bytestring_type sty /\ is_bytestring_type ty) ==>
  compile_internal_return cenv (SOME op) rpc 0 ty sty ets (SOME dst) =
  compile_internal_return cenv (SOME op) rpc 0 ty ty ets (SOME dst)
Proof
  strip_tac >> simp[compile_internal_return_def] >>
  metis_tac[compile_store_memory_bytestring_src]
QED

Theorem compile_internal_return_buffer_value_frag:
  !ctx func cenv cx es ty sty tv stv v val_op rpc elem_types buf_op sa su sb bw.
    compile_return_unlock cenv sa = ((),su) /\
    compile_internal_return cenv (SOME val_op) rpc cenv.ce_returns_count
      ty sty elem_types (SOME buf_op) su = ((),sb) /\
    cenv.ce_returns_count = 0 /\
    (!x. val_op = Var x ==> not_fresh_at sa x) /\
    (!x. buf_op = Var x ==> not_fresh_at sa x) /\
    (!x. rpc = Var x ==> not_fresh_at sa x) /\
    (!x. cenv.ce_imm_alloca = SOME (Var x) ==> not_fresh_at sa x) /\
    evaluate_type (get_tenv cx) ty = SOME tv /\ value_has_type tv v /\
    val_wf tv v /\ type_memory_bytes cenv ty = type_memory_size tv /\
    evaluate_type (get_tenv cx) sty = SOME stv /\ value_has_type stv v /\
    ~is_word_type ty /\
    (sty = ty \/ is_bytestring_type sty /\ is_bytestring_type ty) /\
    w2n bw + type_memory_size tv + 64 < dimword (:256) /\
    (cenv.ce_is_ctor ==> !name itv iv off.
       FLOOKUP cenv.ce_module_vars (cenv.ce_module,name) =
         SOME (ImmutableLoc off) /\
       FLOOKUP (case ALOOKUP es.immutables cx.txn.target of NONE => FEMPTY
         | SOME imms => get_source_immutables cenv.ce_module imms) name =
         SOME (itv,iv) ==>
       regions_disjoint off (type_memory_size itv) (w2n bw)
         (type_memory_size tv)) ==>
    frag_exec ctx sa sb
      (\s. stmt_state_rel ctx func cenv cx (es with scopes := []) s /\
           expr_val_rel cx sty v val_op s /\
           eval_operand buf_op s = SOME bw /\
           ?pc. eval_operand rpc s = SOME pc)
      (\s. F)
      (intret_mem_q func cenv cx tv bw v (es with scopes := []))
Proof
  rpt gen_tac >> strip_tac >>
  `compile_internal_return cenv (SOME val_op) rpc cenv.ce_returns_count
     ty ty elem_types (SOME buf_op) su = ((),sb)` by
    metis_tac[internal_return_buffer_source_code] >>
  drule_all compile_internal_return_memory_frag >>
  simp[frag_exec_def] >> rpt strip_tac >>
  first_x_assum irule >> simp[] >>
  metis_tac[exprSimAggregateLoopsTheory.expr_val_rel_compatible]
QED
