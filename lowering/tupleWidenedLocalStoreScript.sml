Theory tupleWidenedLocalStore
Ancestors
  tupleWidenedStoreFrame exprLoweringProps compileEnv venomState
  typedCopyRankPathMem tupleLocalStoreProps stmtLowering

Theorem tuple_local_widened_memory_path:
  compile_tuple_store_all cenv [sty] [BaseTarget (NameTarget id)] [op] sa = ((),sb) /\
  cenv.ce_var_type id = SOME dty /\
  ~is_word_type dty /\ ~is_word_type sty /\
  acyclic_struct_metadata cenv.ce_struct_fields /\
  sfields_tenv_consistent cenv.ce_struct_fields (get_tenv cx) /\
  (!name fields. FLOOKUP cenv.ce_struct_fields name = SOME fields ==>
     ALL_DISTINCT (MAP FST fields) /\
     EVERY (\(fname,fty,sz). !tv.
       evaluate_type (get_tenv cx) fty = SOME tv ==> sz = type_memory_size tv) fields) /\
  (!ty tv. evaluate_type (get_tenv cx) ty = SOME tv ==>
     type_memory_bytes cenv ty = type_memory_size tv) /\
  fn_inst_ids_distinct func /\ type_widens_to (get_tenv cx) sty dty /\
  evaluate_type (get_tenv cx) dty = SOME entry.type /\
  evaluate_type (get_tenv cx) sty = SOME stv /\
  value_has_type entry.type v /\ val_wf entry.type v /\
  value_has_type stv v /\ val_wf stv v /\
  val_in_memory stv v (w2n sw) s.vs_memory /\
  w2n sw + type_memory_size stv < dimword (:256) /\
  w2n dw + type_memory_size entry.type < dimword (:256) /\
  type_memory_size entry.type + 64 < dimword (:256) /\
  w2n sw + type_memory_size stv <= s.vs_alloca_next /\
  w2n dw + type_memory_size entry.type <= s.vs_alloca_next /\
  eval_operand op s = SOME sw /\ lookup_var p s = SOME dw /\
  (!x. op = Var x ==> not_fresh_at sa x) /\
  local_ptrs_reserved cenv sa /\ fn_has_code sa sb func /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\ cenv.ce_target CapMcopy /\
  (dty <> sty /\ ~is_bytestring_type dty ==>
    w2n sw + type_memory_size stv <= w2n dw \/
    w2n dw + type_memory_size entry.type <= w2n sw) /\
  stmt_state_rel ctx func cenv cx es s /\
  find_containing_scope id es.scopes = SOME (pre, env, entry, rest) /\
  FLOOKUP cenv.ce_vars id = SOME (PtrVar (Var p) sz) /\
  alloca_history func s /\ return_buf_frame d cenv sa s ==>
  ?t. gas_path_mem ctx func s 0 (OK t) /\
    typed_copy_effect ctx func sa sb s t (w2n dw) (type_memory_size entry.type) /\
    stmt_state_rel ctx func cenv cx
      (es with scopes :=
        pre ++ (env |+ (id, entry with <|value := v; popped := []|>)) :: rest) t /\
    alloca_history func t /\ return_buf_frame d cenv sb t /\
    t.vs_alloca_next = s.vs_alloca_next
Proof
  strip_tac >>
  `compile_tuple_store_all cenv (sty::[]) 
     (BaseTarget (NameTarget id) :: MAP (BaseTarget o NameTarget) [])
     (op::[]) sa = ((),sb)` by simp[] >>
  `is_word_type dty = is_word_type sty` by simp[] >>
  drule_all tuple_store_local_step >>
  simp[compile_tuple_store_all_def, comp_return_def] >> strip_tac >>
  `not_fresh_at sa p` by (fs[local_ptrs_reserved_def] >> metis_tac[]) >>
  `eval_operand (Var p) s = SOME dw` by simp[eval_operand_def] >>
  `type_memory_bytes cenv dty = type_memory_size entry.type /\
   type_memory_bytes cenv sty = type_memory_size stv` by metis_tac[] >>
  drule_at (Pat `compile_store_memory _ _ _ _ _ _ = _`)
    compile_store_memory_nonword_effect_mem >>
  disch_then (drule_at (Pat `val_in_memory _ _ _ _`)) >>
  disch_then (drule_at (Pat `evaluate_type _ dty = _`)) >>
  disch_then (drule_at (Pat `eval_operand (Var p) _ = _`)) >>
  disch_then (drule_at (Pat `fn_has_code _ _ _`)) >>
  disch_then (qspecl_then [`entry.type`, `ctx`] mp_tac) >>
  (impl_tac >- (simp[] >> first_assum ACCEPT_TAC)) >> strip_tac >>
  `sa.cs_next_var <= sb.cs_next_var` by
    (mp_tac (Q.SPECL [`cenv`, `op`, `Var p`, `dty`, `sty`, `sa`]
      ci_mono_compile_store_memory) >> simp[ci_mono_def]) >>
  `alloca_inv s` by fs[stmt_state_rel_def] >>
  drule_all typed_copy_body_frames >> strip_tac >>
  qexists_tac `t` >> simp[] >>
  irule typed_copy_local_write_frame >> goal_assum (drule_at Any) >>
  metis_tac[]
QED
