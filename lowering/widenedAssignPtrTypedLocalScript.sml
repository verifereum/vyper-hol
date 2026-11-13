(* Counted typed copying and semantic local landing share one endpoint. *)
Theory widenedAssignPtrTypedLocal
Ancestors widenedAssignPtrCopyRecursive aggregateStorePtr widenedAssignPtrLocalLanding
  tupleLocalStoreRun bodyPtrDefs compileEnv loweringStateRelDefs
  exprLoweringProps localPtrsProps allocLimits valueEncoding valueEncodingDefs
  vyperLookup venomState venomExecSemantics ptrDiscipline finite_map words

Theorem widened_assign_typed_local_store_ptr:
  !cenv tenv ctx D PG dty sty stv v a b p src dw sw fn G tn s
    d cx es es' id pre sc entry rest sz.
    acyclic_struct_metadata cenv.ce_struct_fields /\
    sfields_tenv_consistent cenv.ce_struct_fields tenv /\
    (!name fields. FLOOKUP cenv.ce_struct_fields name = SOME fields ==>
      ALL_DISTINCT (MAP FST fields) /\
      EVERY (\(fname,fty,sz). !tv. evaluate_type tenv fty = SOME tv ==>
        sz = type_memory_size tv) fields) /\
    type_widens_to tenv sty dty /\
    evaluate_type tenv sty = SOME stv /\
    evaluate_type tenv dty = SOME entry.type /\
    value_has_type stv v /\ value_has_type entry.type v /\
    val_wf stv v /\ val_wf entry.type v /\
    ~is_word_type dty /\ type_memory_bytes cenv dty = type_memory_size entry.type /\
    compile_store_memory cenv (Var src) (Var p) dty sty a = ((),b) /\
    not_fresh_at a src /\ lookup_var src s = SOME sw /\
    op_taint tn (Var src) = {} /\
    (0 < type_memory_size stv ==> ptr_covers G tn src s (type_memory_size stv)) /\
    w2n sw + type_memory_size stv < dimword (:256) /\
    (w2n dw + type_memory_size entry.type <= w2n sw \/
     w2n sw + type_memory_size stv <= w2n dw) /\
    (!m. mem_agree_outside tn.t_mem s.vs_memory m ==>
      val_in_memory stv v (w2n sw) m) /\
    fn_has_code a b fn /\ fn_inst_ids_distinct fn /\
    s.vs_current_bb = a.cs_current_bb /\
    s.vs_inst_idx = LENGTH a.cs_current_insts /\ ~s.vs_halted /\
    ~ctx_has_dalloca ctx /\
    stmt_state_rel ctx fn cenv cx es s /\ ghost_inv d cenv cx es G tn s /\
    find_containing_scope id es.scopes = SOME (pre,sc,entry,rest) /\
    write_place cx (MemoryPlace id []) v es = (INL (),es') /\
    FLOOKUP cenv.ce_vars id = SOME (PtrVar (Var p) sz) /\
    lookup_var p s = SOME dw /\ local_ptrs_reserved cenv a /\
    (!x cap. cenv.ce_return_buf = SOME (PtrVar (Var x) cap) ==> not_fresh_at a x) /\
    (!x cap. cenv.ce_return_pc = SOME (PtrVar (Var x) cap) ==> not_fresh_at a x) ==>
    ?G' tn' t.
      gas_path_ptr D 0 ctx fn PG G tn s 0 G' tn' (OK t) /\
      t.vs_current_bb = b.cs_current_bb /\
      t.vs_inst_idx = LENGTH b.cs_current_insts /\ ~t.vs_halted /\
      (!m. mem_agree_outside tn'.t_mem t.vs_memory m ==>
        val_in_memory entry.type v (w2n dw) m) /\
      typed_copy_state_frame a (w2n dw) (type_memory_size entry.type) s t /\
      (!x. not_fresh_at a x ==>
        lookup_var x t = lookup_var x s /\ FLOOKUP G' x = FLOOKUP G x /\
        op_taint tn' (Var x) = op_taint tn (Var x)) /\
      tn'.t_stor = tn.t_stor /\ tn'.t_trans = tn.t_trans /\ tn'.t_imm = tn.t_imm /\
      (!i. ~(w2n dw <= i /\ i < w2n dw + type_memory_size entry.type) ==>
        (i IN tn'.t_mem <=> i IN tn.t_mem)) /\
      stmt_state_rel ctx fn cenv cx es' t /\ ghost_inv d cenv cx es' G' tn' t
Proof
  rpt gen_tac >> strip_tac >>
  `lookup_scopes id es.scopes = SOME entry` by
    metis_tac[find_containing_scope_lookup] >>
  drule_all tuple_store_destination_region >> strip_tac >>
  `not_fresh_at a p` by metis_tac[local_ptrs_reserved_def] >>
  `ptr_covers G tn p s sz` by (fs[ghost_inv_def] >> metis_tac[]) >>
  `ptr_covers G tn p s (type_memory_size entry.type)` by
    (fs[ptr_covers_def] >> metis_tac[arithmeticTheory.LESS_EQ_TRANS]) >>
  `local_ptrs_rel fn cenv es.scopes s /\ alloca_room ctx fn s` by
    fs[stmt_state_rel_def, state_rel_def] >>
  `w2n dw + sz <= s.vs_alloca_next` by
    (qpat_assum `local_ptrs_rel _ _ _ _`
       (strip_assume_tac o REWRITE_RULE [local_ptrs_rel_def]) >>
     first_x_assum drule_all >> strip_tac >> gvs[]) >>
  `s.vs_alloca_next < dimword (:256)` by metis_tac[alloca_room_next_lt] >>
  `w2n dw + type_memory_size entry.type < dimword (:256)` by decide_tac >>
  `eval_operand (Var p) s = SOME dw /\ eval_operand (Var src) s = SOME sw /\
   op_taint tn (Var p) = {}` by gvs[eval_operand_def, ptr_covers_def] >>
  mp_tac (Q.SPECL [`cenv`,`tenv`,`ctx`,`D`,`PG`,`dty`,`sty`,
    `entry.type`,`stv`,`v`] compile_store_memory_aggregate_counted_ptr) >>
  (impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)) >>
  disch_then (qspecl_then [`a`,`b`,`p`,`Var src`,`dw`,`sw`,`fn`,`G`,`tn`,`s`] mp_tac) >>
  (impl_tac >- (simp[] >> metis_tac[])) >> strip_tac >>
  rename1 `gas_path_ptr D 0 ctx fn PG G tn s 0 Gf tf (OK t)` >>
  `stmt_state_rel ctx fn cenv cx es' t /\ ghost_inv d cenv cx es' Gf tf t` by
    (irule widened_local_write_landing_ptr >>
     goal_assum (drule_at (Pat `write_place _ _ _ _ = _`)) >>
     goal_assum (drule_at (Pat `typed_copy_state_frame _ _ _ _ _`)) >>
     goal_assum (drule_at (Pat `ghost_inv _ _ _ _ _ _ _`)) >>
     simp[] >> metis_tac[]) >>
  qexistsl_tac [`Gf`, `tf`, `t`] >> gvs[] >> metis_tac[]
QED
