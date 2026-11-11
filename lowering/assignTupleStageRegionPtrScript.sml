(* Full local-capacity separation at the existing tuple staging endpoint. *)
Theory assignTupleStageRegionPtr
Ancestors
  assignTupleLayoutStagePtr tupleStageProps localPtrsProps emitHelperProps
  loweringStateRelDefs exprLoweringProps venomInst
Libs
  monadsyntax

Theorem optional_tuple_stage_region_run_ptr:
  !ctx func cenv cx es flag tys tvs vs se sa sb staged op s sw d D PG G tn.
    (if flag then
       do buf <- compile_alloc_buffer (type_memory_bytes cenv (TupleT tys));
          emit_void MCOPY [buf.buf_operand; op;
            Lit (n2w (type_memory_bytes cenv (TupleT tys)))];
          comp_return buf.buf_operand od
     else comp_return op) sa = (staged,sb) /\
    evaluate_type (get_tenv cx) (TupleT tys) = SOME (TupleTV tvs) /\
    value_has_type (TupleTV tvs) (ArrayV (TupleV vs)) /\
    expr_val_rel cx (TupleT tys) (ArrayV (TupleV vs)) op s /\
    expr_val_at cenv cx (TupleT tys) se sa es (ArrayV (TupleV vs)) op s /\
    eval_operand op s = SOME sw /\
    0 < type_memory_size_list tvs /\
    type_memory_bytes cenv (TupleT tys) = type_memory_size_list tvs /\
    (flag ==> type_memory_size_list tvs < dimword (:256)) /\
    fn_has_code sa sb func /\ local_ptrs_reserved cenv sa /\
    (!x. op = Var x ==> not_fresh_at sa x) /\
    stmt_state_rel ctx func cenv cx es s /\ fn_inst_ids_distinct func /\
    ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
    s.vs_inst_idx = LENGTH sa.cs_current_insts /\
    ~ctx_has_dalloca ctx /\
    ptr_val_ok cx (TupleT tys) (ArrayV (TupleV vs)) op G tn s /\
    (!w. eval_operand op s = SOME w /\
       type_memory_bytes cenv (TupleT tys) <> 0 ==>
       ?x b sz. op = Var x /\ FLOOKUP G x = SOME (b,sz) /\
         b <= w2n w /\
         w2n w + type_memory_bytes cenv (TupleT tys) <= b+sz) /\
    ghost_inv d cenv cx es G tn s /\
    (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
    (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) ==>
    tuple_val_wf vs tvs /\ values_have_types tvs vs /\
    ?t w G' tn'. eval_operand staged t = SOME w /\
      tuple_in_memory vs tvs (w2n w) t.vs_memory /\
      stmt_state_rel ctx func cenv cx es t /\
      (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s) /\
      (!aid entry. FLOOKUP s.vs_allocas aid = SOME entry ==>
        FLOOKUP t.vs_allocas aid = SOME entry) /\
      (!x. staged = Var x ==> not_fresh_at sb x) /\
      ~t.vs_halted /\ t.vs_current_bb = sb.cs_current_bb /\
      t.vs_inst_idx = LENGTH sb.cs_current_insts /\
      (?b sz. b <= w2n w /\
        w2n w + type_memory_size_list tvs <= b + sz /\
        ((?aid. FLOOKUP t.vs_allocas aid = SOME (b,sz)) \/
         (?name. local_region cenv es.scopes t name b sz))) /\
      gas_path_ptr D 0 ctx func PG G tn s 0 G' tn' (OK t) /\
      ghost_inv d cenv cx es G' tn' t /\
      ptr_val_ok cx (TupleT tys) (ArrayV (TupleV vs)) staged G' tn' t /\
      (!w. eval_operand staged t = SOME w /\
         type_memory_bytes cenv (TupleT tys) <> 0 ==>
         ?x b sz. staged = Var x /\ FLOOKUP G' x = SOME (b,sz) /\
           b <= w2n w /\
           w2n w + type_memory_bytes cenv (TupleT tys) <= b+sz) /\
      (!x. not_fresh_at sa x ==> FLOOKUP G' x = FLOOKUP G x /\
        op_taint tn' (Var x) = op_taint tn (Var x)) /\
      (flag ==> ?b. FLOOKUP t.vs_allocas sa.cs_next_id =
          SOME (b,type_memory_size_list tvs) /\ w2n w = b /\
        (!name entry p sz u. lookup_scopes name es.scopes = SOME entry /\
          FLOOKUP cenv.ce_vars name = SOME (PtrVar (Var p) sz) /\
          lookup_var p t = SOME u ==>
          w2n u + val_footprint entry.type entry.value <= b \/
          b + type_memory_size_list tvs <= w2n u) /\
        (!n lb len. local_region cenv es.scopes t n lb len ==>
          regions_disjoint b (type_memory_size_list tvs) lb len))
Proof
  rpt gen_tac >> strip_tac >>
  drule_all optional_tuple_stage_layout_run_ptr >>
  disch_then (qspecl_then [`D`, `PG`]
    (CONJUNCTS_THEN2 assume_tac (CONJUNCTS_THEN2 assume_tac
      (qx_choosel_then [`t`,`w`,`G'`,`tn'`]
        (map_every assume_tac o CONJUNCTS))))) >>
  asm_rewrite_tac [] >>
  qexistsl_tac [`t`, `w`, `G'`, `tn'`] >>
  asm_rewrite_tac [] >>
  conj_tac >- (metis_tac [arithmeticTheory.ADD_COMM]) >>
  strip_tac >>
  qpat_x_assum `flag ==> _` mp_tac >> simp[] >> strip_tac >>
  asm_rewrite_tac [] >>
  qpat_x_assum `(if flag then _ else _) sa = _` mp_tac >>
  asm_rewrite_tac [] >> strip_tac >>
  drule_all tuple_stage_copy_parts >> strip_tac >>
  `not_local_ptr cenv es.scopes p` by
    (fs[local_ptrs_reserved_def, not_local_ptr_def] >> metis_tac[]) >>
  drule_all loweringHaltTheory.emit_inst_fn_member >> strip_tac >>
  rpt strip_tac >>
  irule local_ptrs_rel_alloca_disjoint >>
  goal_assum (drule_at Any) >>
  qexistsl_tac [`func`, `mk_inst sx.cs_next_id ALLOCA
    [Lit (n2w (type_memory_size_list tvs))] [p]`, `p`] >>
  gvs[stmt_state_rel_def, state_rel_def, venomInstTheory.mk_inst_def]
QED
