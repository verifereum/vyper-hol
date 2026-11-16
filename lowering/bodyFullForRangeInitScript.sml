Theory bodyFullForRangeInit
Ancestors
  bodyFullAllocaFresh bodyFullGhostFrame bodyMemoryDefs stmtSimForRange
  venomState venomExecSemantics exprLoweringProps loweringStateRelDefs
  loweringPosts ptrDiscipline bodyPtrDefs finite_map pred_set

Theorem for_range_literal_initial_inv:
  expr_sim_inv cenv cx env es /\ n1 <= n2 /\
  Num (n2-n1) < dimword (:256) /\ local_ptrs_reserved cenv sa /\
  (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  return_buf_frame d cenv sa s0 /\ alloca_history func s0 /\
  (!H. valid_horizon cx st0 H es.storage_trace ==>
    stmt_state_rel H ctx func cenv cx es s0 /\
    storage_well_formed_on cx es (FST H) /\
    ghost_inv_at (DF H) lo d cenv cx es G0 tn0 s0) /\
  t.vs_current_bb = sb.cs_current_bb /\
  t.vs_inst_idx = LENGTH sb.cs_current_insts /\
  t with <|vs_vars := s0.vs_vars; vs_allocas := s0.vs_allocas;
           vs_alloca_next := s0.vs_alloca_next;
           vs_inst_idx := s0.vs_inst_idx|> = s0 /\
  (!H : (bool # bytes32 # type_value) list # num list.
        stmt_state_rel H ctx func cenv cx es s0 ==>
        stmt_state_rel H ctx func cenv cx es t) /\
  alloca_history func t /\ allocas_from lo t /\
  s0.vs_alloca_next <= t.vs_alloca_next /\
  lookup_var q t = SOME w /\ ptr_covers G' tn' q t 32 /\
  FLOOKUP t.vs_allocas sa.cs_next_id = SOME (w2n w,32) /\
  w2n w + 32 < dimword (:256) /\ w2n w + 32 <= t.vs_alloca_next /\
  (!aid e. FLOOKUP s0.vs_allocas aid = SOME e ==>
           FLOOKUP t.vs_allocas aid = SOME e) /\
  (!aid b len. aid < sa.cs_next_id /\
    FLOOKUP s0.vs_allocas aid = SOME (b,len) ==>
    regions_disjoint (w2n w) 32 b len) /\
  (!name b len. local_region cenv es.scopes t name b len ==>
    regions_disjoint (w2n w) 32 b len) /\
  tn'.t_stor = tn0.t_stor /\ tn'.t_trans = tn0.t_trans /\
  tn'.t_imm = tn0.t_imm /\
  (!i. i IN tn'.t_mem <=> i IN tn0.t_mem \/
       (s0.vs_alloca_next <= i /\ i < w2n w + 32)) /\
  (!x. not_fresh_at sa x ==>
    lookup_var x t = lookup_var x s0 /\ FLOOKUP G' x = FLOOKUP G0 x /\
    op_taint tn' (Var x) = op_taint tn0 (Var x)) /\
  ~t.vs_halted /\ e0 = jump_to entry_lbl t /\
  ec = jump_to cond_lbl (update_var ev (i2w n2) (update_var cv (i2w n1) e0)) /\
  q <> cv /\ q <> ev /\
  (!x. not_fresh_at sa x ==> x <> cv /\ x <> ev) /\
  lookup_var cv ec = SOME (i2w n1) /\ lookup_var ev ec = SOME (i2w n2) /\
  FLOOKUP Gentry cv = NONE /\ FLOOKUP Gentry ev = NONE /\
  op_taint tnentry (Var cv) = {} /\ op_taint tnentry (Var ev) = {} /\
  tnentry.t_mem = tn'.t_mem /\ tnentry.t_stor = tn'.t_stor /\
  tnentry.t_trans = tn'.t_trans /\ tnentry.t_imm = tn'.t_imm /\
  (!v. v <> cv /\ v <> ev ==>
    lookup_var v ec = lookup_var v e0 /\ FLOOKUP Gentry v = FLOOKUP G' v /\
    op_taint tnentry (Var v) = op_taint tn' (Var v)) ==>
  let Inv = \H rs ee G tn s.
    expr_sim_inv cenv cx env ee /\
    stmt_state_rel H ctx func cenv cx ee s /\
    storage_well_formed_on cx ee (FST H) /\
    return_buf_frame d cenv sa s /\ alloca_history func s /\
    s0.vs_alloca_next <= s.vs_alloca_next /\ allocas_from lo s /\
    ghost_inv_at (DF H) lo d cenv cx ee G tn s /\
    ~s.vs_halted /\ s.vs_current_bb = cond_lbl /\ s.vs_inst_idx = 0 /\
    lookup_var q s = SOME w /\ ptr_covers G tn q s 32 /\
    FLOOKUP s.vs_allocas sa.cs_next_id = SOME (w2n w,32) /\
    w2n w + 32 < dimword (:256) /\ w2n w + 32 <= s.vs_alloca_next /\
    (!name b len. local_region cenv ee.scopes s name b len ==>
      regions_disjoint (w2n w) 32 b len) /\
    FLOOKUP G cv = NONE /\ FLOOKUP G ev = NONE /\
    op_taint tn (Var cv) = {} /\ op_taint tn (Var ev) = {} /\
    lookup_var ev s = SOME (i2w n2) /\
    (?k. k <= Num (n2-n1) /\
      rs = DROP k (GENLIST (\j. Value (IntV (n1 + &j))) (Num (n2-n1))) /\
      lookup_var cv s = SOME (i2w (n1 + &k)) /\
      n1 + &k <= n2 /\ Num (n2-n1) < dimword (:256)) /\
    (!x v. not_fresh_at sa x /\ lookup_var x s0 = SOME v ==>
      lookup_var x s = SOME v) /\
    (!aid bl. FLOOKUP s0.vs_allocas aid = SOME bl ==>
      FLOOKUP s.vs_allocas aid = SOME bl) /\
    (!x. not_fresh_at sa x ==>
      FLOOKUP G x = FLOOKUP G0 x /\
      op_taint tn (Var x) = op_taint tn0 (Var x))
  in !H. valid_horizon cx st0 H es.storage_trace ==>
    Inv H (GENLIST (\j. Value (IntV (n1 + &j))) (Num (n2-n1)))
      es Gentry tnentry ec
Proof
  strip_tac >> simp_tac bool_ss [LET_THM] >> gen_tac >> strip_tac >>
  `stmt_state_rel H ctx func cenv cx es s0 /\
   storage_well_formed_on cx es (FST H) /\
   ghost_inv_at (DF H) lo d cenv cx es G0 tn0 s0` by metis_tac[] >>
  `ghost_inv_at (DF H) lo d cenv cx es G' tn' t` by
    (drule_at (Pat `ghost_inv_at _ _ _ _ _ _ _ _ _`)
       (INST_TYPE [alpha |-> ``:256``] alloc_buffer_ghost_inv_at) >>
     disch_then irule >> simp[] >>
     conj_tac >- (qexists_tac `w2n w + 32` >> simp[]) >>
     conj_tac >- (qexists_tac `sa` >> simp[]) >>
     metis_tac[]) >>
  `!x. not_fresh_at sa x ==>
    lookup_var x ec = lookup_var x t /\ FLOOKUP Gentry x = FLOOKUP G' x /\
    op_taint tnentry (Var x) = op_taint tn' (Var x)` by
    (gen_tac >> disch_tac >>
     `x <> cv /\ x <> ev` by metis_tac[] >>
     qpat_assum `!x. not_fresh_at sa x ==> _`
       (qspec_then `x` strip_assume_tac) >>
     qpat_x_assum `!v. v <> cv /\ v <> ev ==> _`
       (qspec_then `x` mp_tac) >>
     simp[jump_to_def, update_var_def, lookup_var_def, FLOOKUP_UPDATE] >>
     gvs[lookup_var_def]) >>
  `ghost_inv_at (DF H) lo d cenv cx es Gentry tnentry ec` by
    (irule ghost_inv_at_exterior_frame >>
     qpat_assum `ghost_inv_at _ _ _ _ _ _ _ _ t` (irule_at Any) >>
     qexists_tac `sa` >> simp[] >>
     simp[jump_to_def, update_var_def]) >>
  `not_local_ptr cenv es.scopes cv /\ not_local_ptr cenv es.scopes ev` by
    (simp[not_local_ptr_def] >>
     fs[local_ptrs_reserved_def] >> metis_tac[]) >>
  `stmt_state_rel H ctx func cenv cx es t` by
    (qpat_x_assum `!H. stmt_state_rel _ _ _ _ _ _ _ ==> _` irule >> simp[]) >>
  `stmt_state_rel H ctx func cenv cx es ec` by
    (asm_rewrite_tac [stmt_state_rel_jump_to] >>
     irule stmt_state_rel_update_var >> simp[] >>
     irule stmt_state_rel_update_var >> simp[] >>
     simp[stmt_state_rel_jump_to]) >>
  `return_buf_frame d cenv sa ec` by
    (irule return_buf_frame_frame >>
     qpat_assum `return_buf_frame _ _ _ s0` (irule_at Any) >>
     simp[jump_to_def, update_var_def] >> metis_tac[]) >>
  `alloca_history func ec` by
    (gvs[allocaHistoryTheory.alloca_history_def, jump_to_def, update_var_def]) >>
  `ptr_covers Gentry tnentry q ec 32` by
    (gvs[ptr_covers_def, jump_to_def, lookup_var_def]) >>
  `!name b len. local_region cenv es.scopes ec name b len ==>
     regions_disjoint (w2n w) 32 b len` by
    (rpt strip_tac >>
     `local_region cenv es.scopes t name b len` suffices_by metis_tac[] >>
     qpat_x_assum `local_region _ _ ec _ _ _` mp_tac >>
     fs[local_region_def, local_ptrs_reserved_def] >> metis_tac[]) >>
  simp[] >> simp[jump_to_def, update_var_def, allocas_from_def, lookup_var_def,
                   FLOOKUP_UPDATE] >>
  conj_tac >- fs[allocas_from_def] >>
  conj_tac >- fs[lookup_var_def] >>
  conj_tac >- gvs[jump_to_def, update_var_def] >>
  qexists_tac `0` >> simp[]
QED
