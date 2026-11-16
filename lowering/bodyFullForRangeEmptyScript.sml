Theory bodyFullForRangeEmpty
Ancestors
  bodyFullForRangeInit bodyFullGhostFrame bodyMemoryDefs stmtSimForParts
  stmtSimProps fragGasEmitCtrl ptrDiscipline venomExecSemantics venomInst
  venomState exprLoweringProps loweringStateRelDefs loweringPosts
  bodyPtrDefs finite_map pred_set list integer_word vyperStorageFootprint
  bodyPtrBopInLiteralSuffix allocaHistory vyperStorageBackend

Theorem for_range_literal_empty_full:
  (!PG G tn j1 j2 cv ev dv cc a b bb lbl exit_lbl body_lbl ctx func lo explicit.
    let i = mk_inst j1 EQ [Var cv; Var ev] [dv];
        u = update_var dv (bool_to_word (a=b)) cc;
        Gf = step_prov PG G i u;
        tf = step_taint i cc u tn
    in
    bb = <|bb_label := lbl; bb_instructions :=
      [i; mk_inst j2 JNZ [Var dv; Label exit_lbl; Label body_lbl] []]|> /\
    lookup_block lbl func.fn_blocks = SOME bb /\
    cc.vs_current_bb = lbl /\ cc.vs_inst_idx = 0 /\ ~cc.vs_halted /\
    lookup_var cv cc = SOME a /\ lookup_var ev cc = SOME b /\
    FLOOKUP G cv = NONE /\ FLOOKUP G ev = NONE /\
    op_taint tn (Var cv) = {} /\ op_taint tn (Var ev) = {} /\
    ~ctx_has_dalloca ctx /\ allocas_from lo cc ==>
    !D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (cc,G,tn) []
      (OK (jump_to (if a=b then exit_lbl else body_lbl) u),Gf,tf)) /\
  lookup_block cond_lbl func.fn_blocks = SOME
    <|bb_label := cond_lbl; bb_instructions :=
      [mk_inst j1 EQ [Var cv; Var ev] [dv];
       mk_inst j2 JNZ [Var dv; Label exit_lbl; Label body_lbl] []]|> /\
  r.cs_current_bb = exit_lbl /\ r.cs_current_insts = [] /\
  sa.cs_next_var <= r.cs_next_var /\ ~block_is_terminated r /\
  local_ptrs_reserved cenv sa /\
  (!x. not_fresh_at sa x ==> x <> dv) /\
  (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  ~ctx_has_dalloca ctx ==>
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
      op_taint tn (Var x) = op_taint tn0 (Var x));
      Done = \H ee G tn s.
    stmt_lands lctx r (INL ()) s /\ ~s.vs_halted /\
    ~block_is_terminated r /\ cenv_top_ext cenv cenv ee.scopes /\
    stmt_state_rel H ctx func cenv cx ee s /\
    storage_well_formed_on cx ee (FST H) /\
    return_buf_frame d cenv r s /\ alloca_history func s /\
    s0.vs_alloca_next <= s.vs_alloca_next /\
    ghost_inv_at (DF H) lo d cenv cx ee G tn s /\
    (!x v. not_fresh_at sa x /\ lookup_var x s0 = SOME v ==>
      lookup_var x s = SOME v) /\
    (!aid bl. FLOOKUP s0.vs_allocas aid = SOME bl ==>
      FLOOKUP s.vs_allocas aid = SOME bl) /\
    (!x. not_fresh_at sa x ==>
      FLOOKUP G x = FLOOKUP G0 x /\
      op_taint tn (Var x) = op_taint tn0 (Var x))
  in !ee s G tn.
    ~s.vs_halted /\ storage_trace_domain cx st0 ee.storage_trace /\
    (!H. valid_horizon cx st0 H ee.storage_trace ==> Inv H [] ee G tn s) ==>
    ?u G1 tn1. !H. valid_horizon cx st0 H ee.storage_trace ==>
      gas_origin_ptr_path (DF H,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
        (s,G,tn) [] (OK u,G1,tn1) /\
      Done H (ee with gas_obs := []) G1 tn1 u
Proof
  strip_tac >> simp_tac bool_ss [LET_THM] >> rpt gen_tac >> strip_tac >>
  `?H0. valid_horizon cx st0 H0 ee.storage_trace` by
    metis_tac[storage_trace_domain_def] >>
  qpat_assum `!H. valid_horizon _ _ _ _ ==> _`
    (qspec_then `H0` mp_tac) >> simp[] >> strip_tac >>
  `k = Num (n2-n1)` by decide_tac >>
  `n1 + &k = n2` by
    (gvs[] >> intLib.ARITH_TAC) >>
  `lookup_var cv s = SOME (i2w n2)` by metis_tac[] >>
  qabbrev_tac `i = mk_inst j1 EQ [Var cv; Var ev] [dv]` >>
  qabbrev_tac `v = update_var dv 1w s` >>
  qabbrev_tac `u = jump_to exit_lbl v` >>
  qabbrev_tac `G1 = step_prov PG G i v` >>
  qabbrev_tac `tn1 = step_taint i s v tn` >>
  `!D. gas_origin_ptr_path (D,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
      (s,G,tn) [] (OK u,G1,tn1)` by
    (qpat_x_assum `!PG G tn j1 j2 cv ev dv cc a b bb lbl exit_lbl body_lbl ctx func lo explicit. _`
       (mp_tac o Q.INST [`cc` |-> `s`, `a` |-> `i2w n2 : bytes32`,
         `b` |-> `i2w n2 : bytes32`,
         `explicit` |-> `gas_explicit_sites ctx shadow_ctx`] o SPEC_ALL o SRULE [LET_THM]) >>
     simp[Abbr `i`,Abbr `v`,Abbr `u`,Abbr `G1`,Abbr `tn1`, bool_to_word_def]) >>
  qexistsl_tac [`u`,`G1`,`tn1`] >> gen_tac >> strip_tac >>
  qpat_x_assum `!H. valid_horizon _ _ _ _ ==> _`
    (qspec_then `H` mp_tac) >> simp[] >> strip_tac >>
  `tn1 = tn with t_var := tn.t_var |+ (dv,{})` by
    simp[Abbr `tn1`,Abbr `i`,Abbr `v`,membership_scalar_ghost_frame] >>
  `!x. x <> dv ==> FLOOKUP G1 x = FLOOKUP G x /\
        op_taint tn1 (Var x) = op_taint tn (Var x)` by
    (simp[Abbr `G1`,Abbr `i`,step_prov_def,out_prov_def,set_prov_def,
          mk_inst_def,FLOOKUP_DRESTRICT,op_taint_def,FLOOKUP_UPDATE] >>
     metis_tac[]) >>
  `!x. not_fresh_at sa x ==> lookup_var x u = lookup_var x s` by
    (rpt strip_tac >> `x <> dv` by metis_tac[] >>
     simp[Abbr `u`,Abbr `v`,lookup_var_def,jump_to_def,update_var_def,FLOOKUP_UPDATE]) >>
  `ghost_inv_at (DF H) lo d cenv cx (ee with gas_obs := []) G1 tn1 u` by
    (irule ghost_inv_at_exterior_frame >>
     qexistsl_tac [`G`,`ee`,`s`,`sa`,`tn`] >>
     simp[Abbr `u`,Abbr `v`,jump_to_def,update_var_def] >> metis_tac[]) >>
  `not_local_ptr cenv ee.scopes dv` by
    (gvs[not_local_ptr_def,local_ptrs_reserved_def] >> metis_tac[]) >>
  `stmt_state_rel H ctx func cenv cx ee u` by
    (simp[Abbr `u`,Abbr `v`,stmt_state_rel_jump_to] >>
     irule stmt_state_rel_update_var >> simp[]) >>
  `return_buf_frame d cenv r u` by
    (irule return_buf_frame_frame >> qexistsl_tac [`cenv`,`s`,`sa`] >>
     simp[Abbr `u`,Abbr `v`,jump_to_def,update_var_def] >> metis_tac[]) >>
  `alloca_history func u` by
    (irule alloca_history_jump >>
     simp[Abbr `u`,Abbr `v`,jump_to_def,update_var_def] >> metis_tac[]) >>
  simp[stmt_lands_def,cenv_top_ext_def,Abbr `u`,Abbr `v`,
       jump_to_def,update_var_def] >>
  qpat_x_assum `storage_well_formed_on _ _ _` mp_tac >>
  simp[storage_well_formed_on_def,oneline get_storage_def]
QED
