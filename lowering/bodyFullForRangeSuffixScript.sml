Theory bodyFullForRangeSuffix
Ancestors
  bodyFullShared bodyFullForRangeSlot bodyExprPreFacts bodyFullForRangeScalar
  forPtrCheckedScalar bodyFullGhostFrame venomState ptrDiscipline
  stmtSimProps loweringPosts vyperEvalPreservesScopes vyperStorageFootprint
  exprSimHypsDefs vyperTypeInvariants compileEnv vyperStorageBackend
  stmtSimDeclCompose venomInst instMemFrontier
  vyperInterpreter vyperState list finite_map pred_set

(* Source scope facts needed before projecting the selected body post to
   the exterior environment.  No target execution is selected here. *)
Theorem for_range_body_scopes:
  eval_stmts cx stmts
    (ee with <|scopes := (FEMPTY |+ (id,entry)) :: ee.scopes;
               gas_obs := gs|>) = (res,mid) /\
  lookup_scopes id ee.scopes = NONE ==>
  mid.scopes <> [] /\
  MAP FDOM (TL mid.scopes) = MAP FDOM ee.scopes /\
  (!n. n IN FDOM (HD mid.scopes) ==>
    lookup_scopes n (TL mid.scopes) = NONE)
Proof
  strip_tac >>
  drule eval_stmts_preserves_scopes_dom >>
  simp[preserves_scopes_dom_def] >> strip_tac >>
  rpt strip_tac >> Cases_on `n = id`
  >- (gvs[] >> Cases_on `mid.scopes` >> gvs[] >>
      drule eval_stmts_preserves_tail_lookup_none >> simp[])
  >> drule eval_stmts_new_in_head_not_in_tail >>
  simp[] >> metis_tac[]
QED

(* Cleanup retains the entire selected post, including the actual normal
   output environment bc_out.  Extension is composed before the projection. *)
Theorem for_range_body_post_pop:
  eval_stmts cx stmts
    (ee with <|scopes := (FEMPTY |+ (id,entry)) :: ee.scopes;
               gas_obs := gs|>) = (res,mid) /\
  lookup_scopes id ee.scopes = NONE /\
  cenv_top_ext cenv bc ((FEMPTY |+ (id,entry)) :: ee.scopes) /\
  (?cenv''.
    stmt_lands (InLoop exit_lbl incr_lbl) sb1 res t /\ ~t.vs_halted /\
    (res = INL () ==> ~block_is_terminated sb1 /\ cenv'' = bc_out) /\
    cenv_top_ext bc cenv'' mid.scopes /\
    stmt_state_rel H ctx func cenv'' cx mid t /\
    storage_well_formed_on cx mid (FST H) /\
    return_buf_frame d cenv'' sb1 t /\ alloca_history func t /\
    sstart.vs_alloca_next <= t.vs_alloca_next /\
    ghost_inv_at D lo d cenv'' cx mid G tn t /\
    (!x w. not_fresh_at sb0 x /\ lookup_var x sstart = SOME w ==>
      lookup_var x t = SOME w) /\
    (!aid b. FLOOKUP sstart.vs_allocas aid = SOME b ==>
      FLOOKUP t.vs_allocas aid = SOME b) /\
    (!x. not_fresh_at sb0 x ==>
      FLOOKUP G x = FLOOKUP Gstart x /\
      op_taint tn (Var x) = op_taint tnstart (Var x))) ==>
    stmt_lands (InLoop exit_lbl incr_lbl) sb1 res t /\ ~t.vs_halted /\
    (res = INL () ==> ~block_is_terminated sb1) /\
    cenv_top_ext cenv cenv (TL mid.scopes) /\
    stmt_state_rel H ctx func cenv cx (mid with scopes := TL mid.scopes) t /\
    storage_well_formed_on cx (mid with scopes := TL mid.scopes) (FST H) /\
    return_buf_frame d cenv sb1 t /\ alloca_history func t /\
    sstart.vs_alloca_next <= t.vs_alloca_next /\
    ghost_inv_at D lo d cenv cx (mid with scopes := TL mid.scopes) G tn t /\
    (!x w. not_fresh_at sb0 x /\ lookup_var x sstart = SOME w ==>
      lookup_var x t = SOME w) /\
    (!aid b. FLOOKUP sstart.vs_allocas aid = SOME b ==>
      FLOOKUP t.vs_allocas aid = SOME b) /\
    (!x. not_fresh_at sb0 x ==>
      FLOOKUP G x = FLOOKUP Gstart x /\
      op_taint tn (Var x) = op_taint tnstart (Var x))
Proof
  strip_tac >>
  drule_all for_range_body_scopes >> strip_tac >>
  `cenv_top_ext cenv cenv'' mid.scopes` by
    (irule cenv_top_ext_trans >> qexistsl_tac [`bc`,
      `(FEMPTY |+ (id,entry)) :: ee.scopes`] >> simp[]) >>
  `stmt_state_rel H ctx func cenv cx (mid with scopes := TL mid.scopes) t` by
    (irule stmt_state_rel_pop_top_ext >>
     Cases_on `mid.scopes` >> gvs[] >> metis_tac[]) >>
  `ghost_inv_at D lo d cenv cx (mid with scopes := TL mid.scopes) G tn t` by
    (irule ghost_inv_at_pop >>
     Cases_on `mid.scopes` >> gvs[] >> metis_tac[]) >>
  `cenv''.ce_return_buf = cenv.ce_return_buf` by
    fs[cenv_top_ext_def,compile_env_component_equality] >>
  simp[cenv_top_ext_refl] >> conj_tac
  >- fs[storage_well_formed_on_def,get_storage_scopes] >>
  qpat_x_assum `return_buf_frame _ _ _ _` mp_tac >>
  Cases_on `d` >> simp[return_buf_frame_def] >>
  rename1 `SOME dd` >> PairCases_on `dd` >> simp[return_buf_frame_def]
QED

(* Exterior ghost transport for the concrete increment's normalized updates.
   Freshness is at sa, not at the body boundary sb0. *)
Theorem for_range_increment_exterior_ghost[local]:
  ghost_inv_at D lo d cenv cx es G tn s /\
  local_ptrs_reserved cenv sa /\
  (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==>
    not_fresh_at sa x) /\
  (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==>
    not_fresh_at sa x) /\
  (!x. not_fresh_at sa x ==> x <> cv /\ x <> nv) ==>
  ghost_inv_at D lo d cenv cx es
    (DRESTRICT (DRESTRICT G (COMPL {nv})) (COMPL {cv}))
    (tn with t_var := (tn.t_var |+ (nv,{}) |+ (cv,{})))
    (jump_to cond_lbl (update_var cv w (update_var nv w s)))
Proof
  strip_tac >> irule ghost_inv_at_exterior_frame >>
  qexistsl_tac [`G`,`es`,`s`,`sa`,`tn`] >>
  simp[update_var_def,jump_to_def] >>
  rpt strip_tac >>
  `x <> cv /\ x <> nv` by metis_tac[] >>
  simp[lookup_var_def,FLOOKUP_UPDATE,FLOOKUP_DRESTRICT,op_taint_def]
QED

(* Complete selected successful round suffix.  Every semantic packet is
   explicit; the body output environment is independent of its input. *)
Theorem for_range_exit_post_layout_full:
  supported_program tops /\ get_module_code cx NONE = SOME tops /\
  supported_stmts tops bindings stmts /\
  id NOTIN FDOM env.var_types /\
  evaluate_type (get_tenv cx) typ = SOME tyv /\
  value_has_type tyv (IntV (n1 + &k)) /\
  type_stmts (extend_local env id typ F) ret_ty stmts = SOME env_b /\
  call_evaluation_safe cx (int_calls_stmts stmts) /\
  cenv.ce_alloca_locals /\ FLOOKUP cenv.ce_vars id = NONE /\
  local_ptrs_reserved cenv sa /\ ret_pc_ok cenv sa s0 /\
  (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==>
    not_fresh_at sa x) /\
  ~ctx_has_dalloca ctx /\
  q = STRING #"%" (toString sa.cs_next_var) /\
  not_fresh_at sb0 cv /\ not_fresh_at sb0 ev /\
  (!x. not_fresh_at sa x ==> x <> cv) /\
  q <> cv /\ cv <> ev /\
  declare_local cenv id typ sa =
    (bc,sa with cs_next_var := sa.cs_next_var + 1) /\
  sb0.cs_current_bb = body_lbl /\
  sb0.cs_current_insts =
    [mk_inst jstore MSTORE [Var q; Var cv] []] /\
  sa.cs_next_var < sb0.cs_next_var /\ cs_extends sa sb0 /\
  compile_stmts bc (InLoop exit_lbl incr_lbl) ret_ty stmts sb0 = ((),sb1) /\
  stmts_env bc (InLoop exit_lbl incr_lbl) ret_ty stmts sb0 = (bc_out,sb1) /\
  cs_extends sb0 sb1 /\ fn_has_code sb0 sb1 func /\
  (~block_is_terminated sb1 ==>
    sj.cs_blocks = sb1.cs_blocks /\ sj.cs_current_bb = sb1.cs_current_bb /\
    sj.cs_current_insts = sb1.cs_current_insts ++
      [mk_inst sb1.cs_next_id JMP [Label incr_lbl] []] /\
    fn_has_code sb1 sj func) /\
  sj.cs_next_var = sb1.cs_next_var /\
  nv = STRING #"%" (toString sj.cs_next_var) /\
  lookup_block incr_lbl func.fn_blocks = SOME
    <|bb_label := incr_lbl; bb_instructions :=
      [mk_inst sj.cs_next_id ADD [Var cv; Lit 1w] [nv];
       mk_inst (sj.cs_next_id + 1) ASSIGN [Var nv] [cv];
       mk_inst (sj.cs_next_id + 2) JMP [Label cond_lbl] []]|> /\
  r.cs_current_bb = exit_lbl /\ r.cs_current_insts = [] /\
  sa.cs_next_var <= r.cs_next_var /\
  k < Num (n2-n1) /\ n1 <= n2 /\ Num (n2-n1) < dimword (:256) /\
  rs = DROP (SUC k)
    (GENLIST (\j. Value (IntV (n1 + &j))) (Num (n2-n1))) /\
  (!H. valid_horizon cx st0 H ee.storage_trace ==>
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
    lookup_var cv s = SOME (i2w (n1 + &k)) /\
    (!x v. not_fresh_at sa x /\ lookup_var x s0 = SOME v ==>
      lookup_var x s = SOME v) /\
    (!aid bl. FLOOKUP s0.vs_allocas aid = SOME bl ==>
      FLOOKUP s.vs_allocas aid = SOME bl) /\
    (!x. not_fresh_at sa x ==> FLOOKUP G x = FLOOKUP G0 x /\
      op_taint tn (Var x) = op_taint tn0 (Var x))) /\
  storage_trace_domain cx st0 ee.storage_trace /\
  (!H. valid_horizon cx st0 H ee.storage_trace ==>
    gas_origin_ptr_path (DF H,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
      (s,G,tn) [] (OK sstart,Gstart,tnstart) /\
    expr_sim_inv bc cx (extend_local env id typ F)
      (ee with <|scopes := (FEMPTY |+ (id,
        <|assignable := F; type := tyv; value := IntV (n1 + &k);
          popped := []|>)) :: ee.scopes; gas_obs := []|>) /\
    stmt_state_rel H ctx func bc cx
      (ee with <|scopes := (FEMPTY |+ (id,
        <|assignable := F; type := tyv; value := IntV (n1 + &k);
          popped := []|>)) :: ee.scopes; gas_obs := []|>) sstart /\
    storage_well_formed_on cx ee (FST H) /\
    return_buf_frame d bc sb0 sstart /\ alloca_history func sstart /\
    ghost_inv_at (DF H) lo d bc cx
      (ee with <|scopes := (FEMPTY |+ (id,
        <|assignable := F; type := tyv; value := IntV (n1 + &k);
          popped := []|>)) :: ee.scopes; gas_obs := []|>) Gstart tnstart sstart /\
    ~sstart.vs_halted /\ sstart.vs_current_bb = sb0.cs_current_bb /\
    sstart.vs_inst_idx = LENGTH sb0.cs_current_insts /\
    ret_pc_ok bc sb0 sstart /\ allocas_from lo sstart /\
    lookup_var q sstart = SOME w /\ ptr_covers Gstart tnstart q sstart 32 /\
    FLOOKUP sstart.vs_allocas sa.cs_next_id = SOME (w2n w,32) /\
    w2n w + 32 < dimword (:256) /\ w2n w + 32 <= sstart.vs_alloca_next /\
    (!name b len. local_region cenv ee.scopes sstart name b len ==>
      regions_disjoint (w2n w) 32 b len) /\
    FLOOKUP Gstart cv = NONE /\ FLOOKUP Gstart ev = NONE /\
    op_taint tnstart (Var cv) = {} /\ op_taint tnstart (Var ev) = {} /\
    lookup_var ev sstart = SOME (i2w n2) /\
    lookup_var cv sstart = SOME (i2w (n1 + &k)) /\
    s0.vs_alloca_next <= sstart.vs_alloca_next /\
    (!x v. not_fresh_at sa x /\ lookup_var x s0 = SOME v ==>
      lookup_var x sstart = SOME v) /\
    (!aid bl. FLOOKUP s0.vs_allocas aid = SOME bl ==>
      FLOOKUP sstart.vs_allocas aid = SOME bl) /\
    (!x. not_fresh_at sa x ==> FLOOKUP Gstart x = FLOOKUP G0 x /\
      op_taint tnstart (Var x) = op_taint tn0 (Var x))) /\
  eval_stmts cx stmts
    (ee with <|scopes := (FEMPTY |+ (id,
      <|assignable := F; type := tyv; value := IntV (n1 + &k);
        popped := []|>)) :: ee.scopes; gas_obs := gs|>) = (res,mid) /\
  mid.gas_obs = [] /\ storage_trace_domain cx st0 mid.storage_trace /\
  (!H. valid_horizon cx st0 H mid.storage_trace ==>
    ?cenv''.
      stmt_lands (InLoop exit_lbl incr_lbl) sb1 res t /\ ~t.vs_halted /\
      (res = INL () ==> ~block_is_terminated sb1 /\ cenv'' = bc_out) /\
      cenv_top_ext bc cenv'' mid.scopes /\
      stmt_state_rel H ctx func cenv'' cx mid t /\
      storage_well_formed_on cx mid (FST H) /\
      return_buf_frame d cenv'' sb1 t /\ alloca_history func t /\
      sstart.vs_alloca_next <= t.vs_alloca_next /\
      ghost_inv_at (DF H) lo d cenv'' cx mid G1 tn1 t /\
      (!x v. not_fresh_at sb0 x /\ lookup_var x sstart = SOME v ==>
        lookup_var x t = SOME v) /\
      (!aid bl. FLOOKUP sstart.vs_allocas aid = SOME bl ==>
        FLOOKUP t.vs_allocas aid = SOME bl) /\
      (!x. not_fresh_at sb0 x ==> FLOOKUP G1 x = FLOOKUP Gstart x /\
        op_taint tn1 (Var x) = op_taint tnstart (Var x))) ==>
  (res = INL () \/ res = INR BreakException \/ res = INR ContinueException) /\
  ?u G2 tn2. !H. valid_horizon cx st0 H mid.storage_trace ==>
    gas_origin_ptr_path (DF H,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
      (t,G1,tn1) [] (OK u,G2,tn2) /\
    (mid with scopes := TL mid.scopes).gas_obs = [] /\ ~u.vs_halted /\
    (res = INR BreakException ==>
      stmt_lands lctx r (INL ()) u /\ ~block_is_terminated r /\
      cenv_top_ext cenv cenv (TL mid.scopes) /\
      stmt_state_rel H ctx func cenv cx (mid with scopes := TL mid.scopes) u /\
      storage_well_formed_on cx (mid with scopes := TL mid.scopes) (FST H) /\
      return_buf_frame d cenv r u /\ alloca_history func u /\
      s0.vs_alloca_next <= u.vs_alloca_next /\
      ghost_inv_at (DF H) lo d cenv cx (mid with scopes := TL mid.scopes) G2 tn2 u /\
      (!x v. not_fresh_at sa x /\ lookup_var x s0 = SOME v ==>
        lookup_var x u = SOME v) /\
      (!aid bl. FLOOKUP s0.vs_allocas aid = SOME bl ==>
        FLOOKUP u.vs_allocas aid = SOME bl) /\
      (!x. not_fresh_at sa x ==> FLOOKUP G2 x = FLOOKUP G0 x /\
        op_taint tn2 (Var x) = op_taint tn0 (Var x))) /\
    (res <> INR BreakException ==>
      expr_sim_inv cenv cx env (mid with scopes := TL mid.scopes) /\
      stmt_state_rel H ctx func cenv cx (mid with scopes := TL mid.scopes) u /\
      storage_well_formed_on cx (mid with scopes := TL mid.scopes) (FST H) /\
      return_buf_frame d cenv sa u /\ alloca_history func u /\
      s0.vs_alloca_next <= u.vs_alloca_next /\ allocas_from lo u /\
      ghost_inv_at (DF H) lo d cenv cx (mid with scopes := TL mid.scopes) G2 tn2 u /\
      u.vs_current_bb = cond_lbl /\ u.vs_inst_idx = 0 /\
      lookup_var q u = SOME w /\ ptr_covers G2 tn2 q u 32 /\
      FLOOKUP u.vs_allocas sa.cs_next_id = SOME (w2n w,32) /\
      w2n w + 32 < dimword (:256) /\ w2n w + 32 <= u.vs_alloca_next /\
      (!name b len. local_region cenv (TL mid.scopes) u name b len ==>
        regions_disjoint (w2n w) 32 b len) /\
      FLOOKUP G2 cv = NONE /\ FLOOKUP G2 ev = NONE /\
      op_taint tn2 (Var cv) = {} /\ op_taint tn2 (Var ev) = {} /\
      lookup_var ev u = SOME (i2w n2) /\
      (?kk. kk <= Num (n2-n1) /\
        rs = DROP kk (GENLIST (\j. Value (IntV (n1 + &j))) (Num (n2-n1))) /\
        lookup_var cv u = SOME (i2w (n1 + &kk)) /\
        n1 + &kk <= n2 /\ Num (n2-n1) < dimword (:256)) /\
      (!x v. not_fresh_at sa x /\ lookup_var x s0 = SOME v ==>
        lookup_var x u = SOME v) /\
      (!aid bl. FLOOKUP s0.vs_allocas aid = SOME bl ==>
        FLOOKUP u.vs_allocas aid = SOME bl) /\
      (!x. not_fresh_at sa x ==> FLOOKUP G2 x = FLOOKUP G0 x /\
        op_taint tn2 (Var x) = op_taint tn0 (Var x)))
Proof
  strip_tac >>
  `?H0. valid_horizon cx st0 H0 mid.storage_trace` by
    metis_tac[storage_trace_domain_def] >>
  conj_tac
  >- (qpat_x_assum `!H. valid_horizon _ _ H mid.storage_trace ==> _` drule >>
      strip_tac >> qpat_x_assum `stmt_lands _ _ res _` mp_tac >>
      simp_tac std_ss [stmt_lands_def] >> metis_tac[]) >>
  `?Hs. valid_horizon cx st0 Hs ee.storage_trace` by
    metis_tac[storage_trace_domain_def] >>
  qpat_assum `!H. valid_horizon _ _ H ee.storage_trace ==> expr_sim_inv _ _ _ _ /\ _`
    drule >> disch_then strip_assume_tac >>
  `lookup_scopes id ee.scopes = NONE` by
    (qpat_x_assum `expr_sim_inv cenv _ _ _` mp_tac >>
     simp[expr_sim_inv_def,env_consistent_def,env_scopes_consistent_def] >>
     strip_tac >> Cases_on `lookup_scopes id ee.scopes` >> simp[] >>
     qpat_x_assum `!id entry. lookup_scopes _ _ = SOME _ ==> _` drule >>
     simp[FLOOKUP_DEF]) >>
  drule_all for_range_body_scopes >> strip_tac >>
  `cenv_top_ext cenv bc ((FEMPTY |+ (id,
      <|assignable := F; type := tyv; value := IntV (n1 + &k);
        popped := []|>)) :: ee.scopes)` by
    (irule cenv_top_ext_declare_local >>
     simp[] >> qexistsl_tac [`id`,`sa`,
       `sa with cs_next_var := sa.cs_next_var + 1`,`typ`] >> simp[]) >>
  `!H. valid_horizon cx st0 H mid.storage_trace ==>
    stmt_state_rel H ctx func cenv cx (mid with scopes := TL mid.scopes) t /\
    ghost_inv_at (DF H) lo d cenv cx (mid with scopes := TL mid.scopes) G1 tn1 t` by
    (rpt gen_tac >> disch_tac >>
     qpat_assum `!H. valid_horizon _ _ H mid.storage_trace ==> _` drule >>
     disch_then (mp_then Any mp_tac for_range_body_post_pop) >>
     disch_then drule >>
     disch_then (qspec_then `cenv` mp_tac) >> simp[]) >>
  `!x. not_fresh_at sa x ==> not_fresh_at sb0 x` by
    (simp[loweringStateRelDefsTheory.not_fresh_at_def] >> metis_tac[DECIDE ``!n a. a + 4 <= n ==> a <= n``]) >>
  Cases_on `res = INR BreakException`
  >- (qexistsl_tac [`t`,`G1`,`tn1`] >> rpt gen_tac >> disch_tac >>
      qpat_assum `!H. valid_horizon _ _ H mid.storage_trace ==> ?cenv''. _` drule >>
      disch_then (mp_then Any mp_tac for_range_body_post_pop) >>
      disch_then drule >> disch_then (qspec_then `cenv` mp_tac) >>
      simp[] >> strip_tac >>
      qpat_assum `!H. valid_horizon _ _ H ee.storage_trace ==> gas_origin_ptr_path _ _ _ _ /\ _` drule >>
      disch_then strip_assume_tac >>
      `return_buf_frame d cenv r t` by
        (Cases_on `d` >- fs[return_buf_frame_def] >>
         rename1 `return_buf_frame (SOME dd) cenv sa s` >> PairCases_on `dd` >>
         gvs[return_buf_frame_def] >>
         qpat_x_assum `not_fresh_at sa _` mp_tac >>
         simp[loweringStateRelDefsTheory.not_fresh_at_def] >>
         metis_tac[arithmeticTheory.LESS_EQ_TRANS]) >>
      fs[stmt_lands_def,block_is_terminated_def] >>
      metis_tac[fragGasOriginPtrTheory.gas_origin_ptr_path_rules]) >>
  `res <> INL () ==> res = INR ContinueException` by
    (qpat_assum `!H. valid_horizon _ _ H mid.storage_trace ==> ?cenv''. _` drule >>
     strip_tac >> fs[stmt_lands_def] >> metis_tac[]) >>
  `expr_sim_inv cenv cx env (mid with scopes := TL mid.scopes)` by
    (mp_tac expr_sim_inv_for_pop >>
     disch_then (qspecl_then [`cenv`,`cx`,`env`,`ee with gas_obs := gs`,
       `id`,`typ`,`tyv`,`IntV (n1 + &k)`,`ret_ty`,`stmts`,`env_b`,
       `res`,`mid`,`HD mid.scopes`,`TL mid.scopes`,`tops`,`bindings`] mp_tac) >>
     simp[expr_sim_inv_gas_obs] >>
     impl_tac >- (Cases_on `mid.scopes` >> gvs[] >> metis_tac[]) >> simp[]) >>
  qpat_assum `!H. valid_horizon _ _ H mid.storage_trace ==> ?cenv''. _` drule >>
  disch_then (mp_then Any mp_tac for_range_body_post_pop) >>
  disch_then drule >> disch_then (qspec_then `cenv` mp_tac) >>
  simp[] >> strip_tac >>
  qpat_assum `!H. valid_horizon _ _ H ee.storage_trace ==> gas_origin_ptr_path _ _ _ _ /\ _` drule >>
  disch_then strip_assume_tac >>
  `not_fresh_at sb0 cv /\ not_fresh_at sb0 ev` by
    simp[loweringStateRelDefsTheory.not_fresh_at_def] >>
  `lookup_var cv t = SOME (i2w (n1 + &k)) /\
   lookup_var ev t = SOME (i2w n2) /\
   FLOOKUP G1 cv = NONE /\ FLOOKUP G1 ev = NONE /\
   op_taint tn1 (Var cv) = {} /\ op_taint tn1 (Var ev) = {}` by metis_tac[] >>
  `allocas_from lo t` by
    (qpat_assum `!H. valid_horizon _ _ H mid.storage_trace ==> stmt_state_rel _ _ _ _ _ _ _ /\ _` drule >>
     disch_then strip_assume_tac >> fs[bodyPtrDefsTheory.ghost_inv_at_def]) >>
  qabbrev_tac `dd = if res = INL () then jump_to incr_lbl t else t` >>
  `!H. gas_origin_ptr_path (DF H,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
      (t,G1,tn1) [] (OK dd,G1,tn1)` by
    (gen_tac >> Cases_on `res = INL ()`
     >- (fs[stmt_lands_def] >>
         `?bb. lookup_block sb1.cs_current_bb func.fn_blocks = SOME bb /\
           get_instruction bb (LENGTH sb1.cs_current_insts) =
             SOME (mk_inst sb1.cs_next_id JMP [Label incr_lbl] [])` by
           (drule_at (Pat `fn_has_code _ _ _`) fragExecTheory.fn_has_code_same_block >>
            disch_then (qspec_then `[mk_inst sb1.cs_next_id JMP [Label incr_lbl] []]` mp_tac) >>
            simp[] >> metis_tac[DECIDE ``0 < 1``]) >>
         simp[Abbr `dd`] >> irule fragGasOriginPtrLoopTheory.jmp_origin_ptr_path >>
         metis_tac[]) >>
     `res = INR ContinueException` by metis_tac[] >>
     fs[stmt_lands_def,Abbr `dd`] >>
     metis_tac[fragGasOriginPtrTheory.gas_origin_ptr_path_rules]) >>
  `dd.vs_current_bb = incr_lbl /\ dd.vs_inst_idx = 0 /\
   ~dd.vs_halted /\ allocas_from lo dd /\
   lookup_var cv dd = SOME (i2w (n1 + &k))` by
    (Cases_on `res = INL ()` >>
     gvs[Abbr `dd`,jump_to_def,stmt_lands_def,lookup_var_def,allocas_from_def] >>
     metis_tac[]) >>
  qabbrev_tac `u = jump_to cond_lbl (update_var cv (i2w (n1 + &k)+1w)
        (update_var nv (i2w (n1 + &k)+1w) dd))` >>
  qabbrev_tac `Gf = DRESTRICT (DRESTRICT G1 (COMPL {nv})) (COMPL {cv})` >>
  qabbrev_tac `tf = tn1 with t_var := tn1.t_var |+ (nv,{}) |+ (cv,{})` >>
  `!D. inst_seq_ptr D lo ctx func PG G1 tn1
    [mk_inst sj.cs_next_id ADD [Var cv; Lit 1w] [nv];
     mk_inst (sj.cs_next_id+1) ASSIGN [Var nv] [cv]] dd Gf tf` by
    (drule_all for_range_increment_sequence_full >>
     disch_then (qspecl_then [`nv`,`sj.cs_next_id+1`,`sj.cs_next_id`,`func`,`PG`] mp_tac) >>
     qpat_x_assum `nv = _` kall_tac >>
     qpat_x_assum `sj.cs_next_var = _` kall_tac >>
     simp[Abbr `Gf`,Abbr `tf`,step_prov_def,out_prov_def,set_prov_def,
       first_prov_def,step_taint_def,out_taint_def,set_var_taint_def,
       mk_inst_def,op_prov_def,op_taint_def,eval_operand_def,
       lookup_var_def,update_var_def,FLOOKUP_UPDATE,FLOOKUP_DRESTRICT,
       new_site_bytes_def,mem_taint_def,step_writes_def,
       codegenRelTheory.source_memory_write_ranges_def,store_taint_def,written_taint_def,
       adopt_reset_def,imm_taint_def,range_bytes_def,FLOOKUP_DEF] >>
     simp[SF CONJ_ss] >>
     `!tv. <|t_mem := tn1.t_mem; t_var := tv; t_stor := tn1.t_stor;
             t_trans := tn1.t_trans; t_imm := tn1.t_imm|> =
           (tn1 with t_var := tv)` by
       simp[ptrDisciplineTheory.taint_component_equality] >>
     simp[]) >>
  `!H. valid_horizon cx st0 H mid.storage_trace ==>
    gas_origin_ptr_path (DF H,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
      (dd,G1,tn1) [] (OK u,Gf,tf)` by
    (qunabbrev_tac `u` >>
     match_mp_tac (for_range_incr_path_full_valid |> Q.INST
       [`code` |-> `[mk_inst sj.cs_next_id ADD [Var cv; Lit 1w] [nv];
                      mk_inst (sj.cs_next_id+1) ASSIGN [Var nv] [cv]]`,
        `bb` |-> `<|bb_label := incr_lbl; bb_instructions :=
          [mk_inst sj.cs_next_id ADD [Var cv; Lit 1w] [nv];
           mk_inst (sj.cs_next_id+1) ASSIGN [Var nv] [cv];
           mk_inst (sj.cs_next_id+2) JMP [Label cond_lbl] []]|>`,
        `lbl` |-> `incr_lbl`, `i1` |-> `sj.cs_next_id`,
        `i2` |-> `sj.cs_next_id+1`, `i3` |-> `sj.cs_next_id+2`]) >>
     simp[]) >>
  `sb0.cs_next_var <= sb1.cs_next_var` by
    (mp_tac (CONJUNCT2 stmtLoweringMonoTheory.compile_stmt_ci_mono) >>
     disch_then (qspecl_then [`bc`,`InLoop exit_lbl incr_lbl`,`ret_ty`,`stmts`,`sb0`] mp_tac) >>
     simp[exprLoweringPropsTheory.ci_mono_def]) >>
  `sa.cs_next_var <= sj.cs_next_var` by decide_tac >>
  `!x. not_fresh_at sa x ==> x <> cv /\ x <> nv` by
    (gen_tac >> disch_tac >> conj_tac >- metis_tac[] >>
     qpat_x_assum `not_fresh_at sa x` mp_tac >>
     simp[loweringStateRelDefsTheory.not_fresh_at_def]) >>
  qexistsl_tac [`u`,`Gf`,`tf`] >> gen_tac >> disch_tac >>
  qpat_assum `!H. valid_horizon _ _ H mid.storage_trace ==> ?cenv''. _` drule >>
  disch_then (mp_then Any mp_tac for_range_body_post_pop) >>
  disch_then drule >> disch_then (qspec_then `cenv` mp_tac) >>
  simp[] >> strip_tac >>
  `gas_origin_ptr_path (DF H,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
      (t,G1,tn1) [] (OK u,Gf,tf)` by
    metis_tac[fragGasOriginPtrLoopTheory.gas_origin_ptr_path_trans] >>
  `~not_fresh_at sa cv` by metis_tac[] >>
  `stmt_state_rel H ctx func cenv cx (mid with scopes := TL mid.scopes) u` by
    (simp[Abbr `u`,exprLoweringPropsTheory.stmt_state_rel_jump_to] >>
     irule exprLoweringPropsTheory.stmt_state_rel_update_var >>
     reverse conj_tac
     >- (irule exprLoweringPropsTheory.stmt_state_rel_update_var >>
         Cases_on `res = INL ()` >>
         simp[Abbr `dd`,exprLoweringPropsTheory.stmt_state_rel_jump_to] >>
         irule exprSimOperandsTheory.fresh_not_local_ptr >>
         qexists_tac `sa` >> simp[loweringStateRelDefsTheory.not_fresh_at_def]) >>
     irule exprSimOperandsTheory.fresh_not_local_ptr >>
     qexists_tac `sa` >> simp[loweringStateRelDefsTheory.not_fresh_at_def]) >>
  `!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x` by
    fs[ret_pc_ok_def] >>
  `ghost_inv_at (DF H) lo d cenv cx (mid with scopes := TL mid.scopes) Gf tf u` by
    (map_every qunabbrev_tac [`u`,`Gf`,`tf`] >>
     irule for_range_increment_exterior_ghost >>
     simp[] >> reverse conj_tac
     >- (Cases_on `res = INL ()` >> simp[Abbr `dd`,ghost_inv_at_jump]) >>
     qexists_tac `sa` >> simp[] >>
     rpt strip_tac >> qpat_x_assum `not_fresh_at sa x` mp_tac >>
     simp[loweringStateRelDefsTheory.not_fresh_at_def]) >>
  `!x v. not_fresh_at sa x /\ lookup_var x s0 = SOME v ==> lookup_var x u = SOME v` by
    (rpt strip_tac >>
     `x <> cv /\ x <> nv` by metis_tac[] >>
     `lookup_var x sstart = SOME v` by metis_tac[] >>
     `lookup_var x t = SOME v` by metis_tac[] >>
     Cases_on `res = INL ()` >>
     fs[Abbr `u`,Abbr `dd`,lookup_var_def,update_var_def,jump_to_def,FLOOKUP_UPDATE] >>
     qpat_x_assum `x <> cv` mp_tac >> qpat_x_assum `x <> nv` mp_tac >> simp[] >>
     metis_tac[]) >>
  `!aid bl. FLOOKUP s0.vs_allocas aid = SOME bl ==> FLOOKUP u.vs_allocas aid = SOME bl` by
    (rpt strip_tac >>
     `FLOOKUP sstart.vs_allocas aid = SOME bl` by metis_tac[] >>
     `FLOOKUP t.vs_allocas aid = SOME bl` by metis_tac[] >>
     Cases_on `res = INL ()` >> simp[Abbr `u`,Abbr `dd`,update_var_def,jump_to_def]) >>
  `!x. not_fresh_at sa x ==> FLOOKUP Gf x = FLOOKUP G0 x /\
      op_taint tf (Var x) = op_taint tn0 (Var x)` by
    (rpt strip_tac >>
     `x <> cv /\ x <> nv` by metis_tac[] >>
     `FLOOKUP G1 x = FLOOKUP G0 x /\ op_taint tn1 (Var x) = op_taint tn0 (Var x)` by metis_tac[] >>
     fs[Abbr `Gf`,Abbr `tf`,FLOOKUP_DRESTRICT,op_taint_def,FLOOKUP_UPDATE] >>
     qpat_x_assum `x <> cv` mp_tac >> qpat_x_assum `x <> nv` mp_tac >> simp[] >> metis_tac[]) >>
  `u.vs_alloca_next = t.vs_alloca_next /\ u.vs_allocas = t.vs_allocas /\
    ~u.vs_halted /\ u.vs_current_bb = cond_lbl /\ u.vs_inst_idx = 0` by
    (Cases_on `res = INL ()` >> fs[Abbr `u`,Abbr `dd`,update_var_def,jump_to_def]) >>
  `s0.vs_alloca_next <= u.vs_alloca_next /\ w2n w + 32 <= u.vs_alloca_next` by decide_tac >>
  `return_buf_frame d cenv sa u` by
    (Cases_on `d` >- fs[return_buf_frame_def] >>
     rename1 `return_buf_frame (SOME bwcap) cenv sa u` >>
     PairCases_on `bwcap` >>
     qpat_x_assum `return_buf_frame _ cenv sb1 t` mp_tac >>
     simp[return_buf_frame_def] >> strip_tac >>
     rename1 `cenv.ce_return_buf = SOME (PtrVar (Var rx) sz)` >>
     `not_fresh_at sa rx` by metis_tac[] >>
     `rx <> cv /\ rx <> nv` by metis_tac[] >>
     `lookup_var rx u = lookup_var rx t` by
       (map_every qunabbrev_tac [`u`,`dd`] >>
        qpat_x_assum `rx <> cv` mp_tac >> qpat_x_assum `rx <> nv` mp_tac >>
        simp[NoAsms,lookup_var_def,update_var_def,jump_to_def,FLOOKUP_UPDATE] >>
        rpt strip_tac >> IF_CASES_TAC >> simp[lookup_var_def]) >>
     qexistsl_tac [`rx`,`sz`] >> simp[]) >>
  `alloca_history func u` by fs[allocaHistoryTheory.alloca_history_def] >>
  `allocas_from lo u` by (fs[allocas_from_def] >> metis_tac[]) >>
  `not_fresh_at sb0 q /\ q <> cv /\ q <> nv /\ ev <> cv /\ ev <> nv` by
    (fs[loweringStateRelDefsTheory.not_fresh_at_def] >>
     simp[] >> decide_tac) >>
  `lookup_var q t = SOME w /\ FLOOKUP G1 q = FLOOKUP Gstart q /\
    op_taint tn1 (Var q) = op_taint tnstart (Var q)` by metis_tac[] >>
  `lookup_var q u = lookup_var q t /\ lookup_var ev u = lookup_var ev t` by
    (map_every qunabbrev_tac [`u`,`dd`] >>
     qpat_x_assum `q <> cv` mp_tac >> qpat_x_assum `q <> nv` mp_tac >>
     qpat_x_assum `ev <> cv` mp_tac >> qpat_x_assum `ev <> nv` mp_tac >>
     simp[NoAsms,lookup_var_def,update_var_def,jump_to_def,FLOOKUP_UPDATE] >>
     rpt strip_tac >> IF_CASES_TAC >> simp[lookup_var_def]) >>
  `FLOOKUP Gf q = FLOOKUP Gstart q /\
    op_taint tf (Var q) = op_taint tnstart (Var q) /\
    FLOOKUP Gf cv = NONE /\ FLOOKUP Gf ev = NONE /\
    op_taint tf (Var cv) = {} /\ op_taint tf (Var ev) = {}` by
    (fs[Abbr `Gf`,Abbr `tf`,FLOOKUP_DRESTRICT,op_taint_def,FLOOKUP_UPDATE] >>
     metis_tac[]) >>
  `ptr_covers Gf tf q u 32` by
    (qpat_x_assum `ptr_covers Gstart tnstart q sstart 32` mp_tac >>
     simp[bodyPtrDefsTheory.ptr_covers_def] >> metis_tac[]) >>
  `stmt_state_rel Hs ctx func cenv cx (ee with gas_obs := []) sstart` by
    (qpat_assum `stmt_state_rel Hs ctx func bc _ _ sstart`
       (mp_then Any mp_tac stmt_state_rel_pop_top_ext) >>
     disch_then (qspec_then `cenv` mp_tac) >>
     simp[] >>
     `ee with <| scopes := ee.scopes; gas_obs := [] |> = ee with gas_obs := []` by
       (Cases_on `ee` >> simp[vyperStateTheory.evaluation_state_fn_updates]) >>
     simp[]) >>
  `!x v. not_fresh_at sa x /\ lookup_var x sstart = SOME v ==>
      lookup_var x u = SOME v` by
    (rpt strip_tac >>
     `x <> cv /\ x <> nv` by metis_tac[] >>
     `lookup_var x t = SOME v` by metis_tac[] >>
     `lookup_var x u = lookup_var x t` by
       (map_every qunabbrev_tac [`u`,`dd`] >>
        qpat_x_assum `x <> cv` mp_tac >> qpat_x_assum `x <> nv` mp_tac >>
        simp[NoAsms,lookup_var_def,update_var_def,jump_to_def,FLOOKUP_UPDATE] >>
        rpt strip_tac >> IF_CASES_TAC >> simp[lookup_var_def]) >>
     metis_tac[]) >>
  `local_ptrs_rel func cenv ee.scopes sstart` by
    fs[exprSimWordArgsTheory.stmt_state_rel_gas_obs,
       exprLoweringPropsTheory.stmt_state_rel_def,loweringStateRelDefsTheory.state_rel_def] >>
  `!name b len. local_region cenv (TL mid.scopes) u name b len ==>
      regions_disjoint (w2n w) 32 b len` by
    (rpt strip_tac >>
     `local_region cenv ee.scopes sstart name b len` by
       (irule exprSimPropsTheory.local_region_frame >>
        conj_tac >- metis_tac[] >>
        qexistsl_tac [`sa`,`TL mid.scopes`,`u`] >> simp[]) >>
     metis_tac[]) >>
  qpat_x_assum `q = _` (assume_tac o SYM) >>
  simp[] >> conj_tac >- metis_tac[] >>
  qexists_tac `SUC k` >> simp[] >>
  reverse conj_tac
  >- (qpat_x_assum `k < Num (n2 - n1)` mp_tac >>
      qpat_x_assum `n1 <= n2` mp_tac >>
      POP_ASSUM_LIST (K ALL_TAC) >> rpt strip_tac >>
      `0 <= n2 - n1` by intLib.COOPER_TAC >>
      `&(Num (n2 - n1)) = n2 - n1` by simp[integerTheory.INT_OF_NUM] >>
      `&k < &(Num (n2 - n1))` by simp[] >>
      fs[integerTheory.INT] >> intLib.COOPER_TAC) >>
  simp[Abbr `u`,lookup_var_def,update_var_def,jump_to_def,FLOOKUP_UPDATE,
       stmtSimForPartsTheory.i2w_counter_suc,arithmeticTheory.ADD1]
QED

Theorem for_range_literal_exit_post_full:
  supported_program tops /\ get_module_code cx NONE = SOME tops /\
  supported_stmts tops bindings stmts /\
  id NOTIN FDOM env.var_types /\
  evaluate_type (get_tenv cx) typ = SOME tyv /\
  value_has_type tyv (IntV (n1 + &k)) /\
  type_stmts (extend_local env id typ F) ret_ty stmts = SOME env_b /\
  call_evaluation_safe cx (int_calls_stmts stmts) /\
  cenv.ce_alloca_locals /\ FLOOKUP cenv.ce_vars id = NONE /\
  local_ptrs_reserved cenv sa /\ ret_pc_ok cenv sa s0 /\
  (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==>
    not_fresh_at sa x) /\
  ~ctx_has_dalloca ctx /\
  q = STRING #"%" (toString sa.cs_next_var) /\
  cv = STRING #"%" (toString (sa.cs_next_var + 1)) /\
  ev = STRING #"%" (toString (sa.cs_next_var + 2)) /\
  declare_local cenv id typ sa =
    (bc,sa with cs_next_var := sa.cs_next_var + 1) /\
  sb0.cs_current_bb = body_lbl /\
  sb0.cs_current_insts =
    [mk_inst (sa.cs_next_id + 7) MSTORE [Var q; Var cv] []] /\
  sb0.cs_next_var = sa.cs_next_var + 4 /\ cs_extends sa sb0 /\
  compile_stmts bc (InLoop exit_lbl incr_lbl) ret_ty stmts sb0 = ((),sb1) /\
  stmts_env bc (InLoop exit_lbl incr_lbl) ret_ty stmts sb0 = (bc_out,sb1) /\
  cs_extends sb0 sb1 /\ fn_has_code sb0 sb1 func /\
  (~block_is_terminated sb1 ==>
    sj.cs_blocks = sb1.cs_blocks /\ sj.cs_current_bb = sb1.cs_current_bb /\
    sj.cs_current_insts = sb1.cs_current_insts ++
      [mk_inst sb1.cs_next_id JMP [Label incr_lbl] []] /\
    fn_has_code sb1 sj func) /\
  sj.cs_next_var = sb1.cs_next_var /\
  nv = STRING #"%" (toString sj.cs_next_var) /\
  lookup_block incr_lbl func.fn_blocks = SOME
    <|bb_label := incr_lbl; bb_instructions :=
      [mk_inst sj.cs_next_id ADD [Var cv; Lit 1w] [nv];
       mk_inst (sj.cs_next_id + 1) ASSIGN [Var nv] [cv];
       mk_inst (sj.cs_next_id + 2) JMP [Label cond_lbl] []]|> /\
  r.cs_current_bb = exit_lbl /\ r.cs_current_insts = [] /\
  sa.cs_next_var <= r.cs_next_var /\
  k < Num (n2-n1) /\ n1 <= n2 /\ Num (n2-n1) < dimword (:256) /\
  rs = DROP (SUC k)
    (GENLIST (\j. Value (IntV (n1 + &j))) (Num (n2-n1))) /\
  (!H. valid_horizon cx st0 H ee.storage_trace ==>
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
    lookup_var cv s = SOME (i2w (n1 + &k)) /\
    (!x v. not_fresh_at sa x /\ lookup_var x s0 = SOME v ==>
      lookup_var x s = SOME v) /\
    (!aid bl. FLOOKUP s0.vs_allocas aid = SOME bl ==>
      FLOOKUP s.vs_allocas aid = SOME bl) /\
    (!x. not_fresh_at sa x ==> FLOOKUP G x = FLOOKUP G0 x /\
      op_taint tn (Var x) = op_taint tn0 (Var x))) /\
  storage_trace_domain cx st0 ee.storage_trace /\
  (!H. valid_horizon cx st0 H ee.storage_trace ==>
    gas_origin_ptr_path (DF H,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
      (s,G,tn) [] (OK sstart,Gstart,tnstart) /\
    expr_sim_inv bc cx (extend_local env id typ F)
      (ee with <|scopes := (FEMPTY |+ (id,
        <|assignable := F; type := tyv; value := IntV (n1 + &k);
          popped := []|>)) :: ee.scopes; gas_obs := []|>) /\
    stmt_state_rel H ctx func bc cx
      (ee with <|scopes := (FEMPTY |+ (id,
        <|assignable := F; type := tyv; value := IntV (n1 + &k);
          popped := []|>)) :: ee.scopes; gas_obs := []|>) sstart /\
    storage_well_formed_on cx ee (FST H) /\
    return_buf_frame d bc sb0 sstart /\ alloca_history func sstart /\
    ghost_inv_at (DF H) lo d bc cx
      (ee with <|scopes := (FEMPTY |+ (id,
        <|assignable := F; type := tyv; value := IntV (n1 + &k);
          popped := []|>)) :: ee.scopes; gas_obs := []|>) Gstart tnstart sstart /\
    ~sstart.vs_halted /\ sstart.vs_current_bb = sb0.cs_current_bb /\
    sstart.vs_inst_idx = LENGTH sb0.cs_current_insts /\
    ret_pc_ok bc sb0 sstart /\ allocas_from lo sstart /\
    lookup_var q sstart = SOME w /\ ptr_covers Gstart tnstart q sstart 32 /\
    FLOOKUP sstart.vs_allocas sa.cs_next_id = SOME (w2n w,32) /\
    w2n w + 32 < dimword (:256) /\ w2n w + 32 <= sstart.vs_alloca_next /\
    (!name b len. local_region cenv ee.scopes sstart name b len ==>
      regions_disjoint (w2n w) 32 b len) /\
    FLOOKUP Gstart cv = NONE /\ FLOOKUP Gstart ev = NONE /\
    op_taint tnstart (Var cv) = {} /\ op_taint tnstart (Var ev) = {} /\
    lookup_var ev sstart = SOME (i2w n2) /\
    lookup_var cv sstart = SOME (i2w (n1 + &k)) /\
    s0.vs_alloca_next <= sstart.vs_alloca_next /\
    (!x v. not_fresh_at sa x /\ lookup_var x s0 = SOME v ==>
      lookup_var x sstart = SOME v) /\
    (!aid bl. FLOOKUP s0.vs_allocas aid = SOME bl ==>
      FLOOKUP sstart.vs_allocas aid = SOME bl) /\
    (!x. not_fresh_at sa x ==> FLOOKUP Gstart x = FLOOKUP G0 x /\
      op_taint tnstart (Var x) = op_taint tn0 (Var x))) /\
  eval_stmts cx stmts
    (ee with <|scopes := (FEMPTY |+ (id,
      <|assignable := F; type := tyv; value := IntV (n1 + &k);
        popped := []|>)) :: ee.scopes; gas_obs := gs|>) = (res,mid) /\
  mid.gas_obs = [] /\ storage_trace_domain cx st0 mid.storage_trace /\
  (!H. valid_horizon cx st0 H mid.storage_trace ==>
    ?cenv''.
      stmt_lands (InLoop exit_lbl incr_lbl) sb1 res t /\ ~t.vs_halted /\
      (res = INL () ==> ~block_is_terminated sb1 /\ cenv'' = bc_out) /\
      cenv_top_ext bc cenv'' mid.scopes /\
      stmt_state_rel H ctx func cenv'' cx mid t /\
      storage_well_formed_on cx mid (FST H) /\
      return_buf_frame d cenv'' sb1 t /\ alloca_history func t /\
      sstart.vs_alloca_next <= t.vs_alloca_next /\
      ghost_inv_at (DF H) lo d cenv'' cx mid G1 tn1 t /\
      (!x v. not_fresh_at sb0 x /\ lookup_var x sstart = SOME v ==>
        lookup_var x t = SOME v) /\
      (!aid bl. FLOOKUP sstart.vs_allocas aid = SOME bl ==>
        FLOOKUP t.vs_allocas aid = SOME bl) /\
      (!x. not_fresh_at sb0 x ==> FLOOKUP G1 x = FLOOKUP Gstart x /\
        op_taint tn1 (Var x) = op_taint tnstart (Var x))) ==>
  (res = INL () \/ res = INR BreakException \/ res = INR ContinueException) /\
  ?u G2 tn2. !H. valid_horizon cx st0 H mid.storage_trace ==>
    gas_origin_ptr_path (DF H,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
      (t,G1,tn1) [] (OK u,G2,tn2) /\
    (mid with scopes := TL mid.scopes).gas_obs = [] /\ ~u.vs_halted /\
    (res = INR BreakException ==>
      stmt_lands lctx r (INL ()) u /\ ~block_is_terminated r /\
      cenv_top_ext cenv cenv (TL mid.scopes) /\
      stmt_state_rel H ctx func cenv cx (mid with scopes := TL mid.scopes) u /\
      storage_well_formed_on cx (mid with scopes := TL mid.scopes) (FST H) /\
      return_buf_frame d cenv r u /\ alloca_history func u /\
      s0.vs_alloca_next <= u.vs_alloca_next /\
      ghost_inv_at (DF H) lo d cenv cx (mid with scopes := TL mid.scopes) G2 tn2 u /\
      (!x v. not_fresh_at sa x /\ lookup_var x s0 = SOME v ==>
        lookup_var x u = SOME v) /\
      (!aid bl. FLOOKUP s0.vs_allocas aid = SOME bl ==>
        FLOOKUP u.vs_allocas aid = SOME bl) /\
      (!x. not_fresh_at sa x ==> FLOOKUP G2 x = FLOOKUP G0 x /\
        op_taint tn2 (Var x) = op_taint tn0 (Var x))) /\
    (res <> INR BreakException ==>
      expr_sim_inv cenv cx env (mid with scopes := TL mid.scopes) /\
      stmt_state_rel H ctx func cenv cx (mid with scopes := TL mid.scopes) u /\
      storage_well_formed_on cx (mid with scopes := TL mid.scopes) (FST H) /\
      return_buf_frame d cenv sa u /\ alloca_history func u /\
      s0.vs_alloca_next <= u.vs_alloca_next /\ allocas_from lo u /\
      ghost_inv_at (DF H) lo d cenv cx (mid with scopes := TL mid.scopes) G2 tn2 u /\
      u.vs_current_bb = cond_lbl /\ u.vs_inst_idx = 0 /\
      lookup_var q u = SOME w /\ ptr_covers G2 tn2 q u 32 /\
      FLOOKUP u.vs_allocas sa.cs_next_id = SOME (w2n w,32) /\
      w2n w + 32 < dimword (:256) /\ w2n w + 32 <= u.vs_alloca_next /\
      (!name b len. local_region cenv (TL mid.scopes) u name b len ==>
        regions_disjoint (w2n w) 32 b len) /\
      FLOOKUP G2 cv = NONE /\ FLOOKUP G2 ev = NONE /\
      op_taint tn2 (Var cv) = {} /\ op_taint tn2 (Var ev) = {} /\
      lookup_var ev u = SOME (i2w n2) /\
      (?kk. kk <= Num (n2-n1) /\
        rs = DROP kk (GENLIST (\j. Value (IntV (n1 + &j))) (Num (n2-n1))) /\
        lookup_var cv u = SOME (i2w (n1 + &kk)) /\
        n1 + &kk <= n2 /\ Num (n2-n1) < dimword (:256)) /\
      (!x v. not_fresh_at sa x /\ lookup_var x s0 = SOME v ==>
        lookup_var x u = SOME v) /\
      (!aid bl. FLOOKUP s0.vs_allocas aid = SOME bl ==>
        FLOOKUP u.vs_allocas aid = SOME bl) /\
      (!x. not_fresh_at sa x ==> FLOOKUP G2 x = FLOOKUP G0 x /\
        op_taint tn2 (Var x) = op_taint tn0 (Var x)))
Proof
  strip_tac >>
  `not_fresh_at sb0 cv /\ not_fresh_at sb0 ev /\
   (!x. not_fresh_at sa x ==> x <> cv) /\ q <> cv /\ cv <> ev /\
   sa.cs_next_var < sb0.cs_next_var` by
    (gvs[loweringStateRelDefsTheory.not_fresh_at_def] >>
     metis_tac[ASCIInumbersTheory.toString_inj]) >>
  mp_tac (Q.INST [`jstore` |-> `sa.cs_next_id + 7`]
    (SPEC_ALL for_range_exit_post_layout_full)) >>
  (impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)) >>
  simp[]
QED

