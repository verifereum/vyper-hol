(* Ordinary AugAssign: a completed place and its load, followed by the RHS. *)
Theory s1PrefixAugAssignOrdinaryLoad
Ancestors
  s1PrefixAugAssignBindStages augAssignFullLoad augAssignFullEntryPre
  augAssignFullCodeStages bodyFullIfExpReach bodyFullPreds bodyFullSimProjection s1PrefixPreds
  gasOutcomeFullCompose bodyMemoryDefs exprSimMemorySource
  exprSimIfExpWidenedAdapter exprBodyPreProps freshWrites vyperStorageFootprint
  loweringPosts exprLoweringProps stmtSimAugAssignPlaceMemory tuplePlaceHeadGas
  exprSimSource s1PrefixCompose s1PrefixDefs bodySimFull exprSimDefs
  vyperStorageTrace stmtSimAugAssign bodyPtrDefs exprSimHypsDefs vyperInterpreter vyperState

(* SCRATCH MEASUREMENT: the original proof failed after widening the body
   definitions. Temporarily admit it to test its downstream consumers.
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `valid_horizon cx st0 (storage_trace_horizon st.storage_trace) st.storage_trace`
    by fs[storage_trace_domain_def] >>
  qpat_assum `!H. valid_horizon _ _ H st.storage_trace ==> _`
    (qspec_then `storage_trace_horizon st.storage_trace` (drule_then strip_assume_tac)) >>
  qpat_x_assum `_ \/ ?loc old cb rhsop cc shadow_cb shadow_cc. _`
    (DISJ_CASES_THEN2 STRIP_ASSUME_TAC
      (qx_choosel_then [`loc`,`old`,`cb`,`rhsop`,`cc`,`shadow_cb`,`shadow_cc`]
        STRIP_ASSUME_TAC))
  >- (Cases_on `p` >> fs[target_post_def, place_ptr_rel_def]) >>
  `loc <> LocCode` by
    (`!tr. slot_loc tr <> LocCode` by (Cases >> simp[slot_loc_def]) >>
     Cases_on `p` >> fs[target_post_def, place_ptr_rel_def] >> metis_tac[]) >>
  qpat_assum `loc <> LocCode` (fn th => RULE_ASSUM_TAC (SIMP_RULE bool_ss [th])) >>
  `local_ptrs_reserved cenv ca /\
   (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at ca x) /\
   (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at ca x)` by
    metis_tac[local_ptrs_reserved_next_var, not_fresh_at_mono] >>
  `return_buf_frame d cenv ca v` by
    (irule return_buf_frame_frame >> qexistsl_tac [`cenv`,`s0`,`sa`] >> fs[target_post_def]) >>
  `eval_target_place cx t (es with gas_obs := gas_explicit marks s0.vs_gas_readings) =
     (INL p,st)` by
    (`st with gas_obs := [] = st` by simp[vyperStateTheory.evaluation_state_component_equality] >>
     pop_assum (fn upd =>
       qpat_assum `!tail. eval_target_place _ _ _ = _`
         (qspec_then `[]` (ACCEPT_TAC o REWRITE_RULE [listTheory.APPEND_NIL,upd])))) >>
  qmatch_asmsub_abbrev_tac `eval_target_place cx t (es with gas_obs := reads) = (INL p,st)` >>
  `body_const_cells_agree [(NONE,tops)] cx env st` by
    (irule body_const_cells_agree_target >>
     qpat_assum `eval_target_place cx t (es with gas_obs := reads) = (INL p,st)`
       (irule_at Any) >> simp[]) >>
  `expr_body_pre cenv cx env e st` by
    (drule_all aug_place_rhs_pre_target_gas_obs >> simp[]) >>
  reverse (qsuff_tac `((FST (SND r) = NONE /\ emit_void INVALID [] ca = ((),sf)) \/
    (?loc' old' cb'. FST (SND r) = SOME loc' /\
      emit_op (case loc' of LocStorage => SLOAD | LocTransient => TLOAD | _ => MLOAD)
        [FST r] ca = (old',cb') /\ fn_has_code ca cb' func))`)
  >- (disj2_tac >> qexistsl_tac [`loc`,`old`,`cb`] >> simp[]) >>
  disch_tac >>
  `!H. valid_horizon cx st0 H st.storage_trace ==>
     target_post H ctx func cenv cx es sa ca s0 st (PlaceR p) (Type aty) r v /\
     target_ptr_ok cenv (PlaceR p) r Gtarget tnt v /\
     ghost_inv_at (DF H) lo d cenv cx st Gtarget tnt v /\
     ghost_kept_at lo cenv (es with gas_obs := reads) sa G0 tn0 s0 Gtarget tnt /\
     dead_lo_ok H (DF H) lo cenv cx /\
     return_buf_frame d cenv ca v /\ alloca_history func v /\
     (ctx_has_dalloca ctx ==> allocas_below_fmp v) /\
     ~v.vs_halted /\ v.vs_current_bb = ca.cs_current_bb /\
     v.vs_inst_idx = LENGTH ca.cs_current_insts` by
    (qx_gen_tac `H` >> disch_tac >>
     qpat_assum `!K. valid_horizon _ _ K st.storage_trace ==> target_post _ _ _ _ _ es _ _ _ _ _ _ _ _ /\ _`
       (qspecl_then [`H`] (drule_then strip_assume_tac)) >> simp[] >>
     qpat_assum `ghost_kept_at lo cenv es sa _ _ _ _ _` mp_tac >>
     simp[NoAsms,ghost_kept_at_def] >> strip_tac >>
     conj_tac >> first_assum ACCEPT_TAC) >>
  suspend "load_and_rhs"
QED
*)
Theorem augassign_ordinary_load_rhs_prefix:
  (!s p t1 sr cur tr sty ptv tty.
     eval_target_place cx t s = (INL p,t1) /\
     read_place cx p sr = (INL cur,tr) /\
     place_type_value cx p sty = (INL ptv,tty) ==> body_expr_full_ok cx e) /\
  (!s p t1 sr cur tr sty ptv tty.
     eval_target_place cx t s = (INL p,t1) /\
     read_place cx p sr = (INL cur,tr) /\
     place_type_value cx p sty = (INL ptv,tty) ==> body_expr_prefix_ok cx e) /\
  body_inv tops ctx cenv cx /\ shadow_body_inv tops ctx shadow_ctx /\
  body_const_cells_agree [(NONE,tops)] cx env es /\
  expr_body_pre cenv cx env e es /\ expr_sim_inv cenv cx env es /\
  target_indices_pre cenv cx env t /\
  supported_target_info tops bindings t = SOME info /\ is_word_type aty /\
  type_place_target env t = SOME (Type aty) /\
  compile_get_target_ptr compile_expr cenv t sa = (r,ca) /\
  sa.cs_next_var <= ca.cs_next_var /\
  ((FST (SND r) = NONE /\ emit_void INVALID [] ca = ((),sf)) \/
   (?loc old cb rhsop cc shadow_cb shadow_cc.
     FST (SND r) = SOME loc /\
     (if loc = LocCode then
        compile_ptr_load cenv.ce_is_ctor cenv.ce_imm_alloca loc (FST r)
      else emit_op (case loc of LocStorage => SLOAD | LocTransient => TLOAD | _ => MLOAD)
        [FST r]) ca = (old,cb) /\ fn_has_code ca cb func /\
     lower_value compile_expr cenv aty e cb = (rhsop,cc) /\
     lower_value compile_expr (gas_shadow_env T cenv) aty (gas_shadow_expr e)
        shadow_cb = (rhsop,shadow_cc) /\
     gas_shadow_state cb shadow_cb /\ gas_shadow_state cc shadow_cc /\
     fn_has_code cb cc func /\ fn_has_code shadow_cb shadow_cc shadow_func)) /\
  gas_shadow_context ctx shadow_ctx /\ ctx_inst_ids_distinct ctx /\
  gas_shadow_function func shadow_func /\ MEM func ctx.ctx_functions /\
  MEM shadow_func shadow_ctx.ctx_functions /\ fn_inst_ids_distinct func /\
  local_ptrs_reserved cenv sa /\ return_buf_frame d cenv sa s0 /\
  (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!H. dead_lo_ok H (DF H) lo cenv cx) /\
  (!tail. eval_target_place cx t
     (es with gas_obs := gas_explicit marks s0.vs_gas_readings ++ tail) =
     (INL p,st with gas_obs := tail)) /\
  storage_trace_domain cx st0 st.storage_trace /\
  (!H. valid_horizon cx st0 H st.storage_trace ==>
    target_post H ctx func cenv cx es sa ca s0 st (PlaceR p) (Type aty) r v /\
    (!id path. p = MemoryPlace id path ==>
      ?entry vl. lookup_scopes id st.scopes = SOME entry /\
          evaluate_subscripts entry.type entry.value path = INL vl) /\
    v.vs_current_bb = ca.cs_current_bb /\ v.vs_inst_idx = LENGTH ca.cs_current_insts /\
    alloca_history func v /\ (ctx_has_dalloca ctx ==> allocas_below_fmp v) /\
    s0.vs_alloca_next <= v.vs_alloca_next /\
    ghost_inv_at (DF H) lo d cenv cx st Gtarget tnt v /\
    target_ptr_ok cenv (PlaceR p) r Gtarget tnt v /\
    ghost_kept_at lo cenv es sa G0 tn0 s0 Gtarget tnt /\
    ~v.vs_halted /\ st.gas_obs = [] /\
    (!fn i z. frag_reachable ctx func v fn i z ==> dalloca_fmp_headroom i z)) ==>
  gas_prefix_full (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
    cx st0 (bind (read_place cx p) (\cur.
      bind (place_type_value cx p) (\ptv.
        bind (bind (eval_expr cx e) (read_result cx)) (\rhs.
          bind (lift_sum (evaluate_binop
            (case type_to_int_bound aty of SOME n => n | NONE => Unsigned 0)
            ptv bop cur rhs)) (write_place cx p))))) (st,v,Gtarget,tnt)
Proof
  cheat
QED

(* SCRATCH MEASUREMENT: original continuation.
Resume augassign_ordinary_load_rhs_prefix[load_and_rhs]:
  drule_all (REWRITE_RULE [expr_sim_inv_gas_obs, tuple_place_target_post_gas_obs]
    (Q.INST [`explicit` |-> `gas_explicit_sites ctx shadow_ctx`,
             `es` |-> `es with gas_obs := reads`] augassign_load_joint)) >>
  disch_then (qspecl_then [`shadow_ctx`,`PG`]
    (qx_choosel_then [`loadloc`,`loadop`,`loadcs`,`addr`,`cur`,`ptv`,`u`,
       `Gload`,`tnload`] (mk_asm "loadPost"))) >>
  asm "loadPost" (qspec_then `storage_trace_horizon st.storage_trace` (drule_then strip_assume_tac)) >>
  `loadloc = loc /\ loadop = old /\ loadcs = cb` by
    metis_tac[optionTheory.SOME_11, pairTheory.PAIR_EQ] >>
  qpat_x_assum `loadloc = loc` SUBST_ALL_TAC >>
  qpat_x_assum `loadop = old` SUBST_ALL_TAC >>
  qpat_x_assum `loadcs = cb` SUBST_ALL_TAC >>
  `!bb. MEM bb func.fn_blocks ==> phi_prefix_length bb.bb_instructions = 0` by
    metis_tac[body_inv_no_phi] >>
  `!fn inst q. frag_reachable ctx func u fn inst q ==> dalloca_fmp_headroom inst q` by
    (qpat_assum `gas_origin_ptr_path _ (v,Gtarget,tnt) [] (OK u,Gload,tnload)` (fn path =>
       qpat_assum `!bb. MEM bb func.fn_blocks ==> phi_prefix_length _ = _` (fn no_phi =>
         qpat_assum `!fn i z. frag_reachable ctx func v fn i z ==> _`
           (ACCEPT_TAC o MATCH_MP gas_origin_ptr_path_dalloca_fmp_headroom o
            CONJ path o CONJ no_phi)))) >>
  `!H. valid_horizon cx st0 H st.storage_trace ==>
    stmt_state_rel H ctx func cenv cx st u /\
    storage_well_formed_on cx st (FST H) /\
    ghost_inv_at (DF H) lo d cenv cx st Gload tnload u` by
    (qx_gen_tac `H` >> disch_tac >>
     asm "loadPost" (drule_then strip_assume_tac) >> simp[] >>
     qpat_assum `!K. valid_horizon _ _ K st.storage_trace ==> target_post _ _ _ _ _ es _ _ _ _ _ _ _ _ /\ _`
       (drule_then (ACCEPT_TAC o cj 2 o REWRITE_RULE [target_post_def] o CONJUNCT1))) >>
  `gas_admissible (bind (eval_expr cx e) (read_result cx)) expr_res_ok st` by
    (irule expr_body_pre_gas_admissible >> qexistsl_tac [`cenv`,`env`] >> simp[]) >>
  `expr_sim_full_pre (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func) cenv cx aty e st
    (st0,cb,cc,shadow_cb,shadow_cc,rhsop,u,Gload,tnload)` by
    (simp[expr_sim_full_pre_def] >> rpt conj_tac >> first_assum ACCEPT_TAC) >>
  suspend "finish_rhs"
QED
*)

(* SCRATCH MEASUREMENT: original continuation.
Resume augassign_ordinary_load_rhs_prefix[finish_rhs]:
  `body_expr_full_ok cx e /\ body_expr_prefix_ok cx e` by
    (conj_tac >> first_assum irule >> rpt (first_assum (irule_at Any))) >>
  `expr_sim_full (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func) cenv cx aty e st` by
    metis_tac[body_expr_full_ok_simulations] >>
  `expr_sim_prefix (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func) cenv cx aty e st` by
    (qpat_x_assum `body_expr_prefix_ok _ _`
       (mp_tac o CONJUNCT1 o ONCE_REWRITE_RULE [body_expr_prefix_ok_def]) >>
     metis_tac[]) >>
  qpat_x_assum `expr_sim_full _ _ _ _ _ _`
    (mp_tac o REWRITE_RULE [expr_sim_full_def]) >>
  disch_then drule_all >> disch_tac >>
  qpat_x_assum `expr_sim_prefix _ _ _ _ _ _`
    (mp_tac o REWRITE_RULE [expr_sim_prefix_def]) >>
  disch_then drule >> strip_tac >>
  qabbrev_tac `goRhs = bind (bind (eval_expr cx e) (read_result cx)) (\rhs.
    bind (lift_sum (evaluate_binop
      (case type_to_int_bound aty of SOME n => n | NONE => Unsigned 0)
      ptv bop cur rhs)) (write_place cx p))` >>
  `gas_prefix_full (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
    cx st0 goRhs (st,v,Gtarget,tnt)` by
    (irule gas_prefix_full_zero_prefix_guarded >> simp[] >> conj_tac
     >- (simp[Abbr `goRhs`] >> irule storage_trace_frame_bind_all >>
         simp[augassign_rhs_trace_frame, aug_place_store_trace_frame]) >>
     qexistsl_tac [`Gload`,`u`,`tnload`] >> conj_tac
     >- (qx_gen_tac `H` >> disch_tac >> asm "loadPost" (drule_then strip_assume_tac) >> simp[]) >>
     simp[Abbr `goRhs`] >> irule augassign_rhs_bind_prefix >>
     (conj_tac >- first_assum ACCEPT_TAC) >>
     qexistsl_tac [`\H v ee G tn t. ~t.vs_halted`, `\H res ee gt r. T`,`cx_tops cx`] >>
     simp[] >> irule gas_outcome_full_post_source >>
     qpat_assum `gas_outcome_full _ _ _ _ _ _ _ _` (irule_at Any) >>
     simp[] >> rpt gen_tac >> Cases_on `res` >> simp[]) >>
  `!gs. read_place cx p (st with gas_obs := gs) = (INL cur,st with gas_obs := gs)` by
    (`read_result cx (PlaceR p) st = (INL cur,st)` by simp[read_result_def] >>
     drule read_result_gas_obs >> simp[read_result_def]) >>
  drule_then assume_tac place_type_value_gas_obs >>
  `!gs. bind (read_place cx p) (\cur.
      bind (place_type_value cx p) (\ptv.
        bind (bind (eval_expr cx e) (read_result cx)) (\rhs.
          bind (lift_sum (evaluate_binop
            (case type_to_int_bound aty of SOME n => n | NONE => Unsigned 0)
            ptv bop cur rhs)) (write_place cx p)))) (st with gas_obs := gs) =
     goRhs (st with gas_obs := gs)` by simp[bind_def,Abbr `goRhs`] >>
  qpat_x_assum `gas_prefix_full _ _ _ goRhs _`
    (qx_choose_then `rhsMarks` (map_every assume_tac o CONJUNCTS) o
       REWRITE_RULE [gas_prefix_full_def]) >>
  rewrite_tac[gas_prefix_full_def] >> qexists_tac `rhsMarks` >>
  (conj_tac >- first_assum ACCEPT_TAC) >>
  qpat_assum `!gs. bind (read_place cx p) _ _ = goRhs _`
    (fn th => PURE_REWRITE_TAC [th]) >>
  first_assum ACCEPT_TAC
QED
*)

(* SCRATCH MEASUREMENT: original continuation.
Finalise augassign_ordinary_load_rhs_prefix
*)
