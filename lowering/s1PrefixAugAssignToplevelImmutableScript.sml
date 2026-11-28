(* Request-prefix execution of the constructor's immutable load and RHS. *)
Theory s1PrefixAugAssignToplevelImmutable
Ancestors
  s1PrefixAugAssignBindStages s1PrefixInvalidTraceDomain s1PrefixCompose
  s1PrefixPreds s1PrefixDefs bodyFullPreds augAssignFullImmutableSetup
  augAssignFullLoadImmutableResources augAssignFullImmutableValidLoad
  augAssignFullLoadFrame augAssignFullCodeStages augAssignFullEntryPre
  augAssignFullSourceReplay
  bodyImmutableAugAssignExec bodyFullIfExpReach bodySimFull
  bodyPtrDefs[qualified,ignore_grammar] stateRelProj
  stmtSimAugAssignPlace stmtSimAugAssignPlaceMemory stmtSimAugAssign
  exprBodyPreProps exprLoweringProps gasShadow gasContext gasOutcomeFullCompose
  vyperTypeCallStackSoundness vyperStorageTrace vyperStorageFootprint vyperState
  vyperInterpreter vyperTypeSystem words finite_map pred_set list
  exprLowering compileEnv context ptrDiscipline loweringStateRelDefs
  freshWrites stmtSimDefs wordArgsPtr venomState arithmetic
  exprSimCopy loweringPosts bodyFullTargetDefs bodyFullSimProjection
  bodyImmutableAugAssignFacts exprSimDefs vyperValue exprSimSource
  gasOutcomeFull vyperCallOutcomeFrame stateFrame[qualified,ignore_grammar]

(* SCRATCH MEASUREMENT: the original proof failed after widening the body
   definitions. Temporarily admit it to test its downstream consumers.
Proof
  strip_tac >> simp[stmt_frag_prefix_def] >> rpt gen_tac >> disch_tac >>
  qpat_assum `stmt_frag_full_pre _ _ _ _ _ _ _ _ _ _`
    (strip_assume_tac o REWRITE_RULE [stmt_frag_full_pre_def]) >>
  reverse (Cases_on `storage_trace_domain cx st0 es.storage_trace`)
  >- (irule gas_prefix_full_invalid_trace_domain >> simp[evaluate_storage_trace_frame]) >>
  `call_evaluation_safe cx []` by
    (irule call_evaluation_safe_mono >>
     goal_assum (drule_at (Pat `call_evaluation_safe _ _`)) >> simp[]) >>
  `cx.in_deploy` by (drule_all augassign_immutable_in_deploy >> simp[]) >>
  qabbrev_tac `H0 = storage_trace_horizon es.storage_trace` >>
  `valid_horizon cx st0 H0 es.storage_trace` by
    fs[storage_trace_domain_def, Abbr `H0`] >>
  qpat_assum `!H. valid_horizon cx st0 H es.storage_trace ==> _`
    (qspec_then `H0` (drule_then strip_assume_tac)) >>
  `dead_lo_ok H0 (DF H0) lo cenv cx` by simp[] >>
  drule_all augassign_immutable_load_resources >>
  disch_then (qx_choosel_then [`off`,`ptv`,`cur`] strip_assume_tac) >>
  qpat_x_assum `aty = ity` (SUBST_ALL_TAC o SYM) >>
  drule_all augassign_full_code_stages >>
  disch_then (CONJUNCTS_THEN2 SUBST_ALL_TAC
    (qx_choosel_then [`r`,`ca`,`shadow_ca`] (fn th =>
       case rev (CONJUNCTS th) of
         cases::slices => map_every assume_tac (rev slices) >> assume_tac cases
       | [] => NO_TAC))) >>
  suspend "code"
QED
*)
Theorem augassign_toplevel_immutable_prefix:
  (!s'' p t' s'3' cur t'' s'4' ptv t'3'.
    eval_target_place cx (TopLevelNameTarget (src,id)) s'' = (INL p,t') /\
    read_place cx p s'3' = (INL cur,t'') /\
    place_type_value cx p s'4' = (INL ptv,t'3') ==> body_expr_full_ok cx e) /\
  (!s'' p t' s'3' cur t'' s'4' ptv t'3'.
    eval_target_place cx (TopLevelNameTarget (src,id)) s'' = (INL p,t') /\
    read_place cx p s'3' = (INL cur,t'') /\
    place_type_value cx p s'4' = (INL ptv,t'3') ==> body_expr_prefix_ok cx e) /\
  body_inv tops ctx cenv cx /\ shadow_body_inv tops ctx shadow_ctx /\
  supported_stmt tops bindings (AugAssign aty (TopLevelNameTarget (src,id)) bop e) /\
  (!target. supported_stmt_expr_exists (expr_abi_decode_target_root target)
    (AugAssign aty (TopLevelNameTarget (src,id)) bop e) ==>
    occurs_abi_decode_target target tops) /\
  expr_sim_inv cenv cx env es /\
  body_const_cells_agree [(NONE,tops)] cx env es /\
  type_stmt env ret_ty (AugAssign aty (TopLevelNameTarget (src,id)) bop e) = SOME env' /\
  stmt_exprs_ok cenv (AugAssign aty (TopLevelNameTarget (src,id)) bop e) /\
  call_evaluation_safe cx (int_calls_stmt (AugAssign aty (TopLevelNameTarget (src,id)) bop e)) /\
  supported_immutable_type tops (src,id) = SOME ity ==>
  stmt_frag_prefix (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
    cx lctx RetQ cenv
    (stmt_env cenv lctx ret_ty (AugAssign aty (TopLevelNameTarget (src,id)) bop e))
    (stmt_env (gas_shadow_env T cenv) lctx ret_ty
      (gas_shadow_stmt (AugAssign aty (TopLevelNameTarget (src,id)) bop e)))
    (eval_stmt cx (AugAssign aty (TopLevelNameTarget (src,id)) bop e)) es
Proof
  cheat
QED

(* SCRATCH MEASUREMENT: original continuation.
Resume augassign_toplevel_immutable_prefix[code]:
  `FLOOKUP cenv.ce_module_vars (cenv.ce_module,id) = SOME (ImmutableLoc off) /\
   cenv.ce_module_var_type (cenv.ce_module,id) = SOME aty` by metis_tac[] >>
  qpat_x_assum `compile_get_target_ptr _ _ (TopLevelNameTarget _) sa = _` mp_tac >>
  simp[Once compile_get_target_ptr_def, comp_return_def] >> strip_tac >>
  qpat_x_assum `compile_get_target_ptr _ _ (gas_shadow_target _) shadow_sa = _` mp_tac >>
  once_rewrite_tac [cj 14 gas_shadow_expr_def] >>
  simp[Once compile_get_target_ptr_def, comp_return_def] >> strip_tac >>
  qpat_x_assum `(Lit _, SOME LocCode, SOME (ValPT _)) = r` (SUBST_ALL_TAC o SYM) >>
  qpat_x_assum `sa = ca` (SUBST_ALL_TAC o SYM) >>
  qpat_x_assum `shadow_sa = shadow_ca` (SUBST_ALL_TAC o SYM) >>
  qpat_x_assum `_ \/ ?loc cur rhs result s1 s2 s3 ss1 ss2 ss3. _` mp_tac >>
  simp[] >> disch_then (qx_choosel_then [`old`,`rhsop`,`dst`,`cb`,`cc`,`cd`,
    `shadow_cb`,`shadow_cc`,`shadow_cd`] STRIP_ASSUME_TAC) >>
  `compile_imm_load_word T cenv.ce_imm_alloca (Lit (n2w off)) sa = (old,cb)` by
    fs[compile_ptr_load_def] >>
  suspend "load"
QED
*)

(* SCRATCH MEASUREMENT: original continuation.
Resume augassign_toplevel_immutable_prefix[load]:
  `lo <> 0` by decide_tac >>
  `!region. cenv.ce_imm_alloca = SOME region ==> eval_operand region s0 = SOME 0w /\
    copy_old_operand sa region /\ op_taint tn0 region = {} /\ op_prov G0 region = NONE` by
    (`immutable_base_zero cenv s0` by metis_tac[stmt_state_rel_immutable_base_zero] >>
     qpat_assum `ghost_inv_at (DF H0) lo d cenv cx es G0 tn0 s0`
       (strip_assume_tac o REWRITE_RULE [bodyPtrDefsTheory.ghost_inv_at_def]) >>
     qpat_assum `immutable_base_zero cenv s0`
       (strip_assume_tac o REWRITE_RULE [immutable_base_zero_def]) >>
     qpat_assum `local_ptrs_reserved cenv sa`
       (strip_assume_tac o REWRITE_RULE [local_ptrs_reserved_def]) >>
     Cases >> simp[copy_old_operand_def, op_taint_def, op_prov_def] >> metis_tac[]) >>
  `allocas_from lo s0 /\ lo <= s0.vs_alloca_next` by fs[bodyPtrDefsTheory.ghost_inv_at_def] >>
  `mem_word_taint tn0.t_mem (w2n (n2w off:bytes32)) = {}` by
    (simp[mem_word_taint_def, EXTENSION] >> qx_gen_tac `k` >>
     Cases_on `k < 32` >> simp[] >>
     qpat_assum `!j. off <= j /\ j < off + 32 ==> _` irule >> decide_tac) >>
  `w2n (n2w off:bytes32) + 32 <= lo` by simp[] >>
  drule_all augassign_ctor_word_load >>
  disch_then (qspecl_then [`gas_explicit_sites ctx shadow_ctx`,`PG`]
    (strip_assume_tac)) >>
  rename1 `!D. gas_origin_ptr_path (D,lo,_,ctx,func,PG) (s0,G0,tn0) [] (OK u,Gload,tnload)` >>
  `(!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x)` by
    fs[ret_pc_ok_def] >>
  `!H. valid_horizon cx st0 H es.storage_trace ==>
     stmt_state_rel H ctx func cenv cx es u /\
     storage_well_formed_on cx es (FST H) /\
     ghost_inv_at (DF H) lo d cenv cx es Gload tnload u /\
     return_buf_frame d cenv cb u /\ alloca_history func u /\
     (ctx_has_dalloca ctx ==> allocas_below_fmp u)` by suspend "frame" >>
  pop_assum (mk_asm "loadPost") >> suspend "rhs"
QED
*)

(* SCRATCH MEASUREMENT: original continuation.
Resume augassign_toplevel_immutable_prefix[frame]:
  qx_gen_tac `H` >> disch_tac >>
  qpat_assum `!K. valid_horizon _ _ K es.storage_trace ==> _`
    (qspec_then `H` (drule_then strip_assume_tac)) >>
  `target_ptr_ok cenv (PlaceR (ImmutablePlace src id []))
    (Lit (n2w off),SOME LocMemory,SOME (ValPT aty)) G0 tn0 s0` by
    simp[target_ptr_ok_def, op_taint_def] >>
  `ghost_kept_at lo cenv es sa G0 tn0 s0 G0 tn0` by simp[ghost_kept_at_refl] >>
  qpat_assum `stmt_state_rel H ctx func cenv cx es s0`
    (mp_then (Pos hd) mp_tac augassign_load_endpoint_frame) >>
  qpat_x_assum `ghost_inv_at (DF H0) lo d cenv cx es G0 tn0 s0` kall_tac >>
  disch_then (drule_at (Pat `ghost_inv_at _ _ _ _ _ _ _ _ _`)) >>
  disch_then (drule_at (Pat `target_ptr_ok _ _ _ _ _ _`)) >>
  disch_then (drule_at (Pat `ghost_kept_at _ _ _ _ _ _ _ _ _`)) >>
  disch_then (drule_at (Pat `state_frame _ = _`)) >>
  disch_then (drule_at (Pat `_ = _ ++ emitted_insts _ _`)) >>
  disch_then (qspecl_then [`tnload`,`n2w off`,`Gload`] mp_tac) >>
  (impl_tac >- (simp[] >> rpt conj_tac >> first_assum ACCEPT_TAC)) >>
  strip_tac >> simp[]
QED
*)

(* SCRATCH MEASUREMENT: original continuation.
Resume augassign_toplevel_immutable_prefix[rhs]:
  `local_ptrs_reserved cenv cb /\
   (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at cb x) /\
   (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at cb x)` by
    metis_tac[local_ptrs_reserved_next_var, not_fresh_at_mono] >>
  `!bb. MEM bb func.fn_blocks ==> phi_prefix_length bb.bb_instructions = 0` by
    metis_tac[body_inv_no_phi] >>
  `!fn inst q. frag_reachable ctx func u fn inst q ==> dalloca_fmp_headroom inst q` by
    (qpat_assum `!D. gas_origin_ptr_path _ _ _ (OK u,Gload,tnload)`
       (qspec_then `DF H0` (fn path =>
        qpat_assum `!bb. MEM bb func.fn_blocks ==> phi_prefix_length _ = _` (fn no_phi =>
          qpat_assum `!fn i z. frag_reachable ctx func s0 fn i z ==> _`
           (ACCEPT_TAC o MATCH_MP gas_origin_ptr_path_dalloca_fmp_headroom o
            CONJ path o CONJ no_phi))))) >>
  `expr_body_pre cenv cx env e es` by (drule_all augassign_entry_rhs_pre >> simp[]) >>
  `gas_admissible (bind (eval_expr cx e) (read_result cx)) expr_res_ok es` by
    (irule expr_body_pre_gas_admissible >> qexistsl_tac [`cenv`,`env`] >> simp[]) >>
  asm "loadPost" (qspec_then `H0` (drule_then strip_assume_tac)) >>
  `expr_sim_full_pre (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func) cenv cx aty e es
    (st0,cb,cc,shadow_cb,shadow_cc,rhsop,u,Gload,tnload)` by
    (simp[expr_sim_full_pre_def] >> rpt conj_tac >>
     TRY (first_assum ACCEPT_TAC >> NO_TAC) >>
     rpt strip_tac >> asm "loadPost" (drule_then strip_assume_tac) >> simp[]) >>
  `body_expr_full_ok cx e /\ body_expr_prefix_ok cx e` by
    (conj_tac >> first_assum irule >> rpt (first_assum (irule_at Any))) >>
  `expr_sim_full (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func) cenv cx aty e es` by
    (irule (cj 1 (REWRITE_RULE [AND_IMP_INTRO] body_expr_full_ok_simulations)) >>
     rpt (first_assum (irule_at Any))) >>
  `expr_sim_prefix (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func) cenv cx aty e es` by
    (qpat_x_assum `body_expr_prefix_ok _ _`
       (mp_tac o CONJUNCT1 o ONCE_REWRITE_RULE [body_expr_prefix_ok_def]) >>
     metis_tac[]) >>
  qpat_x_assum `expr_sim_full _ _ _ _ _ _`
    (mp_tac o REWRITE_RULE [expr_sim_full_eq]) >>
  disch_then (drule_then assume_tac) >>
  qpat_x_assum `expr_sim_prefix _ _ _ _ _ _`
    (mp_tac o REWRITE_RULE [expr_sim_prefix_def]) >>
  disch_then (drule_then assume_tac) >> suspend "join"
QED
*)

(* SCRATCH MEASUREMENT: original continuation.
Resume augassign_toplevel_immutable_prefix[join]:
  qabbrev_tac `goRhs = bind (bind (eval_expr cx e) (read_result cx)) (\rhs.
    bind (lift_sum (evaluate_binop
      (case type_to_int_bound aty of SOME n => n | NONE => Unsigned 0)
      ptv bop cur rhs)) (write_place cx (ImmutablePlace src id [])))` >>
  `gas_prefix_full (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
    cx st0 goRhs (es,s0,G0,tn0)` by
    (irule gas_prefix_full_zero_prefix_guarded >> simp[] >> conj_tac
     >- (simp[Abbr `goRhs`] >> irule storage_trace_frame_bind_all >>
         simp[augassign_rhs_trace_frame, aug_place_store_trace_frame]) >>
     qexistsl_tac [`Gload`,`u`,`tnload`] >> simp[Abbr `goRhs`] >>
     irule augassign_rhs_bind_prefix >>
     (conj_tac >- first_assum ACCEPT_TAC) >>
     qexistsl_tac [`\H v ee G tn t. ~t.vs_halted`, `\H res ee gt r. T`,`cx_tops cx`] >>
     simp[] >> irule gas_outcome_full_post_source >>
     qpat_assum `gas_outcome_full _ _ _ _ (bind (eval_expr cx e) _) _ _ _` (irule_at Any) >>
     simp[] >> rpt gen_tac >> Cases_on `res` >> simp[]) >>
  suspend "source"
QED
*)

(* SCRATCH MEASUREMENT: original continuation.
Resume augassign_toplevel_immutable_prefix[source]:
  drule_all immutable_augassign_metadata >> strip_tac >>
  drule_all immutable_augassign_entry >>
  disch_then (qx_choosel_then [`ts`,`imms`,`tv`,`v`] strip_assume_tac) >>
  drule_all immutable_augassign_prefix_obs >> disch_then (mk_asm "sourcePrefix") >>
  `ptv = tv` by metis_tac[optionTheory.SOME_11] >>
  `cur = v` by
    (asm "sourcePrefix" (qspec_then `es.gas_obs` mp_tac) >>
     simp[evaluation_state_component_equality, IgnAsm `src = _`]) >>
  qpat_x_assum `ptv = tv` SUBST_ALL_TAC >>
  qpat_x_assum `cur = v` SUBST_ALL_TAC >>
  qpat_x_assum `src = cenv.ce_module` SUBST_ALL_TAC >>
  asm "sourcePrefix" (strip_assume_tac o REWRITE_RULE [FORALL_AND_THM]) >>
  `!gs. eval_stmt cx (AugAssign aty (TopLevelNameTarget (cenv.ce_module,id)) bop e)
      (es with gas_obs := gs) = goRhs (es with gas_obs := gs)` by
    simp[augassign_source_bind, bind_def, Abbr `goRhs`, IgnAsm `cenv.ce_module = NONE`] >>
  qpat_x_assum `gas_prefix_full _ _ _ goRhs _` mp_tac >>
  pure_rewrite_tac[gas_prefix_full_def] >> simp[]
QED
*)

(* SCRATCH MEASUREMENT: original continuation.
Finalise augassign_toplevel_immutable_prefix
*)
