(* Fold the completed constructor reads at their observed snapshot cuts. *)
Theory createCtorSavedRowsMods
Ancestors
  createCtorSavedRows createExprSizeExitDefsMods
  createCtorSavedSimpleMods createCtorSavedConsMods bodyFullExtCallPosList
  bodyStorageCases exprSimWordArgs exprLoweringProps vyperStorageTrace
  vyperStorageFootprint vyperState list rich_list
  createCtorRowCutsMods createCtorRowSuffixFoldMods
  createCtorRowCompletedHeadMods createCtorRowPostAdvanceMods

Theorem ctor_rows_post_INL_mods[local]:
  extcall_positional_post_mods mods p DF lo d ctx func ce cx env kw xs svs
    sa sb es s g h H (INL vs : value list + 'a) ee G tn t <=>
  extcall_positional_post_mods mods p DF lo d ctx func ce cx env kw xs svs
    sa sb es s g h H (INL vs : value list + exception) ee G tn t
Proof
  simp[extcall_positional_post_mods_def]
QED

Theorem ctor_rows_fold_mods[local]:
  0 < LENGTH args /\ J 0 G0 tn0 /\
  LENGTH svs = LENGTH args /\ LENGTH vs = LENGTH args /\
  contract_inv mods exps ctx ce cx /\
  module_body_inv mods src tops ce cx /\ (!K. dead_lo_ok_mods K (DF K) lo ce cx) /\
  EVERY (source_body_call_supported cx)
    (int_calls_exprs args) /\
  (!i. i < LENGTH args /\ ~exprs_can_mutate ce (DROP (SUC i) args) ==>
    (E (LENGTH args)).immutables = (E (SUC i)).immutables /\
    !tr. get_storage cx (E (LENGTH args)) tr = get_storage cx (E (SUC i)) tr) /\
  (?H. valid_horizon cx st0 H (E (LENGTH args)).storage_trace) /\
  (!i. i <= LENGTH args ==>
    eval_exprs cx (DROP i args) (E i) = (INL (DROP i vs), E (LENGTH args))) /\
  (!i K. i < LENGTH args /\ valid_horizon cx st0 K (E (SUC i)).storage_trace ==>
    valid_horizon cx st0 K (E i).storage_trace) /\
  (!i. i < LENGTH args ==> local_ptrs_reserved ce (C i) /\
    ci_mono (C i) (C (SUC i)) /\ (St (SUC i)).vs_labels = (St i).vs_labels) /\
  (!i g h. J i g h ==>
    !K. valid_horizon cx st0 K (E i).storage_trace ==>
      stmt_state_rel K ctx func ce cx (E i) (St i)) /\
  (!i. i < LENGTH args ==> !g h. J i g h ==>
    expr_body_pre_mods mods ce cx env (EL i args) (E i) /\
    ?g' h'. !K. valid_horizon cx st0 K (E (SUC i)).storage_trace ==>
      extcall_positional_post_mods mods T DF lo d ctx func ce cx env
        (DROP (SUC i) args) [EL i args] [EL i svs] (C i) (C (SUC i))
        (E i) (St i) g h K (INL [EL i vs] : value list + exception) (E (SUC i)) g' h' (St (SUC i))) /\
  (!i g h g' h'. i < LENGTH args /\
    (?K. valid_horizon cx st0 K (E (SUC i)).storage_trace) /\
    (!K. valid_horizon cx st0 K (E (SUC i)).storage_trace ==>
      extcall_positional_post_mods mods T DF lo d ctx func ce cx env
        (DROP (SUC i) args) [EL i args] [EL i svs] (C i) (C (SUC i))
        (E i) (St i) g h K (INL [EL i vs] : value list + exception) (E (SUC i)) g' h' (St (SUC i))) ==>
    J (SUC i) g' h') ==>
  ?G tn. !K. valid_horizon cx st0 K (E (LENGTH args)).storage_trace ==>
    extcall_positional_post_mods mods T DF lo d ctx func ce cx env [] args svs
      (C 0) (C (LENGTH args)) (E 0) (St 0) G0 tn0 K (INL vs : value list + exception)
      (E (LENGTH args)) G tn (St (LENGTH args))
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  `!i. i < LENGTH args ==> !g h. J i g h ==>
    ?G tn. !K. valid_horizon cx st0 K (E (LENGTH args)).storage_trace ==>
      extcall_positional_post_mods mods T DF lo d ctx func ce cx env
        [] (DROP i args) (DROP i svs) (C i) (C (LENGTH args)) (E i) (St i) g h K
        (INL (DROP i vs) : value list + exception) (E (LENGTH args)) G tn (St (LENGTH args))`
    suffices_by (disch_then (qspec_then `0` mp_tac) >> simp[]) >>
  ho_match_mp_tac ctor_rows_suffix_fold_by_step_mods >> simp[] >>
  rpt conj_tac
  >- (rpt strip_tac >>
      qpat_assum `?H. valid_horizon _ _ H _` (qx_choose_then `H` assume_tac) >>
      qexists_tac `H` >>
      `SUC i <= LENGTH args` by decide_tac >>
      qpat_assum `!j. j <= LENGTH args ==> _` (drule_then assume_tac) >>
      drule_all_then ACCEPT_TAC ctor_rows_horizon_mods)
  >- (rpt strip_tac >>
      qpat_assum `!i. _ ==> !g h. J i g h ==> _`
        (qspec_then `i` (drule_then (qspecl_then [`g`,`h`] (drule_then (ACCEPT_TAC o CONJUNCT1))))))
  >- first_assum ACCEPT_TAC
  >> rpt strip_tac >>
  `i < LENGTH args /\ SUC i <= LENGTH args` by decide_tac >>
  `!j. j < LENGTH args ==> ci_mono (C j) (C (SUC j)) /\
      (St (SUC j)).vs_labels = (St j).vs_labels` by simp[] >>
  drule_then (qspec_then `SUC i` (drule_then strip_assume_tac)) ctor_rows_suffix_cuts_mods >>
  irule ctor_saved_rows_cons_mods >>
  qpat_assum `contract_inv _ _ _ _ _` (irule_at Any) >>
  qpat_assum `module_body_inv _ _ _ _ _` (irule_at Any) >>
  `EVERY (source_body_call_supported cx) (int_calls_exprs (DROP (SUC i) args))` by
    (irule int_calls_exprs_DROP_EVERY >> first_assum ACCEPT_TAC) >>
  qexistsl [`b`,`St (SUC i)`,`st0`,`(E (LENGTH args)).gas_obs`,
            `(E (SUC i)).gas_obs`,`E (SUC i)`,`C (SUC i)`,`a`] >>
  simp[ctor_rows_post_INL_mods] >>
  qpat_assum `!i g h. J i g h ==> _`
    (qspecl_then [`i`,`g`,`h`] (drule_then ACCEPT_TAC))
QED

Theorem ctor_saved_rows_at_last_cut_mods:
  0 < LENGTH args /\ LENGTH svs = LENGTH args /\ LENGTH vs = LENGTH args /\
  contract_inv mods exps ctx ce cx /\
  module_body_inv mods src tops ce cx /\ (!K. dead_lo_ok_mods K (DF K) lo ce cx) /\
  EVERY (source_body_call_supported cx)
    (int_calls_exprs args) /\
  (!i. i < LENGTH args /\ ~exprs_can_mutate ce (DROP (SUC i) args) ==>
    (E (LENGTH args)).immutables = (E (SUC i)).immutables /\
    !tr. get_storage cx (E (LENGTH args)) tr = get_storage cx (E (SUC i)) tr) /\
  (?H. valid_horizon cx st0 H (E (LENGTH args)).storage_trace) /\
  (!i. i < LENGTH args ==>
    compile_expr ce (expr_type (EL i args)) (EL i args) (C i) = (V i,M i) /\
    compile_snapshot_vv ce (exprs_can_mutate ce (DROP (SUC i) args))
      (ext_call_arg_value (lowered_value_type ce (EL i args)) (V i)) (M i) =
      (EL i svs,C (SUC i)) /\
    vyperState$bind (eval_expr cx (EL i args)) (read_result cx) (E i) =
      (INL (EL i vs),E (SUC i)) /\
    (expr_sim_inv_mods mods ce cx env (E i) ==> expr_body_pre_mods mods ce cx env (EL i args) (E i)) /\
    local_ptrs_reserved ce (C i) /\
    (!x sz. ce.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at (C i) x) /\
    (!x sz. ce.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at (C i) x) /\
    ci_mono (C i) (C (SUC i)) /\ (St (SUC i)).vs_labels = (St i).vs_labels /\
    ~(St (SUC i)).vs_halted /\ (St (SUC i)).vs_current_bb = (C (SUC i)).cs_current_bb /\
    (St (SUC i)).vs_inst_idx = LENGTH (C (SUC i)).cs_current_insts) /\
  expr_sim_inv_mods mods ce cx env (E 0) /\ return_buf_frame d ce (C 0) (St 0) /\
  alloca_history func (St 0) /\ ~(St 0).vs_halted /\
  (St 0).vs_current_bb = (C 0).cs_current_bb /\
  (St 0).vs_inst_idx = LENGTH (C 0).cs_current_insts /\
  (!K. valid_horizon cx st0 K (E 0).storage_trace ==>
    stmt_state_rel K ctx func ce cx (E 0) (St 0) /\
    storage_well_formed_on cx (E 0) (FST K) /\
    ghost_inv_at_mods (DF K) lo d ce cx (E 0) G0 tn0 (St 0)) /\
  (!i g h. i < LENGTH args /\ expr_sim_inv_mods mods ce cx env (E i) /\
    return_buf_frame d ce (C i) (St i) /\ alloca_history func (St i) /\
    ~(St i).vs_halted /\ (St i).vs_current_bb = (C i).cs_current_bb /\
    (St i).vs_inst_idx = LENGTH (C i).cs_current_insts /\
    (!K. valid_horizon cx st0 K (E i).storage_trace ==>
      stmt_state_rel K ctx func ce cx (E i) (St i) /\
      storage_well_formed_on cx (E i) (FST K) /\
      ghost_inv_at_mods (DF K) lo d ce cx (E i) g h (St i)) ==>
    (is_word_type (lowered_value_type ce (EL i args)) ==>
      ?g' h'. !K op. valid_horizon cx st0 K (E (SUC i)).storage_trace /\
        lower_value compile_expr ce (expr_type (EL i args)) (EL i args) (C i) =
          (op,C (SUC i)) ==>
        expr_sim_full_post_mods (DF,lo,d,ctx,func) ce cx (EL i args)
          (E i,C i,C (SUC i),St i,op,g,h) K (INL (EL i vs) : value + exception) (E (SUC i)) g' h' (St (SUC i))) /\
    (~is_word_type (lowered_value_type ce (EL i args)) /\
     ~exprs_can_mutate ce (DROP (SUC i) args) ==>
      ?g' h'. !K. valid_horizon cx st0 K (E (SUC i)).storage_trace ==>
        ?raw. eval_expr cx (EL i args) (E i) = (INL raw,E (SUC i)) /\
          vv_post_mods K ctx func ce cx (EL i args) (E i) (C i) (M i) (St i)
            (E (SUC i)) raw (V i) (St (SUC i)) /\
          vv_store_bound cx (post_value_type ce (EL i args)) (lowered_value_type ce (EL i args))
            (E (SUC i)) raw (V i) (St (SUC i)) /\
          ptr_vv_ok cx (post_value_type ce (EL i args)) raw (V i) (E (SUC i)) g' h' (St (SUC i)) /\
          alloca_history func (St (SUC i)) /\ (St i).vs_alloca_next <= (St (SUC i)).vs_alloca_next /\
          ghost_inv_at_mods (DF K) lo d ce cx (E (SUC i)) g' h' (St (SUC i)) /\
          ghost_kept_at lo ce (E i) (C i) g h (St i) g' h' /\
          (!tag op. V i = StackValue tag op /\ ~is_word_type (post_value_type ce (EL i args)) ==>
            ptr_buf_ok ce (EL i args) op g' (St (SUC i))) /\
          (!tag p. V i = LocatedValue tag p /\ p.ptr_location = LocMemory ==>
            ptr_buf_ok ce (EL i args) p.ptr_operand g' (St (SUC i))) /\
          (ce.ce_is_ctor /\ vv_location (V i) = SOME LocCode ==>
            ?val. read_result cx raw (E (SUC i)) = (INL val,E (SUC i)) /\
              !rt w. evaluate_type (get_tenv cx) (post_value_type ce (EL i args)) = SOME rt /\
                eval_operand (vv_operand (V i)) (St (SUC i)) = SOME w ==>
                w2n w + type_memory_size rt <= lo /\
                (!mem. mem_agree_outside h'.t_mem (St (SUC i)).vs_memory mem ==>
                       val_in_memory rt val (w2n w) mem))) /\
    (~is_word_type (lowered_value_type ce (EL i args)) /\
     exprs_can_mutate ce (DROP (SUC i) args) ==>
      ?g' h'. !K. valid_horizon cx st0 K (E (SUC i)).storage_trace ==>
        extcall_positional_post_mods mods T DF lo d ctx func ce cx env
          (DROP (SUC i) args) [EL i args] [EL i svs] (C i) (C (SUC i))
          (E i) (St i) g h K (INL [EL i vs] : value list + exception) (E (SUC i)) g' h' (St (SUC i)))) ==>
  ?G tn. !K. valid_horizon cx st0 K (E (LENGTH args)).storage_trace ==>
    extcall_positional_post_mods mods T DF lo d ctx func ce cx env [] args svs
      (C 0) (C (LENGTH args)) (E 0) (St 0) G0 tn0 K (INL vs : value list + exception)
      (E (LENGTH args)) G tn (St (LENGTH args))
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  qabbrev_tac `J = \i g h. expr_sim_inv_mods mods ce cx env (E i) /\
    return_buf_frame d ce (C i) (St i) /\ alloca_history func (St i) /\
    ~(St i).vs_halted /\ (St i).vs_current_bb = (C i).cs_current_bb /\
    (St i).vs_inst_idx = LENGTH (C i).cs_current_insts /\
    (!K. valid_horizon cx st0 K (E i).storage_trace ==>
      stmt_state_rel K ctx func ce cx (E i) (St i) /\
      storage_well_formed_on cx (E i) (FST K) /\
      ghost_inv_at_mods (DF K) lo d ce cx (E i) g h (St i))` >>
  irule ctor_rows_fold_mods >>
  qpat_assum `contract_inv _ _ _ _ _` (irule_at Any) >>
  qpat_assum `module_body_inv _ _ _ _ _` (irule_at Any) >>
  simp[] >>
  qpat_assum `?H. valid_horizon _ _ H _` (qx_choose_then `H` assume_tac) >>
  qexistsl [`J`,`H`] >> simp[] >> rpt conj_tac
  >- (rpt strip_tac >>
      qpat_assum `!i. i < LENGTH args ==> compile_expr _ _ _ _ = _ /\ _`
        (qspec_then `i` (drule_then strip_assume_tac)) >>
      drule_all_then ACCEPT_TAC ctor_rows_read_horizon_mods)
  >- (ho_match_mp_tac ctor_rows_source_mods >> simp[])
  >- (rpt gen_tac >> disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
      drule_all_then mp_tac ctor_row_post_advance_mods >> simp[Abbr `J`])
  >- simp[Abbr `J`]
  >- (rpt gen_tac >> disch_tac >> rpt gen_tac >> disch_tac >>
      qpat_assum `!i. i < LENGTH args ==> compile_expr _ _ _ _ = _ /\ _`
        (qspec_then `i` (drule_then (MAP_EVERY assume_tac o CONJUNCTS))) >>
      qpat_assum `!i g h. _ ==> _` (qspecl_then [`i`,`g`,`h`] mp_tac) >>
      (impl_tac >- fs[Abbr `J`]) >>
      disch_then (MAP_EVERY assume_tac o CONJUNCTS) >> fs[Abbr `J`] >>
      irule ctor_row_completed_head_mods >>
      qpat_assum `compile_expr _ _ _ _ = _` (irule_at Any) >>
      qpat_assum `contract_inv _ _ _ _ _` (irule_at Any) >>
      qpat_assum `module_body_inv _ _ _ _ _` (irule_at Any) >> simp[])
  >> simp[Abbr `J`]
QED
