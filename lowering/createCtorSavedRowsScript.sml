(* Fold the completed constructor reads at their observed snapshot cuts. *)
Theory createCtorSavedRows
Ancestors
  createCtorSavedSimple createCtorSavedCons bodyFullExtCallPosList
  bodyStorageCases exprSimWordArgs exprLoweringProps vyperStorageTrace
  vyperStorageFootprint vyperState list rich_list

Theorem ctor_rows_source[local]:
  LENGTH vs = LENGTH args /\
  (!i. i < LENGTH args ==>
    vyperState$bind (eval_expr cx (EL i args)) (read_result cx) (E i) =
      (INL (EL i vs), E (SUC i))) ==>
  !i. i <= LENGTH args ==>
    eval_exprs cx (DROP i args) (E i) = (INL (DROP i vs), E (LENGTH args))
Proof
  strip_tac >> gen_tac >> measureInduct_on `LENGTH args - i` >> strip_tac >>
  Cases_on `i = LENGTH args` >- fs[eval_exprs_nil] >>
  `i < LENGTH args /\ i < LENGTH vs` by decide_tac >>
  first_x_assum (qspec_then `SUC i` mp_tac) >>
  (impl_tac >- decide_tac) >>
  (impl_tac >- decide_tac) >> strip_tac >>
  imp_res_tac DROP_CONS_EL >>
  simp[eval_exprs_cons_action, bind_def, return_def]
QED

Theorem ctor_rows_read_horizon[local]:
  vyperState$bind (eval_expr cx e) (read_result cx) es = (res,ee) /\
  valid_horizon cx st0 H ee.storage_trace ==> valid_horizon cx st0 H es.storage_trace
Proof
  strip_tac >>
  `storage_trace_frame (vyperState$bind (eval_expr cx e) (read_result cx))` by
    simp[storage_trace_frame_bind_all, cj 5 evaluate_storage_trace_frame,
         storage_trace_frame_read_result] >>
  drule_all_then ACCEPT_TAC valid_horizon_frame
QED

Theorem ctor_rows_horizon[local]:
  eval_exprs cx xs es = (res,ee) /\ valid_horizon cx st0 H ee.storage_trace ==>
  valid_horizon cx st0 H es.storage_trace
Proof
  metis_tac[valid_horizon_frame, cj 6 evaluate_storage_trace_frame]
QED

Theorem ctor_rows_suffix_cuts[local]:
  (!i. i < n ==> ci_mono (C i) (C (SUC i)) /\ (St (SUC i)).vs_labels = (St i).vs_labels) ==>
  !i. i <= n ==> ci_mono (C i) (C n) /\ (St n).vs_labels = (St i).vs_labels
Proof
  strip_tac >> gen_tac >> measureInduct_on `n - i` >> strip_tac >>
  Cases_on `i = n` >- simp[ci_mono_refl] >>
  `i < n` by decide_tac >>
  first_x_assum (qspec_then `SUC i` mp_tac) >>
  (impl_tac >- decide_tac) >>
  (impl_tac >- decide_tac) >> strip_tac >>
  qpat_x_assum `!j. j < n ==> _` drule >> metis_tac[ci_mono_trans]
QED

(* Boundary recursion only needs a successful singleton at the next cut.
   The public theorem below obtains it in the scalar and retained cases. *)
Theorem ctor_rows_fold[local]:
  0 < LENGTH args /\ J 0 G0 tn0 /\
  LENGTH svs = LENGTH args /\ LENGTH vs = LENGTH args /\
  body_inv tops ctx ce cx /\ (!K. dead_lo_ok K (DF K) lo ce cx) /\
  EVERY (\c. FST c = NONE /\ IS_SOME (supported_function_decl tops c Internal))
    (int_calls_exprs args) /\ (?H. valid_horizon cx st0 H (E (LENGTH args)).storage_trace) /\
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
    expr_body_pre ce cx env (EL i args) (E i) /\
    ?g' h'. !K. valid_horizon cx st0 K (E (SUC i)).storage_trace ==>
      extcall_positional_post T DF lo d ctx func ce cx env
        (DROP (SUC i) args) [EL i args] [EL i svs] (C i) (C (SUC i))
        (E i) (St i) g h K (INL [EL i vs] : value list + exception) (E (SUC i)) g' h' (St (SUC i))) /\
  (!i g h g' h'. i < LENGTH args /\
    (?K. valid_horizon cx st0 K (E (SUC i)).storage_trace) /\
    (!K. valid_horizon cx st0 K (E (SUC i)).storage_trace ==>
      extcall_positional_post T DF lo d ctx func ce cx env
        (DROP (SUC i) args) [EL i args] [EL i svs] (C i) (C (SUC i))
        (E i) (St i) g h K (INL [EL i vs] : value list + exception) (E (SUC i)) g' h' (St (SUC i))) ==>
    J (SUC i) g' h') ==>
  ?G tn. !K. valid_horizon cx st0 K (E (LENGTH args)).storage_trace ==>
    extcall_positional_post T DF lo d ctx func ce cx env [] args svs
      (C 0) (C (LENGTH args)) (E 0) (St 0) G0 tn0 K (INL vs : value list + exception)
      (E (LENGTH args)) G tn (St (LENGTH args))
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  `!i. i <= LENGTH args ==> i < LENGTH args ==> !g h. J i g h ==>
    ?G tn. !K. valid_horizon cx st0 K (E (LENGTH args)).storage_trace ==>
      extcall_positional_post T DF lo d ctx func ce cx env [] (DROP i args) (DROP i svs)
        (C i) (C (LENGTH args)) (E i) (St i) g h K
        (INL (DROP i vs) : value list + exception) (E (LENGTH args)) G tn (St (LENGTH args))` suffices_by
    (disch_then (qspec_then `0` mp_tac) >> simp[] >>
     disch_then (qspecl_then [`G0`,`tn0`] mp_tac) >> asm_simp_tac bool_ss []) >>
  `!j. j < LENGTH args ==> ci_mono (C j) (C (SUC j)) /\
     (St (SUC j)).vs_labels = (St j).vs_labels` by simp[] >>
  drule_then assume_tac ctor_rows_suffix_cuts >>
  gen_tac >> measureInduct_on `LENGTH args - i` >>
  rpt strip_tac >>
  qpat_assum `!i. _ ==> !g h. _ ==> expr_body_pre _ _ _ _ _ /\ _`
    (qspec_then `i` (drule_then (qspecl_then [`g`,`h`] (drule_then
      (CONJUNCTS_THEN2 assume_tac (qx_choosel_then [`g1`,`h1`] assume_tac)))))) >>
  `i < LENGTH vs /\ i < LENGTH svs` by fs[] >>
  `DROP i args = EL i args :: DROP (SUC i) args` by simp[DROP_CONS_EL] >>
  `DROP i vs = EL i vs :: DROP (SUC i) vs` by simp[DROP_CONS_EL] >>
  `DROP i svs = EL i svs :: DROP (SUC i) svs` by simp[DROP_CONS_EL] >>
  Cases_on `SUC i = LENGTH args`
  >- (`DROP (LENGTH args) vs = [] /\ DROP (LENGTH args) svs = []` by
        simp[DROP_LENGTH_NIL_rwt] >> qexistsl_tac [`g1`,`h1`] >> fs[DROP_LENGTH_TOO_LONG]) >>
  `SUC i < LENGTH args` by decide_tac >>
  `SUC i <= LENGTH args` by decide_tac >>
  `eval_exprs cx (DROP (SUC i) args) (E (SUC i)) =
    (INL (DROP (SUC i) vs), E (LENGTH args))` by simp[] >>
  `!K. valid_horizon cx st0 K (E (LENGTH args)).storage_trace ==>
       valid_horizon cx st0 K (E (SUC i)).storage_trace` by
    (rpt strip_tac >> drule_all_then ACCEPT_TAC ctor_rows_horizon) >>
  `J (SUC i) g1 h1` by
    (first_x_assum irule >> reverse conj_tac >- metis_tac[] >>
     qexistsl_tac [`g`,`h`] >> first_assum ACCEPT_TAC) >>
  qpat_x_assum `!j. LENGTH args - j < LENGTH args - i ==> _`
    (qspec_then `SUC i` mp_tac) >>
  (impl_tac >- decide_tac) >> simp[] >>
  disch_then (qspecl_then [`g1`,`h1`] (drule_then
    (qx_choosel_then [`G`,`tn`] assume_tac))) >>
  qexistsl_tac [`G`,`tn`] >> simp[] >> rpt strip_tac >>
  irule ctor_saved_rows_cons >>
  rpt conj_tac
  >- first_assum ACCEPT_TAC
  >- simp[]
  >- (qexists_tac `tops` >> simp[] >> irule int_calls_exprs_DROP_EVERY >> simp[])
  >- (qexistsl_tac [`g1`,`C (SUC i)`,`E (SUC i)`,
        `(E (SUC i)).gas_obs`,`(E (LENGTH args)).gas_obs`,`st0`,`St (SUC i)`,`h1`] >>
      simp[extcall_positional_post_INL] >> rpt conj_tac
      >- (qpat_assum `!i g h. J i g h ==> _`
            (qspecl_then [`i`,`g`,`h`] (drule_then ACCEPT_TAC)))
      >> `i <= LENGTH args` by decide_tac >> simp[])
  >> first_assum ACCEPT_TAC
QED

Theorem ctor_saved_rows_at_last_cut:
  0 < LENGTH args /\ LENGTH svs = LENGTH args /\ LENGTH vs = LENGTH args /\
  body_inv tops ctx ce cx /\ (!K. dead_lo_ok K (DF K) lo ce cx) /\
  EVERY (\c. FST c = NONE /\ IS_SOME (supported_function_decl tops c Internal))
    (int_calls_exprs args) /\ (?H. valid_horizon cx st0 H (E (LENGTH args)).storage_trace) /\
  (!i. i < LENGTH args ==>
    compile_expr ce (expr_type (EL i args)) (EL i args) (C i) = (V i,M i) /\
    compile_snapshot_vv ce (exprs_can_mutate ce (DROP (SUC i) args))
      (ext_call_arg_value (lowered_value_type ce (EL i args)) (V i)) (M i) =
      (EL i svs,C (SUC i)) /\
    vyperState$bind (eval_expr cx (EL i args)) (read_result cx) (E i) =
      (INL (EL i vs),E (SUC i)) /\
    (expr_sim_inv ce cx env (E i) ==> expr_body_pre ce cx env (EL i args) (E i)) /\
    local_ptrs_reserved ce (C i) /\
    (!x sz. ce.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at (C i) x) /\
    (!x sz. ce.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at (C i) x) /\
    ci_mono (C i) (C (SUC i)) /\ (St (SUC i)).vs_labels = (St i).vs_labels /\
    ~(St (SUC i)).vs_halted /\ (St (SUC i)).vs_current_bb = (C (SUC i)).cs_current_bb /\
    (St (SUC i)).vs_inst_idx = LENGTH (C (SUC i)).cs_current_insts) /\
  expr_sim_inv ce cx env (E 0) /\ return_buf_frame d ce (C 0) (St 0) /\
  alloca_history func (St 0) /\ ~(St 0).vs_halted /\
  (St 0).vs_current_bb = (C 0).cs_current_bb /\
  (St 0).vs_inst_idx = LENGTH (C 0).cs_current_insts /\
  (!K. valid_horizon cx st0 K (E 0).storage_trace ==>
    stmt_state_rel K ctx func ce cx (E 0) (St 0) /\
    storage_well_formed_on cx (E 0) (FST K) /\
    ghost_inv_at (DF K) lo d ce cx (E 0) G0 tn0 (St 0)) /\
  (!i g h. i < LENGTH args /\ expr_sim_inv ce cx env (E i) /\
    return_buf_frame d ce (C i) (St i) /\ alloca_history func (St i) /\
    ~(St i).vs_halted /\ (St i).vs_current_bb = (C i).cs_current_bb /\
    (St i).vs_inst_idx = LENGTH (C i).cs_current_insts /\
    (!K. valid_horizon cx st0 K (E i).storage_trace ==>
      stmt_state_rel K ctx func ce cx (E i) (St i) /\
      storage_well_formed_on cx (E i) (FST K) /\
      ghost_inv_at (DF K) lo d ce cx (E i) g h (St i)) ==>
    (is_word_type (lowered_value_type ce (EL i args)) ==>
      ?g' h'. !K op. valid_horizon cx st0 K (E (SUC i)).storage_trace /\
        lower_value compile_expr ce (expr_type (EL i args)) (EL i args) (C i) =
          (op,C (SUC i)) ==>
        expr_sim_full_post (DF,lo,d,ctx,func) ce cx (EL i args)
          (E i,C i,C (SUC i),St i,op,g,h) K (INL (EL i vs) : value + exception) (E (SUC i)) g' h' (St (SUC i))) /\
    (~is_word_type (lowered_value_type ce (EL i args)) /\
     ~exprs_can_mutate ce (DROP (SUC i) args) ==>
      ?g' h'. !K. valid_horizon cx st0 K (E (SUC i)).storage_trace ==>
        ?raw. eval_expr cx (EL i args) (E i) = (INL raw,E (SUC i)) /\
          vv_post K ctx func ce cx (EL i args) (E i) (C i) (M i) (St i)
            (E (SUC i)) raw (V i) (St (SUC i)) /\
          vv_store_bound cx (post_value_type ce (EL i args)) (lowered_value_type ce (EL i args))
            (E (SUC i)) raw (V i) (St (SUC i)) /\
          ptr_vv_ok cx (post_value_type ce (EL i args)) raw (V i) (E (SUC i)) g' h' (St (SUC i)) /\
          alloca_history func (St (SUC i)) /\ (St i).vs_alloca_next <= (St (SUC i)).vs_alloca_next /\
          ghost_inv_at (DF K) lo d ce cx (E (SUC i)) g' h' (St (SUC i)) /\
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
        extcall_positional_post T DF lo d ctx func ce cx env
          (DROP (SUC i) args) [EL i args] [EL i svs] (C i) (C (SUC i))
          (E i) (St i) g h K (INL [EL i vs] : value list + exception) (E (SUC i)) g' h' (St (SUC i)))) ==>
  ?G tn. !K. valid_horizon cx st0 K (E (LENGTH args)).storage_trace ==>
    extcall_positional_post T DF lo d ctx func ce cx env [] args svs
      (C 0) (C (LENGTH args)) (E 0) (St 0) G0 tn0 K (INL vs : value list + exception)
      (E (LENGTH args)) G tn (St (LENGTH args))
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  qabbrev_tac `J = \i g h. expr_sim_inv ce cx env (E i) /\
    return_buf_frame d ce (C i) (St i) /\ alloca_history func (St i) /\
    ~(St i).vs_halted /\ (St i).vs_current_bb = (C i).cs_current_bb /\
    (St i).vs_inst_idx = LENGTH (C i).cs_current_insts /\
    (!K. valid_horizon cx st0 K (E i).storage_trace ==>
      stmt_state_rel K ctx func ce cx (E i) (St i) /\
      storage_well_formed_on cx (E i) (FST K) /\
      ghost_inv_at (DF K) lo d ce cx (E i) g h (St i))` >>
  irule ctor_rows_fold >> simp[] >> rpt conj_tac
  >- (rpt strip_tac >>
      qpat_assum `!i. i < LENGTH args ==> compile_expr _ _ _ _ = _ /\ _`
        (qspec_then `i` (drule_then strip_assume_tac)) >>
      drule_all_then ACCEPT_TAC ctor_rows_read_horizon)
  >- (ho_match_mp_tac ctor_rows_source >> simp[])
  >- (qexists_tac `J` >> simp[Abbr `J`] >> conj_tac
      >- suspend "advance"
      >> suspend "singleton")
  >> qexists_tac `tops` >> simp[]
QED

Resume ctor_saved_rows_at_last_cut[advance]:
  rpt gen_tac >> strip_tac >>
  qpat_assum `!K. _ ==> extcall_positional_post _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ K _ _ _ _ _`
    (drule_then (MAP_EVERY assume_tac o CONJUNCTS o
       SIMP_RULE (srw_ss()) [extcall_positional_post_def])) >>
  simp[] >> qx_gen_tac `K1` >> disch_tac >>
  qpat_assum `!K. _ ==> extcall_positional_post _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ K _ _ _ _ _`
    (qspec_then `K1` (drule_then (MAP_EVERY assume_tac o CONJUNCTS o
       SIMP_RULE (srw_ss()) [extcall_positional_post_def]))) >> simp[]
QED

Resume ctor_saved_rows_at_last_cut[singleton]:
  rpt gen_tac >> disch_tac >> rpt gen_tac >> disch_then strip_assume_tac >>
  qpat_assum `!i. i < LENGTH args ==> compile_expr _ _ _ _ = _ /\ _`
    (qspec_then `i` (drule_then (MAP_EVERY assume_tac o CONJUNCTS))) >>
  qpat_x_assum `!i g h. _ ==> _`
    (qspecl_then [`i`,`g`,`h`] mp_tac) >>
  asm_simp_tac bool_ss [] >>
  Cases_on `is_word_type (lowered_value_type ce (EL i args))` >>
  Cases_on `exprs_can_mutate ce (DROP (SUC i) args)` >>
  simp[] >> disch_then (qx_choosel_then [`g1`,`h1`] assume_tac) >>
  qexistsl_tac [`g1`,`h1`] >> asm_simp_tac bool_ss [] >>
  rpt strip_tac >> irule ctor_saved_head_simple >>
  qpat_assum `compile_expr _ _ _ _ = _` (irule_at Any) >>
  simp[] >> qexistsl_tac [`tops`,`(E i).gas_obs`] >> simp[] >>
  TRY (qpat_assum `!K op. _ ==> expr_sim_full_post _ _ _ _ _ K _ _ _ _ _`
         (qspec_then `K'` mp_tac) >> simp[] >> disch_then ACCEPT_TAC) >>
  drule_all_then assume_tac ctor_rows_read_horizon >>
  qpat_assum `!K. valid_horizon cx st0 K (E i).storage_trace ==> _`
     (drule_then (MAP_EVERY assume_tac o CONJUNCTS)) >>
  fs[valid_horizon_def]
QED

Finalise ctor_saved_rows_at_last_cut
