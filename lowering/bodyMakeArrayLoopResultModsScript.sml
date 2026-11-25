(* Reassemble the length prefix and traversed slots at the actual final cut. *)
Theory bodyMakeArrayLoopResultMods
Ancestors
  bodyMakeElementsContractMods bodyMakeArrayCompletedMods bodyMemArrayLayout
  exprSimAggregateEncoding exprLoweringProps supportedExprTraverse
  valueEncoding valueEncodingDefs integer_word rich_list list
  vyperAST exprLowering compileEnv context

val _ = Parse.hide "base";

Triviality homogeneous_array_encoding:
  compatible_bound n (LENGTH (args:expr list)) /\ LENGTH vs = LENGTH args /\
  make_elements_prefix_mods base
    (if (case n of Dynamic _ => T | _ => F)
     then [(BaseTV (UintT 256),IntV (&LENGTH args),base,32)] else [])
    (if (case n of Dynamic _ => T | _ => F) then 32 else 0) t tf /\
  (!m. mem_agree_outside tf.t_mem t.vs_memory m ==>
    tuple_in_memory vs (REPLICATE (LENGTH args) tv)
      (base + (if (case n of Dynamic _ => T | _ => F) then 32 else 0)) m) ==>
  !m. mem_agree_outside tf.t_mem t.vs_memory m ==>
    val_in_memory (ArrayTV tv n) (ArrayV (make_array_value tv n vs)) base m
Proof
  strip_tac >> qx_gen_tac `m` >> strip_tac >> irule array_from_dense_memory >>
  Cases_on `n` >> gvs[make_elements_prefix_mods_def] >>
  qpat_assum `LENGTH vs = LENGTH args` (SUBST1_TAC o SYM) >>
  simp[GSYM tuple_in_memory_replicate_elems] >>
  `val_in_memory (BaseTV (UintT 256)) (IntV (&LENGTH args)) base m` by
    (first_assum irule >> first_assum ACCEPT_TAC) >>
  fs[val_in_memory_def,val_to_w256_def,i2w_pos]
QED

Triviality homogeneous_array_frame:
  off <= cap /\
  (!name b k. local_region ce es.scopes sj name b k <=>
              local_region ce es.scopes si name b k) /\
  (!name b k. local_region ce es.scopes si name b k ==>
              mem_bytes_at b k sj.vs_memory = mem_bytes_at b k si.vs_memory) /\
  (!p k. p + k <= base \/ base + off <= p ==>
          mem_bytes_at p k sj.vs_memory = mem_bytes_at p k si.vs_memory) /\
  make_elements_frame_mods ce func base cap sh es sj t ==>
  make_elements_frame_mods ce func base cap sh es si t
Proof
  rewrite_tac[make_elements_frame_mods_def] >> strip_tac >> conj_tac
  >- (qx_genl_tac [`name`,`b`,`k`] >> strip_tac >>
      `local_region ce es.scopes sj name b k` by simp[] >>
      qpat_assum `!name b k. local_region _ _ sj name b k ==> _`
        (drule_then SUBST1_TAC) >>
      qpat_assum `!name b k. local_region _ _ si name b k ==> _`
        (drule_then ACCEPT_TAC)) >>
  qx_genl_tac [`p`,`k`] >> disch_then (map_every assume_tac o CONJUNCTS) >>
  `mem_bytes_at p k t.vs_memory = mem_bytes_at p k sj.vs_memory` by
    (first_assum irule >> rpt conj_tac >> first_assum ACCEPT_TAC) >>
  pop_assum SUBST1_TAC >> first_assum irule >> decide_tac
QED

val array_completion_contract =
  concl (GEN_ALL (INST_TYPE [alpha |-> ``:256``] make_array_completed_mods));

Theorem make_array_loop_result_from_completed_mods:
  ^array_completion_contract /\
  expr_body_pre_mods mods ce cx env (Builtin (ArrayT et n) (MakeArray (SOME et) n) args) es /\
  compatible_bound n (LENGTH args) /\
  evaluate_type (get_tenv cx) (ArrayT et n) = SOME (ArrayTV tv n) /\
  cap = type_memory_bytes ce (ArrayT et n) /\ cap = type_memory_size (ArrayTV tv n) /\
  off = (if (case n of Dynamic _ => T | _ => F) then 32 else 0) /\ off <= cap /\
  ps = (if (case n of Dynamic _ => T | _ => F)
        then [(BaseTV (UintT 256),IntV (&LENGTH args),base,32)] else []) /\
  eval_expr cx (Builtin (ArrayT et n) (MakeArray (SOME et) n) args) (es with gas_obs := gs) =
    (INL (Value (ArrayV (make_array_value tv n vs))),ee) /\
  ci_mono sa sh /\ ci_mono sh sb /\ sa.cs_next_id < sh.cs_next_id /\
  MEM (mk_inst sa.cs_next_id ALLOCA [Lit (n2w cap)] [q]) (fn_insts func) /\
  si.vs_memory = s0.vs_memory /\
  (!name b k. local_region ce es.scopes si name b k <=>
              local_region ce es.scopes s0 name b k) /\
  (!name b k. local_region ce es.scopes sj name b k <=>
              local_region ce es.scopes si name b k) /\
  (!name b k. local_region ce es.scopes si name b k ==>
              mem_bytes_at b k sj.vs_memory = mem_bytes_at b k si.vs_memory) /\
  (!p k. p + k <= base \/ base + off <= p ==>
          mem_bytes_at p k sj.vs_memory = mem_bytes_at p k si.vs_memory) /\
  valid_horizon cx st0 H ee.storage_trace /\
  make_elements_post_mods mods ce cx env DF lo d ctx func st0
    (sa,es,s0,G0,tn0) (sa.cs_next_id,base,cap,q) args (REPLICATE (LENGTH args) tv)
    ps off sh sb es sj H (INL vs) ee gf tf t ==>
  make_slot_child_post_mods DF lo d ctx func ce cx
    (Builtin (ArrayT et n) (MakeArray (SOME et) n) args) es sa sb s0 G0 tn0
    (LocatedValue (ArrayT et n) (mk_ptr (Var q) LocMemory))
    H (INL (Value (ArrayV (make_array_value tv n vs)))) ee gf tf t
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  qhdtm_x_assum `make_elements_post_mods`
    (strip_assume_tac o REWRITE_RULE [make_elements_post_mods_def, sumTheory.INL_11]) >>
  qpat_x_assum `vs = _` (SUBST_ALL_TAC o SYM) >>
  qhdtm_x_assum `make_elements_cut_mods`
    (strip_assume_tac o REWRITE_RULE [make_elements_cut_mods_def]) >>
  `LENGTH vs = LENGTH args` by
    (qpat_assum `LIST_REL value_has_type _ _` (mp_tac o MATCH_MP LIST_REL_LENGTH) >>
     simp[]) >>
  `!m. mem_agree_outside tf.t_mem t.vs_memory m ==>
       val_in_memory (ArrayTV tv n) (ArrayV (make_array_value tv n vs)) base m` by
    (qpat_x_assum `^array_completion_contract` kall_tac >>
     rpt strip_tac >> irule homogeneous_array_encoding >>
     qexistsl [`args`,`t`,`tf`] >>
     qpat_x_assum `off = _` SUBST_ALL_TAC >>
     qpat_x_assum `ps = _` SUBST_ALL_TAC >>
     rpt conj_tac >> first_assum ACCEPT_TAC) >>
  `~expr_has_effect (Builtin (ArrayT et n) (MakeArray (SOME et) n) args) ==>
     make_elements_frame_mods ce func base cap sh es si t` by
    (simp_tac (srw_ss()) [expr_has_effect_def,supported_expr_exists_def,supported_exprs_exists_every] >>
     strip_tac >>
     `~EXISTS expr_has_effect args` by
       (qpat_x_assum `EVERY _ args` mp_tac >> simp[EVERY_MEM,EXISTS_MEM]) >>
     qpat_assum `~EXISTS _ _ ==> make_elements_frame_mods _ _ _ _ _ _ _ _`
       (drule_then assume_tac) >>
     irule homogeneous_array_frame >> qexistsl [`off`,`sj`] >>
     qpat_x_assum `^array_completion_contract` kall_tac >> gs[] >>
     rpt conj_tac >> first_assum ACCEPT_TAC) >>
  qpat_assum `!h. valid_horizon cx st0 h ee.storage_trace ==> _`
    (qspec_then `H` (drule_then strip_assume_tac)) >>
  qabbrev_tac `e = Builtin (ArrayT et n) (MakeArray (SOME et) n) args` >>
  qabbrev_tac `v = ArrayV (make_array_value tv n vs)` >>
  `expr_type e = ArrayT et n /\ lowered_value_type ce e = expr_type e /\
   ~is_word_type (expr_type e)` by
    simp[Abbr`e`,expr_type_def,lowered_value_type_def,is_word_type_def] >>
  suspend "complete"
QED

Resume make_array_loop_result_from_completed_mods[complete]:
  `vv_post_mods H ctx func ce cx e es sa sb s0 ee (Value v)
      (LocatedValue (expr_type e) (mk_ptr (Var q) LocMemory)) t /\
   vv_store_bound cx (post_value_type ce e) (lowered_value_type ce e) ee (Value v)
      (LocatedValue (expr_type e) (mk_ptr (Var q) LocMemory)) t /\
   ptr_vv_ok cx (post_value_type ce e) (Value v)
      (LocatedValue (expr_type e) (mk_ptr (Var q) LocMemory)) ee gf tf t /\
   vv_own ce cx (post_value_type ce e) sa sb ee (Value v)
      (LocatedValue (expr_type e) (mk_ptr (Var q) LocMemory)) t /\
   ptr_buf_ok ce e (Var q) gf t /\
   t.vs_current_bb = sb.cs_current_bb /\ t.vs_inst_idx = LENGTH sb.cs_current_insts /\
   alloca_history func t /\ (ctx_has_dalloca ctx ==> allocas_below_fmp t) /\
   s0.vs_alloca_next <= t.vs_alloca_next /\ ghost_inv_at_mods (DF H) lo d ce cx ee gf tf t /\
   ghost_kept_at lo ce es sa G0 tn0 s0 gf tf /\ return_buf_frame d ce sb t /\ ~t.vs_halted` by
    (qpat_x_assum `^array_completion_contract` irule >>
     rpt (first_assum ACCEPT_TAC ORELSE conj_tac)
     >- (qexists_tac `gs` >> first_assum ACCEPT_TAC)
     >- (qexistsl [`base`,`cap`,`si`,`sh`,`ArrayTV tv n`] >>
         qpat_assum `~expr_has_effect e ==> make_elements_frame_mods _ _ _ _ _ _ _ _`
           (assume_tac o PURE_REWRITE_RULE [make_elements_frame_mods_def]) >>
         rpt (first_assum ACCEPT_TAC ORELSE conj_tac) >>
         qpat_assum `expr_type e = _` SUBST1_TAC >> first_assum ACCEPT_TAC) >>
     qexistsl [`env`,`mods`] >> first_assum ACCEPT_TAC) >>
  qpat_x_assum `^array_completion_contract` kall_tac >>
  rule_assum_tac (PURE_REWRITE_RULE [mk_ptr_def]) >>
  qpat_assum `expr_type e = _` (SUBST1_TAC o SYM) >>
  simp_tac (srw_ss()) [make_slot_child_post_mods_def,mk_ptr_def,vv_location_def] >>
  rpt (first_assum ACCEPT_TAC ORELSE conj_tac) >>
  strip_tac >> first_assum ACCEPT_TAC
QED

Finalise make_array_loop_result_from_completed_mods
