Theory s1PrefixBoolChainWordEqFullRead
Ancestors
  s1PrefixBoolChainEqDemand bodyFullBopWordSuffix bodyFullBopBytesEqSuffix
  bodyFullIntCallReturnHalt exprSimCompare exprBopSimDefs gasExemptCert
  exprBodyPreProps s1PrefixDefs bodyFullBopWordLayout gasOutcomeFullCompose
  exprBopSimProps exprSimDefs vyperStorageTrace vyperStorageFootprint
  bodyFullHashKeccakFixed loweringPosts gasOutcomeFull compileEnv vyperAST
  exprSimHypsDefs vyperTypeSystem bodyPtrBopTypedSource bodyPtrBopScalarDispatch
  exprSimProps arithmeticProps valueEncoding freshWrites vyperState vyperValue
  vyperContext vyperValueOperation venomExecSemantics vyperTyping list

(* Address and fixed bytes are stack words but not word_value_type. *)
Theorem word_eq_bytes_type[local]:
  !ty. is_word_type ty /\ ~word_value_type ty ==>
    ty = BaseT AddressT \/ ?m. ty = BaseT (BytesT (Fixed m)) /\ m <= 32
Proof
  Cases >> simp[is_word_type_def,word_value_type_def,is_flag_type_def] >>
  rename1 `BaseT bt` >> Cases_on `bt` >> simp[is_word_type_def] >>
  rename1 `BytesT sz` >> Cases_on `sz` >> simp[is_word_type_def]
QED

Theorem word_eq_bytes_value[local]:
  (ty = BaseT AddressT \/ ?m. ty = BaseT (BytesT (Fixed m)) /\ m <= 32) /\
  evaluate_type (get_tenv cx) ty = SOME tv /\
  value_has_type tv v1 /\ value_has_type tv v2 ==>
  bop_result cx (BaseT BoolT) Eq [ty;ty] v1 v2 es =
    INL (BoolV (eval_compare Eq ty (typed_val_to_w256 tv v1)
                                  (typed_val_to_w256 tv v2)))
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `?b1 b2. v1 = BytesV b1 /\ v2 = BytesV b2 /\
    (tv = BaseTV AddressT \/ ?m. tv = BaseTV (BytesT (Fixed m)) /\ m <= 32)` by
    (qpat_x_assum `ty = BaseT AddressT \/ _` strip_assume_tac >>
     gvs[evaluate_type_def,optionTheory.IF_EQUALS_OPTION] >>
     Cases_on `v1` >> Cases_on `v2` >> gvs[value_has_type_def]) >>
  `typed_val_to_w256 tv v1 = typed_val_to_w256 tv v2 <=> v1 = v2` by
    (gvs[] >> irule typed_val_to_w256_bytes_11 >> simp[]) >>
  qpat_x_assum `ty = BaseT AddressT \/ _` strip_assume_tac >>
  gvs[bop_result_def,evaluate_builtin_def,evaluate_binop_def,
      eval_compare_def,oEL_def]
QED

(* The exempt paths do not execute the continuation on a left exit. *)
fun eq_full_bind_tac rule =
  irule rule >> rpt conj_tac
  >~ [`gas_marked_exec _ _ _ _ _ _ _`]
  >- (rpt (pop_assum kall_tac) >> rpt strip_tac >>
      irule gas_exempt_cert_bind_value >>
      qpat_assum `gas_marked_exec _ _ _ _ _ _ _ _` (irule_at Any) >> gvs[])
  >~ [`gas_exempt_cert _ _ _ _ _ _ _`]
  >- (rpt strip_tac >> irule gas_exempt_cert_error_value >> simp[])
  >~ [`storage_trace_frame (bind (eval_expr _ _) _)`]
  >- (irule storage_trace_frame_bind_all >>
      simp[evaluate_storage_trace_frame,storage_trace_frame_read_result])
  >~ [`storage_trace_frame _`]
  >- (rpt (pop_assum kall_tac) >> gen_tac >> BETA_TAC >>
      simp[storage_trace_frame_bind_all,evaluate_storage_trace_frame,
           storage_trace_frame_read_result,storage_trace_frame_def,bop_result_def]);

fun eq_full_child_tac pattern =
  irule gas_outcome_full_post_source >> qpat_assum pattern (irule_at Any) >>
  simp[] >> rpt strip_tac >> Cases_on `res` >> fs[expr_exit_def];

fun eq_full_lift_suffix_tac g =
  (disch_then (mp_tac o MATCH_MP gas_outcome_full_halt_room o BETA_RULE) >>
   disch_then (fn th => irule gas_outcome_full_post_mono >> irule_at Any th) >>
   BETA_TAC >> simp[Abbr `Q`,Abbr `exitR`,expr_type_def,is_word_type_def] >>
   rpt gen_tac >> disch_then (qx_choose_then `v` strip_assume_tac) >>
   qexists_tac `v` >> simp[] >>
   first_assum (ACCEPT_TAC o MATCH_MP stmt_state_rel_allocas_below_fmp o
                CONJUNCT1 o REWRITE_RULE [expr_post_def])) g;

(* SCRATCH MEASUREMENT: the original proof failed after widening the body
   definitions. Temporarily admit it to test its downstream consumers.
Proof
  rpt gen_tac >> strip_tac >>
  drule_all bool_chain_word_eq_demand_closure >> strip_tac >>
  qpat_x_assum `value_read_demand _ _ _ _ _ (Builtin _ _ _) _ _ _`
    (strip_assume_tac o REWRITE_RULE [value_read_demand_def,expr_sim_full_pre_def]) >>
  drule_all bop_full_layout >> strip_tac >>
  qpat_assum `value_read_demand _ _ _ _ _ l _ _ _`
    (strip_assume_tac o REWRITE_RULE [value_read_demand_def,expr_sim_full_pre_def]) >>
  qpat_assum `!a b c. _ ==> gas_outcome_full _ _ _ _ _ (es,s0,G0,tn0) _ _`
    (drule_then strip_assume_tac) >>
  gvs[] >>
  qpat_x_assum `!a b c. _ ==> gas_outcome_full _ _ _ _ _ (es,s0,G0,tn0) _ _`
    kall_tac >>
  qmatch_asmsub_abbrev_tac `gas_outcome_full _ _ _ _ _ (es,s0,G0,tn0) leftQ exitR` >>
  pure_once_rewrite_tac[REWRITE_RULE [ETA_THM] eval_expr_bop_bind] >>
  eq_full_bind_tac gas_outcome_full_bind_all_path >>
  qexists_tac `\H res ee G tn u. leftQ H res ee G tn u /\ ~u.vs_halted /\ ee.gas_obs = []` >>
  conj_tac >- suspend "right_entry" >>
  eq_full_child_tac `gas_outcome_full _ _ _ _ _ (es,s0,G0,tn0) leftQ exitR` >>
  fs[Abbr `exitR`]
QED
*)
Theorem word_eq_read_full_at_demand:
  !DF lo d ctx shadow_ctx PG func shadow_func cenv cx ty l r env tops es
     st0 sa sb shadow_sa shadow_sb op s0 G0 tn0.
    value_read_demand (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
      tops cenv cx env (Builtin (BaseT BoolT) (Bop Eq) [l;r]) ty es
      (st0,sa,sb,shadow_sa,shadow_sb,op,s0,G0,tn0) /\
    ~is_bytestring_type (expr_type l) /\
    is_word_type (expr_type l) /\ is_word_type (expr_type r) /\
    (!s1 shadow_s1 x.
      value_read_demand (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
        tops cenv cx env l (expr_type l) es
        (st0,sa,s1,shadow_sa,shadow_s1,x,s0,G0,tn0) ==>
      gas_outcome_full (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
        (cx_tops cx) cx st0 (bind (eval_expr cx l) (read_result cx)) (es,s0,G0,tn0)
        (\H res ee G tn u. ?v. res = INL v /\
          expr_post H ctx func cenv cx l es sa s1 s0 ee v x u /\
          expr_store_bound cx (post_value_type cenv l) v x u /\
          u.vs_current_bb = s1.cs_current_bb /\
          u.vs_inst_idx = LENGTH s1.cs_current_insts /\
          alloca_history func u /\
          (ctx_has_dalloca ctx ==> allocas_below_fmp u) /\
          s0.vs_alloca_next <= u.vs_alloca_next /\
          ghost_inv_at (DF H) lo d cenv cx ee G tn u /\
          ptr_val_ok cx (post_value_type cenv l) v x G tn u /\
          (~is_word_type (post_value_type cenv l) ==> ptr_buf_ok cenv l x G u) /\
          ghost_kept_at lo cenv es sa G0 tn0 s0 G tn)
        (\H res ee gt ex. expr_exit res ex /\ halt_exit H cx ee res ex /\
          (ctx_has_dalloca ctx ==> !s. ex = Halt s ==> allocas_below_fmp s))) /\
    (!s1 s2 shadow_s1 shadow_s2 x y left v1 mid G1 tn1 t.
      value_read_demand (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
        tops cenv cx env l (expr_type l) es
        (st0,sa,s1,shadow_sa,shadow_s1,x,s0,G0,tn0) /\
      (!tail. bind (eval_expr cx l) (read_result cx)
         (es with gas_obs := gas_explicit left s0.vs_gas_readings ++ tail) =
           (INL v1,mid with gas_obs := tail)) /\
      storage_trace_domain cx st0 mid.storage_trace /\
      (!H. valid_horizon cx st0 H mid.storage_trace ==>
        gas_origin_ptr_path (DF H,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
          (s0,G0,tn0) left (OK t,G1,tn1) /\
        expr_post H ctx func cenv cx l es sa s1 s0 mid v1 x t /\
        expr_store_bound cx (post_value_type cenv l) v1 x t /\
        t.vs_current_bb = s1.cs_current_bb /\
        t.vs_inst_idx = LENGTH s1.cs_current_insts /\
        alloca_history func t /\
        (ctx_has_dalloca ctx ==> allocas_below_fmp t) /\
        s0.vs_alloca_next <= t.vs_alloca_next /\
        ghost_inv_at (DF H) lo d cenv cx mid G1 tn1 t /\
        ptr_val_ok cx (post_value_type cenv l) v1 x G1 tn1 t /\
        (~is_word_type (post_value_type cenv l) ==> ptr_buf_ok cenv l x G1 t) /\
        ghost_kept_at lo cenv es sa G0 tn0 s0 G1 tn1 /\
        ~t.vs_halted /\ mid.gas_obs = []) /\
      value_read_demand (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
        tops cenv cx env r (expr_type l) mid
        (st0,s1,s2,shadow_s1,shadow_s2,y,t,G1,tn1) ==>
      gas_outcome_full (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
        (cx_tops cx) cx st0 (bind (eval_expr cx r) (read_result cx)) (mid,t,G1,tn1)
        (\H res ee G tn u. ?v. res = INL v /\
          expr_post H ctx func cenv cx r mid s1 s2 t ee v y u /\
          expr_store_bound cx (post_value_type cenv r) v y u /\
          u.vs_current_bb = s2.cs_current_bb /\
          u.vs_inst_idx = LENGTH s2.cs_current_insts /\
          alloca_history func u /\
          (ctx_has_dalloca ctx ==> allocas_below_fmp u) /\
          t.vs_alloca_next <= u.vs_alloca_next /\
          ghost_inv_at (DF H) lo d cenv cx ee G tn u /\
          ptr_val_ok cx (post_value_type cenv r) v y G tn u /\
          (~is_word_type (post_value_type cenv r) ==> ptr_buf_ok cenv r y G u) /\
          ghost_kept_at lo cenv mid s1 G1 tn1 t G tn)
        (\H res ee gt ex. expr_exit res ex /\ halt_exit H cx ee res ex /\
          (ctx_has_dalloca ctx ==> !s. ex = Halt s ==> allocas_below_fmp s))) ==>
    gas_outcome_full (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
      (cx_tops cx) cx st0
      (bind (eval_expr cx (Builtin (BaseT BoolT) (Bop Eq) [l;r])) (read_result cx))
      (es,s0,G0,tn0)
      (\H res ee G tn u. ?v. res = INL v /\
        expr_post H ctx func cenv cx (Builtin (BaseT BoolT) (Bop Eq) [l;r])
          es sa sb s0 ee v op u /\
        expr_store_bound cx (post_value_type cenv (Builtin (BaseT BoolT) (Bop Eq) [l;r])) v op u /\
        u.vs_current_bb = sb.cs_current_bb /\
        u.vs_inst_idx = LENGTH sb.cs_current_insts /\
        alloca_history func u /\
        (ctx_has_dalloca ctx ==> allocas_below_fmp u) /\
        s0.vs_alloca_next <= u.vs_alloca_next /\
        ghost_inv_at (DF H) lo d cenv cx ee G tn u /\
        ptr_val_ok cx (post_value_type cenv (Builtin (BaseT BoolT) (Bop Eq) [l;r])) v op G tn u /\
        (~is_word_type (post_value_type cenv (Builtin (BaseT BoolT) (Bop Eq) [l;r])) ==>
          ptr_buf_ok cenv (Builtin (BaseT BoolT) (Bop Eq) [l;r]) op G u) /\
        ghost_kept_at lo cenv es sa G0 tn0 s0 G tn)
      (\H res ee gt ex. expr_exit res ex /\ halt_exit H cx ee res ex /\
        (ctx_has_dalloca ctx ==> !s. ex = Halt s ==> allocas_below_fmp s))
Proof
  cheat
QED

(* SCRATCH MEASUREMENT: original continuation.
Resume word_eq_read_full_at_demand[right_entry]:
  qx_genl_tac [`left`,`res`,`mid`,`G1`,`tn1`,`t`] >> BETA_TAC >> strip_tac >>
  qunabbrev_tac `leftQ` >> rule_assum_tac BETA_RULE >>
  `valid_horizon cx st0 (storage_trace_horizon mid.storage_trace) mid.storage_trace` by
    fs[storage_trace_domain_def] >>
  qpat_assum `!H. valid_horizon _ _ H mid.storage_trace ==> (?v. _) /\ _`
    (qspec_then `storage_trace_horizon mid.storage_trace` (drule_then strip_assume_tac)) >>
  qpat_x_assum `res = INL _` SUBST_ALL_TAC >>
  disj1_tac >> qexists_tac `v` >> simp[] >>
  `!H. valid_horizon cx st0 H mid.storage_trace ==>
    gas_origin_ptr_path (DF H,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
      (s0,G0,tn0) left (OK t,G1,tn1) /\
    expr_post H ctx func cenv cx l es sa s1 s0 mid v x t /\
    expr_store_bound cx (expr_type l) v x t /\
    t.vs_current_bb = s1.cs_current_bb /\
    t.vs_inst_idx = LENGTH s1.cs_current_insts /\
    alloca_history func t /\ (ctx_has_dalloca ctx ==> allocas_below_fmp t) /\
    s0.vs_alloca_next <= t.vs_alloca_next /\
    ghost_inv_at (DF H) lo d cenv cx mid G1 tn1 t /\
    ptr_val_ok cx (expr_type l) v x G1 tn1 t /\
    ghost_kept_at lo cenv es sa G0 tn0 s0 G1 tn1 /\
    ~t.vs_halted /\ mid.gas_obs = []` by
      (gen_tac >> disch_tac >>
       qpat_assum `!H. valid_horizon _ _ H mid.storage_trace ==> (?w. _) /\ _`
         (qspec_then `H` (drule_then strip_assume_tac)) >>
       qpat_assum `!H. valid_horizon _ _ H mid.storage_trace ==> gas_origin_ptr_path _ _ _ _`
         (qspec_then `H` (drule_then assume_tac)) >> fs[]) >>
  `value_read_demand (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
     tops cenv cx env r (expr_type l) mid
     (st0,s1,s2,shadow_s1,shadow_s2,y,t,G1,tn1)` by
    (first_x_assum irule >> simp[] >> qexistsl_tac [`left`,`v`] >> simp[]) >>
  qpat_x_assum `!a b c e f g h i j k m n. _ ==> gas_outcome_full _ _ _ _ _ _ _ _`
    (drule_at (Pat `value_read_demand _ _ _ _ _ r _ mid _`)) >>
  disch_then (qspecl_then [`x`,`left`,`v`] mp_tac) >>
  impl_tac >- simp[] >> strip_tac >>
  qpat_assum `value_read_demand _ _ _ _ _ r _ _ _`
    (strip_assume_tac o REWRITE_RULE [value_read_demand_def,expr_sim_full_pre_def]) >>
  gvs[] >>
  qmatch_asmsub_abbrev_tac `gas_outcome_full _ _ _ _ (bind (eval_expr cx r) _) _ rightQ exitR` >>
  eq_full_bind_tac gas_outcome_full_bind_all >>
  qexists_tac `\H res ee G tn u. rightQ H res ee G tn u /\ ~u.vs_halted /\ ee.gas_obs = []` >>
  conj_tac >- suspend "suffix" >>
  eq_full_child_tac `gas_outcome_full _ _ _ _ (bind (eval_expr cx r) _) _ rightQ exitR` >>
  fs[Abbr `exitR`]
QED
*)

(* SCRATCH MEASUREMENT: original continuation.
Resume word_eq_read_full_at_demand[suffix]:
  qx_genl_tac [`right`,`res2`,`fin`,`G2`,`tn2`,`u`] >> BETA_TAC >> strip_tac >>
  qunabbrev_tac `rightQ` >> rule_assum_tac BETA_RULE >>
  `valid_horizon cx st0 (storage_trace_horizon fin.storage_trace) fin.storage_trace` by
    fs[storage_trace_domain_def] >>
  qpat_assum `!H. valid_horizon _ _ H fin.storage_trace ==> (?v. _) /\ _`
    (qspec_then `storage_trace_horizon fin.storage_trace` (drule_then strip_assume_tac)) >>
  qpat_x_assum `res2 = INL _` SUBST_ALL_TAC >>
  rename1 `expr_store_bound cx (expr_type r) v2 y u` >>
  disj1_tac >> qexists_tac `v2` >> simp[] >>
  rename1 `expr_store_bound cx (expr_type l) v1 x t` >>
  `!H. valid_horizon cx st0 H fin.storage_trace ==>
    expr_post H ctx func cenv cx r mid s1 s2 t fin v2 y u /\
    ghost_inv_at (DF H) lo d cenv cx fin G2 tn2 u` by
    (gen_tac >> disch_tac >>
     qpat_assum `!H. valid_horizon _ _ H fin.storage_trace ==> (?w. _) /\ _`
       (qspec_then `H` (drule_then strip_assume_tac)) >> fs[]) >>
  qpat_x_assum `!H. valid_horizon _ _ H fin.storage_trace ==> (?w. _) /\ _` kall_tac >>
  rename1 `compile_binop Eq x y (expr_type e1) NONE NONE s2 = (op,sb)` >>
  rename1 `expr_store_bound cx (expr_type e2) v2 y u` >>
  qmatch_goalsub_abbrev_tac `gas_outcome_full _ _ _ _ _ _ Q exitR` >>
  Cases_on `word_value_type (expr_type e1) /\ word_value_type (expr_type e2)`
  >- (mp_tac (Q.INST [`ann` |-> `BaseT BoolT`,`bop` |-> `Eq`] bop_word_suffix_full_halt) >>
      (impl_tac >- (simp[] >> rpt conj_tac >> rpt strip_tac >> simp[])) >>
      eq_full_lift_suffix_tac) >>
  suspend "bytes_suffix"
QED
*)

(* SCRATCH MEASUREMENT: original continuation.
Resume word_eq_read_full_at_demand[bytes_suffix]:
  `(?gs. bind (eval_expr cx e1) (read_result cx) (es with gas_obs := gs) = (INL v1,mid)) /\
   (?gs. bind (eval_expr cx e2) (read_result cx) (mid with gas_obs := gs) = (INL v2,fin))` by
    (`mid with gas_obs := [] = mid /\ fin with gas_obs := [] = fin` by
       simp[evaluation_state_component_equality] >>
     pop_assum (map_every assume_tac o CONJUNCTS) >>
     conj_tac >- (qexists_tac `gas_explicit left s0.vs_gas_readings` >>
       qpat_assum `mid with gas_obs := [] = mid` (fn clear =>
         qpat_assum `!tail. bind (eval_expr cx e1) _ _ = _`
           (qspec_then `[]` (ACCEPT_TAC o REWRITE_RULE [APPEND_NIL,clear])))) >>
     qexists_tac `gas_explicit right t.vs_gas_readings` >>
     qpat_assum `fin with gas_obs := [] = fin` (fn clear =>
       qpat_assum `!tail. bind (eval_expr cx e2) _ _ = _`
         (qspec_then `[]` (ACCEPT_TAC o REWRITE_RULE [APPEND_NIL,clear])))) >>
  pop_assum (map_every assume_tac o CONJUNCTS) >>
  drule bop_pair_source_facts >>
  disch_then (qspecl_then [`v2`,`v1`,`fin`,`mid`] mp_tac) >>
  (impl_tac >- (simp[] >> metis_tac[])) >> strip_tac >>
  `expr_type e2 = expr_type e1` by fs[well_typed_binop_def] >>
  `~word_value_type (expr_type e1)` by fs[] >>
  drule_all_then assume_tac word_eq_bytes_type >>
  `?tv. evaluate_type (get_tenv cx) (expr_type e1) = SOME tv /\
        value_has_type tv v1 /\ value_has_type tv v2` by metis_tac[optionTheory.SOME_11] >>
  `post_value_type cenv e1 = expr_type e1` by metis_tac[post_value_type_word] >>
  `post_value_type cenv e2 = expr_type e1` by metis_tac[post_value_type_word] >>
  `eval_operand x t = SOME (typed_val_to_w256 tv v1) /\
   eval_operand y u = SOME (typed_val_to_w256 tv v2)` by
    ((qpat_assum `!H. valid_horizon _ _ H mid.storage_trace ==> _ /\ expr_post _ _ _ _ _ _ _ _ _ _ _ _ _ _`
        (qspec_then `storage_trace_horizon mid.storage_trace` (drule_then strip_assume_tac)) >>
     qpat_assum `!H. valid_horizon _ _ H fin.storage_trace ==> expr_post _ _ _ _ _ _ _ _ _ _ _ _ _ _ /\ _`
        (qspec_then `storage_trace_horizon fin.storage_trace` (drule_then strip_assume_tac)) >>
     conj_tac
     >- (irule expr_val_rel_typed >> qexistsl_tac [`cx`,`expr_type e1`] >>
         gvs[expr_post_def,post_value_type_word]) >>
     irule expr_val_rel_typed >> qexistsl_tac [`cx`,`expr_type e2`] >>
     gvs[expr_post_def,post_value_type_word] >> (metis_tac[expr_post_def, post_value_type_word, expr_val_rel_typed]))) >>
  `eval_operand x u = SOME (typed_val_to_w256 tv v1)` by
    (irule eval_operand_frame >>
     qpat_assum `eval_operand x t = _` (irule_at Any) >>
     qexists_tac `s1` >> simp[] >>
     qpat_assum `!H. valid_horizon _ _ H fin.storage_trace ==> _ /\ _`
       (qspec_then `storage_trace_horizon fin.storage_trace` (drule_then strip_assume_tac)) >>
     fs[expr_post_def]) >>
  `!z. x = Var z ==> not_fresh_at s2 z` by metis_tac[freshWritesTheory.not_fresh_at_mono] >>
  `expr_type e1 = BaseT AddressT \/ ?m. expr_type e1 = BaseT (BytesT (Fixed m))` suffices_by
    (disch_then assume_tac >>
     drule_all_then strip_assume_tac (SRULE [] (Q.INST [`bop` |-> `Eq`] bop_bytes_eq_suffix_run)) >>
     suspend "bytes_run") >> metis_tac[]
QED
*)

(* SCRATCH MEASUREMENT: original continuation.
Resume word_eq_read_full_at_demand[bytes_run]:
  `?B. bop_scalar_seq {z | not_fresh_at s2 z}
     ({x;y} UNION IMAGE Lit UNIV) (emitted_insts s2 sb) B /\ op IN B` by
    (irule bop_scalar_binop_certificate >> simp[] >>
     qexistsl_tac [`BaseT BoolT`,`NONE`,`Eq`,`NONE`,`expr_type e1`,`expr_type e2`,`expr_type e1`] >> simp[]) >>
  qpat_x_assum `!cc. ?q. run_inst_seq (emitted_insts s2 sb) u = OK q /\ _`
    (qspec_then `ctx` strip_assume_tac) >>
  rename1 `run_inst_seq (emitted_insts s2 sb) u = OK target` >>
  `?v target. bop_result cx (BaseT BoolT) Eq [expr_type e1;expr_type e2] v1 v2 fin = INL v /\
     run_inst_seq (emitted_insts s2 sb) u = OK target /\
     expr_val_rel cx (BaseT BoolT) v op target` by
    (qexistsl_tac [`BoolV (eval_compare Eq (expr_type e1) (typed_val_to_w256 tv v1)
                                          (typed_val_to_w256 tv v2))`, `target`] >>
     conj_tac
     >- (simp[] >> irule word_eq_bytes_value >> simp[]) >>
     simp[expr_val_rel_def,is_word_type_def,evaluate_type_def,
          typed_val_to_w256_def,val_to_w256_def] >>
     Cases_on `eval_compare Eq (expr_type e1) (typed_val_to_w256 tv v1)
                                         (typed_val_to_w256 tv v2)` >> simp[bool_to_word_def]) >>
  mp_tac (Q.INST [`ann` |-> `BaseT BoolT`,`bop` |-> `Eq`] bop_suffix_full_halt) >>
  (impl_tac >- (simp[] >> rpt conj_tac >> rpt strip_tac >> simp[] >> metis_tac[])) >>
  eq_full_lift_suffix_tac
QED
*)

(* SCRATCH MEASUREMENT: original continuation.
Finalise word_eq_read_full_at_demand
*)
