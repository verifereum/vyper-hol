(* Start the checked suffix at the second operand's actual source and
   target landing. The callback owns the loop from the full header onwards. *)
Theory bodyForRangeCheckedSuffixJoinMods
Ancestors
  bodyForRangeCheckedStartMods bodyForRangeAllocMods bodyForRangeRouteMods
  gasOutcomeFullZeroPrefixMods gasOutcomeFullPostMods gasExplicitSites
  bodyForRangeHeaderMods bodyFullIfExpReach vyperEvalPreservesScopes
  vyperTypeSystem vyperInterpreter vyperState venomState stmtSimProps
  localPtrsProps freshWrites integer_word finite_map ptrDiscipline loweringPosts
  bodyFullShadowBodyInv
Libs
  monadsyntax

val _ = Parse.hide "body";

Theorem checked_counter_normal_source[local]:
  (!tail. range_counter_source n1 n2 bound (mid2 with gas_obs := marks ++ tail) =
          (INL rs,ee with gas_obs := tail)) /\
  mid2.gas_obs = [] /\ ee.gas_obs = [] ==> ee = mid2
Proof
  strip_tac >>
  qpat_x_assum `!tail. range_counter_source _ _ _ _ = _` (qspec_then `[]` mp_tac) >>
  Cases_on `n2 < n1` >> simp[range_counter_source_cases,raise_def] >>
  Cases_on `bound < Num (n2 - n1)` >> simp[raise_def,return_def] >>
  simp[evaluation_state_component_equality] >> strip_tac >> first_assum ACCEPT_TAC
QED

Theorem checked_alloc_operand_kept[local]:
  (!x. not_fresh_at z x ==> lookup_var x sA = lookup_var x t2 /\
        FLOOKUP GA x = FLOOKUP G2 x /\ op_taint tnA (Var x) = op_taint tn2 (Var x)) /\
  (!x. op = Var x ==> not_fresh_at z x) /\ (!l. op <> Label l) /\
  eval_operand op t2 = SOME w /\ op_prov G2 op = NONE /\ op_taint tn2 op = {} ==>
  eval_operand op sA = SOME w /\ op_prov GA op = NONE /\ op_taint tnA op = {}
Proof
  Cases_on `op` >> simp[eval_operand_def,op_prov_def,op_taint_def] >>
  strip_tac >> first_x_assum drule >> simp[]
QED

Theorem range_checked_suffix_join_mods:
  p = STRING #"%" (toString z.cs_next_var) /\
  lookup_block z.cs_current_bb func.fn_blocks =
    SOME <|bb_label := z.cs_current_bb; bb_instructions := z.cs_current_insts ++
      [mk_inst z.cs_next_id ALLOCA [Lit (n2w sz)] [p];
       mk_inst (z.cs_next_id + 1) JMP [Label entry_lbl] []]|> /\
  lookup_block entry_lbl func.fn_blocks = SOME
    <|bb_label := entry_lbl;
      bb_instructions :=
        [mk_inst (z.cs_next_id + 2) ASSIGN [op1] [cv];
         mk_inst (z.cs_next_id + 3) SUB [op2;op1] [rv];
         mk_inst (z.cs_next_id + 4) (if is_signed_type typ then SGT else GT) [op1;op2] [g1];
         mk_inst (z.cs_next_id + 5) ISZERO [Var g1] [z1];
         mk_inst (z.cs_next_id + 6) ASSERT [Var z1] [];
         mk_inst (z.cs_next_id + 7) GT [Var rv;Lit (n2w bound)] [g2];
         mk_inst (z.cs_next_id + 8) ISZERO [Var g2] [z2];
         mk_inst (z.cs_next_id + 9) ASSERT [Var z2] [];
         mk_inst (z.cs_next_id + 10) ADD [op1;Var rv] [ev];
         mk_inst (z.cs_next_id + 11) JMP [Label cond_lbl] []]|> /\
  ALL_DISTINCT [p;cv;rv;g1;z1;g2;z2;ev] /\
  (!x. MEM x [cv;rv;g1;z1;g2;z2;ev] ==> ~not_fresh_at z x) /\
  sa.cs_next_var <= z.cs_next_var /\ sa.cs_next_id <= z.cs_next_id /\
  z.cs_next_var <= sb0.cs_next_var /\
  fn_inst_ids_distinct func /\
  (!bb. MEM bb func.fn_blocks ==> phi_prefix_length bb.bb_instructions = 0) /\
  ret_pc_ok cenv sa s0 /\
  (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  lookup_scopes id es.scopes = NONE /\
  sz < dimword (:256) /\ bound < dimword (:256) /\
  is_int_type typ /\ evaluate_type (get_tenv cx) typ = SOME tyv /\
  (!tail. bind (eval_expr cx e1) (read_result cx) (es with gas_obs := gs1 ++ tail) =
          (INL (IntV n1),mid1 with gas_obs := tail)) /\
  (!tail. bind (eval_expr cx e2) (read_result cx) (mid1 with gas_obs := gs2 ++ tail) =
          (INL (IntV n2),mid2 with gas_obs := tail)) /\
  value_has_type tyv (IntV n1) /\ value_has_type tyv (IntV n2) /\
  eval_operand op1 t2 = SOME (i2w n1) /\ eval_operand op2 t2 = SOME (i2w n2) /\
  op_prov G2 op1 = NONE /\ op_prov G2 op2 = NONE /\
  op_taint tn2 op1 = {} /\ op_taint tn2 op2 = {} /\
  (!l. op1 <> Label l /\ op2 <> Label l) /\
  (!x. op1 = Var x \/ op2 = Var x ==> not_fresh_at z x) /\
  storage_trace_domain cx st0 mid2.storage_trace /\ mid2.gas_obs = [] /\
  expr_sim_inv_mods mods cenv cx env mid2 /\ body_const_cells_agree_mods mods cx env mid2 /\
  MAP FDOM mid2.scopes = MAP FDOM es.scopes /\
  ~t2.vs_halted /\ t2.vs_current_bb = z.cs_current_bb /\
  t2.vs_inst_idx = LENGTH z.cs_current_insts /\
  local_ptrs_reserved cenv z /\ return_buf_frame d cenv z t2 /\ return_buf_sep d cenv mid2 t2 /\
  alloca_history func t2 /\ s0.vs_alloca_next <= t2.vs_alloca_next /\
  (!fn inst s. frag_reachable ctx func t2 fn inst s ==> dalloca_fmp_headroom inst s) /\
  (!H. valid_horizon cx st0 H mid2.storage_trace ==>
    stmt_state_rel H ctx func cenv cx mid2 t2 /\ immutable_frame_mods func cenv cx mid2 t2 /\
    storage_well_formed_on cx mid2 (FST H) /\ ghost_inv_at_mods (DF H) lo d cenv cx mid2 G2 tn2 t2) /\
  (!x w. not_fresh_at sa x /\ lookup_var x s0 = SOME w ==> lookup_var x t2 = SOME w) /\
  (!aid b. FLOOKUP s0.vs_allocas aid = SOME b ==> FLOOKUP t2.vs_allocas aid = SOME b) /\
  (!x. not_fresh_at sa x ==> FLOOKUP G2 x = FLOOKUP G0 x /\ op_taint tn2 (Var x) = op_taint tn0 (Var x)) /\
  alloca_frame cenv es sa s0 cenv mid2 t2 /\
  (!aid off sz i. FLOOKUP s0.vs_allocas aid = SOME (off,sz) /\ aid < sa.cs_next_id /\
    (!id b sz'. local_region cenv es.scopes s0 id b sz' ==> off + sz <= b \/ b + sz' <= off) /\
    off <= i /\ i < off + sz /\ i IN tn2.t_mem ==> i IN tn0.t_mem) /\
  gas_admissible (do rl <- lift_sum (get_range_limits (IntV n1) (IntV n2));
    check (compatible_bound (Dynamic bound) (SND rl)) "For too long";
    eval_for cx tyv id body (GENLIST (\j. Value (IntV (FST rl + &j))) (SND rl)) od)
    (stmt_res_ok lctx) mid2 /\
  (n1 <= n2 /\ Num (n2 - n1) <= bound ==>
    (do rl <- lift_sum (get_range_limits (IntV n1) (IntV n2));
     check (compatible_bound (Dynamic bound) (SND rl)) "For too long";
     eval_for cx tyv id body (GENLIST (\j. Value (IntV (FST rl + &j))) (SND rl)) od) =
    eval_for cx tyv id body (GENLIST (\j. Value (IntV (n1 + &j))) (Num (n2 - n1)))) /\
  (!tenv s tv t s1 vs t1 s2 u t2.
    tenv = get_tenv cx /\
    lift_option_type (evaluate_type tenv typ) "For evaluate_type" s = (INL tv,t) /\
    eval_iterator cx (Range e1 e2) s1 = (INL vs,t1) /\
    check (compatible_bound (Dynamic bound) (LENGTH vs)) "For too long" s2 = (INL u,t2) ==>
    body_for_full_ok_mods mods exps cx tv id body vs) /\
  (!w mid t G tn rs.
    n1 <= n2 /\ Num (n2 - n1) <= bound /\
    rs = GENLIST (\j. Value (IntV (n1 + &j))) (Num (n2 - n1)) /\
    body_for_full_ok_mods mods exps cx tyv id body rs /\
    storage_trace_domain cx st0 mid.storage_trace /\ ~t.vs_halted /\
    gas_admissible (eval_for cx tyv id body rs) (stmt_res_ok lctx) mid /\
    (!H. valid_horizon cx st0 H mid.storage_trace ==>
      range_header_mods mods DF lo d ctx func cenv cx env id tyv st0
        sa sb0 es s0 G0 tn0 n1 n2 bound cond_lbl cv ev p z.cs_next_id sz w H rs mid G tn t) ==>
    gas_outcome_full_mods (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG) mods cx st0
      (eval_for cx tyv id body rs) (mid,t,G,tn) Q
      (\H res ee gt r. (!tail. stmt_exit_ptr (RetQ H) (ee with gas_obs := tail) res gt r) /\
        halt_exit H cx ee res r /\ (ctx_has_dalloca ctx ==>
          !s. (r = Halt s \/ ?ir. r = IntRet ir s) ==> allocas_below_fmp s))) ==>
  gas_outcome_full_mods (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG) mods cx st0
    (do rl <- lift_sum (get_range_limits (IntV n1) (IntV n2));
     check (compatible_bound (Dynamic bound) (SND rl)) "For too long";
     eval_for cx tyv id body (GENLIST (\j. Value (IntV (FST rl + &j))) (SND rl)) od)
    (mid2,t2,G2,tn2) Q
    (\H res ee gt r. (!tail. stmt_exit_ptr (RetQ H) (ee with gas_obs := tail) res gt r) /\
      halt_exit H cx ee res r /\ (ctx_has_dalloca ctx ==>
        !s. (r = Halt s \/ ?ir. r = IntRet ir s) ==> allocas_below_fmp s))
Proof
  strip_tac >>
  `ret_pc_ok cenv sa t2` by
    (irule ret_pc_ok_frame >>
     qpat_assum `ret_pc_ok cenv sa s0` (irule_at Any) >> simp[]) >>
  `lookup_block z.cs_current_bb func.fn_blocks =
     SOME <|bb_label := z.cs_current_bb; bb_instructions := z.cs_current_insts ++
       [mk_inst z.cs_next_id ALLOCA [Lit (n2w sz)] [p]] ++
       [mk_inst (z.cs_next_id + 1) JMP [Label entry_lbl] []]|>` by simp[] >>
  qpat_assum `alloca_frame cenv es sa s0 cenv mid2 t2`
    (mp_then (Pat `alloca_frame _ _ _ _ _ _ _`) (drule_all_then mp_tac)
      range_slot_alloc_path_mods) >>
  disch_then (qspecl_then [`gas_explicit_sites ctx shadow_ctx`,`PG`]
    (qx_choosel_then [`w`,`sA`,`GA`,`tnA`] strip_assume_tac)) >>
  irule gas_outcome_full_mods_zero_prefix >>
  qexistsl_tac [`GA`,`sA`,`tnA`] >> conj_tac
  >- (gen_tac >> first_assum irule) >>
  qmatch_goalsub_abbrev_tac `gas_outcome_full_mods E mods cx st0 src (mid2,sA,GA,tnA) Q R` >>
  qabbrev_tac `Header = range_header_mods mods DF lo d ctx func cenv cx env id tyv st0
    sa sb0 es s0 G0 tn0 n1 n2 bound cond_lbl cv ev p z.cs_next_id sz w` >>
  `gas_outcome_full_mods E mods cx st0 (range_counter_source n1 n2 bound) (mid2,sA,GA,tnA)
    (\H res ee G tn t. ?rs. res = INL rs /\ Header H rs ee G tn t)
    (\H res ee gt r. ?ex. res = INR ex /\ R H (INR ex) ee gt r)` by suspend "counter" >>
  `gas_outcome_full_mods E mods cx st0 (range_counter_source n1 n2 bound) (mid2,sA,GA,tnA)
    (\H res ee G tn t. ?rs. res = INL rs /\ (Header H rs ee G tn t /\ ee = mid2))
    (\H res ee gt r. ?ex. res = INR ex /\ R H (INR ex) ee gt r)` by suspend "ready" >>
  qunabbrev_tac `src` >> qunabbrev_tac `E` >>
  irule range_counter_rounds_mods >>
  qexists_tac `\H rs ee G tn t. Header H rs ee G tn t /\ ee = mid2` >>
  BETA_TAC >> reverse conj_tac >- first_assum ACCEPT_TAC >>
  suspend "rounds"
QED

Resume range_checked_suffix_join_mods[counter]:
  qabbrev_tac `pre = <|bb_label := z.cs_current_bb; bb_instructions := z.cs_current_insts ++
      [mk_inst z.cs_next_id ALLOCA [Lit (n2w sz)] [p];
       mk_inst (z.cs_next_id + 1) JMP [Label entry_lbl] []]|>` >>
  `lookup_block sA.vs_current_bb func.fn_blocks = SOME pre` by simp[Abbr `pre`] >>
  `get_instruction pre sA.vs_inst_idx = SOME (mk_inst (z.cs_next_id + 1) JMP [Label entry_lbl] [])`
    by simp[Abbr `pre`,venomInstTheory.get_instruction_def,listTheory.EL_APPEND_EQN] >>
  `range_outer_frame_mods ctx func cenv sa es s0 G0 tn0 mid2 GA tnA sA` by
    (pure_rewrite_tac[range_outer_frame_mods_def] >> rpt conj_tac >> first_assum ACCEPT_TAC) >>
  `valid_horizon cx st0 (storage_trace_horizon mid2.storage_trace) mid2.storage_trace` by
    (qhdtm_assum `storage_trace_domain`
       (ACCEPT_TAC o REWRITE_RULE [vyperStorageFootprintTheory.storage_trace_domain_def])) >>
  `allocas_from lo sA` by
    (qpat_assum `!H. valid_horizon _ _ H _ ==> stmt_state_rel _ _ _ _ _ _ sA /\ _`
        (drule_then strip_assume_tac) >>
     fs[ghost_inv_at_mods_def]) >>
  `lookup_scopes id mid2.scopes = NONE` by
    (irule lookup_scopes_none_map_fdom >> qexists_tac `es.scopes` >> simp[]) >>
  `!x. not_fresh_at sa x ==> not_fresh_at z x` by
    (gen_tac >> disch_tac >> irule not_fresh_at_mono >> qexists_tac `sa` >> simp[]) >>
  `!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at z x` by
    (rpt strip_tac >> first_x_assum irule >> first_x_assum drule >> simp[]) >>
  `!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at z x` by
    (rpt strip_tac >> qpat_assum `ret_pc_ok cenv sa sA` (mp_tac o REWRITE_RULE[ret_pc_ok_def]) >>
     disch_then drule >> simp[]) >>
  `eval_operand op1 sA = SOME (i2w n1) /\ op_prov GA op1 = NONE /\ op_taint tnA op1 = {}` by
    (irule checked_alloc_operand_kept >>
     conj_tac
     >- (qx_gen_tac `l` >> qpat_assum `!l. op1 <> Label l /\ op2 <> Label l`
           (qspec_then `l` strip_assume_tac) >> first_assum ACCEPT_TAC) >>
     qexistsl_tac [`G2`,`t2`,`tn2`,`z`] >> simp[] >> rpt strip_tac >> fs[]) >>
  `eval_operand op2 sA = SOME (i2w n2) /\ op_prov GA op2 = NONE /\ op_taint tnA op2 = {}` by
    (irule checked_alloc_operand_kept >>
     conj_tac
     >- (qx_gen_tac `l` >> qpat_assum `!l. op1 <> Label l /\ op2 <> Label l`
           (qspec_then `l` strip_assume_tac) >> first_assum ACCEPT_TAC) >>
     qexistsl_tac [`G2`,`t2`,`tn2`,`z`] >> simp[] >> rpt strip_tac >> fs[]) >>
  `!x. op1 = Var x \/ op2 = Var x ==>
       op_prov GA (Var x) = NONE /\ op_taint tnA (Var x) = {}` by
    (gen_tac >> disch_then (DISJ_CASES_THEN SUBST_ALL_TAC) >>
     conj_tac >> first_assum ACCEPT_TAC) >>
  `!fn inst u. frag_reachable ctx func sA fn inst u ==> dalloca_fmp_headroom inst u` by
    (qpat_assum `!D. gas_origin_ptr_path _ _ [] (OK sA,_,_)`
       (mp_then (Pos hd) mp_tac gas_origin_ptr_path_dalloca_fmp_headroom o
        Q.SPEC `DF (storage_trace_horizon mid2.storage_trace)`) >>
     qpat_assum `!fn inst u. frag_reachable ctx func t2 fn inst u ==> _`
       (pure_rewrite_tac o single o EQT_INTRO) >> simp[]) >>
  simp_tac std_ss [Abbr `E`,Abbr `Header`,Abbr `R`] >>
  irule (SIMP_RULE (std_ss ++ numSimps.REDUCE_ss) [GSYM arithmeticTheory.ADD_ASSOC]
    (Q.INST [`i` |-> `(k:num) + 2`] range_checked_start_mods)) >>
  qpat_assum `get_instruction _ sA.vs_inst_idx = SOME _` (irule_at Any) >>
  qpat_assum `lookup_block entry_lbl func.fn_blocks = SOME _` (irule_at Any) >>
  qexists_tac `z` >> rpt conj_tac >> first_assum ACCEPT_TAC
QED
Resume range_checked_suffix_join_mods[ready]:
  simp_tac std_ss [Abbr `E`] >> irule gas_outcome_full_mods_post_source >>
  qpat_assum `gas_outcome_full_mods E _ _ _ (range_counter_source _ _ _) _ _ _`
    (irule_at Any o SIMP_RULE std_ss []) >>
  BETA_TAC >> conj_tac
  >- (rpt gen_tac >> strip_tac >>
      qpat_x_assum `res = INL _` SUBST_ALL_TAC >> simp[] >>
      qpat_assum `!tail. range_counter_source _ _ _ _ = _`
        (mp_then (Pos hd) (drule_all_then ACCEPT_TAC) checked_counter_normal_source)) >>
  simp[]
QED
Resume range_checked_suffix_join_mods[rounds]:
  qx_genl_tac [`rs`,`mid`,`G`,`tn`,`t`] >> strip_tac >>
  `valid_horizon cx st0 (storage_trace_horizon mid.storage_trace) mid.storage_trace` by
    (qpat_assum `storage_trace_domain cx st0 mid.storage_trace`
       (ACCEPT_TAC o REWRITE_RULE [vyperStorageFootprintTheory.storage_trace_domain_def])) >>
  qpat_assum `!H. valid_horizon _ _ H mid.storage_trace ==> _ /\ _`
    (drule_then strip_assume_tac) >>
  `~t.vs_halted` by
    (qpat_assum `Header _ _ _ _ _ t` mp_tac >>
     simp_tac std_ss [Abbr `Header`,range_header_mods_def] >>
     strip_tac >> first_assum ACCEPT_TAC) >>
  qpat_x_assum `mid = mid2` SUBST_ALL_TAC >>
  `gas_admissible (eval_for cx tyv id body rs) (stmt_res_ok lctx) mid2` by
    (qpat_assum `_ /\ _ ==> _ = eval_for cx tyv id body _`
       (drule_all_then (fn th => pure_once_rewrite_tac [GSYM th])) >>
     fs[]) >>
  `eval_iterator cx (Range e1 e2) (es with gas_obs := gs1 ++ gs2) =
    (INL rs,mid2 with gas_obs := [])` by
    (qpat_x_assum `rs = GENLIST _ _` SUBST1_TAC >> irule range_iterator_success_mods >>
     reverse conj_tac >- first_assum ACCEPT_TAC >>
     qexists_tac `mid1 with gas_obs := gs2` >> conj_tac
     >- (qpat_assum `!tail. bind (eval_expr cx e1) _ _ = _` (qspec_then `gs2` ACCEPT_TAC)) >>
     qpat_assum `!tail. bind (eval_expr cx e2) _ _ = _`
       (ACCEPT_TAC o REWRITE_RULE [listTheory.APPEND_NIL] o Q.SPEC `[]`)) >>
  `body_for_full_ok_mods mods exps cx tyv id body rs` by suspend "callback" >>
  qpat_assum `!w mid t G tn rs. _ ==> gas_outcome_full_mods _ _ _ _ _ _ _ _` irule >>
  conj_tac
  >- (qexists_tac `w` >> gen_tac >> disch_tac >>
      qpat_assum `!H. valid_horizon _ _ H _ ==> Header H _ _ _ _ _ /\ _`
        (drule_then strip_assume_tac) >>
      qpat_assum `Header _ _ _ _ _ _` mp_tac >> simp_tac std_ss [Abbr `Header`]) >>
  rpt conj_tac >> first_assum ACCEPT_TAC
QED
Resume range_checked_suffix_join_mods[callback]:
  qpat_assum `!tenv s tv t s1 vs t1 s2 u t2. _ ==> body_for_full_ok_mods _ _ _ _ _ _ _` irule >>
  qpat_assum `eval_iterator cx (Range e1 e2) _ = (INL rs,_)` (irule_at Any) >>
  simp[lift_option_type_def,lift_option_def,return_def,check_def,assert_def,
       vyperValueTheory.compatible_bound_def]
QED
Finalise range_checked_suffix_join_mods
