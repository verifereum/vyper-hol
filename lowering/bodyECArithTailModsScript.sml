(* Select the concrete launch and consume that same packet in every exit. *)
Theory bodyECArithTailMods
Ancestors
  bodyECArithStageSelectMods bodyECArithEmptyTailMods bodyECArithAssertExitMods
  bodyECArithHeadSourceMods bodyECArithHeadRunMods bodyECArithSuccessFrameMods
  bodyECArithSuccessRunMods bodyECArithSuccessVVMods
  bodyFullBuiltinECArithSourceMatch vyperCallOutcomeProps vyperStorageTrace
  bodyPtrDefs rich_list list
Libs monadsyntax

Theorem ec_arith_tail_from_staging_mods:
  let staged =
    ?sm res out_alloc gi ci ai gv cv src dst wi wo bb u Gu tnu.
      (do gas <- emit_op GAS [];
          success <- emit_op STATICCALL
            [gas; Lit addr; Var src; Lit an; Var dst; Lit 64w];
          emit_void ASSERT [success]; return (Var dst) od) sm = (res,sb) /\
      vv = StackValue a (Var dst) /\
      gi = mk_inst sm.cs_next_id GAS [] [gv] /\
      ci = mk_inst (sm.cs_next_id+1) STATICCALL
        [Var gv; Lit addr; Var src; Lit an; Var dst; Lit 64w] [cv] /\
      ai = mk_inst (sm.cs_next_id+2) ASSERT [Var cv] [] /\
      emitted_insts sm sb = [gi;ci;ai] /\
      ~u.vs_halted /\ u.vs_current_bb = sm.cs_current_bb /\
      u.vs_inst_idx = LENGTH sm.cs_current_insts /\ alloca_history func u /\
      lookup_block u.vs_current_bb func.fn_blocks = SOME bb /\
      isPREFIX [gi;ci;ai] (DROP u.vs_inst_idx bb.bb_instructions) /\
      (func.fn_name,sm.cs_next_id) NOTIN gas_explicit_sites ctx shadow_ctx /\
      src <> gv /\ dst <> gv /\ dst <> cv /\
      not_fresh_at sm src /\ not_fresh_at sm dst /\
      ~not_fresh_at sm gv /\ ~not_fresh_at sm cv /\
      s2.cs_next_var <= sm.cs_next_var /\ s2.cs_next_id <= sm.cs_next_id /\
      local_ptrs_reserved cenv s2 /\ local_ptrs_reserved cenv sm /\
      (!z sz. cenv.ce_return_buf = SOME (PtrVar (Var z) sz) ==> not_fresh_at sm z) /\
      (!z sz. cenv.ce_return_pc = SOME (PtrVar (Var z) sz) ==> not_fresh_at sm z) /\
      eval_operand (Var src) u = SOME wi /\ eval_operand (Var dst) u = SOME wo /\
      w2n wi + w2n an <= u.vs_alloca_next /\ w2n wo + 64 <= u.vs_alloca_next /\
      lo <= w2n wo /\ t2.vs_alloca_next <= u.vs_alloca_next /\
      allocas_from lo u /\ (ctx_has_dalloca ctx ==> allocas_below_fmp u) /\
      ptr_covers Gu tnu src u (w2n an) /\ ptr_covers Gu tnu dst u 64 /\
      (!i. w2n wi <= i /\ i < w2n wi + w2n an ==> i NOTIN tnu.t_mem) /\
      mem_word_at (w2n wi) u.vs_memory = mem_word_at (w2n p) t2.vs_memory /\
      mem_word_at (w2n wi+32) u.vs_memory = mem_word_at (w2n p+32) t2.vs_memory /\
      (if bt = ECAdd then
         mem_word_at (w2n wi+64) u.vs_memory = mem_word_at (w2n q) t2.vs_memory /\
         mem_word_at (w2n wi+96) u.vs_memory = mem_word_at (w2n q+32) t2.vs_memory
       else mem_word_at (w2n wi+64) u.vs_memory = q) /\
      es2.outcomes = SOME u.vs_outcomes /\
      MEM (mk_inst out_alloc.cs_next_id ALLOCA [Lit 64w] [dst]) (fn_insts func) /\
      FLOOKUP u.vs_allocas out_alloc.cs_next_id = SOME (w2n wo,64) /\
      s2.cs_next_id <= out_alloc.cs_next_id /\ out_alloc.cs_next_id < sb.cs_next_id /\
      (!name b sz. local_region cenv es2.scopes u name b sz ==>
        regions_disjoint (w2n wo) 64 b sz) /\
      (!aid b sz. aid < s2.cs_next_id /\ FLOOKUP u.vs_allocas aid = SOME (b,sz) ==>
        regions_disjoint (w2n wo) 64 b sz) /\
      (cenv.ce_is_ctor ==> !name tv iv off.
        FLOOKUP cenv.ce_module_vars (cenv.ce_module,name) = SOME (ImmutableLoc off) /\
        FLOOKUP (case ALOOKUP es2.immutables cx.txn.target of NONE => FEMPTY
          | SOME imms => get_source_immutables cenv.ce_module imms) name = SOME (tv,iv) ==>
        regions_disjoint (w2n wo) 64 off (type_memory_size tv)) /\
      wb_frame cenv es2 es2 s2 t2 u /\ pure_frame cenv func es2 s2 t2 u /\
      immutable_frame_mods func cenv cx es2 u /\ local_ptrs_rel func cenv es2.scopes u /\
      ghost_kept_at lo cenv es2 s2 G2 tn2 t2 Gu tnu /\
      !H. valid_horizon cx st0 H es2.storage_trace ==>
        gas_origin_ptr_path (DF H,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
          (t2,G2,tn2) [] (OK u,Gu,tnu) /\
        stmt_state_rel H ctx func cenv cx es2 u /\
        ghost_inv_at_mods (DF H) lo d cenv cx es2 Gu tnu u /\
        stor_taint_ok_at (DF H) tnu u
  in
  ((bt = ECAdd ==> staged) /\ (bt = ECMul ==> staged) /\ (bt = ECAdd \/ bt = ECMul)) /\
  MEM func ctx.ctx_functions /\
  addr = (if bt = ECAdd then 6w else 7w) /\
  an = (if bt = ECAdd then 128w else 96w) /\
  a = ArrayT (BaseT (UintT 256)) (Fixed 2) /\
  value_has_type (ArrayTV (BaseTV (UintT 256)) (Fixed 2)) v1 /\
  value_has_type (if bt = ECAdd then ArrayTV (BaseTV (UintT 256)) (Fixed 2)
                  else BaseTV (UintT 256)) v2 /\
  expr_val_rel cx (ArrayT (BaseT (UintT 256)) (Fixed 2)) v1 x t2 /\
  expr_val_rel cx (if bt = ECAdd then ArrayT (BaseT (UintT 256)) (Fixed 2)
                  else BaseT (UintT 256)) v2 y t2 /\
  eval_operand x t2 = SOME p /\ eval_operand y t2 = SOME q /\
  (!tail. bind (eval_expr cx e1) (read_result cx)
    (es with gas_obs := gas_explicit marks1 s0.vs_gas_readings ++ tail) =
      (INL v1,es1 with gas_obs := tail)) /\
  (!tail. bind (eval_expr cx e2) (read_result cx)
    (es1 with gas_obs := gas_explicit marks2 t1.vs_gas_readings ++ tail) =
      (INL v2,es2 with gas_obs := tail)) /\
  es2.gas_obs = [] /\ storage_trace_domain cx st0 es2.storage_trace /\
  local_ptrs_reserved cenv sa /\
  sa.cs_next_var <= s1.cs_next_var /\ s1.cs_next_var <= s2.cs_next_var /\
  sa.cs_next_id <= s1.cs_next_id /\ s1.cs_next_id <= s2.cs_next_id /\
  MAP FDOM es.scopes = MAP FDOM es1.scopes /\ MAP FDOM es1.scopes = MAP FDOM es2.scopes /\
  s0.vs_alloca_next <= t1.vs_alloca_next /\ t1.vs_alloca_next <= t2.vs_alloca_next /\
  (!H. valid_horizon cx st0 H es.storage_trace ==> stmt_state_rel H ctx func cenv cx es s0) /\
  (!H. valid_horizon cx st0 H es1.storage_trace ==>
    expr_post_mods H ctx func cenv cx e1 es sa s1 s0 es1 v1 x t1 /\
    ghost_kept_at lo cenv es sa G0 tn0 s0 G1 tn1) /\
  (!H. valid_horizon cx st0 H es2.storage_trace ==>
    expr_post_mods H ctx func cenv cx e2 es1 s1 s2 t1 es2 v2 y t2 /\
    ghost_kept_at lo cenv es1 s1 G1 tn1 t1 G2 tn2) ==>
  gas_outcome_full_mods (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
    cenv.ce_modules cx st0 (ec_source_tail cx a bt [expr_type e1;expr_type e2] [v1;v2])
    (es2,t2,G2,tn2)
    (\H rr ee G tn t. ?tv. rr = INL tv /\
      vv_post_mods H ctx func cenv cx (Builtin a bt [e1;e2]) es sa sb s0 ee tv vv t /\
      vv_store_bound cx (post_value_type cenv (Builtin a bt [e1;e2]))
        (lowered_value_type cenv (Builtin a bt [e1;e2])) ee tv vv t /\
      t.vs_current_bb = sb.cs_current_bb /\ t.vs_inst_idx = LENGTH sb.cs_current_insts /\
      alloca_history func t /\ (ctx_has_dalloca ctx ==> allocas_below_fmp t) /\
      s0.vs_alloca_next <= t.vs_alloca_next /\ ghost_inv_at_mods (DF H) lo d cenv cx ee G tn t /\
      ptr_vv_ok cx (post_value_type cenv (Builtin a bt [e1;e2])) tv vv ee G tn t /\
      (!v. tv = Value v /\ ~is_word_type (post_value_type cenv (Builtin a bt [e1;e2])) /\
        ~is_bytestring_type (post_value_type cenv (Builtin a bt [e1;e2])) ==>
        vv_own cenv cx (post_value_type cenv (Builtin a bt [e1;e2])) sa sb ee tv vv t /\
        (!ty' p. vv = LocatedValue ty' p ==> p.ptr_location = LocMemory)) /\
      (cenv.ce_is_ctor /\ vv_location vv = SOME LocCode ==>
        ?val. read_result cx tv ee = (INL val,ee) /\
          !rt w. evaluate_type (get_tenv cx) (post_value_type cenv (Builtin a bt [e1;e2])) = SOME rt /\
            eval_operand (vv_operand vv) t = SOME w ==>
            w2n w + type_memory_size rt <= lo /\
            !mem. mem_agree_outside tn.t_mem t.vs_memory mem ==> val_in_memory rt val (w2n w) mem) /\
      (!ty' op. vv = StackValue ty' op /\ ~is_word_type (post_value_type cenv (Builtin a bt [e1;e2])) ==>
        ptr_buf_ok cenv (Builtin a bt [e1;e2]) op G t) /\
      (!ty' p. vv = LocatedValue ty' p /\ p.ptr_location = LocMemory ==>
        ptr_buf_ok cenv (Builtin a bt [e1;e2]) p.ptr_operand G t) /\
      ghost_kept_at lo cenv es sa G0 tn0 s0 G tn)
    (\H rr ee gt r. expr_exit rr r /\ halt_exit H cx ee rr r /\
      (ctx_has_dalloca ctx ==> !s. r = Halt s ==> allocas_below_fmp s))
Proof
  pure_rewrite_tac[LET_THM] >> BETA_TAC >>
  disch_then (CONJUNCTS_THEN2 ASSUME_TAC (map_every assume_tac o CONJUNCTS)) >>
  mp_tac (INST_TYPE [alpha |-> ``:256``] ec_arith_stage_select_mods) >>
  pure_rewrite_tac[LET_THM] >> BETA_TAC >>
  (impl_tac >- first_assum ACCEPT_TAC) >>
  qpat_x_assum `(_ ==> _) /\ (_ ==> _) /\ (_ \/ _)` kall_tac >>
  pure_rewrite_tac[GSYM RIGHT_AND_OVER_OR] >>
  disch_then (CONJUNCTS_THEN2 ASSUME_TAC
    (qx_choosel_then [`sm`,`res`,`out_alloc`,`gi`,`ci`,`ai`,`gv`,`cv`,`src`,`dst`,
      `wi`,`wo`,`bb`,`u`,`Gu`,`tnu`] (map_every assume_tac o CONJUNCTS))) >>
  drule_all_then (qx_choose_then `point_result` (map_every assume_tac o CONJUNCTS))
    ec_arith_staged_source_match >>
  `!H. valid_horizon cx st0 H es2.storage_trace ==>
    gas_origin_ptr_path (DF H,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
      (t2,G2,tn2) [] (OK u,Gu,tnu) /\
    ptr_covers Gu tnu src u (w2n an) /\ ptr_covers Gu tnu dst u 64 /\
    allocas_from lo u /\
    (!i. w2n wi <= i /\ i < w2n wi + w2n an ==> i NOTIN tnu.t_mem) /\
    tnu.t_stor SUBSET (DF H).d_stor u.vs_call_ctx.cc_address
      (u.vs_accounts u.vs_call_ctx.cc_address).storage /\
    tnu.t_trans SUBSET (DF H).d_trans u.vs_call_ctx.cc_address
      (u.vs_transient u.vs_call_ctx.cc_address)` by
    (gen_tac >> disch_tac >>
     qpat_assum `!H. valid_horizon _ _ H _ ==> gas_origin_ptr_path _ _ [] _ /\ _`
       (drule_then (map_every assume_tac o CONJUNCTS)) >>
     fs[stor_taint_ok_at_def]) >>
  Cases_on `u.vs_outcomes = []`
  >- suspend "empty" >>
  suspend "head"
QED

Resume ec_arith_tail_from_staging_mods[empty]:
  `isPREFIX [gi;ci] (DROP u.vs_inst_idx bb.bb_instructions)` by
    (qpat_assum `isPREFIX [gi;ci;ai] _`
       (qx_choose_then `rest` assume_tac o REWRITE_RULE[IS_PREFIX_APPEND]) >>
     pure_rewrite_tac[IS_PREFIX_APPEND] >> qexists_tac `ai::rest` >>
     pure_rewrite_tac[APPEND] >> first_assum (ACCEPT_TAC o PURE_REWRITE_RULE[APPEND])) >>
  MATCH_MP_TAC (Q.INST [`id` |-> `sm.cs_next_id`,
    `explicit` |-> `gas_explicit_sites ctx shadow_ctx`] ec_arith_empty_tail_mods) >>
  rpt conj_tac >> (first_assum ACCEPT_TAC ORELSE simp[])
QED

Resume ec_arith_tail_from_staging_mods[head]:
  `precompile_address bt = w2w addr` by
    (qpat_assum `bt = ECAdd \/ bt = ECMul` DISJ_CASES_TAC >>
     simp[vyperInterpreterTheory.precompile_address_def, wordsTheory.w2w_n2w,
       fcpLib.INDEX_CONV ``dimindex(:160)``]) >>
  `precompile_result (precompile_address bt) (precompile_input bt [v1;v2]) =
    SOME (OPTION_MAP (\(rx,ry). word_to_bytes (n2w rx:bytes32) T ++
      word_to_bytes (n2w ry:bytes32) T) point_result)` by
    (qpat_assum `precompile_address bt = w2w addr` (pure_rewrite_tac o single) >>
     qpat_assum `precompile_input bt [v1;v2] = read_memory _ _ u` (pure_rewrite_tac o single) >>
     qpat_assum `precompile_result (venom_call_request _ _ _ _ _ _).cr_target _ = _`
       mp_tac >>
     simp[NoAsms, venomCallOracleDefsTheory.venom_call_request_def]) >>
  mp_tac (Q.INST [`es` |-> `es2`, `tys` |-> `[expr_type e1;expr_type e2]`]
    ec_arith_head_source_mods) >>
  (impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)) >>
  disch_then (mk_asm "source") >>
  `valid_horizon cx st0 (storage_trace_horizon es2.storage_trace) es2.storage_trace` by
    (fs[vyperStorageFootprintTheory.storage_trace_domain_def]) >>
  qpat_assum `!H. valid_horizon _ _ H _ ==> gas_origin_ptr_path _ _ [] _ /\ ptr_covers _ _ _ _ _ /\ _`
    (drule_then (map_every assume_tac o CONJUNCTS)) >>
  mp_tac (Q.INST [`D` |-> `DF (storage_trace_horizon es2.storage_trace)`,
    `id` |-> `sm.cs_next_id`] ec_arith_head_run_mods) >>
  (impl_tac >- (rpt conj_tac >> (first_assum ACCEPT_TAC ORELSE simp[wordsTheory.dimword_def]))) >>
  disch_then (qx_choosel_then [`sg`,`sc`]
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
      (DISJ_CASES_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (mk_asm "no_success"))))))
  >- suspend "success" >>
  suspend "assert"
QED

Resume ec_arith_tail_from_staging_mods[assert]:
  `?msg ee. ec_source_tail cx a bt [expr_type e1;expr_type e2] [v1;v2] es2 =
      (INR (Error (RuntimeError msg)),ee) /\
    storage_trace_domain cx st0 ee.storage_trace /\
    (!H. valid_horizon cx st0 H ee.storage_trace ==>
         valid_horizon cx st0 H es2.storage_trace)` by
    (Cases_on `point_result` >-
      (asm "source" mp_tac >> simp[] >> disch_tac >>
       qexistsl [`if bt = ECAdd then "ECAdd invalid point" else "ECMul invalid point"`, `es2`] >>
       rpt conj_tac >> simp[]) >>
     qmatch_asmsub_rename_tac `OPTION_MAP _ (SOME point)` >>
     Cases_on `u.vs_outcomes` >- fs[] >>
     rename1 `u.vs_outcomes = co::rest` >>
     `~co.co_success` by
       (asm "no_success" mp_tac >>
        simp[NoAsms] >>
        disch_then (qspecl_then [`FST point`,`SND point`] mp_tac) >> simp[NoAsms]) >>
     asm "source" mp_tac >>
     simp[vyperStorageFootprintTheory.storage_trace_domain_def] >>
     disch_tac >> fs[vyperStorageFootprintTheory.storage_trace_domain_def]) >>
  rename1 `ec_source_tail _ _ _ _ _ _ = (INR (Error (RuntimeError msg)),ee)` >>
  MATCH_MP_TAC (Q.INST [`id` |-> `sm.cs_next_id`, `source_end` |-> `ee`,
    `explicit` |-> `gas_explicit_sites ctx shadow_ctx`] ec_arith_assert_exit_mods) >>
  rpt conj_tac >> first_assum ACCEPT_TAC
QED

Resume ec_arith_tail_from_staging_mods[success]:
  qpat_x_assum `?rx ry co rest raw. _ /\ _ /\ co.co_success /\
      run_inst_seq _ _ = OK raw`
    (qx_choosel_then [`rx`,`ry`,`co`,`rest`,`raw`]
      (map_every assume_tac o CONJUNCTS)) >>
  `((addr = 6w /\ an = 128w) \/ (addr = 7w /\ an = 96w))` by
    (qpat_assum `bt = ECAdd \/ bt = ECMul` DISJ_CASES_TAC >> simp[]) >>
  qabbrev_tac `data = word_to_bytes (n2w rx:bytes32) T ++ word_to_bytes (n2w ry:bytes32) T` >>
  `precompile_result (venom_call_request u addr 0w wi an T).cr_target
    (venom_call_request u addr 0w wi an T).cr_data = SOME (SOME data)` by
    (qpat_assum `precompile_result (venom_call_request _ _ _ _ _ _).cr_target _ = _`
      mp_tac >> simp[Abbr `data`]) >>
  `!H. valid_horizon cx st0 H es2.storage_trace ==>
    stmt_state_rel H ctx func cenv cx es2 u /\ stor_taint_ok_at (DF H) tnu u` by
    (rpt strip_tac >>
     qpat_assum `!H. valid_horizon _ _ H _ ==> gas_origin_ptr_path _ _ [] _ /\ stmt_state_rel _ _ _ _ _ _ _ /\ _`
       (drule_then (map_every assume_tac o CONJUNCTS)) >> first_assum ACCEPT_TAC) >>
  mp_tac (Q.INST [`id` |-> `sm.cs_next_id`, `sf` |-> `s2`, `es` |-> `es2`,
    `s` |-> `u`, `u` |-> `sg`, `v` |-> `sc`, `q` |-> `raw`, `G` |-> `Gu`, `tn` |-> `tnu`,
    `explicit` |-> `gas_explicit_sites ctx shadow_ctx`] ec_arith_success_run_mods) >>
  (impl_tac >- (rpt conj_tac >> (first_assum ACCEPT_TAC ORELSE simp[Abbr `data`]))) >>
  pure_rewrite_tac[LET_THM] >> BETA_TAC >>
  disch_then (REPEAT_TCL CHOOSE_THEN (map_every assume_tac o CONJUNCTS)) >>
  rename1 `t = raw with vs_inst_idx := u.vs_inst_idx + 3` >>
  qmatch_asmsub_rename_tac `(OK t,Gfin,tnfin)` >>
  qabbrev_tac `ee = SND (take_call_outcome NONE (w2w addr) (read_memory (w2n wi) (w2n an) u) NONE es2)` >>
  `ec_source_tail cx a bt [expr_type e1;expr_type e2] [v1;v2] es2 =
     (INL (Value (mk_ec_result (rx,ry))), ee)` by
    (asm "source" mp_tac >> simp[Abbr `ee`]) >>
  `ee.gas_obs = [] /\ ee.scopes = es2.scopes /\ ee.accounts = es2.accounts /\
   ee.tStorage = es2.tStorage /\ storage_trace_domain cx st0 ee.storage_trace /\
   (!H. valid_horizon cx st0 H ee.storage_trace <=> valid_horizon cx st0 H es2.storage_trace)` by
    (simp[Abbr `ee`, vyperStorageFootprintTheory.storage_trace_domain_def] >>
     fs[vyperStorageFootprintTheory.storage_trace_domain_def]) >>
  `computed_precompile (venom_call_request u addr 0w wi an T)` by
    simp[extCallOracleTheory.computed_precompile_def,
         venomCallOracleDefsTheory.venom_call_request_def] >>
  `64 <= LENGTH data` by simp[Abbr `data`, byteTheory.LENGTH_word_to_bytes, wordsTheory.dimword_def] >>
  `gas_explicit [F] t2.vs_gas_readings = []` by
    (Cases_on `t2.vs_gas_readings` >> simp[gasSummaryTheory.gas_explicit_cons]) >>
  pure_rewrite_tac[gasOutcomeFullModsTheory.gas_outcome_full_mods_def] >>
  qexists_tac `[F]` >> disj2_tac >> disj1_tac >>
  qexistsl [`INL (Value (mk_ec_result (rx,ry)))`,`ee`,`OK t`,`Gfin`,`tnfin`] >>
  (conj_tac >-
    (qpat_assum `gas_explicit [F] _ = []` (pure_rewrite_tac o single) >>
     rewrite_tac[APPEND] >> gen_tac >>
     irule exprSimECArithTheory.ec_source_tail_gas_obs >>
     conj_tac >> first_assum ACCEPT_TAC)) >>
  (conj_tac >- first_assum ACCEPT_TAC) >>
  rpt gen_tac >> disch_tac >>
  `valid_horizon cx st0 H es2.storage_trace` by
    (qpat_assum `!h. valid_horizon _ _ h ee.storage_trace <=> _`
      (qspec_then `H` (pure_rewrite_tac o single o GSYM)) >> first_assum ACCEPT_TAC) >>
  qpat_assum `!H. valid_horizon _ _ H es2.storage_trace ==>
      gas_origin_ptr_path _ _ [] _ /\ stmt_state_rel _ _ _ _ _ _ _ /\ _`
    (qspec_then `H` mp_tac) >>
  (impl_tac >- first_assum ACCEPT_TAC) >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  qpat_assum `!H. valid_horizon _ _ H _ ==> gas_origin_ptr_path _ _ [F] _ /\ _`
    (qspec_then `H` mp_tac) >>
  (impl_tac >- first_assum ACCEPT_TAC) >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  (conj_tac >-
    (qpat_assum `gas_origin_ptr_path _ (t2,G2,tn2) [] _`
       (mp_tac o MATCH_MP fragGasOriginPtrTheory.gas_origin_ptr_path_append) >>
     simp[NoAsms] >> disch_then drule >> simp[NoAsms])) >>
  disj1_tac >> qexists_tac `t` >> BETA_TAC >>
  pure_rewrite_tac[venomExecSemanticsTheory.exec_result_11] >>
  (conj_tac >- REFL_TAC) >>
  `ee with gas_obs := [] = ee` by simp[vyperStateTheory.evaluation_state_component_equality] >>
  qpat_assum `ee with gas_obs := [] = ee` (pure_rewrite_tac o single) >>
  suspend "success_vv"
QED

Resume ec_arith_tail_from_staging_mods[success_vv]:
  markerLib.RESUME_TAC >>
  mp_tac (Q.INST [`id` |-> `sm.cs_next_id`, `sf` |-> `s2`, `es` |-> `es2`,
    `s` |-> `u`, `q` |-> `raw`, `G` |-> `Gu`, `tn` |-> `tnu`,
    `G2` |-> `Gfin`, `tn2` |-> `tnfin`, `ce` |-> `cenv`,
    `D` |-> `DF (H:(bool # bytes32 # type_value) list # num list)`,
    `out` |-> `mk_inst out_alloc.cs_next_id ALLOCA [Lit 64w] [dst]`]
      ec_arith_success_frame_mods) >>
  (impl_tac >- (rpt conj_tac >> (first_assum ACCEPT_TAC ORELSE simp[venomInstTheory.mk_inst_def]))) >>
  pure_rewrite_tac[LET_THM] >> BETA_TAC >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `!e. storage_trace_frame (bind (eval_expr cx e) (read_result cx))` by
    (gen_tac >> irule storage_trace_frame_bind_all >>
     simp[storage_trace_frame_read_result, cj 5 evaluate_storage_trace_frame]) >>
  `valid_horizon cx st0 H es1.storage_trace` by
    (qpat_assum `!tail. bind (eval_expr cx e2) _ _ = _`
       (qspec_then `[]` (mp_then (Pos last) mp_tac storage_trace_frame_prefix)) >>
     (impl_tac >- simp[]) >> simp[NoAsms] >>
     disch_then (qx_choose_then `obs` (fn eq =>
       qpat_assum `valid_horizon cx st0 H es2.storage_trace` (mp_tac o PURE_REWRITE_RULE[eq]))) >>
     disch_then (mp_then Any ACCEPT_TAC gasOutcomeFullTheory.valid_horizon_append)) >>
  `valid_horizon cx st0 H es.storage_trace` by
    (qpat_assum `!tail. bind (eval_expr cx e1) _ _ = _`
       (qspec_then `[]` (mp_then (Pos last) mp_tac storage_trace_frame_prefix)) >>
     (impl_tac >- simp[]) >> simp[NoAsms] >>
     disch_then (qx_choose_then `obs` (fn eq =>
       qpat_assum `valid_horizon cx st0 H es1.storage_trace` (mp_tac o PURE_REWRITE_RULE[eq]))) >>
     disch_then (mp_then Any ACCEPT_TAC gasOutcomeFullTheory.valid_horizon_append)) >>
  qpat_assum `!h. valid_horizon _ _ h es.storage_trace ==> stmt_state_rel _ _ _ _ _ _ _`
    (qspec_then `H` mp_tac) >>
  (impl_tac >- first_assum ACCEPT_TAC) >> disch_tac >>
  qpat_assum `!h. valid_horizon _ _ h es1.storage_trace ==> expr_post_mods _ _ _ _ _ _ _ _ _ _ _ _ _ _ /\ _`
    (qspec_then `H` mp_tac) >>
  (impl_tac >- first_assum ACCEPT_TAC) >> strip_tac >>
  qpat_assum `!h. valid_horizon _ _ h es2.storage_trace ==> expr_post_mods _ _ _ _ _ _ _ _ _ _ _ _ _ _ /\ _`
    (qspec_then `H` mp_tac) >>
  (impl_tac >- first_assum ACCEPT_TAC) >> strip_tac >>
  MATCH_MP_TAC (Q.INST [`G` |-> `Gfin`, `tn` |-> `tnfin`] ec_arith_success_vv_mods) >>
  rpt conj_tac >> (first_assum ACCEPT_TAC ORELSE simp[Abbr `ee`, Abbr `data`])
QED

Finalise ec_arith_tail_from_staging_mods
