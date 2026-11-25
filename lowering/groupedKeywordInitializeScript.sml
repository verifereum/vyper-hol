(* Run the omitted suffix of a selected grouped entry initializer. *)
Theory groupedKeywordInitialize
Ancestors
  groupedDefaultCode groupedDefaultEvaluation groupedKeywordOmitted
  bodyFullIfExpReach bodyFullPreds exprBodyPreProps
  exprSimSource exprSimDefs exprSimFullBundleProps exprSimWordArgs
  exprSimProps stmtSimProps valueEncoding ptrDiscipline
  loweringPosts loweringStateRelDefs bodyPtrDefs freshWrites valueEncodingTyping
  gasOutcomeFull gasOutcomeFullCompose fragGasOriginPtr
  vyperInterpreter vyperState vyperStorageFootprint vyperStorageTrace
  exprLoweringProps moduleLowering compileEnv venomState vyperValue finite_map words list pair
  groupedKeywordSupplied calldataSourceSize vyperCalldata
  selectedAcceptedFold fragGasOriginPtrLoop venomMemDefs entryCreateDefaultSlotContinue

val allocated_slot = ``\sa s G tn (aid,p,base,tv).
  aid < sa.cs_next_id /\ not_fresh_at sa p /\ base < dimword (:256) /\
  FLOOKUP s.vs_allocas aid = SOME (base,type_memory_size tv) /\
  lookup_var p s = SOME (n2w base) /\ ptr_covers G tn p s (type_memory_size tv)``;

val initialized_slot = ``\sa s G tn (aid,p,base,tv,v).
  ^allocated_slot sa s G tn (aid,p,base,tv) /\ value_has_type tv v /\
  (!mem. mem_agree_outside tn.t_mem s.vs_memory mem ==> val_in_memory tv v base mem)``;

val grouped_initializer_slot_tac = fn row =>
  mp_tac (SIMP_RULE (srw_ss()) []
    (Q.INST [`sb` |-> `last`, `t` |-> `tail_state`, `J` |-> `G1`,
      `tz` |-> `tn1`, `slot` |-> row] (SPEC_ALL grouped_initializer_allocated_slot_kept))) >>
  asm_rewrite_tac[];

Theorem grouped_initializer_head_exit[local]:
  (\H (res:value + exception) ee gt r. expr_exit res r /\ halt_exit H cx ee res r /\
    (ctx_has_dalloca ctx ==> !s. r = Halt s ==> allocas_below_fmp s)) =
  (\H res ee gt r. ?ex. res = INR ex /\ expr_exit (INR ex:value list + exception) r /\
    halt_exit H cx ee (INR ex:value list + exception) r /\
    (ctx_has_dalloca ctx ==> !s. r = Halt s ==> allocas_below_fmp s))
Proof
  simp[FUN_EQ_THM] >> rpt gen_tac >> Cases_on `res` >>
  simp[expr_exit_INR_type, halt_exit_def]
QED

Theorem grouped_omitted_initializers:
  !vars slots kept sa sha es s G tn.
    compile_init_kwargs ce vars off 0 hi sa = ((),sb) /\
    compile_init_kwargs (gas_shadow_env T ce)
      (MAP (\(n,p,ty,e). (n,p,ty,gas_shadow_expr e)) vars)
      off 0 hi sha = ((),shb) /\
    fn_has_code sa sb fn /\ fn_has_code sha shb shfn /\ gas_shadow_state sa sha /\
    LIST_REL (\(n,dst,ty,e) (aid,p,base,tv).
      dst = Var p /\ runtime_constant_expr mods e /\ expr_type e = ty /\
      (!es'. expr_sim_inv (ce with ce_vars := FEMPTY) cx env es' ==>
        expr_body_pre (ce with ce_vars := FEMPTY) cx env e es') /\
      lower_value compile_expr (ce with ce_vars := FEMPTY) ty e =
        lower_value compile_expr ce ty e /\
      lower_value compile_expr (gas_shadow_env T (ce with ce_vars := FEMPTY))
        ty (gas_shadow_expr e) =
        lower_value compile_expr (gas_shadow_env T ce) ty (gas_shadow_expr e) /\
      evaluate_type (get_tenv cx) ty = SOME tv /\
      type_memory_bytes ce ty = type_memory_size tv /\
      type_memory_size tv + 64 < dimword (:256)) vars slots /\
    EVERY (^allocated_slot sa s G tn) slots /\
    EVERY (^initialized_slot sa s G tn) kept /\
    ALL_DISTINCT (MAP FST slots ++ MAP FST kept) /\
    body_inv tops ctx (ce with ce_vars := FEMPTY) cx /\ shadow_body_inv tops ctx shadow_ctx /\
    body_const_cells_agree [(NONE,tops)] cx env es /\
    env.type_defs = get_tenv cx /\ ~ce.ce_is_ctor /\ ce.ce_imm_alloca = NONE /\
    ce.ce_return_pc = NONE /\ ce.ce_return_buf = NONE /\
    gas_shadow_context ctx shadow_ctx /\ ctx_inst_ids_distinct ctx /\
    gas_shadow_function fn shfn /\ MEM fn ctx.ctx_functions /\ MEM shfn shadow_ctx.ctx_functions /\
    fn_inst_ids_distinct fn /\
    (!bb. MEM bb fn.fn_blocks ==> phi_prefix_length bb.bb_instructions = 0) /\
    (!H. dead_lo_ok H (DF H) 0 (ce with ce_vars := FEMPTY) cx) /\
    (!H. valid_horizon cx st0 H es.storage_trace ==>
      stmt_state_rel H ctx fn (ce with ce_vars := FEMPTY) cx es s /\
      storage_well_formed_on cx es (FST H) /\
      ghost_inv_at (DF H) 0 NONE (ce with ce_vars := FEMPTY) cx es G tn s) /\
    expr_sim_inv (ce with ce_vars := FEMPTY) cx env es /\
    alloca_history fn s /\ (ctx_has_dalloca ctx ==> allocas_below_fmp s) /\
    (!f inst u. frag_reachable ctx fn s f inst u ==> dalloca_fmp_headroom inst u) /\
    ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
    s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
    gas_outcome_full (DF,0,gas_explicit_sites ctx shadow_ctx,ctx,fn,PG)
      (cx_tops cx) cx st0 (eval_exprs cx (MAP (\(_,_,_,e). e) vars)) (es,s,G,tn)
      (\H res ee J tz u. ?values.
        res = INL values /\
        LIST_REL (\(aid,p,base,tv) v. ^initialized_slot sb u J tz (aid,p,base,tv,v))
          slots values /\
        EVERY (^initialized_slot sb u J tz) kept /\
        stmt_state_rel H ctx fn (ce with ce_vars := FEMPTY) cx ee u /\
        storage_well_formed_on cx ee (FST H) /\
        ghost_inv_at (DF H) 0 NONE (ce with ce_vars := FEMPTY) cx ee J tz u /\
        ee.scopes = es.scopes /\ alloca_history fn u /\
        (ctx_has_dalloca ctx ==> allocas_below_fmp u) /\
        ~u.vs_halted /\ u.vs_current_bb = sb.cs_current_bb /\
        u.vs_inst_idx = LENGTH sb.cs_current_insts)
      (\H res ee gt r. ?ex. res = INR ex /\ expr_exit (INR ex:value list + exception) r /\
        halt_exit H cx ee (INR ex:value list + exception) r /\
        (ctx_has_dalloca ctx ==> !u. r = Halt u ==> allocas_below_fmp u))
Proof
  Induct
  >- suspend "nil" >>
  suspend "cons"
QED

Resume grouped_omitted_initializers[nil]:
  Cases_on `slots` >> simp[compile_init_kwargs_def, comp_return_def] >>
  rpt gen_tac >> strip_tac >> gvs[] >>
  irule gas_outcome_full_pure >>
  conj_tac >-
    (qexistsl_tac [`G`,`es`,`INL ([]:value list)`,`s`,`tn`] >>
     simp[eval_exprs_nil, return_def, gas_origin_ptr_path_rules] >>
     gen_tac >> strip_tac >> first_x_assum drule >> strip_tac >>
     simp[stmt_state_rel_start_gas_obs] >>
     `storage_well_formed_on cx (es with gas_obs := []) (FST H) <=>
       storage_well_formed_on cx es (FST H)` by
       (irule storage_well_formed_on_backends >> simp[]) >>
     fs[ghost_inv_at_def]) >>
  first_assum ACCEPT_TAC
QED

Resume grouped_omitted_initializers[cons]:
  gen_tac >> PairCases_on `h` >> gen_tac >> Cases_on `slots`
  >- simp[] >>
  PairCases_on `h` >> simp[] >>
  rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
  qpat_x_assum `_ = Var _` SUBST_ALL_TAC >>
  rename1 `compile_init_kwargs ce ((name,Var p,ty,e)::vars) off 0 hi sa = _` >>
  rename1 `aid < sa.cs_next_id` >>
  rename1 `evaluate_type (get_tenv cx) ty = SOME kw_tv` >>
  mp_tac (SPEC_ALL grouped_initializer_head_inputs) >>
  (impl_tac >- asm_rewrite_tac[]) >>
  disch_then (qx_choosel_then [`op`,`mid`,`last`,`shmid`,`shlast`] strip_assume_tac) >>
  `w2n (n2w h2':256 word) = h2'` by simp[wordsTheory.w2n_n2w] >>
  mp_tac (Q.INST [`dst` |-> `p`, `b` |-> `n2w h2':256 word`,
    `oid` |-> `aid`, `tv` |-> `kw_tv`, `shadow_fn` |-> `shfn`, `src` |-> `op`]
    (SPEC_ALL grouped_keyword_omitted_expression)) >>
  impl_tac >- fs[] >> strip_tac >>
  qpat_assum `gas_outcome_full _ _ _ _ (bind (eval_expr _ _) _) _ _ _`
    (fn result =>
       let
         val head = REWRITE_RULE [grouped_initializer_head_exit] result
         val args = snd (strip_comb (concl head))
         val (binders,body) = strip_abs (List.nth (args,6))
         val (v,post) = dest_exists body
         val P = list_mk_abs (hd binders :: v :: List.drop (binders,2),snd (dest_conj post))
         val (exit_binders,exit_body) = strip_abs (List.nth (args,7))
         val (ex,exit_post) = dest_exists exit_body
         val R = list_mk_abs (hd exit_binders :: ex :: List.drop (exit_binders,2),
           snd (dest_conj exit_post))
         val compose = BETA_RULE (Q.INST [`P` |-> `^P`,`R` |-> `^R`]
           grouped_default_exprs_cons_outcome)
       in
         ho_match_mp_tac compose >> conj_tac >- ACCEPT_TAC head
       end) >>
  qx_genl_tac [`marks`,`v`,`ee`,`G1`,`tn1`,`tail_state`] >> BETA_TAC >> strip_tac >>
  qpat_assum `w2n (n2w h2':256 word) = h2'`
    (RULE_ASSUM_TAC o PURE_REWRITE_RULE o single) >>
  mp_tac (Q.INST [`slots` |-> `t`, `b0` |-> `h2'`, `tv` |-> `kw_tv`,
    `explicit` |-> `gas_explicit_sites ctx shadow_ctx`]
    (SPEC_ALL grouped_initializer_tail_inputs)) >>
  (impl_tac >-
    (fs[] >> reverse conj_tac >- first_assum ACCEPT_TAC >>
     gen_tac >> disch_tac >>
     qpat_assum `!H. valid_horizon _ _ H ee.storage_trace ==> _`
       (qspec_then `H` (drule_then strip_assume_tac)) >>
     asm_rewrite_tac[])) >>
  disch_then (strip_assume_tac o SIMP_RULE (srw_ss()) []) >>
  qpat_assum `!slots kept sa sha es s G tn. compile_init_kwargs _ vars _ _ _ _ = _ /\ _ ==> _`
    (qspecl_then [`t`,`(aid,p,h2',kw_tv,v)::kept`,`last`,`shlast`,`ee`,
       `tail_state`,`G1`,`tn1`] mp_tac) >>
  (impl_tac >-
    (simp_tac (srw_ss()) [] >> rpt conj_tac >> first_assum ACCEPT_TAC)) >>
  strip_tac >> irule gas_outcome_full_post_mono >>
  goal_assum (drule_at Any) >>
  qpat_assum `ee.scopes = es.scopes` mp_tac >>
  POP_ASSUM_LIST (K all_tac) >>
  disch_tac >> conj_tac
  >- (rpt gen_tac >> BETA_TAC >>
      disch_then (qx_choose_then `values`
        (strip_assume_tac o SIMP_RULE (srw_ss()) [])) >>
      qexists_tac `values` >> simp[]) >>
  rpt gen_tac >> BETA_TAC >> simp_tac bool_ss []
QED

Finalise grouped_omitted_initializers

Theorem grouped_supplied_initializers:
  !tvs vars slots vals kept off sa sha s G tn.
    compile_init_kwargs ce vars (4+off) (LENGTH tvs) hi sa = ((),sb) /\
    compile_init_kwargs (gas_shadow_env T ce)
      (MAP (\(n,p,ty,e). (n,p,ty,gas_shadow_expr e)) vars)
      (4+off) (LENGTH tvs) hi sha = ((),shb) /\
    fn_has_code sa sb fn /\ fn_has_code sha shb shfn /\ gas_shadow_state sa sha /\
    LIST_REL (\(n,dst,ty,e) (aid,p,base,tv).
      dst = Var p /\ abi_decoder_coherent ce env ce.ce_struct_fields ty tv /\
      is_abi_dynamic ce.ce_struct_fields ty = tv_abi_dynamic tv /\
      base+type_memory_size tv < dimword (:256)) vars slots /\
    tvs = MAP (\(_,_,_,tv). tv) (TAKE (LENGTH tvs) slots) /\
    calldata_decode_args s.vs_call_ctx.cc_calldata tvs off = SOME vals /\
    4+off+SUM (MAP tv_abi_size tvs) < dimword (:256) /\
    EVERY (^allocated_slot sa s G tn) slots /\
    EVERY (^initialized_slot sa s G tn) kept /\
    ALL_DISTINCT (MAP FST slots ++ MAP FST kept) /\
    selected_registration_resources ctx fn site lo sa s /\
    (ctx_has_dalloca ctx ==> allocas_below_fmp s /\
      s.vs_alloca_next + pending_alloca_size fn s <= w2n s.vs_initial_fmp) /\
    unit_alloca_budget ctx < dimword (:256) /\ fn_inst_ids_distinct fn /\
    (!label bb. lookup_block label fn.fn_blocks = SOME bb ==>
      phi_prefix_length bb.bb_instructions = 0) ==>
    ?last shlast t J tz.
      compile_init_kwargs ce (DROP (LENGTH tvs) vars)
        (4+off+SUM (MAP tv_abi_size tvs)) 0 hi last = ((),sb) /\
      compile_init_kwargs (gas_shadow_env T ce)
        (MAP (\(n,p,ty,e). (n,p,ty,gas_shadow_expr e)) (DROP (LENGTH tvs) vars))
        (4+off+SUM (MAP tv_abi_size tvs)) 0 hi shlast = ((),shb) /\
      fn_has_code last sb fn /\ fn_has_code shlast shb shfn /\ gas_shadow_state last shlast /\
      selected_registration_resources ctx fn site lo last t /\
      (ctx_has_dalloca ctx ==> allocas_below_fmp t /\
        t.vs_alloca_next + pending_alloca_size fn t <= w2n t.vs_initial_fmp) /\
      EVERY (^allocated_slot last t J tz) (DROP (LENGTH tvs) slots) /\
      LIST_REL (\(aid,p,base,tv) v. ^initialized_slot last t J tz (aid,p,base,tv,v))
        (TAKE (LENGTH tvs) slots) vals /\
      EVERY (^initialized_slot last t J tz) kept /\
      selected_registration_frame s tn t tz /\ tz.t_mem SUBSET tn.t_mem /\
      (!D exp. gas_origin_ptr_path (D,lo,exp,ctx,fn,PG) (s,G,tn) [] (OK t,J,tz))
Proof
  Induct
  >- suspend "nil" >>
  suspend "cons"
QED

Resume grouped_supplied_initializers[nil]:
  simp[calldata_decode_args_def] >> rpt gen_tac >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  qexistsl_tac [`sa`,`sha`,`s`,`G`,`tn`] >>
  asm_rewrite_tac[] >>
  simp[selected_registration_frame_def, gas_origin_ptr_path_rules] >>
  rpt gen_tac >> irule (cj 1 gas_origin_ptr_path_rules) >> fs[selected_registration_resources_def]
QED

Resume grouped_supplied_initializers[cons]:
  qx_genl_tac [`h`,`vars`,`slots`] >> Cases_on `slots` >- simp[] >>
  Cases_on `vars` >- simp[] >>
  PairCases_on `h'` >> PairCases_on `h''` >>
  simp_tac bool_ss [listTheory.LENGTH, listTheory.MAP, listTheory.LIST_REL_def,
    rich_listTheory.DROP, rich_listTheory.TAKE, listTheory.EVERY_DEF, listTheory.CONS_11,
    listTheory.ALL_DISTINCT, listTheory.APPEND, listTheory.SUM, pairTheory.FST,
    listTheory.MEM_APPEND, boolTheory.DE_MORGAN_THM,
    arithmeticTheory.ADD_ASSOC, pairTheory.UNCURRY, pairTheory.SND] >>
  rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
  qpat_x_assum `_ = Var _` SUBST_ALL_TAC >>
  qpat_x_assum `h = _` SUBST_ALL_TAC >>
  rename1 `compile_init_kwargs ce ((name,Var p,ty,e)::var_tail) _ _ hi sa = _` >>
  rename1 `LIST_REL _ var_tail slot_tail` >>
  qpat_x_assum `tvs = MAP _ _` (assume_tac o SYM) >>
  rename1 `abi_decoder_coherent ce env ce.ce_struct_fields ty tv` >>
  rename1 `FLOOKUP s.vs_allocas aid = SOME (b0, type_memory_size tv)` >>
  `?x xs. vals = x::xs` by
    (qpat_assum `calldata_decode_args _ (_::_) off = SOME vals` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >> simp[calldata_decode_args_def] >>
     rpt (BasicProvers.TOP_CASE_TAC >> simp[]) >> metis_tac[]) >>
  qpat_x_assum `vals = x::xs` SUBST_ALL_TAC >>
  qpat_assum `selected_registration_resources _ _ _ _ _ _`
    (strip_assume_tac o REWRITE_RULE [selected_registration_resources_def]) >>
  `4+off < dimword (:256)` by decide_tac >>
  mp_tac (Q.INST [`dst` |-> `p`,`d` |-> `b0`,`oid` |-> `aid`,
    `vars` |-> `var_tail`, `k` |-> `SUC (LENGTH tvs)`]
    (SPEC_ALL grouped_keyword_decode_supplied_with_frame)) >>
  impl_tac >- asm_rewrite_tac[arithmeticTheory.SUC_POS] >>
  disch_then (qx_choosel_then [`src`,`mid`,`first`,`last`,`tail_state`,`G1`,`tn1`,`scratch`]
    (map_every assume_tac o CONJUNCTS)) >>
  `abi_embedded_static_size ce.ce_struct_fields ty = tv_abi_size tv` by
    (qpat_assum `abi_decoder_coherent ce env ce.ce_struct_fields ty tv`
       (ACCEPT_TAC o MATCH_MP calldata_coherent_embedded_size)) >>
  mp_tac (Q.INST [`dst` |-> `Var p`,`off` |-> `4+off`,`vars` |-> `var_tail`,
    `k` |-> `SUC (LENGTH (tvs:type_value list))`]
    (SPEC_ALL grouped_supplied_initializer_shadow)) >>
  impl_tac >- asm_rewrite_tac[arithmeticTheory.SUC_POS] >>
  disch_then (qx_choose_then `shadow_last` strip_assume_tac) >>
  suspend "owners"
QED

Resume grouped_supplied_initializers[owners]:
  `!q w. not_fresh_at sa q /\ lookup_var q s = SOME w ==>
    lookup_var q tail_state = SOME w /\ FLOOKUP G1 q = FLOOKUP G q /\
    op_taint tn1 (Var q) = op_taint tn (Var q)` by
    (rpt gen_tac >> strip_tac >>
     qpat_assum `!q. not_fresh_at sa q ==> _`
       (qspec_then `q` (drule_then strip_assume_tac)) >> asm_rewrite_tac[]) >>
  `^allocated_slot sa s G tn (aid,p,b0,tv)` by simp[] >>
  `^allocated_slot last tail_state G1 tn1 (aid,p,b0,tv)` by
    (grouped_initializer_slot_tac `(aid,p,b0,tv)` >> simp[]) >>
  qpat_assum `^allocated_slot last tail_state G1 tn1 (aid,p,b0,tv)`
    (strip_assume_tac o SIMP_RULE (srw_ss()) []) >>
  `^initialized_slot last tail_state G1 tn1 (aid,p,b0,tv,x)` by simp[] >>
  `EVERY (^allocated_slot last tail_state G1 tn1) slot_tail` by
    (qpat_assum `EVERY _ slot_tail` mp_tac >>
     simp_tac bool_ss [EVERY_MEM] >> strip_tac >> qx_gen_tac `row` >> strip_tac >>
     qpat_assum `!y. MEM y slot_tail ==> _` (qspec_then `row` (drule_then assume_tac)) >>
     grouped_initializer_slot_tac `row` >> simp[]) >>
  `EVERY (^initialized_slot last tail_state G1 tn1) kept` by
    (qpat_assum `EVERY _ kept` mp_tac >>
     simp_tac bool_ss [EVERY_MEM] >> strip_tac >>
     qx_gen_tac `row` >> PairCases_on `row` >> strip_tac >>
     qpat_assum `!row. MEM row kept ==> _`
       (qspec_then `(row0,row1,row2,row3,row4)` (drule_then mp_tac)) >>
     simp_tac (srw_ss()) [] >> strip_tac >>
     `MEM row0 (MAP FST kept)` by
       (simp_tac bool_ss [MEM_MAP] >> qexists_tac `(row0,row1,row2,row3,row4)` >> simp[]) >>
     `row0 <> aid` by metis_tac[] >>
     `val_wf row3 row4` by (irule (cj 1 value_has_type_val_wf) >> first_assum ACCEPT_TAC) >>
     `val_footprint row3 row4 <= type_memory_size row3` by simp[val_footprint_le] >>
     conj_tac
     >- (grouped_initializer_slot_tac `(row0,row1,row2,row3)` >> simp[]) >>
     simp_tac bool_ss [value_has_type_val_wf] >>
     qpat_assum `value_has_type row3 row4` (fn th => rewrite_tac[th]) >>
     mp_tac (Q.INST [`t` |-> `tail_state`,`oid` |-> `row0`,`b` |-> `row2`,
       `n` |-> `type_memory_size row3`,`did` |-> `aid`,`d` |-> `b0`,
       `sz` |-> `type_memory_size tv`,`tn'` |-> `tn1`,`tv` |-> `row3`,
       `v` |-> `row4`] (SPEC_ALL grouped_keyword_decode_owner_frame)) >>
     impl_tac
     >- (asm_rewrite_tac[] >> conj_tac
         >- (qpat_assum `FLOOKUP s.vs_allocas row0 = SOME (row2,type_memory_size row3)`
               (fn row => qpat_assum `!id entry. FLOOKUP s.vs_allocas id = SOME entry ==>
                  FLOOKUP tail_state.vs_allocas id = SOME entry`
                 (fn th => ACCEPT_TAC (MATCH_MP (SPEC_ALL th) row)))) >>
         rpt gen_tac >> strip_tac >>
         qpat_assum `!b n. MEM (b,n) scratch ==> _`
           (drule_then (qx_choose_then `id` strip_assume_tac)) >>
         qexists_tac `id` >> asm_rewrite_tac[] >> decide_tac) >>
     disch_then ACCEPT_TAC) >>
  `ALL_DISTINCT (MAP FST slot_tail ++ MAP FST ((aid,p,b0,tv,x)::kept))` by
    (MAP_EVERY (fn pat => qpat_assum pat mp_tac)
       [`ALL_DISTINCT (MAP FST slot_tail ++ MAP FST kept)`,
        `~MEM aid (MAP FST slot_tail)`,`~MEM aid (MAP FST kept)`] >>
     POP_ASSUM_LIST (K all_tac) >> simp[ALL_DISTINCT_APPEND] >> metis_tac[]) >>
  `selected_registration_resources ctx fn site lo last tail_state` by
    (pure_rewrite_tac [selected_registration_resources_def] >>
     conj_tac >- first_assum ACCEPT_TAC >>
     conj_tac
     >- (qpat_assum `!inst w b n. MEM inst (fn_insts fn) /\ _ /\ _ /\
                  FLOOKUP s.vs_allocas inst.inst_id = SOME (b,n) ==> _`
           (fn old => qpat_assum
             `(!inst w b n. MEM inst (fn_insts fn) /\ _ /\ _ /\
               FLOOKUP s.vs_allocas inst.inst_id = SOME (b,n) ==> _) ==> _`
             (fn th => ACCEPT_TAC (MATCH_MP th old)))) >>
     `lo <= tail_state.vs_alloca_next` by decide_tac >>
     asm_rewrite_tac[]) >>
  `selected_registration_frame s tn tail_state tn1` by
    asm_rewrite_tac[selected_registration_frame_def] >>
  `4 + (off + tv_abi_size tv) + SUM (MAP tv_abi_size tvs) < dimword (:256)` by decide_tac >>
  qpat_assum `abi_embedded_static_size ce.ce_struct_fields ty = tv_abi_size tv`
    (fn size_eq => MAP_EVERY (fn pattern =>
       qpat_assum pattern (assume_tac o SIMP_RULE bool_ss
         [size_eq,arithmeticTheory.SUC_SUB1,arithmeticTheory.ADD_ASSOC]))
       [`compile_init_kwargs ce var_tail _ _ hi last = _`,
        `compile_init_kwargs _ (MAP _ var_tail) _ _ hi shadow_last = _`]) >>
  qpat_assum `!vars slots vals kept off sa sha s G tn. compile_init_kwargs _ vars _ _ _ _ = _ /\ _ ==> _`
    (qspecl_then [`var_tail`,`slot_tail`,`xs`,`(aid,p,b0,tv,x)::kept`,
      `off+tv_abi_size tv`,`last`,`shadow_last`,`tail_state`,`G1`,`tn1`] mp_tac) >>
  impl_tac
  >- asm_rewrite_tac[listTheory.EVERY_DEF,arithmeticTheory.ADD_ASSOC,arithmeticTheory.SUC_SUB1] >>
  disch_then (qx_choosel_then [`end_st`,`end_shadow`,`u`,`Ju`,`tzu`]
    (map_every assume_tac o CONJUNCTS o SIMP_RULE bool_ss
      [arithmeticTheory.ADD_ASSOC, pairTheory.UNCURRY, pairTheory.FST, pairTheory.SND])) >>
  qpat_assum `EVERY _ ((aid,p,b0,tv,x)::kept)`
    (strip_assume_tac o SIMP_RULE (srw_ss()) []) >>
  qexistsl_tac [`end_st`,`end_shadow`,`u`,`Ju`,`tzu`] >>
  asm_simp_tac bool_ss [arithmeticTheory.ADD_ASSOC, listTheory.LIST_REL_def,
    pairTheory.UNCURRY, pairTheory.FST, pairTheory.SND] >>
  rpt conj_tac
  >- (qpat_assum `selected_registration_frame s tn tail_state tn1` mp_tac >>
     qpat_assum `selected_registration_frame tail_state tn1 u tzu` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >> rw[selected_registration_frame_def])
  >- metis_tac[pred_setTheory.SUBSET_TRANS] >>
  rpt gen_tac >> irule gas_origin_ptr_path_trans >> asm_rewrite_tac[] >>
  qexistsl_tac [`G1`,`tail_state`,`tn1`] >> asm_rewrite_tac[]
QED

Finalise grouped_supplied_initializers
