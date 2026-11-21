(* Run the omitted suffix of a selected grouped entry initializer. *)
Theory groupedKeywordInitialize
Ancestors
  groupedDefaultCode groupedDefaultEvaluation groupedKeywordOmitted
  bodyFullIfExpReach exprSimSource exprSimDefs exprSimFullBundleProps exprSimWordArgs
  exprSimProps stmtSimProps valueEncoding ptrDiscipline
  loweringPosts loweringStateRelDefs bodyPtrDefs freshWrites valueEncodingTyping
  gasOutcomeFull gasOutcomeFullCompose fragGasOriginPtr
  vyperInterpreter vyperState vyperStorageFootprint vyperStorageTrace
  exprLoweringProps moduleLowering compileEnv venomState vyperValue finite_map words list pair

val allocated_slot = ``\sa s G tn (aid,p,base,tv).
  aid < sa.cs_next_id /\ not_fresh_at sa p /\ base < dimword (:256) /\
  FLOOKUP s.vs_allocas aid = SOME (base,type_memory_size tv) /\
  lookup_var p s = SOME (n2w base) /\ ptr_covers G tn p s (type_memory_size tv)``;

val initialized_slot = ``\sa s G tn (aid,p,base,tv,v).
  ^allocated_slot sa s G tn (aid,p,base,tv) /\ value_has_type tv v /\
  (!mem. mem_agree_outside tn.t_mem s.vs_memory mem ==> val_in_memory tv v base mem)``;

Theorem grouped_initializer_slot_kept[local]:
  ci_mono sa sb /\
  (!aid entry. FLOOKUP s.vs_allocas aid = SOME entry ==>
     FLOOKUP t.vs_allocas aid = SOME entry) /\
  (!p w. not_fresh_at sa p /\ lookup_var p s = SOME w ==>
     lookup_var p t = SOME w /\ FLOOKUP J p = FLOOKUP G p /\
     op_taint tz (Var p) = op_taint tn (Var p)) /\
  ^allocated_slot sa s G tn slot ==>
  ^allocated_slot sb t J tz slot
Proof
  PairCases_on `slot` >> simp[] >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  qpat_assum `!p w. _` (qspecl_then [`slot1`,`n2w slot2:256 word`] mp_tac) >>
  asm_rewrite_tac[] >> strip_tac >>
  fs[ci_mono_def, ptr_covers_def] >>
  metis_tac[arithmeticTheory.LESS_LESS_EQ_TRANS, not_fresh_at_mono]
QED

val grouped_initializer_slot_tac = fn row =>
  mp_tac (SIMP_RULE (srw_ss()) []
    (Q.INST [`sb` |-> `last`, `t` |-> `tail_state`, `J` |-> `G1`,
      `tz` |-> `tn1`, `slot` |-> row] (SPEC_ALL grouped_initializer_slot_kept))) >>
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
    compile_init_kwargs ce (MAP (\(n,p,ty,e). (n,p,ty,gas_shadow_expr e)) vars)
      off 0 hi sha = ((),shb) /\
    fn_has_code sa sb fn /\ fn_has_code sha shb shfn /\ gas_shadow_state sa sha /\
    LIST_REL (\(n,dst,ty,e) (aid,p,base,tv).
      dst = Var p /\ runtime_constant_expr mods e /\ expr_type e = ty /\
      (!es'. expr_sim_inv (ce with ce_vars := FEMPTY) cx env es' ==>
        expr_body_pre (ce with ce_vars := FEMPTY) cx env e es') /\
      lower_value compile_expr (ce with ce_vars := FEMPTY) ty e =
        lower_value compile_expr ce ty e /\
      lower_value compile_expr (ce with ce_vars := FEMPTY) ty (gas_shadow_expr e) =
        lower_value compile_expr ce ty (gas_shadow_expr e) /\
      evaluate_type (get_tenv cx) ty = SOME tv /\
      type_memory_bytes ce ty = type_memory_size tv /\
      type_memory_size tv + 64 < dimword (:256)) vars slots /\
    EVERY (^allocated_slot sa s G tn) slots /\
    EVERY (^initialized_slot sa s G tn) kept /\
    ALL_DISTINCT (MAP FST slots ++ MAP FST kept) /\
    body_inv tops ctx (ce with ce_vars := FEMPTY) cx /\ shadow_body_inv tops ctx shadow_ctx /\
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
    (!f inst u. frag_reachable ctx fn s f inst u ==> dalloca_no_wrap inst u) /\
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
  `expr_body_pre (ce with ce_vars := FEMPTY) cx env e es` by metis_tac[] >>
  mp_tac (Q.INST [`dst` |-> `Var p`] (SPEC_ALL grouped_default_initializer_intervals)) >>
  impl_tac >- asm_rewrite_tac[] >>
  disch_then (qx_choosel_then [`op`,`mid`,`last`,`shmid`,`shlast`] strip_assume_tac) >>
  `expr_sim_full_hypotheses (DF,0,NONE,ctx,shadow_ctx,PG,fn,shfn)
    (ce with ce_vars := FEMPTY) cx ty e es (st0,sa,mid,sha,shmid,op,s,G,tn)` by
    (simp[expr_sim_full_hypotheses_def, expr_sim_full_code_def, local_ptrs_reserved_def,
          return_buf_frame_def, FLOOKUP_EMPTY] >>
     metis_tac[expr_body_pre_gas_admissible]) >>
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
  `valid_horizon cx st0 (storage_trace_horizon ee.storage_trace) ee.storage_trace` by
    fs[storage_trace_domain_def] >>
  qpat_assum `!H. valid_horizon _ _ H ee.storage_trace ==> _`
    (drule_then strip_assume_tac) >>
  `!f inst u. frag_reachable ctx fn tail_state f inst u ==> dalloca_no_wrap inst u` by
    (qpat_assum `gas_origin_ptr_path _ _ marks (OK tail_state,_,_)` (fn path =>
       qpat_assum `!bb. MEM bb fn.fn_blocks ==> _` (fn no_phi =>
       qpat_assum `!f inst u. frag_reachable ctx fn s f inst u ==> _` (fn bounds =>
         ACCEPT_TAC (MATCH_MP gas_origin_ptr_path_dalloca_no_wrap
           (LIST_CONJ [path,no_phi,bounds])))))) >>
  `EVERY (^allocated_slot last tail_state G1 tn1) t` by
    (qpat_assum `EVERY _ t` mp_tac >>
     simp_tac bool_ss [EVERY_MEM] >> strip_tac >> qx_gen_tac `row` >> strip_tac >>
     qpat_assum `!x. MEM x t ==> _` (qspec_then `row` (drule_then assume_tac)) >>
     grouped_initializer_slot_tac `row` >> simp[]) >>
  `EVERY (^initialized_slot last tail_state G1 tn1) kept` by
    (qpat_assum `EVERY _ kept` mp_tac >>
     simp_tac bool_ss [EVERY_MEM] >> strip_tac >>
     qx_gen_tac `row` >> PairCases_on `row` >> strip_tac >>
     qpat_assum `!row. MEM row kept ==> _`
       (qspec_then `(row0,row1,row2,row3,row4)` (drule_then mp_tac)) >>
     simp_tac (srw_ss()) [] >> strip_tac >>
     `row0 <> aid` by
       (`MEM row0 (MAP FST kept)` by
          (simp_tac bool_ss [MEM_MAP] >> qexists_tac `(row0,row1,row2,row3,row4)` >> simp[]) >>
        strip_tac >>
        qpat_assum `MEM row0 (MAP FST kept)` mp_tac >>
        qpat_assum `~MEM aid (MAP FST kept)` (fn neg =>
          qpat_assum `row0 = aid` (fn eq => simp_tac bool_ss [eq,neg]))) >>
     `val_wf row3 row4` by (irule (cj 1 value_has_type_val_wf) >> first_assum ACCEPT_TAC) >>
     `val_footprint row3 row4 <= type_memory_size row3` by simp[val_footprint_le] >>
     conj_tac >-
       (grouped_initializer_slot_tac `(row0,row1,row2,row3)` >> simp[]) >>
     simp[] >>
     qpat_assum `!id p old_base n otv x. id <> aid /\ _ ==> _`
       (qspecl_then [`row0`,`row1`,`row2`,`type_memory_size row3`,`row3`,`row4`] mp_tac) >>
     impl_tac >- asm_rewrite_tac[] >> disch_then ACCEPT_TAC) >>
  qpat_assum `ci_mono sa last` (strip_assume_tac o REWRITE_RULE [ci_mono_def]) >>
  `aid < last.cs_next_id` by decide_tac >>
  `not_fresh_at last p` by
    (irule freshWritesTheory.not_fresh_at_mono >> qexists_tac `sa` >> simp[]) >>
  qpat_assum `w2n (n2w h2':256 word) = h2'`
    (RULE_ASSUM_TAC o PURE_REWRITE_RULE o single) >>
  `^initialized_slot last tail_state G1 tn1 (aid,p,h2',kw_tv,v)` by simp[] >>
  `ALL_DISTINCT (MAP FST t ++ MAP FST ((aid,p,h2',kw_tv,v)::kept))` by
    (MAP_EVERY (fn pat => qpat_assum pat mp_tac)
       [`ALL_DISTINCT (MAP FST t ++ MAP FST kept)`,
        `~MEM aid (MAP FST t)`,`~MEM aid (MAP FST kept)`] >>
     POP_ASSUM_LIST (K all_tac) >> simp[ALL_DISTINCT_APPEND] >> metis_tac[]) >>
  `!H. valid_horizon cx st0 H ee.storage_trace ==>
    stmt_state_rel H ctx fn (ce with ce_vars := FEMPTY) cx ee tail_state /\
    storage_well_formed_on cx ee (FST H) /\
    ghost_inv_at (DF H) 0 NONE (ce with ce_vars := FEMPTY) cx ee G1 tn1 tail_state` by
    (gen_tac >> strip_tac >>
     qpat_assum `!H. valid_horizon _ _ H ee.storage_trace ==> _`
       (qspec_then `H` (drule_then strip_assume_tac)) >> asm_rewrite_tac[]) >>
  qpat_assum `!slots kept sa sha es s G tn. compile_init_kwargs _ vars _ _ _ _ = _ /\ _ ==> _`
    (qspecl_then [`t`,`(aid,p,h2',kw_tv,v)::kept`,`last`,`shlast`,`ee`,
       `tail_state`,`G1`,`tn1`] mp_tac) >>
  impl_tac >- asm_rewrite_tac[listTheory.EVERY_DEF] >>
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
