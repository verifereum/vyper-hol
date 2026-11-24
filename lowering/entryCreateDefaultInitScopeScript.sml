(* Confinement of the omitted defaults at the selected initializer cut. *)
Theory entryCreateDefaultInitScope
Libs groupedKeywordOmittedLib
Ancestors
  groupedDefaultOmittedCut groupedKeywordOmitted entryCreateDefaultSlotContinue
  entryCreateDefaultConsOutcome entryCreateDefaultCutLayout entryCreateKeywordStoreRun
  entryCreateOutcomeStore entryCreateIntervalLayout createSizeOperandCode
  groupedInternalLabels groupedEntryCounters entryCreateOutcomeWitness
  exprSimFullBundleProps createSizeCutCode createSizeCutRegion pair
  entryCreateCompletedCut entryCreatePathScope entryCreatePendingScope
  fragExec fragGasOriginPtr gasOutcomeFull gasOutcomeFullCompose compileEnv
  arithmetic list vyperStorageFootprint vyperState vyperInterpreter loweringPosts
  loweringStateRelDefs bodyPtrDefs exprSimProps exprSimDefs bodyFullPreds
  selectedAcceptedFold groupedDefaultState words finite_map
  gasStorage gasSummary stmtSimProps moduleLowering exprSimWordArgs exprLoweringProps

val omitted_expr_inputs = groupedKeywordOmittedLib.omitted_expr_inputs ();
val omitted_expr_store_post = groupedKeywordOmittedLib.omitted_expr_store_post ();
val omitted_expr_normal_post = groupedKeywordOmittedLib.omitted_expr_normal_post ();

val row_exit = ``\(H:(bool # 256 word # type_value) list # num list) (res:value + vyperState$exception) ee (gt:(string |-> num # num) # taint) r.
    expr_exit res r /\ halt_exit H cx ee res r /\
    (ctx_has_dalloca ctx ==> !s. r = Halt s ==> allocas_below_fmp s)``;

val explicit = ``gas_explicit_sites ctx shadow_ctx``;
val focus = ``create_operand_focus_scope A sb ^explicit ctx fn``;
val full = ``create_operand_full_scope A sb ^explicit ctx fn``;
val prefix = ``create_expr_prefix A sb ^explicit ctx fn``;

(* Only the chosen row is needed; the callback must accept its actual layout. *)
val guarded_rows = ``
  !e ty sa mid sha shmid src es s G tn.
    runtime_constant_expr mods e /\ expr_type e = ty /\
    body_inv tops ctx (ce with ce_vars := FEMPTY) cx /\
    shadow_body_inv tops ctx shadow_ctx /\ body_const_cells_agree [(NONE,tops)] cx env es /\
    expr_body_pre (ce with ce_vars := FEMPTY) cx env e es /\
    expr_sim_full_hypotheses (DF,0,NONE,ctx,shadow_ctx,PG,fn,shadow_fn)
      (ce with ce_vars := FEMPTY) cx ty e es (st0,sa,mid,sha,shmid,src,s,G,tn) /\
    create_layout sa mid ==>
    scoped_operand_outcome (DF,0,^explicit,ctx,fn,PG) (cx_tops cx) cx st0 sa mid
      (bind (eval_expr cx e) (read_result cx)) (es,s,G,tn)
      ^omitted_expr_normal_post ^row_exit``;

Theorem witnessed_restrict_start[local]:
  witnessed_operand_outcome
    (\v ms. v = s /\ focus v ms) (\v ms r. v = s /\ full v ms r)
    (DF,lo,explicit,ctx,fn,PG) tops cx st0 source (es,s,G,tn) Q R <=>
  witnessed_operand_outcome focus full
    (DF,lo,explicit,ctx,fn,PG) tops cx st0 source (es,s,G,tn) Q R
Proof
  simp[witnessed_operand_outcome_def]
QED

Theorem confined_keyword_store[local]:
  ^omitted_expr_inputs /\
  scoped_operand_outcome (DF,0,^explicit,ctx,fn,PG) (cx_tops cx) cx st0 sa mid
    (bind (eval_expr cx e) (read_result cx)) (es,s,G,tn)
    ^omitted_expr_normal_post ^row_exit /\
  (?bb i. lookup_block sb.cs_current_bb fn.fn_blocks = SOME bb /\
          get_instruction bb (LENGTH sb.cs_current_insts) = SOME i /\
          sb.cs_next_id <= i.inst_id) /\
  A.cs_next_id <= sa.cs_next_id /\ last.cs_next_id <= sb.cs_next_id /\
  fn_has_code sa mid fn /\ MEM fn ctx.ctx_functions /\
  s.vs_current_bb = sa.cs_current_bb /\ s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  witnessed_operand_outcome ^focus
    (\s ms r. case r of OK u => ^prefix s ms u | _ => ^full s ms r)
    (DF,0,^explicit,ctx,fn,PG) (cx_tops cx) cx st0
    (bind (eval_expr cx e) (read_result cx)) (es,s,G,tn)
    ^omitted_expr_store_post ^row_exit
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  RULE_ASSUM_TAC (REWRITE_RULE [GSYM witnessed_operand_outcome_scoped]) >>
  `create_cut_code {} sa mid` by
    (fs[expr_sim_full_hypotheses_def] >> metis_tac[cj 2 create_operand_cut_code,SND]) >>
  `create_cut_code {} mid last` by
    (qpat_assum `(if _ then _ else _) mid = _`
      (ACCEPT_TAC o cj 1 o MATCH_MP grouped_keyword_store_layout)) >>
  `sa.cs_next_id <= mid.cs_next_id /\ mid.cs_next_id <= sb.cs_next_id` by
    (fs[create_cut_code_def] >> decide_tac) >>
  `create_cut_region sa mid s` by
    (mp_tac (Q.INST [`a` |-> `sa`,`m` |-> `mid`]
       (SPEC_ALL create_cut_region_rules)) >>
     (impl_tac >- asm_rewrite_tac[]) >> disch_then (irule o cj 1) >> simp[]) >>
  mp_tac (Q.INST [`a` |-> `A`,`b` |-> `sb`,`x` |-> `sa`,`y` |-> `mid`,
    `explicit` |-> `^explicit`] (SPEC_ALL grouped_initializer_inner_lifts)) >>
  (impl_tac >- (asm_rewrite_tac[] >> decide_tac)) >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  qpat_x_assum `!tops ce cx s. _ ==> _`
    (qspecl_then [`tops`,`ce with ce_vars := FEMPTY`,`cx`,`s`] mp_tac) >>
  simp_tac bool_ss [AND_IMP_INTRO] >> impl_tac >- asm_rewrite_tac[] >> strip_tac >>
  mp_tac (Q.INST [`a` |-> `A`,`b` |-> `sb`,`x` |-> `mid`,`y` |-> `last`,
    `explicit` |-> `^explicit`] (SPEC_ALL grouped_initializer_inner_lifts)) >>
  (impl_tac >- (asm_rewrite_tac[] >> decide_tac)) >>
  disch_then (assume_tac o cj 3) >>
  suspend "lift"
QED

Resume confined_keyword_store[lift]:
  `witnessed_operand_outcome
      (\v ms. v = s /\ create_operand_focus_scope sa mid ^explicit ctx fn v ms)
      (\v ms r. v = s /\ create_operand_full_scope sa mid ^explicit ctx fn v ms r)
      (DF,0,^explicit,ctx,fn,PG) (cx_tops cx) cx st0
      (bind (eval_expr cx e) (read_result cx)) (es,s,G,tn)
      ^omitted_expr_normal_post ^row_exit` by
    (rewrite_tac[witnessed_restrict_start] >>
     CONV_TAC (DEPTH_CONV ETA_CONV) >> first_assum ACCEPT_TAC) >>
  irule witnessed_operand_zero_suffix >>
  pop_assum (irule_at Any) >> simp[] >>
  (reverse conj_tac >- (rpt strip_tac >> Cases_on `r` >> gvs[exit_result_def])) >>
  qx_genl_tac [`m`,`res`,`ee`,`G1`,`tn1`,`t`] >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  mp_tac (Q.INST [`keep` |-> `\t u. create_expr_prefix mid last ^explicit ctx fn t [] u`]
    (SPEC_ALL grouped_keyword_store_normal_witness)) >>
  simp_tac bool_ss [] >>
  (impl_tac >- (asm_rewrite_tac[] >> rpt strip_tac >>
    irule grouped_keyword_store_run_prefix >> asm_rewrite_tac[] >>
    qexistsl_tac [`ce`,`Var dst`,`src`,`ty`] >> first_assum ACCEPT_TAC)) >>
  disch_then (qx_choosel_then [`u`,`J`,`tz`] strip_assume_tac) >>
  qexistsl_tac [`u`,`J`,`tz`] >> asm_rewrite_tac[] >>
  irule (SIMP_RULE bool_ss [APPEND_NIL] (Q.INST [`right` |-> `[]`]
    (SPEC_ALL create_expr_prefix_append))) >>
  qexists_tac `t` >> fs[create_operand_full_scope_def]
QED
Finalise confined_keyword_store

Theorem witnessed_post_mono[local]:
  witnessed_operand_outcome focus full (DF,lo,explicit,ctx,fn,PG)
    tops cx st0 source (es,s,G,tn) Q R /\
  (!H res ee G' tn' u. Q H res ee G' tn' u ==> Q' H res ee G' tn' u) /\
  (!H res ee gt r. R H res ee gt r ==> R' H res ee gt r) ==>
  witnessed_operand_outcome focus full (DF,lo,explicit,ctx,fn,PG)
    tops cx st0 source (es,s,G,tn) Q' R'
Proof
  rw[witnessed_operand_outcome_def] >> qexists_tac `marks` >> metis_tac[]
QED

Theorem witnessed_pure[local]:
  ~s.vs_halted /\ focus s [] /\ full s [] (OK u) /\
  (!tail. source (es with gas_obs := tail) = (res, ee with gas_obs := tail)) /\
  (!H. valid_horizon cx st0 H ee.storage_trace ==>
     gas_origin_ptr_path (DF H,lo,explicit,ctx,fn,PG) (s,G,tn) [] (OK u,J,tz) /\
     Q H res (ee with gas_obs := []) J tz u) ==>
  witnessed_operand_outcome focus full (DF,lo,explicit,ctx,fn,PG)
    tops cx st0 source (es,s,G,tn) Q R
Proof
  strip_tac >> rewrite_tac[witnessed_operand_outcome_def] >> qexists_tac `[]` >>
  Cases_on `storage_trace_domain cx st0 ee.storage_trace`
  >- (disj2_tac >> disj1_tac >> qexistsl_tac [`res`,`ee`,`OK u`,`J`,`tz`] >> simp[]) >>
  disj1_tac >> simp[gas_bad_storage_at_def, gas_explicit_def] >>
  qexistsl_tac [`storage_trace_horizon es.storage_trace`,`fn`,`PG`,`G`,`tn`,`s`] >>
  simp[gas_origin_ptr_focus_nil, storage_trace_domain_def]
QED

Theorem full_scope_prepend_prefix[local]:
  create_expr_prefix a b explicit ctx fn s left t /\
  create_operand_full_scope a b explicit ctx fn t right r ==>
  create_operand_full_scope a b explicit ctx fn s (left ++ right) r
Proof
  Cases_on `r` >> simp[create_operand_full_scope_def] >>
  metis_tac[create_expr_prefix_append,APPEND_ASSOC]
QED

val allocated = ``\sa s G tn (aid,p,base,tv).
  aid < sa.cs_next_id /\ not_fresh_at sa p /\ base < dimword (:256) /\
  FLOOKUP s.vs_allocas aid = SOME (base,type_memory_size tv) /\
  lookup_var p s = SOME (n2w base) /\ ptr_covers G tn p s (type_memory_size tv)``;

val initialized = ``\sa s G tn (aid,p,base,tv,v).
  ^allocated sa s G tn (aid,p,base,tv) /\ value_has_type tv v /\
  (!mem. mem_agree_outside tn.t_mem s.vs_memory mem ==> val_in_memory tv v base mem)``;

val row_slots = ``\((n,dst,ty,e):string # operand # type # expr)
    ((aid,p,base,tv):num # string # num # type_value).
    dst = Var p /\ runtime_constant_expr mods e /\ expr_type e = ty /\
    (!es'. expr_sim_inv (ce with ce_vars := FEMPTY) cx env es' ==>
      expr_body_pre (ce with ce_vars := FEMPTY) cx env e es') /\
    lower_value compile_expr (ce with ce_vars := FEMPTY) ty e =
      lower_value compile_expr ce ty e /\
    lower_value compile_expr (gas_shadow_env T (ce with ce_vars := FEMPTY))
      ty (gas_shadow_expr e) = lower_value compile_expr (gas_shadow_env T ce) ty (gas_shadow_expr e) /\
    evaluate_type (get_tenv cx) ty = SOME tv /\
    type_memory_bytes ce ty = type_memory_size tv /\
    type_memory_size tv + 64 < dimword (:256)``;

val list_exit = ``\(H:(bool # 256 word # type_value) list # num list) (res:value list + vyperState$exception)
    ee (gt:(string |-> num # num) # taint) r.
    ?ex. res = INR ex /\ expr_exit (INR ex:value list + exception) r /\
    halt_exit H cx ee (INR ex:value list + exception) r /\
    (ctx_has_dalloca ctx ==> !u. r = Halt u ==> allocas_below_fmp u)``;

Theorem row_exit_as_list[local]:
  ^row_exit =
  (\H res ee gt r. ?ex. res = INR ex /\ expr_exit (INR ex:value list + exception) r /\
    halt_exit H cx ee (INR ex:value list + exception) r /\
    (ctx_has_dalloca ctx ==> !u. r = Halt u ==> allocas_below_fmp u))
Proof
  simp[FUN_EQ_THM] >> rpt gen_tac >> Cases_on `res` >>
  simp[expr_exit_INR_type,halt_exit_def]
QED

Theorem confined_omitted_initializers[local]:
  ^guarded_rows /\ create_layout A sb /\
  (?bb i. lookup_block sb.cs_current_bb fn.fn_blocks = SOME bb /\
          get_instruction bb (LENGTH sb.cs_current_insts) = SOME i /\
          sb.cs_next_id <= i.inst_id) ==>
  !vars slots kept sa sha es s G tn.
    compile_init_kwargs ce vars off 0 hi sa = ((),sb) /\
    compile_init_kwargs (gas_shadow_env T ce)
      (MAP (\(n,p,ty,e). (n,p,ty,gas_shadow_expr e)) vars) off 0 hi sha = ((),shb) /\
    cs_extends A sa /\ A.cs_next_id <= sa.cs_next_id /\
    fn_has_code sa sb fn /\ fn_has_code sha shb shadow_fn /\ gas_shadow_state sa sha /\
    LIST_REL (^row_slots) vars slots /\
    EVERY (^allocated sa s G tn) slots /\ EVERY (^initialized sa s G tn) kept /\
    ALL_DISTINCT (MAP FST slots ++ MAP FST kept) /\
    body_inv tops ctx (ce with ce_vars := FEMPTY) cx /\ shadow_body_inv tops ctx shadow_ctx /\
    body_const_cells_agree [(NONE,tops)] cx env es /\
    env.type_defs = get_tenv cx /\ ~ce.ce_is_ctor /\ ce.ce_imm_alloca = NONE /\
    ce.ce_return_pc = NONE /\ ce.ce_return_buf = NONE /\
    gas_shadow_context ctx shadow_ctx /\ ctx_inst_ids_distinct ctx /\
    gas_shadow_function fn shadow_fn /\ MEM fn ctx.ctx_functions /\ MEM shadow_fn shadow_ctx.ctx_functions /\
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
    witnessed_operand_outcome ^focus ^full (DF,0,^explicit,ctx,fn,PG)
      (cx_tops cx) cx st0 (eval_exprs cx (MAP (\(_,_,_,e). e) vars)) (es,s,G,tn)
      (\H res ee J tz u. ?values.
        res = INL values /\
        LIST_REL (\(aid,p,base,tv) v. ^initialized sb u J tz (aid,p,base,tv,v)) slots values /\
        EVERY (^initialized sb u J tz) kept /\
        stmt_state_rel H ctx fn (ce with ce_vars := FEMPTY) cx ee u /\
        storage_well_formed_on cx ee (FST H) /\
        ghost_inv_at (DF H) 0 NONE (ce with ce_vars := FEMPTY) cx ee J tz u /\
        ee.scopes = es.scopes /\ alloca_history fn u /\
        (ctx_has_dalloca ctx ==> allocas_below_fmp u) /\
        ~u.vs_halted /\ u.vs_current_bb = sb.cs_current_bb /\
        u.vs_inst_idx = LENGTH sb.cs_current_insts)
      ^list_exit
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >> Induct
  >- suspend "nil" >>
  suspend "cons"
QED

Resume confined_omitted_initializers[nil]:
  Cases_on `slots` >> simp[compile_init_kwargs_def,comp_return_def] >>
  rpt gen_tac >> strip_tac >> gvs[] >>
  irule witnessed_pure >> simp[] >>
  conj_tac >- (irule create_operand_focus_scope_caller >> qexists_tac `s` >> simp[create_expr_prefix_nil]) >>
  qexistsl_tac [`G`,`es`,`INL ([]:value list)`,`tn`,`s`] >>
  simp[eval_exprs_nil,return_def,gas_origin_ptr_path_rules,create_operand_full_scope_def,
       create_operand_focus_scope_caller,create_expr_prefix_nil] >>
  gen_tac >> strip_tac >> first_x_assum drule >> strip_tac >>
  simp[stmt_state_rel_start_gas_obs] >>
  `storage_well_formed_on cx (es with gas_obs := []) (FST H) <=>
     storage_well_formed_on cx es (FST H)` by
    (irule storage_well_formed_on_backends >> simp[]) >> fs[ghost_inv_at_def]
QED

Resume confined_omitted_initializers[cons]:
  gen_tac >> PairCases_on `h` >> gen_tac >> Cases_on `slots` >- simp[] >>
  PairCases_on `h` >> simp[] >>
  rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
  qpat_x_assum `_ = Var _` SUBST_ALL_TAC >>
  rename1 `compile_init_kwargs ce ((name,Var p,ty,e)::vars) off 0 hi sa = _` >>
  rename1 `aid < sa.cs_next_id` >>
  rename1 `evaluate_type (get_tenv cx) ty = SOME kw_tv` >>
  qpat_assum `compile_init_kwargs ce ((name,Var p,ty,e)::vars) off 0 hi sa = _`
    (fn eq => mp_tac (PART_MATCH (hd o strip_conj o fst o dest_imp)
      (Q.INST [`shfn` |-> `shadow_fn`] (SPEC_ALL grouped_initializer_head_inputs))
      (concl eq))) >>
  (impl_tac >- asm_rewrite_tac[]) >>
  disch_then (qx_choosel_then [`op`,`mid`,`last`,`shmid`,`shlast`] strip_assume_tac) >>
  `cs_extends sa mid` by
    (qspecl_then [`ce`,`ty`,`e`,`sa`] mp_tac (cj 2 create_operand_cut_code) >>
     simp[create_cut_code_def]) >>
  `cs_extends mid last` by
    (qpat_assum `(if _ then _ else _) mid = _`
      (mp_tac o cj 1 o MATCH_MP grouped_keyword_store_layout) >> simp[create_cut_code_def]) >>
  `cs_extends last sb` by metis_tac[compile_init_kwargs_extends] >>
  `create_layout sa mid` by metis_tac[create_layout_subinterval,cs_extends_trans] >>
  `last.cs_next_id <= sb.cs_next_id` by
    (qpat_assum `compile_init_kwargs ce vars off 0 hi last = _` (fn eq =>
      qspecl_then [`vars`,`ce`,`off`,`0`,`hi`,`last`] mp_tac compile_init_kwargs_ci_mono >>
      simp[eq,ci_mono_def])) >>
  qpat_assum `!e ty sa mid sha shmid src es s G tn. _ ==> scoped_operand_outcome _ _ _ _ _ _ _ _ _ _`
    (qspecl_then [`e`,`ty`,`sa`,`mid`,`sha`,`shmid`,`op`,`es`,`s`,`G`,`tn`] mp_tac) >>
  (impl_tac >- asm_rewrite_tac[]) >> strip_tac >>
  `w2n (n2w h2':256 word) = h2'` by simp[w2n_n2w] >>
  mp_tac (Q.INST [`dst` |-> `p`, `b` |-> `n2w h2':256 word`,
    `oid` |-> `aid`, `tv` |-> `kw_tv`, `src` |-> `op`] (SPEC_ALL confined_keyword_store)) >>
  (impl_tac >- fs[]) >>
  disch_then (assume_tac o REWRITE_RULE [row_exit_as_list]) >>
  suspend "compose"
QED

Resume confined_omitted_initializers[compose]:
  qpat_assum `witnessed_operand_outcome _ _ _ _ _ _ (bind (eval_expr _ _) _) _ _ _`
    (fn head =>
       let
         val args = snd (strip_comb (concl head))
         val (binders,body) = strip_abs (List.nth (args,8))
         val (v,post) = dest_exists body
         val P = list_mk_abs (hd binders :: v :: List.drop (binders,2),snd (dest_conj post))
         val (eb,exit_body) = strip_abs (List.nth (args,9))
         val (ex,exit_post) = dest_exists exit_body
         val R = list_mk_abs (hd eb :: ex :: List.drop (eb,2),snd (dest_conj exit_post))
         val M1 = List.nth (args,1)
         val compose = BETA_RULE (Q.INST [`P` |-> `^P`,`R` |-> `^R`,
           `F1` |-> `^focus`, `F2` |-> `^focus`, `M1` |-> `^M1`, `M2` |-> `^full`]
           grouped_default_exprs_cons_witnessed)
       in
         ho_match_mp_tac compose >> conj_tac >- ACCEPT_TAC head
       end) >>
  rpt conj_tac
  >- suspend "tail"
  >- simp[]
  >- (rpt gen_tac >> Cases_on `r` >> simp[exit_result_def])
  >- (simp[] >> metis_tac[create_operand_focus_scope_prepend]) >>
  simp[] >> metis_tac[full_scope_prepend_prefix]
QED

Resume confined_omitted_initializers[tail]:
  qx_genl_tac [`marks`,`v`,`ee`,`G1`,`tn1`,`tail_state`] >> BETA_TAC >> strip_tac >>
  qpat_assum `w2n (n2w h2':256 word) = h2'`
    (RULE_ASSUM_TAC o PURE_REWRITE_RULE o single) >>
  mp_tac (Q.INST [`slots` |-> `t`, `b0` |-> `h2'`, `tv` |-> `kw_tv`,
    `explicit` |-> `^explicit`] (SPEC_ALL grouped_initializer_tail_inputs)) >>
  (impl_tac >-
    (fs[] >> reverse conj_tac >- first_assum ACCEPT_TAC >>
     gen_tac >> disch_tac >>
     qpat_assum `!H. valid_horizon _ _ H ee.storage_trace ==> _`
       (qspec_then `H` (drule_then strip_assume_tac)) >> asm_rewrite_tac[])) >>
  disch_then (strip_assume_tac o SIMP_RULE (srw_ss()) []) >>
  `cs_extends A last` by metis_tac[cs_extends_trans] >>
  `A.cs_next_id <= last.cs_next_id` by (fs[ci_mono_def] >> decide_tac) >>
  qpat_assum `!slots kept sa sha es s G tn. compile_init_kwargs _ vars _ _ _ _ = _ /\ _ ==> _`
    (qspecl_then [`t`,`(aid,p,h2',kw_tv,v)::kept`,`last`,`shlast`,`ee`,
       `tail_state`,`G1`,`tn1`] mp_tac) >>
  (impl_tac >-
    (simp_tac (srw_ss()) [] >> rpt conj_tac >> first_assum ACCEPT_TAC)) >>
  strip_tac >> irule witnessed_post_mono >>
  goal_assum (drule_at Any) >>
  qpat_assum `ee.scopes = es.scopes` mp_tac >>
  POP_ASSUM_LIST (K all_tac) >>
  disch_tac >> conj_tac
  >- (rpt gen_tac >> BETA_TAC >>
      disch_then (qx_choose_then `values` (strip_assume_tac o SIMP_RULE (srw_ss()) [])) >>
      qexists_tac `values` >> simp[]) >>
  rpt gen_tac >> BETA_TAC >> simp_tac bool_ss []
QED
Finalise confined_omitted_initializers

Theorem grouped_default_omitted_cut_scoped_from_rows:
  ^guarded_rows /\ create_layout last sb /\
  emit_inst JMP [Label common] [] sb = ((),term) /\ fn_has_code sb term fn /\
  compile_init_kwargs ce (DROP k vars) off 0 hi last = ((),sb) /\
  compile_init_kwargs (gas_shadow_env T ce)
    (MAP (\(n,p,ty,e). (n,p,ty,gas_shadow_expr e)) (DROP k vars)) off 0 hi shlast = ((),shb) /\
  fn_has_code last sb fn /\ fn_has_code shlast shb shadow_fn /\ gas_shadow_state last shlast /\
  LIST_REL (^row_slots) (DROP k vars) (DROP k slots) /\
  MAP (\(_,_,_,e). e) vars = ds /\
  EVERY (^allocated last t J tz) (DROP k slots) /\
  LIST_REL (\(aid,p,base,tv) v. ^initialized last t J tz (aid,p,base,tv,v))
    (TAKE k slots) supplied_vals /\
  ALL_DISTINCT (MAP FST slots) /\
  body_inv tops ctx (ce with ce_vars := FEMPTY) cx /\ shadow_body_inv tops ctx shadow_ctx /\
  body_const_cells_agree [(NONE,tops)] cx env es /\
  env.type_defs = get_tenv cx /\ ~ce.ce_is_ctor /\ ce.ce_imm_alloca = NONE /\
  ce.ce_return_pc = NONE /\ ce.ce_return_buf = NONE /\
  gas_shadow_context ctx shadow_ctx /\ ctx_inst_ids_distinct ctx /\
  gas_shadow_function fn shadow_fn /\ MEM fn ctx.ctx_functions /\ MEM shadow_fn shadow_ctx.ctx_functions /\
  fn_inst_ids_distinct fn /\
  (!bb. MEM bb fn.fn_blocks ==> phi_prefix_length bb.bb_instructions = 0) /\
  (!H. dead_lo_ok H (DF H) 0 (ce with ce_vars := FEMPTY) cx) /\
  es.scopes = [FEMPTY] /\ tn.t_imm = {} /\
  (!H. valid_horizon cx st0 H es.storage_trace ==>
    stmt_state_rel H ctx fn (ce with ce_vars := FEMPTY) cx es s /\
    storage_well_formed_on cx es (FST H) /\
    ghost_inv_at (DF H) 0 NONE (ce with ce_vars := FEMPTY) cx es G tn s) /\
  selected_registration_frame s tn t tz /\
  selected_registration_resources ctx fn site 0 last t /\
  (!D exp. gas_origin_ptr_path (D,0,exp,ctx,fn,PG) (s,G,tn) [] (OK t,J,tz)) /\
  expr_sim_inv (ce with ce_vars := FEMPTY) cx env es /\
  alloca_history fn t /\
  (ctx_has_dalloca ctx ==> allocas_below_fmp t /\
    t.vs_alloca_next + pending_alloca_size fn t <= w2n t.vs_initial_fmp) /\
  (!f inst u. frag_reachable ctx fn t f inst u ==> dalloca_fmp_headroom inst u) ==>
  scoped_operand_outcome (DF,0,^explicit,ctx,fn,PG) (cx_tops cx) cx st0 last sb
    (eval_exprs cx (DROP k ds)) (es,t,J,tz)
    (\H res ee J' tz' u. ?values.
      res = INL values /\
      LIST_REL (\(aid,p,base,tv) v. ^initialized sb u J' tz' (aid,p,base,tv,v))
        slots (supplied_vals ++ values) /\
      stmt_state_rel H ctx fn (ce with ce_vars := FEMPTY) cx ee u /\
      storage_well_formed_on cx ee (FST H) /\
      ghost_inv_at (DF H) 0 NONE (ce with ce_vars := FEMPTY) cx ee J' tz' u /\
      ee.scopes = es.scopes /\ alloca_history fn u /\
      (ctx_has_dalloca ctx ==> allocas_below_fmp u) /\
      ~u.vs_halted /\ u.vs_current_bb = sb.cs_current_bb /\
      u.vs_inst_idx = LENGTH sb.cs_current_insts)
    ^list_exit
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all grouped_initializer_exit_fetch >> strip_tac >>
  mp_tac (SPEC_ALL grouped_omitted_decoder_inputs) >>
  (impl_tac >- asm_rewrite_tac[]) >> disch_then assume_tac >>
  qspec_then `^initialized last t J tz` mp_tac grouped_omitted_kept_inputs >>
  (impl_tac >- asm_rewrite_tac[]) >>
  disch_then (qx_choose_then `kept` (map_every assume_tac o CONJUNCTS)) >>
  qpat_assum `selected_registration_resources _ _ _ _ _ _`
    (strip_assume_tac o REWRITE_RULE [selected_registration_resources_def]) >>
  qpat_assum `MAP _ vars = ds` (SUBST1_TAC o SYM) >>
  once_rewrite_tac[GSYM MAP_DROP] >>
  rewrite_tac[GSYM witnessed_operand_outcome_scoped] >>
  suspend "finish"
QED

Resume grouped_default_omitted_cut_scoped_from_rows[finish]:
  irule witnessed_post_mono >>
  mp_tac (Q.INST [`A` |-> `last`] (SPEC_ALL confined_omitted_initializers)) >>
  (impl_tac >- (asm_rewrite_tac[] >> qexistsl_tac [`bb`,`i`] >> simp[])) >>
  disch_then (qspecl_then [`DROP k vars`,`DROP k slots`,`kept`,`last`,`shlast`,`es`,`t`,`J`,`tz`] mp_tac) >>
  (impl_tac >- (asm_rewrite_tac[cs_extends_refl,LESS_EQ_REFL] >> metis_tac[])) >>
  disch_then (irule_at Any) >>
  simp[] >> rpt gen_tac >> disch_then (qx_choose_then `values` strip_assume_tac) >>
  qexists_tac `values` >> simp[] >>
  `TAKE k slots ++ DROP k slots = slots` by simp[] >>
  pop_assum (SUBST1_TAC o SYM) >> irule LIST_REL_APPEND_suff >> simp[]
QED
Finalise grouped_default_omitted_cut_scoped_from_rows
