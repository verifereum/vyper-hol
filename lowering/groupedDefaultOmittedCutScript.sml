(* Execute the omitted keyword expressions from the supplied-decoder cut. *)
Theory groupedDefaultOmittedCut
Ancestors
  groupedKeywordInitialize groupedDefaultState gasOutcomeFullCompose
  groupedDefaultCode selectedAcceptedFold exprSimDefs exprSimProps
  loweringStateRelDefs loweringPosts bodyPtrDefs compileEnv freshWrites
  ptrDiscipline valueEncoding vyperInterpreter vyperState vyperValue
  fragGasOriginPtr venomState finite_map list pair words

val omitted_cut_allocated = ``\sa s G tn (aid,p,base,tv).
  aid < sa.cs_next_id /\ not_fresh_at sa p /\ base < dimword (:256) /\
  FLOOKUP s.vs_allocas aid = SOME (base,type_memory_size tv) /\
  lookup_var p s = SOME (n2w base) /\ ptr_covers G tn p s (type_memory_size tv)``;

val omitted_cut_initialized = ``\sa s G tn (aid,p,base,tv,v).
  ^omitted_cut_allocated sa s G tn (aid,p,base,tv) /\ value_has_type tv v /\
  (!mem. mem_agree_outside tn.t_mem s.vs_memory mem ==> val_in_memory tv v base mem)``;

Theorem grouped_omitted_kept_rows[local]:
  !slots vals. LENGTH slots = LENGTH vals ==>
    ?kept. MAP FST kept = MAP FST slots /\
      !P. EVERY P kept <=> LIST_REL (\(aid,p,base,tv) v. P (aid,p,base,tv,v)) slots vals
Proof
  Induct >> Cases_on `vals` >> simp[] >>
  qx_gen_tac `row` >> PairCases_on `row` >> strip_tac >>
  first_x_assum (drule_then (qx_choose_then `kept` strip_assume_tac)) >>
  qexists_tac `(row0,row1,row2,row3,h)::kept` >> simp[]
QED

Theorem grouped_omitted_kept_inputs:
  !P. LIST_REL (\(aid,p,base,tv) v. P (aid,p,base,tv,v)) (TAKE k slots) supplied_vals /\
  ALL_DISTINCT (MAP FST slots) ==>
  ?kept. EVERY P kept /\ ALL_DISTINCT (MAP FST (DROP k slots) ++ MAP FST kept) /\
    !Q. EVERY Q kept <=> LIST_REL (\(aid,p,base,tv) v. Q (aid,p,base,tv,v))
      (TAKE k slots) supplied_vals
Proof
  gen_tac >> strip_tac >>
  `LENGTH (TAKE k slots) = LENGTH supplied_vals` by fs[LIST_REL_EL_EQN] >>
  drule_then (qx_choose_then `kept` strip_assume_tac) grouped_omitted_kept_rows >>
  qexists_tac `kept` >> simp[] >>
  `ALL_DISTINCT (MAP FST (TAKE k slots) ++ MAP FST (DROP k slots))` by
    (pure_once_rewrite_tac[GSYM MAP_APPEND] >>
     pure_rewrite_tac[TAKE_DROP] >> first_assum ACCEPT_TAC) >>
  fs[ALL_DISTINCT_APPEND] >> metis_tac[]
QED

Theorem grouped_omitted_decoder_inputs:
  es.scopes = [FEMPTY] /\ tn.t_imm = {} /\
  (!H. valid_horizon cx st0 H es.storage_trace ==>
    stmt_state_rel H ctx fn (ce with ce_vars := FEMPTY) cx es s /\
    storage_well_formed_on cx es (FST H) /\
    ghost_inv_at (DF H) 0 NONE (ce with ce_vars := FEMPTY) cx es G tn s) /\
  selected_registration_frame s tn t tz /\ ~ce.ce_is_ctor /\ ce.ce_imm_alloca = NONE /\
  ce.ce_return_pc = NONE /\ selected_registration_resources ctx fn site 0 last t /\
  fn_inst_ids_distinct fn /\
  (!D exp. gas_origin_ptr_path (D,0,exp,ctx,fn,PG) (s,G,tn) [] (OK t,J,tz)) ==>
  !H. valid_horizon cx st0 H es.storage_trace ==>
    stmt_state_rel H ctx fn (ce with ce_vars := FEMPTY) cx es t /\
    storage_well_formed_on cx es (FST H) /\
    ghost_inv_at (DF H) 0 NONE (ce with ce_vars := FEMPTY) cx es J tz t
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >> gen_tac >> strip_tac >>
  qpat_assum `!H. valid_horizon _ _ H _ ==> _`
    (qspec_then `H` (drule_then strip_assume_tac)) >>
  qpat_assum `!D exp. gas_origin_ptr_path _ _ [] _`
    (qspecl_then [`DF H`,`{}`] assume_tac) >>
  drule_all grouped_empty_scope_decoder_frame >> simp[]
QED

Theorem grouped_default_omitted_cut:
  compile_init_kwargs ce (DROP k vars) off 0 hi last = ((),sb) /\
  compile_init_kwargs (gas_shadow_env T ce)
    (MAP (\(n,p,ty,e). (n,p,ty,gas_shadow_expr e)) (DROP k vars))
    off 0 hi shlast = ((),shb) /\
  fn_has_code last sb fn /\ fn_has_code shlast shb shfn /\ gas_shadow_state last shlast /\
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
    type_memory_size tv + 64 < dimword (:256)) (DROP k vars) (DROP k slots) /\
  MAP (\(_,_,_,e). e) vars = ds /\
  EVERY (^omitted_cut_allocated last t J tz) (DROP k slots) /\
  LIST_REL (\(aid,p,base,tv) v. ^omitted_cut_initialized last t J tz (aid,p,base,tv,v))
    (TAKE k slots) supplied_vals /\
  ALL_DISTINCT (MAP FST slots) /\
  body_inv tops ctx (ce with ce_vars := FEMPTY) cx /\ shadow_body_inv tops ctx shadow_ctx /\
  body_const_cells_agree [(NONE,tops)] cx env es /\
  env.type_defs = get_tenv cx /\ ~ce.ce_is_ctor /\ ce.ce_imm_alloca = NONE /\
  ce.ce_return_pc = NONE /\ ce.ce_return_buf = NONE /\
  gas_shadow_context ctx shadow_ctx /\ ctx_inst_ids_distinct ctx /\
  gas_shadow_function fn shfn /\ MEM fn ctx.ctx_functions /\ MEM shfn shadow_ctx.ctx_functions /\
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
  gas_outcome_full (DF,0,gas_explicit_sites ctx shadow_ctx,ctx,fn,PG)
    (cx_tops cx) cx st0 (eval_exprs cx (DROP k ds)) (es,t,J,tz)
    (\H res ee J' tz' u. ?values.
      res = INL values /\
      LIST_REL (\(aid,p,base,tv) v. ^omitted_cut_initialized sb u J' tz' (aid,p,base,tv,v))
        slots (supplied_vals ++ values) /\
      stmt_state_rel H ctx fn (ce with ce_vars := FEMPTY) cx ee u /\
      storage_well_formed_on cx ee (FST H) /\
      ghost_inv_at (DF H) 0 NONE (ce with ce_vars := FEMPTY) cx ee J' tz' u /\
      ee.scopes = es.scopes /\ alloca_history fn u /\
      (ctx_has_dalloca ctx ==> allocas_below_fmp u) /\
      ~u.vs_halted /\ u.vs_current_bb = sb.cs_current_bb /\
      u.vs_inst_idx = LENGTH sb.cs_current_insts)
    (\H res ee gt r. ?ex. res = INR ex /\ expr_exit (INR ex:value list + exception) r /\
      halt_exit H cx ee (INR ex:value list + exception) r /\
      (ctx_has_dalloca ctx ==> !u. r = Halt u ==> allocas_below_fmp u))
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  mp_tac (SPEC_ALL grouped_omitted_decoder_inputs) >>
  (impl_tac >- asm_rewrite_tac[]) >> disch_then assume_tac >>
  qspec_then `^omitted_cut_initialized last t J tz` mp_tac grouped_omitted_kept_inputs >>
  (impl_tac >- asm_rewrite_tac[]) >>
  disch_then (qx_choose_then `kept` (map_every assume_tac o CONJUNCTS)) >>
  qpat_assum `selected_registration_resources _ _ _ _ _ _`
    (strip_assume_tac o REWRITE_RULE [selected_registration_resources_def]) >>
  qpat_assum `MAP _ vars = ds` (SUBST1_TAC o SYM) >>
  once_rewrite_tac[GSYM MAP_DROP] >>
  irule gas_outcome_full_post_source >>
  rev_drule_then (irule_at (Pos last))
    (ONCE_REWRITE_RULE [GSYM AND_IMP_INTRO] grouped_omitted_initializers) >>
  qexistsl_tac [`tops`,`DROP k slots`,`shfn`,`shb`,`shlast`,`mods`,`kept`,`env`] >>
  simp[] >> conj_tac >- first_assum ACCEPT_TAC >>
  rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
  qpat_x_assum `?values. res = INL values /\ _`
    (qx_choose_then `values` strip_assume_tac) >>
  qexists_tac `values` >> simp[] >>
  `TAKE k slots ++ DROP k slots = slots` by simp[] >>
  pop_assum (SUBST1_TAC o SYM) >>
  irule LIST_REL_APPEND_suff >> simp[]
QED
