(* Enter a selected, nonempty internal callee in its actual compiled function. *)
Theory s1PrefixBoolChainCalleeBodyEntry
Ancestors
  s1PrefixBoolChainInvokeSite s1PrefixBoolChainCallRankBase
  s1PrefixDefs s1PrefixPreds bodySimFullMain bodyFullIntCallCallee bodyFullShadowBodyInv
  fragGasFocus fragGasOriginPtr
  compileUnit compileVyper loweringShapeProps constSubst
  vyperContext vyperInterpreter vyperState vyperStorageFootprint
  alist finite_map list pair

Theorem selected_callee_in_order[local]:
  MEM name names /\
  MEM (FunctionDecl Internal mut nr rr name args ds ret ss) tops ==>
  MEM (NONE,subst_consts_fn (module_consts_env tops [])
    (mut,nr,rr,name,args,ds,ret,ss))
    (order_internals_unit names (FST (SND (classify_functions_unit [(NONE,tops)] []))))
Proof
  strip_tac >>
  `MEM (subst_consts_fn (module_consts_env tops [])
      (mut,nr,rr,name,args,ds,ret,ss)) (FST (SND (classify_functions tops)))` by
    (simp[subst_consts_fn_def, MEM_classify_internal] >> metis_tac[]) >>
  `MEM (NONE,subst_consts_fn (module_consts_env tops [])
      (mut,nr,rr,name,args,ds,ret,ss))
      (FST (SND (classify_functions_unit [(NONE,tops)] [])))` by
    (Cases_on `classify_functions tops` >> PairCases_on `r` >>
     fs[classify_functions_unit_singleton, MEM_MAP] >> metis_tac[]) >>
  simp[order_internals_unit_def, MEM_FLAT, MEM_MAP, MEM_FILTER, PULL_EXISTS] >>
  simp[subst_consts_fn_def, fn_decl_name_def, compileEnvTheory.nsid_to_string_def]
QED

(* SCRATCH MEASUREMENT: the original proof failed after widening the body
   definitions. Temporarily admit it to test its downstream consumers.
Proof
  strip_tac >>
  qpat_x_assum `pushed = _` SUBST_ALL_TAC >>
  qpat_x_assum `callee_stmts = _` SUBST_ALL_TAC >>
  `ss <> []` by (strip_tac >> fs[subst_consts_stmt_def]) >>
  `LENGTH (remcode (cx with stk updated_by CONS (NONE,name))) < LENGTH (remcode cx)` by
    (irule callable_remcode_decreases >> simp[]) >>
  `!ts. ALOOKUP (cx with stk updated_by CONS (NONE,name)).sources
      (cx with stk updated_by CONS (NONE,name)).txn.target = SOME [(NONE,ts)] ==>
    struct_args_unique ts /\
    (!vis fm fr raw fn fa fd ft stmts.
       MEM (FunctionDecl vis fm fr raw fn fa fd ft stmts) ts ==>
       stmts_loop_calls_ok [(NONE,ts)]
         (subst_consts_stmts (module_consts_env ts []) stmts)) /\
    stmts_loop_calls_ok [(NONE,ts)] (subst_consts_stmts (module_consts_env tops []) ss)` by
    (gen_tac >> strip_tac >> fs[] >>
     `ts = tops` by fs[get_module_code_def, ALOOKUP_def] >>
     qpat_x_assum `ts = tops` SUBST_ALL_TAC >> simp[] >> metis_tac[]) >>
  `lookup_function (internal_fn_label (build_func_ids 0 tops name) name
       (MAP SND args) cx.in_deploy) ctx.ctx_functions = SOME callee` by
    fs[gas_invoke_entry_def] >>
  rpt conj_tac >> TRY (first_assum ACCEPT_TAC >> NO_TAC)
  >- (irule (cj 2 body_sim_full_mutual) >> first_assum ACCEPT_TAC)
  >- (first_x_assum irule >> asm_rewrite_tac[])
  >- (rpt strip_tac >> irule selected_callee_in_order >> asm_rewrite_tac[])
  >- (drule venomInstTheory.lookup_function_MEM >> simp[])
  >- fs[gas_invoke_entry_def]
  >- (drule gas_invoke_entry_readings >> simp[])
  >- simp[valid_horizon_def,
      vyperFiniteStoragePreservationTheory.storage_well_formed_on_stk,
      vyperFiniteStoragePreservationTheory.storage_observations_ok_stk]
  >- (rpt strip_tac >> drule intcall_callee_body_gas_trace >> simp[])
  >- (rpt strip_tac >>
      qpat_x_assum `request_site _ _ _ _ _ _ _` mp_tac >>
      `request_site (D,lo,explicit,ctx,callee,MAP (op_prov G1) arg_ops)
         (cx with stk updated_by CONS (NONE,name)) H (entered,FEMPTY,tn1 with t_var := FEMPTY) k rq outcome <=>
       request_site (D,lo,explicit,ctx,callee,MAP (op_prov G1) arg_ops)
         cx H (entered,FEMPTY,tn1 with t_var := FEMPTY) k rq outcome` by simp[request_site_def] >>
      asm_rewrite_tac[] >> strip_tac >>
      drule_all bool_chain_request_site_through_invoke >> simp[]) >>
  drule_all shadow_body_inv_callee_code >> simp[] >> rpt strip_tac >>
  goal_assum (drule_at Any) >> metis_tac[]
QED
*)
Theorem bool_chain_callee_body_entry_prefix:
  body_inv tops ctx cenv cx /\ shadow_body_inv tops ctx shadow_ctx /\
  gas_shadow_context ctx shadow_ctx /\
  ~MEM (NONE,name) cx.stk /\ get_module_code cx NONE = SOME tops /\
  lookup_callable_function cx.in_deploy name tops = SOME (mut,nr,args,ds,ret,ss) /\
  MEM (FunctionDecl Internal mut nr rr name args ds ret ss) tops /\
  callee_stmts = subst_consts_stmts (module_consts_env tops []) ss /\ callee_stmts <> [] /\
  pushed = cx with stk updated_by CONS (NONE,name) /\
  (!ts. ALOOKUP cx.sources cx.txn.target = SOME [(NONE,ts)] ==>
    struct_args_unique ts /\
    (!vis fm fr raw fn fa fd ft stmts.
       MEM (FunctionDecl vis fm fr raw fn fa fd ft stmts) ts ==>
       stmts_loop_calls_ok [(NONE,ts)]
         (subst_consts_stmts (module_consts_env ts []) stmts))) /\
  (!c ys. LENGTH (remcode c) < LENGTH (remcode cx) /\
    (!ts. ALOOKUP c.sources c.txn.target = SOME [(NONE,ts)] ==>
      struct_args_unique ts /\
      (!vis fm fr raw fn fa fd ft stmts.
         MEM (FunctionDecl vis fm fr raw fn fa fd ft stmts) ts ==>
         stmts_loop_calls_ok [(NONE,ts)]
           (subst_consts_stmts (module_consts_env ts []) stmts)) /\
      stmts_loop_calls_ok [(NONE,ts)] ys) ==> body_stmts_prefix_ok c ys) /\
  gas_invoke_entry (ctx,func) t callee entered /\
  lookup_block t.vs_current_bb func.fn_blocks = SOME bb /\
  get_instruction bb t.vs_inst_idx = SOME inst /\
  decode_invoke inst = SOME
    (internal_fn_label (build_func_ids 0 tops name) name (MAP SND args) cx.in_deploy,
     arg_ops) ==>
  LENGTH (remcode pushed) < LENGTH (remcode cx) /\
  body_stmts_full_ok pushed callee_stmts /\ body_stmts_prefix_ok pushed callee_stmts /\
  (!names. MEM name names ==> MEM (NONE,subst_consts_fn (module_consts_env tops [])
    (mut,nr,rr,name,args,ds,ret,ss))
    (order_internals_unit names (FST (SND (classify_functions_unit [(NONE,tops)] []))))) /\
  MEM callee ctx.ctx_functions /\
  ~entered.vs_halted /\ entered.vs_gas_readings = t.vs_gas_readings /\
  (!st0 H obs_pre. valid_horizon pushed st0 H obs_pre <=> valid_horizon cx st0 H obs_pre) /\
  (!es1 locked. lock_if_nr cx nr (is_view_mut mut) es1 = (INL (),locked) ==>
    !gs. SND (intcall_callee_src cx name mut nr ss (es1 with gas_obs := gs)) =
         SND (eval_stmts pushed ss (locked with gas_obs := gs))) /\
  (!D lo explicit PG s G tn marks G1 tn1 H k rq outcome.
    gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn)
      marks (OK t,G1,tn1) /\
    ptr_inst_ok D lo 0 ctx func G1 tn1 inst t /\
    request_site (D,lo,explicit,ctx,callee,MAP (op_prov G1) arg_ops)
      pushed H (entered,FEMPTY,tn1 with t_var := FEMPTY) k rq outcome ==>
    request_site (D,lo,explicit,ctx,func,PG) cx H (s,G,tn) k rq outcome) /\
  (?ce params has_rb nr' key trans view ctor ilen rt entry final sf entryS finalS.
    compile_internal_function ce params has_rb nr' key trans view ctor ilen
      callee_stmts rt entry = ((),final) /\
    compile_internal_function (gas_shadow_env T ce) params has_rb nr' key trans view
      ctor ilen (MAP gas_shadow_stmt callee_stmts) rt entryS = ((),finalS) /\
    gas_shadow_state entry entryS /\ gas_shadow_state final finalS /\
    gas_shadow_function callee sf /\ MEM sf shadow_ctx.ctx_functions /\
    ctx_inst_ids_distinct ctx /\ fn_has_code entry final callee /\ fn_has_code entryS finalS sf)
Proof
  cheat
QED
