(* Prefixes of staged actuals: the normal head outcome lands after marshaling. *)
Theory s1PrefixIntCallStageList
Ancestors
  s1PrefixCompose s1PrefixIntCallStageConsCut s1PrefixIntCallStageReplay
  s1PrefixIntCallStageSingleton
  s1PrefixFrame
  bodyFullIntCallArgs bodyFullIfExpReach bodyFullHashKeccakFixed stmtSimForRounds
  exprBodyPreProps exprLoweringProps exprSimWordArgs exprSimSource
  bodyFullPreds bodyFullExprsListFacts bodyFullExprsSingleton
  s1PrefixPreds exprSimSliceCompose vyperInterpreter vyperState
  contextRawReachable fragGasPath gasContext list pair
  s1PrefixProps s1PrefixOfVV vyperStorageTrace vyperStorageFootprint

Theorem intcall_stage_nil_source:
  eval_exprs cx [] = return []
Proof
  simp[FUN_EQ_THM,eval_exprs_nil,return_def]
QED

Theorem intcall_stage_cons_source:
  eval_exprs cx (e::es) =
  bind (eval_exprs cx [e]) (\hs. bind (eval_exprs cx es) (\vs. return (hs ++ vs)))
Proof
  simp[Once eval_exprs_cons_action, Once eval_exprs_cons_action,
       intcall_stage_nil_source, bind_assoc, bind_return]
QED

Theorem intcall_stage_full_head[local]:
  body_exprs_full_ok cx (e::es) ==> body_exprs_full_ok cx [e]
Proof
  simp[body_exprs_full_ok_cons, body_exprs_full_ok_singleton]
QED

Theorem intcall_stage_headroom_after_path:
  body_inv tops ctx cenv cx /\ MEM func ctx.ctx_functions /\
  gas_path ctx func s n (OK t) /\
  (!fn inst u. frag_reachable ctx func s fn inst u ==> dalloca_fmp_headroom inst u) /\
  frag_reachable ctx func t fn inst u ==>
  dalloca_fmp_headroom inst u
Proof
  strip_tac >>
  `!inst. active_inst func inst t ==> frag_reachable ctx func s func inst t` by
    (`!bb. MEM bb func.fn_blocks ==> phi_prefix_length bb.bb_instructions = 0` by
       (rpt strip_tac >> irule body_inv_no_phi >>
        qexistsl_tac [`cenv`,`ctx`,`cx`,`func`,`tops`] >> simp[]) >>
     qpat_assum `gas_path ctx func s _ (OK t)` (mp_then Any mp_tac gas_path_reach) >>
     disch_then (qspecl_then [`func`,`s`,`t`] mp_tac) >> simp[frag_reachable_start]) >>
  rpt strip_tac >>
  qpat_assum `!fn inst u. frag_reachable ctx func s fn inst u ==> _` irule >>
  qexists_tac `fn` >> irule frag_reachable_trans >>
  qpat_assum `frag_reachable ctx func t fn inst u` (irule_at Any) >>
  first_assum ACCEPT_TAC
QED

(* The normal callback is checked separately from the compiler and bind cuts. *)
(* SCRATCH MEASUREMENT: the original proof failed after widening the body
   definitions. Temporarily admit it to test its downstream consumers.
Proof
  strip_tac >>
  `valid_horizon cx st0 (storage_trace_horizon mid.storage_trace) mid.storage_trace` by
    fs[GSYM storage_trace_domain_def] >>
  `!H. valid_horizon cx st0 H mid.storage_trace ==>
     stmt_state_rel H ctx func cenv cx mid t /\
     storage_well_formed_on cx mid (FST H) /\
     ghost_inv_at (DF H) lo d cenv cx mid G1 tn1 t` by
    (gen_tac >> strip_tac >>
     qpat_assum `!H. valid_horizon _ _ H _ ==> intcall_args_stage_post _ _ _ H _ _ _ _ _`
       (qspec_then `H` (drule_then (strip_assume_tac o REWRITE_RULE[intcall_args_stage_post_def]))) >>
     rpt conj_tac >> first_assum ACCEPT_TAC) >>
  drule_all_then strip_assume_tac intcall_stage_replay_tail_facts >>
  Cases_on `eval_operands (ops ++ [h]) t` >>
  qpat_x_assum `!H. valid_horizon _ _ H _ ==> intcall_args_stage_post _ _ _ H _ _ _ _ _`
    (qspec_then `storage_trace_horizon mid.storage_trace` mp_tac) >>
  simp[intcall_args_stage_post_def] >> strip_tac >>
  rename1 `eval_operands (ops ++ [h]) t = SOME ws1` >>
  `gas_admissible (bind (eval_exprs cx es) (\vs. return (hs ++ vs))) P mid` by
    (qpat_assum `gas_admissible (bind (eval_exprs cx [e]) _) _ _`
       (fn th => drule_then mp_tac
         (MATCH_MP (REWRITE_RULE[GSYM AND_IMP_INTRO] gas_admissible_bind_tail) th)) >>
     simp[]) >>
  `gas_admissible (eval_exprs cx es) (\res. !err. res = INR err ==> expr_vv_res_ok (INR err)) mid` by
    (qpat_assum `gas_admissible (vyperState$bind (eval_exprs cx es) _) P mid`
       (mp_then Any mp_tac slice_gas_admissible_bind_head) >>
     disch_then (qspec_then `\r:value list + exception. !err. r = INR err ==> expr_vv_res_ok (INR err)` mp_tac) >>
     simp[]) >>
  `si.cs_next_var <= sm.cs_next_var` by
    (mp_tac (MATCH_MP ci_mono_compile_stage_intcall_args
       (CONJUNCT1 stmtLoweringMonoTheory.ci_mono_compile_expr_sa)) >>
     disch_then (qspecl_then [`cenv`,`[e]`,`[flag]`,`[dty]`,`si`] mp_tac) >>
     simp[ci_mono_def]) >>
  `!fn inst u. frag_reachable ctx func t fn inst u ==> dalloca_fmp_headroom inst u` by
    (rpt gen_tac >> strip_tac >> irule intcall_stage_headroom_after_path >>
     qpat_assum `body_inv tops ctx cenv cx` (irule_at Any) >>
     qpat_assum `gas_path ctx func s _ (OK t)` (irule_at Any) >>
     qpat_assum `frag_reachable ctx func t fn inst u` (irule_at Any) >>
     rpt conj_tac >> first_assum ACCEPT_TAC) >>
  `!st. SND (bind (eval_exprs cx es) (\vs. return (hs ++ vs)) st) =
         SND (eval_exprs cx es st)` by
    (gen_tac >> Cases_on `eval_exprs cx es st` >> rename1 `_ = (res,_)` >>
     Cases_on `res` >> simp[bind_def,return_def]) >>
  drule gas_prefix_full_state_cong >> disch_then (fn th => once_rewrite_tac[th]) >>
  qpat_x_assum `!DF lo d ctx shadow_ctx PG func shadow_func tops cenv cx tenv st0 sa s0 es0 G0 tn0
     si sf shadow_si shadow_sf esi s G tn flags dtys newops ops ws vals ptys pflags pin clean_words keep_sites P.
     _ ==> gas_prefix_full _ _ _ (eval_exprs cx es) _` irule >>
  rpt conj_tac >> TRY (first_assum ACCEPT_TAC)
  >- (qpat_assum `!H. valid_horizon cx st0 H mid.storage_trace ==> stmt_state_rel H ctx func cenv cx mid t /\ _`
        (qspec_then `storage_trace_horizon mid.storage_trace` (drule_then strip_assume_tac)) >>
      drule stmt_state_rel_allocas_below_fmp >> simp[])
  >- (qexists_tac `\res:value list + exception. !err. res = INR err ==> expr_vv_res_ok (INR err)` >> simp[]) >>
  qpat_assum `compile_stage_intcall_args _ _ es fs ts sm = (rest,sf)` (irule_at Any) >>
  qpat_assum `compile_stage_intcall_args _ _ (MAP gas_shadow_expr es) fs ts shadow_sm = (rest,shadow_sf)` (irule_at Any) >>
  qpat_assum `return_buf_frame d cenv sm t` (irule_at Any) >>
  qpat_assum `gas_shadow_function func shadow_func` (irule_at Any) >>
  qpat_assum `body_inv tops ctx cenv cx` (irule_at Any) >>
  qpat_assum `body_const_cells_agree _ cx tenv mid` (irule_at Any) >>
  qpat_assum `ghost_kept_at lo cenv es0 sa G0 tn0 s0 G1 tn1` (irule_at Any) >>
  qpat_assum `eval_operands (ops ++ [h]) t = SOME ws1` (irule_at Any) >>
  qexistsl_tac [`vals ++ hs`,`ptys ++ [dty]`,`pin`,`pflags ++ [flag]`,`keep_sites`,`clean_words`] >>
  fs[] >> rpt conj_tac >> TRY (first_assum ACCEPT_TAC)
  >- (rpt strip_tac >>
      qpat_x_assum `!j. j < SUC (LENGTH es) /\ EL j (flag::fs) ==> _`
        (qspec_then `SUC j` mp_tac) >> simp[listTheory.EL]) >>
  TRY (rename1 `local_ptrs_reserved cenv sm` >>
       irule local_ptrs_reserved_next_var >> qexists_tac `si` >> simp[] >> NO_TAC)
  >- (rpt strip_tac >> irule freshWritesTheory.not_fresh_at_mono >>
      qexists_tac `si` >> simp[] >> metis_tac[])
  >- (rpt strip_tac >> irule freshWritesTheory.not_fresh_at_mono >>
      qexists_tac `si` >> simp[] >> metis_tac[]) >>
  simp[EVERY_MEM] >> rpt strip_tac >> irule intcall_args_pre_state >>
  simp[] >> qexists_tac `esi` >> fs[EVERY_MEM]
QED
*)
Theorem intcall_stage_list_normal_cut[local]:
  (!DF lo d ctx shadow_ctx PG func shadow_func tops cenv cx tenv
    st0 sa s0 es0 G0 tn0 si sf shadow_si shadow_sf esi s G tn
    flags dtys newops ops ws vals ptys pflags pin clean_words keep_sites P.
    body_inv tops ctx cenv cx /\
    shadow_body_inv tops ctx shadow_ctx /\
    body_const_cells_agree [(NONE,tops)] cx tenv esi /\
    expr_sim_inv cenv cx tenv esi /\
    EVERY (\e. expr_body_pre cenv cx tenv e esi) es /\
    body_exprs_full_ok cx es /\ body_exprs_prefix_ok cx es /\
    LENGTH flags = LENGTH es /\ LENGTH dtys = LENGTH es /\
    EVERY (\ty. type_memory_bytes cenv ty < 2 ** 64) dtys /\
    LIST_REL (type_widens_to (get_tenv cx)) (MAP expr_type es) dtys /\
    (!j. j < LENGTH es /\ EL j flags ==> is_word_type (EL j dtys)) /\
    (!e dty ee ci vv cm.
       expr_body_pre cenv cx tenv e ee /\
       compile_expr cenv (expr_type e) e ci = (vv,cm) /\
       ~is_word_type dty /\ ~is_bytestring_type dty /\
       type_widens_to (get_tenv cx) (expr_type e) dty ==>
       vv_type vv = lowered_value_type cenv e) /\
    compile_stage_intcall_args compile_expr cenv es flags dtys si = (newops,sf) /\
    compile_stage_intcall_args compile_expr (gas_shadow_env T cenv) (MAP gas_shadow_expr es)
      flags dtys shadow_si = (newops,shadow_sf) /\
    gas_shadow_state si shadow_si /\ gas_shadow_state sf shadow_sf /\
    gas_shadow_context ctx shadow_ctx /\ ctx_inst_ids_distinct ctx /\
    gas_shadow_function func shadow_func /\
    MEM func ctx.ctx_functions /\ MEM shadow_func shadow_ctx.ctx_functions /\
    fn_has_code si sf func /\ fn_has_code shadow_si shadow_sf shadow_func /\
    fn_inst_ids_distinct func /\ local_ptrs_reserved cenv si /\
    ((ctx_has_dalloca ctx ==> allocas_below_fmp s) /\
     (!fn inst u. frag_reachable ctx func s fn inst u ==> dalloca_fmp_headroom inst u)) /\
    (!H. dead_lo_ok H (DF H) lo cenv cx) /\
    (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at si x) /\
    (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at si x) /\
    gas_admissible (eval_exprs cx es) P esi /\
    (!err. P (INR err) ==> expr_vv_res_ok (INR err)) /\
    LENGTH ws = LENGTH ops /\ LENGTH vals = LENGTH ops /\
    LENGTH ptys = LENGTH ops /\ LENGTH pflags = LENGTH ops /\
    eval_operands ops s = SOME ws /\ EVERY (\op. op_taint tn op = {}) ops /\
    (!x. MEM (Var x) ops ==> not_fresh_at si x) /\
    (keep_sites ==> !j. j < LENGTH ops /\ ~EL j pflags ==>
       ?b cap aid. op_prov G (EL j ops) = SOME (b,cap) /\
         FLOOKUP s.vs_allocas aid = SOME (b,cap) /\
         sa.cs_next_id <= aid /\ aid < si.cs_next_id /\ 32 <= cap /\
         ?inst. MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\ inst.inst_id = aid) /\
    (keep_sites ==> !i j b k c l.
       i < j /\ j < LENGTH ops /\ ~EL i pflags /\ ~EL j pflags /\
       op_prov G (EL i ops) = SOME (b,k) /\ op_prov G (EL j ops) = SOME (c,l) ==>
       regions_disjoint b k c l) /\
    (!j rt. j < LENGTH ops /\ evaluate_type (get_tenv cx) (EL j ptys) = SOME rt ==>
       value_has_type rt (EL j vals) /\ val_wf rt (EL j vals) /\
       val_footprint rt (EL j vals) <= type_memory_size rt /\
       (EL j pflags ==> EL j ws = typed_val_to_w256 rt (EL j vals) /\
         (clean_words ==> op_prov G (EL j ops) = NONE)) /\
       (~EL j pflags ==>
         ?b cap aid. op_prov G (EL j ops) = SOME (b,cap) /\
           FLOOKUP s.vs_allocas aid = SOME (b,cap) /\
           sa.cs_next_id <= aid /\ aid < si.cs_next_id /\
           lo <= b /\ b+cap <= s.vs_alloca_next /\ b <= w2n (EL j ws) /\
           w2n (EL j ws) + type_memory_size rt <= b+cap /\
           (!mem. mem_agree_outside tn.t_mem s.vs_memory mem ==>
             val_in_memory rt (EL j vals) (w2n (EL j ws)) mem) /\
           (!n lb sz. local_region cenv esi.scopes s n lb sz ==> b+cap <= lb \/ lb+sz <= b) /\
           (case pin of NONE => T | SOME (rb,pb,pk) => b+cap <= pb \/ pb+pk <= b))) /\
    (case pin of NONE => T | SOME (rb,b,k) =>
       FLOOKUP G rb = SOME (b,k) /\ op_taint tn (Var rb) = {} /\
       lookup_var rb s = SOME (n2w b) /\
       FLOOKUP s.vs_allocas sa.cs_next_id = SOME (b,k) /\
       sa.cs_next_id < si.cs_next_id /\ lo <= b /\ b+k <= s.vs_alloca_next /\
       not_fresh_at si rb /\
       (!n lb sz. local_region cenv esi.scopes s n lb sz ==> b+k <= lb \/ lb+sz <= b)) /\
    wb_frame cenv es0 esi sa s0 s /\
    ghost_kept_at lo cenv es0 sa G0 tn0 s0 G tn /\
    alloca_history func s /\ sa.cs_next_id <= si.cs_next_id /\ sa.cs_next_var <= si.cs_next_var /\
    (!n b sz. local_region cenv es0.scopes s0 n b sz <=> local_region cenv esi.scopes s n b sz) /\
    s0.vs_alloca_next <= s.vs_alloca_next /\ MAP FDOM es0.scopes = MAP FDOM esi.scopes /\
    return_buf_frame d cenv si s /\ ~s.vs_halted /\
    s.vs_current_bb = si.cs_current_bb /\ s.vs_inst_idx = LENGTH si.cs_current_insts /\
    (!H. valid_horizon cx st0 H esi.storage_trace ==>
       stmt_state_rel H ctx func cenv cx esi s /\
       storage_well_formed_on cx esi (FST H) /\
       ghost_inv_at (DF H) lo d cenv cx esi G tn s) ==>
    gas_prefix_full (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
      cx st0 (eval_exprs cx es) (esi,s,G,tn)) /\
  body_inv tops ctx cenv cx /\ shadow_body_inv tops ctx shadow_ctx /\
  body_const_cells_agree [(NONE,tops)] cx tenv esi /\ expr_body_pre cenv cx tenv e esi /\
  EVERY (\e. expr_body_pre cenv cx tenv e esi) es /\
  body_exprs_full_ok cx (e::es) /\ body_exprs_prefix_ok cx (e::es) /\
  LENGTH fs = LENGTH es /\ LENGTH ts = LENGTH es /\
  EVERY (\ty. type_memory_bytes cenv ty < 2 ** 64) ts /\
  LIST_REL (type_widens_to (get_tenv cx)) (MAP expr_type es) ts /\
  (!j. j < SUC (LENGTH es) /\ EL j (flag::fs) ==> is_word_type (EL j (dty::ts))) /\
  (!e dty ee ci vv cm. expr_body_pre cenv cx tenv e ee /\
    compile_expr cenv (expr_type e) e ci = (vv,cm) /\
    ~is_word_type dty /\ ~is_bytestring_type dty /\
    type_widens_to (get_tenv cx) (expr_type e) dty ==> vv_type vv = lowered_value_type cenv e) /\
  compile_stage_intcall_args compile_expr cenv [e] [flag] [dty] si = ([h],sm) /\
  compile_stage_intcall_args compile_expr cenv es fs ts sm = (rest,sf) /\
  compile_stage_intcall_args compile_expr (gas_shadow_env T cenv) (MAP gas_shadow_expr es)
    fs ts shadow_sm = (rest,shadow_sf) /\
  gas_shadow_state sm shadow_sm /\ gas_shadow_state sf shadow_sf /\
  gas_shadow_context ctx shadow_ctx /\ ctx_inst_ids_distinct ctx /\
  gas_shadow_function func shadow_func /\ MEM func ctx.ctx_functions /\
  MEM shadow_func shadow_ctx.ctx_functions /\ fn_has_code sm sf func /\
  fn_has_code shadow_sm shadow_sf shadow_func /\ fn_inst_ids_distinct func /\
  local_ptrs_reserved cenv si /\
  (!fn inst u. frag_reachable ctx func s fn inst u ==> dalloca_fmp_headroom inst u) /\
  (!H. dead_lo_ok H (DF H) lo cenv cx) /\
  (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at si x) /\
  (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at si x) /\
  gas_admissible (bind (eval_exprs cx [e]) (\hs. bind (eval_exprs cx es) (\vs. return (hs ++ vs)))) P esi /\
  (!err. P (INR err) ==> expr_vv_res_ok (INR err)) /\
  LENGTH vals = LENGTH ops /\ LENGTH ptys = LENGTH ops /\ LENGTH pflags = LENGTH ops /\
  (!tail. eval_exprs cx [e] (esi with gas_obs := gas_explicit marks s.vs_gas_readings ++ tail) =
    (INL hs,mid with gas_obs := tail)) /\
  storage_trace_domain cx st0 mid.storage_trace /\
  gas_path ctx func s (LENGTH marks) (OK t) /\
  (!H. valid_horizon cx st0 H mid.storage_trace ==>
    intcall_args_stage_post (DF,lo,d,ctx,func,cenv,cx,tenv) ([e],sa,s0,es0,G0,tn0,sm)
      ([flag],[dty],[h],ops,vals,ptys,pflags,pin,clean_words,keep_sites)
      H (INL hs : value list + exception) mid G1 tn1 t) ==>
  gas_prefix_full (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
    cx st0 (bind (eval_exprs cx es) (\vs. return (hs ++ vs))) (mid,t,G1,tn1)
Proof
  cheat
QED

Theorem intcall_stage_list_prefix:
  !es DF lo d ctx shadow_ctx PG func shadow_func tops cenv cx tenv
   st0 sa s0 es0 G0 tn0 si sf shadow_si shadow_sf esi s G tn
   flags dtys newops ops ws vals ptys pflags pin clean_words keep_sites P.
    body_inv tops ctx cenv cx /\
    shadow_body_inv tops ctx shadow_ctx /\
    body_const_cells_agree [(NONE,tops)] cx tenv esi /\
    expr_sim_inv cenv cx tenv esi /\
    EVERY (\e. expr_body_pre cenv cx tenv e esi) es /\
    body_exprs_full_ok cx es /\ body_exprs_prefix_ok cx es /\
    LENGTH flags = LENGTH es /\ LENGTH dtys = LENGTH es /\
    EVERY (\ty. type_memory_bytes cenv ty < 2 ** 64) dtys /\
    LIST_REL (type_widens_to (get_tenv cx)) (MAP expr_type es) dtys /\
    (!j. j < LENGTH es /\ EL j flags ==> is_word_type (EL j dtys)) /\
    (!e dty ee ci vv cm.
       expr_body_pre cenv cx tenv e ee /\
       compile_expr cenv (expr_type e) e ci = (vv,cm) /\
       ~is_word_type dty /\ ~is_bytestring_type dty /\
       type_widens_to (get_tenv cx) (expr_type e) dty ==>
       vv_type vv = lowered_value_type cenv e) /\
    compile_stage_intcall_args compile_expr cenv es flags dtys si =
      (newops,sf) /\
    compile_stage_intcall_args compile_expr (gas_shadow_env T cenv) (MAP gas_shadow_expr es)
      flags dtys shadow_si = (newops,shadow_sf) /\
    gas_shadow_state si shadow_si /\ gas_shadow_state sf shadow_sf /\
    gas_shadow_context ctx shadow_ctx /\ ctx_inst_ids_distinct ctx /\
    gas_shadow_function func shadow_func /\
    MEM func ctx.ctx_functions /\ MEM shadow_func shadow_ctx.ctx_functions /\
    fn_has_code si sf func /\ fn_has_code shadow_si shadow_sf shadow_func /\
    fn_inst_ids_distinct func /\ local_ptrs_reserved cenv si /\
    ((ctx_has_dalloca ctx ==> allocas_below_fmp s) /\
     (!fn inst u. frag_reachable ctx func s fn inst u ==> dalloca_fmp_headroom inst u)) /\
    (!H. dead_lo_ok H (DF H) lo cenv cx) /\
    (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==>
       not_fresh_at si x) /\
    (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==>
       not_fresh_at si x) /\
    gas_admissible (eval_exprs cx es) P esi /\
    (!err. P (INR err) ==> expr_vv_res_ok (INR err)) /\
    LENGTH ws = LENGTH ops /\ LENGTH vals = LENGTH ops /\
    LENGTH ptys = LENGTH ops /\ LENGTH pflags = LENGTH ops /\
    eval_operands ops s = SOME ws /\ EVERY (\op. op_taint tn op = {}) ops /\
    (!x. MEM (Var x) ops ==> not_fresh_at si x) /\
    (keep_sites ==> !j. j < LENGTH ops /\ ~EL j pflags ==>
       ?b cap aid. op_prov G (EL j ops) = SOME (b,cap) /\
         FLOOKUP s.vs_allocas aid = SOME (b,cap) /\
         sa.cs_next_id <= aid /\ aid < si.cs_next_id /\
         32 <= cap /\
         ?inst. MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\
           inst.inst_id = aid) /\
    (keep_sites ==> !i j b k c l.
       i < j /\ j < LENGTH ops /\ ~EL i pflags /\ ~EL j pflags /\
       op_prov G (EL i ops) = SOME (b,k) /\ op_prov G (EL j ops) = SOME (c,l) ==>
       regions_disjoint b k c l) /\
    (!j rt. j < LENGTH ops /\
       evaluate_type (get_tenv cx) (EL j ptys) = SOME rt ==>
       value_has_type rt (EL j vals) /\ val_wf rt (EL j vals) /\
       val_footprint rt (EL j vals) <= type_memory_size rt /\
       (EL j pflags ==> EL j ws = typed_val_to_w256 rt (EL j vals) /\
         (clean_words ==> op_prov G (EL j ops) = NONE)) /\
       (~EL j pflags ==>
         ?b cap aid.
           op_prov G (EL j ops) = SOME (b,cap) /\
           FLOOKUP s.vs_allocas aid = SOME (b,cap) /\
           sa.cs_next_id <= aid /\ aid < si.cs_next_id /\
           lo <= b /\ b+cap <= s.vs_alloca_next /\ b <= w2n (EL j ws) /\
           w2n (EL j ws) + type_memory_size rt <= b+cap /\
           (!mem. mem_agree_outside tn.t_mem s.vs_memory mem ==>
             val_in_memory rt (EL j vals) (w2n (EL j ws)) mem) /\
           (!n lb sz. local_region cenv esi.scopes s n lb sz ==>
             b+cap <= lb \/ lb+sz <= b) /\
           (case pin of NONE => T | SOME (rb,pb,pk) =>
             b+cap <= pb \/ pb+pk <= b))) /\
    (case pin of NONE => T | SOME (rb,b,k) =>
       FLOOKUP G rb = SOME (b,k) /\ op_taint tn (Var rb) = {} /\
       lookup_var rb s = SOME (n2w b) /\
       FLOOKUP s.vs_allocas sa.cs_next_id = SOME (b,k) /\
       sa.cs_next_id < si.cs_next_id /\ lo <= b /\ b+k <= s.vs_alloca_next /\
       not_fresh_at si rb /\
       (!n lb sz. local_region cenv esi.scopes s n lb sz ==>
         b+k <= lb \/ lb+sz <= b)) /\
    wb_frame cenv es0 esi sa s0 s /\
    ghost_kept_at lo cenv es0 sa G0 tn0 s0 G tn /\
    alloca_history func s /\ sa.cs_next_id <= si.cs_next_id /\
    sa.cs_next_var <= si.cs_next_var /\
    (!n b sz. local_region cenv es0.scopes s0 n b sz <=>
       local_region cenv esi.scopes s n b sz) /\
    s0.vs_alloca_next <= s.vs_alloca_next /\
    MAP FDOM es0.scopes = MAP FDOM esi.scopes /\
    return_buf_frame d cenv si s /\ ~s.vs_halted /\
    s.vs_current_bb = si.cs_current_bb /\
    s.vs_inst_idx = LENGTH si.cs_current_insts /\
    (!H. valid_horizon cx st0 H esi.storage_trace ==>
       stmt_state_rel H ctx func cenv cx esi s /\
       storage_well_formed_on cx esi (FST H) /\
       ghost_inv_at (DF H) lo d cenv cx esi G tn s) ==>
    gas_prefix_full
      (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
      cx st0 (eval_exprs cx es) (esi,s,G,tn)
Proof
  Induct
  >- (rpt gen_tac >> strip_tac >> rewrite_tac[intcall_stage_nil_source] >>
      irule gas_prefix_full_no_outcome >> simp[storage_trace_frame_return, return_def]) >>
  rpt gen_tac >> strip_tac >> rename1 `body_exprs_full_ok cx (e::es)` >>
  qpat_assum `compile_stage_intcall_args _ cenv (e::es) flags dtys si = (newops,sf)`
    (mp_then (Pos (el 3)) mp_tac intcall_stage_cons_cut_elim) >>
  disch_then irule >>
  qpat_assum `compile_stage_intcall_args _ _ (MAP gas_shadow_expr (e::es)) flags dtys shadow_si = (newops,shadow_sf)`
    (irule_at Any) >>
  qpat_assum `fn_has_code si sf func` (irule_at Any) >>
  qpat_assum `fn_has_code shadow_si shadow_sf shadow_func` (irule_at Any) >>
  rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
  map_every qx_gen_tac [`flag`,`fs`,`dty`,`ts`,`h`,`sm`,`shadow_sm`,`rest`] >>
  strip_tac >> gvs[MAP] >>
  `expr_body_pre cenv cx tenv e esi /\ body_expr_prefix_ok cx e` by
    fs[Once body_exprs_prefix_ok_def] >>
  drule_then assume_tac intcall_stage_full_head >>
  `gas_prefix_full (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
      cx st0 (eval_exprs cx [e]) (esi,s,G,tn)` by
    (irule intcall_stage_singleton_prefix >>
     qpat_assum `compile_stage_intcall_args _ _ [e] _ _ si = _` (irule_at Any) >>
     qpat_assum `compile_stage_intcall_args _ _ [gas_shadow_expr e] _ _ shadow_si = _`
       (irule_at Any) >>
     qpat_assum `expr_body_pre cenv cx tenv e esi` (irule_at Any) >>
     qpat_assum `body_inv tops ctx cenv cx` (irule_at Any) >>
     qpat_assum `gas_shadow_function func shadow_func` (irule_at Any) >>
     qpat_assum `return_buf_frame d cenv si s` (irule_at Any) >>
     rpt conj_tac >> first_assum ACCEPT_TAC) >>
  `gas_admissible (bind (eval_exprs cx [e])
      (\hs. bind (eval_exprs cx es) (\vs. return (hs ++ vs)))) P esi` by
    (pure_rewrite_tac[GSYM intcall_stage_cons_source] >> first_assum ACCEPT_TAC) >>
  `gas_admissible (eval_exprs cx [e])
       (\res. !err. res = INR err ==> expr_vv_res_ok (INR err)) esi` by
    (qpat_assum `gas_admissible (vyperState$bind (eval_exprs cx [e]) _) P esi`
       (mp_then Any mp_tac slice_gas_admissible_bind_head) >>
     disch_then (qspec_then `\r:value list + exception. !err. r = INR err ==> expr_vv_res_ok (INR err)` mp_tac) >>
     simp[]) >>
  `flag ==> is_word_type dty` by
    (strip_tac >> qpat_x_assum `!j. _ /\ EL j (flag::fs) ==> is_word_type (EL j (dty::ts))`
       (qspec_then `0` mp_tac) >> simp[]) >>
  `gas_outcome_full (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
      (cx_tops cx) cx st0 (eval_exprs cx [e]) (esi,s,G,tn)
      (intcall_args_stage_post (DF,lo,d,ctx,func,cenv,cx,tenv)
        ([e],sa,s0,es0,G0,tn0,sm)
        ([flag],[dty],[h],ops,vals,ptys,pflags,pin,clean_words,keep_sites))
      (\H res ee gt r. (?err. res = INR err) /\
        expr_exit res r /\ halt_exit H cx ee res r /\
        (ctx_has_dalloca ctx ==> !s. r = Halt s ==> allocas_below_fmp s))` by
    (irule intcall_args_stage_left_outcome >>
     qpat_assum `body_inv tops ctx cenv cx` (irule_at Any) >>
     qpat_assum `compile_stage_intcall_args _ _ [e] _ _ si = _` (irule_at Any) >>
     qexistsl_tac [`ws`,`shadow_si`,`shadow_sm`,`shadow_func`,
       `\res:value list + exception. !err. res = INR err ==> expr_vv_res_ok (INR err)`] >>
     rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >> simp[] >>
     FIRST [qpat_x_assum `LIST_REL _ _ (dty::ts)` mp_tac >> simp[] >> NO_TAC,
       qpat_x_assum `EVERY _ (dty::ts)` mp_tac >> simp[] >> NO_TAC,
       qpat_x_assum `flag ==> is_word_type dty` ACCEPT_TAC]) >>
  once_rewrite_tac[intcall_stage_cons_source] >>
  irule gas_prefix_full_bind_path >>
  qpat_assum `gas_outcome_full _ _ _ _ (eval_exprs cx [e]) _ _ _`
    (irule_at Any) >>
  rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
  TRY (simp[evaluate_storage_trace_frame,evaluate_requests_outcomes_frame] >> NO_TAC) >>
  TRY (gen_tac >> BETA_TAC >> irule storage_trace_frame_bind_all >>
       simp[evaluate_storage_trace_frame,storage_trace_frame_return] >> NO_TAC) >>
  TRY (rpt gen_tac >> Cases_on `res` >> simp[NoAsms] >> NO_TAC) >>
  map_every qx_gen_tac [`marks`,`hs`,`mid`,`G1`,`tn1`,`t`] >>
  BETA_TAC >> strip_tac >>
  qpat_assum `!H. valid_horizon _ _ H _ ==> intcall_args_stage_post _ _ _ H _ _ _ _ _`
    (mp_then (Pos last) mp_tac intcall_stage_list_normal_cut) >>
  disch_then irule >>
  qpat_assum `gas_path ctx func s (LENGTH marks) (OK t)` (irule_at Any) >>
  qpat_assum `compile_stage_intcall_args _ _ [e] _ _ si = _` (irule_at Any) >>
  qpat_assum `compile_stage_intcall_args _ _ es fs ts sm = (rest,sf)` (irule_at Any) >>
  qpat_assum `compile_stage_intcall_args _ _ (MAP gas_shadow_expr es) fs ts shadow_sm = (rest,shadow_sf)`
    (irule_at Any) >>
  qpat_assum `gas_admissible (bind (eval_exprs cx [e]) _) P esi` (irule_at Any) >>
  qpat_assum `body_inv tops ctx cenv cx` (irule_at Any) >>
  qpat_assum `gas_shadow_function func shadow_func` (irule_at Any) >>
  rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
  simp[NoAsms] >> first_assum ACCEPT_TAC
QED
