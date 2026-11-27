(* Compose the supplied decoder and the omitted-default evaluation at a passing check. *)
Theory groupedDefaultPassingExecution
Ancestors
  groupedDefaultSuppliedCut groupedDefaultOmittedCut groupedSelectedOmittedReadiness
  groupedDefaultSuffixReadings groupedDefaultExitResult deployBodyReachability
  externalBodyFrame exprSimHypsDefs
  bodyFullIfExpReach bodyFullPathHistory vyperTypeABI venomExecProofs venomState
  contextCodegenRel contextRawReachable fragExec ptrDiscipline unitTransformDefs
  list rich_list vyperContext constSubstCorrect vyperABIEntries vyperStorageFootprint
  gasContext e2eDefs fragGasOriginPtr selectedAcceptedFold vyperState vyperInterpreter

(* ML quotation abbreviations; these expand in the theorem statement. *)
val pcx = ``initial_evaluation_context am.sources am.layouts tx NONE``;
val pst = ``initial_state am []``;
val pce = ``common.ec_env``;
val pce0 = ``^pce with ce_vars := FEMPTY``;
val penv = ``artifact_env art [(NONE,tops)] NONE``;
val pctx = ``unit.cu_context``;
val psh = ``shadow_unit.cu_context``;
val pexp = ``gas_explicit_sites ^pctx ^psh``;
val pentry = ``vs with <|vs_prev_bb := NONE; vs_current_bb := "__entry"; vs_inst_idx := 0|>``;
val ppos = ``LENGTH (args:(string # type) list) - LENGTH (ds:expr list)``;
val poff = ``4 + SUM (MAP tv_abi_size (TAKE ^ppos tvs))``;
val pallocated = ``\st s G tn (aid,q,base,tv).
  aid < st.cs_next_id /\ not_fresh_at st q /\ base < dimword (:256) /\
  FLOOKUP s.vs_allocas aid = SOME (base,type_memory_size tv) /\
  lookup_var q s = SOME (n2w base) /\ ptr_covers G tn q s (type_memory_size tv)``;
val pinitialized = ``\st s G tn (aid,q,base,tv) v.
  ^pallocated st s G tn (aid,q,base,tv) /\ value_has_type tv v /\
  (!mem. mem_agree_outside tn.t_mem s.vs_memory mem ==> val_in_memory tv v base mem)``;

Theorem grouped_passing_frag_headroom[local]:
  ctx.ctx_entry = SOME "__entry" /\
  venomInst$lookup_function "__entry" ctx.ctx_functions = SOME fn /\
  fn_entry_label fn = SOME "__entry" /\
  lookup_block "__entry" fn.fn_blocks = SOME bb /\ phi_prefix_length bb.bb_instructions = 0 /\
  (!b label. lookup_block label fn.fn_blocks = SOME b ==> phi_prefix_length b.bb_instructions = 0) /\
  gas_origin_ptr_path (D,0,exp,ctx,fn,[]) (^pentry,FEMPTY,entry_taint) marks (OK t,J,tz) /\
  (ctx_has_dalloca ctx ==> !f inst s. raw_reachable vs ctx f inst s ==> dalloca_fmp_headroom inst s) ==>
  !f inst s. frag_reachable ctx fn t f inst s ==> dalloca_fmp_headroom inst s
Proof
  strip_tac >> Cases_on `ctx_has_dalloca ctx`
  >- (`enters_block fn ^pentry ^pentry` by
        simp[enters_block_def, eval_phis_no_phi, venom_state_fupdfupds] >>
      `!i. active_inst fn i ^pentry ==> raw_reachable vs ctx fn i ^pentry` by
        (rpt strip_tac >> irule raw_reachable_entry >> simp[]) >>
      drule_then assume_tac gas_origin_ptr_path_erase >>
      `!i. active_inst fn i t ==> raw_reachable vs ctx fn i t` by
        (rpt strip_tac >> irule raw_reachable_gas_path >>
         qpat_assum `gas_path _ _ _ _ (OK t)` (irule_at Any) >>
         rpt conj_tac >> first_assum ACCEPT_TAC) >>
      rpt strip_tac >> drule raw_reachable_through_fragment >>
      disch_then (qspec_then `vs` mp_tac) >> simp[] >> metis_tac[]) >>
  rpt strip_tac >>
  `MEM fn ctx.ctx_functions` by metis_tac[venomInstTheory.lookup_function_MEM] >>
  drule_then drule frag_reachable_members >> strip_tac >>
  fs[ctx_has_dalloca_def, EXISTS_MEM, dalloca_fmp_headroom_def] >> metis_tac[]
QED

(* The full type evaluation and the slot types refer to the same index. *)
Theorem grouped_passing_slot_types[local]:
  OPT_MMAP (evaluate_type tenv) (MAP SND args) = SOME tvs /\
  MAP (\(n,_,ty,_). (n,ty)) vars = DROP p args /\
  MAP (\(_,_,_,tv). tv) slots = DROP p tvs ==>
  LIST_REL (\(_,_,ty,_) (_,_,_,tv). evaluate_type tenv ty = SOME tv) vars slots
Proof
  strip_tac >> drule OPT_MMAP_LIST_REL >> simp[LIST_REL_MAP1] >>
  disch_then (qspec_then `p` mp_tac o MATCH_MP LIST_REL_DROP) >>
  qpat_assum `MAP _ vars = _` (fn th => pure_rewrite_tac[GSYM th]) >>
  qpat_assum `MAP _ slots = _` (fn th => pure_rewrite_tac[GSYM th]) >>
  simp[LIST_REL_MAP1, LIST_REL_MAP2, combinTheory.o_DEF, pairTheory.LAMBDA_PROD]
QED

val passing_input = ``
  lower_vyper_runtime_unit tops rp = SOME unit /\
  source_typing_ok tops am tx /\ source_deployment_rel tops am tx /\
  check_contract F am.layouts tx.target [(NONE,tops)] = SOME art /\
  vyperInterpreter$lookup_function NONE tx.function_name External tops =
    SOME (mut,nr,args,raw,ret,fbody) /\
  MEM (FunctionDecl External mut nr rr tx.function_name args raw ret fbody) tops /\
  ds = subst_consts_exprs (module_consts_env tops []) raw /\
  ss = subst_consts_stmts (module_consts_env tops []) fbody /\
  MEM (mut,nr,rr,tx.function_name,args,ds,ret,ss) (FST (classify_functions tops)) /\
  package_external_group tops rp.rpol_target T (K global_nonreentrant_slot)
    (mut,nr,rr,tx.function_name,args,ds,ret,ss) = ExternalDefaults common entries specs off /\
  send_call_value mut ^pcx
    (initial_state am [FEMPTY] with <|outcomes := SOME vs.vs_outcomes; requests := []|>) =
    (INL (),es) /\ es.scopes = [FEMPTY] /\ es.immutables = am.immutables /\
  es.storage_trace = (^pst).storage_trace /\ storage_trace_domain ^pcx ^pst es.storage_trace /\
  (^pctx).ctx_entry = SOME "__entry" /\
  venomInst$lookup_function "__entry" (^pctx).ctx_functions = SOME fn /\
  fn_entry_label fn = SOME "__entry" /\
  lookup_block "__entry" fn.fn_blocks = SOME bb /\ phi_prefix_length bb.bb_instructions = 0 /\
  gas_shadow_context ^pctx ^psh /\ gas_shadow_function fn shfn /\
  MEM fn (^pctx).ctx_functions /\ MEM shfn (^psh).ctx_functions /\
  LENGTH ds <= LENGTH args /\ MEM (prefix,k) (abi_entries args ds) /\
  OPT_MMAP (evaluate_type (type_env tops)) (MAP SND args) = SOME tvs /\
  OPT_MMAP (evaluate_type (type_env tops)) (MAP SND prefix) = SOME provided /\
  calldata_decode_args s.vs_call_ctx.cc_calldata provided 0 = SOME tx.args /\
  LIST_REL (\arg tv. abi_decoder_coherent ^pce (type_env tops) (^pce).ce_struct_fields (SND arg) tv)
    args tvs /\
  4 + SUM (MAP tv_abi_size tvs) < dimword (:256) /\
  specs = MAP (\((n,ty),e). (n,ty,e)) (ZIP (DROP ^ppos args,ds)) /\
  compile_create_kwarg_allocas ^pce specs a = (vars,b) /\
  compile_init_kwargs ^pce vars ^poff k (Lit 0w) si = ((),sb) /\
  compile_init_kwargs (gas_shadow_env T ^pce) (MAP (\(n,p,ty,e). (n,p,ty,gas_shadow_expr e)) vars)
    ^poff k (Lit 0w) sha = ((),shb) /\
  fn_has_code si sb fn /\ fn_has_code sha shb shfn /\ gas_shadow_state si sha /\
  (!name op ty e. MEM (name,op,ty,e) vars ==>
    ?id q base. op = Var q /\ not_fresh_at si q /\ lookup_var q s = SOME (n2w base) /\
      MEM (mk_inst id ALLOCA [Lit (n2w (type_memory_bytes ^pce ty))] [q]) (fn_insts fn) /\
      FLOOKUP s.vs_allocas id = SOME (base,type_memory_bytes ^pce ty) /\
      base + type_memory_bytes ^pce ty < dimword (:256) /\ id < si.cs_next_id /\
      ptr_covers G tn q s (type_memory_bytes ^pce ty)) /\
  selected_registration_resources ^pctx fn site 0 si s /\
  (ctx_has_dalloca ^pctx ==> allocas_below_fmp s /\
    s.vs_alloca_next + pending_alloca_size fn s <= w2n s.vs_initial_fmp) /\
  unit_alloca_budget ^pctx < dimword (:256) /\ fn_inst_ids_distinct fn /\
  (!label bb. lookup_block label fn.fn_blocks = SOME bb ==> phi_prefix_length bb.bb_instructions = 0) /\
  body_inv tops ^pctx ^pce0 ^pcx /\ shadow_body_inv tops ^pctx ^psh /\
  get_tenv ^pcx = type_env tops /\ (^penv).type_defs = get_tenv ^pcx /\
  ~(^pce).ce_is_ctor /\ (^pce).ce_imm_alloca = NONE /\
  (^pce).ce_return_pc = NONE /\ (^pce).ce_return_buf = NONE /\ ctx_inst_ids_distinct ^pctx /\
  (!bb. MEM bb fn.fn_blocks ==> phi_prefix_length bb.bb_instructions = 0) /\
  (!H. dead_lo_ok H (cx_dead H ^pcx) 0 ^pce0 ^pcx) /\ tn.t_imm = {} /\
  (!H. valid_horizon ^pcx ^pst H es.storage_trace ==>
    stmt_state_rel H ^pctx fn ^pce0 ^pcx es s /\
    storage_well_formed_on ^pcx es (FST H) /\
    ghost_inv_at (cx_dead H ^pcx) 0 NONE ^pce0 ^pcx es G tn s) /\
  expr_sim_inv ^pce0 ^pcx ^penv es /\ alloca_history fn s /\
  (!D e. gas_origin_ptr_path (D,0,e,^pctx,fn,[]) (^pentry,FEMPTY,entry_taint) [] (OK s,G,tn)) /\
  s.vs_gas_readings = vs.vs_gas_readings /\ s.vs_call_ctx.cc_calldata = vs.vs_call_ctx.cc_calldata /\
  (ctx_has_dalloca ^pctx ==>
    !f inst u. raw_reachable vs ^pctx f inst u ==> dalloca_fmp_headroom inst u)``;

val passing_normal = ``
  ?slots last t J tz marks values ee u Gu tu.
    ALL_DISTINCT (MAP FST slots) /\ MAP (\(_,_,_,tv). tv) slots = DROP ^ppos tvs /\
    LIST_REL (\(name,op,ty,e) (id,q,base,tv).
      op = Var q /\ type_memory_bytes ^pce ty = type_memory_size tv /\
      not_fresh_at si q /\ lookup_var q s = SOME (n2w base) /\
      MEM (mk_inst id ALLOCA [Lit (n2w (type_memory_size tv))] [q]) (fn_insts fn) /\
      FLOOKUP s.vs_allocas id = SOME (base,type_memory_size tv) /\
      base + type_memory_size tv < dimword (:256) /\ id < si.cs_next_id /\
      ptr_covers G tn q s (type_memory_size tv)) vars slots /\
    MAP (\(name,_,ty,_). (name,ty)) vars = DROP ^ppos args /\
    MAP (\(_,_,_,e). e) vars = ds /\ LENGTH tx.args = ^ppos + k /\
    calldata_decode_args vs.vs_call_ctx.cc_calldata (TAKE ^ppos tvs) 0 =
      SOME (TAKE ^ppos tx.args) /\
    selected_registration_resources ^pctx fn site 0 last t /\
    (ctx_has_dalloca ^pctx ==> allocas_below_fmp t /\
      t.vs_alloca_next + pending_alloca_size fn t <= w2n t.vs_initial_fmp) /\
    selected_registration_frame s tn t tz /\ tz.t_mem SUBSET tn.t_mem /\
    (!D e. gas_origin_ptr_path (D,0,e,^pctx,fn,[]) (s,G,tn) [] (OK t,J,tz)) /\
    (!tail. eval_exprs ^pcx (DROP (LENGTH raw - (LENGTH args - LENGTH tx.args)) raw)
      (es with gas_obs := gas_explicit marks vs.vs_gas_readings ++ tail) =
      (INL values,ee with gas_obs := tail)) /\
    ((ee with gas_obs := []) = (es with gas_obs := [])) /\
    (!H. valid_horizon ^pcx ^pst H ee.storage_trace ==>
      gas_origin_ptr_path (cx_dead H ^pcx,0,^pexp,^pctx,fn,[]) (t,J,tz) marks (OK u,Gu,tu) /\
      LIST_REL (\(aid,q,base,tv) v.
        aid < sb.cs_next_id /\ not_fresh_at sb q /\ base < dimword (:256) /\
        FLOOKUP u.vs_allocas aid = SOME (base,type_memory_size tv) /\
        lookup_var q u = SOME (n2w base) /\ ptr_covers Gu tu q u (type_memory_size tv) /\
        value_has_type tv v /\
        (!mem. mem_agree_outside tu.t_mem u.vs_memory mem ==> val_in_memory tv v base mem))
        slots (DROP ^ppos tx.args ++ values) /\
      stmt_state_rel H ^pctx fn ^pce0 ^pcx (ee with gas_obs := []) u /\
      storage_well_formed_on ^pcx (ee with gas_obs := []) (FST H) /\
      ghost_inv_at (cx_dead H ^pcx) 0 NONE ^pce0 ^pcx (ee with gas_obs := []) Gu tu u /\
      (ee with gas_obs := []).scopes = es.scopes /\ alloca_history fn u /\
      (ctx_has_dalloca ^pctx ==> allocas_below_fmp u) /\
      ~u.vs_halted /\ u.vs_current_bb = sb.cs_current_bb /\ u.vs_inst_idx = LENGTH sb.cs_current_insts)``;

val passing_readings = ``
  (?tail. call_storage_ok am tx vs.vs_outcomes (gas_explicit marks vs.vs_gas_readings ++ tail)) ==>
  !tail. FST (call_external (SOME vs.vs_outcomes)
    (gas_explicit marks vs.vs_gas_readings ++ tail) am tx) <>
    INR (Error (RuntimeError "msg.gas: no gas reading"))``;

Theorem grouped_default_passing_execution_trace:
  ^passing_input ==>
  (?marks. source_unit_execution_correct_with ^psh marks tops ret am tx unit vs /\
    ^passing_readings /\
    (!tail res am' rqs obs.
      call_external_trace (SOME vs.vs_outcomes)
        (gas_explicit marks vs.vs_gas_readings ++ tail) am tx = (res,am',rqs,obs) ==>
      obs = []) /\
    (marks = [] \/ ?f (H : (bool # bytes32 # type_value) list # num list).
      venomInst$lookup_function "__entry" (^pctx).ctx_functions = SOME f /\
      ((?r J tz.
        gas_origin_ptr_path (cx_dead H ^pcx,0,^pexp,^pctx,f,[])
          (^pentry,FEMPTY,entry_taint) marks (r,J,tz)) \/
       (?leaf leaf_pg leaf_g leaf_tn finish.
        gas_origin_ptr_focus (cx_dead H ^pcx,0,^pexp,^pctx,f,[])
          (^pentry,FEMPTY,entry_taint) marks (leaf,leaf_pg,leaf_g,leaf_tn,finish))))) \/
  ^passing_normal
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all grouped_default_supplied_cut >>
  disch_then (qspec_then `[]` (qx_choosel_then [`slots`,`last`,`shlast`,`t`,`J`,`tz`]
    (map_every assume_tac o CONJUNCTS))) >>
  drule_all (SIMP_RULE bool_ss [] (Q.INST
    [`ce` |-> `^pce`, `c0` |-> `^pce0`, `env` |-> `^penv`, `cx` |-> `^pcx`]
    (SPEC_ALL grouped_selected_omitted_readiness))) >>
  qpat_assum `ds = _` (fn th =>
    disch_then (map_every assume_tac o CONJUNCTS o PURE_REWRITE_RULE [GSYM th] o Q.SPEC `k`)) >>
  drule_all grouped_passing_slot_types >> disch_tac >>
  `LIST_REL (\(n,dst,ty,e) (aid,q,base,tv).
    dst = Var q /\ runtime_constant_expr [(NONE,tops)] e /\ expr_type e = ty /\
    (!es'. expr_sim_inv ^pce0 ^pcx ^penv es' ==> expr_body_pre ^pce0 ^pcx ^penv e es') /\
    lower_value compile_expr ^pce0 ty e = lower_value compile_expr ^pce ty e /\
    lower_value compile_expr (gas_shadow_env T ^pce0) ty (gas_shadow_expr e) =
      lower_value compile_expr (gas_shadow_env T ^pce) ty (gas_shadow_expr e) /\
    evaluate_type (get_tenv ^pcx) ty = SOME tv /\
    type_memory_bytes ^pce ty = type_memory_size tv /\ type_memory_size tv + 64 < dimword (:256))
    (DROP k vars) (DROP k slots)` by
    (qpat_assum `LIST_REL (\(_,_,ty,_) (_,_,_,tv). evaluate_type _ ty = SOME tv) vars slots`
       (qspec_then `k` (strip_assume_tac o REWRITE_RULE [LIST_REL_EL_EQN]) o MATCH_MP LIST_REL_DROP) >>
     qpat_assum `LIST_REL (\(_,op,_,_) (_,q,_,_). op = Var q /\ _) vars slots`
       (qspec_then `k` (strip_assume_tac o REWRITE_RULE [LIST_REL_EL_EQN]) o MATCH_MP LIST_REL_DROP) >>
     qpat_assum `EVERY _ (DROP k vars)` (strip_assume_tac o REWRITE_RULE [EVERY_EL]) >>
     pure_rewrite_tac[LIST_REL_EL_EQN] >> conj_tac >- first_assum ACCEPT_TAC >>
     qx_gen_tac `i` >> strip_tac >>
     ntac 3 (qpat_x_assum `!j. j < LENGTH (DROP k vars) ==> _` (qspec_then `i` mp_tac)) >>
     `i < LENGTH vars - k` by fs[LENGTH_DROP] >>
     simp[pairTheory.UNCURRY, LENGTH_DROP] >> metis_tac[]) >>
  `!D e. gas_origin_ptr_path (D,0,e,^pctx,fn,[]) (^pentry,FEMPTY,entry_taint) [] (OK t,J,tz)` by
    (rpt gen_tac >> irule (SIMP_RULE bool_ss [APPEND_NIL]
       (Q.INST [`left` |-> `[]`] (SPEC_ALL gas_origin_ptr_path_append))) >>
     qpat_assum `!D e. gas_origin_ptr_path _ (_,FEMPTY,entry_taint) [] (OK s,G,tn)`
       (qspecl_then [`D`,`e`] (irule_at Any)) >>
     simp[]) >>
  `alloca_history fn t` by
    (qpat_assum `!D e. gas_origin_ptr_path _ (s,G,tn) [] _`
       (qspecl_then [`cx_dead (storage_trace_horizon es.storage_trace) ^pcx`,`^pexp`] assume_tac) >>
     `alloca_inv s` by fs[selected_registration_resources_def] >>
     drule_all body_full_path_alloca_history >> simp[]) >>
  `!f inst u. frag_reachable ^pctx fn t f inst u ==> dalloca_fmp_headroom inst u` by
    (qpat_assum `!D e. gas_origin_ptr_path _ (_,FEMPTY,entry_taint) [] (OK t,J,tz)`
       (qspecl_then [`cx_dead (storage_trace_horizon es.storage_trace) ^pcx`,`^pexp`] assume_tac) >>
     `!bb lbl. lookup_block lbl fn.fn_blocks = SOME bb ==> phi_prefix_length bb.bb_instructions = 0`
       by metis_tac[] >>
     rpt strip_tac >> irule grouped_passing_frag_headroom >>
     qpat_assum `gas_origin_ptr_path _ _ [] (OK t,J,tz)` (irule_at Any) >>
     qexistsl_tac [`f`,`bb`] >> rpt conj_tac >> first_assum ACCEPT_TAC) >>
  `cx_tops ^pcx = tops` by
    fs[cx_tops_def, get_module_code_def, initial_evaluation_context_def, source_deployment_rel_def] >>
  `LENGTH ds = LENGTH raw` by simp[subst_consts_exprs_map] >>
  `k <= LENGTH ds` by fs[abi_entries_member] >>
  `LENGTH tx.args <= LENGTH args /\ LENGTH args - LENGTH tx.args <= LENGTH raw /\
   LENGTH raw - (LENGTH args - LENGTH tx.args) = k` by decide_tac >>
  suspend "omitted_suffix"
QED

Resume grouped_default_passing_execution_trace[omitted_suffix]:
  `body_const_cells_agree [(NONE,tops)] ^pcx ^penv es` by
    (`env_context_consistent ^penv ^pcx` by
       fs[expr_sim_inv_def, vyperTypeInvariantsTheory.env_consistent_def] >>
     `!checked_art. check_contract F am.layouts tx.target [(NONE,tops)] = SOME checked_art ==>
                    (^penv).event_fields = checked_art.cta_event_fields` by
       simp[vyperTypeContractTheory.artifact_env_def] >>
     drule_all_then ACCEPT_TAC external_source_body_const_cells_checked) >>
  `gas_outcome_full ((\H. cx_dead H ^pcx),0,^pexp,^pctx,fn,[])
    (cx_tops ^pcx) ^pcx ^pst (eval_exprs ^pcx (DROP k ds)) (es,t,J,tz)
    (\H res ee J' tz' u. ?values. res = INL values /\
      LIST_REL (^pinitialized sb u J' tz') slots (DROP ^ppos tx.args ++ values) /\
      stmt_state_rel H ^pctx fn ^pce0 ^pcx ee u /\ storage_well_formed_on ^pcx ee (FST H) /\
      ghost_inv_at (cx_dead H ^pcx) 0 NONE ^pce0 ^pcx ee J' tz' u /\
      ee.scopes = [FEMPTY] /\ alloca_history fn u /\
      (ctx_has_dalloca ^pctx ==> allocas_below_fmp u) /\
      ~u.vs_halted /\ u.vs_current_bb = sb.cs_current_bb /\ u.vs_inst_idx = LENGTH sb.cs_current_insts)
    (\H res ee gt r. ?ex. res = INR ex /\ expr_exit (INR ex:value list + exception) r /\
      halt_exit H ^pcx ee (INR ex:value list + exception) r /\
      (ctx_has_dalloca ^pctx ==> !u. r = Halt u ==> allocas_below_fmp u))` by
    (SIMP_TAC bool_ss [pairTheory.UNCURRY_DEF, pairTheory.FST, pairTheory.SND] >>
     irule (SIMP_RULE bool_ss [pairTheory.UNCURRY_DEF, pairTheory.FST, pairTheory.SND]
       (Q.INST [`DF` |-> `\H. cx_dead H ^pcx`, `cx` |-> `^pcx`]
         (SPEC_ALL (INST_TYPE [alpha |-> ``:string``, beta |-> ``:operand``]
           grouped_default_omitted_cut)))) >>
     rpt conj_tac >> TRY (first_assum ACCEPT_TAC >> NO_TAC) >>
     TRY (gen_tac >> simp[bodyPtrDefsTheory.dead_lo_ok_def, compileEnvTheory.compile_env_accfupds] >> NO_TAC) >>
     TRY (qexistsl_tac [`G`,`s`,`tn`] >> rpt conj_tac >> first_assum ACCEPT_TAC >> NO_TAC) >>
     qpat_assum `compile_init_kwargs _ (DROP k vars) _ 0 _ last = _` (irule_at Any) >>
     qpat_assum `compile_init_kwargs _ (MAP _ (DROP k vars)) _ 0 _ shlast = _` (irule_at Any) >>
     qpat_assum `LIST_REL _ (DROP k vars) (DROP k slots)` (irule_at Any) >>
     qpat_assum `selected_registration_resources _ _ _ _ last t` (irule_at Any) >>
     qexistsl_tac [`tops`,`shfn`] >> fs[CONJ_ASSOC]) >>
  drule_all (SIMP_RULE bool_ss [] (Q.INST
    [`cx` |-> `^pcx`, `ocomp` |-> `DROP k ds`, `osrc` |-> `DROP k raw`]
    (SPEC_ALL grouped_default_suffix_readings))) >>
  `t.vs_gas_readings = vs.vs_gas_readings` by fs[selected_registration_frame_def] >>
  disch_then (qx_choosel_then [`marks`,`res`,`ee`] (map_every assume_tac o CONJUNCTS o BETA_RULE)) >>
  `ee.storage_trace = es.storage_trace` by
    (qpat_assum `(ee with gas_obs := []) = _`
       (mp_tac o AP_TERM ``evaluation_state_storage_trace``) >> simp[evaluation_state_accfupds]) >>
  `valid_horizon ^pcx ^pst (storage_trace_horizon es.storage_trace) ee.storage_trace` by
    (qpat_assum `ee.storage_trace = es.storage_trace` (pure_rewrite_tac o single) >>
     pure_rewrite_tac[GSYM storage_trace_domain_def] >> first_assum ACCEPT_TAC) >>
  qpat_x_assum `!tail. eval_exprs _ (DROP k raw) _ = _`
    (fn th => qpat_assum `LENGTH raw - (LENGTH args - LENGTH tx.args) = k`
      (fn idx => qpat_assum `t.vs_gas_readings = vs.vs_gas_readings`
        (assume_tac o PURE_REWRITE_RULE [SYM idx] o (fn gas => PURE_REWRITE_RULE [gas] th)))) >>
  Cases_on `res` >- suspend "normal" >>
  suspend "exception"
QED

Resume grouped_default_passing_execution_trace[normal]:
  qmatch_asmsub_rename_tac `INL values : value list + exception` >>
  qpat_x_assum `(?r U V. !H. _) \/ _`
    (qx_choosel_then [`r`,`Gu`,`tu`] assume_tac o
     SIMP_RULE bool_ss [sumTheory.sum_distinct]) >>
  qpat_assum `!H. valid_horizon _ _ H ee.storage_trace ==> gas_origin_ptr_path _ _ _ _ /\ _`
    (qspec_then `storage_trace_horizon es.storage_trace` (drule_then strip_assume_tac))
  >- (rename1 `r = OK u` >> disj2_tac >>
      qexistsl_tac [`slots`,`last`,`t`,`J`,`tz`,`marks`,`values`,`ee`,`u`,`Gu`,`tu`] >>
      `calldata_decode_args vs.vs_call_ctx.cc_calldata (TAKE ^ppos tvs) 0 =
         SOME (TAKE ^ppos tx.args)` by metis_tac[] >>
      rpt conj_tac >> TRY (first_assum ACCEPT_TAC >> NO_TAC) >>
      qx_gen_tac `h` >> disch_tac >>
      qpat_assum `!H. valid_horizon _ _ H ee.storage_trace ==> gas_origin_ptr_path _ _ _ _ /\ _`
        (qspec_then `h` (drule_then mp_tac)) >>
      gvs[exit_result_def, sumTheory.INL_11, pairTheory.UNCURRY_DEF, CONJ_ASSOC]) >>
  gvs[sumTheory.sum_distinct]
QED

Resume grouped_default_passing_execution_trace[exception]:
  qmatch_asmsub_rename_tac `INR ex : value list + exception` >>
  disj1_tac >> qexists_tac `marks` >>
  `!H. valid_horizon ^pcx ^pst H es.storage_trace ==>
       gas_origin_ptr_path (cx_dead H ^pcx,0,^pexp,^pctx,fn,[])
         (^pentry,FEMPTY,entry_taint) [] (OK t,J,tz)` by simp[] >>
  `(?r Gu tu. exit_result r /\
       create_size_exit_ok ^pctx (INR ex : value list + exception) r /\
       !H. valid_horizon ^pcx ^pst H ee.storage_trace ==>
         gas_origin_ptr_path (cx_dead H ^pcx,0,^pexp,^pctx,fn,[])
           (t,J,tz) marks (r,Gu,tu) /\
         expr_exit (INR ex : value list + exception) r /\
         halt_exit H ^pcx (ee with gas_obs := []) (INR ex : value list + exception) r) \/
   (?err H leaf leaf_pg leaf_g leaf_tn finish.
       ex = Error err /\ unspecified_behaviour_exempt tops err /\
       valid_horizon ^pcx ^pst H es.storage_trace /\
       gas_origin_ptr_focus (cx_dead H ^pcx,0,^pexp,^pctx,fn,[])
         (t,J,tz) marks (leaf,leaf_pg,leaf_g,leaf_tn,finish))` suffices_by
    (disch_tac >>
     qsuff_tac `(!tail res am' rqs obs.
         call_external_trace (SOME vs.vs_outcomes)
           (gas_explicit marks vs.vs_gas_readings ++ tail) am tx = (res,am',rqs,obs) ==>
         obs = es.storage_trace) /\
       (?(H : (bool # bytes32 # type_value) list # num list).
         (?r J tz. gas_origin_ptr_path (cx_dead H ^pcx,0,^pexp,^pctx,fn,[])
           (^pentry,FEMPTY,entry_taint) marks (r,J,tz)) \/
         (?leaf pg lg ltn finish. gas_origin_ptr_focus
           (cx_dead H ^pcx,0,^pexp,^pctx,fn,[])
           (^pentry,FEMPTY,entry_taint) marks (leaf,pg,lg,ltn,finish))) /\
       source_unit_execution_correct_with ^psh marks tops ret am tx unit vs /\
       ^passing_readings`
     >- (disch_then (map_every assume_tac o CONJUNCTS) >>
         asm_rewrite_tac[] >> conj_tac
         >- (rpt gen_tac >> strip_tac >>
             qpat_assum `!tail res am' rqs obs. _ ==> obs = es.storage_trace`
               (drule_then SUBST1_TAC) >> fs[initial_state_def]) >>
         disj2_tac >>
         qpat_assum `?H. _ \/ _` (qx_choose_then `H` assume_tac) >>
         qexistsl_tac [`fn`,`H`] >> asm_rewrite_tac[]) >>
     irule (SIMP_RULE bool_ss [] (Q.INST [`cx` |-> `^pcx`]
       (SPEC_ALL grouped_default_exception_result))) >>
     qpat_assum `vyperInterpreter$lookup_function NONE tx.function_name External tops = _`
       (irule_at Any) >>
     qpat_assum `lookup_block "__entry" fn.fn_blocks = SOME bb` (irule_at Any) >>
     qpat_assum `gas_shadow_function fn shfn` (irule_at Any) >>
     qexistsl_tac [`tz`,`t`,`ex`,`ee`,`J`] >>
     rpt conj_tac >> first_assum ACCEPT_TAC) >>
  qpat_x_assum `(?r U V. !H. _) \/ _` (DISJ_CASES_THEN2
    (qx_choosel_then [`r`,`Gu`,`tu`] assume_tac)
    (strip_assume_tac o SIMP_RULE bool_ss [sumTheory.INR_11]))
  >- (disj1_tac >> qexistsl_tac [`r`,`Gu`,`tu`] >>
      qpat_assum `!H. valid_horizon _ _ H ee.storage_trace ==> gas_origin_ptr_path _ _ _ _ /\ _`
        (qspec_then `storage_trace_horizon es.storage_trace` (drule_then strip_assume_tac o
           SIMP_RULE bool_ss [sumTheory.sum_distinct1, sumTheory.INR_11])) >>
      conj_tac >- first_assum ACCEPT_TAC >>
      conj_tac >- first_assum ACCEPT_TAC >>
      qx_gen_tac `h` >> disch_tac >>
      qpat_assum `!H. valid_horizon _ _ H ee.storage_trace ==> gas_origin_ptr_path _ _ _ _ /\ _`
        (qspec_then `h` (drule_then strip_assume_tac o
            SIMP_RULE bool_ss [sumTheory.sum_distinct1, sumTheory.INR_11])) >>
      rpt conj_tac >> first_assum ACCEPT_TAC) >>
  disj2_tac >> metis_tac[]
QED

Finalise grouped_default_passing_execution_trace[local]

Theorem grouped_default_passing_execution = grouped_default_passing_execution_trace
