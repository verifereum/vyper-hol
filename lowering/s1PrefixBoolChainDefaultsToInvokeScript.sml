(* The terminal default stage continues at the caller's actual INVOKE. *)
Theory s1PrefixBoolChainDefaultsToInvoke
Ancestors
  bodyCallLiveness bodyInvCodeProps bodySim bodyInvSplit exprSimHypsDefs gasContext
  s1PrefixBoolChainPushedLockedRun s1PrefixBoolChainDefaultCallback
  s1PrefixIntCallArgsSource s1PrefixOfVV bodyFullIntCall bodyFullIntCallArgsTrace
  bodyFullIntCallReturnSource bodyFullIntCallDefs fragGasFocus ptrSafeRun
  s1PrefixBoolChainSelectedLockedLift s1PrefixFrame
  s1PrefixDefs s1PrefixIntCallStageList vyperInterpreter vyperStorageTrace vyperState
  exprLowering compileEnv vyperStorageFootprint bodyFullIntCallArgs exprBodyPreProps list
  contractInvContextProps compileUnit[qualified] bodyIntCallSeams[qualified] alist

Theorem selected_entry_rest_prefix[local]:
  body_inv tops ctx cenv cx /\
  shadow_body_inv tops ctx shadow_ctx /\
  get_module_code cx NONE = SOME tops /\
  ~MEM (NONE,name) cx.stk /\
  lookup_callable_function cx.in_deploy name tops = SOME (mut,nr,args,dflts,ret,ss) /\
  MEM (FunctionDecl Internal mut nr rr name args dflts ret ss) tops /\
  LENGTH args - LENGTH dflts <= LENGTH es /\ LENGTH es <= LENGTH args /\
  (!s1 vs t1 sd dvs td p rt.
     ~MEM (NONE,name) cx.stk /\
     eval_exprs cx es s1 = (INL vs,t1) /\
     eval_exprs (cx with stk updated_by CONS (NONE,name))
       (DROP (LENGTH dflts - (LENGTH args - LENGTH es)) dflts)
       (sd with scopes := [FEMPTY]) = (INL dvs,td) /\
     bind_arguments (get_tenv cx) args (vs ++ dvs) = SOME p /\
     evaluate_type (get_tenv cx) ret = SOME rt /\
     (nr ==> IS_SOME cx.nonreentrant_slot) /\
     (nr /\ ~is_view_mut mut ==> ~cx.txn.is_static) ==>
     body_stmts_full_ok (cx with stk updated_by CONS (NONE,name))
       (subst_consts_stmts (module_consts_env tops []) ss)) /\
  MEM (NONE,name) (vyperTypeContract$linked_live_functions [(NONE,tops)] []) /\
  LENGTH (remcode cx) <= rank /\
  (!c ys. LENGTH (remcode c) < rank /\
     (!ts. ALOOKUP c.sources c.txn.target = SOME [(NONE,ts)] ==>
        EVERY (\k. MEM k (vyperTypeContract$linked_live_functions [(NONE,ts)] []))
          (vyperTypeCallGraph$int_calls_stmts ys) /\
        stmts_loop_calls_ok [(NONE,ts)] ys) ==>
     body_stmts_prefix_ok c ys) /\
  gas_shadow_context ctx shadow_ctx /\ ctx_inst_ids_distinct ctx /\
  MEM func ctx.ctx_functions /\
  (ctx_has_dalloca ctx ==> allocas_below_fmp s0) /\
  (!fn inst s. frag_reachable ctx func s0 fn inst s ==> dalloca_fmp_headroom inst s) /\
  (!i. active_inst func i t ==> frag_reachable ctx func s0 func i t) /\
  (!H. dead_lo_ok H (DF H) lo cenv cx) /\
  (!H. valid_horizon cx st0 H es1.storage_trace ==>
     intcall_entry_full (DF,lo,d) H tops ctx func cenv cx tenv name es
       sa sm vv s0 es0 G0 tn0 (mut,nr,args,ret,ss,rr) prev penv rtv es1 t G tn) /\
  body_const_cells_agree [(NONE,tops)] cx tenv es1 /\
  (?H. valid_horizon cx st0 H es1.storage_trace) /\
  cenv.ce_func_info (nsid_to_string (NONE,name)) = (result_count,rbs,pvs) ==>
  gas_prefix_full (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
    cx st0 (intcall_rest cx name mut nr ss prev rtv) (es1,t,G,tn)
Proof
  strip_tac >>
  `intcall_entry_full (DF,lo,d) H tops ctx func cenv cx tenv name es
     sa sm vv s0 es0 G0 tn0 (mut,nr,args,ret,ss,rr) prev penv rtv es1 t G tn` by
    (first_assum irule >> first_assum ACCEPT_TAC) >>
  drule_then assume_tac body_inv_contract >>
  drule_then assume_tac contract_inv_singleton_source_modules >>
  drule_then assume_tac contract_inv_immutable_section_layout >>
  `cenv.ce_module = NONE` by (drule body_inv_module_locations >> simp[]) >>
  `intcall_entry_full_mods (DF,lo,d) H [(NONE,tops)] NONE tops ctx func cenv cx tenv name es
     sa sm vv s0 es0 G0 tn0 (mut,nr,args,ret,ss,rr) prev penv rtv es1 t G tn` by
    asm_simp_tac bool_ss [intcall_entry_full_mods_singleton] >>
  `((nr /\ ~is_view_mut mut ==> ~cx.txn.is_static) ==>
      body_stmts_full_ok (cx with stk updated_by CONS (NONE,name))
        (subst_consts_stmts (module_consts_env tops []) ss))` by
    (strip_tac >> drule_all_then ACCEPT_TAC intcall_entry_after_arguments) >>
  `?callee entered. gas_invoke_entry (ctx,func) t callee entered` by
    (qhdtm_assum `intcall_entry_full` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >> simp[intcall_entry_full_def] >> metis_tac[]) >>
  `?bb inst lbl arg_ops argv.
     lookup_block t.vs_current_bb func.fn_blocks = SOME bb /\
     get_instruction bb t.vs_inst_idx = SOME inst /\
     inst.inst_opcode = INVOKE /\ decode_invoke inst = SOME (lbl,arg_ops) /\
     eval_operands arg_ops t = SOME argv` by
    (qhdtm_assum `gas_invoke_entry` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >> simp[gas_invoke_entry_def] >> metis_tac[]) >>
  `!h. ptr_inst_ok (DF h) lo 0 ctx func G tn inst t` by
    (`ptr_inst_ok (DF H) lo 0 ctx func G tn inst t` by
       (drule_all_then ACCEPT_TAC intcall_entry_invoke_ptr) >>
     pop_assum mp_tac >> asm_simp_tac bool_ss [ptr_inst_ok_def]) >>
  irule bool_chain_selected_locked_lift >>
  qhdtm_assum `gas_invoke_entry` (irule_at Any) >>
  qexistsl_tac [`vv`,`tops`,`tn0`,`tenv`,`sm`,`sa`,`s0`,`rr`,`ret`,
    `result_count`,`rbs`,`pvs`,`penv`,`lbl`,`inst`,`es0`,`es`,`dflts`,`d`,`cenv`,
    `bb`,`argv`,`args`,`arg_ops`,`G0`] >>
  rpt conj_tac >> TRY (first_assum ACCEPT_TAC >> NO_TAC) >>
  rpt gen_tac >> strip_tac >>
  Cases_on `compiled = []`
  >- (qhdtm_assum `stmt_frag_full_pre` (strip_assume_tac o REWRITE_RULE [stmt_frag_full_pre_def]) >>
      irule gas_prefix_full_no_outcome >>
      simp[evaluate_storage_trace_frame, Once evaluate_def, return_def]) >>
  `ss <> []` by (strip_tac >> fs[constSubstTheory.subst_consts_stmt_def]) >>
  `LENGTH (remcode pushed) < rank` by
    (`(dflts,ss) <> ([],[])` by simp[] >>
     drule_all bodySimFullMainTheory.callable_remcode_decreases >>
     qpat_assum `pushed = _` SUBST1_TAC >> decide_tac) >>
  drule_then assume_tac body_const_cells_agree_runtime_check >>
  `EVERY (\k. MEM k (vyperTypeContract$linked_live_functions [(NONE,tops)] []))
      (int_calls_stmts compiled)` by
    (qpat_assum `compiled = _` SUBST1_TAC >>
     fs[optionTheory.IS_SOME_EXISTS] >>
     drule_all_then (ACCEPT_TAC o CONJUNCT1) callable_compiled_calls_live) >>
  qpat_x_assum `body_pg = _` SUBST_ALL_TAC >>
  drule_all_then ACCEPT_TAC bool_chain_pushed_locked_run_compiled
QED

Theorem bool_chain_defaults_to_invoke_projected_prefix:
  (* Static caller layout and the return-buffer preparation. *)
  body_inv tops ctx cenv cx /\ shadow_body_inv tops ctx shadow_ctx /\
  expr_body_pre cenv cx tenv (Call ann (IntCall (NONE,name)) es dflt) es0 /\
  expr_sim_inv cenv cx tenv es0 /\
  ~MEM (NONE,name) cx.stk /\ get_module_code cx NONE = SOME tops /\
  lookup_callable_function cx.in_deploy name tops = SOME (mut,nr,args,dflts,ret,ss) /\
  MEM (FunctionDecl Internal mut nr rr name args dflts ret ss) tops /\
  LENGTH args - LENGTH dflts <= LENGTH es /\ LENGTH es <= LENGTH args /\
  evaluate_type (get_tenv cx) ret = SOME rtv /\
  call_evaluation_safe cx ((NONE,name)::int_calls_exprs es) /\
  (!e. P (INR e) ==> expr_vv_res_ok (INR e)) /\
  compile_expr cenv ty (Call ann (IntCall (NONE,name)) es dflt) sa = (vv,sm) /\
  kc vv sm = (out,sb) /\
  fn_has_code sa sb func /\ fn_has_code sa st2 func /\ fn_has_code st3 sm func /\
  cs_extends sa st2 /\ cs_extends st2 st2a /\ cs_extends st2a st3 /\
  cs_extends st3 sm /\ cs_extends sm sb /\
  MEM func ctx.ctx_functions /\ fn_inst_ids_distinct func /\
  local_ptrs_reserved cenv sa /\
  gas_shadow_context ctx shadow_ctx /\ ctx_inst_ids_distinct ctx /\
  (ctx_has_dalloca ctx ==> allocas_below_fmp s0) /\
  (!fn inst s. frag_reachable ctx func s0 fn inst s ==> dalloca_fmp_headroom inst s) /\
  (!H. dead_lo_ok H (DF H) lo cenv cx) /\
  cenv.ce_func_info (nsid_to_string (NONE,name)) = (result_count,rbs,pvs) /\
  cenv.ce_func_info (nsid_to_string (NONE,name)) =
    compute_func_info
      (\n. MAP (FST o SND) (get_struct_fields (make_struct_fields_map tops) n))
      ret (type_mem_bytes (get_struct_fields (make_struct_fields_map tops)) ret)
      (MAP SND args) /\
  cenv.ce_func_param_types (nsid_to_string (NONE,name)) = MAP SND args /\
  pvs = compute_pass_via_stack (MAP SND args) result_count /\
  (!i. i < LENGTH args /\ EL i pvs ==> is_word_type (EL i (MAP SND args))) /\
  EVERY (\t. type_memory_bytes cenv t < 2 ** 64) (MAP SND args) /\
  LENGTH (omitted_defaults cenv (nsid_to_string (NONE,name)) (LENGTH es)) =
    LENGTH args - LENGTH es /\
  ds = omitted_defaults cenv (nsid_to_string (NONE,name)) (LENGTH es) /\
  compile_stage_intcall_args compile_expr cenv es pvs
    (TAKE (LENGTH args) (cenv.ce_func_param_types (nsid_to_string (NONE,name)))) st2 =
      (sup_ops,st2a) /\
  compile_stage_intcall_args compile_expr
    (cenv_without_defaults cenv (nsid_to_string (NONE,name))) ds (DROP (LENGTH es) pvs)
    (DROP (LENGTH es) (TAKE (LENGTH args)
      (cenv.ce_func_param_types (nsid_to_string (NONE,name))))) st2a = (def_ops,st3) /\
  ilabel = internal_fn_label (cenv.ce_func_ids (nsid_to_string (NONE,name)))
    (nsid_to_string (NONE,name)) (cenv.ce_func_param_types (nsid_to_string (NONE,name)))
    cenv.ce_is_ctor /\
  (0 < result_count ==> ?rb results mid ignored.
     compile_alloc_buffer (32 * result_count) sa = (rb,st2) /\
     emit_multi_op INVOKE (Label ilabel::(sup_ops ++ def_ops)) result_count st3 = (results,mid) /\
     store_multi_results rb.buf_operand results 0 mid = (ignored,sm) /\
     vv = LocatedValue (cenv.ce_func_return_type (nsid_to_string (NONE,name))) (base_ptr rb)) /\
  (result_count = 0 /\ 0 < rbs ==> ?rb ignored.
     compile_alloc_buffer rbs sa = (rb,st2) /\
     emit_void INVOKE (Label ilabel::rb.buf_operand::(sup_ops ++ def_ops)) st3 = (ignored,sm) /\
     vv = LocatedValue (cenv.ce_func_return_type (nsid_to_string (NONE,name))) (base_ptr rb)) /\
  (result_count = 0 /\ rbs = 0 ==> ?ignored. st2 = sa /\
     emit_void INVOKE (Label ilabel::(sup_ops ++ def_ops)) st3 = (ignored,sm) /\
     vv = StackValue (cenv.ce_func_return_type (nsid_to_string (NONE,name))) (Lit 0w)) /\
  (!D. gas_origin_ptr_path (D,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
       (s0,G0,tn0) [] (OK entry,Ga,tna)) /\
  (0 < result_count \/ 0 < rbs ==> ?rb q (w:bytes32).
     compile_alloc_buffer (if 0 < result_count then 32 * result_count else rbs) sa = (rb,st2) /\
     rb.buf_operand = Var q /\ rb.buf_size = (if 0 < result_count then 32 * result_count else rbs) /\
     pin = SOME (q,w2n w,(if 0 < result_count then 32 * result_count else rbs))) /\
  (* Both completed replays and the native accumulated staging post. *)
  (!tail. eval_exprs cx es
    (es0 with gas_obs := gas_explicit marks entry.vs_gas_readings ++ tail) =
      (INL svs,ee with gas_obs := tail)) /\
  gas_path ctx func entry (LENGTH marks) (OK t) /\
  expr_sim_inv cenv cx tenv ee /\
  cxd = cx with stk updated_by CONS (NONE,name) /\
  dc = cenv_without_defaults cenv name /\
  supported_pure_exprs tops ds /\
  well_typed_exprs (defaults_env (tenv with current_src := NONE)) ds /\
  well_typed_exprs (tenv with current_src := NONE) ds /\
  body_const_cells_agree [(NONE,tops)] cxd (tenv with current_src := NONE) ee /\
  (!gs scs. eval_exprs cxd ds (ee with <|gas_obs := gs; scopes := scs|>) =
    eval_exprs cxd (DROP (LENGTH dflts - (LENGTH args - LENGTH es)) dflts)
      (ee with <|gas_obs := gs; scopes := scs|>)) /\
  (!tail. eval_exprs cxd ds
    (ee with gas_obs := gas_explicit dm t.vs_gas_readings ++ tail) =
      (INL dvs,ed with gas_obs := tail)) /\
  gas_path ctx func t (LENGTH dm) (OK u) /\
  vals = svs ++ dvs /\ ops = sup_ops ++ def_ops /\
  ptys = TAKE (LENGTH es) (MAP SND args) ++ DROP (LENGTH es) (MAP SND args) /\
  pflags = TAKE (LENGTH es) pvs ++ DROP (LENGTH es) pvs /\
  storage_trace_domain cxd st0 ed.storage_trace /\
  gas_admissible (next vals) P ed /\
  (!H. valid_horizon cxd st0 H ed.storage_trace ==>
    intcall_args_stage_post (DF,lo,d,ctx,func,dc,cxd,tenv with current_src := NONE)
      ([]:expr list,sa,s0,es0,G0,tn0,st3) ([],[],[],ops,vals,ptys,pflags,pin,T,T)
      H (INL [] : value list + exception) ed Gd tnd u) /\
  (* The actual source continuation, after restoring the caller's scope. *)
  after_defaults = (\prev dvs.
    bind
      (bind (lift_option_type (bind_arguments (get_tenv cx) args (svs ++ dvs))
                "IntCall bind_arguments") (\penv.
       bind (lift_option_type (evaluate_type (get_tenv cx) ret)
                "IntCall eval ret") (\rtv.
       ignore_bind (lock_if_nr cx nr (is_view_mut mut))
         (bind (push_function (NONE,name) penv cx) (\cxf.
          bind (finally_unless_halt
            (finally
              (try (ignore_bind (eval_stmts cxf ss) (return NoneV)) handle_function)
              (pop_function prev))
            (unlock_if_nr cx nr (is_view_mut mut))) (\rv.
          bind (lift_option_type (safe_cast rtv rv) "IntCall cast ret")
               (\crv. return (Value crv)))))))) f) /\
  next vals = (\src. after_defaults src.scopes dvs src) /\
  (!v src. SND (f v src) = src) /\
  (!v. storage_trace_frame (f v)) /\
  (!s1 vs t1 sd vsd td p rt.
     ~MEM (NONE,name) cx.stk /\ eval_exprs cx es s1 = (INL vs,t1) /\
     eval_exprs (cx with stk updated_by CONS (NONE,name))
       (DROP (LENGTH dflts - (LENGTH args - LENGTH es)) dflts)
       (sd with scopes := [FEMPTY]) = (INL vsd,td) /\
     bind_arguments (get_tenv cx) args (vs ++ vsd) = SOME p /\
     evaluate_type (get_tenv cx) ret = SOME rt /\
     (nr ==> IS_SOME cx.nonreentrant_slot) /\
     (nr /\ ~is_view_mut mut ==> ~cx.txn.is_static) ==>
     body_stmts_full_ok (cx with stk updated_by CONS (NONE,name))
       (subst_consts_stmts (module_consts_env tops []) ss)) /\
  MEM (NONE,name) (vyperTypeContract$linked_live_functions [(NONE,tops)] []) /\
  LENGTH (remcode cx) <= rank /\
  (!c ys. LENGTH (remcode c) < rank /\
     (!ts. ALOOKUP c.sources c.txn.target = SOME [(NONE,ts)] ==>
        EVERY (\k. MEM k (vyperTypeContract$linked_live_functions [(NONE,ts)] []))
          (vyperTypeCallGraph$int_calls_stmts ys) /\
        stmts_loop_calls_ok [(NONE,ts)] ys) ==>
     body_stmts_prefix_ok c ys) ==>
  gas_prefix_full (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
    cxd st0 (next vals) (ed,u,Gd,tnd)
Proof
  strip_tac >>
  `valid_horizon cxd st0 (storage_trace_horizon ed.storage_trace) ed.storage_trace` by
    fs[storage_trace_domain_def] >>
  qpat_assum `!H. valid_horizon cxd _ H _ ==> intcall_args_stage_post _ _ _ H _ _ _ _ _`
    (drule_then (strip_assume_tac o SIMP_RULE bool_ss
       [intcall_args_stage_post_def,APPEND_NIL,sumTheory.INL_11,UNWIND_THM2])) >>
  `!H. valid_horizon cxd st0 H ed.storage_trace ==>
    stmt_state_rel H ctx func dc cxd ed u /\
    storage_well_formed_on cxd ed (FST H) /\
    ghost_inv_at (DF H) lo d dc cxd ed Gd tnd u` by
    (gen_tac >> disch_tac >>
     qpat_assum `!H. valid_horizon cxd _ H _ ==> intcall_args_stage_post _ _ _ H _ _ _ _ _`
       (drule_then (strip_assume_tac o SIMP_RULE bool_ss
          [intcall_args_stage_post_def,APPEND_NIL,sumTheory.INL_11,UNWIND_THM2])) >>
     rpt conj_tac >> first_assum ACCEPT_TAC) >>
  `gas_admissible ((\dvs src. after_defaults src.scopes dvs src) dvs) P ed` by
    (qpat_assum `gas_admissible (next vals) P ed` mp_tac >>
     qpat_assum `next vals = _` (fn th => simp_tac bool_ss [th])) >>
  suspend "native_entry"
QED

Resume bool_chain_defaults_to_invoke_projected_prefix[native_entry]:
  map_every (fn p => qpat_x_assum p SUBST_ALL_TAC)
    [`ops = _`,`vals = _`,`ptys = _`,`pflags = _`,`dc = _`] >>
  `well_typed_expr tenv (Call ann (IntCall (NONE,name)) es dflt)` by
    (drule expr_body_pre_static_facts >> simp[]) >>
  `cx_tops cx = tops` by drule_then (ACCEPT_TAC o CONJUNCT2) body_inv_main_code >>
  `cx_tops cxd = tops` by fs[cx_tops_def, vyperContextTheory.get_module_code_def] >>
  `expr_sim_inv_mods [(NONE,tops)] cenv cx tenv es0` by
    (qpat_assum `expr_sim_inv cenv cx tenv es0` (fn th =>
       qpat_assum `cx_tops cx = tops` (fn code =>
         ACCEPT_TAC (CONJUNCT1 (REWRITE_RULE [expr_sim_inv_split_def,code] th))))) >>
  `expr_sim_inv_mods [(NONE,tops)] cenv cx tenv ee` by
    (qpat_assum `expr_sim_inv cenv cx tenv ee` (fn th =>
       qpat_assum `cx_tops cx = tops` (fn code =>
         ACCEPT_TAC (CONJUNCT1 (REWRITE_RULE [expr_sim_inv_split_def,code] th))))) >>
  `expr_sim_inv_mods [(NONE,tops)] (cenv_without_defaults cenv name) cxd
      (tenv with current_src := NONE) ed` by
    (qpat_assum `expr_sim_inv (cenv_without_defaults cenv name) cxd _ ed` (fn th =>
       qpat_assum `cx_tops cxd = tops` (fn code =>
         ACCEPT_TAC (CONJUNCT1 (REWRITE_RULE [expr_sim_inv_split_def,code] th))))) >>
  `cenv.ce_module = NONE` by
    fs[body_inv_split_def, cenv_module_pins_split_def, cenv_module_pins_mods_def] >>
  `cenv with ce_module := NONE = cenv` by simp[compile_env_component_equality] >>
  drule_then assume_tac body_inv_contract >>
  drule_then assume_tac contract_inv_singleton_source_modules >>
  drule_then assume_tac contract_inv_immutable_section_layout >>
  `?penv tv.
     ~u.vs_halted /\
     compile_expr cenv ty (Call ann (IntCall (NONE,name)) es dflt) sa = (vv,sm) /\
     kc vv sm = (out,sb) /\
     (!locked. lock_if_nr cx nr (is_view_mut mut) ed = (INL (),locked) ==>
       !tail. after_defaults ed.scopes dvs (ed with gas_obs := tail) =
         bind (intcall_rest cx name mut nr ss ed.scopes tv) f
           ((ed with scopes := [penv]) with gas_obs := tail)) /\
     (!err failed. lock_if_nr cx nr (is_view_mut mut) ed = (INR err,failed) ==>
       !tail. after_defaults ed.scopes dvs (ed with gas_obs := tail) =
         (INR err,failed with <|scopes := ed.scopes; gas_obs := tail|>)) /\
     (!H. valid_horizon cx st0 H ed.storage_trace ==>
       intcall_entry_full (DF,lo,d) H tops ctx func cenv cx tenv name es sa sm
         vv s0 es0 G0 tn0 (mut,nr,args,ret,ss,rr) ed.scopes penv tv
         (ed with scopes := [penv]) u Gd tnd) /\
     body_const_cells_agree [(NONE,tops)] cx tenv (ed with scopes := [penv]) /\
     (!i. active_inst func i u ==> frag_reachable ctx func s0 func i u) /\
     (?H. valid_horizon cx st0 H ed.storage_trace) /\
     gas_admissible (bind (intcall_rest cx name mut nr ss ed.scopes tv) f)
       P (ed with scopes := [penv])` by
    (drule_all_then
       (fn entry =>
         qpat_assum `cenv with ce_module := NONE = cenv` (fn repin =>
           irule (intcall_args_after_defaults_data
             |> Q.INST [`mods` |-> `[(NONE,tops)]`, `exps` |-> `[]`,
                         `caller_src` |-> `NONE`, `caller_tops` |-> `tops`,
                         `src` |-> `NONE`, `vis` |-> `Internal`]
             |> PURE_REWRITE_RULE [APPEND, ALOOKUP_def,
                  compileUnitTheory.make_struct_fields_map_mods_singleton,
                  GSYM bodyIntCallSeamsTheory.intcall_rest_singleton_def, entry, repin])))
       intcall_entry_full_mods_singleton >>
     drule_then assume_tac body_inv_module >>
     rpt conj_tac >> TRY (first_assum ACCEPT_TAC >> NO_TAC) >>
     TRY (qexists_tac `rtv` >> first_assum ACCEPT_TAC >> NO_TAC) >>
     TRY (map_every qexists_tac
       [`Ga`,`PG`,`cxd`,`def_ops`,`dflts`,`dm`,`ds`,`ee`,`entry`,
        `gas_explicit_sites ctx shadow_ctx`,`ilabel`,`marks`,`pin`,`pvs`,`rbs`,`result_count`,
        `st2`,`st2a`,`st3`,`sup_ops`,`t`,`tna`,`ws1`,`svs`]) >>
     rpt conj_tac >> TRY (first_assum ACCEPT_TAC >> NO_TAC) >>
     simp_tac bool_ss [nsid_to_string_def] >>
     TRY (first_assum (ACCEPT_TAC o REWRITE_RULE [nsid_to_string_def]))) >>
  suspend "continuation"
QED

Resume bool_chain_defaults_to_invoke_projected_prefix[continuation]:
  qpat_assum `next (svs ++ dvs) = _` SUBST1_TAC >>
  qpat_assum `cxd = _` SUBST1_TAC >>
  rewrite_tac[intcall_args_prefix_stack] >>
  Cases_on `lock_if_nr cx nr (is_view_mut mut) ed` >>
  rename1 `lock_if_nr cx nr _ ed = (result,locked)` >>
  Cases_on `result`
  >- (rename1 `lock_if_nr _ _ _ _ = (INL unit,locked)` >> Cases_on `unit` >>
      `(gas_prefix_full (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
          cx st0 (\src. after_defaults src.scopes dvs src) (ed,u,Gd,tnd) =
        gas_prefix_full (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
          cx st0 (bind (intcall_rest cx name mut nr ss ed.scopes tv) f)
          (ed with scopes := [penv],u,Gd,tnd))` by
        (irule intcall_args_prefix_source_replay >>
         simp_tac bool_ss [evaluation_state_accfupds] >>
         qpat_assum `!other. (INL (),locked) = (INL (),other) ==> _`
           (qspec_then `locked` mp_tac) >> simp_tac bool_ss [] >>
         first_assum ACCEPT_TAC) >>
      pop_assum SUBST1_TAC >> suspend "reached_entry") >>
  rename1 `lock_if_nr cx nr _ ed = (INR err,failed)` >>
  irule intcall_args_failed_lock_prefix >>
  qpat_assum `lock_if_nr cx nr _ ed = (INR err,failed)` (irule_at Any) >>
  simp_tac bool_ss [evaluation_state_accfupds] >>
  rpt conj_tac >> TRY (first_assum ACCEPT_TAC >> NO_TAC)
  >- (`!prev. storage_trace_frame (after_defaults prev dvs)` by
        (qpat_assum `after_defaults = _` (fn th => simp_tac bool_ss [th]) >>
         gen_tac >> irule intcall_after_defaults_storage_trace_frame >> first_assum ACCEPT_TAC) >>
      simp_tac bool_ss [storage_trace_frame_def,evaluation_state_accfupds] >>
      map_every qx_gen_tac [`src`,`obs`] >>
      qpat_assum `!prev. storage_trace_frame (after_defaults prev dvs)`
        (qspec_then `src.scopes` (qspecl_then [`src`,`obs`] ACCEPT_TAC o
          REWRITE_RULE [storage_trace_frame_def]))) >>
  qpat_assum `!e s. (INR err,failed) = (INR e,s) ==> _`
    (qspecl_then [`err`,`failed`] mp_tac) >> simp_tac bool_ss [] >>
  first_assum ACCEPT_TAC
QED

Resume bool_chain_defaults_to_invoke_projected_prefix[reached_entry]:
  qabbrev_tac `rest_src = intcall_rest cx name mut nr ss ed.scopes tv` >>
  `gas_prefix_full (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
      cx st0 rest_src (ed with scopes := [penv],u,Gd,tnd)` by
    (qunabbrev_tac `rest_src` >> irule selected_entry_rest_prefix >>
     qpat_assum `lookup_callable_function _ _ _ = SOME _` (irule_at Any) >>
     qpat_assum `cenv.ce_func_info _ = (result_count,rbs,pvs)` (irule_at Any) >>
     qexistsl_tac [`vv`,`tn0`,`tenv`,`sm`,`sa`,`s0`,`rr`,`rank`,`penv`,`es0`,`es`,`d`,`H`,`G0`] >>
     simp_tac bool_ss [evaluation_state_accfupds] >>
     rpt conj_tac >> first_assum ACCEPT_TAC) >>
  `!src. SND (bind rest_src f src) = SND (rest_src src)` by
    (gen_tac >> Cases_on `rest_src src` >> rename1 `rest_src src = (res,ee')` >>
     Cases_on `res` >> simp[bind_def]) >>
  drule gas_prefix_full_state_cong >> disch_then (fn th => simp[th])
QED

Finalise bool_chain_defaults_to_invoke_projected_prefix

Theorem bool_chain_defaults_to_invoke_prefix:
  (* Static caller layout and the return-buffer preparation. *)
  body_inv tops ctx cenv cx /\ shadow_body_inv tops ctx shadow_ctx /\
  expr_body_pre cenv cx tenv (Call ann (IntCall (NONE,name)) es dflt) es0 /\
  expr_sim_inv cenv cx tenv es0 /\
  ~MEM (NONE,name) cx.stk /\ get_module_code cx NONE = SOME tops /\
  lookup_callable_function cx.in_deploy name tops = SOME (mut,nr,args,dflts,ret,ss) /\
  MEM (FunctionDecl Internal mut nr rr name args dflts ret ss) tops /\
  LENGTH args - LENGTH dflts <= LENGTH es /\ LENGTH es <= LENGTH args /\
  evaluate_type (get_tenv cx) ret = SOME rtv /\
  call_evaluation_safe cx ((NONE,name)::int_calls_exprs es) /\
  (!e. P (INR e) ==> expr_vv_res_ok (INR e)) /\
  compile_expr cenv ty (Call ann (IntCall (NONE,name)) es dflt) sa = (vv,sm) /\
  kc vv sm = (out,sb) /\
  fn_has_code sa sb func /\ fn_has_code sa st2 func /\ fn_has_code st3 sm func /\
  cs_extends sa st2 /\ cs_extends st2 st2a /\ cs_extends st2a st3 /\
  cs_extends st3 sm /\ cs_extends sm sb /\
  MEM func ctx.ctx_functions /\ fn_inst_ids_distinct func /\
  local_ptrs_reserved cenv sa /\
  gas_shadow_context ctx shadow_ctx /\ ctx_inst_ids_distinct ctx /\
  (ctx_has_dalloca ctx ==> allocas_below_fmp s0) /\
  (!fn inst s. frag_reachable ctx func s0 fn inst s ==> dalloca_fmp_headroom inst s) /\
  (!H. dead_lo_ok H (DF H) lo cenv cx) /\
  cenv.ce_func_info (nsid_to_string (NONE,name)) = (result_count,rbs,pvs) /\
  cenv.ce_func_info (nsid_to_string (NONE,name)) =
    compute_func_info
      (\n. MAP (FST o SND) (get_struct_fields (make_struct_fields_map tops) n))
      ret (type_mem_bytes (get_struct_fields (make_struct_fields_map tops)) ret)
      (MAP SND args) /\
  cenv.ce_func_param_types (nsid_to_string (NONE,name)) = MAP SND args /\
  pvs = compute_pass_via_stack (MAP SND args) result_count /\
  (!i. i < LENGTH args /\ EL i pvs ==> is_word_type (EL i (MAP SND args))) /\
  EVERY (\t. type_memory_bytes cenv t < 2 ** 64) (MAP SND args) /\
  LENGTH (omitted_defaults cenv (nsid_to_string (NONE,name)) (LENGTH es)) =
    LENGTH args - LENGTH es /\
  ds = omitted_defaults cenv (nsid_to_string (NONE,name)) (LENGTH es) /\
  compile_stage_intcall_args compile_expr cenv es pvs
    (TAKE (LENGTH args) (cenv.ce_func_param_types (nsid_to_string (NONE,name)))) st2 =
      (sup_ops,st2a) /\
  compile_stage_intcall_args compile_expr
    (cenv_without_defaults cenv (nsid_to_string (NONE,name))) ds (DROP (LENGTH es) pvs)
    (DROP (LENGTH es) (TAKE (LENGTH args)
      (cenv.ce_func_param_types (nsid_to_string (NONE,name))))) st2a = (def_ops,st3) /\
  ilabel = internal_fn_label (cenv.ce_func_ids (nsid_to_string (NONE,name)))
    (nsid_to_string (NONE,name)) (cenv.ce_func_param_types (nsid_to_string (NONE,name)))
    cenv.ce_is_ctor /\
  (0 < result_count ==> ?rb results mid ignored.
     compile_alloc_buffer (32 * result_count) sa = (rb,st2) /\
     emit_multi_op INVOKE (Label ilabel::(sup_ops ++ def_ops)) result_count st3 = (results,mid) /\
     store_multi_results rb.buf_operand results 0 mid = (ignored,sm) /\
     vv = LocatedValue (cenv.ce_func_return_type (nsid_to_string (NONE,name))) (base_ptr rb)) /\
  (result_count = 0 /\ 0 < rbs ==> ?rb ignored.
     compile_alloc_buffer rbs sa = (rb,st2) /\
     emit_void INVOKE (Label ilabel::rb.buf_operand::(sup_ops ++ def_ops)) st3 = (ignored,sm) /\
     vv = LocatedValue (cenv.ce_func_return_type (nsid_to_string (NONE,name))) (base_ptr rb)) /\
  (result_count = 0 /\ rbs = 0 ==> ?ignored. st2 = sa /\
     emit_void INVOKE (Label ilabel::(sup_ops ++ def_ops)) st3 = (ignored,sm) /\
     vv = StackValue (cenv.ce_func_return_type (nsid_to_string (NONE,name))) (Lit 0w)) /\
  (!D. gas_origin_ptr_path (D,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
       (s0,G0,tn0) [] (OK entry,Ga,tna)) /\
  (0 < result_count \/ 0 < rbs ==> ?rb q (w:bytes32).
     compile_alloc_buffer (if 0 < result_count then 32 * result_count else rbs) sa = (rb,st2) /\
     rb.buf_operand = Var q /\ rb.buf_size = (if 0 < result_count then 32 * result_count else rbs) /\
     pin = SOME (q,w2n w,(if 0 < result_count then 32 * result_count else rbs))) /\
  (* Both completed replays and the native accumulated staging post. *)
  (!tail. eval_exprs cx es
    (es0 with gas_obs := gas_explicit marks entry.vs_gas_readings ++ tail) =
      (INL svs,ee with gas_obs := tail)) /\
  gas_path ctx func entry (LENGTH marks) (OK t) /\
  expr_sim_inv cenv cx tenv ee /\
  cxd = cx with stk updated_by CONS (NONE,name) /\
  dc = cenv_without_defaults cenv name /\
  supported_pure_exprs tops ds /\
  well_typed_exprs (defaults_env (tenv with current_src := NONE)) ds /\
  well_typed_exprs (tenv with current_src := NONE) ds /\
  body_const_cells_agree [(NONE,tops)] cxd (tenv with current_src := NONE) ee /\
  (!gs scs. eval_exprs cxd ds (ee with <|gas_obs := gs; scopes := scs|>) =
    eval_exprs cxd (DROP (LENGTH dflts - (LENGTH args - LENGTH es)) dflts)
      (ee with <|gas_obs := gs; scopes := scs|>)) /\
  (!tail. eval_exprs cxd ds
    (ee with gas_obs := gas_explicit dm t.vs_gas_readings ++ tail) =
      (INL dvs,ed with gas_obs := tail)) /\
  gas_path ctx func t (LENGTH dm) (OK u) /\
  vals = svs ++ dvs /\ ops = sup_ops ++ def_ops /\
  ptys = TAKE (LENGTH es) (MAP SND args) ++ DROP (LENGTH es) (MAP SND args) /\
  pflags = TAKE (LENGTH es) pvs ++ DROP (LENGTH es) pvs /\
  bool_chain_default_ready (DF,lo,d,ctx,shadow_ctx,func,shadow_func,tops,dc,cxd,
       tenv with current_src := NONE,st0)
    (sa,s0,es0,G0,tn0,st3,sh_st3,pin,T,T) next P []
    (si,shi,[],[],ops,vals,ptys,pflags) (ed,u,Gd,tnd) /\
  (* The actual source continuation, after restoring the caller's scope. *)
  after_defaults = (\prev dvs.
    bind
      (bind (lift_option_type (bind_arguments (get_tenv cx) args (svs ++ dvs))
                "IntCall bind_arguments") (\penv.
       bind (lift_option_type (evaluate_type (get_tenv cx) ret)
                "IntCall eval ret") (\rtv.
       ignore_bind (lock_if_nr cx nr (is_view_mut mut))
         (bind (push_function (NONE,name) penv cx) (\cxf.
          bind (finally_unless_halt
            (finally
              (try (ignore_bind (eval_stmts cxf ss) (return NoneV)) handle_function)
              (pop_function prev))
            (unlock_if_nr cx nr (is_view_mut mut))) (\rv.
          bind (lift_option_type (safe_cast rtv rv) "IntCall cast ret")
               (\crv. return (Value crv)))))))) f) /\
  next vals = (\src. after_defaults src.scopes dvs src) /\
  (!v src. SND (f v src) = src) /\
  (!v. storage_trace_frame (f v)) /\
  (!s1 vs t1 sd vsd td p rt.
     ~MEM (NONE,name) cx.stk /\ eval_exprs cx es s1 = (INL vs,t1) /\
     eval_exprs (cx with stk updated_by CONS (NONE,name))
       (DROP (LENGTH dflts - (LENGTH args - LENGTH es)) dflts)
       (sd with scopes := [FEMPTY]) = (INL vsd,td) /\
     bind_arguments (get_tenv cx) args (vs ++ vsd) = SOME p /\
     evaluate_type (get_tenv cx) ret = SOME rt /\
     (nr ==> IS_SOME cx.nonreentrant_slot) /\
     (nr /\ ~is_view_mut mut ==> ~cx.txn.is_static) ==>
     body_stmts_full_ok (cx with stk updated_by CONS (NONE,name))
       (subst_consts_stmts (module_consts_env tops []) ss)) /\
  MEM (NONE,name) (vyperTypeContract$linked_live_functions [(NONE,tops)] []) /\
  LENGTH (remcode cx) <= rank /\
  (!c ys. LENGTH (remcode c) < rank /\
     (!ts. ALOOKUP c.sources c.txn.target = SOME [(NONE,ts)] ==>
        EVERY (\k. MEM k (vyperTypeContract$linked_live_functions [(NONE,ts)] []))
          (vyperTypeCallGraph$int_calls_stmts ys) /\
        stmts_loop_calls_ok [(NONE,ts)] ys) ==>
     body_stmts_prefix_ok c ys) ==>
  gas_prefix_full (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
    cxd st0 (next vals) (ed,u,Gd,tnd)
Proof
  strip_tac >>
  qhdtm_assum `bool_chain_default_ready`
    (strip_assume_tac o SIMP_RULE bool_ss
      [bool_chain_default_ready_def,MAP,compile_stage_intcall_args_def,
       comp_return_def,pairTheory.PAIR_EQ,intcall_stage_nil_source,
       bind_return,APPEND_NIL]) >>
  qpat_x_assum `si = st3` SUBST_ALL_TAC >>
  match_mp_tac (SPEC_ALL bool_chain_defaults_to_invoke_projected_prefix) >>
  rpt conj_tac >> first_assum ACCEPT_TAC
QED
