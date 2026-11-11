(* Actual-entry root frame and producer resources, without exposing windows
   or instruction distinctness plumbing to the packaging consumer. *)
Theory bodyIntCallPackageRootReady
Ancestors
  bodyIntCallPackageRoot bodyIntCallPackageProducerEntry bodyIntCallInvokedCode
  venomExecProps venomWf list

Theorem intcall_entry_root_ready:
  body_inv tops ctx cenv cx /\ cenv_module_pins tops cenv /\
  MEM (FunctionDecl Internal mut F rr name args [] ret ss) tops /\
  lookup_callable_function cx.in_deploy name tops = SOME (mut,F,args,[],ret,ss) /\
  call_stack_follows (call_edge_rel E) ((NONE,name)::cx.stk) /\
  irreflexive (TC (call_edge_rel E)) /\
  functions_follow_call_graph E (cx with stk updated_by CONS (NONE,name)) /\
  intcall_entry tops ctx func cenv cx tenv name es sa sb vv s0 es0
    (mut,args,ret,ss,rr) prev penv rtv es1 t /\
  lookup_block t.vs_current_bb func.fn_blocks = SOME bb /\
  get_instruction bb t.vs_inst_idx = SOME inst /\
  decode_invoke inst = SOME (lbl,arg_ops) /\ eval_operands arg_ops t = SOME argv /\
  lookup_function lbl ctx.ctx_functions = SOME callee /\
  setup_callee callee argv t = SOME entered /\
  cenv.ce_func_info (nsid_to_string (NONE,name)) = (nret,rbs,pvs) /\
  set_internal_package_target cenv.ce_target
    (package_internal_fn tops use_trans (nkeys:string->num) cenv.ce_is_ctor ilen
      (mut,F,rr,name,args,([]:expr list),ret,ss)) =
    (label,ce,params,has_rb,is_nr,key,trans,view,ctor,ilen',ss',rt) /\
  compile_internal_function_entry ce params has_rb ctor ilen' rt entry =
    ((ce2,rpc,imm),body_start) /\
  fn_has_code entry body_start callee /\ ctx_inst_ids_distinct ctx /\
  run_inst_seq (emitted_insts entry body_start) entered = OK u ==>
  ?P staged fp env env_after bindings.
    fn_inst_ids_distinct callee /\
    (!a k. P a k <=> a + k <= t.vs_alloca_next /\
      !aid off asz. FLOOKUP t.vs_allocas aid = SOME (off,asz) /\
        sa.cs_next_id <= aid /\ aid < sb.cs_next_id ==> regions_disjoint a k off asz) /\
    (!b z. staged b z <=> ?i po.
      i < LENGTH params /\ ~SND (EL i params) /\
      FLOOKUP ce.ce_vars (FST (EL i params)) = SOME (MemLoc po z) /\
      b = w2n (EL ((if has_rb then 1 else 0) + i) argv)) /\
    intcall_frame_ok fp /\
    fp.jc_tops = tops /\ fp.jc_ctx = ctx /\ fp.jc_func = callee /\
    fp.jc_cx = (cx with stk updated_by CONS (NONE,name)) /\
    fp.jc_owner = (NONE,name) /\ fp.jc_ancestors = cx.stk /\ fp.jc_edges = E /\
    fp.jc_ret_ty = ret /\ fp.jc_ret_tv = rtv /\
    fp.jc_lo = t.vs_alloca_next /\ fp.jc_morig = t /\ fp.jc_oorig = u /\
    fp.jc_root_ce = (ce2 with <|ce_imm_alloca := imm; ce_alloca_locals := T|>) /\
    fp.jc_rpc = rpc /\ fp.jc_pc = entered.vs_return_pc_token /\
    fp.jc_rb = (if has_rb then SOME (HD argv,type_memory_size rtv) else NONE) /\
    fp.jc_prot = P /\ fp.jc_staged = staged /\
    fp.jc_reserved = (\op. op = rpc \/
      (?sz. (ce2 with <|ce_imm_alloca := imm; ce_alloca_locals := T|>).
        ce_return_buf = SOME (PtrVar op sz)) \/
      (ce2 with <|ce_imm_alloca := imm; ce_alloca_locals := T|>).ce_imm_alloca = SOME op) /\
    (!op x. fp.jc_reserved op /\ op = Var x ==> not_fresh_at body_start x) /\
    body_inv tops ctx fp.jc_root_ce fp.jc_cx /\
    supported_stmts tops bindings ss /\
    (!target. supported_stmts_expr_exists (expr_abi_decode_target_root target) ss ==>
      occurs_abi_decode_target target tops) /\
    type_stmts env ret ss = SOME env_after /\
    IS_SOME (type_stmts (env with bare_global_assignable := FEMPTY) ret ss) /\
    EVERY (stmt_exprs_ok fp.jc_root_ce) ss /\
    calls_follow_call_graph E (NONE,name) (int_calls_stmts ss) /\
    gas_admissible (eval_stmts fp.jc_cx ss) (stmt_res_ok NoLoop) es1 /\
    (ret = NoneT \/ stmts_no_fallthrough ss) /\
    intcall_joint_res fp fp.jc_root_ce env es1 body_start
      (u with vs_inst_idx := LENGTH body_start.cs_current_insts)
Proof
  strip_tac >>
  `fn_inst_ids_distinct callee` by
    (drule lookup_function_MEM >> simp[MEM_SPLIT] >> strip_tac >>
     gvs[venomWfTheory.ctx_inst_ids_distinct_def,
         venomWfTheory.fn_inst_ids_distinct_def,
         MAP_APPEND, FLAT_APPEND, ALL_DISTINCT_APPEND]) >>
  qabbrev_tac `P = \a k. a + k <= t.vs_alloca_next /\
    !aid off asz. FLOOKUP t.vs_allocas aid = SOME (off,asz) /\
      sa.cs_next_id <= aid /\ aid < sb.cs_next_id ==>
      regions_disjoint a k off asz` >>
  qabbrev_tac `staged = \b z. ?i po.
    i < LENGTH params /\ ~SND (EL i params) /\
    FLOOKUP ce.ce_vars (FST (EL i params)) = SOME (MemLoc po z) /\
    b = w2n (EL ((if has_rb then 1 else 0) + i) argv)` >>
  `!a k. P a k <=> a + k <= t.vs_alloca_next /\
    !aid off asz. FLOOKUP t.vs_allocas aid = SOME (off,asz) /\
      sa.cs_next_id <= aid /\ aid < sb.cs_next_id ==>
      regions_disjoint a k off asz` by simp[Abbr `P`] >>
  `!b z. staged b z <=> ?i po.
    i < LENGTH params /\ ~SND (EL i params) /\
    FLOOKUP ce.ce_vars (FST (EL i params)) = SOME (MemLoc po z) /\
    b = w2n (EL ((if has_rb then 1 else 0) + i) argv)` by simp[Abbr `staged`] >>
  drule_all intcall_entry_root_frame >> strip_tac >>
  drule_all intcall_entry_producer_resources >>
  disch_then (qx_choose_then `env` (qx_choose_then `env_after`
    (qx_choose_then `bindings` (fn th => map_every assume_tac (CONJUNCTS th))))) >>
  qexistsl [`P`,`staged`,`fp`,`env`,`env_after`,`bindings`] >>
  asm_rewrite_tac[]
QED
