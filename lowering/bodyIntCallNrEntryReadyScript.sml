(* The actual guarded entry: transport of runtime resources through its lock. *)
Theory bodyIntCallNrEntryReady
Ancestors
  bodyIntCallNrEntrySemantic bodyIntCallNrEntryResources bodyIntCallNrLockResources
  bodyIntCallNonreentrantLock nonreentrantEntry fragExecMem moduleLoweringProps
  exprLoweringProps loweringStateRelDefs venomState finite_map words
  transientLockFrameProps transientLockProps nonreentrantEquiv vyperInterpreter
  vyperState fragGasSeq fragGasSeqAbort venomInst emitHelper
  supportedProgram bodySim bodyIntCallActualEntrySemantic compileVyper
  bodyIntCallPackageBounds bodyIntCallJointInputs bodyMemoryDefs vyperContext

Theorem internal_entry_lock_runtime_resources:
  fmp_room ctx func s /\ immutable_base_zero ce s /\
  vars_pc_only (if view then s else tstore (n2w key) 1w s) u /\
  (!x. not_fresh_at st x ==> lookup_var x u = lookup_var x s) /\
  (!op. ce.ce_imm_alloca = SOME op ==> ?x. op = Var x /\ not_fresh_at st x) ==>
  fmp_room ctx func u /\ immutable_base_zero ce u
Proof
  strip_tac >>
  `u.vs_allocas = s.vs_allocas /\ u.vs_alloca_next = s.vs_alloca_next /\
   u.vs_fmp = s.vs_fmp /\ u.vs_labels = s.vs_labels` by
    (fs[vars_pc_only_def] >> Cases_on `view` >>
     gvs[tstore_def, venom_state_component_equality]) >>
  conj_tac
  >- (fs[fmp_room_def, pending_alloca_size_def] >> metis_tac[]) >>
  irule immutable_base_zero_frame >> qexists_tac `s` >> simp[] >> rpt strip_tac >>
  first_x_assum (qspec_then `Var x` mp_tac) >> simp[] >>
  strip_tac >> gvs[]
QED

Theorem internal_entry_lock_success_resources:
  compile_nonreentrant_lock key T view st = ((),st') /\
  cx.nonreentrant_slot = SOME key /\ nonreentrant_slot_separated cx /\
  stmt_state_rel ctx func ce cx es s /\ fresh_vars_wrt st s /\
  tload (n2w key) s <> 1w /\
  (!op. ce.ce_imm_alloca = SOME op ==> ?x. op = Var x /\ not_fresh_at st x) ==>
  ?locked u.
    run_inst_seq (emitted_insts st st') s = OK u /\
    lock_if_nr cx T view es = (INL (),locked) /\
    state_rel func ce cx locked u /\ fresh_vars_wrt st' u /\
    u.vs_memory = s.vs_memory /\ u.vs_allocas = s.vs_allocas /\
    u.vs_alloca_next = s.vs_alloca_next /\
    fmp_room ctx func u /\ immutable_base_zero ce u /\
    (!op w. eval_operand op s = SOME w ==> eval_operand op u = SOME w)
Proof
  strip_tac >>
  `state_rel func ce cx es s /\ local_ptrs_rel func ce es.scopes s /\
   ~s.vs_call_ctx.cc_static` by
    fs[stmt_state_rel_def, state_rel_def] >>
  drule_all compile_nonreentrant_lock_source_correct >> strip_tac >>
  drule_all compile_nonreentrant_lock_transient_frame >> strip_tac >>
  gvs[] >> rename1 `state_rel func ce cx locked u` >>
  drule compile_nonreentrant_lock_transient_code >> strip_tac >>
  `vars_pc_only (if view then s else tstore (n2w key) 1w s) u` by
    (gvs[transient_lock_code_execution] >> Cases_on `view` >>
     gvs[vars_pc_only_def, transient_lock_checked_state_def,
         update_var_def, tstore_def]) >>
  `!x. not_fresh_at st x ==> lookup_var x u = lookup_var x s` by
    (gvs[transient_lock_code_execution] >> Cases_on `view` >>
     gvs[transient_lock_checked_state_def, lookup_var_def, update_var_def,
         tstore_def, FLOOKUP_UPDATE] >>
     rpt strip_tac >> gvs[not_fresh_at_def]) >>
  `fmp_room ctx func s /\ immutable_base_zero ce s /\ ~cx.txn.is_static` by
    fs[stmt_state_rel_def, state_rel_def] >>
  drule_all internal_entry_lock_runtime_resources >> strip_tac >>
  qexists_tac `locked` >> simp[] >>
  fs[lock_if_nr_def, ignore_bind_def, bind_def, check_not_static_def,
     check_def, assert_def, return_def, raise_def] >>
  Cases_on `view` >>
  gvs[assert_def, return_def, vars_pc_only_def, tstore_def,
      venom_state_component_equality]
QED

Theorem internal_entry_lock_failure_resources:
  compile_nonreentrant_lock key T view st = ((),st') /\
  cx.nonreentrant_slot = SOME key /\ nonreentrant_slot_separated cx /\
  state_rel func ce cx es s /\ tload (n2w key) s = 1w ==>
  lock_if_nr cx T view es =
    (INR (vyperState$Error (RuntimeError "nonreentrant lock")),es) /\
  ?u. run_inst_seq (emitted_insts st st') s = Abort Revert_abort u /\
    u.vs_returndata = [] /\ u.vs_memory = s.vs_memory /\
    u.vs_allocas = s.vs_allocas /\ u.vs_alloca_next = s.vs_alloca_next
Proof
  strip_tac >> drule_all compile_nonreentrant_lock_source_revert >> strip_tac >>
  drule compile_nonreentrant_lock_transient_code >> strip_tac >>
  conj_tac
  >- (`~cx.txn.is_static` by fs[state_rel_def] >>
      fs[lock_if_nr_def, ignore_bind_def, bind_def]) >>
  gvs[transient_lock_code_execution] >>
  simp[revert_state_def, set_returndata_def, transient_lock_checked_state_def,
       update_var_def]
QED

Theorem internal_entry_lock_success_path:
  compile_nonreentrant_lock key T view st = ((),st') /\
  ~s.vs_halted /\ lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
  isPREFIX (emitted_insts st st') (DROP s.vs_inst_idx bb.bb_instructions) /\
  run_inst_seq (emitted_insts st st') s = OK u ==>
  gas_path ctx func s 0
    (OK (u with vs_inst_idx := s.vs_inst_idx + LENGTH (emitted_insts st st')))
Proof
  strip_tac >> drule compile_nonreentrant_lock_transient_code >> strip_tac >>
  `EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
     (emitted_insts st st')` by
    (Cases_on `view` >> simp[transient_lock_code_def, mk_inst_def, is_terminator_def]) >>
  drule_all tuple_run_inst_seq_gas_path >>
  simp[transient_lock_code_def, mk_inst_def] >>
  Cases_on `view` >> simp[transient_lock_code_def, mk_inst_def]
QED

Theorem internal_entry_lock_failure_path:
  compile_nonreentrant_lock key T view st = ((),st') /\
  ~s.vs_halted /\ lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
  isPREFIX (emitted_insts st st') (DROP s.vs_inst_idx bb.bb_instructions) /\
  run_inst_seq (emitted_insts st st') s = Abort a u ==>
  ?j. gas_marked_path F ctx func s 0 (Abort a (u with vs_inst_idx := j))
Proof
  strip_tac >> drule compile_nonreentrant_lock_transient_code >> strip_tac >>
  irule run_inst_seq_abort_zero_path >>
  simp[] >> qexists_tac `emitted_insts st st'` >> simp[] >>
  Cases_on `view` >> simp[transient_lock_code_def, mk_inst_def, is_terminator_def]
QED

Theorem internal_entry_root_joint_after_lock_advance:
  supported_program tops /\ cxf.stk = owner::ancestors /\
  call_stack_follows (call_edge_rel edges) cxf.stk /\
  irreflexive (TC (call_edge_rel edges)) /\
  functions_follow_call_graph edges cxf /\
  evaluate_type (get_tenv cxf) ret = SOME rtv /\
  root.ce_return_pc = SOME (PtrVar rpc 0) /\ cenv_module_pins tops root /\
  root.ce_returns_count = returns_stack_count
    (\name. MAP (FST o SND) (get_struct_fields root.ce_struct_fields name)) ret /\
  (has_rb <=> root.ce_returns_count = 0 /\ ret <> NoneT) /\
  (?x. rpc = Var x /\ not_fresh_at pre x /\ lookup_var x v = SOME pc) /\
  (!op sz. root.ce_return_buf = SOME (PtrVar op sz) ==>
    ?x w. op = Var x /\ not_fresh_at pre x /\ lookup_var x v = SOME w) /\
  (!op. root.ce_imm_alloca = SOME op ==>
    ?x w. op = Var x /\ not_fresh_at pre x /\ lookup_var x v = SOME w) /\
  (!a k. P a k ==> a + k <= lo) /\
  (!b z. staged b z ==> !a k. P a k ==> regions_disjoint a k b z) /\
  (has_rb ==> cap = type_memory_size rtv /\ w2n bw + cap <= lo /\
    (!b z. staged b z ==> regions_disjoint (w2n bw) cap b z) /\
    (!a k. P a k ==> regions_disjoint a k (w2n bw) cap)) /\
  stmt_state_rel ctx callee root cxf es v /\ expr_sim_inv root cxf env es /\
  ce_locals_declared root env /\ locals_alloc_ok root env /\
  local_ptrs_reserved root pre /\ allocas_above lo v /\
  (!a k. P a k ==> mem_bytes_at a k v.vs_memory = mem_bytes_at a k origin.vs_memory) /\
  (!n p k. local_region root es.scopes v n p k ==>
    lo <= p \/ ?b z. staged b z /\ b <= p /\ p + k <= b + z) /\
  return_buf_frame (if has_rb then SOME (bw,cap) else NONE) root pre v /\
  (has_rb /\ root.ce_is_ctor ==> !nm tv iv io.
    FLOOKUP root.ce_module_vars (root.ce_module,nm) = SOME (ImmutableLoc io) /\
    FLOOKUP (case ALOOKUP es.immutables cxf.txn.target of NONE => FEMPTY
      | SOME imms => get_source_immutables root.ce_module imms) nm = SOME (tv,iv) ==>
    regions_disjoint io (type_memory_size tv) (w2n bw) cap) /\
  lock_if_nr cxf nr view es = (INL (),locked) /\
  state_rel callee root cxf locked u /\ fresh_vars_wrt post u /\
  u.vs_memory = v.vs_memory /\ u.vs_allocas = v.vs_allocas /\
  u.vs_alloca_next = v.vs_alloca_next /\
  (!op w. eval_operand op v = SOME w ==> eval_operand op u = SOME w) /\
  fmp_room ctx callee u /\ immutable_base_zero root u /\
  pre.cs_next_var <= post.cs_next_var ==>
  ?fp. intcall_frame_ok fp /\
    fp.jc_tops = tops /\ fp.jc_ctx = ctx /\ fp.jc_func = callee /\
    fp.jc_cx = cxf /\ fp.jc_owner = owner /\ fp.jc_ancestors = ancestors /\
    fp.jc_edges = edges /\ fp.jc_ret_ty = ret /\ fp.jc_ret_tv = rtv /\
    fp.jc_lo = lo /\ fp.jc_morig = origin /\ fp.jc_oorig = u /\
    fp.jc_root_ce = root /\ fp.jc_rpc = rpc /\ fp.jc_pc = pc /\
    fp.jc_rb = (if has_rb then SOME (bw,cap) else NONE) /\
    fp.jc_prot = P /\ fp.jc_staged = staged /\
    fp.jc_reserved = (\op. op = rpc \/
      (?sz. root.ce_return_buf = SOME (PtrVar op sz)) \/
      root.ce_imm_alloca = SOME op) /\
    intcall_joint_res fp root env locked post
      (u with vs_inst_idx := LENGTH post.cs_current_insts)
Proof
  strip_tac >>
  `!x. not_fresh_at pre x ==> not_fresh_at post x` by
    (simp[not_fresh_at_def] >> metis_tac[arithmeticTheory.LE_TRANS]) >>
  `local_ptrs_reserved root post` by
    metis_tac[local_ptrs_reserved_next_var] >>
  `return_buf_frame (if has_rb then SOME (bw,cap) else NONE) root post v` by
    (irule return_buf_frame_frame >> qexistsl [`root`, `v`, `pre`] >> simp[]) >>
  irule internal_entry_root_joint_after_lock >> simp[] >>
  qexistsl [`es`, `nr`, `v`, `view`] >> simp[arithmeticTheory.ADD_COMM] >>
  rpt conj_tac
  >- gvs[]
  >- (rpt strip_tac >>
      qpat_x_assum `!op sz. _` drule >> strip_tac >> gvs[])
  >- (rpt strip_tac >>
      qpat_x_assum `!op. root.ce_imm_alloca = SOME op ==> _` drule >>
      strip_tac >> gvs[])
  >> gvs[]
QED

Theorem intcall_entry_root_ready_nr:
  body_inv tops ctx cenv cx /\ cenv_module_pins tops cenv /\
  MEM (FunctionDecl Internal mut T rr name args dflts ret ss) tops /\
  lookup_callable_function cx.in_deploy name tops = SOME (mut,T,args,dflts,ret,ss) /\
  call_stack_follows (call_edge_rel E) ((NONE,name)::cx.stk) /\
  irreflexive (TC (call_edge_rel E)) /\
  functions_follow_call_graph E (cx with stk updated_by CONS (NONE,name)) /\
  intcall_entry tops ctx func cenv cx tenv name es sa sb vv s0 es0
    (mut,T,args,ret,ss,rr) prev penv rtv es1 t /\
  lookup_block t.vs_current_bb func.fn_blocks = SOME bb /\
  get_instruction bb t.vs_inst_idx = SOME inst /\
  decode_invoke inst = SOME (lbl,arg_ops) /\ eval_operands arg_ops t = SOME argv /\
  lookup_function lbl ctx.ctx_functions = SOME callee /\
  setup_callee callee argv t = SOME entered /\
  cenv.ce_func_info (nsid_to_string (NONE,name)) = (nret,rbs,pvs) /\
  set_internal_package_target cenv.ce_target
    (package_internal_fn tops use_trans (nkeys:string->num) cenv.ce_is_ctor ilen
      (mut,T,rr,name,args,([]:expr list),ret,ss)) =
    (label,ce,params,has_rb,is_nr,key,trans,view,ctor,ilen',ss',rt) /\
  compile_internal_function_entry ce params has_rb ctor ilen' rt entry =
    ((ce2,rpc,imm),prelock) /\
  compile_nonreentrant_lock key T (is_view_mut mut) prelock = ((),body_start) /\
  cx.nonreentrant_slot = SOME key /\ nonreentrant_slot_separated cx /\
  entry.cs_current_insts = [] /\
  entry.cs_current_bb = (HD callee.fn_blocks).bb_label /\
  fn_has_code entry prelock callee /\ fn_inst_ids_distinct callee /\
  run_inst_seq (emitted_insts entry prelock) entered = OK v /\
  tload (n2w key) v <> 1w /\ fresh_vars_wrt prelock v /\
  (!a k. P a k <=> a + k <= t.vs_alloca_next /\
    !aid off asz. FLOOKUP t.vs_allocas aid = SOME (off,asz) /\
      sa.cs_next_id <= aid /\ aid < sb.cs_next_id ==> regions_disjoint a k off asz) /\
  (!b z. staged b z <=> ?i po.
    i < LENGTH params /\ ~SND (EL i params) /\
    FLOOKUP ce.ce_vars (FST (EL i params)) = SOME (MemLoc po z) /\
    b = w2n (EL ((if has_rb then 1 else 0) + i) argv)) ==>
  ?locked u fp env env_after bindings.
    run_inst_seq (emitted_insts prelock body_start) v = OK u /\
    lock_if_nr cx T (is_view_mut mut) es1 = (INL (),locked) /\
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
    body_inv tops ctx fp.jc_root_ce fp.jc_cx /\
    supported_stmts tops bindings ss /\
    (!target. supported_stmts_expr_exists (expr_abi_decode_target_root target) ss ==>
      occurs_abi_decode_target target tops) /\
    type_stmts env ret ss = SOME env_after /\
    IS_SOME (type_stmts (env with bare_global_assignable := FEMPTY) ret ss) /\
    stmts_exprs_ok fp.jc_root_ce ss /\
    calls_follow_call_graph E (NONE,name) (int_calls_stmts ss) /\
    gas_admissible (eval_stmts fp.jc_cx ss) (stmt_res_ok NoLoop) locked /\
    (ret = NoneT \/ stmts_no_fallthrough ss) /\
    intcall_joint_res fp fp.jc_root_ce env locked body_start
      (u with vs_inst_idx := LENGTH body_start.cs_current_insts)
Proof
  strip_tac >> drule_all intcall_entry_producer_semantics_nr >>
  disch_then (qx_choose_then `env` (qx_choose_then `env_after`
    (qx_choose_then `bindings` (fn th => map_every assume_tac (CONJUNCTS th))))) >>
  `supported_function_body tops Internal args ss` by
    (drule_at (Pat `MEM (FunctionDecl _ _ _ _ _ _ _ _ _) _`)
       supported_program_function >> fs[body_inv_def]) >>
  drule_all packaged_internal_entry_locals_declared >> strip_tac >>
  drule_all body_inv_internal_allocs_ok >> strip_tac >>
  `set_internal_package_target cenv.ce_target
     (package_internal_fn tops use_trans nkeys cenv.ce_is_ctor ilen
       (mut,T,rr,name,args,dflts,ret,ss)) =
   (label,ce,params,has_rb,is_nr,key,trans,view,ctor,ilen',ss',rt)` by
    (qpat_assum `set_internal_package_target _ _ = _` (SUBST1_TAC o SYM) >>
     rewrite_tac[package_internal_fn_def]) >>
  drule_all packaged_internal_entry_locals_alloc_ok >> strip_tac >>
  drule_all intcall_entry_prelock_resources_nr >>
  disch_then (qx_choose_then `v0` strip_assume_tac) >>
  qpat_x_assum `run_inst_seq _ _ = OK v0` mp_tac >>
  asm_rewrite_tac[] >> simp[] >> disch_then SUBST_ALL_TAC >>
  `(cx with stk updated_by CONS (NONE,name)).nonreentrant_slot = SOME key /\
   nonreentrant_slot_separated (cx with stk updated_by CONS (NONE,name))` by
    simp[] >>
  `!op. (ce2 with <|ce_imm_alloca := imm; ce_alloca_locals := T|>).ce_imm_alloca = SOME op ==>
     ?x. op = Var x /\ not_fresh_at prelock x` by metis_tac[] >>
  drule_all internal_entry_lock_success_resources >> strip_tac >>
  drule compile_nonreentrant_lock_transient_counter >> strip_tac >>
  `prelock.cs_next_var <= body_start.cs_next_var` by decide_tac >>
  `supported_program tops /\
   evaluate_type (get_tenv (cx with stk updated_by CONS (NONE,name))) ret = SOME rtv` by
    (drule bodyIntCallSeamDefsTheory.intcall_entry_source >>
     simp[get_tenv_def] >> strip_tac >> fs[body_inv_def]) >>
  qmatch_asmsub_abbrev_tac `stmt_state_rel ctx callee root cxf es1 v0` >>
  `?fp. intcall_frame_ok fp /\
    fp.jc_tops = tops /\ fp.jc_ctx = ctx /\ fp.jc_func = callee /\
    fp.jc_cx = cxf /\ fp.jc_owner = (NONE,name) /\ fp.jc_ancestors = cx.stk /\
    fp.jc_edges = E /\ fp.jc_ret_ty = ret /\ fp.jc_ret_tv = rtv /\
    fp.jc_lo = t.vs_alloca_next /\ fp.jc_morig = t /\ fp.jc_oorig = u /\
    fp.jc_root_ce = root /\ fp.jc_rpc = rpc /\ fp.jc_pc = entered.vs_return_pc_token /\
    fp.jc_rb = (if has_rb then SOME (HD argv,type_memory_size rtv) else NONE) /\
    fp.jc_prot = P /\ fp.jc_staged = staged /\
    fp.jc_reserved = (\op. op = rpc \/
      (?sz. root.ce_return_buf = SOME (PtrVar op sz)) \/ root.ce_imm_alloca = SOME op) /\
    intcall_joint_res fp root env locked body_start
      (u with vs_inst_idx := LENGTH body_start.cs_current_insts)` by
    (qpat_x_assum `!a k. P a k <=> _` kall_tac >>
     qpat_x_assum `!b z. staged b z <=> _` kall_tac >>
     irule internal_entry_root_joint_after_lock_advance >>
     simp[Abbr `root`, Abbr `cxf`] >>
     qexistsl [`es1`, `T`, `prelock`, `v0`, `is_view_mut mut`] >>
     qpat_x_assum `ret = NoneT \/ stmts_no_fallthrough ss` kall_tac >>
     gvs[] >> metis_tac[]) >>
  qexistsl [`locked`, `fp`, `env`, `env_after`, `bindings`] >>
  qpat_x_assum `!a k. P a k <=> _` kall_tac >>
  qpat_x_assum `!b z. staged b z <=> _` kall_tac >>
  `lock_if_nr cx T (is_view_mut mut) es1 = (INL (),locked)` by
    (qpat_x_assum `lock_if_nr cxf _ _ _ = _` mp_tac >>
     simp[Abbr `cxf`, lock_if_nr_def, check_not_static_def]) >>
  qpat_x_assum `!locked. lock_if_nr cx _ _ _ = _ ==> _` drule >>
  simp[] >> qpat_x_assum `lock_if_nr cx _ _ _ = _` mp_tac >>
  simp[lock_if_nr_def]
QED
