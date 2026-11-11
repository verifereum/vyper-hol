(* Joint resources for a supplied actual-entry root. Semantic typing inputs
   stay abstract; geometry and administrative resources use entry boundaries. *)
Theory bodyIntCallActualJointInit
Ancestors
  bodyIntCallActualRootFrame bodyIntCallJointEntry
  bodyIntCallActualEntryProtection bodyIntCallActualEntryLanding
  bodyIntCallActualEntryWitness bodyIntCallActualEntryReservation
  bodyIntCallJointContract intCallCallee compileEnv context exprLoweringProps
  loweringPosts venomState finite_map list

Theorem internal_entry_joint_res_init:
  compile_internal_function_entry ce params has_rb ctor imm_len rt st0 =
    ((ce2,rpc,imm),st1) /\
  fn_has_code st0 st1 func /\ fn_inst_ids_distinct func /\
  setup_callee func args caller = SOME s0 /\
  internal_args_rel ce params sc (if has_rb then 1 else 0) args
    caller.vs_alloca_next caller.vs_memory /\
  caller.vs_alloca_next + internal_stack_size ce params < dimword (:256) /\
  run_inst_seq (emitted_insts st0 st1) s0 = OK u /\
  intcall_frame_ok fp /\ fp.jc_ctx = ctx /\ fp.jc_func = func /\
  fp.jc_root_ce = (ce2 with <|ce_imm_alloca := imm; ce_alloca_locals := T|>) /\
  fp.jc_cx = cx /\ fp.jc_oorig = u /\ fp.jc_morig = origin /\
  fp.jc_lo = caller.vs_alloca_next /\ fp.jc_prot = P /\ fp.jc_staged = staged /\
  fp.jc_rb = (if has_rb then SOME (HD args,capacity) else NONE) /\
  state_rel f ce cx (vs with scopes := []) caller /\
  internal_immutable_regions ce cx vs caller.vs_alloca_next /\
  alloca_room ctx func s0 /\ fmp_room ctx func s0 /\
  (ce.ce_is_ctor ==> IS_SOME (FLOOKUP caller.vs_labels "runtime_begin")) /\
  (ce.ce_is_ctor ==> !i po psz name tv iv io.
    i < LENGTH params /\ ~SND (EL i params) /\
    FLOOKUP ce.ce_vars (FST (EL i params)) = SOME (MemLoc po psz) /\
    FLOOKUP ce.ce_module_vars (ce.ce_module,name) = SOME (ImmutableLoc io) /\
    FLOOKUP (case ALOOKUP vs.immutables cx.txn.target of NONE => FEMPTY
      | SOME imms => get_source_immutables ce.ce_module imms) name = SOME (tv,iv) ==>
    regions_disjoint io (type_memory_size tv)
      (w2n (EL ((if has_rb then 1 else 0) + i) args)) psz) /\
  expr_sim_inv fp.jc_root_ce cx env (vs with scopes := [sc]) /\
  ce_locals_declared fp.jc_root_ce env /\ locals_alloc_ok fp.jc_root_ce env /\
  local_ptrs_reserved fp.jc_root_ce st1 /\
  (!op x. fp.jc_reserved op /\ op = Var x ==> not_fresh_at st1 x) /\
  (!a k. P a k ==> a + k <= caller.vs_alloca_next) /\
  (!a k. P a k ==>
    mem_bytes_at a k s0.vs_memory = mem_bytes_at a k origin.vs_memory) /\
  (!i off sz. i < LENGTH params /\ ~SND (EL i params) /\
    FLOOKUP ce.ce_vars (FST (EL i params)) = SOME (MemLoc off sz) ==>
    ?b z. staged b z /\ b <= w2n (EL ((if has_rb then 1 else 0) + i) args) /\
      w2n (EL ((if has_rb then 1 else 0) + i) args) + sz <= b + z) /\
  (has_rb ==> (?off sz. ce.ce_return_buf = SOME (MemLoc off sz)) /\
    w2n (HD args) + capacity <= caller.vs_alloca_next) /\
  (~has_rb ==> ce.ce_return_buf = NONE) /\
  (!bw cap. fp.jc_rb = SOME (bw,cap) /\ fp.jc_root_ce.ce_is_ctor ==>
    !nm tv iv io.
    FLOOKUP fp.jc_root_ce.ce_module_vars (fp.jc_root_ce.ce_module,nm) =
      SOME (ImmutableLoc io) /\
    FLOOKUP (case ALOOKUP vs.immutables cx.txn.target of NONE => FEMPTY
      | SOME imms => get_source_immutables fp.jc_root_ce.ce_module imms) nm =
      SOME (tv,iv) ==>
    regions_disjoint io (type_memory_size tv) (w2n bw) cap) ==>
  intcall_joint_res fp fp.jc_root_ce env (vs with scopes := [sc]) st1
    (u with vs_inst_idx := LENGTH st1.cs_current_insts)
Proof
  strip_tac >>
  drule_all internal_entry_landing_stmt_state_rel >>
  disch_then (qspec_then `u.vs_inst_idx` assume_tac) >>
  drule_all internal_entry_landing_allocas_above >> strip_tac >>
  drule_all internal_entry_landing_return_buf >> strip_tac >>
  drule_all internal_entry_installed_protection >> strip_tac >>
  qpat_assum `fp.jc_oorig = u` (fn th => rewrite_tac[GSYM th]) >>
  irule internal_root_joint_res_init >>
  fs[stmt_state_rel_inst_idx] >> simp[] >>
  conj_tac
  >- (strip_tac >>
      qpat_x_assum `!bw cap. fp.jc_rb = SOME (bw,cap) /\ _ ==> _`
        (qspecl_then [`HD args`, `capacity`] mp_tac) >> simp[]) >>
  gvs[] >> first_assum ACCEPT_TAC
QED

(* Construction boundary: all fields are exposed for subsequent producer use.
   The actual-entry lemmas supply these semantic and resource inputs without
   depending on which root record witnesses the compiler fields. *)
Theorem internal_entry_root_joint_exists:
  supported_program tops /\ cxf.stk = owner::ancestors /\
  call_stack_follows (call_edge_rel edges) cxf.stk /\
  irreflexive (TC (call_edge_rel edges)) /\
  functions_follow_call_graph edges cxf /\
  evaluate_type (get_tenv cxf) ret = SOME rtv /\
  root.ce_return_pc = SOME (PtrVar rpc 0) /\ cenv_module_pins tops root /\
  root.ce_returns_count = returns_stack_count
    (\name. MAP (FST o SND) (get_struct_fields root.ce_struct_fields name)) ret /\
  (has_rb <=> root.ce_returns_count = 0 /\ ret <> NoneT) /\
  (?x. rpc = Var x /\ not_fresh_at st x /\ lookup_var x u = SOME pc) /\
  (!op sz. root.ce_return_buf = SOME (PtrVar op sz) ==>
    ?x w. op = Var x /\ not_fresh_at st x /\ lookup_var x u = SOME w) /\
  (!op. root.ce_imm_alloca = SOME op ==>
    ?x w. op = Var x /\ not_fresh_at st x /\ lookup_var x u = SOME w) /\
  (!a k. P a k ==> a + k <= lo) /\
  (!b z. staged b z ==> !a k. P a k ==> regions_disjoint a k b z) /\
  (has_rb ==> cap = type_memory_size rtv /\ w2n bw + cap <= lo /\
    (!b z. staged b z ==> regions_disjoint (w2n bw) cap b z) /\
    (!a k. P a k ==> regions_disjoint a k (w2n bw) cap)) /\
  stmt_state_rel ctx callee root cxf es u /\ expr_sim_inv root cxf env es /\
  ce_locals_declared root env /\ locals_alloc_ok root env /\
  local_ptrs_reserved root st /\ allocas_above lo u /\
  (!a k. P a k ==> mem_bytes_at a k u.vs_memory = mem_bytes_at a k origin.vs_memory) /\
  (!n p k. local_region root es.scopes u n p k ==>
    lo <= p \/ ?b z. staged b z /\ b <= p /\ p + k <= b + z) /\
  return_buf_frame (if has_rb then SOME (bw,cap) else NONE) root st u /\
  (has_rb /\ root.ce_is_ctor ==> !nm tv iv io.
    FLOOKUP root.ce_module_vars (root.ce_module,nm) = SOME (ImmutableLoc io) /\
    FLOOKUP (case ALOOKUP es.immutables cxf.txn.target of NONE => FEMPTY
      | SOME imms => get_source_immutables root.ce_module imms) nm = SOME (tv,iv) ==>
    regions_disjoint io (type_memory_size tv) (w2n bw) cap) ==>
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
    intcall_joint_res fp root env es st
      (u with vs_inst_idx := LENGTH st.cs_current_insts)
Proof
  strip_tac >>
  drule_all (SRULE [PULL_EXISTS] internal_entry_root_frame_exists) >>
  disch_then (qspecl_then [`origin`, `ctx`, `callee`] strip_assume_tac) >>
  qexists `fp` >> simp[] >>
  qpat_assum `fp.jc_root_ce = root` (fn th => rewrite_tac[GSYM th]) >>
  qpat_assum `fp.jc_oorig = u` (fn th => rewrite_tac[GSYM th]) >>
  irule internal_root_joint_res_init >> simp[] >>
  gvs[] >> rpt conj_tac >> first_assum ACCEPT_TAC
QED
