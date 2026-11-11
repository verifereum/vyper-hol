(* Source-normalized application boundary for the actual-entry initializer. *)
Theory bodyIntCallSourceJointInit
Ancestors bodyIntCallActualJointInit

Theorem internal_entry_source_joint_res_init:
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
  expr_sim_inv fp.jc_root_ce cx env vs /\
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
    regions_disjoint io (type_memory_size tv) (w2n bw) cap) /\
  vs with scopes := [sc] = vs ==>
  intcall_joint_res fp fp.jc_root_ce env vs st1
    (u with vs_inst_idx := LENGTH st1.cs_current_insts)
Proof
  strip_tac >>
  qpat_assum `vs with scopes := [sc] = vs`
    (fn th => once_rewrite_tac[GSYM th]) >>
  irule internal_entry_joint_res_init >>
  rpt (conj_tac >- first_assum ACCEPT_TAC) >>
  goal_assum (drule_at (Pat `compile_internal_function_entry _ _ _ _ _ _ _ = _`)) >>
  goal_assum (drule_at (Pat `setup_callee _ _ _ = _`)) >>
  goal_assum (drule_at (Pat `fp.jc_rb = _`)) >>
  goal_assum (drule_at (Pat `state_rel _ _ _ _ _`)) >>
  asm_rewrite_tac[] >>
  qexistsl [`P`, `capacity`, `ctx`, `origin`, `staged`] >> gvs[]
QED
