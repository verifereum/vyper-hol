(* One actual prologue run carries semantic and spatial entry resources.
   Memory is referenced to the caller; root operands are referenced to the
   eventual landing, not to caller registers cleared by setup_callee. *)
Theory bodyIntCallPrologueInit
Ancestors
  bodyIntCallPrologueResource bodyIntCallSemanticEntry intCallFrame
  loweringPosts intCallCallee vyperTypeCallStackSoundness
  exprLoweringProps compileEnv venomState venomExecSemantics
  list rich_list finite_map words fragExec

(* Administrative room invariants at the fixed instruction endpoint. *)
Theorem internal_prologue_landing_rooms:
  compile_internal_prologue ce params has_rb rt st0 = ((ce2,rpc),st1) /\
  fn_has_code st0 st1 func /\
  run_inst_seq (emitted_insts st0 st1) s0 = OK u /\
  mat_frame st0 s0 u /\
  alloca_room ctx func s0 /\ fmp_room ctx func s0 ==>
  alloca_room ctx func u /\ fmp_room ctx func u
Proof
  strip_tac >> drule compile_internal_prologue_shape >> strip_tac >>
  `EVERY (\i. MEM i (fn_insts func) /\ i.inst_opcode <> INVOKE)
    (emitted_insts st0 st1)` by
    (fs[EVERY_MEM, emitted_insts_def, DROP_LENGTH_APPEND] >>
     rpt strip_tac >>
     qpat_x_assum `fn_has_code _ _ _` mp_tac >>
     simp[fn_has_code_def] >> strip_tac >>
     irule lookup_block_fn_insts >>
     goal_assum (drule_at Any) >>
     fs[IS_PREFIX_APPEND] >> gvs[]) >>
  conj_tac
  >- (irule run_inst_seq_alloca_room >>
      qexistsl_tac [`emitted_insts st0 st1`, `s0`] >> simp[]) >>
  irule run_inst_seq_fmp_room >>
  qexistsl_tac [`emitted_insts st0 st1`, `s0`] >>
  fs[mat_frame_def] >>
  qpat_x_assum `u = _` (fn th => ONCE_REWRITE_TAC [th]) >> simp[]
QED

Theorem protected_internal_prologue_run:
  compile_internal_prologue ce params has_rb rt st0 = ((ce2,rpc),st1) /\
  fn_has_code st0 st1 func /\ fn_inst_ids_distinct func /\
  setup_callee func args caller = SOME s0 /\
  state_rel f ce cx (vs with scopes := []) caller /\
  internal_immutable_regions ce cx vs caller.vs_alloca_next /\
  internal_args_rel ce params env (if has_rb then 1 else 0) args
    caller.vs_alloca_next caller.vs_memory /\
  (ce.ce_is_ctor ==> !i po psz name tv iv io.
    i < LENGTH params /\ ~SND (EL i params) /\
    FLOOKUP ce.ce_vars (FST (EL i params)) = SOME (MemLoc po psz) /\
    FLOOKUP ce.ce_module_vars (ce.ce_module,name) = SOME (ImmutableLoc io) /\
    FLOOKUP (case ALOOKUP vs.immutables cx.txn.target of NONE => FEMPTY
      | SOME imms => get_source_immutables ce.ce_module imms) name =
      SOME (tv,iv) ==>
    regions_disjoint io (type_memory_size tv)
      (w2n (EL ((if has_rb then 1 else 0) + i) args)) psz) /\
  caller.vs_alloca_next + internal_stack_size ce params < dimword (:256) /\
  (!a k. P a k ==> a + k <= caller.vs_alloca_next) /\
  (!i off sz. i < LENGTH params /\ ~SND (EL i params) /\
    FLOOKUP ce.ce_vars (FST (EL i params)) = SOME (MemLoc off sz) ==>
    ?b z. staged b z /\
      b <= w2n (EL ((if has_rb then 1 else 0) + i) args) /\
      w2n (EL ((if has_rb then 1 else 0) + i) args) + sz <= b + z) ==>
  ?u.
    run_inst_seq (emitted_insts st0 st1) s0 = OK u /\
    state_rel func (ce2 with ce_alloca_locals := T) cx
      (vs with scopes := [env]) u /\
    immutable_alloca_sep func (ce2 with ce_alloca_locals := T) cx
      (vs with scopes := [env]) u /\
    alloca_inv u /\ fresh_vars_wrt st1 u /\
    allocas_above caller.vs_alloca_next u /\
    mat_frame st0 s0 u /\
    (!a k. P a k ==>
      mem_bytes_at a k u.vs_memory = mem_bytes_at a k caller.vs_memory) /\
    (!n p k. local_region ce2 [env] u n p k ==>
      caller.vs_alloca_next <= p \/
      ?b z. staged b z /\ b <= p /\ p + k <= b + z) /\
    (?x. rpc = Var x /\ not_fresh_at st1 x /\
      lookup_var x u = SOME s0.vs_return_pc_token) /\
    (has_rb ==> ?rb. not_fresh_at st1 rb /\
      lookup_var rb u = SOME (HD args) /\
      !off sz. ce.ce_return_buf = SOME (MemLoc off sz) ==>
        ce2.ce_return_buf = SOME (PtrVar (Var rb) sz)) /\
    eval_operand rpc u = SOME s0.vs_return_pc_token /\
    (has_rb ==> !off sz capacity.
      ce.ce_return_buf = SOME (MemLoc off sz) /\
      w2n (HD args) + capacity <= caller.vs_alloca_next ==>
      return_buf_frame (SOME (HD args,capacity)) ce2 st1 u) /\
    (!ctx k. alloca_room ctx func s0 /\ fmp_room ctx func s0 /\
      ce.ce_imm_alloca = NONE /\
      (ce.ce_is_ctor ==> IS_SOME (FLOOKUP caller.vs_labels "runtime_begin")) ==>
      stmt_state_rel ctx func (ce2 with ce_alloca_locals := T) cx
        (vs with scopes := [env]) (u with vs_inst_idx := k))
Proof
  strip_tac >> drule_all internal_prologue_run >> strip_tac >>
  drule_all internal_prologue_landing_resources >> strip_tac >>
  `!a k. P a k ==>
    mem_bytes_at a k s0.vs_memory = mem_bytes_at a k caller.vs_memory` by
    (qpat_x_assum `setup_callee _ _ _ = _` mp_tac >>
     simp[setup_callee_def, AllCaseEqs()] >> strip_tac >>
     pop_assum (SUBST1_TAC o SYM) >> simp[]) >>
  drule_all internal_prologue_protected_landing >> strip_tac >>
  qmatch_asmsub_rename_tac `run_inst_seq _ s0 = OK u` >>
  qexists_tac `u` >> simp[eval_operand_def] >>
  rpt conj_tac
  >~ [`stmt_state_rel _ _ _ _ _ _`]
  >- (rpt strip_tac >> drule_all internal_prologue_landing_rooms >> strip_tac >>
      drule compile_internal_prologue_fields >>
      simp[compile_env_component_equality] >> strip_tac >>
      `u.vs_labels = caller.vs_labels` by
        (qpat_x_assum `mat_frame _ _ _` mp_tac >>
         qpat_x_assum `setup_callee _ _ _ = _` mp_tac >>
         simp[setup_callee_def, AllCaseEqs(), mat_frame_def] >>
         rpt strip_tac >> gvs[venom_state_component_equality]) >>
      simp[stmt_state_rel_inst_idx, stmt_state_rel_def, immutable_base_zero_def] >>
      rpt strip_tac >> first_x_assum drule >> simp[])
  >~ [`allocas_above _ _`]
  >- (fs[mat_inv_def, allocas_above_def] >>
      rpt strip_tac >> first_x_assum irule >> goal_assum drule)
  >~ [`local_region _ _ _ _ _ _`]
  >- (rpt strip_tac >> first_x_assum drule >> simp[]) >>
  rpt strip_tac >> fs[mat_inv_def, return_buf_frame_def] >>
  goal_assum (drule_at Any) >> simp[]
QED

(* The staging predicate is precisely the caller allocation-id interval;
   protected windows are precisely those quantified by the frozen exit. *)
Theorem internal_prologue_caller_windows:
  compile_internal_prologue ce params has_rb rt st0 = ((ce2,rpc),st1) /\
  fn_has_code st0 st1 func /\ fn_inst_ids_distinct func /\
  setup_callee func args caller = SOME s0 /\
  internal_args_rel ce params env (if has_rb then 1 else 0) args
    caller.vs_alloca_next caller.vs_memory /\
  caller.vs_alloca_next + internal_stack_size ce params < dimword (:256) /\
  run_inst_seq (emitted_insts st0 st1) s0 = OK u /\
  (!i off sz. i < LENGTH params /\ ~SND (EL i params) /\
    FLOOKUP ce.ce_vars (FST (EL i params)) = SOME (MemLoc off sz) ==>
    ?aid b z. FLOOKUP caller.vs_allocas aid = SOME (b,z) /\
      n <= aid /\ aid < m /\
      b <= w2n (EL ((if has_rb then 1 else 0) + i) args) /\
      w2n (EL ((if has_rb then 1 else 0) + i) args) + sz <= b + z) ==>
  (!a k. a + k <= caller.vs_alloca_next /\
    (!aid b z. FLOOKUP caller.vs_allocas aid = SOME (b,z) /\
      n <= aid /\ aid < m ==> regions_disjoint a k b z) ==>
    mem_bytes_at a k u.vs_memory = mem_bytes_at a k caller.vs_memory) /\
  (!name p k. local_region ce2 [env] u name p k ==>
    caller.vs_alloca_next <= p \/
    ?aid b z. FLOOKUP caller.vs_allocas aid = SOME (b,z) /\
      n <= aid /\ aid < m /\ b <= p /\ p + k <= b + z)
Proof
  strip_tac >>
  drule_all internal_prologue_landing_resources >> strip_tac >>
  conj_tac
  >- (drule setup_callee_frontier >> strip_tac >>
      qpat_x_assum `mat_frame _ _ _` mp_tac >>
      qpat_x_assum `setup_callee _ _ _ = _` mp_tac >>
      simp[setup_callee_def, AllCaseEqs(), mat_frame_def] >>
      rpt strip_tac >> gvs[] >> metis_tac[]) >>
  fs[mat_inv_def] >> rpt strip_tac >>
  qpat_x_assum `!name b sz. local_region _ _ _ _ _ _ ==> _` drule >>
  strip_tac >- simp[] >>
  disj2_tac >> gvs[] >> first_x_assum drule >> strip_tac >>
  goal_assum (drule_at Any) >> simp[]
QED

