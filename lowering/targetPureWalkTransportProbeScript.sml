(* Relational boundary for the zero-index compiler probe. *)
Theory targetPureWalkTransportProbe
Ancestors
  targetPureWalkSimulationProbe exprSimProps targetPlaceSimCasesBase
  loweringPosts exprLoweringProps loweringStateRelDefs venomState
  finite_map exprOperandVar compileEnv

Theorem simulation_probe_source_transport:
  !ctx fn cx es ee s.
    stmt_state_rel ctx fn simulation_probe_cenv cx es s /\
    ee.scopes = es.scopes /\ ee.accounts = es.accounts /\
    ee.tStorage = es.tStorage /\ ee.logs = es.logs /\
    ee.outcomes = es.outcomes /\ ee.requests = es.requests /\
    ee.pending_deletions = es.pending_deletions ==>
    stmt_state_rel ctx fn simulation_probe_cenv cx ee s
Proof
  rpt strip_tac >>
  fs[stmt_state_rel_def, state_rel_def, storage_rel_def, transient_rel_def,
     accounts_rel_def, logs_rel_def, immutables_rel_def,
     immutable_alloca_sep_def, immutable_decl_sep_alt,
     simulation_probe_cenv_def] >> first_assum ACCEPT_TAC
QED

Theorem simulation_probe_target_post_transport:
  !fn cx es ee sa sb s0 t pv vt p w.
    stmt_state_rel simulation_probe_context fn simulation_probe_cenv cx es t /\
    local_ptrs_reserved simulation_probe_cenv sa /\
    place_ptr_rel simulation_probe_cenv cx s0 pv w (SOME LocMemory) vt /\
    eval_operand p t = SOME w /\
    (!x. p = Var x ==> not_fresh_at sb x) /\
    place_readable cx ee pv /\
    ee.scopes = es.scopes /\ ee.accounts = es.accounts /\
    ee.tStorage = es.tStorage /\ ee.logs = es.logs /\
    ee.outcomes = es.outcomes /\ ee.requests = es.requests /\
    ee.pending_deletions = es.pending_deletions /\
    (!x v. not_fresh_at sa x /\ lookup_var x s0 = SOME v ==>
       lookup_var x t = SOME v) /\
    (!aid b. FLOOKUP s0.vs_allocas aid = SOME b ==>
       FLOOKUP t.vs_allocas aid = SOME b) /\
    t.vs_memory = s0.vs_memory ==>
    target_post simulation_probe_context fn simulation_probe_cenv cx es sa sb
      s0 ee pv vt (p,SOME LocMemory,SOME (value_type_place vt)) t
Proof
  rpt strip_tac >>
  `stmt_state_rel simulation_probe_context fn simulation_probe_cenv cx ee t` by
    (irule simulation_probe_source_transport >> qexists_tac `es` >> simp[]) >>
  `place_ptr_rel simulation_probe_cenv cx t pv w (SOME LocMemory) vt` by
    (Cases_on `pv` >> gvs[place_ptr_rel_def] >>
     Cases_on `p'` >> gvs[place_ptr_rel_def] >>
     fs[local_ptrs_reserved_def] >> metis_tac[]) >>
  simp[target_post_def] >> irule locals_kept_mem >> simp[]
QED

Theorem simulation_probe_pointer_reserved:
  !sa sb op x.
    compile_get_target_ptr compile_expr simulation_probe_cenv
      module_probe_target sa = (op,sb) /\ FST op = Var x ==>
    not_fresh_at sb x
Proof
  rpt gen_tac >>
  rewrite_tac[simulation_probe_compile_target, comp_ignore_bind_def, comp_bind_def] >>
  Cases_on `emit_void INVOKE [Label simulation_probe_label] sa` >>
  Cases_on `compile_array_subscript (Var "a_ptr") (Lit 0w) F 1 32 32 F
    (compile_ptr_load F simulation_probe_cenv.ce_imm_alloca LocMemory) r` >>
  simp[comp_return_def] >> strip_tac >> gvs[] >>
  metis_tac[compiler_subscript_ops_var]
QED

Theorem simulation_probe_zero_place:
  !cx s w.
    eval_operand (Var "a_ptr") s = SOME w ==>
    place_ptr_rel simulation_probe_cenv cx s
      (PlaceR (MemoryPlace "a" [ValueSubscript (IntV 0)])) w
      (SOME LocMemory) (Type (BaseT (UintT 256)))
Proof
  simp[place_ptr_rel_def, simulation_probe_cenv_def, FLOOKUP_UPDATE,
       eval_operand_def] >> rpt strip_tac >>
  qexistsl_tac [`ArrayTV (BaseTV (UintT 256)) (Fixed 1)`, `0`,
                 `BaseTV (UintT 256)`] >> EVAL_TAC >>
  simp[wordsTheory.dimword_def, wordsTheory.WORD_ADD_0]
QED
