(* Arbitrary-bound primitive interface probes for the joint request path. *)
Theory bodyFullExtCallRequestPrimitives
Ancestors
  fragExecPtr bodyPtrEnvBuiltinsEdges ptrSafeRun ptrDiscipline venomInst
  codegenRel contextCodegenRel

Theorem extcall_alloca_check_at:
  ~ctx_has_dalloca ctx /\ allocas_from lo s ==>
  ptr_inst_ok D lo fuel ctx fn G tn
    (mk_inst id ALLOCA [Lit n] [out]) s
Proof
  strip_tac >> drule ptr_inst_ok_alloca >>
  disch_then (qspecl_then [`D`, `fn`, `G`, `tn`, `s`, `id`, `n`, `out`, `fuel`]
    mp_tac) >>
  simp[ptr_inst_ok_def, access_ok_def, mk_inst_def,
    source_memory_write_ranges_def, source_memory_read_ranges_def]
QED

Theorem extcall_selector_store_check_at:
  ptr_covers G tn p s 32 /\ ~ctx_has_dalloca ctx /\ allocas_from lo s ==>
  ptr_inst_ok D lo fuel ctx fn G tn
    (mk_inst id MSTORE [Var p; Lit selector] []) s
Proof
  strip_tac >>
  `ptr_inst_ok D 0 fuel ctx fn G tn
    (mk_inst id MSTORE [Var p; Lit selector] []) s` by
    (irule ptr_inst_ok_mstore >> simp[op_taint_def]) >>
  gvs[ptr_inst_ok_def, access_ok_def] >> rpt strip_tac >>
  first_x_assum irule >> simp[]
QED

Theorem extcall_buffer_add_check_at:
  op_taint tn (Var p) = {} /\ ~ctx_has_dalloca ctx /\ allocas_from lo s /\
  lo <= s.vs_alloca_next ==>
  ptr_inst_ok D lo fuel ctx fn G tn
    (mk_inst id ADD [Var p; Lit 28w] [out]) s
Proof
  strip_tac >> irule ptr_inst_ok_scalar_builtin_at >> simp[] >>
  rpt strip_tac >> gvs[op_taint_def]
QED
