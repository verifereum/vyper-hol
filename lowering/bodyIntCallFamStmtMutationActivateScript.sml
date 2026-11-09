(* Activate a physically initialized local without changing machine resources. *)
Theory bodyIntCallFamStmtMutationActivate
Ancestors
  bodyIntCallJointContract bodyIntCallDeclarationStore
  bodyIntCallDeclarationRegions

Theorem intcall_declared_local_activate_resources:
  let es' = es with scopes :=
        (sc |+ (id,<|assignable := a; type := tv; value := v; popped := []|>)) :: rest
  in
  intcall_expr_res fp ce env es sa s /\
  fn_inst_ids_distinct fp.jc_func /\ es.scopes = sc :: rest /\
  lookup_scopes id es.scopes = NONE /\
  FLOOKUP ce.ce_vars id = SOME (PtrVar (Var p) sz) /\
  not_local_ptr ce es.scopes p /\ lookup_var p s = SOME w /\
  MEM inst (fn_insts fp.jc_func) /\ inst.inst_opcode = ALLOCA /\
  inst.inst_outputs = [p] /\
  FLOOKUP s.vs_allocas inst.inst_id = SOME (w2n w,sz) /\
  type_memory_size tv <= sz /\ val_wf tv v /\
  val_in_memory tv v (w2n w) s.vs_memory /\
  expr_sim_inv ce fp.jc_cx env' es' /\ locals_alloc_ok ce env' /\
  ce_locals_declared ce env' ==>
  intcall_joint_res fp ce env' es' sa s
Proof
  pure_rewrite_tac [LET_THM] >> BETA_TAC >> strip_tac >>
  `stmt_state_rel fp.jc_ctx fp.jc_func ce fp.jc_cx
    (es with scopes :=
      (sc |+ (id,<|assignable := a; type := tv; value := v; popped := []|>)) :: rest) s` by
    (irule declared_local_activate >>
     fs[intcall_expr_res_def] >> metis_tac[]) >>
  fs[intcall_joint_res_def, intcall_expr_res_def] >>
  reverse conj_tac >- metis_tac[] >>
  ho_match_mp_tac (local_region_declared_allocation |> SPEC_ALL |>
    Q.INST [`lo` |-> `fp.jc_lo`, `aid` |-> `inst.inst_id`,
            `size_bytes` |-> `sz`]) >>
  goal_assum (drule_at Any) >> simp[] >> metis_tac[]
QED
