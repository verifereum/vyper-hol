(* Checked refutation of the frozen immutable assignment obligation. *)
Theory immutableDeployCounterexample
Ancestors
  immutableDeployLocalOutcomeProbe immutableDeployLocalEndpointProbe
  immutableDeployLocalPremiseProbe stmtSimDefs

Theorem local_probe_not_stmt_frag:
  ~stmt_frag local_probe_unit.cu_context local_probe_fn local_probe_cx
    NoLoop (\v es r. F) local_probe_empty_ce
    (stmt_env local_probe_empty_ce NoLoop NoneT local_probe_empty_stmt)
    (eval_stmt local_probe_cx local_probe_empty_stmt) local_probe_es
Proof
  rewrite_tac[stmt_frag_def, stmt_framed_frag_def] >> strip_tac >>
  qpat_x_assum `!sa sb s0 cenv'. _` (qspecl_then
    [`local_probe_sa`,
     `SND (stmt_env local_probe_empty_ce NoLoop NoneT local_probe_empty_stmt local_probe_sa)`,
     `local_probe_entry`, `local_probe_empty_ce`] mp_tac) >>
  simp[local_probe_compilation, local_probe_joint_premises,
    local_probe_no_counted_outcome]
QED

Theorem immutable_deploy_assign_case_false:
  ~(!ctx func cx lctx RetQ cenv ty env tops nsid e es ity.
    body_inv tops ctx cenv cx /\ cx.in_deploy /\
    supported_immutable_type tops nsid = SOME ity /\
    type_place_target env (TopLevelNameTarget nsid) = SOME (Type ity) /\
    type_widens_to env.type_defs (expr_type e) ity /\
    expr_vv_sim ctx func cenv cx (expr_type e) e es /\
    expr_body_pre cenv cx env e es ==>
    stmt_frag ctx func cx lctx RetQ cenv
      (stmt_env cenv lctx ty (Assign (BaseTarget (TopLevelNameTarget nsid)) e))
      (eval_stmt cx (Assign (BaseTarget (TopLevelNameTarget nsid)) e)) es)
Proof
  strip_tac >>
  qpat_x_assum `!ctx func cx lctx RetQ cenv ty env tops nsid e es ity. _`
    (qspecl_then [`local_probe_unit.cu_context`, `local_probe_fn`,
      `local_probe_cx`, `NoLoop`, `\v es r. F`, `local_probe_empty_ce`,
      `NoneT`, `local_probe_env`, `local_probe_tops`, `(NONE,"dst")`,
      `Name (StructT (NONE,"Empty")) "x"`, `local_probe_es`,
      `StructT (NONE,"Empty")`] mp_tac) >>
  simp[local_probe_joint_premises, GSYM immutableDeployLocalCodeProbeTheory.local_probe_empty_stmt_def,
    local_probe_not_stmt_frag]
QED
