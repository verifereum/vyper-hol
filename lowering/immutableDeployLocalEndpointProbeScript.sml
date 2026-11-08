(* Source and endpoint audit for the jointly certified local fixture. *)
Theory immutableDeployLocalEndpointProbe
Ancestors
  immutableDeployLocalPremiseProbe immutableDeployLocalCodeProbe

Theorem local_probe_eval_stmt:
  !gs. eval_stmt local_probe_cx local_probe_empty_stmt
    (local_probe_es with gas_obs := gs) =
    (INL (), local_probe_es with gas_obs := gs)
Proof
  gen_tac >> EVAL_TAC >> simp[finite_mapTheory.FLOOKUP_EXT, FUN_EQ_THM,
    finite_mapTheory.FLOOKUP_UPDATE] >>
  gen_tac >> Cases_on `x = "dst"` >> gvs[]
QED

Theorem local_probe_compilation:
  stmt_env local_probe_empty_ce NoLoop NoneT local_probe_empty_stmt local_probe_sa =
    (local_probe_empty_ce,
     local_probe_sa with <|cs_next_var := 4; cs_next_id := 6;
       cs_current_insts := local_probe_sa.cs_current_insts ++
         [mk_inst 3 MLOAD [Var "%1"] ["%2"];
          mk_inst 4 ADD [Var "%0"; Lit 0w] ["%3"];
          mk_inst 5 ISTORE [Var "%3"; Var "%2"] []]|>)
Proof
  once_rewrite_tac[pairTheory.PAIR_FST_SND_EQ] >>
  conj_tac
  >- simp[stmt_env_environment_projection, local_probe_empty_stmt_def,
          stmtLoweringTheory.declare_stmt_local_def, compileEnvTheory.comp_return_def] >>
  simp[local_probe_assignment_shape]
QED

Definition local_probe_after_load_def:
  local_probe_after_load = (update_var "%2" 0w local_probe_entry) with vs_inst_idx := 4
End
Definition local_probe_after_add_def:
  local_probe_after_add = (update_var "%3" 0w local_probe_after_load) with vs_inst_idx := 5
End
Definition local_probe_after_store_def:
  local_probe_after_store = (istore 0 0w local_probe_after_add) with vs_inst_idx := 6
End

Theorem local_probe_assignment_steps:
  !fuel ctx.
    step_inst fuel ctx (mk_inst 3 MLOAD [Var "%1"] ["%2"]) local_probe_entry =
      OK (update_var "%2" 0w local_probe_entry) /\
    step_inst fuel ctx (mk_inst 4 ADD [Var "%0"; Lit 0w] ["%3"])
      local_probe_after_load = OK (update_var "%3" 0w local_probe_after_load) /\
    step_inst fuel ctx (mk_inst 5 ISTORE [Var "%3"; Var "%2"] [])
      local_probe_after_add = OK (istore 0 0w local_probe_after_add)
Proof
  rpt gen_tac >> conj_tac
  >- (EVAL_TAC >> simp[wordsTheory.dimword_def, venomMemPropsTheory.dimindex_256] >> EVAL_TAC >> simp[wordsTheory.word_0_n2w]) >>
  conj_tac
  >- (EVAL_TAC >> simp[wordsTheory.dimword_def, venomMemPropsTheory.dimindex_256,
       wordsTheory.WORD_ADD_0]) >>
  EVAL_TAC >> simp[wordsTheory.dimword_def, venomMemPropsTheory.dimindex_256,
       wordsTheory.word_0_n2w]
QED

Theorem local_probe_endpoint_no_immutables_rel:
  !gs. ~immutables_rel local_probe_empty_ce local_probe_cx.txn.target NONE T
    (local_probe_es with gas_obs := gs) local_probe_after_store
Proof
  gen_tac >> rewrite_tac[compileEnvTheory.immutables_rel_def] >>
  simp[] >> qexistsl
    [`"neighbor"`, `BaseTV (UintT 256)`, `IntV 1`, `0`] >>
  simp[local_probe_empty_ce_def, local_probe_real_ce_shape] >>
  EVAL_TAC >> simp[local_probe_one_bytes,
    byteTheory.word_to_bytes_aux_compute, byteTheory.get_byte_def,
    byteTheory.byte_index_def, fcpLib.INDEX_CONV ``dimindex(:256)``,
    wordsTheory.dimword_def] >> EVAL_TAC >> simp[wordsTheory.word_0_n2w] >>
  wordsLib.WORD_DECIDE_TAC
QED

Theorem local_probe_endpoint_no_post:
  !gs sb. ~stmt_post local_probe_unit.cu_context local_probe_fn local_probe_cx
    NoLoop local_probe_empty_ce local_probe_empty_ce local_probe_sa sb
    local_probe_entry (INL ()) (local_probe_es with gas_obs := gs)
    local_probe_after_store
Proof
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `stmt_post _ _ _ _ _ _ _ _ _ _ _ _` mp_tac >>
  rewrite_tac[stmtSimDefsTheory.stmt_post_def] >> strip_tac >> gvs[] >>
  qpat_x_assum `stmt_state_rel _ _ _ _ _ _` mp_tac >>
  rewrite_tac[exprLoweringPropsTheory.stmt_state_rel_def,
    compileEnvTheory.state_rel_def] >> strip_tac >>
  `local_probe_empty_ce.ce_module = NONE /\ local_probe_empty_ce.ce_is_ctor = T` by
    (simp[local_probe_empty_ce_def, local_probe_real_ce_shape] >> EVAL_TAC) >>
  qpat_x_assum `immutables_rel _ _ _ _ _ _` mp_tac >>
  simp[] >>
  qspec_then `local_probe_es.gas_obs` mp_tac local_probe_endpoint_no_immutables_rel >>
  simp[]
QED
