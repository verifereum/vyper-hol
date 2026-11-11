(* Pure-argument staging: source annotation and layout boundary. *)
Theory bodyIntCallFamCallIntPureStageInterface
Ancestors
  bodyExprPreFacts exprSimHyps exprSimHypsDefs abiBuiltinEncodeWord

Theorem intcall_pure_post_type:
  supported_pure_expr tops e ==> post_value_type ce e = expr_type e
Proof
  metis_tac[supported_pure_int_calls, post_value_type_no_calls]
QED

Theorem intcall_pure_stage_layout:
  supported_pure_expr tops e /\ expr_body_pre ce cx env e es ==>
  ?tv. post_value_type ce e = expr_type e /\
    evaluate_type (get_tenv cx) (expr_type e) = SOME tv /\
    type_memory_bytes ce (expr_type e) = type_memory_size tv /\
    type_memory_size tv < 2**64
Proof
  strip_tac >>
  `post_value_type ce e = expr_type e` by
    metis_tac[intcall_pure_post_type] >>
  drule post_type_evaluates >> strip_tac >> gvs[] >>
  `expr_sim_inv ce cx env es` by fs[expr_body_pre_def] >>
  `type_memory_bytes ce (expr_type e) = type_memory_size tv` by
    metis_tac[expr_sim_inv_memory_size] >>
  simp[] >> Cases_on `is_word_type (expr_type e)`
  >- (`type_memory_bytes ce (expr_type e) = 32` by
        metis_tac[abi_builtin_encode_word_info] >> gvs[]) >>
  drule_all expr_body_pre_copy_ok >> simp[]
QED

(* Successful delayed reads are pointwise at one fixed source state. *)
Theorem intcall_read_results_index:
  !rs vs es i.
    read_results cx rs es = (INL vs,es) /\ i < LENGTH rs ==>
    read_result cx (EL i rs) es = (INL (EL i vs),es)
Proof
  Induct_on `rs` >- simp[] >>
  rpt gen_tac >>
  simp[Once vyperStateTheory.read_results_def,
       vyperStateTheory.bind_def, vyperStateTheory.return_def,
       AllCaseEqs()] >> strip_tac >>
  drule vyperStateTheory.read_result_state >> strip_tac >> gvs[] >>
  drule vyperStateTheory.read_results_state >> strip_tac >> gvs[] >>
  Cases_on `i` >> gvs[] >> first_x_assum irule >> simp[]
QED

(* Premise provenance for the pure staging consumer (not a staging theorem):
   - Purity: supported_effect_expr's IntCall clause supplies
     supported_pure_exprs tops ds; supported_pure_exprs_every turns this into
     EVERY (supported_pure_expr tops) ds.
   - Annotation/post equality, evaluation, layout and size: the first two
     boundaries above apply to each member's expr_body_pre. At the traversal
     endpoint expr_body_pre_state_transport uses the endpoint expr_sim_inv.
   - Pointwise reads: intcall_read_results_index above; read_results_length
     supplies LENGTH values = LENGTH rs.
   - Value typing: vyperTypeEvalSoundness.eval_scc_type_sound_results_mutual,
     its final eval_expr_results conjunct, consumes well_typed_exprs env ds,
     env_consistent env cx es, state_well_typed es, context_well_typed cx,
     accounts_well_typed es.accounts, functions_well_typed cx,
     call_evaluation_safe cx (int_calls_exprs ds), and the actual successful
     eval_expr_results run. It returns state_well_typed ee and
     expr_results_typed (env,cx,ee) ds rs. read_results_typed then returns
     exprs_runtime_typed env ds values. exprs_runtime_typed_value_expr_LIST_REL
     (vyperTypeBindArguments) gives each evaluated annotation/value_has_type;
     env.type_defs = get_tenv cx comes from expr_sim_inv.
   - Well-formedness: exprSimAggregateChildren.typed_value_wf's first conjunct
     gives value_has_type tv v ==> val_wf tv v. No independent wf premise is
     needed at this consumer.
   - Equal-type stores: dty = sty = expr_type child, so StageStore's final
     incompatible-layout implication is vacuous. Remove all widening metadata,
     the duplicate evaluated layout and type_widens_to from the old candidate.

   Integration gap, NOT an unavailable external contract clause:
   Traverse.intcall_deferred_traverse retains the deferred list and joint
   resources, but no explicit expr_results_typed certificate. A deferred
   certificate by itself is not a source typing certificate: vv_holds relates
   representations, not value_has_type. Before recursive staging, the consumer
   must combine the actual successful eval_expr_results branch with the
   source-soundness theorem above (including its gas-observation reset) and
   expr_body_pre's source invariant. Alternatively a new traversal wrapper can
   carry that source typing consequence. This file does not assume an indexed
   value_has_type premise in an outer producer or assert the old candidate.
   The exact source-run/reset adapter remains to be authorized and checked.
*)
