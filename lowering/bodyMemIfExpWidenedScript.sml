(* Memory case of the body induction for a ternary with a widened arm.
   Selected arms are normalized at their actual lowered value type before
   the destination-indexed post is joined to the condition prefix. *)
Theory bodyMemIfExpWidened
Ancestors
  bodyIfExpConditionalMemory bodyIfExpDestinationEndpoint bodyIfExpMemory bodyIfExpCountedOutcome bodyIfExpAggregateEndpoint bodyIfExpCompiledAggregate ifExpPhysicalSourceAllocation bodyIfExpNormalizationSuffix fragGasMemoryLength bodyMemoryPreds bodyIfExpWidenedTyping bodyIfExpTypedMemory typedArrayCopyPathsMem typedFieldCopyPathsMem typedFieldCopyCuts typedFieldCopyAggregateMem

Theorem body_ifexp_widened_call_arm_mem:
  !cx v5 e1 e2 e3.
    (!s'' tv t. eval_expr cx e1 s'' = (INL tv,t) ==> body_expr_mem_ok cx e2) /\
    (!s'' tv t. eval_expr cx e1 s'' = (INL tv,t) ==> body_expr_mem_ok cx e3) /\
    body_expr_mem_ok cx e1 ==>
    !tops ctx func cenv env ty es.
      body_inv tops ctx cenv cx /\
      expr_body_pre cenv cx env (IfExp v5 e1 e2 e3) es /\
      (?e. (e = e2 \/ e = e3) /\
           ~((int_calls_expr e = [] \/
              same_memory_layout cenv (lowered_value_type cenv e) (expr_type e)) /\
             post_value_type cenv e = expr_type e)) ==>
      expr_sim_mem ctx func cenv cx ty (IfExp v5 e1 e2 e3) es /\
      expr_vv_sim_mem ctx func cenv cx ty (IfExp v5 e1 e2 e3) es
Proof
  rpt gen_tac >> strip_tac >> rpt gen_tac >>
  disch_then (CONJUNCTS_THEN2 assume_tac (CONJUNCTS_THEN2 assume_tac kall_tac)) >>
  drule exprSimOperatorsTheory.expr_body_pre_ifexp >> strip_tac >>
  `expr_sim_mem ctx func cenv cx (BaseT BoolT) e1 es` by
    metis_tac[bodyMemoryPredsTheory.body_expr_mem_ok_def] >>
  `!gs tv es1.
    (do result <- eval_expr cx e1; read_result cx result od) (es with gas_obs := gs) = (INL tv,es1) ==>
    expr_body_pre cenv cx env e2 es1 /\ expr_body_pre cenv cx env e3 es1 /\
    expr_sim_mem ctx func cenv cx ty e2 es1 /\ expr_sim_mem ctx func cenv cx ty e3 es1 /\
    expr_vv_sim_mem ctx func cenv cx ty e2 es1 /\ expr_vv_sim_mem ctx func cenv cx ty e3 es1` by
    (rpt gen_tac >> strip_tac >>
     `expr_body_pre cenv cx env e1 (es with gas_obs := gs)` by simp[] >>
     drule_all exprSimSourceTheory.expr_body_pre_eval >> strip_tac >>
     drule exprSimSourceTheory.eval_expr_read_INL >> strip_tac >>
     metis_tac[bodyMemoryPredsTheory.body_expr_mem_ok_def]) >>
  Cases_on `is_word_type v5` >- suspend "word" >>
  `expr_vv_sim_mem ctx func cenv cx ty (IfExp v5 e1 e2 e3) es` by
    (irule ifexp_body_nonword_vv_sim_mem >> metis_tac[]) >>
  simp[] >> irule exprSimMemUnwrapTheory.expr_sim_mem_of_vv_sim_mem >>
  simp[vyperASTTheory.expr_type_def, loweringPostsTheory.post_value_type_def] >>
  conj_tac
  >- (rpt strip_tac >> drule exprSimIfExpTheory.compile_expr_ifexp >> strip_tac >> gvs[]) >>
  qspecl_then [`cenv`, `cx`, `env`, `IfExp v5 e1 e2 e3`]
    mp_tac exprSimHypsTheory.expr_body_pre_copy_ok >>
  simp[vyperASTTheory.expr_type_def] >>
  disch_then (qspec_then `es` mp_tac) >> simp[]
QED

Resume body_ifexp_widened_call_arm_mem[word]:
  `!sa sb op. lower_value compile_expr cenv (BaseT BoolT) e1 sa = (op,sb) ==>
    cs_extends sa sb /\ sa.cs_next_var <= sb.cs_next_var /\ sa.cs_next_id <= sb.cs_next_id` by
    metis_tac[cj 2 exprLoweringPropsTheory.compile_expr_grows] >>
  `!e sa sb op. (e = e2 \/ e = e3) /\ lower_value compile_expr cenv ty e sa = (op,sb) ==>
    cs_extends sa sb /\ sa.cs_next_var <= sb.cs_next_var /\ sa.cs_next_id <= sb.cs_next_id` by
    metis_tac[cj 2 exprLoweringPropsTheory.compile_expr_grows] >>
  conj_tac
  >- (irule compile_ifexp_word_sim_mem >> metis_tac[]) >>
  `!e. (e = e2 \/ e = e3) ==> post_value_type cenv e = expr_type e` by
    metis_tac[loweringPostsTheory.post_value_type_word] >>
  `?tvt. evaluate_type (get_tenv cx) v5 = SOME tvt` by
    (qpat_assum `expr_body_pre _ _ _ (IfExp _ _ _ _) _`
       (mp_tac o MATCH_MP exprSimHypsTheory.expr_body_pre_type_evaluates) >>
     simp[optionTheory.IS_SOME_EXISTS, vyperASTTheory.expr_type_def]) >>
  irule compile_ifexp_word_vv_sim_mem >> metis_tac[]
QED
Finalise body_ifexp_widened_call_arm_mem
