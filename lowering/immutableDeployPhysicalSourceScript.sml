(* Physical source typing for constructor immutable assignment. *)
Theory immutableDeployPhysicalSource
Ancestors
  exprSimHyps memoryLocalRhsProps valueTypingMemoryProps loweringPosts
  exprSimHypsDefs vyperTypeInvariants exprLowering vyperInterpreter
Libs monadsyntax

Theorem immutable_rhs_physical_typed:
  expr_body_pre ce cx env e es /\
  (do pv <- eval_expr cx e; read_result cx pv od) es = (INL v,ee) ==>
  ?stv. evaluate_type (get_tenv cx) (lowered_value_type ce e) = SOME stv /\
    value_has_type stv v /\ val_wf stv v /\
    type_memory_bytes ce (lowered_value_type ce e) = type_memory_size stv
Proof
  strip_tac >>
  `expr_sim_inv ce cx env es` by fs[expr_body_pre_def] >>
  Cases_on `?ann fid args drv. e = Call ann (IntCall fid) args drv`
  >- (qpat_x_assum `?ann fid args drv. _` strip_assume_tac >> gvs[] >>
      drule_all ifexp_intcall_read_physical_typed >> strip_tac >>
      qexists_tac `stv` >> simp[value_has_type_memory_wf] >>
      metis_tac[expr_sim_inv_memory_size]) >>
  `value_runtime_typed env (lowered_value_type ce e) v` by
    (irule memory_rhs_read_lowered_typed_unwidened >>
     conj_tac >- metis_tac[] >>
     qexistsl_tac [`cx`,`es`,`ee`] >> simp[]) >>
  drule_all memory_rhs_runtime_layout >> strip_tac >>
  goal_assum (drule_at Any) >> simp[value_has_type_memory_wf]
QED
