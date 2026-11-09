(* Physical layout and source capacity for widened local copies. *)
Theory widenedLocalRuntimeMem
Ancestors
  exprSimMemDefs exprSimHyps exprSimHypsDefs memoryLocalRhsProps bodySim
  loweringPosts valueEncoding vyperValue valueTypingMemoryProps
  localCopyDestinationMem
Libs monadsyntax

Theorem widened_local_source_memory[local]:
  vv_post ctx fn ce cx e es sa sb s0 ee raw (LocatedValue vt p) s /\
  vv_store_bound cx (expr_type e) (lowered_value_type ce e)
    ee raw (LocatedValue vt p) s /\
  p.ptr_location = LocMemory /\ read_result cx raw ee = (INL v,ee) /\
  post_value_type ce e = lowered_value_type ce e /\
  evaluate_type (get_tenv cx) (lowered_value_type ce e) = SOME stv ==>
  val_wf stv v /\
  ?w. eval_operand p.ptr_operand s = SOME w /\
      val_in_memory stv v (w2n w) s.vs_memory /\
      (type_memory_size stv = 0 \/
       w2n w + type_memory_size stv <= s.vs_alloca_next)
Proof
  strip_tac >>
  `val_wf stv v` by gvs[vv_post_def, vv_at_def] >>
  qpat_x_assum `vv_post _ _ _ _ _ _ _ _ _ _ _ _ _` mp_tac >>
  simp[vv_post_def, vv_holds_def] >> rpt strip_tac >> gvs[] >>
  gvs[vv_store_bound_def]
QED

Theorem widened_local_source_layout:
  expr_body_pre ce cx env e es /\
  (do r <- eval_expr cx e; read_result cx r od) es = (INL v,ee) /\
  vv_post ctx fn ce cx e es sa sb s0 ee raw (LocatedValue vt p) s /\
  vv_store_bound cx (expr_type e) (lowered_value_type ce e)
    ee raw (LocatedValue vt p) s /\
  p.ptr_location = LocMemory /\ read_result cx raw ee = (INL v,ee) /\
  post_value_type ce e = lowered_value_type ce e ==>
  ?stv w.
    evaluate_type (get_tenv cx) (lowered_value_type ce e) = SOME stv /\
    type_memory_bytes ce (lowered_value_type ce e) = type_memory_size stv /\
    value_has_type stv v /\ val_wf stv v /\
    eval_operand p.ptr_operand s = SOME w /\
    val_in_memory stv v (w2n w) s.vs_memory /\
    (type_memory_size stv = 0 \/
     w2n w + type_memory_size stv <= s.vs_alloca_next)
Proof
  strip_tac >>
  `value_runtime_typed env (post_value_type ce e) v` by
    (drule_all memory_rhs_read_post_typed >> simp[]) >>
  `expr_sim_inv ce cx env es` by fs[expr_body_pre_def] >>
  drule_all memory_rhs_runtime_layout >> strip_tac >>
  metis_tac[widened_local_source_memory]
QED

Theorem widened_local_runtime_types:
  expr_body_pre ce cx env e es /\
  type_widens_to env.type_defs (expr_type e) dty /\
  (do r <- eval_expr cx e; read_result cx r od) es = (INL v,ee) ==>
  ?stv dtv.
    evaluate_type (get_tenv cx) (post_value_type ce e) = SOME stv /\
    evaluate_type (get_tenv cx) dty = SOME dtv /\
    value_has_type stv v /\ value_has_type dtv v /\
    val_wf stv v /\ val_wf dtv v /\
    type_memory_bytes ce (post_value_type ce e) = type_memory_size stv /\
    type_memory_bytes ce dty = type_memory_size dtv
Proof
  strip_tac >>
  `value_runtime_typed env (post_value_type ce e) v` by
    (drule_all memory_rhs_read_post_typed >> simp[]) >>
  `value_runtime_typed env dty v` by
    (drule_all memory_rhs_read_destination_typed >> simp[]) >>
  `expr_sim_inv ce cx env es` by fs[expr_body_pre_def] >>
  `?stv. evaluate_type (get_tenv cx) (post_value_type ce e) = SOME stv /\
     value_has_type stv v /\
     type_memory_bytes ce (post_value_type ce e) = type_memory_size stv` by
    metis_tac[memory_rhs_runtime_layout] >>
  `?dtv. evaluate_type (get_tenv cx) dty = SOME dtv /\
     value_has_type dtv v /\ type_memory_bytes ce dty = type_memory_size dtv` by
    metis_tac[memory_rhs_runtime_layout] >>
  metis_tac[value_has_type_memory_wf]
QED
