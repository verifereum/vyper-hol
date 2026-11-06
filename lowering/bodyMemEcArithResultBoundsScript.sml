(* A fixed two-word EC result has its entire type below the frontier. *)
Theory bodyMemEcArithResultBounds
Ancestors
  bodyMemEcArithOperands bodyMemoryDefs exprSimMemDefs loweringPosts
  exprLoweringProps venomMemDefs valueEncoding vyperValue vyperInterpreter

Theorem ec_result_vv_store_bound:
  vv_post ctx func cenv cx e es sa sb s0 es' (Value v)
    (LocatedValue (expr_type e) p) t /\
  expr_type e = ArrayT (BaseT (UintT 256)) (Fixed 2) /\
  lowered_value_type cenv e = expr_type e ==>
  vv_store_bound cx (expr_type e) (lowered_value_type cenv e) es'
    (Value v) (LocatedValue (expr_type e) p) t
Proof
  strip_tac >> Cases_on `p.ptr_location = LocMemory`
  >- (drule vv_store_bound_capacity >> simp[] >>
      disch_then irule >>
      simp[evaluate_type_def, type_slot_size_def, wordsTheory.dimword_def] >>
      qpat_assum `vv_post _ _ _ _ _ _ _ _ _ _ _ _ _`
        (strip_assume_tac o REWRITE_RULE [vv_post_def]) >>
      gvs[vv_at_def, vyperStateTheory.read_result_def, vyperStateTheory.return_def,
          evaluate_type_def, type_slot_size_def, wordsTheory.dimword_def,
          ec_point_footprint, type_memory_size_def]
      >- (fs[stmt_state_rel_def, alloca_inv_def, alloca_next_valid_def] >>
          `b + sz <= t.vs_alloca_next` by metis_tac[] >> decide_tac) >>
      drule_all body_local_region_frontier >> decide_tac) >>
  irule vv_store_bound_nonmem >> simp[]
QED
