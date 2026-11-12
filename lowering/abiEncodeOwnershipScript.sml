(* Actual source ownership at a fresh staging frontier. *)
Theory abiEncodeOwnership
Ancestors
  loweringStateRelDefs
  abiEncodeInputSupplier exprSimDefs exprSimProps loweringPosts exprLoweringProps compileEnv venomMemDefs
  abiEncodeArgsSim finite_map words arithmetic list rich_list

Theorem abi_encode_local_region_frontier:
  stmt_state_rel ctx func cenv cx es s /\
  local_region cenv es.scopes s n b sz ==>
  b + sz <= s.vs_alloca_next
Proof
  simp_tac bool_ss [stmt_state_rel_def, state_rel_def,
    local_ptrs_rel_def, local_region_def] >>
  rpt strip_tac >> res_tac >> gvs[]
QED

Theorem abi_encode_owned_footprint_frontier:
  stmt_state_rel ctx func cenv cx es s /\
  expr_val_at cenv cx ty sa st es v op s /\
  evaluate_type (get_tenv cx) ty = SOME tv /\ ~is_word_type ty /\
  eval_operand op s = SOME w ==>
  val_footprint tv v = 0 \/
  w2n w + val_footprint tv v <= s.vs_alloca_next
Proof
  strip_tac >>
  qpat_x_assum `expr_val_at _ _ _ _ _ _ _ _ _` mp_tac >>
  simp_tac bool_ss [expr_val_at_def] >>
  disch_then drule_all >> strip_tac >> gvs[]
  >- (qpat_x_assum `stmt_state_rel _ _ _ _ _ _` mp_tac >>
      simp_tac bool_ss [stmt_state_rel_def, alloca_inv_def, alloca_next_valid_def] >>
      rpt strip_tac >> res_tac >> decide_tac)
  >- (drule_all abi_encode_local_region_frontier >> decide_tac)
QED

Theorem abi_encode_fresh_footprint_separation:
  stmt_state_rel ctx func cenv cx es s /\
  expr_val_at cenv cx ty sa st es v op s /\
  evaluate_type (get_tenv cx) ty = SOME tv /\ ~is_word_type ty /\
  eval_operand op s = SOME w /\ s.vs_alloca_next <= lo ==>
  val_footprint tv v = 0 \/
  w2n w + val_footprint tv v <= lo \/ hi <= w2n w
Proof
  strip_tac >> drule_all abi_encode_owned_footprint_frontier >> decide_tac
QED

(* An empty footprint alone does not imply the ordered-interval condition
   required by the current staging input interface. *)
Theorem abi_encode_empty_ordered_separation_obstacle:
  ~(16 + 0 <= 0 \/ 32 <= 16)
Proof
  EVAL_TAC
QED

Theorem abi_encode_argument_footprint_frontier:
  abi_args_post ctx func ce cx es sa st s0 es' args ops vs s /\
  i < LENGTH args /\
  evaluate_type (get_tenv cx) (lowered_value_type ce (EL i args)) = SOME tv /\
  ~is_word_type (lowered_value_type ce (EL i args)) /\
  eval_operand (EL i ops) s = SOME w ==>
  val_footprint tv (EL i vs) = 0 \/
  w2n w + val_footprint tv (EL i vs) <= s.vs_alloca_next
Proof
  strip_tac >>
  `LENGTH args = LENGTH vs /\ LENGTH ops = LENGTH args` by
    metis_tac[abi_args_post_lengths] >>
  qpat_x_assum `abi_args_post _ _ _ _ _ _ _ _ _ _ _ _ _` mp_tac >>
  simp_tac bool_ss [abi_args_post_def, LIST_REL_EL_EQN] >> strip_tac >>
  first_x_assum (qspec_then `i` mp_tac) >> simp[EL_ZIP] >> strip_tac >>
  irule abi_encode_owned_footprint_frontier >> metis_tac[]
QED
