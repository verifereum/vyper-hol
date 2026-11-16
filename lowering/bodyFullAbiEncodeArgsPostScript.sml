Theory bodyFullAbiEncodeArgsPost
Ancestors
  abiEncodeArgsSim loweringPosts

Theorem abi_encode_args_post_cons_uncaptured_eq:
  expr_post (H1:(bool # bytes32 # type_value) list # num list) ctx func ce cx e es sa sm s0 es1 v op t /\
  expr_val_rel cx (lowered_value_type ce e) v op t /\
  expr_val_at ce cx (lowered_value_type ce e) sa sm es1 v op t /\
  abi_args_post (H:(bool # bytes32 # type_value) list # num list) ctx func ce cx es1 sm sb t es' args ops vs u /\
  stmt_state_rel (H0:(bool # bytes32 # type_value) list # num list) ctx func ce cx es s0 /\ local_ptrs_reserved ce sa /\
  local_ptrs_reserved ce sm /\ expr_sim_inv ce cx env es1 /\
  MAP FDOM es.scopes = MAP FDOM es1.scopes /\
  MAP FDOM es'.scopes = MAP FDOM es1.scopes /\
  (~is_word_type (lowered_value_type ce e) ==> es'.scopes = es1.scopes) /\
  sa.cs_next_var <= sm.cs_next_var /\ sa.cs_next_id <= sm.cs_next_id /\
  sm.cs_next_id <= sb.cs_next_id /\
  (!x. op = Var x ==> not_fresh_at sm x) /\ eval_operand op t = eval_operand op u ==>
  abi_args_post H ctx func ce cx es sa sb s0 es' (e::args) (op::ops) (v::vs) u
Proof
  strip_tac >>
  `wb_frame ce es1 es' sm t u` by metis_tac[abi_args_post_def] >>
  `stmt_state_rel H1 ctx func ce cx es1 t` by metis_tac[expr_post_def] >>
  `stmt_state_rel H ctx func ce cx es' u` by metis_tac[abi_args_post_def] >>
  `expr_val_at ce cx (lowered_value_type ce e) sa sb es' v op u` by
    (irule abi_args_location_end_mono >>
     qexists `sm` >> simp[] >> irule abi_args_location_kept_eq >>
     metis_tac[]) >>
  `expr_val_rel cx (lowered_value_type ce e) v op u` by
    (Cases_on `is_word_type (lowered_value_type ce e)`
     >- (qpat_x_assum `expr_val_rel _ _ _ _ t` mp_tac >>
         simp[expr_val_rel_def] >> strip_tac >> qexists `w` >> simp[]) >>
     `es'.scopes = es1.scopes` by simp[] >>
     `sm.cs_next_id <= sm.cs_next_id` by simp[] >>
     irule abi_args_value_kept_eq >> metis_tac[]) >>
  irule abi_args_post_cons_frame >> metis_tac[]
QED
