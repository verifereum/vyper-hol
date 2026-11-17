Theory bodyFullBopBytestringPost
Ancestors bodyMemBopHeldPost loweringPosts

Theorem bop_bytestring_frames_post:
  wb_frame cenv es es1 sa s0 t /\
  (~expr_has_effect e1 ==> pure_frame cenv func es sa s0 t) /\
  wb_frame cenv es1 ee s1 t u /\
  (~expr_has_effect e2 ==> pure_frame cenv func es1 s1 t u) /\
  stmt_state_rel H ctx func cenv cx ee ss /\
  storage_well_formed_on cx ee (FST H) /\
  eval_operand op ss = SOME (bool_to_word b) /\
  (!z. not_fresh_at s2 z ==> lookup_var z ss = lookup_var z u) /\
  ss.vs_memory = u.vs_memory /\ ss.vs_allocas = u.vs_allocas /\
  local_ptrs_reserved cenv sa /\ stmt_state_rel H ctx func cenv cx es s0 /\
  MAP FDOM es.scopes = MAP FDOM es1.scopes /\
  sa.cs_next_var <= s1.cs_next_var /\ s1.cs_next_var <= s2.cs_next_var /\
  sa.cs_next_id <= s1.cs_next_id /\ is_bytestring_type (expr_type e1) /\
  (bop = Eq \/ bop = NotEq) ==>
  expr_post H ctx func cenv cx (Builtin (BaseT BoolT) (Bop bop) [e1;e2])
    es sa sb s0 ee (BoolV b) op ss
Proof
  strip_tac >> irule held_digest_compare_post >> simp[] >>
  qexistsl_tac [`es1`, `s1`, `s2`, `t`, `u`] >>
  gvs[wb_frame_def] >> conj_tac >> first_assum ACCEPT_TAC
QED
