(* Captured slice payloads survive both subsequent operands. *)
Theory exprSimSliceOrdinaryFrame
Ancestors
  exprSimSliceMemory exprSimWordArgs stmtSimLogArgs loweringPosts
  words list

Theorem slice_dynamic_payload_two_operands:
  expr_sim_inv cenv cx env es /\ expr_sim_inv cenv cx env' es1 /\
  stmt_state_rel ctx func cenv cx es s /\
  expr_val_at cenv cx (BaseT bt) sa sb es v src s /\
  evaluate_type (get_tenv cx) (BaseT bt) = SOME vt /\
  ~is_word_type (BaseT bt) /\ eval_operand src s = SOME p /\
  32 + LENGTH bs <= val_footprint vt v /\
  mem_bytes_at (w2n p + 32) (LENGTH bs) s.vs_memory = bs /\
  local_ptrs_reserved cenv sb /\ sb.cs_next_id <= sc.cs_next_id /\
  MAP FDOM es.scopes = MAP FDOM es1.scopes /\
  (!z. src = Var z ==> not_fresh_at sb z) /\ (!l. src <> Label l) /\
  expr_post ctx func cenv cx start es sb sc s es1 v1 op1 t /\
  expr_post ctx func cenv cx len es1 sc sd t es2 v2 op2 u ==>
  expr_val_at cenv cx (BaseT bt) sa sc es1 v src t /\
  mem_bytes_at (w2n p + 32) (LENGTH bs) u.vs_memory = bs
Proof
  strip_tac >>
  `wb_frame cenv es sb s t` by
    (irule expr_post_frame >> goal_assum (drule_at Any)) >>
  `expr_val_at cenv cx (BaseT bt) sa sc es1 v src t` by
    (drule_all log_frame_placement >> simp[]) >>
  `eval_operand src t = SOME p` by
    (drule_all log_frame_operand >> simp[]) >>
  `mem_bytes_at (w2n p + 32) (LENGTH bs) t.vs_memory = bs` by
    (drule_all slice_payload_after_operand >> simp[]) >>
  simp[] >> drule_all slice_payload_after_operand >> simp[]
QED

Theorem slice_captured_operand_two_posts:
  expr_post ctx func cenv cx e1 es sb sc s es1 v1 op1 t /\
  expr_post ctx func cenv cx e2 es1 sc sd t es2 v2 op2 u /\
  (!z. op = Var z ==> not_fresh_at sb z /\ not_fresh_at sc z) /\
  (!l. op <> Label l) /\ eval_operand op s = SOME w ==>
  eval_operand op u = SOME w
Proof
  strip_tac >>
  `wb_frame cenv es sb s t /\ wb_frame cenv es1 sc t u` by
    metis_tac[expr_post_frame] >>
  `eval_operand op t = SOME w` by
    (irule log_frame_operand >> simp[] >> qexistsl_tac [`cenv`, `es`, `s`, `sb`] >> simp[]) >>
  irule log_frame_operand >> simp[] >> qexistsl_tac [`cenv`, `es1`, `t`, `sc`] >> simp[]
QED

Theorem slice_fixed_payload_two_operands:
  stmt_state_rel ctx func cenv cx es s /\
  local_ptrs_reserved cenv sb /\
  MAP FDOM es.scopes = MAP FDOM es1.scopes /\
  FLOOKUP s.vs_allocas aid = SOME (b,32) /\
  aid < sb.cs_next_id /\ aid < sc.cs_next_id /\ LENGTH bs <= 32 /\
  (!name off sz. local_region cenv es.scopes s name off sz ==>
                 b + 32 <= off \/ off + sz <= b) /\
  mem_bytes_at b (LENGTH bs) s.vs_memory = bs /\
  expr_post ctx func cenv cx start es sb sc s es1 v1 op1 t /\
  expr_post ctx func cenv cx len es1 sc sd t es2 v2 op2 u ==>
  mem_bytes_at b (LENGTH bs) u.vs_memory = bs
Proof
  strip_tac >>
  `wb_frame cenv es sb s t /\ wb_frame cenv es1 sc t u` by
    metis_tac[expr_post_frame] >>
  `FLOOKUP t.vs_allocas aid = SOME (b,32)` by fs[expr_post_def] >>
  `!name off sz. local_region cenv es1.scopes t name off sz ==>
                 b + 32 <= off \/ off + sz <= b` by
    (rpt strip_tac >>
     `local_region cenv es.scopes s name off sz` by
       (drule_all log_frame_local_region >> metis_tac[]) >> metis_tac[]) >>
  `mem_bytes_at (b+0) (LENGTH bs) t.vs_memory =
   mem_bytes_at (b+0) (LENGTH bs) s.vs_memory` by
    (irule slice_allocated_window_preserved >>
     qexistsl_tac [`aid`, `cenv`, `es`, `sb`, `32`] >> simp[] >> metis_tac[arithmeticTheory.ADD_COMM]) >>
  `mem_bytes_at (b+0) (LENGTH bs) u.vs_memory =
   mem_bytes_at (b+0) (LENGTH bs) t.vs_memory` by
    (irule slice_allocated_window_preserved >>
     qexistsl_tac [`aid`, `cenv`, `es1`, `sc`, `32`] >> simp[] >> metis_tac[arithmeticTheory.ADD_COMM]) >>
  gvs[]
QED

(* Fix the post chain before choosing the operand to be framed. *)
Theorem slice_two_posts_operands:
  expr_post ctx func cenv cx e1 es sb sc s es1 v1 op1 t /\
  expr_post ctx func cenv cx e2 es1 sc sd t es2 v2 op2 u ==>
  !op w. (!z. op = Var z ==> not_fresh_at sb z /\ not_fresh_at sc z) /\
    (!l. op <> Label l) /\ eval_operand op s = SOME w ==>
    eval_operand op u = SOME w
Proof
  metis_tac[slice_captured_operand_two_posts]
QED

Theorem slice_post_operands:
  expr_post ctx func cenv cx e es sb sc s es1 v op1 t ==>
  !op w. (!z. op = Var z ==> not_fresh_at sb z) /\
    (!l. op <> Label l) /\ eval_operand op s = SOME w ==>
    eval_operand op t = SOME w
Proof
  strip_tac >> drule expr_post_frame >> strip_tac >>
  rpt strip_tac >> irule log_frame_operand >> simp[] >>
  qexistsl_tac [`cenv`, `es`, `s`, `sb`] >> simp[]
QED
