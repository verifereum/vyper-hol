(* Seam 2 joint induction, a family leaf of the pure step: ternaries. *)
Theory bodyIntCallFamPureIfExp
Ancestors
  bodyIntCallJointContract exprSimIfExp bodyIntCallJointPureSuffix
  loweringPosts venomState venomExecSemantics finite_map context exprLowering vyperAST

(* The layout-copy alternative only arises for bytestrings. *)
Theorem ifexp_arm_unwrap_nonbytes:
  (at = rt \/
   is_bytestring_type rt /\ is_bytestring_type at /\ arg_type_fits at rt \/
   same_memory_layout ce at rt) /\ ~is_bytestring_type rt ==>
  compile_ifexp_arm ce rt at vv = unwrap_value ce vv
Proof
  strip_tac >> irule compile_ifexp_arm_unwrap >>
  Cases_on `is_word_type rt` >> simp[] >>
  metis_tac[ifexp_copy_types]
QED

(* Keep an arbitrary property of the selected pointer word at the explicit
   ASSIGN/JMP endpoint used by the ordinary IfExp post. *)
Theorem ifexp_finish_slot:
  post_value_type ce e = expr_type e /\
  expr_post ctx func ce cx c es sa s1 s0 es1 v1 cop tt /\
  expr_post ctx func ce cx e es1 sc sd (jump_to lbl tt) ee v op u /\
  read_result cx tv ee = (INL v,ee) /\ expr_type e = t /\
  eval_operand op u = SOME w /\ slot_ok w /\
  (!x. not_fresh_at sa x ==> x <> rv) /\
  local_ptrs_reserved ce sa /\ stmt_state_rel ctx func ce cx es s0 /\
  MAP FDOM es.scopes = MAP FDOM es1.scopes /\
  sa.cs_next_var <= s1.cs_next_var /\ s1.cs_next_var <= sc.cs_next_var /\
  sa.cs_next_id <= s1.cs_next_id /\ s1.cs_next_id <= sc.cs_next_id /\
  sd.cs_next_id <= sb.cs_next_id /\ sb.cs_current_bb = xl /\ sb.cs_current_insts = [] /\
  emit_inst ASSIGN [op] [rv] sd = ((),sy) /\
  emit_inst JMP [Label xl] [] sy = ((),sz) /\
  fn_has_code sd sy func /\ fn_has_code sy sz func /\
  ~u.vs_halted /\ u.vs_current_bb = sd.cs_current_bb /\
  u.vs_inst_idx = LENGTH sd.cs_current_insts ==>
  ?q. gas_path ctx func u 0 (OK q) /\
    vv_post ctx func ce cx (IfExp t c a b) es sa sb s0 ee tv
      (if is_word_type t then StackValue t (Var rv)
       else LocatedValue t (mk_ptr (Var rv) LocMemory)) q /\
    eval_operand (Var rv) q = SOME w /\ slot_ok w /\
    q.vs_current_bb = sb.cs_current_bb /\ q.vs_inst_idx = LENGTH sb.cs_current_insts
Proof
  strip_tac >>
  qexists `jump_to xl (update_var rv w u with vs_inst_idx := LENGTH sy.cs_current_insts)` >>
  conj_tac >- (irule ifexp_root_suffix_path >> metis_tac[]) >>
  conj_tac >- (irule ifexp_root_finish_post >> metis_tac[]) >>
  simp[eval_operand_def, jump_to_def, update_var_def, lookup_var_def,
       FLOOKUP_UPDATE]
QED

Theorem ifexp_arm_finish_slot:
  post_value_type ce e = expr_type e /\
  expr_post ctx func ce cx c es sa s1 s0 es1 v1 cop tt /\
  expr_type e = t /\ (!x. not_fresh_at sa x ==> x <> rv) /\
  local_ptrs_reserved ce sa /\ stmt_state_rel ctx func ce cx es s0 /\
  MAP FDOM es.scopes = MAP FDOM es1.scopes /\
  sa.cs_next_var <= s1.cs_next_var /\ s1.cs_next_var <= sc.cs_next_var /\
  sa.cs_next_id <= s1.cs_next_id /\ s1.cs_next_id <= sc.cs_next_id /\
  sd.cs_next_id <= sb.cs_next_id /\ sb.cs_current_bb = xl /\ sb.cs_current_insts = [] /\
  emit_inst ASSIGN [op] [rv] sd = ((),sy) /\
  emit_inst JMP [Label xl] [] sy = ((),sz) /\
  fn_has_code sd sy func /\ fn_has_code sy sz func /\
  gas_outcome F tops (ctx,func) source (es1,jump_to lbl tt)
    (\res ee u. ?tv v w. res = INL tv /\ read_result cx tv ee = (INL v,ee) /\
      expr_post ctx func ce cx e es1 sc sd (jump_to lbl tt) ee v op u /\
      eval_operand op u = SOME w /\ slot_ok w /\
      u.vs_current_bb = sd.cs_current_bb /\ u.vs_inst_idx = LENGTH sd.cs_current_insts) R ==>
  gas_outcome F tops (ctx,func) source (es1,jump_to lbl tt)
    (\res ee u. ?tv w. res = INL tv /\
      vv_post ctx func ce cx (IfExp t c a b) es sa sb s0 ee tv
        (if is_word_type t then StackValue t (Var rv)
         else LocatedValue t (mk_ptr (Var rv) LocMemory)) u /\
      eval_operand (Var rv) u = SOME w /\ slot_ok w /\
      u.vs_current_bb = sb.cs_current_bb /\ u.vs_inst_idx = LENGTH sb.cs_current_insts) R
Proof
  strip_tac >> drule ifexp_root_outcome_suffix >> disch_then irule >>
  rpt strip_tac >>
  qpat_x_assum `gas_outcome _ _ _ _ _ _ _` kall_tac >>
  qpat_x_assum `(\res ee u. _) res ee u` (strip_assume_tac o BETA_RULE) >>
  BETA_TAC >>
  drule_all ifexp_finish_slot >>
  disch_then (qspecl_then [`b`, `a`] strip_assume_tac) >>
  qexists `q` >> simp[] >> metis_tac[]
QED

Theorem intcall_ifexp_step:
  (!e'. expr_size e' < expr_size e ==>
        intcall_expr_producer fp e' /\ intcall_forced_producer fp e' /\
        intcall_map_producer fp e') /\
  (?ty c e1 e2. e = IfExp ty c e1 e2) ==>
  intcall_expr_producer fp e /\ intcall_map_producer fp e
Proof
  cheat
QED
