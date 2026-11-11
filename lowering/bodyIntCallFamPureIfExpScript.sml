(* Seam 2 joint induction, a family leaf of the pure step: ternaries. *)
Theory bodyIntCallFamPureIfExp
Ancestors
  bodyIntCallJointContract exprSimIfExp bodyIntCallJointPureSuffix
  loweringPosts venomState venomExecSemantics finite_map context exprLowering vyperAST
  exprSimAggregateChildren exprBopSimProps arithmetic exprSimProps
  exprSimWordArgs exprSimSubscriptArrayCompose exprSimAggregateSource
  stmtSimAugAssignPlaceMemory gasSummary gasContext vyperState exprSimSubscriptMap
  exprSimDefs gasOutcome exprSimOperators exprLoweringProps bodyIntCallJointStmtJump
  stmtSimForLoop

(* Assemble the ordinary forced post at the chosen forcing endpoint. *)
Theorem vv_post_forcing_frames:
  post_value_type ce e = expr_type e /\
  eval_expr cx e es = (INL raw,ee) /\
  read_result cx raw ee = (INL v,ee) /\
  vv_post ctx func ce cx e es sa sm s0 ee raw vv s /\
  stmt_state_rel ctx func ce cx es s0 /\ local_ptrs_reserved ce sa /\
  MAP FDOM es.scopes = MAP FDOM ee.scopes /\
  sa.cs_next_var <= sm.cs_next_var /\ sa.cs_next_id <= sm.cs_next_id /\
  stmt_state_rel ctx func ce cx ee q /\
  expr_val_rel cx (post_value_type ce e) v op q /\
  expr_val_at ce cx (post_value_type ce e) sa sb ee v op q /\
  (!x w. not_fresh_at sm x /\ lookup_var x s = SOME w ==>
         lookup_var x q = SOME w) /\
  (!aid b. FLOOKUP s.vs_allocas aid = SOME b ==>
           FLOOKUP q.vs_allocas aid = SOME b) /\
  locals_kept ce ee s q /\
  (!aid off sz.
     FLOOKUP s.vs_allocas aid = SOME (off,sz) /\ aid < sm.cs_next_id /\
     (!n b sz'. local_region ce ee.scopes s n b sz' ==>
                off + sz <= b \/ b + sz' <= off) ==>
     mem_bytes_at off sz q.vs_memory = mem_bytes_at off sz s.vs_memory) ==>
  expr_post ctx func ce cx e es sa sb s0 ee v op q
Proof
  strip_tac >>
  `!n b sz. local_region ce ee.scopes s n b sz ==>
            local_region ce es.scopes s0 n b sz` by
    (rpt strip_tac >> irule vv_post_local_region_backward >> metis_tac[]) >>
  fs[vv_post_def] >>
  simp[expr_post_def] >>
  rpt conj_tac
  >- metis_tac[freshWritesTheory.not_fresh_at_mono]
  >- (rpt strip_tac >>
      `mem_bytes_at off sz q.vs_memory = mem_bytes_at off sz s.vs_memory` by
        (first_x_assum irule >> metis_tac[LESS_LESS_EQ_TRANS]) >>
      metis_tac[]) >>
  irule locals_kept_trans >> metis_tac[]
QED

(* Protected forcing and its ordinary post share a single endpoint. *)
Theorem vv_post_protected_unwrap:
  post_value_type ce e = expr_type e /\
  eval_expr cx e es = (INL raw,ee) /\
  read_result cx raw ee = (INL v,ee) /\
  vv_post ctx func ce cx e es sa sm s0 ee raw vv s /\
  stmt_state_rel ctx func ce cx es s0 /\ local_ptrs_reserved ce sa /\
  MAP FDOM es.scopes = MAP FDOM ee.scopes /\
  sa.cs_next_var <= sm.cs_next_var /\ sa.cs_next_id <= sm.cs_next_id /\
  unwrap_value ce vv sm = (op,sb) /\
  evaluate_type (get_tenv cx) (post_value_type ce e) = SOME tv /\
  type_memory_bytes ce (post_value_type ce e) = type_memory_size tv /\
  type_memory_size tv < 2**64 /\
  fn_has_code sm sb func /\ fn_inst_ids_distinct func /\
  local_ptrs_reserved ce sm /\ allocas_above lo s /\
  (!x. vv_operand vv = Var x ==> not_fresh_at sm x) /\
  (!q x. reserved q /\ q = Var x ==> not_fresh_at sm x) /\
  (!p k. P p k ==> p+k <= lo) /\
  (post_value_type ce e <> NoneT /\ ~is_word_type (post_value_type ce e) /\
   ~is_bytestring_type (post_value_type ce e) /\
   (case vv of StackValue _ _ => T | LocatedValue _ p => p.ptr_location = LocMemory) ==>
   ?w a k. eval_operand (vv_operand vv) s = SOME w /\
     a <= w2n w /\ w2n w + type_memory_size tv <= a+k /\ a+k < dimword (:256) /\
     (lo <= a \/ ?b z. staged b z /\ b <= a /\ a+k <= b+z)) /\
  ~s.vs_halted /\ s.vs_current_bb = sm.cs_current_bb /\
  s.vs_inst_idx = LENGTH sm.cs_current_insts ==>
  ?q. gas_marked_path F ctx func s 0 (OK q) /\
    expr_post ctx func ce cx e es sa sb s0 ee v op q /\
    allocas_above lo q /\ s.vs_alloca_next <= q.vs_alloca_next /\
    (!p k. P p k ==> mem_bytes_at p k q.vs_memory = mem_bytes_at p k s.vs_memory) /\
    (!r. reserved r ==> eval_operand r q = eval_operand r s) /\
    (post_value_type ce e <> NoneT /\ ~is_word_type (post_value_type ce e) /\
     ~is_bytestring_type (post_value_type ce e) ==>
     ?w a k. eval_operand op q = SOME w /\ a <= w2n w /\
       w2n w + type_memory_size tv <= a+k /\ a+k < dimword (:256) /\
       (lo <= a \/ ?b z. staged b z /\ b <= a /\ a+k <= b+z)) /\
    ~q.vs_halted /\ q.vs_current_bb = sb.cs_current_bb /\
    q.vs_inst_idx = LENGTH sb.cs_current_insts
Proof
  strip_tac >>
  `vv_holds ce cx (post_value_type ce e) raw vv ee s /\
   stmt_state_rel ctx func ce cx ee s` by fs[vv_post_def] >>
  mp_tac (Q.INST [
    `sa` |-> `sm`, `ty` |-> `post_value_type ce e`,
    `r` |-> `raw`, `es` |-> `ee`,
    `Win` |-> `\p k. ?aid. FLOOKUP s.vs_allocas aid = SOME (p,k) /\
      aid < sm.cs_next_id /\
      (!n b z. local_region ce ee.scopes s n b z ==> p+k <= b \/ b+z <= p)`,
    `scopes` |-> `ee.scopes`]
    bodyIntCallWindowForcingTheory.protected_value_window_forcing) >>
  impl_tac >- (simp[] >> rpt strip_tac >> qexistsl [`aid`,`p`,`k`] >> simp[]) >>
  strip_tac >> qexists `u` >> simp[] >>
  irule vv_post_forcing_frames >>
  simp[] >> reverse conj_tac
  >- (qexistsl [`s`,`sm`,`vv`] >> simp[] >>
      rpt strip_tac >> first_x_assum irule >> metis_tac[]) >>
  qpat_assum `post_value_type ce e = _` (fn th => rewrite_tac[GSYM th]) >>
  first_x_assum irule >> fs[vv_post_def]
QED

(* Source observations select the raw execution; forcing uses its exact endpoint. *)
Theorem ifexp_protected_marked_unwrap:
  post_value_type ce e = expr_type e /\
  gas_marked_exec F (ctx,func) (eval_expr cx e) (es,s0) marks (INL raw) ee (OK s) /\
  vv_post ctx func ce cx e es sa sm s0 (ee with gas_obs := []) raw vv s /\
  gas_admissible (bind (eval_expr cx e) (conditional_result cx)) expr_vv_res_ok es /\
  stmt_state_rel ctx func ce cx es s0 /\ local_ptrs_reserved ce sa /\
  sa.cs_next_var <= sm.cs_next_var /\ sa.cs_next_id <= sm.cs_next_id /\
  unwrap_value ce vv sm = (op,sb) /\
  evaluate_type (get_tenv cx) (post_value_type ce e) = SOME tv /\
  type_memory_bytes ce (post_value_type ce e) = type_memory_size tv /\
  type_memory_size tv < 2**64 /\
  fn_has_code sm sb func /\ fn_inst_ids_distinct func /\
  local_ptrs_reserved ce sm /\ allocas_above lo s /\
  (!x. vv_operand vv = Var x ==> not_fresh_at sm x) /\
  (!q x. reserved q /\ q = Var x ==> not_fresh_at sm x) /\
  (!p k. P p k ==> p+k <= lo) /\
  (post_value_type ce e <> NoneT /\ ~is_word_type (post_value_type ce e) /\
   ~is_bytestring_type (post_value_type ce e) /\
   (case vv of StackValue _ _ => T | LocatedValue _ p => p.ptr_location = LocMemory) ==>
   ?w a k. eval_operand (vv_operand vv) s = SOME w /\
     a <= w2n w /\ w2n w + type_memory_size tv <= a+k /\ a+k < dimword (:256) /\
     (lo <= a \/ ?b z. staged b z /\ b <= a /\ a+k <= b+z)) /\
  s.vs_current_bb = sm.cs_current_bb /\
  s.vs_inst_idx = LENGTH sm.cs_current_insts ==>
  ?tr v q. gas_marked_exec F (ctx,func) (conditional_result cx raw)
      (ee with gas_obs := [],s) [] (INL tr) (ee with gas_obs := []) (OK q) /\
    read_result cx tr (ee with gas_obs := []) = (INL v,ee with gas_obs := []) /\
    expr_post ctx func ce cx e es sa sb s0 (ee with gas_obs := []) v op q /\
    allocas_above lo q /\ s.vs_alloca_next <= q.vs_alloca_next /\
    (!p k. P p k ==> mem_bytes_at p k q.vs_memory = mem_bytes_at p k s.vs_memory) /\
    (!r. reserved r ==> eval_operand r q = eval_operand r s) /\
    (post_value_type ce e <> NoneT /\ ~is_word_type (post_value_type ce e) /\
     ~is_bytestring_type (post_value_type ce e) ==>
     ?w a k. eval_operand op q = SOME w /\ a <= w2n w /\
       w2n w + type_memory_size tv <= a+k /\ a+k < dimword (:256) /\
       (lo <= a \/ ?b z. staged b z /\ b <= a /\ a+k <= b+z)) /\
    ~q.vs_halted /\ q.vs_current_bb = sb.cs_current_bb /\
    q.vs_inst_idx = LENGTH sb.cs_current_insts
Proof
  strip_tac >>
  drule vv_post_materialises >> strip_tac >>
  drule_all aug_place_marked_bind_tail >> disch_tac >>
  `eval_expr cx e (es with gas_obs := gas_explicit marks s0.vs_gas_readings) =
     (INL raw,ee with gas_obs := [])` by
    (qpat_x_assum `gas_marked_exec _ _ _ _ _ _ _ _` mp_tac >>
     simp[gas_marked_exec_def] >> strip_tac >>
     first_x_assum (qspec_then `[]` mp_tac) >> simp[]) >>
  `~s.vs_halted` by
    (irule aug_place_marked_path_not_halted >>
     fs[gas_marked_exec_def] >> metis_tac[]) >>
  `MAP FDOM es.scopes = MAP FDOM ee.scopes` by
    (drule vyperEvalExprPreservesScopesDomTheory.eval_expr_preserves_scopes_dom >> simp[]) >>
  Cases_on `conditional_result cx raw (ee with gas_obs := [])` >>
  rename1 `conditional_result cx raw (ee with gas_obs := []) = (cr,ss)` >>
  `expr_vv_res_ok cr` by
    (qpat_x_assum `gas_admissible (conditional_result _ _) _ _` mp_tac >>
     simp[gas_admissible_def] >> metis_tac[evaluation_state_component_equality]) >>
  drule_all ifexp_arm_conditional_read >> strip_tac >> gvs[] >>
  mp_tac (Q.INST [
    `es` |-> `es with gas_obs := gas_explicit marks s0.vs_gas_readings`,
    `ee` |-> `ee with gas_obs := []`]
    vv_post_protected_unwrap) >>
  (impl_tac >- simp[vv_post_initial_gas]) >> strip_tac >>
  qexistsl [`tv'`,`v`,`q`] >> gvs[expr_post_initial_gas] >>
  simp[gas_marked_exec_def] >>
  drule ifexp_arm_conditional_gas_obs >> simp[]
QED

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

(* The selected arm's conditional-result suffix retains its authorized slot. *)
Theorem ifexp_joint_arm_marked_suffix:
  post_value_type ce e = expr_type e /\
  gas_marked_exec F (fp.jc_ctx,fp.jc_func) (eval_expr fp.jc_cx e)
    (es,s0) marks (INL raw) ee (OK s) /\
  vv_post fp.jc_ctx fp.jc_func ce fp.jc_cx e es sa sm s0
    (ee with gas_obs := []) raw vv s /\
  intcall_frame_ok fp /\ intcall_expr_res fp ce env es sa s0 /\
  intcall_expr_cont fp ce env es sa s0 (ee with gas_obs := []) sm s /\
  compile_ifexp_arm ce (expr_type e) (lowered_value_type ce e) vv sm = (op,sb) /\
  (~is_word_type (expr_type e) ==>
    lowered_value_type ce e = expr_type e \/
    is_bytestring_type (expr_type e) /\ is_bytestring_type (lowered_value_type ce e) /\
      arg_type_fits (lowered_value_type ce e) (expr_type e) \/
    same_memory_layout ce (lowered_value_type ce e) (expr_type e)) /\
  (!tv. evaluate_type (get_tenv fp.jc_cx) (expr_type e) = SOME tv /\
      ~is_word_type (expr_type e) ==>
      type_memory_bytes ce (expr_type e) = type_memory_size tv /\
      type_memory_size tv < 2 ** 64) /\
  (!gs v es2. ~is_word_type (expr_type e) /\
    bind (eval_expr fp.jc_cx e) (read_result fp.jc_cx)
      (es with gas_obs := gs) = (INL v,es2) ==>
    ?tv. evaluate_type (get_tenv fp.jc_cx) (expr_type e) = SOME tv /\ value_has_type tv v) /\
  (?tv. evaluate_type (get_tenv fp.jc_cx) (expr_type e) = SOME tv) /\
  gas_admissible (bind (eval_expr fp.jc_cx e) (conditional_result fp.jc_cx))
    expr_vv_res_ok es /\
  sa.cs_next_var <= sm.cs_next_var /\ sa.cs_next_id <= sm.cs_next_id /\
  fn_has_code sm sb fp.jc_func /\ fn_inst_ids_distinct fp.jc_func /\
  (!x. vv_operand vv = Var x ==> not_fresh_at sm x) /\
  (post_value_type ce e <> NoneT /\ ~is_word_type (post_value_type ce e) /\
   ~is_bytestring_type (post_value_type ce e) /\
   (case vv of StackValue _ _ => T | LocatedValue _ p => p.ptr_location = LocMemory) ==>
   !tv. evaluate_type (get_tenv fp.jc_cx) (post_value_type ce e) = SOME tv ==>
     ?w a k. eval_operand (vv_operand vv) s = SOME w /\ a <= w2n w /\
       w2n w + type_memory_size tv <= a+k /\ a+k < dimword (:256) /\
       (fp.jc_lo <= a \/ ?b z. fp.jc_staged b z /\ b <= a /\ a+k <= b+z)) ==>
  ?tr v q w. gas_marked_exec F (fp.jc_ctx,fp.jc_func)
      (conditional_result fp.jc_cx raw) (ee with gas_obs := [],s) []
      (INL tr) (ee with gas_obs := []) (OK q) /\
    read_result fp.jc_cx tr (ee with gas_obs := []) = (INL v,ee with gas_obs := []) /\
    expr_post fp.jc_ctx fp.jc_func ce fp.jc_cx e es sa sb s0
      (ee with gas_obs := []) v op q /\ eval_operand op q = SOME w /\
    (post_value_type ce e <> NoneT /\ ~is_word_type (post_value_type ce e) /\
     ~is_bytestring_type (post_value_type ce e) ==>
     !tv. evaluate_type (get_tenv fp.jc_cx) (post_value_type ce e) = SOME tv ==>
       ?a k. a <= w2n w /\ w2n w + type_memory_size tv <= a+k /\
         a+k < dimword (:256) /\
         (fp.jc_lo <= a \/ ?b z. fp.jc_staged b z /\ b <= a /\ a+k <= b+z)) /\
    q.vs_current_bb = sb.cs_current_bb /\ q.vs_inst_idx = LENGTH sb.cs_current_insts
Proof
  strip_tac >>
  `stmt_state_rel fp.jc_ctx fp.jc_func ce fp.jc_cx es s0 /\
   local_ptrs_reserved ce sa /\ local_ptrs_reserved ce sm /\ allocas_above fp.jc_lo s /\
   (!r x. fp.jc_reserved r /\ r = Var x ==> not_fresh_at sm x) /\
   (!p k. fp.jc_prot p k ==> p+k <= fp.jc_lo) /\
   s.vs_current_bb = sm.cs_current_bb /\ s.vs_inst_idx = LENGTH sm.cs_current_insts` by
    fs[intcall_expr_cont_def, intcall_joint_res_def, intcall_expr_res_def, intcall_frame_ok_def] >>
  Cases_on `post_value_type ce e <> NoneT /\ ~is_word_type (post_value_type ce e) /\
            ~is_bytestring_type (post_value_type ce e)`
  >- (`unwrap_value ce vv sm = (op,sb)` by
        (`compile_ifexp_arm ce (expr_type e) (lowered_value_type ce e) vv =
          unwrap_value ce vv` by
           (irule ifexp_arm_unwrap_nonbytes >> gvs[]) >> metis_tac[]) >>
      drule_at (Pat `gas_marked_exec _ _ _ _ _ _ _ _`)
        (Q.INST [`lo` |-> `fp.jc_lo`, `P` |-> `fp.jc_prot`,
                 `reserved` |-> `fp.jc_reserved`, `staged` |-> `fp.jc_staged`]
          ifexp_protected_marked_unwrap) >>
      disch_then (drule_at (Pat `vv_post _ _ _ _ _ _ _ _ _ _ _ _ _`)) >>
      disch_then (drule_at (Pat `allocas_above _ _`)) >>
      disch_then (drule_at (Pat `unwrap_value _ _ _ = _`)) >>
      disch_then (qspec_then `tv` mp_tac) >>
      (impl_tac >- (gvs[] >> metis_tac[])) >> strip_tac >>
      qexistsl [`tr`,`v`,`q`] >> gvs[] >> metis_tac[]) >>
  drule_at (Pat `gas_marked_exec _ _ _ _ _ _ _ _`) ifexp_arm_marked_suffix >>
  disch_then (drule_at (Pat `vv_post _ _ _ _ _ _ _ _ _ _ _ _ _`)) >>
  disch_then (drule_at (Pat `compile_ifexp_arm _ _ _ _ _ = _`)) >>
  (impl_tac >- (simp[SF ETA_ss] >> metis_tac[optionTheory.SOME_11])) >> strip_tac >>
  qexistsl [`tv'`,`v`,`q`] >> simp[] >>
  fs[expr_post_def, expr_val_rel_def] >> metis_tac[]
QED


Theorem ifexp_joint_arm_outcome:
  intcall_expr_producer fp e /\ post_value_type ce e = expr_type e /\
  intcall_frame_ok fp /\ body_inv fp.jc_tops fp.jc_ctx ce fp.jc_cx /\
  expr_body_pre ce fp.jc_cx env e es /\ supportedExprs$supported_expr fp.jc_tops e /\
  calls_follow_call_graph fp.jc_edges fp.jc_owner (int_calls_expr e) /\
  compile_expr ce ty e sa = (vv,sm) /\
  compile_ifexp_arm ce (expr_type e) (lowered_value_type ce e) vv sm = (op,sb) /\
  fn_has_code sa sm fp.jc_func /\ fn_has_code sm sb fp.jc_func /\
  fn_inst_ids_distinct fp.jc_func /\
  gas_admissible (eval_expr fp.jc_cx e) expr_vv_res_ok es /\
  gas_admissible (bind (eval_expr fp.jc_cx e) (conditional_result fp.jc_cx))
    expr_vv_res_ok es /\
  intcall_expr_res fp ce env es sa s0 /\ ~s0.vs_halted /\
  s0.vs_current_bb = sa.cs_current_bb /\ s0.vs_inst_idx = LENGTH sa.cs_current_insts /\
  sa.cs_next_var <= sm.cs_next_var /\ sa.cs_next_id <= sm.cs_next_id /\
  (~is_word_type (expr_type e) ==>
    lowered_value_type ce e = expr_type e \/
    is_bytestring_type (expr_type e) /\ is_bytestring_type (lowered_value_type ce e) /\
      arg_type_fits (lowered_value_type ce e) (expr_type e) \/
    same_memory_layout ce (lowered_value_type ce e) (expr_type e)) /\
  (!tv. evaluate_type (get_tenv fp.jc_cx) (expr_type e) = SOME tv /\
      ~is_word_type (expr_type e) ==>
      type_memory_bytes ce (expr_type e) = type_memory_size tv /\
      type_memory_size tv < 2 ** 64) /\
  (!gs v es2. ~is_word_type (expr_type e) /\
    bind (eval_expr fp.jc_cx e) (read_result fp.jc_cx)
      (es with gas_obs := gs) = (INL v,es2) ==>
    ?tv. evaluate_type (get_tenv fp.jc_cx) (expr_type e) = SOME tv /\ value_has_type tv v) /\
  (?tv. evaluate_type (get_tenv fp.jc_cx) (expr_type e) = SOME tv) ==>
  gas_outcome F (cx_tops fp.jc_cx) (fp.jc_ctx,fp.jc_func)
    (bind (eval_expr fp.jc_cx e) (conditional_result fp.jc_cx)) (es,s0)
    (\res ee q. ?tr v w. res = INL tr /\ read_result fp.jc_cx tr ee = (INL v,ee) /\
      expr_post fp.jc_ctx fp.jc_func ce fp.jc_cx e es sa sb s0 ee v op q /\
      eval_operand op q = SOME w /\
      (post_value_type ce e <> NoneT /\ ~is_word_type (post_value_type ce e) /\
       ~is_bytestring_type (post_value_type ce e) ==>
       !tv. evaluate_type (get_tenv fp.jc_cx) (post_value_type ce e) = SOME tv ==>
         ?a k. a <= w2n w /\ w2n w + type_memory_size tv <= a+k /\
           a+k < dimword (:256) /\
           (fp.jc_lo <= a \/ ?b z. fp.jc_staged b z /\ b <= a /\ a+k <= b+z)) /\
      q.vs_current_bb = sb.cs_current_bb /\ q.vs_inst_idx = LENGTH sb.cs_current_insts)
    (\res ee r. expr_exit res r)
Proof
  strip_tac >>
  qpat_x_assum `intcall_expr_producer _ _` mp_tac >>
  simp[Once intcall_expr_producer_def] >>
  disch_then (drule_at (Pat `compile_expr _ _ _ _ = _`)) >>
  disch_then (drule_at (Pat `intcall_expr_res _ _ _ _ _ _`)) >>
  (impl_tac >- simp[]) >> strip_tac >>
  irule gas_outcome_bind_result_exec >>
  goal_assum (drule_at Any) >> simp[] >>
  conj_tac >- (rpt gen_tac >> Cases_on `res` >> simp[expr_exit_def]) >>
  reverse conj_tac >- (rpt strip_tac >> simp[]) >>
  rpt strip_tac >>
  qpat_x_assum `gas_outcome _ _ _ _ _ _ _` kall_tac >>
  `vv_post fp.jc_ctx fp.jc_func ce fp.jc_cx e es sa sm s0
     (mid with gas_obs := []) v vv t` by
    (fs[vv_post_def, intcall_expr_cont_def, intcall_joint_res_def, intcall_expr_res_def] >>
     first_assum MATCH_ACCEPT_TAC) >>
  drule_at (Pat `gas_marked_exec _ _ _ _ _ _ _ _`) ifexp_joint_arm_marked_suffix >>
  disch_then (drule_at (Pat `vv_post _ _ _ _ _ _ _ _ _ _ _ _ _`)) >>
  disch_then (drule_at (Pat `compile_ifexp_arm _ _ _ _ _ = _`)) >>
  disch_then (drule_at (Pat `intcall_expr_res _ _ _ _ _ _`)) >>
  (impl_tac >- (simp[] >> metis_tac[optionTheory.SOME_11])) >>
  strip_tac >> rewrite_tac[gas_outcome_def] >> qexists `[]` >> disj1_tac >>
  rewrite_tac[gas_summary_at_def] >>
  qexistsl [`INL tr`, `mid with gas_obs := []`, `OK q`] >>
  simp[] >>
  qpat_x_assum `_ ==> !tv. _` mp_tac >> simp[]
QED

Theorem ifexp_joint_expr_producer:
  intcall_forced_producer fp c /\ intcall_expr_producer fp a /\
  intcall_expr_producer fp b ==>
  intcall_expr_producer fp (IfExp t c a b)
Proof
  strip_tac >> simp[Once intcall_expr_producer_def] >> rpt gen_tac >> strip_tac >>
  drule expr_body_pre_ifexp >> strip_tac >>
  `local_ptrs_reserved ce sa` by fs[intcall_joint_res_def, intcall_expr_res_def] >>
  `?cop sc. lower_value compile_expr ce (BaseT BoolT) c sa = (cop,sc) /\
    fn_has_code sa sc fp.jc_func` by
    (drule_at (Pat `compile_expr _ _ _ _ = _`) ifexp_root_code_layout >>
     disch_then (drule_at (Pat `fn_has_code _ _ _`)) >>
     (impl_tac >- (simp[] >> metis_tac[compile_expr_grows])) >>
     disch_then (qspec_then `T` strip_assume_tac) >> metis_tac[]) >>
  `supportedExprs$supported_expr fp.jc_tops c /\
   calls_follow_call_graph fp.jc_edges fp.jc_owner (int_calls_expr c)` by
    fs[supportedExprsTheory.supported_expr_def,
       supportedExprsTheory.supported_pure_expr_def,
       supportedExprsTheory.supported_effect_expr_def,
       vyperTypeCallGraphTheory.int_calls_expr_def] >>
  qpat_x_assum `intcall_forced_producer _ _` mp_tac >>
  simp[Once intcall_forced_producer_def] >>
  disch_then (drule_at (Pat `lower_value _ _ _ _ _ = _`)) >>
  disch_then (drule_at (Pat `intcall_expr_res _ _ _ _ _ _`)) >>
  (impl_tac >- (simp[] >> metis_tac[ifexp_root_condition_admissible])) >>
  disch_then (strip_assume_tac o REWRITE_RULE [gas_outcome_def])
  >- (qpat_x_assum `gas_summary_at _ _ _ _ _ _ _` mp_tac >>
      rewrite_tac[gas_summary_at_def] >> strip_tac
      >- suspend "normal" >>
      irule ifexp_root_condition_exit >> goal_assum (drule_at Any) >> fs[]) >>
  rewrite_tac[gas_outcome_def] >> qexists `marks` >> disj2_tac >>
  drule ifexp_root_condition_cert >> metis_tac[]
QED

Resume ifexp_joint_expr_producer[normal]:
  qpat_x_assum `(\res ee u. _) _ _ _` (strip_assume_tac o BETA_RULE) >>
  gvs[] >>
  `?sel. v = BoolV sel` by
    (irule ifexp_root_condition_bool >> goal_assum (drule_at Any) >>
     fs[gas_marked_exec_def] >> metis_tac[]) >>
  gvs[] >>
  `expr_post fp.jc_ctx fp.jc_func ce fp.jc_cx c es sa sc s
     (es_end with gas_obs := []) (BoolV sel) cop t'` by
    (fs[expr_post_def, intcall_expr_cont_def, intcall_joint_res_def, intcall_expr_res_def] >>
     first_assum MATCH_ACCEPT_TAC) >>
  drule_at (Pat `compile_expr _ _ (IfExp _ _ _ _) _ = _`) ifexp_root_code_layout >>
  disch_then (drule_at (Pat `fn_has_code sa sb _`)) >>
  (impl_tac >- (simp[] >> metis_tac[compile_expr_grows])) >>
  disch_then (qspec_then `sel` strip_assume_tac) >> gvs[] >>
  `~t'.vs_halted /\ t'.vs_current_bb = sc.cs_current_bb /\
   t'.vs_inst_idx = LENGTH sc.cs_current_insts` by fs[intcall_expr_cont_def] >>
  drule_all ifexp_root_jnz_path >> strip_tac >>
  `intcall_expr_res fp ce env (es_end with gas_obs := []) se
     (jump_to (if sel then tl else el) t')` by
    (`intcall_expr_res fp ce env (es_end with gas_obs := []) sc t'` by
       fs[intcall_expr_cont_def] >>
     pop_assum mp_tac >>
     simp[intcall_expr_res_def, stmt_state_rel_jump_to, stmtSimPropsTheory.ret_pc_ok_jump_to,
          bodyMemoryDefsTheory.return_buf_frame_jump_to, intCallFrameTheory.allocas_above_def, loweringStateRelDefsTheory.local_region_def,
          jump_to_def, eval_operand_def, lookup_var_def] >>
     strip_tac >>
     `local_ptrs_reserved ce se` by
       (irule local_ptrs_reserved_next_var >> goal_assum (drule_at Any) >> simp[]) >>
     `ret_pc_ok ce se t'` by
       (drule stmtSimPropsTheory.ret_pc_ok_frame >> disch_then irule >> simp[]) >>
     `return_buf_frame fp.jc_rb ce se t'` by
       (drule bodyMemoryDefsTheory.return_buf_frame_frame >> disch_then irule >> simp[]) >>
     simp[] >> rpt strip_tac >> metis_tac[freshWritesTheory.not_fresh_at_mono]) >>
  `expr_body_pre ce fp.jc_cx env (if sel then a else b)
     (es_end with gas_obs := [])` by
    (Cases_on `sel` >> fs[intcall_joint_res_def, intcall_expr_res_def]) >>
  `supportedExprs$supported_pure_expr fp.jc_tops (if sel then a else b)` by
    (Cases_on `sel` >>
     fs[supportedExprsTheory.supported_expr_def,
        supportedExprsTheory.supported_pure_expr_def,
        supportedExprsTheory.supported_effect_expr_def]) >>
  `post_value_type ce (if sel then a else b) = expr_type (if sel then a else b)` by
    (irule post_value_type_not_int_call >> rpt strip_tac >>
     gvs[supportedExprsTheory.supported_pure_expr_def]) >>
  `int_calls_expr (if sel then a else b) = []` by
    metis_tac[bodyExprPreFactsTheory.supported_pure_int_calls] >>
  `gas_admissible (bind (eval_expr fp.jc_cx (if sel then a else b))
     (conditional_result fp.jc_cx)) expr_vv_res_ok (es_end with gas_obs := [])` by
    (irule ifexp_root_branch_admissible >> goal_assum (drule_at Any) >>
     fs[gas_marked_exec_def] >> metis_tac[]) >>
  `intcall_expr_producer fp (if sel then a else b)` by (Cases_on `sel` >> simp[]) >>
  `expr_type (if sel then a else b) = expr_type a` by (Cases_on `sel` >> simp[]) >>
  drule_at (Pat `compile_expr _ _ _ _ = _`) ifexp_joint_arm_outcome >>
  disch_then (drule_at (Pat `intcall_expr_res _ _ _ _ _ _`)) >>
  disch_then (fn th => qpat_assum `expr_type (if _ then _ else _) = _`
    (fn eq => drule_at (Pat `compile_ifexp_arm _ _ _ _ _ = _`) (REWRITE_RULE [eq] th))) >>
  impl_tac >- suspend "arm_hyps" >> strip_tac >>
  suspend "arm_finish"
QED

Resume ifexp_joint_expr_producer[arm_hyps]:
  `cs_extends se sea /\ se.cs_next_var <= sea.cs_next_var /\
   se.cs_next_id <= sea.cs_next_id` by metis_tac[compile_expr_grows] >>
  `cs_extends sea sx` by
    (mp_tac ci_mono_compile_ifexp_arm >>
     simp[ci_mono_def] >> metis_tac[pairTheory.SND]) >>
  `fn_has_code se sea fp.jc_func /\ fn_has_code sea sx fp.jc_func` by
    metis_tac[fragExecTheory.fn_has_code_split] >>
  `gas_admissible (eval_expr fp.jc_cx (if sel then a else b)) expr_vv_res_ok
     (es_end with gas_obs := [])` by metis_tac[ifexp_arm_raw_admissible] >>
  simp[jump_to_def, supportedExprsTheory.supported_expr_def] >>
  rpt conj_tac
  >- (qpat_assum `expr_body_pre _ _ _ (if _ then _ else _) _`
        (mp_tac o MATCH_MP (REWRITE_RULE [GSYM AND_IMP_INTRO]
          ifexp_body_pre_lowered_type_compatible)) >> simp[] >> metis_tac[]) 
  >- (rpt strip_tac >>
      qpat_assum `expr_body_pre _ _ _ (if _ then _ else _) _`
        (mp_tac o MATCH_MP (REWRITE_RULE [GSYM AND_IMP_INTRO]
          exprSimHypsTheory.expr_body_pre_copy_ok)) >> simp[])
  >- (rpt strip_tac >>
      `expr_body_pre ce fp.jc_cx env (if sel then a else b)
         (es_end with gas_obs := gs)` by
        fs[exprSimSourceTheory.expr_body_pre_gas_obs] >>
      metis_tac[ifexp_body_pre_read_typed]) >>
  qpat_assum `expr_body_pre _ _ _ (if _ then _ else _) _`
    (mp_tac o MATCH_MP exprSimHypsTheory.expr_body_pre_type_evaluates) >>
  simp[optionTheory.IS_SOME_EXISTS]
QED

Resume ifexp_joint_expr_producer[arm_finish]:
  drule_at (Pat `gas_outcome _ _ _ _ _ _ _`)
    (ifexp_arm_finish_slot |> Q.INST
      [`slot_ok` |-> `\w:bytes32.
        (post_value_type ce (if sel then a else b) <> NoneT /\
         ~is_word_type (post_value_type ce (if sel then a else b)) /\
         ~is_bytestring_type (post_value_type ce (if sel then a else b)) ==>
         !tv. evaluate_type (get_tenv fp.jc_cx)
           (post_value_type ce (if sel then a else b)) = SOME tv ==>
         ?a k. a <= w2n w /\ w2n w + type_memory_size tv <= a+k /\
           a+k < dimword (:256) /\
           (fp.jc_lo <= a \/ ?b z. fp.jc_staged b z /\ b <= a /\ a+k <= b+z))`]
      |> SIMP_RULE (srw_ss()) []) >>
  disch_then (drule_at (Pat `expr_post _ _ _ _ _ _ _ _ _ _ _ _ _`)) >>
  disch_then (drule_at (Pat `emit_inst ASSIGN _ _ _ = _`)) >>
  disch_then (drule_at (Pat `emit_inst JMP _ _ _ = _`)) >>
  disch_then (qspecl_then [`expr_type a`, `sb`] mp_tac) >>
  impl_tac >- (simp[] >> conj_tac
    >- fs[intcall_joint_res_def, intcall_expr_res_def] >>
    drule (REWRITE_RULE [ETA_THM] bop_marked_scopes_dom) >> simp[]) >>
  strip_tac >>
  drule_at (Pat `gas_outcome _ _ _ _ _ _ _`)
    ifexp_root_selected_outcome_prefix >>
  disch_then (drule_at (Pat `gas_marked_exec _ _ _ _ _ _ _ _`)) >>
  disch_then (drule_at (Pat `gas_path _ _ _ _ _`)) >>
  disch_then (qspec_then `expr_type a` mp_tac) >>
  disch_then (irule o MATCH_MP
    (REWRITE_RULE [GSYM AND_IMP_INTRO]
      stmtSimForLoopTheory.gas_outcome_exec_conseq)) >>
  reverse conj_tac >- simp[] >>
  rpt strip_tac >>
  qpat_x_assum `(\res ee u. _) _ _ _` (strip_assume_tac o BETA_RULE) >>
  gvs[] >> suspend "lift_root"
QED

Resume ifexp_joint_expr_producer[lift_root]:
  `~expr_has_effect (IfExp (expr_type a) c a b)` by
    (irule supportedExprTraverseTheory.supported_pure_expr_effect_free >>
     qexists `fp.jc_tops` >>
     qpat_x_assum `supportedExprs$supported_expr _ (IfExp _ _ _ _)` mp_tac >>
     simp[supportedExprsTheory.supported_expr_def,
          supportedExprsTheory.supported_effect_expr_def]) >>
  qpat_assum `gas_marked_exec _ _ (eval_expr _ _) _ _ _ _ _`
    (strip_assume_tac o REWRITE_RULE [gas_marked_exec_def,
       fragGasModeTheory.gas_marked_path_def]) >>
  `intcall_expr_cont fp ce env
     (es with gas_obs := gas_explicit marks' s.vs_gas_readings)
     sa s (mid with gas_obs := []) sb t` by
    (irule bodyIntCallJointPureContTheory.pure_vv_post_cont >>
     simp[] >>
     conj_tac >- metis_tac[exprSimUnwrapTheory.compile_expr_extends] >>
     conj_tac >- metis_tac[] >>
     conj_tac >- (fs[intcall_joint_res_def, intcall_expr_res_def] >> metis_tac[]) >>
     qexistsl [`IfExp (expr_type a) c a b`, `INL tv`, `tv`,
       `if is_word_type (expr_type a) then StackValue (expr_type a) (Var rv)
        else LocatedValue (expr_type a) (mk_ptr (Var rv) LocMemory)`] >>
     simp[] >>
     conj_tac >- (first_x_assum (qspec_then `[]` mp_tac) >> simp[]) >>
     qpat_x_assum `vv_post _ _ _ _ _ _ _ _ _ _ _ _ _` mp_tac >>
     simp[vv_post_def, locals_kept_def] >> strip_tac >> metis_tac[]) >>
  `intcall_expr_cont fp ce env es sa s (mid with gas_obs := []) sb t` by
    (qpat_x_assum `intcall_expr_cont _ _ _ (_ with gas_obs := _) _ _ _ _ _` mp_tac >>
     simp[intcall_expr_cont_def, locals_kept_def] >> strip_tac >> metis_tac[]) >>
  qpat_x_assum `vv_post _ _ _ _ _ _ _ _ _ _ _ _ _` mp_tac >>
  simp[vv_post_def] >> strip_tac >>
  simp[] >> conj_tac
  >- metis_tac[CONJUNCT1 exprOperandVarTheory.compiler_compile_var] >>
  simp[expr_type_def, contextTheory.vv_operand_def,
       contextTheory.mk_ptr_def] >> metis_tac[]
QED

Finalise ifexp_joint_expr_producer

Theorem intcall_ifexp_step:
  (!e'. expr_size e' < expr_size e ==>
        intcall_expr_producer fp e' /\ intcall_forced_producer fp e' /\
        intcall_map_producer fp e') /\
  (?ty c e1 e2. e = IfExp ty c e1 e2) ==>
  intcall_expr_producer fp e /\ intcall_map_producer fp e
Proof
  strip_tac >> gvs[] >> conj_tac
  >- (irule ifexp_joint_expr_producer >>
      simp[]) >>
  simp[intcall_map_producer_def, exprSimMapDefsTheory.expr_map_pre_def,
       Once vyperTypeSystemTheory.well_typed_expr_def]
QED
