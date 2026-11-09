(* Seam 2 joint induction, a family leaf of the pure step: ternaries. *)
Theory bodyIntCallFamPureIfExp
Ancestors
  bodyIntCallJointContract exprSimIfExp bodyIntCallJointPureSuffix
  loweringPosts venomState venomExecSemantics finite_map context exprLowering vyperAST
  exprSimAggregateChildren exprBopSimProps arithmetic exprSimProps
  exprSimWordArgs exprSimSubscriptArrayCompose exprSimAggregateSource
  stmtSimAugAssignPlaceMemory gasSummary gasContext vyperState exprSimSubscriptMap
  exprSimDefs gasOutcome

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
  intcall_frame_ok fp /\ intcall_joint_res fp ce env es sa s0 /\
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
    fs[intcall_expr_cont_def, intcall_joint_res_def, intcall_frame_ok_def] >>
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


Theorem intcall_ifexp_step:
  (!e'. expr_size e' < expr_size e ==>
        intcall_expr_producer fp e' /\ intcall_forced_producer fp e' /\
        intcall_map_producer fp e') /\
  (?ty c e1 e2. e = IfExp ty c e1 e2) ==>
  intcall_expr_producer fp e /\ intcall_map_producer fp e
Proof
  cheat
QED
