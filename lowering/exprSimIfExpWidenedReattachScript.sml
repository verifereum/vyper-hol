Theory exprSimIfExpWidenedReattach
Ancestors
  exprSimProps exprBopSimProps exprSimAggregateChildren
  exprSimIfExpWidenedEntry exprSimIfExpWidenedCounted
  loweringPosts compileEnv exprLoweringProps

Theorem vv_post_reattach_expr_post:
  vv_post ctx func ce cx e es origin sm s0 ee tv vv u /\
  expr_post ctx func ce cx e ee
    (origin with cs_next_var := sm.cs_next_var) sn u ee v op q /\
  local_ptrs_rel func ce es.scopes s0 /\
  local_ptrs_reserved ce origin /\
  MAP FDOM es.scopes = MAP FDOM ee.scopes /\
  origin.cs_next_var <= sm.cs_next_var ==>
  expr_post ctx func ce cx e es origin sn s0 ee v op q
Proof
  simp[expr_post_def, vv_post_def, expr_val_at_def, expr_val_own_def] >>
  strip_tac >>
  `!n b sz. local_region ce ee.scopes u n b sz ==>
    local_region ce es.scopes s0 n b sz` by
    (rpt strip_tac >> irule local_region_frame >>
     conj_tac >- (qexists_tac `func` >> simp[]) >>
     qexistsl_tac [`origin`, `ee.scopes`, `u`] >> simp[]) >>
  conj_tac
  >- (rpt strip_tac >>
      `not_fresh_at (origin with cs_next_var := sm.cs_next_var) x` by
        (fs[not_fresh_at_def] >> metis_tac[arithmeticTheory.LESS_LESS_EQ_TRANS]) >>
      metis_tac[]) >>
  conj_tac
  >- (rpt strip_tac >>
      `mem_bytes_at off sz u.vs_memory = mem_bytes_at off sz s0.vs_memory` by
        metis_tac[] >>
      `mem_bytes_at off sz q.vs_memory = mem_bytes_at off sz u.vs_memory` by
        metis_tac[] >> simp[]) >>
  irule locals_kept_trans >> qexistsl_tac [`ee`, `origin`, `u`] >> simp[]
QED

Theorem unwrap_value_physical_framed_path:
  (post_value_type ce e <> expr_type e ==>
    ((?t op. vv = StackValue t op) \/
     (?t p. vv = LocatedValue t p /\ p.ptr_location = LocMemory /\
       ~is_word_type t))) /\
  unwrap_value ce vv sm = (op,sn) /\
  local_ptrs_reserved ce origin /\
  local_ptrs_rel func ce es.scopes s0 /\
  MAP FDOM es.scopes = MAP FDOM ee.scopes /\
  origin.cs_next_var <= sm.cs_next_var /\ origin.cs_next_id <= sm.cs_next_id /\
  fn_has_code sm sn func /\ fn_inst_ids_distinct func /\
  (!x. vv_operand vv = Var x ==> not_fresh_at sm x) /\
  (!tvt. evaluate_type (get_tenv cx) (post_value_type ce e) = SOME tvt /\
    ~is_word_type (post_value_type ce e) ==>
    type_memory_bytes ce (post_value_type ce e) = type_memory_size tvt /\
    type_memory_size tvt < 2 ** 64) /\
  read_result cx tv ee = (INL v,ee) /\
  vv_post ctx func ce cx e es origin sm s0 ee tv vv s /\
  ~s.vs_halted /\ s.vs_current_bb = sm.cs_current_bb /\
  s.vs_inst_idx = LENGTH sm.cs_current_insts ==>
  ?u. gas_marked_path F ctx func s 0 (OK u) /\
    expr_post ctx func ce cx e es origin sn s0 ee v op u /\
    u.vs_current_bb = sn.cs_current_bb /\
    u.vs_inst_idx = LENGTH sn.cs_current_insts /\
    (!x w. not_fresh_at sm x /\ lookup_var x s = SOME w ==>
      lookup_var x u = SOME w) /\
    (!aid entry. FLOOKUP s.vs_allocas aid = SOME entry ==>
      FLOOKUP u.vs_allocas aid = SOME entry)
Proof
  disch_then (REPEAT_TCL CONJUNCTS_THEN assume_tac) >>
  `vv_post ctx func ce cx e ee (origin with cs_next_var := sm.cs_next_var)
     sm s ee tv vv s` by metis_tac[vv_post_rebase] >>
  `local_ptrs_reserved ce (origin with cs_next_var := sm.cs_next_var)` by
    (irule local_ptrs_reserved_next_var >> qexists_tac `origin` >> simp[]) >>
  qpat_assum `vv_post _ _ _ _ _ ee _ sm s _ _ _ s`
    (mp_then (Pat `vv_post _ _ _ _ _ _ _ _ _ _ _ _ _`) mp_tac unwrap_value_physical_path) >>
  simp[] >> strip_tac >> qexists_tac `u` >> simp[] >>
  conj_tac
  >- (irule vv_post_reattach_expr_post >> simp[] >>
      qexistsl_tac [`sm`, `tv`, `s`, `vv`] >> simp[]) >>
  conj_tac >- metis_tac[expr_post_rebased_lookup] >>
  qpat_assum `expr_post _ _ _ _ _ ee _ sn s _ _ _ u`
    (strip_assume_tac o PURE_REWRITE_RULE[expr_post_def]) >> simp[]
QED
