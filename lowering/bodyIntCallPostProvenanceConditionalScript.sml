(* Conditional certificates use the selected arm's actual endpoint. *)
Theory bodyIntCallPostProvenanceConditional
Ancestors
  bodyIntCallPostProvenanceArmIdentity bodyIntCallPostProvenanceArmCopy
  bodyIntCallPostProvenanceTypedCases bodyIntCallPostProvenanceOrdinary
  exprSimIfExp bodyIntCallMemoryView bodyIntCallProducerInterface
  venomState finite_map context loweringPosts loweringStateRelDefs compileEnv words
  bodyPtrIfExpRepresentationCases vyperTypeSystem vyperAST exprLowering
  bodyIntCallPostProvenanceCallbacks

Theorem intcall_ifexp_merge_provenance:
  intcall_vv_provenance ce cx ty sc sd ee tv
    (LocatedValue ty (mk_ptr op LocMemory)) u /\
  eval_operand op u = SOME w /\ local_ptrs_reserved ce sa /\
  (!x. not_fresh_at sa x ==> x <> rv) /\
  sa.cs_next_id <= sc.cs_next_id /\ sd.cs_next_id <= sb.cs_next_id ==>
  intcall_vv_provenance ce cx ty sa sb ee tv
    (LocatedValue ty (mk_ptr (Var rv) LocMemory))
    (jump_to xl (update_var rv w u with vs_inst_idx := k))
Proof
  strip_tac >>
  qabbrev_tac `ss = jump_to xl (update_var rv w u with vs_inst_idx := k)` >>
  `ss.vs_allocas = u.vs_allocas /\ lookup_var rv ss = SOME w /\
   (!x. x <> rv ==> lookup_var x ss = lookup_var x u)` by
    simp[Abbr `ss`, jump_to_def, update_var_def, lookup_var_def,
         FLOOKUP_UPDATE] >>
  `!n b sz. local_region ce ee.scopes ss n b sz <=>
            local_region ce ee.scopes u n b sz` by
    (rpt gen_tac >> simp[local_region_def] >> eq_tac >> rpt strip_tac >>
     fs[local_ptrs_reserved_def] >> metis_tac[]) >>
  qpat_x_assum `intcall_vv_provenance _ _ _ _ _ _ _ _ u` mp_tac >>
  simp[intcall_vv_provenance_def, mk_ptr_def, eval_operand_def] >>
  rpt strip_tac >> first_x_assum drule_all >> strip_tac >> gvs[]
  >~ [`FLOOKUP u.vs_allocas aid = SOME _`]
  >- (disj1_tac >> qexistsl_tac [`aid`, `b`, `sz`] >> simp[] >>
      first_assum ACCEPT_TAC)
  >~ [`local_val_at ce cx n _ _ _`]
  >- (ntac 2 disj2_tac >> disj1_tac >> qexistsl_tac [`n`, `b`, `sz`] >> simp[]) >>
  ntac 3 disj2_tac >>
  rename [`FLOOKUP ce.ce_vars n = SOME (PtrVar (Var pv) sz)`,
          `lookup_var pv u = SOME bv`, `sub_layout _ _ offset tvt v`] >>
  `pv <> rv` by (fs[local_ptrs_reserved_def] >> metis_tac[]) >>
  qexistsl_tac [`n`, `sz`, `entry`, `pv`, `bv`, `offset`] >> simp[]
QED

Theorem intcall_ifexp_merge_outcome:
  post_value_type ce e = expr_type e /\
  expr_post ctx func ce cx c es sa s1 s0 es1 v1 cop tt /\
  expr_type e = ty /\ (!x. not_fresh_at sa x ==> x <> rv) /\
  local_ptrs_reserved ce sa /\ stmt_state_rel ctx func ce cx es s0 /\
  MAP FDOM es.scopes = MAP FDOM es1.scopes /\
  sa.cs_next_var <= s1.cs_next_var /\ s1.cs_next_var <= sc.cs_next_var /\
  sa.cs_next_id <= s1.cs_next_id /\ s1.cs_next_id <= sc.cs_next_id /\
  (~expr_has_effect (IfExp ty c a b) ==> ~expr_has_effect e) /\
  sd.cs_next_id <= sb.cs_next_id /\ sb.cs_current_bb = xl /\ sb.cs_current_insts = [] /\
  emit_inst ASSIGN [op] [rv] sd = ((),sy) /\
  emit_inst JMP [Label xl] [] sy = ((),sz) /\
  fn_has_code sd sy func /\ fn_has_code sy sz func /\
  gas_outcome F tops (ctx,func) source (es1,jump_to lbl tt)
    (\res ee u. ?tv v. res = INL tv /\ read_result cx tv ee = (INL v,ee) /\
      expr_post ctx func ce cx e es1 sc sd (jump_to lbl tt) ee v op u /\
      u.vs_current_bb = sd.cs_current_bb /\ u.vs_inst_idx = LENGTH sd.cs_current_insts /\
      (~is_word_type ty ==>
       vv_at ce cx ty sc sd ee tv (LocatedValue ty (mk_ptr op LocMemory)) u /\
       intcall_vv_provenance ce cx ty sc sd ee tv
         (LocatedValue ty (mk_ptr op LocMemory)) u)) R ==>
  gas_outcome F tops (ctx,func) source (es1,jump_to lbl tt)
    (\res ee u. ?tv. res = INL tv /\
      vv_post ctx func ce cx (IfExp ty c a b) es sa sb s0 ee tv
        (if is_word_type ty then StackValue ty (Var rv)
         else LocatedValue ty (mk_ptr (Var rv) LocMemory)) u /\
      u.vs_current_bb = sb.cs_current_bb /\ u.vs_inst_idx = LENGTH sb.cs_current_insts /\
      intcall_vv_provenance ce cx ty sa sb ee tv
        (if is_word_type ty then StackValue ty (Var rv)
         else LocatedValue ty (mk_ptr (Var rv) LocMemory)) u) R
Proof
  strip_tac >>
  qpat_x_assum `_ ==> ~expr_has_effect e` (assume_tac o SIMP_RULE (srw_ss()) []) >>
  irule ifexp_root_outcome_suffix >> goal_assum (drule_at Any) >>
  simp[] >> rpt strip_tac >>
  `?w. eval_operand op u = SOME w` by fs[expr_post_def, expr_val_rel_def] >>
  qexists_tac `jump_to xl (update_var rv w u with vs_inst_idx := LENGTH sy.cs_current_insts)` >>
  conj_tac >- (irule ifexp_root_suffix_path >> simp[] >> metis_tac[]) >>
  simp[] >> conj_tac
  >- (irule ifexp_root_finish_post >> simp[] >> metis_tac[]) >>
  conj_tac >- simp[jump_to_def] >>
  conj_tac >- simp[jump_to_def] >> Cases_on `is_word_type ty`
  >- simp[intcall_vv_provenance_word] >> simp[] >>
  irule intcall_ifexp_merge_provenance >> simp[] >>
  conj_tac >- metis_tac[] >>
  qexistsl_tac [`op`, `sc`, `sd`] >> simp[] >> decide_tac
QED

Theorem intcall_dynamic_lowered_type:
  well_typed_expr env e /\ ~expr_has_effect e /\
  evaluate_type tenv (expr_type e) = SOME tv /\ ~dynarray_free tv ==>
  lowered_value_type ce e = expr_type e
Proof
  strip_tac >> spose_not_then assume_tac >>
  drule lowered_value_type_exceptions >> strip_tac >> gvs[]
  >- metis_tac[evaluate_base_dynarray_free, expr_type_def]
  >- metis_tac[evaluate_base_dynarray_free, expr_type_def]
  >- (fs[Once well_typed_expr_def, expr_type_def] >>
      drule typed_builtin_dynarray_free >> simp[] >> metis_tac[])
  >- (fs[expr_type_def] >> drule typed_type_builtin_dynarray_free >>
      simp[] >> metis_tac[]) >>
  fs[expr_has_effect_thm]
QED
