(* Ordinary posts for a selected local child; implementation-only boundaries. *)
Theory bodyPtrSubscriptNamedTuplePostBoundary
Ancestors
  loweringPosts exprSimProps exprSimDefs exprLoweringProps compileEnv context
  venomState valueEncodingTyping vyperAST bodyPtrDefs

Theorem local_child_vv_holds:
  evaluate_type (get_tenv cx) ann = SOME tv /\ value_has_type tv child /\
  read_result cx result es = (INL child,es) /\
  lookup_var out s = SOME a /\ val_in_memory tv child (w2n a) s.vs_memory ==>
  vv_holds cenv cx ann result (LocatedValue ann (mk_ptr (Var out) LocMemory)) es s
Proof
  strip_tac >> simp[vv_holds_def, mk_ptr_def, eval_operand_def] >>
  strip_tac >> irule val_in_memory_word_type >> metis_tac[]
QED

Theorem local_child_vv_at:
  evaluate_type (get_tenv cx) ann = SOME tv /\ val_wf tv child /\
  read_result cx result es = (INL child,es) /\
  lookup_var out s = SOME (a + n2w off) /\
  local_region cenv es.scopes s id (w2n a) sz /\
  local_path_at cenv cx id off tv /\
  off + type_memory_size tv <= sz /\ w2n a + off < dimword (:256) ==>
  vv_at cenv cx ann sa sb es result
    (LocatedValue ann (mk_ptr (Var out) LocMemory)) s
Proof
  strip_tac >> drule val_footprint_le >> strip_tac >>
  `off < dimword (:256)` by decide_tac >>
  simp[vv_at_def, mk_ptr_def, eval_operand_def] >>
  disj2_tac >> disj1_tac >> qexistsl_tac [`id`, `w2n a`, `sz`] >>
  simp[wordsTheory.w2n_add_2, wordsTheory.w2n_n2w,
       arithmeticTheory.LESS_MOD, local_val_at_def] >> decide_tac
QED

Theorem fresh_add_stmt_state_rel:
  stmt_state_rel ctx func cenv cx es s /\ local_ptrs_reserved cenv sa /\
  ~not_fresh_at sa out ==>
  stmt_state_rel ctx func cenv cx es
    (update_var out w s with vs_inst_idx := n)
Proof
  strip_tac >> rewrite_tac[stmt_state_rel_inst_idx] >>
  irule stmt_state_rel_update_var >> simp[] >>
  fs[not_local_ptr_def, local_ptrs_reserved_def] >> metis_tac[]
QED

Theorem local_child_vv_post:
  stmt_state_rel ctx func cenv cx es sf /\ expr_type e = ann /\
  post_value_type cenv e = expr_type e /\
  evaluate_type (get_tenv cx) ann = SOME tv /\ value_has_type tv child /\
  read_result cx result es = (INL child,es) /\
  lookup_var out sf = SOME (a + n2w off) /\
  val_in_memory tv child (w2n (a + n2w off)) sf.vs_memory /\
  local_region cenv es.scopes sf id (w2n a) sz /\
  local_path_at cenv cx id off tv /\ off + type_memory_size tv <= sz /\
  w2n a + off < dimword (:256) /\
  sf.vs_memory = s.vs_memory /\ sf.vs_allocas = s.vs_allocas /\
  (!q. not_fresh_at sa q ==> lookup_var q sf = lookup_var q s) ==>
  vv_post ctx func cenv cx e es sa sb s es result
    (LocatedValue ann (mk_ptr (Var out) LocMemory)) sf
Proof
  strip_tac >>
  `vv_holds cenv cx ann result
     (LocatedValue ann (mk_ptr (Var out) LocMemory)) es sf` by
    (irule local_child_vv_holds >> goal_assum (drule_at Any) >> simp[]) >>
  `vv_at cenv cx ann sa sb es result
     (LocatedValue ann (mk_ptr (Var out) LocMemory)) sf` by
    (irule local_child_vv_at >> goal_assum (drule_at Any) >>
     simp[] >> metis_tac[value_has_type_val_wf]) >>
  simp[vv_post_def, locals_kept_def] >> simp[mk_ptr_def]
QED
