(* Ordinary posts for a selected local child; implementation-only boundaries. *)
Theory bodyPtrSubscriptNamedTuplePostBoundary
Ancestors
  loweringPosts exprSimProps exprSimDefs exprLoweringProps compileEnv loweringStateRelDefs context
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

