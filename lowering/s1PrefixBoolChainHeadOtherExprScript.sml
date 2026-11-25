(* Prefix introductions for residual non-call BoolChain head expressions. *)
Theory s1PrefixBoolChainHeadOtherExpr
Ancestors
  s1PrefixAtomicExprIntro s1PrefixAttribute s1PrefixStructLit
  s1PrefixCheckedContextFull s1PrefixPopFullGuard s1PrefixPopIndexIntro
  s1PrefixTypeBuiltinGuarded s1PrefixPreds exprCallBounds vyperAST list
  s1PrefixBoolChainHeadMakeArray[qualified,ignore_grammar]

Theorem bool_chain_head_other_expr_prefix_ok:
  !cx h.
    (!ann bt xs. h <> Builtin ann bt xs) /\
    (!ann ct xs dr. h <> Call ann ct xs dr) /\
    (!ty c a b. h <> IfExp ty c a b) /\
    (!ann obj idx. h <> Subscript ann obj idx) /\
    (!x. expr_size x < expr_size h ==> body_expr_prefix_ok cx x) ==>
    body_expr_prefix_ok cx h
Proof
  rpt gen_tac >> Cases_on `h` >> simp[] >> strip_tac >>
  TRY (irule atomic_expr_prefix_ok >> simp[] >> NO_TAC) >>
  TRY (rename1 `body_expr_prefix_ok cx (Pop ann bt)` >>
       irule pop_prefix_from_smaller_indices >> simp[expr_size_def] >>
       metis_tac[pop_full_target_at_entry] >> NO_TAC) >>
  reverse (Cases_on `?tops env es. body_const_cells_agree [(NONE,tops)] cx env es`) >>
  TRY (qpat_assum `~(?tops env es. _)` mp_tac >>
       once_rewrite_tac[body_expr_prefix_ok_def] >> simp[] >>
       metis_tac[] >> NO_TAC) >>
  qpat_x_assum `?tops env es. _` strip_assume_tac >>
  drule_then strip_assume_tac checked_context_full_exprs
  >- (rename1 `body_expr_prefix_ok cx (StructLit ann nsid fields)` >>
      Cases_on `nsid` >> irule structlit_expr_prefix_ok >> simp[] >>
      irule s1PrefixBoolChainHeadMakeArrayTheory.prefix_list_from_members >>
      simp[MEM_MAP, pairTheory.EXISTS_PROD] >>
      rpt strip_tac >> first_x_assum irule >>
      drule (SIMP_RULE (srw_ss()) [] expr_struct_field_bound) >> simp[])
  >- (irule attribute_expr_prefix_ok >> simp[expr_attribute_child_bound]) >>
  irule body_type_builtin_case_prefix >> simp[] >>
  rpt strip_tac >>
  irule s1PrefixBoolChainHeadMakeArrayTheory.prefix_list_from_members >>
  rpt strip_tac >>
  first_x_assum irule >>
  drule expr_list_member_bound >> decide_tac
QED
