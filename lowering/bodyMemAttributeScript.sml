(* Memory case of the body induction (bodyMemory's body_mem_mutual): a field
   read, for any base.  The value judgment is bodyAttributeMemory's, from the
   base's; the forced one is the generic unwrap, since a field read compiles
   to a pointer, never a stack value. *)
Theory bodyMemAttribute
Ancestors
  bodyMemoryPreds bodyAttributeMemory bodyExprForceMemory exprSimAttribute
  exprSimMemDefs exprLowering context

Theorem body_attribute_mem_ok:
  !cx v9 e id. body_expr_mem_ok cx e ==> body_expr_mem_ok cx (Attribute v9 e id)
Proof
  rpt gen_tac >> strip_tac >> (match_mp_tac body_expr_mem_ok_intro >>
   conj_tac >- (rpt strip_tac >> gvs[])) >>
  qpat_x_assum `body_expr_mem_ok _ _`
    (assume_tac o CONJUNCT1 o REWRITE_RULE [body_expr_mem_ok_def]) >>
  rpt gen_tac >> strip_tac >>
  drule attr_pre_base >> strip_tac >>
  `expr_vv_sim_mem ctx func cenv cx ty e es` by metis_tac[] >>
  `expr_vv_sim_mem ctx func cenv cx ty (Attribute v9 e id) es` by
    metis_tac[compile_attribute_vv_sim_mem] >>
  simp[] >> irule body_expr_sim_mem_of_vv_sim_mem >> simp[] >>
  conj_tac
  >- (rpt gen_tac >> strip_tac >> drule compile_expr_attribute >> simp[]) >>
  goal_assum drule
QED
