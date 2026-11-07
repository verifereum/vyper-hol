Theory bodyPtrPopNestedHeader
Ancestors bodyPtrPopNestedCompilation bodyPtrPopSuffixSignature vyperAST

Theorem pop_nested_target_header:
  !f cenv bt sa hdr lo pt sb.
  (~(?id. bt = NameTarget id)) /\
  (~(?nid. bt = TopLevelNameTarget nid)) /\
  compile_get_target_ptr f cenv bt sa = ((hdr,lo,pt),sb) ==>
  ?h. hdr = Var h
Proof
  rpt gen_tac >> Cases_on `bt` >> simp[] >>
  metis_tac[pop_target_attribute_address, pop_target_subscript_address]
QED

Theorem pop_nested_entry_nonstorage:
  body_inv tops ctx cenv cx /\ ~cx.in_deploy /\
  stmt_state_rel ctx fn cenv cx es s /\
  (~(?id. bt = NameTarget id)) /\
  (~(?nid. bt = TopLevelNameTarget nid)) /\
  compile_get_target_ptr compile_expr cenv bt sa = ((hdr,lo,pt),sm) /\
  compile_expr cenv ty (Pop ann bt) sa = (vv,sb) /\
  fn_has_code sa sb fn ==>
  lo <> SOME LocStorage /\ lo <> SOME LocTransient
Proof
  rpt strip_tac >> drule_all pop_nested_target_header >> strip_tac >> gvs[] >>
  mp_tac (Q.SPEC `F` (Q.GEN `tr` pop_compile_storage_entry_exclusion)) >>
  mp_tac (Q.SPEC `T` (Q.GEN `tr` pop_compile_storage_entry_exclusion)) >>
  simp[] >> metis_tac[]
QED
