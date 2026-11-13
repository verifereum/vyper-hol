(* Ownership transport for noncapturing selections, on the actual witness. *)
Theory bodyIntCallPostProvenanceSelectors
Ancestors
  bodyIntCallProducerInterface bodyIntCallPostProvenanceOwnedTransport
  bodyIntCallPostProvenanceLiveSource bodyIntCallPostProvenanceLivePost
  bodyIntCallPostProvenanceFootprint exprSimAttribute exprSimSubscriptArrayCompose
  exprSimSubscriptArrayFramed loweringPosts context

Theorem intcall_dynamic_memory_selection:
  intcall_vv_provenance ce cx bt sa sb es raw bvv s /\
  ((?a. bvv = StackValue a op /\ ~is_word_type bt) \/
   (?a p. bvv = LocatedValue a p /\ p.ptr_location = LocMemory /\ op = p.ptr_operand)) /\
  read_result cx raw es = (INL bv,es) /\
  evaluate_type (get_tenv cx) bt = SOME btv /\
  read_result cx result es = (INL v,es) /\
  evaluate_type (get_tenv cx) ty = SOME tv /\ ~dynarray_free btv /\
  off + val_footprint tv v <= val_footprint btv bv /\
  sub_layout btv bv off tv v /\ eval_operand dst s = SOME address /\
  (!w. eval_operand op s = SOME w ==> w2n address = w2n w + off) ==>
  intcall_vv_provenance ce cx ty sa sb es result
    (LocatedValue ty (mk_ptr dst LocMemory)) s
Proof
  strip_tac >>
  `?w. eval_operand op s = SOME w` by
    metis_tac[intcall_vv_provenance_memory_operand] >>
  qpat_x_assum `intcall_vv_provenance _ _ _ _ _ _ _ _ _`
    (mp_tac o REWRITE_RULE [intcall_vv_provenance_def]) >>
  strip_tac >>
  qpat_x_assum `!op. _` (qspec_then `op` mp_tac) >> simp[] >>
  strip_tac >>
  simp[intcall_vv_provenance_def, mk_ptr_def] >>
  rpt strip_tac >> gvs[]
  >>~- ([`FLOOKUP s.vs_allocas aid = SOME (b,sz)`],
      disj1_tac >> qexistsl_tac [`aid`,`b`,`sz`] >>
      simp[] >> first_assum ACCEPT_TAC) >>
  rename1 `lookup_var root s = SOME rootword` >>
  ntac 3 disj2_tac >>
  qexistsl_tac [`n`,`sz`,`entry`,`root`,`rootword`,`k+off`] >>
  simp[] >>
  gvs[sub_layout_def] >> rpt strip_tac >>
  first_x_assum drule >> strip_tac >>
  first_x_assum drule >> pure_rewrite_tac[arithmeticTheory.ADD_ASSOC] >>
  disch_then ACCEPT_TAC
QED
