(* Word conditionals enrich the selected success, not a second run. *)
Theory bodyIntCallWordProducer
Ancestors
  bodyIntCallProducerInterface exprSimIfExp

Theorem compile_ifexp_word_provenance:
  is_word_type ann /\
  compile_expr cenv ty (IfExp ann c a b) sa = (vv,sb) ==>
  intcall_vv_provenance cenv cx ann sa sb ee raw vv t
Proof
  strip_tac >> drule compile_expr_ifexp >> strip_tac >>
  gvs[] >> irule intcall_vv_provenance_word >> simp[]
QED

Theorem gas_outcome_word_ifexp_provenance:
  is_word_type ann /\
  compile_expr cenv ty (IfExp ann c a b) sa = (vv,sb) /\
  gas_outcome memory tops p source start Q R ==>
  gas_outcome memory tops p source start
    (\res ee t. Q res ee t /\
      intcall_vv_provenance cenv cx ann sa sb ee (raw res) vv t) R
Proof
  strip_tac >> ho_match_mp_tac gas_outcome_strengthen_witness >>
  simp[] >> rpt strip_tac >>
  irule compile_ifexp_word_provenance >> metis_tac[]
QED
