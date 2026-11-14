(* Proof-only inhabitants of zero-size layouts. *)
Theory externalReturnZeroWitness
Ancestors externalReturnZeroWidening valueEncodingProofs valueEncoding valueEncodingDefs vyperValue vyperTyping
  vyperTypeArgFits vyperTypeSystem

Theorem return_zero_widening_witness:
  type_widens_to tenv sty dty /\
  evaluate_type tenv sty = SOME stv /\
  evaluate_type tenv dty = SOME dtv /\
  type_memory_size stv = 0 /\ type_memory_size dtv = 0 ==>
  ?z. value_has_type stv z /\ value_has_type dtv z /\
    val_wf stv z /\ val_wf dtv z /\
    (!p mem. val_in_memory stv z p mem) /\
    (!p mem. val_in_memory dtv z p mem)
Proof
  strip_tac >>
  `default_value stv = default_value dtv` by
    (gvs[type_widens_to_def] >> metis_tac[arg_type_fits_default_value]) >>
  qexists_tac `default_value stv` >> metis_tac[return_zero_default]
QED
