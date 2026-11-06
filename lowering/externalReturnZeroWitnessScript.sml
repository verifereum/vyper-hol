(* Proof-only inhabitants of zero-size layouts. *)
Theory externalReturnZeroWitness
Ancestors externalReturnZeroLayout valueEncoding vyperValue vyperTyping
  vyperTypeArgFits vyperTypeSystem

Theorem return_zero_default_mutual:
  (!tv. type_memory_size tv = 0 ==>
    value_has_type tv (default_value tv) /\ val_wf tv (default_value tv) /\
    !p mem. val_in_memory tv (default_value tv) p mem) /\
  (!ts. type_memory_size_list ts = 0 ==>
    values_have_types ts (MAP default_value ts) /\
    tuple_val_wf (MAP default_value ts) ts /\
    !p mem. tuple_in_memory (MAP default_value ts) ts p mem) /\
  (!fs. type_memory_size_fields fs = 0 ==>
    struct_has_type fs (MAP (\(n,t). (n,default_value t)) fs) /\
    fields_val_wf (MAP (\(n,t). (n,default_value t)) fs) fs /\
    !p mem. fields_in_memory (MAP (\(n,t). (n,default_value t)) fs) fs p mem)
Proof
  ho_match_mp_tac type_memory_size_ind >>
  simp[type_memory_size_def, default_value_def,
    default_value_tuple_MAP, default_value_struct_MAP,
    value_has_type_def, val_wf_def, val_in_memory_def]
QED

Theorem return_zero_default:
  type_memory_size tv = 0 ==>
  value_has_type tv (default_value tv) /\ val_wf tv (default_value tv) /\
  !p mem. val_in_memory tv (default_value tv) p mem
Proof
  metis_tac[return_zero_default_mutual]
QED

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
