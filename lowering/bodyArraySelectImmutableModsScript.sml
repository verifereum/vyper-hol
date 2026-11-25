(* Linked selection of an immutable array element at its qualified owner. *)
Theory bodyArraySelectImmutableMods
Ancestors
  bodyArrayImmutableSelectEndpointMods

Theorem array_select_immutable_mods:
  array_nocopy_cut_mods (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
    cenv cx ty obj idx et bd st0 (es,s0,G0,tn0)
    (sa,sm,st2,sb,LocatedValue (ArrayT et bd) p,iop,dst,LocCode)
    (shadow_sa,shadow_sm,shadow_st2,shadow_sb)
    (gs1,mid,PlaceR (ImmutablePlace src id path),s,G1,tn1)
    (gs2,fin,IntV i,it,Gi,tni) /\
  contract_inv mods exps ctx cenv cx /\ expr_sim_inv_mods mods cenv cx env fin /\
  p.ptr_location = LocCode /\ expr_type obj = ArrayT et bd /\
  post_value_type cenv obj = ArrayT et bd /\
  post_value_type cenv idx = expr_type idx /\
  is_word_type (expr_type idx) /\
  (!l. p.ptr_operand <> Label l /\ iop <> Label l) /\
  ALOOKUP cenv.ce_modules src = SOME tops /\
  FLOOKUP cenv.ce_module_vars (src,id) = SOME (ImmutableLoc off) /\
  ALOOKUP fin.immutables cx.txn.target = SOME imms /\
  FLOOKUP (get_source_immutables src imms) id = SOME (itv,iv) /\
  mem_path_offset itv path = SOME (k,ArrayTV etv bd) /\
  evaluate_subscripts itv iv path = INL (ArrayV av) /\
  off + type_memory_size itv < dimword (:256) /\
  value_has_type itv iv /\ well_formed_type_value itv /\
  value_has_type (ArrayTV etv bd) (ArrayV av) /\
  evaluate_type (get_tenv cx) et = SOME etv /\
  evaluate_type (get_tenv cx) (ArrayT et bd) = SOME (ArrayTV etv bd) /\
  type_memory_bytes cenv et = type_memory_size etv /\
  eval_operand p.ptr_operand it = SOME (n2w (off+k)) /\
  eval_operand iop it = SOME iw /\
  i = (if is_signed_type (expr_type idx) then w2i iw else &(w2n iw)) ==>
  array_select_outcome_mods (DF,lo,d,ctx,shadow_ctx,PG,func)
    cenv cx et obj idx et bd st0 (es,s0,G0,tn0) (sa,sb,dst,LocCode)
    (PlaceR (ImmutablePlace src id path),IntV i) (fin,it,Gi,tni)
Proof
  strip_tac >> irule immutable_select_endpoint_mods >> metis_tac[]
QED
