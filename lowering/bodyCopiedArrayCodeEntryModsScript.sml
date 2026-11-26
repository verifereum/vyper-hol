(* Use the same store-entry transport for the qualified code unwrap. *)
Theory bodyCopiedArrayCodeEntryMods
Ancestors
  bodyCopiedArrayCutDefsMods bodyCopiedArrayCodePhysicalEndpointMods
  bodyCopiedArrayMaterializedEntryMods exprLoweringProps

Theorem copied_array_code_store_entry_mods:
  copied_alloc_cut_mods (DF,lo,d,ctx,shctx,PG,fn,shfn) ce cx
    (st0,es,sa,s0,G0,tn0) (obj,mid,raw,saved,et,bd,atv)
    (sm,s,G,tn) (k,a,Ga,ta) (l,src,sc,cvv,bvv) (q,w) /\
  bvv = LocatedValue tag p /\ p.ptr_location = LocCode /\
  ci_mono sa sm /\ ci_mono sm k ==>
  ?t Gl tl sw. copied_store_cut_mods (DF,lo,d,ctx,shctx,PG,fn,shfn) ce cx
    (st0,es,sa,s0,G0,tn0) (obj,mid,raw,saved,et,bd,atv)
    (sm,s,G,tn) (l,t,Gl,tl) (src,sw,sc,cvv) (q,w)
Proof
  strip_tac >>
  drule_all_then assume_tac copied_array_code_physical_endpoint_mods >>
  drule_all_then ACCEPT_TAC copied_array_materialized_store_entry_mods
QED
