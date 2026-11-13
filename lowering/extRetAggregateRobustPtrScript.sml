(* Robust aggregate assembly. Exterior framing and equal-layout relocation
 * are supplied by robustCopyTransportPtr, not reproved here.
 * Exterior framing requires val_wf and disjointness of writes from every
 * byte in [p,p+val_footprint tv v), with memory and taint unchanged outside
 * writes. Equal-layout relocation requires val_wf, footprint <= window,
 * equal copied bytes and pointwise translated taint membership. Neither
 * fact asserts cleanliness of padding or supports a changed type layout. *)
Theory extRetAggregateRobustPtr
Ancestors
  typedCopyTuplePtr robustCopyTransportPtr valueEncoding exprSimMemoryTransport
  bodyPtrDefs list arithmetic

Theorem tuple_in_memory_robust_from_elements:
  !vals tvs base tn mem.
  LENGTH vals = LENGTH tvs /\
  (!i m. i < LENGTH tvs /\ mem_agree_outside tn mem m ==>
    val_in_memory (EL i tvs) (EL i vals)
      ((base:num) + SUM (MAP type_memory_size (TAKE i tvs))) m) ==>
  !m. mem_agree_outside tn mem m ==>
    tuple_in_memory vals tvs base m
Proof
  rpt strip_tac >> irule tuple_in_memory_from_elements >>
  simp[]
QED
