(* Applicability probe: an inner array occupies a subregion of its outer
   argument allocation, not a separately allocated region at its own root. *)
Theory entryReachBodyNestedArrayPath
Ancestors
  entryReachBodyCanonicalBytesArray venomMemDefs finite_map arithmetic

Theorem nested_interior_not_allocation_root[local]:
  alloca_inv s /\ FLOOKUP s.vs_allocas owner = SOME (root,extent) /\
  root < cell /\ cell < root+extent /\ 0 < len ==>
  FLOOKUP s.vs_allocas aid <> SOME (cell,len)
Proof
  strip_tac >> strip_tac >>
  Cases_on `owner = aid`
  >- gvs[] >>
  `root+extent <= cell \/ cell+len <= root` by
    (qpat_x_assum `alloca_inv s`
       (strip_assume_tac o PURE_REWRITE_RULE
         [alloca_inv_def, allocas_non_overlapping_def]) >> metis_tac[]) >>
  decide_tac
QED

(* This refutes an attempted application of the old inner-array resource
   interface, not decoding and not the frozen entry-to-body obligation. *)
Theorem entry_nested_bytes_array_resource_obstruction:
  alloca_inv s /\ FLOOKUP s.vs_allocas owner = SOME (root,extent) /\
  root < cell /\ cell < root+extent /\ 0 < sz ==>
  ~entry_bytes_array_resources dst src maxn asz st
    (ctx,fn,site,cell,sz,b,cap,p,oid,capacity,s)
Proof
  strip_tac >> strip_tac >>
  qpat_x_assum `entry_bytes_array_resources _ _ _ _ _ _`
    (strip_assume_tac o PURE_REWRITE_RULE [entry_bytes_array_resources_def]) >>
  `0 < capacity` by decide_tac >>
  drule_all nested_interior_not_allocation_root >> metis_tac[]
QED
