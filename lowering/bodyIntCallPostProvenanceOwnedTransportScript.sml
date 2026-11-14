(* Allocation certificates survive framing and selection without inspecting execution. *)
Theory bodyIntCallPostProvenanceOwnedTransport
Ancestors bodyIntCallProducerInterface

Theorem intcall_fresh_allocation_transport:
  FLOOKUP u.vs_allocas aid = SOME (b,sz) /\
  FLOOKUP t.vs_allocas aid = FLOOKUP u.vs_allocas aid /\
  lo <= aid /\ aid < hi /\ lo' <= lo /\ hi <= hi' /\
  (!n lb lsz. local_region ce scopes0 u n lb lsz ==>
     b+sz <= lb \/ lb+lsz <= b) /\
  (!n lb lsz. local_region ce scopes1 t n lb lsz ==>
     local_region ce scopes0 u n lb lsz) /\
  b <= address /\ address + footprint <= b+sz ==>
  ?a base size. FLOOKUP t.vs_allocas a = SOME (base,size) /\
    lo' <= a /\ a < hi' /\
    base <= address /\ address + footprint <= base+size /\
    (!n lb lsz. local_region ce scopes1 t n lb lsz ==>
       base+size <= lb \/ lb+lsz <= base)
Proof
  strip_tac >> qexistsl [`aid`, `b`, `sz`] >>
  simp[] >> metis_tac[]
QED

Theorem intcall_fresh_allocation_selected:
  FLOOKUP u.vs_allocas aid = SOME (b,cap) /\
  FLOOKUP t.vs_allocas aid = FLOOKUP u.vs_allocas aid /\
  lo <= aid /\ aid < hi /\ lo' <= lo /\ hi <= hi' /\
  (!n lb lsz. local_region ce scopes0 u n lb lsz ==>
     b+cap <= lb \/ lb+lsz <= b) /\
  (!n lb lsz. local_region ce scopes1 t n lb lsz ==>
     local_region ce scopes0 u n lb lsz) /\
  address = b+k /\ k+footprint <= cap ==>
  ?a base size. FLOOKUP t.vs_allocas a = SOME (base,size) /\
    lo' <= a /\ a < hi' /\
    base <= address /\ address + footprint <= base+size /\
    (!n lb lsz. local_region ce scopes1 t n lb lsz ==>
       base+size <= lb \/ lb+lsz <= base)
Proof
  strip_tac >>
  `b <= address /\ address + footprint <= b+cap` by decide_tac >>
  drule_all intcall_fresh_allocation_transport >> simp[]
QED
