(* Observe written footprints through final allocation-site ownership. *)
Theory bodyIntCallFamStmtLogSuffixFootprint
Ancestors abiDecoderFrame venomState finite_map list arithmetic

Theorem intcall_footprint_allocation_frame:
  abi_decode_footprint_frame fp s u /\
  (!b n. MEM (b,n) fp ==>
    ?aid base size. first <= aid /\ aid < last /\
      FLOOKUP t.vs_allocas aid = SOME (base,size) /\
      base <= b /\ b+n <= base+size) ==>
  !a k. (!aid base size. first <= aid /\ aid < last /\
    FLOOKUP t.vs_allocas aid = SOME (base,size) ==>
    a+k <= base \/ base+size <= a) ==>
  mem_bytes_at a k u.vs_memory = mem_bytes_at a k s.vs_memory
Proof
  rpt strip_tac >> irule abi_decode_footprint_frame_slice >>
  goal_assum (drule_at Any) >>
  simp[abi_footprint_disjoint_def] >> rpt strip_tac >>
  first_x_assum drule >> strip_tac >>
  first_x_assum drule_all >> decide_tac
QED
