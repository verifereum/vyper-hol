(* A footprint-local producer supplies heterogeneous traversal without
   changing its ambient reserve or selecting a second execution endpoint. *)
Theory entryReachBodyCanonicalProducerBridge
Ancestors
  entryReachBodyCanonicalArrayChild entryReachBodyCanonicalMembers
  abiEncoderRegisteredEffect pred_set

Theorem array_child_result_member[local]:
  array_child_result ctx fn oid root extent sites ids b cap site limit_st
    st last d tv v s t /\ ids SUBSET sites ==>
  canonical_member_result ctx fn oid root extent sites b cap site limit_st
    st last d tv v s t
Proof
  simp_tac bool_ss [array_child_result_def, canonical_member_result_def] >>
  strip_tac >> asm_rewrite_tac[] >>
  irule abi_encoder_registered_effect_enlarge >>
  qexistsl_tac [`ids`,`[(d,type_memory_size tv)]`] >> simp[]
QED

Theorem array_child_producer_member:
  array_child_producer ce env ty tv av v ctx fn oid root extent sites b cap site limit_st ==>
  canonical_member_child ce env ty tv av v ctx fn oid root extent sites b cap site limit_st
Proof
  simp_tac bool_ss [array_child_producer_def, canonical_member_child_def] >>
  strip_tac >> rpt gen_tac >> strip_tac >>
  first_x_assum drule_all >> disch_then (qx_choose_then `t` assume_tac) >>
  qexists_tac `t` >> irule array_child_result_member >>
  goal_assum (drule_at Any) >> simp[]
QED
