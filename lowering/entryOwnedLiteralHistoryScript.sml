(* Literal allocation-size transport at the actual owned decoder endpoint. *)
Theory entryOwnedLiteralHistory
Ancestors
  abiAllocationHistory calldataMemberResourceFrame

Theorem owned_member_literal_history:
  abi_alloca_history (fn_insts fn) s /\
  calldata_member_resource_frame ctx fn site limit_st lo hi live p len s t scratch ==>
  abi_alloca_history (fn_insts fn) t
Proof
  simp_tac bool_ss [calldata_member_resource_frame_def] >> strip_tac >>
  rewrite_tac[abi_alloca_history_def] >> rpt strip_tac >>
  Cases_on `lo <= id /\ id < hi`
  >- (qpat_x_assum `calldata_member_own fn lo hi t` mp_tac >>
      rewrite_tac[calldata_member_own_def] >>
      disch_then (qspecl_then [`id`,`off`,`sz`] mp_tac) >>
      simp[] >> strip_tac >>
      qexistsl [`ins`, `32w`] >> simp[wordsTheory.dimword_def]) >>
  `id < lo \/ hi <= id` by decide_tac >>
  `FLOOKUP s.vs_allocas id = SOME (off,sz)` by metis_tac[] >>
  fs[abi_alloca_history_def]
QED
