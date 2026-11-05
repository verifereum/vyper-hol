(* Actual compiler allocation sites fit the ordinary function allocation charge. *)
Theory abiSiteCaller
Ancestors
  abiSiteAllocation abiDecoderSiteCharge abiCallerAllocation exprLoweringProps
  venomMemDefs venomState finite_map pred_set arithmetic words

Theorem abi_site_budget_of_alloca_inv:
  FINITE A /\ alloca_inv s /\
  s.vs_alloca_next + 32 * CARD (A DIFF FDOM s.vs_allocas) < dimword (:256) /\
  (!id off sz. id IN A /\ FLOOKUP s.vs_allocas id = SOME (off,sz) ==> sz = 32) ==>
  abi_site_budget A 0 (s.vs_alloca_next + 32 * CARD (A DIFF FDOM s.vs_allocas)) s
Proof
  rewrite_tac[abi_site_budget_def, alloca_inv_def,
    alloca_next_valid_def, allocas_non_overlapping_def] >>
  rpt strip_tac >> asm_simp_tac std_ss [] >> metis_tac[]
QED

Theorem abi_site_budget_of_room:
  FINITE A /\
  (!id. id IN A ==> ?i. MEM i (fn_insts func) /\ i.inst_id = id /\
    i.inst_opcode = ALLOCA /\ i.inst_operands = [Lit 32w]) /\
  alloca_room ctx func s /\ alloca_inv s /\
  (!id off sz. id IN A /\ FLOOKUP s.vs_allocas id = SOME (off,sz) ==> sz = 32) ==>
  abi_site_budget A 0 (s.vs_alloca_next + 32 * CARD (A DIFF FDOM s.vs_allocas)) s
Proof
  strip_tac >> drule_all alloca_sites_pending_charge >>
  disch_then (qspec_then `s` assume_tac) >>
  irule abi_site_budget_of_alloca_inv >> asm_rewrite_tac[] >>
  qpat_x_assum `alloca_room _ _ _` mp_tac >>
  rewrite_tac[alloca_room_def] >> strip_tac >> decide_tac
QED

Theorem abi_site_budget_emitted:
  cs_extends first last /\ fn_has_code first last func /\
  compiler_emits abi_decoder_alloc_shape first last /\
  alloca_room ctx func s /\ alloca_inv s /\
  (!id off sz. id IN abi_decoder_emitted_sites lo hi first last /\
    FLOOKUP s.vs_allocas id = SOME (off,sz) ==> sz = 32) ==>
  abi_site_budget (abi_decoder_emitted_sites lo hi first last) 0
    (s.vs_alloca_next + 32 * CARD
      (abi_decoder_emitted_sites lo hi first last DIFF FDOM s.vs_allocas)) s
Proof
  strip_tac >> drule_all abi_decoder_emitted_sites_pending_charge >>
  disch_then (qspecl_then [`s`,`lo`,`hi`] assume_tac) >>
  irule abi_site_budget_of_alloca_inv >> asm_simp_tac std_ss [] >>
  conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac >- irule abiDecoderSiteMembershipTheory.abi_decoder_emitted_sites_finite >>
  qpat_x_assum `alloca_room _ _ _` mp_tac >>
  rewrite_tac[alloca_room_def] >> strip_tac >> decide_tac
QED

Theorem abi_site_budget_live_separation:
  abi_site_budget A b cap s /\ alloca_inv s /\
  FLOOKUP s.vs_allocas live = SOME (loff,len) /\ ~(live IN A) /\
  loff <= p /\ p + n <= loff + len ==>
  abi_footprint_disjoint p n (abi_decoder_child_scratch A b cap s)
Proof
  strip_tac >> irule abi_caller_allocation_scratch >>
  goal_assum (drule_at Any) >> asm_rewrite_tac[] >>
  qpat_x_assum `abi_site_budget _ _ _ _` mp_tac >>
  rewrite_tac[abi_site_budget_def] >> strip_tac >> asm_rewrite_tac[] >>
  conj_tac >- decide_tac >> qexistsl_tac [`len`,`live`,`loff`] >> asm_rewrite_tac[]
QED
