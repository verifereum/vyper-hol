(* Allocation credit for finite sets of actual scratch sites. *)
Theory abiSiteAllocation
Ancestors
  abiDecoderAllocation venomExecSemantics venomState finite_map pred_set
  arithmetic words

Definition abi_site_budget_def:
  abi_site_budget A b cap s <=>
    FINITE A /\ b + cap < dimword (:256) /\ b <= s.vs_alloca_next /\
    s.vs_alloca_next + 32 * CARD (A DIFF FDOM s.vs_allocas) <= b + cap /\
    (!id off sz. id IN A /\ FLOOKUP s.vs_allocas id = SOME (off,sz) ==>
      sz = 32 /\ b <= off /\ off + 32 <= s.vs_alloca_next) /\
    (!i j p q. i IN A /\ j IN A /\ i <> j /\
      FLOOKUP s.vs_allocas i = SOME (p,32) /\
      FLOOKUP s.vs_allocas j = SOME (q,32) ==>
      p + 32 <= q \/ q + 32 <= p)
End

Theorem abi_site_budget_interval:
  abi_site_budget (abi_decoder_ids first last) b cap s <=>
  abi_decoder_budget first last b cap s
Proof
  simp[abi_site_budget_def, abi_decoder_budget_def, abi_decoder_missing_def]
QED

Theorem abi_site_budget_site_bounds:
  abi_site_budget A b cap s /\ site IN A /\
  FLOOKUP s.vs_allocas site = SOME (slot,32) ==>
  b <= slot /\ slot+32 <= s.vs_alloca_next /\ s.vs_alloca_next <= b+cap /\
  b+cap < dimword (:256)
Proof
  simp_tac bool_ss [abi_site_budget_def] >> strip_tac >>
  qpat_x_assum `!id off sz. _ ==> sz = 32 /\ _`
    (qspecl_then [`site`,`slot`,`32`] mp_tac) >>
  asm_rewrite_tac[] >> decide_tac
QED

Theorem abi_site_budget_fields:
  t.vs_allocas = s.vs_allocas /\ t.vs_alloca_next = s.vs_alloca_next ==>
  (abi_site_budget A b cap t <=> abi_site_budget A b cap s)
Proof
  simp[abi_site_budget_def]
QED

Theorem abi_site_budget_update_var[simp]:
  abi_site_budget A b cap (update_var out w s) <=> abi_site_budget A b cap s
Proof
  simp[abi_site_budget_def, update_var_def]
QED

Theorem abi_site_missing_credit:
  FINITE A /\ id IN A /\ FLOOKUP s.vs_allocas id = NONE ==>
  CARD (A DIFF FDOM s.vs_allocas) =
    SUC (CARD ((A DIFF FDOM s.vs_allocas) DELETE id))
Proof
  strip_tac >>
  `id IN A DIFF FDOM s.vs_allocas` by gvs[FLOOKUP_DEF] >>
  `A DIFF FDOM s.vs_allocas =
    id INSERT ((A DIFF FDOM s.vs_allocas) DELETE id)` by
    (ASM_SET_TAC[]) >>
  pop_assum (fn th => once_rewrite_tac[th]) >> simp[CARD_INSERT]
QED

Theorem abi_site_budget_subset:
  abi_site_budget A b cap s /\ B SUBSET A ==>
  abi_site_budget B b cap s
Proof
  strip_tac >>
  `FINITE A /\ FINITE B` by metis_tac[abi_site_budget_def, SUBSET_FINITE] >>
  `CARD (B DIFF FDOM s.vs_allocas) <= CARD (A DIFF FDOM s.vs_allocas)` by
    (irule CARD_SUBSET >> simp[] >> ASM_SET_TAC[]) >>
  qpat_x_assum `abi_site_budget _ _ _ _` mp_tac >>
  rewrite_tac[abi_site_budget_def] >> strip_tac >>
  asm_rewrite_tac[] >> conj_tac >- decide_tac >>
  qpat_x_assum `B SUBSET A` mp_tac >>
  rewrite_tac[SUBSET_DEF] >> strip_tac >> metis_tac[]
QED

Theorem abi_site_budget_insert:
  abi_site_budget A b cap s /\ id IN A /\ FLOOKUP s.vs_allocas id = NONE ==>
  abi_site_budget A b cap
    (s with <|vs_allocas := s.vs_allocas |+ (id,(s.vs_alloca_next,32));
              vs_alloca_next := s.vs_alloca_next + 32|>)
Proof
  strip_tac >>
  `FINITE A` by metis_tac[abi_site_budget_def] >>
  drule_all abi_site_missing_credit >> strip_tac >>
  `A DIFF (id INSERT FDOM s.vs_allocas) =
    (A DIFF FDOM s.vs_allocas) DELETE id` by ASM_SET_TAC[] >>
  qpat_x_assum `abi_site_budget _ _ _ _` mp_tac >>
  rewrite_tac[abi_site_budget_def] >> strip_tac >>
  simp_tac (srw_ss()) [] >>
  conj_tac >- asm_rewrite_tac[] >>
  conj_tac >- asm_rewrite_tac[] >>
  conj_tac >- decide_tac >>
  conj_tac >- (asm_rewrite_tac[] >> decide_tac) >>
  conj_tac
  >- (map_every qx_gen_tac [`k`,`off`,`sz`] >>
      Cases_on `id = k` >> simp_tac std_ss [FLOOKUP_UPDATE] >>
      asm_rewrite_tac[] >> strip_tac
      >- (full_simp_tac std_ss [] >> decide_tac) >>
      qpat_x_assum `!id off sz. _ ==> sz = 32 /\ _` drule >>
      disch_then drule >> strip_tac >> asm_rewrite_tac[] >> decide_tac) >>
  map_every qx_gen_tac [`i`,`j`,`p`,`q`] >>
  Cases_on `i = id`
  >- (Cases_on `j = id` >> asm_simp_tac std_ss [FLOOKUP_UPDATE] >>
      rpt strip_tac >> full_simp_tac std_ss [] >>
      `q + 32 <= s.vs_alloca_next` by metis_tac[] >> decide_tac) >>
  Cases_on `j = id`
  >- (asm_simp_tac std_ss [FLOOKUP_UPDATE] >>
      rpt strip_tac >> full_simp_tac std_ss [] >>
      `p + 32 <= s.vs_alloca_next` by metis_tac[] >> decide_tac) >>
  asm_simp_tac std_ss [FLOOKUP_UPDATE] >> metis_tac[]
QED

Theorem abi_site_alloca32:
  abi_site_budget A b cap s /\ inst.inst_id IN A /\ inst.inst_outputs = [out] ==>
  ?t p. exec_alloca inst s (32w:bytes32) = OK t /\
    abi_site_budget A b cap t /\ lookup_var out t = SOME (n2w p) /\
    b <= p /\ p + 32 <= b + cap /\
    FLOOKUP t.vs_allocas inst.inst_id = SOME (p,32) /\
    (!id. id <> inst.inst_id ==>
      FLOOKUP t.vs_allocas id = FLOOKUP s.vs_allocas id) /\
    t.vs_memory = s.vs_memory /\ t.vs_call_ctx = s.vs_call_ctx /\
    t.vs_data_section = s.vs_data_section
Proof
  strip_tac >> Cases_on `FLOOKUP s.vs_allocas inst.inst_id`
  >- (drule_all abi_site_budget_insert >> strip_tac >>
      `FINITE A` by metis_tac[abi_site_budget_def] >>
      drule_all abi_site_missing_credit >> strip_tac >>
      `b <= s.vs_alloca_next /\ s.vs_alloca_next + 32 <= b + cap` by
        (qpat_assum `abi_site_budget A b cap s` mp_tac >>
         rewrite_tac[abi_site_budget_def] >> strip_tac >> decide_tac) >>
      simp_tac (srw_ss()) [exec_alloca_def, LET_THM, dimword_def,
        fcpLib.INDEX_CONV ``dimindex (:256)``] >> asm_rewrite_tac[] >>
      simp_tac (srw_ss()) [] >>
      qexists_tac `s.vs_alloca_next` >>
      asm_simp_tac (srw_ss()) [abi_site_budget_update_var, update_var_def,
        lookup_var_def, FLOOKUP_UPDATE] >>
      rpt strip_tac >> asm_simp_tac std_ss []) >>
  rename1 `SOME entry` >> PairCases_on `entry` >>
  `entry1 = 32 /\ b <= entry0 /\ entry0 + 32 <= s.vs_alloca_next` by
    (qpat_assum `abi_site_budget A b cap s` mp_tac >>
     rewrite_tac[abi_site_budget_def] >> strip_tac >> metis_tac[]) >>
  `entry0 + 32 <= b + cap` by
    (qpat_assum `abi_site_budget A b cap s` mp_tac >>
     rewrite_tac[abi_site_budget_def] >> strip_tac >> decide_tac) >>
  simp_tac (srw_ss()) [exec_alloca_def] >> asm_rewrite_tac[] >>
  simp_tac (srw_ss()) [] >>
  qexists_tac `entry0` >>
  asm_simp_tac (srw_ss()) [abi_site_budget_update_var, update_var_def,
    lookup_var_def, FLOOKUP_UPDATE]
QED

Theorem abi_site_budget_frontier_full:
  abi_site_budget A b cap s /\ s.vs_alloca_next = b + cap /\ id IN A ==>
  ?p. FLOOKUP s.vs_allocas id = SOME (p,32)
Proof
  strip_tac >> Cases_on `FLOOKUP s.vs_allocas id`
  >- (`FINITE A` by metis_tac[abi_site_budget_def] >>
      drule_all abi_site_missing_credit >> strip_tac >>
      qpat_x_assum `abi_site_budget _ _ _ _` mp_tac >>
      rewrite_tac[abi_site_budget_def] >> strip_tac >>
      spose_not_then kall_tac >> decide_tac) >>
  rename1 `SOME entry` >> PairCases_on `entry` >>
  qpat_x_assum `abi_site_budget _ _ _ _` mp_tac >>
  rewrite_tac[abi_site_budget_def] >> strip_tac >>
  `entry1 = 32` by metis_tac[] >> asm_rewrite_tac[] >>
  qexists_tac `entry0` >> asm_rewrite_tac[]
QED

Theorem abi_site_alloca32_full_reuse:
  abi_site_budget A b cap s /\ s.vs_alloca_next = b + cap /\
  inst.inst_id IN A /\ inst.inst_outputs = [out] ==>
  ?p. exec_alloca inst s (32w:bytes32) = OK (update_var out (n2w p) s) /\
    abi_site_budget A b cap (update_var out (n2w p) s) /\
    b <= p /\ p + 32 <= b + cap /\
    (update_var out (n2w p) s).vs_alloca_next = b + cap
Proof
  strip_tac >> drule_all abi_site_budget_frontier_full >> strip_tac >>
  `b <= p /\ p + 32 <= b + cap` by
    (qpat_assum `abi_site_budget _ _ _ _` mp_tac >>
     rewrite_tac[abi_site_budget_def] >> strip_tac >> metis_tac[]) >>
  qexists_tac `p` >>
  asm_simp_tac (srw_ss()) [exec_alloca_def, abi_site_budget_update_var] >>
  simp_tac (srw_ss()) [update_var_def] >> asm_rewrite_tac[]
QED
