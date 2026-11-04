(* Resource credit for actual generated ALLOCA sites, including site reuse. *)
Theory abiDecoderSiteResources
Ancestors
  abiDecoderCode abiDecoderFootprint abiDecoderFrame abiCallerAllocation localPtrsProps
  finite_map pred_set arithmetic words list rich_list venomExecSemantics venomState venomMemDefs

Definition abi_decoder_sites_def:
  abi_decoder_sites first last code =
    {id | first <= id /\ id < last /\
      ?i. abi_decoder_code_member i code /\ i.inst_id = id /\
          i.inst_opcode = ALLOCA}
End

Definition abi_decoder_site_budget_def:
  abi_decoder_site_budget ids cap s <=>
    FINITE ids /\ alloca_inv s /\ cap < dimword (:256) /\
    s.vs_alloca_next + 32 * CARD (ids DIFF FDOM s.vs_allocas) <= cap /\
    (!id p sz. id IN ids /\ FLOOKUP s.vs_allocas id = SOME (p,sz) ==>
       sz = 32)
End

Theorem abi_decoder_sites_member[simp]:
  id IN abi_decoder_sites first last code <=>
  first <= id /\ id < last /\
  ?i. abi_decoder_code_member i code /\ i.inst_id = id /\
      i.inst_opcode = ALLOCA
Proof
  simp[abi_decoder_sites_def]
QED

Theorem abi_decoder_sites_finite[simp]:
  FINITE (abi_decoder_sites first last code)
Proof
  irule SUBSET_FINITE_I >> qexists_tac `count last` >>
  simp[SUBSET_DEF]
QED

Theorem abi_decoder_sites_split:
  first <= mid /\ mid <= last ==>
  abi_decoder_sites first last code =
    abi_decoder_sites first mid code UNION abi_decoder_sites mid last code
Proof
  strip_tac >> simp[EXTENSION] >> gen_tac >>
  Cases_on `x < mid` >> simp[] >> decide_tac
QED

Theorem abi_decoder_sites_disjoint:
  DISJOINT (abi_decoder_sites first mid code)
           (abi_decoder_sites mid last code)
Proof
  simp[DISJOINT_DEF, EXTENSION] >> metis_tac[LESS_EQUAL_ANTISYM, NOT_LESS]
QED

Theorem abi_decoder_sites_nonalloc:
  (!i. abi_decoder_code_member i code /\ i.inst_id = id ==>
       i.inst_opcode <> ALLOCA) ==>
  id NOTIN abi_decoder_sites first last code
Proof
  simp[] >> metis_tac[]
QED

Theorem abi_decoder_site_budget_restrict:
  abi_decoder_site_budget ids cap s /\ sub SUBSET ids ==>
  abi_decoder_site_budget sub cap s
Proof
  rw[abi_decoder_site_budget_def]
  >- metis_tac[SUBSET_FINITE]
  >- (`sub DIFF FDOM s.vs_allocas SUBSET ids DIFF FDOM s.vs_allocas` by
        (simp[SUBSET_DEF] >> metis_tac[SUBSET_DEF]) >>
      `CARD (sub DIFF FDOM s.vs_allocas) <=
       CARD (ids DIFF FDOM s.vs_allocas)` by
        (irule CARD_SUBSET >> simp[]) >> decide_tac)
  >> metis_tac[SUBSET_DEF]
QED

Theorem abi_decoder_site_budget_intro:
  FINITE ids /\ alloca_inv s /\
  s.vs_alloca_next + 32 * CARD (ids DIFF FDOM s.vs_allocas) < dimword (:256) /\
  (!id p sz. id IN ids /\ FLOOKUP s.vs_allocas id = SOME (p,sz) ==> sz = 32)
  ==>
  abi_decoder_site_budget ids
    (s.vs_alloca_next + 32 * CARD (ids DIFF FDOM s.vs_allocas)) s
Proof
  pure_rewrite_tac[abi_decoder_site_budget_def] >>
  strip_tac >> asm_rewrite_tac[LESS_EQ_REFL]
QED

Theorem abi_decoder_site_budget_empty[simp]:
  abi_decoder_site_budget {} cap s <=>
  alloca_inv s /\ cap < dimword (:256) /\ s.vs_alloca_next <= cap
Proof
  simp[abi_decoder_site_budget_def]
QED

Theorem abi_decoder_site_budget_fields:
  abi_decoder_site_budget ids cap s /\
  t.vs_allocas = s.vs_allocas /\ t.vs_alloca_next = s.vs_alloca_next ==>
  abi_decoder_site_budget ids cap t
Proof
  strip_tac >>
  `alloca_inv s` by fs[abi_decoder_site_budget_def] >>
  `alloca_inv t` by (irule alloca_inv_fields >> qexists_tac `s` >> simp[]) >>
  qpat_x_assum `abi_decoder_site_budget _ _ _` mp_tac >>
  pure_rewrite_tac[abi_decoder_site_budget_def] >>
  strip_tac >> asm_rewrite_tac[]
QED

Theorem abi_decoder_site_missing_credit[local]:
  FINITE ids /\ id IN ids /\ FLOOKUP s.vs_allocas id = NONE ==>
  CARD (ids DIFF FDOM s.vs_allocas) =
    SUC (CARD ((ids DIFF FDOM s.vs_allocas) DELETE id))
Proof
  strip_tac >>
  `id IN ids DIFF FDOM s.vs_allocas` by
    (gvs[FLOOKUP_DEF] >> Cases_on `id IN FDOM s.vs_allocas` >> gvs[]) >>
  `ids DIFF FDOM s.vs_allocas =
    id INSERT ((ids DIFF FDOM s.vs_allocas) DELETE id)` by
    (fs[EXTENSION] >> metis_tac[]) >>
  pop_assum (fn th => once_rewrite_tac[th]) >> simp[CARD_INSERT]
QED

Theorem abi_decoder_site_budget_insert[local]:
  abi_decoder_site_budget ids cap s /\ id IN ids /\
  FLOOKUP s.vs_allocas id = NONE /\
  alloca_inv (s with <|vs_allocas := s.vs_allocas |+ (id,(s.vs_alloca_next,32));
                      vs_alloca_next := s.vs_alloca_next + 32|>) ==>
  abi_decoder_site_budget ids cap
    (s with <|vs_allocas := s.vs_allocas |+ (id,(s.vs_alloca_next,32));
              vs_alloca_next := s.vs_alloca_next + 32|>)
Proof
  strip_tac >>
  `FINITE ids` by fs[abi_decoder_site_budget_def] >>
  drule_all abi_decoder_site_missing_credit >> strip_tac >>
  `ids DIFF (id INSERT FDOM s.vs_allocas) =
    (ids DIFF FDOM s.vs_allocas) DELETE id` by
    (simp[EXTENSION] >> metis_tac[]) >>
  qpat_x_assum `abi_decoder_site_budget _ _ _` mp_tac >>
  pure_rewrite_tac[abi_decoder_site_budget_def] >> strip_tac >>
  simp_tac (srw_ss()) [Excl "CARD_DIFF", Excl "CARD_DIFF_EQN"] >>
  pure_asm_rewrite_tac[] >> rewrite_tac[] >>
  conj_tac >- decide_tac >>
  qpat_x_assum `CARD _ = _` kall_tac >>
  qpat_x_assum `_ DIFF (_ INSERT _) = _` kall_tac >>
  rpt gen_tac >> strip_tac >>
  Cases_on `id' = id` >> gvs[FLOOKUP_UPDATE] >> metis_tac[]
QED

Theorem abi_decoder_site_budget_update_var[simp]:
  abi_decoder_site_budget ids cap (update_var out w s) <=>
  abi_decoder_site_budget ids cap s
Proof
  simp[abi_decoder_site_budget_def, alloca_inv_def,
       allocas_non_overlapping_def, alloca_next_valid_def, update_var_def]
QED

Theorem abi_decoder_site_allocation:
  abi_decoder_site_budget ids cap s /\ id IN child /\ child SUBSET ids /\
  inst.inst_id = id /\ inst.inst_outputs = [out] ==>
  ?t p base len. exec_alloca inst s (32w:bytes32) = OK t /\
    abi_decoder_site_budget ids cap t /\
    lookup_var out t = SOME (n2w p) /\
    FLOOKUP t.vs_allocas id = SOME (p,32) /\
    MEM (base,len) (abi_decoder_child_scratch child 0 cap s) /\
    base <= p /\ p + 32 <= base + len
Proof
  strip_tac >>
  `id IN ids` by metis_tac[SUBSET_DEF] >>
  `FINITE ids /\ alloca_inv s` by fs[abi_decoder_site_budget_def] >>
  `FINITE child` by metis_tac[SUBSET_FINITE] >>
  Cases_on `FLOOKUP s.vs_allocas id`
  >- (`exec_alloca inst s (32w:bytes32) =
        OK (update_var out (n2w s.vs_alloca_next)
          (s with <|vs_allocas := s.vs_allocas |+ (id,(s.vs_alloca_next,32));
                    vs_alloca_next := s.vs_alloca_next + 32|>))` by
        simp[exec_alloca_def, dimword_def, fcpLib.INDEX_CONV ``dimindex (:256)``] >>
      `alloca_inv (update_var out (n2w s.vs_alloca_next)
          (s with <|vs_allocas := s.vs_allocas |+ (id,(s.vs_alloca_next,32));
                    vs_alloca_next := s.vs_alloca_next + 32|>))` by
        (drule_all alloca_inv_exec_alloca >> simp[]) >>
      `alloca_inv (s with
          <|vs_allocas := s.vs_allocas |+ (id,(s.vs_alloca_next,32));
            vs_alloca_next := s.vs_alloca_next + 32|>)` by
        (irule alloca_inv_fields >> goal_assum (drule_at Any) >>
         simp[update_var_def]) >>
      drule_all abi_decoder_site_budget_insert >> strip_tac >>
      `s.vs_alloca_next + 32 <= cap` by
        (qpat_x_assum `abi_decoder_site_budget ids cap s` kall_tac >>
         qpat_x_assum `abi_decoder_site_budget _ _ _` mp_tac >>
         pure_rewrite_tac[abi_decoder_site_budget_def] >> strip_tac >>
         qpat_x_assum `_ + 32 * _ <= cap` mp_tac >>
         simp_tac (srw_ss()) [] >> decide_tac) >>
      qexistsl_tac [`update_var out (n2w s.vs_alloca_next)
          (s with <|vs_allocas := s.vs_allocas |+ (id,(s.vs_alloca_next,32));
                    vs_alloca_next := s.vs_alloca_next + 32|>)`,
        `s.vs_alloca_next`, `s.vs_alloca_next`, `cap - s.vs_alloca_next`] >>
      simp[lookup_var_def, update_var_def, FLOOKUP_UPDATE,
           abi_decoder_child_scratch_def]) >>
  rename1 `SOME slot` >> PairCases_on `slot` >>
  `slot1 = 32` by (fs[abi_decoder_site_budget_def] >> metis_tac[]) >>
  gvs[] >>
  qexistsl_tac [`update_var out (n2w slot0) s`, `slot0`, `slot0`, `32`] >>
  simp[exec_alloca_def, lookup_var_def, update_var_def, FLOOKUP_UPDATE,
       abi_decoder_child_scratch_def, MEM_MAP] >>
  disj2_tac >> qexists_tac `inst.inst_id` >> simp[MEM_SET_TO_LIST]
QED

Theorem abi_decoder_sites_subset:
  first <= a /\ b <= last ==>
  abi_decoder_sites a b code SUBSET abi_decoder_sites first last code
Proof
  simp[SUBSET_DEF] >> rpt strip_tac >> simp[]
QED

Theorem abi_decoder_sites_outside:
  id < first \/ last <= id ==> id NOTIN abi_decoder_sites first last code
Proof
  simp[] >> metis_tac[NOT_LESS, LESS_EQ_ANTISYM]
QED

Theorem abi_decoder_site_generated_allocation:
  abi_decoder_code child child_end /\
  abi_decoder_code_member inst child_end /\
  ~abi_decoder_code_member inst child /\ inst.inst_opcode = ALLOCA /\
  abi_decoder_code_member inst code /\ abi_decoder_site_budget ids cap s /\
  abi_decoder_sites child.cs_next_id child_end.cs_next_id code SUBSET ids ==>
  ?out t p base len. inst.inst_outputs = [out] /\
    inst.inst_operands = [Lit 32w] /\
    exec_alloca inst s (32w:bytes32) = OK t /\
    abi_decoder_site_budget ids cap t /\ lookup_var out t = SOME (n2w p) /\
    FLOOKUP t.vs_allocas inst.inst_id = SOME (p,32) /\
    MEM (base,len) (abi_decoder_child_scratch
      (abi_decoder_sites child.cs_next_id child_end.cs_next_id code) 0 cap s) /\
    base <= p /\ p + 32 <= base + len
Proof
  strip_tac >> drule_all abi_decoder_code_alloca >> strip_tac >>
  `inst.inst_id IN abi_decoder_sites child.cs_next_id child_end.cs_next_id code`
    by (simp[] >> metis_tac[]) >>
  qpat_x_assum `abi_decoder_code _ _` kall_tac >>
  rpt (qpat_x_assum `abi_decoder_code_member _ _` kall_tac) >>
  qpat_x_assum `~abi_decoder_code_member _ _` kall_tac >>
  metis_tac[abi_decoder_site_allocation]
QED

Theorem abi_decoder_site_budget_frontier:
  abi_decoder_site_budget ids cap s ==>
  FINITE ids /\ alloca_inv s /\ s.vs_alloca_next <= cap /\ cap < dimword (:256)
Proof
  pure_rewrite_tac[abi_decoder_site_budget_def] >> strip_tac >>
  rpt conj_tac >> simp[] >> decide_tac
QED

Theorem abi_decoder_site_excludes_live:
  abi_decoder_site_budget ids cap s /\ child SUBSET ids /\ live NOTIN child /\
  FLOOKUP s.vs_allocas live = SOME (p,n) ==>
  abi_footprint_disjoint p n (abi_decoder_child_scratch child 0 cap s)
Proof
  strip_tac >> drule abi_decoder_site_budget_frontier >> strip_tac >>
  `FINITE child` by metis_tac[SUBSET_FINITE] >>
  irule abi_caller_allocation_scratch >>
  simp[] >> qexistsl_tac [`n`, `live`, `p`] >> simp[]
QED

Theorem abi_decoder_site_raw_resources:
  abi_decoder_site_budget ids cap s /\
  FLOOKUP s.vs_allocas source_id = SOME (source_base,source_cap) /\
  FLOOKUP s.vs_allocas output_id = SOME (d,outsz) /\
  source_id <> output_id /\ source_id NOTIN ids /\ output_id NOTIN ids /\
  source_base <= sb /\ sb + len <= source_base + source_cap ==>
  sb + len < dimword (:256) /\ d + outsz < dimword (:256) /\
  abi_footprint_disjoint d outsz (abi_decoder_child_scratch ids 0 cap s) /\
  abi_footprint_disjoint sb len
    ((d,outsz)::abi_decoder_child_scratch ids 0 cap s)
Proof
  strip_tac >> drule abi_decoder_site_budget_frontier >> strip_tac >>
  `sb + len <= s.vs_alloca_next` by
    (irule abi_caller_allocation_end >> simp[] >>
     qexistsl_tac [`source_cap`, `source_id`, `source_base`] >> simp[]) >>
  `d + outsz <= s.vs_alloca_next` by
    (irule abi_caller_allocation_end >> simp[] >>
     qexistsl_tac [`outsz`, `output_id`, `d`] >> simp[]) >>
  `abi_footprint_disjoint d outsz (abi_decoder_child_scratch ids 0 cap s)` by
    (irule abi_caller_allocation_scratch >>
     simp[] >> qexistsl_tac [`outsz`, `output_id`, `d`] >> simp[]) >>
  `abi_footprint_disjoint sb len (abi_decoder_child_scratch ids 0 cap s)` by
    (irule abi_caller_allocation_scratch >>
     simp[] >> qexistsl_tac [`source_cap`, `source_id`, `source_base`] >> simp[]) >>
  drule_all abi_caller_allocation_separate >> strip_tac >>
  fs[abi_footprint_disjoint_def] >> rpt strip_tac >>
  gvs[] >> metis_tac[LESS_EQ_TRANS, LESS_EQ_LESS_TRANS]
QED

Theorem abi_decoder_site_caller_raw_resources:
  FINITE ids /\ alloca_inv s /\
  s.vs_alloca_next + 32 * CARD (ids DIFF FDOM s.vs_allocas) < dimword (:256) /\
  (!id p sz. id IN ids /\ FLOOKUP s.vs_allocas id = SOME (p,sz) ==> sz = 32) /\
  FLOOKUP s.vs_allocas source_id = SOME (source_base,source_cap) /\
  FLOOKUP s.vs_allocas output_id = SOME (d,outsz) /\
  source_id <> output_id /\ source_id NOTIN ids /\ output_id NOTIN ids /\
  source_base <= sb /\ sb + len <= source_base + source_cap ==>
  sb + len < dimword (:256) /\ d + outsz < dimword (:256) /\
  abi_footprint_disjoint d outsz (abi_decoder_child_scratch ids 0
    (s.vs_alloca_next + 32 * CARD (ids DIFF FDOM s.vs_allocas)) s) /\
  abi_footprint_disjoint sb len ((d,outsz)::abi_decoder_child_scratch ids 0
    (s.vs_alloca_next + 32 * CARD (ids DIFF FDOM s.vs_allocas)) s)
Proof
  strip_tac >> drule_all abi_decoder_site_budget_intro >> strip_tac >>
  drule_all abi_decoder_site_raw_resources >> simp[]
QED
