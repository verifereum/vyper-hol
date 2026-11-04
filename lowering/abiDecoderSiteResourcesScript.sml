(* Resource credit for actual generated ALLOCA sites, including site reuse. *)
Theory abiDecoderSiteResources
Ancestors
  abiDecoderCode abiDecoderFootprint abiCallerAllocation localPtrsProps
  finite_map pred_set arithmetic words

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
