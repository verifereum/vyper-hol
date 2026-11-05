(* Scratch credit for a fresh decoder instruction interval. *)
Theory entryReachBodyDecoderBudget
Ancestors
  abiDecoderAllocation finite_map pred_set arithmetic words

Theorem entry_decoder_interval_card[local]:
  first <= last ==>
  CARD (abi_decoder_ids first last) = last - first
Proof
  strip_tac >>
  `abi_decoder_ids first last = count last DIFF count first` by
    (simp[abi_decoder_ids_def, EXTENSION] >> decide_tac) >>
  `count last INTER count first = count first` by
    (simp[EXTENSION] >> decide_tac) >>
  simp[CARD_DIFF]
QED

Theorem entry_decoder_fresh_budget:
  first <= last /\
  (!id. first <= id /\ id < last ==> id NOTIN FDOM s.vs_allocas) /\
  s.vs_alloca_next + 32 * (last - first) < dimword (:256) ==>
  abi_decoder_budget first last s.vs_alloca_next (32 * (last - first)) s
Proof
  strip_tac >> irule abi_decoder_budget_empty >>
  simp[entry_decoder_interval_card] >> rpt strip_tac >>
  gvs[abi_decoder_ids_def, finite_mapTheory.FLOOKUP_DEF] >>
  metis_tac[]
QED
