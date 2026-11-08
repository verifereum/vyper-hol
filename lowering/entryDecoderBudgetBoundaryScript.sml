(* Dense decoder credit counts instruction IDs, not allocation sites. *)
Theory entryDecoderBudgetBoundary
Ancestors
  abiDecoderAllocation actualAllocCredit pred_set arithmetic words

Theorem abi_decoder_ids_card:
  CARD (abi_decoder_ids first last) = last - first
Proof
  `abi_decoder_ids first last = count last DIFF count first` by
    (rw[abi_decoder_ids_def, EXTENSION] >> decide_tac) >>
  `count last INTER count first = count (MIN last first)` by
    (rw[EXTENSION] >> decide_tac) >>
  simp[CARD_DIFF_EQN, MIN_DEF]
QED

Theorem abi_decoder_missing_card_unallocated:
  (!id. id IN abi_decoder_ids first last ==>
    FLOOKUP s.vs_allocas id = NONE) ==>
  CARD (abi_decoder_missing first last s) = last - first
Proof
  strip_tac >>
  `abi_decoder_missing first last s = abi_decoder_ids first last` by
    (rw[abi_decoder_missing_def, EXTENSION] >>
     eq_tac >- simp[] >> strip_tac >> simp[] >>
     first_x_assum drule >> simp[finite_mapTheory.FLOOKUP_DEF] >>
     Cases_on `x IN FDOM s.vs_allocas` >> simp[]) >>
  simp[abi_decoder_ids_card]
QED

(* Arithmetic diagnostic only: not a counterexample to the entry theorem. *)
Theorem weighted_credit_does_not_supply_dense_margin:
  dimword (:256) - 32 + 0 < dimword (:256) /\
  ~(dimword (:256) - 32 + 32 * 1 < dimword (:256))
Proof
  EVAL_TAC >> simp[]
QED
