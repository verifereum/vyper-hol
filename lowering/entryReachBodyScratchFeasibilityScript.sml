(* Exact all-instruction-site headroom required by the decoder interface. *)
Theory entryReachBodyScratchFeasibility
Ancestors
  entryReachBodyDecoderBudget abiDecoderAllocation finite_map pred_set
  arithmetic words

Theorem entry_decoder_fresh_budget_necessary:
  !first last b cap s.
  first <= last /\
  (!id. first <= id /\ id < last ==> id NOTIN FDOM s.vs_allocas) /\
  abi_decoder_budget first last b cap s ==>
  s.vs_alloca_next + 32 * (last - first) < dimword (:256)
Proof
  rpt gen_tac >> strip_tac >>
  `abi_decoder_missing first last s = count last DIFF count first` by
    (simp[abi_decoder_missing_def, abi_decoder_ids_def, EXTENSION] >>
     metis_tac[arithmeticTheory.NOT_LESS]) >>
  `count last INTER count first = count first` by
    (simp[EXTENSION] >> decide_tac) >>
  `CARD (abi_decoder_missing first last s) = last - first` by
    simp[CARD_DIFF] >>
  qpat_x_assum `abi_decoder_budget _ _ _ _ _` mp_tac >>
  pure_rewrite_tac[abi_decoder_budget_def] >> strip_tac >>
  qpat_x_assum `CARD _ = _` SUBST_ALL_TAC >>
  qpat_x_assum `_ + 32 * _ <= _` mp_tac >>
  qpat_x_assum `b + cap < _` mp_tac >> decide_tac
QED

Theorem entry_decoder_fresh_budget_feasible:
  !first last s.
  first <= last /\
  (!id. first <= id /\ id < last ==> id NOTIN FDOM s.vs_allocas) ==>
  ((?b cap. abi_decoder_budget first last b cap s) <=>
   s.vs_alloca_next + 32 * (last - first) < dimword (:256))
Proof
  rpt gen_tac >> strip_tac >> eq_tac
  >- (strip_tac >> drule_all entry_decoder_fresh_budget_necessary >> simp[]) >>
  strip_tac >> drule_all entry_decoder_fresh_budget >> metis_tac[]
QED
