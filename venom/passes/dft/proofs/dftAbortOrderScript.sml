(*
 * DFT keeps instructions that abort differently in their order (piece of
 * o1ContractDft).
 *
 * dft_block orders each aborting instruction after the whole previous run
 * of aborting instructions of another kind (dft_abort_kind, as
 * vyperlang/vyper#5336 does), so any two that are not
 * dft_abort_compatible stay in their original order.
 *)
Theory dftAbortOrder
Ancestors
  dftScheduleOrder dftDefs venomWf

Theorem dft_fn_fallible_order_kept:
  wf_function fn /\ fn_inst_wf fn ==>
  dft_fallible_order_kept fn (dft_fn fn)
Proof
  cheat
QED
