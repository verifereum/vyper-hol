(* A symbolic unfolding equation for the actual bounded DFT worklist loop. *)
Theory venomDftEval
Ancestors dftDefs arithmetic

Theorem dft_loop_run_fuel_unfold:
  !step fuel state.
    dft_loop_run_fuel step fuel state =
    if fuel = 0 \/ SND (SND state) then state
    else dft_loop_run_fuel step (fuel - 1) (step state)
Proof
  rpt gen_tac >> Cases_on `fuel` >> simp[dft_loop_run_fuel_def]
QED
