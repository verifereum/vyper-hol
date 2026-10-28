(* Exact outer DFT worklist cases, retaining the original process result. *)
Theory venomDftLoopCases
Ancestors
  dftDefs

Theorem dft_loop_step_done_tuple:
  !cfg lr func st work.
    dft_loop_step cfg lr func (st,work,T) = (st,work,T)
Proof
  simp[dft_loop_step_def]
QED

Theorem dft_loop_step_empty:
  !cfg lr func st.
    dft_loop_step cfg lr func (st,[],F) = (st,[],T)
Proof
  simp[dft_loop_step_def]
QED

Theorem dft_loop_step_cons_result:
  !cfg lr func st lbl rest st' converged preds.
    dft_process_one cfg lr func st lbl = (st',converged,preds) ==>
    dft_loop_step cfg lr func (st,lbl::rest,F) =
      if converged then (st',[],T) else (st',rest ++ preds,F)
Proof
  simp[dft_loop_step_def]
QED

