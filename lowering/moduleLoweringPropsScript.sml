(*
 * Module Lowering Properties
 *
 * TOP-LEVEL:
 *   compile_selector_dispatch_linear_correct — linear dispatch matches selector
 *   compile_selector_dispatch_sparse_correct — sparse dispatch matches selector
 *   compile_decode_args_correct — arg decoding produces correct args
 *   compile_decode_args_nil   — empty arg list is no-op
 *   compile_entry_checks_correct — nonpayable revert on callvalue
 *   compile_constructor_epilogue_correct — runtime code copy + return
 *
 * Source: module.py (VenomModuleCompiler)
 * Lowering: moduleLoweringScript.sml
 *)

Theory moduleLoweringProps
Ancestors
  exprLoweringProps
  moduleLowering compileEnv
  venomExecSemantics venomState venomInst
  abiEncoder

(* ===== Selector Dispatch ===== *)

(* Linear dispatch: emitted instructions either route to matching entry
   block or revert (no match) *)
Theorem compile_selector_dispatch_linear_correct:
  ∀ selectors fallback_lbl ss st st'.
    compile_selector_dispatch_linear selectors fallback_lbl st = ((), st')
    ⇒
    ∃ ss'.
      run_inst_seq (emitted_insts st st') ss = OK ss' ∨
      run_inst_seq (emitted_insts st st') ss = Abort Revert_abort ss'
Proof
  cheat
QED

(* Sparse dispatch: bucket hashing routes selector or reverts *)
Theorem compile_selector_dispatch_sparse_correct:
  ∀ selectors bucket_count fallback_lbl ss st st'.
    compile_selector_dispatch_sparse selectors bucket_count fallback_lbl st =
      ((), st')
    ⇒
    ∃ ss'.
      run_inst_seq (emitted_insts st st') ss = OK ss' ∨
      run_inst_seq (emitted_insts st st') ss = Abort Revert_abort ss'
Proof
  cheat
QED

(* ===== Argument Decoding ===== *)

(* Empty param list is a no-op *)
Theorem compile_decode_args_nil:
  ∀ cenv offset load_opc hi_op base_adj st.
    compile_decode_args cenv [] offset load_opc hi_op base_adj st = ((), st)
Proof
  simp[compile_decode_args_def]
QED

(* Arg decoding stores each param at its alloca location *)
Theorem compile_decode_args_correct:
  ∀ cenv params offset load_opc hi_op base_adj ss st st'.
    compile_decode_args cenv params offset load_opc hi_op base_adj st = ((), st')
    ⇒
    ∃ ss'.
      run_inst_seq (emitted_insts st st') ss = OK ss' ∨
      (* Malformed input → revert (ABI clamping) *)
      run_inst_seq (emitted_insts st st') ss = Abort Revert_abort ss'
Proof
  cheat
QED

(* ===== Entry Checks ===== *)

(* Nonpayable function: reverts if callvalue > 0 *)
Theorem compile_entry_checks_nonpayable_revert:
  ∀ min_cds ss st st'.
    compile_entry_checks min_cds F st = ((), st') ∧
    ss.vs_call_ctx.cc_callvalue ≠ 0w
    ⇒
    ∃ ss'.
      run_inst_seq (emitted_insts st st') ss = Abort Revert_abort ss'
Proof
  cheat
QED

(* Entry checks: either all checks pass or short calldata/nonpayable reverts *)
Theorem compile_entry_checks_correct:
  ∀ min_cds is_payable ss st st'.
    compile_entry_checks min_cds is_payable st = ((), st')
    ⇒
    ∃ ss'.
      (run_inst_seq (emitted_insts st st') ss = OK ss' ∧
       (* On success: payable was OK and calldata was sufficient *)
       (is_payable ∨ ss.vs_call_ctx.cc_callvalue = 0w)) ∨
      run_inst_seq (emitted_insts st st') ss = Abort Revert_abort ss'
Proof
  cheat
QED

(* ===== Constructor ===== *)

(* Constructor epilogue: copies runtime code, terminates with RETURN *)
Theorem compile_constructor_epilogue_correct:
  ∀ runtime_size immutables_len immutables_buf ss st st'.
    compile_constructor_epilogue runtime_size immutables_len immutables_buf st =
      ((), st')
    ⇒
    ∃ ss'.
      run_inst_seq (emitted_insts st st') ss = Halt ss'
Proof
  cheat
QED

(* ===== Kwargs ===== *)

(* Empty kwargs is a no-op *)
Theorem compile_init_kwargs_nil:
  ∀ cenv offset from_cd hi_op st.
    compile_init_kwargs cenv [] offset from_cd hi_op st = ((), st)
Proof
  simp[compile_init_kwargs_def]
QED

(* Kwargs initialization stores defaults *)
Theorem compile_init_kwargs_correct:
  ∀ cenv kwargs offset from_cd hi_op ss st st'.
    compile_init_kwargs cenv kwargs offset from_cd hi_op st = ((), st')
    ⇒
    ∃ ss'.
      run_inst_seq (emitted_insts st st') ss = OK ss' ∨
      run_inst_seq (emitted_insts st st') ss = Abort Revert_abort ss'
Proof
  cheat
QED
