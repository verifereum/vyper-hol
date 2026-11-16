(* TOP-LEVEL: asm_sym_backward_own connects fixed-own-code symbolic runs
   to concrete assembly runs. The original symbolic bridge is unchanged. *)
Theory asmSymBridgeOwn
Ancestors
  asmSymBridge asmSymOwnCode asmSymSem asmSem asmWf symbolResolve
  vfmTypes asmOwnCodeInvariant asmSymOwnCopyBridge asmSymOwnRunBridge
  asmSymOwnStepBridge

(* sym_init erases as_code, so own must agree with the concrete code at
   each step. Concrete assembly never changes that field. Unchanged
   instructions use asmSymBridge's exported asm_sym_step.

   For value-offset CODECOPY, sym_step_concrete_sim at CALLDATACOPY on
   states with calldata temporarily set to own can supply the memory
   correspondence without copying the old bridge's local splice lemmas. *)
Theorem asm_sym_backward_own:
  asm_static_wf p ∧ s.as_pc = 0 ∧ asm_data_env_ok p env s.as_code ∧
  sym_terminal (sym_run_own p env s.as_code fuel (sym_init s))
  ⇒ ∃n. sym_result_rel (sym_run_own p env s.as_code fuel (sym_init s))
          (asm_result_sym (asm_steps (SND (compute_label_offsets p))
             (build_offset_to_pc p) p n s))
Proof
  strip_tac >> irule asm_sym_run_own_backward_from_step >>
  simp[asm_sym_rel_init] >>
  rpt gen_tac >> strip_tac >> conj_tac
  >- (irule asm_sym_step_own_from_copy >> simp[] >>
      metis_tac[sym_codecopy_own_sim]) >>
  metis_tac[asm_step_code_preserved]
QED
