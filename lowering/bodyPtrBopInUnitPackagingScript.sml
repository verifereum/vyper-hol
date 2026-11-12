Theory bodyPtrBopInUnitPackaging
Ancestors
  bodyPtrBopInUnitMetadata bodyPtrBopInSourceFrame
  bodyPtrBopInUnitBody bodyPtrBopInPair compileEnv vyperCompiler moduleLowering emitHelper

(* These constants are successive results of the actual compiler actions.
   Keeping the stages named avoids whole-runtime evaluation and Keccak. *)
Definition equality_runtime_state_def:
  equality_runtime_state sel = SND
    (emit_inst REVERT [Lit 0w; Lit 0w] []
      (SND (new_block (fresh_label_output "fallback" 0) (equality_bodies_state sel))))
End

Definition equality_runtime_context_def:
  equality_runtime_context sel = FST (THE
    (extract_context_with_internals "__entry"
      ([] : (string # compile_env # (string # bool) list # bool # bool # num #
             bool # bool # bool # num # stmt list # type option) list) (equality_runtime_state sel)))
End

Theorem equality_extraction:
  extract_context_with_internals "__entry"
      ([] : (string # compile_env # (string # bool) list # bool # bool # num #
             bool # bool # bool # num # stmt list # type option) list) (equality_runtime_state sel) =
    SOME (equality_runtime_context sel, [])
Proof
  EVAL_TAC
QED

Theorem equality_context_accepted:
  lowering_context_ok (equality_runtime_context sel)
Proof
  EVAL_TAC >> simp[wordsTheory.w2n_n2w, wordsTheory.dimword_def,
                   venomMemPropsTheory.dimindex_256]
QED

Theorem equality_generate_runtime:
  compile_generate_runtime [(sel,"fn_probe",z)] [equality_external_package]
    [] NONE Linear 0 0 [] entry_info
    (initial_compile_state "__entry") = ((),equality_runtime_state sel)
Proof
  simp[compile_generate_runtime_def, comp_bind_def, comp_ignore_bind_def,
       comp_return_def, fresh_label_def, initial_compile_state_def,
       compile_internal_fn_bodies_def, pair_ignore_first,
       equality_runtime_state_def, equality_bodies_state_def,
       equality_dispatch_state_def]
QED

Theorem equality_run_lowering:
  run_lowering [(sel,"fn_probe",z)] [equality_external_package] [] NONE
    probe_policy 0 0 [] entry_info "__entry" =
  SOME <| cu_context := equality_runtime_context sel; cu_data_segment := [] |>
Proof
  simp[run_lowering_def, equality_policy_accepted, probe_policy_def,
       equality_generate_runtime, equality_extraction, equality_context_accepted]
QED
