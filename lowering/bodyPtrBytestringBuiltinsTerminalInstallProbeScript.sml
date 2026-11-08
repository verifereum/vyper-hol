Theory bodyPtrBytestringBuiltinsTerminalInstallProbe
Ancestors bodyPtrBytestringBuiltinsTerminalPairProbe
          bodyPtrBytestringBuiltinsSourceFrame compileVyper vyperCompiler

(* Concrete source/environment fixtures, not assumptions of successful lowering. *)
Definition terminal_install_tops_def:
  terminal_install_tops = terminal_probe_tops ++
    [FunctionDecl External Nonpayable F F "probe" [] [] NoneT
      [Expr terminal_probe_call]]
End
Definition terminal_install_env_def:
  terminal_install_env = build_compile_env terminal_install_tops External
    Nonpayable "probe" [] NoneT [Expr terminal_probe_call] F
End

Theorem terminal_install_support:
  supported_program terminal_install_tops
Proof
  EVAL_TAC
QED

Theorem terminal_install_environment_prefix:
  TAKE 4 (SND (compile_expr terminal_install_env NoneT terminal_probe_call
    (initial_compile_state ""))).cs_current_insts =
  terminal_probe_final.cs_current_insts
Proof
  EVAL_TAC
QED

Theorem terminal_install_lowering_rejected:
  lower_vyper_runtime_unit terminal_install_tops order_frame_policy = NONE
Proof
  EVAL_TAC >> simp[wordsTheory.dimword_def]
QED

Definition terminal_install_exts_def:
  terminal_install_exts = MAP
    (set_external_package_target order_frame_policy.rpol_target o
      package_external_fn terminal_install_tops F (assign_nkeys terminal_install_tops 0))
    (FST (classify_functions terminal_install_tops))
End
Definition terminal_install_ints_def:
  terminal_install_ints = MAP
    (set_internal_package_target order_frame_policy.rpol_target o
      package_internal_fn terminal_install_tops F (assign_nkeys terminal_install_tops 0) F 0)
    (FST (SND (classify_functions terminal_install_tops)))
End
Definition terminal_install_sels_def:
  terminal_install_sels = build_selectors (type_env terminal_install_tops)
    (FST (classify_functions terminal_install_tops))
End
Definition terminal_install_state_def:
  terminal_install_state = SND (compile_generate_runtime terminal_install_sels
    terminal_install_exts terminal_install_ints NONE Linear 0 0 []
    (build_dense_entry_info terminal_install_sels terminal_install_exts)
    (initial_compile_state "__entry"))
End
Definition terminal_install_extracted_def:
  terminal_install_extracted = extract_context_with_internals "__entry"
    terminal_install_ints terminal_install_state
End

Theorem terminal_install_outer_guards:
  compute_immutables_len (get_struct_fields (make_struct_fields_map terminal_install_tops))
    terminal_install_tops < 24576 /\
  EVERY external_return_buffer_ok terminal_install_exts /\
  EVERY (fn_allocs_ok terminal_install_tops)
    (FST (classify_functions terminal_install_tops) ++
      FST (SND (classify_functions terminal_install_tops))) /\
  lowering_policy_ok order_frame_policy /\
  IS_SOME terminal_install_extracted
Proof
  EVAL_TAC
QED

Theorem terminal_install_context_rejection:
  ~lowering_context_ok (FST (THE terminal_install_extracted))
Proof
  EVAL_TAC >> simp[wordsTheory.dimword_def]
QED

Theorem terminal_install_guard_values:
  (wf_invoke_targets_check (FST (THE terminal_install_extracted)),
   ptr_ok_check (FST (THE terminal_install_extracted)),
   forced_alloc_inputs_check (FST (THE terminal_install_extracted))) = (T,F,T)
Proof
  EVAL_TAC
QED
