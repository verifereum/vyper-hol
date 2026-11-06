Theory bodyPtrBytestringBuiltinsUnitProbe
Ancestors
  bodyPtrBytestringBuiltinsPtrFrame compileVyper

val () = computeLib.add_funs
  [wordsTheory.dimword_def, fcpLib.INDEX_CONV ``dimindex(:8)``,
   fcpLib.INDEX_CONV ``dimindex(:160)``,
   fcpLib.INDEX_CONV ``dimindex(:256)``];

(* Name one actual source program so context/function coherence is tested
   against lowering itself, not a hand-inserted observation continuation. *)
Definition order_unit_tops_def:
  order_unit_tops =
    [FunctionDecl External Nonpayable F F "probe"
      [("arr", ArrayT (BaseT AddressT) (Dynamic 2))] []
      (BaseT (BytesT (Dynamic 1)))
      [Return (SOME bodyPtrBytestringBuiltinsOrderProbe$order_probe_expr)]]
End

Theorem order_unit_classification:
  classify_functions order_unit_tops =
    ([(Nonpayable, F, F, "probe",
       [("arr", ArrayT (BaseT AddressT) (Dynamic 2))], [],
       BaseT (BytesT (Dynamic 1)),
       [Return (SOME bodyPtrBytestringBuiltinsOrderProbe$order_probe_expr)])],
     [], NONE, NONE)
Proof
  simp[order_unit_tops_def, classify_functions_def, classify_function_def]
QED

Theorem order_unit_allocation_guard:
  fn_allocs_ok order_unit_tops
    (Nonpayable, F, F, "probe",
     [("arr", ArrayT (BaseT AddressT) (Dynamic 2))], [],
     BaseT (BytesT (Dynamic 1)),
     [Return (SOME bodyPtrBytestringBuiltinsOrderProbe$order_probe_expr)])
Proof
  simp[fn_allocs_ok_def, allocLimitsTheory.alloc_limits_stmt_def, allocLimitsTheory.alloc_limits_expr_def,
       bodyPtrBytestringBuiltinsOrderProbeTheory.order_probe_alloc_limits] >>
  simp[compileEnvTheory.type_memory_bytes_def]
QED

Theorem order_unit_immutable_guard:
  compute_immutables_len (get_struct_fields (make_struct_fields_map order_unit_tops))
    order_unit_tops < 24576
Proof
  EVAL_TAC
QED

Theorem order_unit_return_guard:
  external_return_buffer_ok
    (set_external_package_target order_frame_policy.rpol_target
      (package_external_fn order_unit_tops F (assign_nkeys order_unit_tops 0)
        (Nonpayable, F, F, "probe",
         [("arr", ArrayT (BaseT AddressT) (Dynamic 2))], [],
         BaseT (BytesT (Dynamic 1)),
         [Return (SOME bodyPtrBytestringBuiltinsOrderProbe$order_probe_expr)])))
Proof
  simp[set_external_package_target_def, package_external_fn_def,
       external_return_buffer_ok_def, return_buffer_ok_def] >>
  simp[update_cenv_nonreentrant_def, update_cenv_ret_abi_def,
       external_return_needs_wrap_def, compileEnvTheory.is_abi_dynamic_def,
       compileEnvTheory.abi_size_bound_def,
       exprLoweringTheory.type_to_abi_enc_info_def] >>
  Cases_on `needs_external_call_wrap (BaseT (BytesT (Dynamic 1)))` >> simp[]
QED
