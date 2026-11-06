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

