Theory exprSimAbiEncodeArgsLayoutProbe
Ancestors
  exprSimHypsDefs loweringPosts exprLowering compileEnv vyperTypeSystem
  finite_map

Definition layout_narrow_def:
  layout_narrow = ArrayT (BaseT (BytesT (Dynamic 32))) (Dynamic 2)
End

Definition layout_wide_def:
  layout_wide = ArrayT (BaseT (BytesT (Dynamic 64))) (Dynamic 2)
End

Theorem layout_annotation_widening:
  type_widens_to tenv layout_narrow layout_wide
Proof
  EVAL_TAC >> simp[wordsTheory.dimword_def, vyperValueTheory.type_slot_size_def, vfmConstantsTheory.word_size_def]
QED

Theorem layout_physical_mismatch:
  post_value_type (ce with ce_func_return_type := (\_. layout_narrow))
    (Call layout_wide (IntCall (NONE,"f")) [] NONE) = layout_narrow /\
  expr_type (Call layout_wide (IntCall (NONE,"f")) [] NONE) = layout_wide /\
  type_memory_bytes ce layout_narrow = 160 /\
  type_memory_bytes ce layout_wide = 224 /\
  layout_narrow <> layout_wide
Proof
  EVAL_TAC >> simp[wordsTheory.dimword_def, vyperValueTheory.type_slot_size_def, vfmConstantsTheory.word_size_def]
QED

Theorem layout_call_typing:
  FLOOKUP env.fn_sigs (NONE,"f") = SOME sig /\
  sig.ret_ty = layout_narrow /\ sig.param_types = [] ==>
  well_typed_expr env (Call layout_wide (IntCall (NONE,"f")) [] NONE)
Proof
  simp[well_typed_expr_def, layout_annotation_widening,
       layout_wide_def, well_formed_type_def] >>
  EVAL_TAC >> simp[wordsTheory.dimword_def, vyperValueTheory.type_slot_size_def,
                  vfmConstantsTheory.word_size_def]
QED

(* A concrete return buffer: [2, (1,0xaa), (1,0xbb)] at the
   declared 64-byte element stride, with zero padding. *)
Definition layout_memory_def:
  layout_memory : byte list =
    REPLICATE 31 0w ++ [2w] ++
    REPLICATE 31 0w ++ [1w; 170w] ++ REPLICATE 31 0w ++
    REPLICATE 31 0w ++ [1w; 187w] ++ REPLICATE 31 0w
End

Theorem layout_memory_mismatch:
  val_in_memory (ArrayTV (BaseTV (BytesT (Dynamic 32))) (Dynamic 2))
    (ArrayV (DynArrayV [BytesV [170w]; BytesV [187w]])) 0 layout_memory /\
  ~val_in_memory (ArrayTV (BaseTV (BytesT (Dynamic 64))) (Dynamic 2))
    (ArrayV (DynArrayV [BytesV [170w]; BytesV [187w]])) 0 layout_memory
Proof
  EVAL_TAC >> simp[wordsTheory.w2n_n2w, wordsTheory.dimword_def,
                  wordsTheory.dimindex_8]
QED

Theorem layout_abi_typing:
  FLOOKUP env.fn_sigs (NONE,"f") = SOME sig /\
  sig.ret_ty = layout_narrow /\ sig.param_types = [] ==>
  well_typed_expr env
    (TypeBuiltin (BaseT (BytesT (Dynamic 320))) (AbiEncode T NONE)
       (TupleT [layout_wide])
       [Call layout_wide (IntCall (NONE,"f")) [] NONE])
Proof
  rpt strip_tac >>
  `well_typed_expr env (Call layout_wide (IntCall (NONE,"f")) [] NONE)` by
    (irule layout_call_typing >> simp[] >> metis_tac[]) >>
  simp[well_typed_expr_def, type_builtin_result_ok_def,
       well_typed_type_builtin_args_def, well_formed_type_def] >>
  EVAL_TAC >> simp[wordsTheory.dimword_def]
QED

(* The singleton argument path does not request a layout conversion:
   a returned stack pointer is passed straight to abi_args_post. *)
Theorem layout_singleton_compile:
  cfn ce layout_wide (Call layout_wide (IntCall (NONE,"f")) [] NONE) sa =
    (StackValue layout_narrow op,sb) ==>
  compile_abi_encode_args cfn ce
    [Call layout_wide (IntCall (NONE,"f")) [] NONE] sa = ([op],sb)
Proof
  simp[compile_abi_encode_args_def, expr_can_mutate_def,
       vyperASTTheory.expr_type_def, unwrap_value_def,
       comp_bind_def, comp_ignore_bind_def, comp_return_def]
QED
