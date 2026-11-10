Theory extRetWidenedShapePtr
Ancestors
  extRetRecursivePlanPtr extRetSemanticEntryPtr extRetWideningTransPtr
  extRetEncodableMetadataPtr vyperTypeSystem vyperAST vyperValue
  exprLowering compileEnv vyperContext finite_map list

(* A diagnostic for the proposed entry condition, NOT a counterexample to
   either frozen frame theorem. Evaluation and widening permit nested None
   when a sibling gives the array element positive storage size. *)
Theorem ext_ret_nested_none_layouts:
  evaluate_type FEMPTY
    (ArrayT (TupleT [NoneT; BaseT (UintT 256)]) (Dynamic 1)) =
    SOME (ArrayTV (TupleTV [NoneTV; BaseTV (UintT 256)]) (Dynamic 1)) /\
  evaluate_type FEMPTY
    (ArrayT (TupleT [NoneT; BaseT (UintT 256)]) (Dynamic 2)) =
    SOME (ArrayTV (TupleTV [NoneTV; BaseTV (UintT 256)]) (Dynamic 2))
Proof
  EVAL_TAC >> simp[wordsTheory.dimword_def] >> EVAL_TAC
QED

Theorem ext_ret_nested_none_widening_obstruction:
  type_widens_to FEMPTY
    (ArrayT (TupleT [NoneT; BaseT (UintT 256)]) (Dynamic 1))
    (ArrayT (TupleT [NoneT; BaseT (UintT 256)]) (Dynamic 2)) /\
  ~encodable_ret_shape FEMPTY
    (ArrayT (TupleT [NoneT; BaseT (UintT 256)]) (Dynamic 2))
Proof
  conj_tac
  >- simp[type_widens_to_def, arg_type_fits_def, well_formed_type_def,
          ext_ret_nested_none_layouts] >>
  simp[Once encodable_ret_shape_cases] >>
  simp[Once encodable_ret_shape_cases] >>
  simp[Once encodable_ret_shape_cases]
QED

(* This shape selects an ordinary dynamic-array encoder, not INVALID. *)
Theorem ext_ret_nested_none_encoder_dispatch:
  !ce. type_to_abi_enc_info ce.ce_struct_fields ce
    (ArrayT (TupleT [NoneT; BaseT (UintT 256)]) (Dynamic 2)) =
    AbiDynArray (AbiCopy 32) 32 32 F
Proof
  simp[type_to_abi_enc_info_def, type_memory_bytes_def,
       abi_embedded_static_size_def, is_abi_dynamic_def, abi_static_size_def]
QED

(* Internal-call and Return typing do not impose assignability on the
   signature's return type.  The remaining full-frame invariants are not
   asserted by this conditional typing witness. *)
Theorem ext_ret_nested_none_call_typing:
  !env ce sig.
    env.type_defs = FEMPTY /\
    FLOOKUP env.fn_sigs (NONE,"nested") = SOME sig /\
    sig.param_types = [] /\ sig.num_defaults = 0 /\
    sig.ret_ty = ArrayT (TupleT [NoneT; BaseT (UintT 256)]) (Dynamic 1) /\
    ce.ce_func_return_type "nested" = sig.ret_ty ==>
    well_typed_expr env
      (Call (ArrayT (TupleT [NoneT; BaseT (UintT 256)]) (Dynamic 2))
        (IntCall (NONE,"nested")) [] NONE) /\
    IS_SOME (type_stmt env
      (ArrayT (TupleT [NoneT; BaseT (UintT 256)]) (Dynamic 2))
      (Return (SOME
        (Call (ArrayT (TupleT [NoneT; BaseT (UintT 256)]) (Dynamic 2))
          (IntCall (NONE,"nested")) [] NONE)))) /\
    lowered_value_type ce
      (Call (ArrayT (TupleT [NoneT; BaseT (UintT 256)]) (Dynamic 2))
        (IntCall (NONE,"nested")) [] NONE) <>
      ArrayT (TupleT [NoneT; BaseT (UintT 256)]) (Dynamic 2)
Proof
  rpt strip_tac >>
  simp[well_typed_expr_def, well_formed_type_def,
       ext_ret_nested_none_layouts, ext_ret_nested_none_widening_obstruction,
       typedCopyPtrTheory.type_stmt_return_some_iff,
       lowered_value_type_def, nsid_to_string_def, expr_type_def,
       type_widens_to_def, arg_type_fits_def] >>
  gvs[lowered_value_type_def, nsid_to_string_def]
QED

(* Caller-boundary audit (C1.14.3.1).
   ext_ret_nested_none_layouts consumes no caller hypotheses: it checks the
   two concrete evaluated layouts. ext_ret_nested_none_widening_obstruction
   checks that widening alone cannot produce encodable_ret_shape.
   ext_ret_nested_none_call_typing consumes only local type_defs/fn_sigs
   facts and the compiler return-signature lookup. Its conclusions witness
   local well_typed_expr, valued Return typing and unequal lowered layout.
   ext_ret_nested_none_encoder_dispatch is independent of the compiler
   environment and checks the actual non-INVALID encoder selected.

   Not witnessed: a tops/am/tx satisfying source_typing_ok; a package and
   positional-argument compilation producing ce; same_frame ce next;
   get_tenv cx = type_env tops; expr_sim_inv next cx env es (including its
   source/compiler signature consistency); stmt_exprs_ok; call_evaluation_safe;
   and both expr_sim_ptr and expr_vv_sim_ptr. In particular these theorems
   neither construct a runtime internal-call result nor establish the
   quantified pointer simulations in the frozen widened antecedent.
   Thus this is an obstruction to the smaller typing/evaluation/widening
   entry interface, NOT a counterexample to external_frame_ret_widened_ptr
   or external_frame_ret_ok_ptr. A general encoder interface requiring
   encodable_ret_shape still needs a stronger producer from those remaining
   full-caller facts, or a broadened checked shape interface. Recursive
   implementation is deliberately deferred to strategy review. *)
