(* Every ir_function field must be normalized, including newly added fields. *)
Theory evalCompilerBaseDftLibTest
Ancestors
  compileVyper worklistStepCompute dominatorCompute
Libs
  evalCompilerBaseDftLib

(* Put a beta redex in every field, deriving both coverage and types from the
   record metadata. ARB keeps the compiler query closed, as flow_call requires.
   REFL_TAC below cannot hide an unnormalized field. *)
val function_fields = List.map (fn (name,{accessor,...}) =>
  (name, boolSyntax.mk_arb (snd (dom_rng (type_of accessor)))))
  (TypeBase.fields_of ``:ir_function``);
val normalized_function = TypeBase.mk_record (``:ir_function``, function_fields);
val deferred_function = TypeBase.mk_record (``:ir_function``,
  List.map (fn (name,value) => let
    val variable = mk_var (name,type_of value)
  in (name, mk_comb (mk_abs (variable,variable),value)) end) function_fields);

Theorem dft_input_normalizes_all_fields:
  dft_fn ^deferred_function = dft_fn ^normalized_function
Proof
  base_dft_input_fields >> REFL_TAC
QED

Theorem dft_result_normalizes_all_fields:
  ^deferred_function = ^normalized_function
Proof
  base_dft_result_fields >> REFL_TAC
QED
