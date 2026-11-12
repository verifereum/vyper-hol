Theory entryNaturalCapacityProbe
Ancestors vyperInterpreter vyperTyping vyperTypeSystem valueEncoding
  vyperValue vyperAST vyperValueOperation supportedTypes context words
  compileEnv entryStateRel moduleLowering entryAllocationCapacityProbe
  vyperCompiler
Libs wordsLib

(* The source checks slots, whereas the compiler buffer records bytes. *)
Theorem natural_capacity_type_evaluation:
  evaluate_type tenv
    (ArrayT (BaseT (UintT 256)) (Dynamic (2 ** 251 - 1))) =
  SOME (ArrayTV (BaseTV (UintT 256)) (Dynamic (2 ** 251 - 1))) /\
  type_slot_size
    (ArrayTV (BaseTV (UintT 256)) (Dynamic (2 ** 251 - 1))) = 2 ** 251 /\
  type_memory_size
    (ArrayTV (BaseTV (UintT 256)) (Dynamic (2 ** 251 - 1))) = dimword (:256)
Proof
  simp[evaluate_type_def, type_slot_size_def, type_memory_size_def,
       bound_length_def] >> EVAL_TAC
QED

Theorem natural_capacity_empty_cast:
  safe_cast (ArrayTV (BaseTV (UintT 256)) (Dynamic (2 ** 251 - 1)))
    (ArrayV (DynArrayV [])) = SOME (ArrayV (DynArrayV []))
Proof
  simp[safe_cast_def]
QED

Theorem natural_capacity_binding:
  bind_arguments tenv
    [("a", ArrayT (BaseT (UintT 256)) (Dynamic (2 ** 251 - 1)))]
    [ArrayV (DynArrayV [])] =
  SOME (FEMPTY |+ ("a",
    <| assignable := T;
       type := ArrayTV (BaseTV (UintT 256)) (Dynamic (2 ** 251 - 1));
       value := ArrayV (DynArrayV []); popped := [] |>))
Proof
  simp[bind_arguments_def, natural_capacity_type_evaluation,
       safe_cast_def]
QED

Theorem natural_capacity_supported_place:
  supported_place_type tops
    (ArrayT (BaseT (UintT 256)) (Dynamic (2 ** 251 - 1)))
Proof
  simp[supported_place_type_def, supported_nested_type_def,
       supported_scalar_type_def, supported_word_type_def,
       supported_int_width_def]
QED

Theorem natural_capacity_assignable:
  assignable_type tenv
    (ArrayT (BaseT (UintT 256)) (Dynamic (2 ** 251 - 1)))
Proof
  simp[assignable_type_def, well_formed_type_def,
       natural_capacity_type_evaluation, evaluate_type_def]
QED

Theorem natural_capacity_empty_typed:
  value_has_type
    (ArrayTV (BaseTV (UintT 256)) (Dynamic (2 ** 251 - 1)))
    (ArrayV (DynArrayV []))
Proof
  simp[value_has_type_def]
QED

Theorem natural_capacity_compiler_bytes:
  type_memory_bytes cenv
    (ArrayT (BaseT (UintT 256)) (Dynamic (2 ** 251 - 1))) = dimword (:256)
Proof
  simp[type_memory_bytes_def] >> EVAL_TAC
QED

Theorem natural_capacity_package_location:
  package_external_fn tops use_trans nkey_map
    (mut, nr, rr, fname,
     [("a", ArrayT (BaseT (UintT 256)) (Dynamic (2 ** 251 - 1)))],
     dflts, ret, fbody) = (lbl, cenv, pos_args, rest) ==>
  ?off. FLOOKUP cenv.ce_vars "a" = SOME (MemLoc off (dimword (:256)))
Proof
  strip_tac >> drule package_external_fn_vars >>
  simp[type_memory_bytes_def] >> EVAL_TAC
QED

Theorem natural_capacity_emitted_charge:
  alloca_size (inst with inst_operands :=
    [Lit (n2w (type_memory_bytes cenv
      (ArrayT (BaseT (UintT 256)) (Dynamic (2 ** 251 - 1)))))]) = 0
Proof
  rewrite_tac[natural_capacity_compiler_bytes] >>
  simp[allocation_capacity_wrap_probe]
QED
