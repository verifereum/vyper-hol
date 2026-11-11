(* Checked size diagnostics for registration's source-type interface. *)
Theory registrationSizeAdmissibility
Ancestors vyperValue vyperTypeSystem compileEnv context words
  supportedTypes selectorDispatch compileVyper structFieldsProps

Theorem registration_dynamic_array_size_wrap:
  evaluate_type FEMPTY (ArrayT (BaseT (UintT 256)) (Dynamic (2 ** 251))) =
    SOME (ArrayTV (BaseTV (UintT 256)) (Dynamic (2 ** 251))) /\
  assignable_type FEMPTY (ArrayT (BaseT (UintT 256)) (Dynamic (2 ** 251))) /\
  value_has_type (ArrayTV (BaseTV (UintT 256)) (Dynamic (2 ** 251)))
    (ArrayV (DynArrayV [])) /\
  type_memory_size (ArrayTV (BaseTV (UintT 256)) (Dynamic (2 ** 251))) =
    dimword (:256) + 32 /\
  w2n (n2w (type_memory_size
    (ArrayTV (BaseTV (UintT 256)) (Dynamic (2 ** 251)))) : 256 word) = 32
Proof
  EVAL_TAC >>
  rewrite_tac[wordsTheory.w2n_n2w, wordsTheory.dimword_def,
    fcpTheory.index_bit0, fcpTheory.finite_bit0,
    fcpTheory.index_one, fcpTheory.finite_one] >>
  EVAL_TAC
QED

(* Empty calldata values do not expose the declared capacity. *)
Theorem registration_dynamic_array_empty_source:
  supported_place_type []
    (ArrayT (BaseT (UintT 256)) (Dynamic (2 ** 251))) /\
  vyper_to_abi FEMPTY
    (ArrayT (BaseT (UintT 256)) (Dynamic (2 ** 251)))
    (ArrayV (DynArrayV [])) = SOME (ListV []) /\
  LENGTH (enc
    (vyper_to_abi_type FEMPTY
      (ArrayT (BaseT (UintT 256)) (Dynamic (2 ** 251))))
    (ListV [])) = 32
Proof
  EVAL_TAC >>
  rewrite_tac[fcpTheory.index_bit0, fcpTheory.finite_bit0,
    fcpTheory.index_one, fcpTheory.finite_one] >> EVAL_TAC
QED

(* The lowering guard bounds bytes, before emitting the word literal. *)
Theorem registration_parameter_memory_limit:
  fn_allocs_ok tops
    (mut,(nr:bool),(rr:bool),(fname:string),fargs,dflts,ret,fbody) /\
  ALL_DISTINCT (FLAT (MAP (type_def_keys_toplevel (NONE:num option)) tops)) /\
  MEM (name,ty) fargs /\
  evaluate_type (type_env tops) ty = SOME tv ==>
  type_memory_size tv < 2 ** 64
Proof
  strip_tac >>
  `type_memory_bytes
     (build_compile_env tops Internal mut fname fargs ret fbody F) ty =
   type_memory_size tv` by
    (irule build_compile_env_type_memory_bytes >> simp[]) >>
  gvs[fn_allocs_ok_def, listTheory.EVERY_MEM] >>
  first_x_assum drule >> simp[]
QED
