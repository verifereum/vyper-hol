Theory ctorDeployMemoryRunMemEntryAggregateProbe
Ancestors
  ctorDeployMemoryRunMemEntrySupported structFieldsProps
  typedCopyMetadata vyperContext vyperTypeContract

(* Typing, rather than val_wf alone, selects the canonical sparse form. *)
Theorem ctor_sparse_representation_probe:
  value_has_type (ArrayTV (BaseTV (UintT 256)) (Fixed 3))
    (ArrayV (SArrayV [(1, IntV 7)])) /\
  value_has_type (ArrayTV (BaseTV (UintT 256)) (Fixed 3))
    (ArrayV (SArrayV [])) /\
  ~value_has_type (ArrayTV (BaseTV (UintT 256)) (Fixed 3))
    (ArrayV (SArrayV [(0, IntV 0)])) /\
  ~value_has_type (ArrayTV (BaseTV (UintT 256)) (Fixed 3))
    (ArrayV (SArrayV [(2, IntV 7); (1, IntV 8)])) /\
  val_wf (ArrayTV (BaseTV (UintT 256)) (Fixed 3))
    (ArrayV (SArrayV [(0, IntV 0)]))
Proof
  EVAL_TAC >> intLib.ARITH_TAC
QED

Theorem ctor_sparse_inverse_probe:
  vyper_to_abi FEMPTY (ArrayT (BaseT (UintT 256)) (Fixed 3))
    (ArrayV (SArrayV [(1, IntV 7)])) =
    SOME (ListV [NumV 0; NumV 7; NumV 0]) /\
  abi_to_vyper FEMPTY (ArrayT (BaseT (UintT 256)) (Fixed 3))
    (ListV [NumV 0; NumV 7; NumV 0]) =
    SOME (ArrayV (SArrayV [(1, IntV 7)])) /\
  abi_to_vyper FEMPTY (ArrayT (BaseT (UintT 256)) (Fixed 3))
    (ListV [NumV 0; NumV 0; NumV 0]) =
    SOME (ArrayV (SArrayV []))
Proof
  EVAL_TAC >> intLib.ARITH_TAC
QED

Theorem ctor_supported_struct_type_env_lookup:
  contract_namespaces_ok T [(NONE,tops)] /\
  supported_struct_fields tops (NONE,name) = SOME args ==>
  FLOOKUP (type_env tops) (NONE,name) = SOME (StructArgs args)
Proof
  strip_tac >> drule supported_struct_fields_origin >> strip_tac >>
  simp[type_env_def] >> irule type_env_for_module_struct_lookup >>
  gvs[contract_namespaces_ok_def, contract_keys_def]
QED

Theorem ctor_struct_inverse_probe:
  vyper_to_abi (FEMPTY |+ ((NONE,"S"), StructArgs
      [("x",BaseT (UintT 256)); ("y",BaseT BoolT)]))
    (StructT (NONE,"S")) (StructV [("x",IntV 0); ("y",BoolV T)]) =
    SOME (ListV [NumV 0; NumV 1]) /\
  abi_to_vyper (FEMPTY |+ ((NONE,"S"), StructArgs
      [("x",BaseT (UintT 256)); ("y",BaseT BoolT)]))
    (StructT (NONE,"S")) (ListV [NumV 0; NumV 1]) =
    SOME (StructV [("x",IntV 0); ("y",BoolV T)]) /\
  ~value_has_type (StructTV [("x",BaseTV (UintT 256)); ("y",BaseTV BoolT)])
    (StructV [("y",BoolV T); ("x",IntV 0)])
Proof
  EVAL_TAC >> intLib.ARITH_TAC
QED
