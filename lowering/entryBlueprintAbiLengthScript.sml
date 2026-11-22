Theory entryBlueprintAbiLength
Ancestors
  dallocaBlueprintArgs abiEncodeValuesCode loweringShapeRules
  exprSimAbiEncodeArgsPhysicalCapacity abiTypeBoundProps vyperTypeABI vyperTyping
  vyperABI contractABI compileEnv exprLowering venomState venomMemProps
  list words arithmetic

(* A represented encoding of the physical tuple fits the buffer allocated by
   the compiler. Merely knowing the types of the operands is not this post. *)
Theorem abi_blueprint_tuple_extent_bound:
  sfields_tenv_consistent sf tenv /\
  LIST_REL (\ty tv. evaluate_type tenv ty = SOME tv) tys tvs /\
  values_have_types tvs vs /\
  vyper_to_abi_list tenv tys vs = SOME avs ==>
  LENGTH (enc (Tuple (vyper_to_abi_types tenv tys)) (ListV avs)) <=
    abi_size_bound sf (TupleT tys)
Proof
  strip_tac >>
  `EVERY (\ty. IS_SOME (evaluate_type tenv ty)) tys` by
    (qpat_x_assum `LIST_REL _ tys tvs` mp_tac >>
     simp[LIST_REL_EL_EQN, EVERY_EL] >> metis_tac[optionTheory.IS_SOME_EXISTS]) >>
  drule_all_then SUBST1_TAC abi_size_bound_tuple_typed >>
  pure_rewrite_tac[vyper_abi_size_bound_def] >>
  metis_tac[cj 2 vyper_to_abi_enc_length_bound]
QED

(* The real non-empty branch reads the encoder cursor into a fresh result
   variable at the last MLOAD, before any later operand or CREATE executes. *)
Theorem abi_blueprint_length_result[local]:
  args <> [] /\
  compile_create_blueprint_args cfn ce F later args start = ((data,alen),en) ==>
  ?x. alen = Var x /\ not_fresh_at en x
Proof
  strip_tac >> drule_all_then strip_assume_tac create_blueprint_encoded_args_compile >>
  drule_then strip_assume_tac abi_encode_values_to_buf_trace >>
  drule_then strip_assume_tac emit_op_facts >> metis_tac[]
QED

(* u is the observed encoder exit; the producer supplies its validated extent
   (e.g. by abi_blueprint_tuple_extent_bound and an encoder length post).
   Only the saved result variable needs a frame from u to the ADD state. *)
Theorem abi_blueprint_length_at_add:
  compile_create_blueprint_args cfn ce F later args start = ((data,alen),en) /\
  (args <> [] ==>
    arg_types_fit (MAP (lowered_value_type ce) args) (MAP expr_type args) /\
    abi_size_bound ce.ce_struct_fields (TupleT (MAP expr_type args)) < 2 ** 64 /\
    (?extent. extent <= abi_size_bound ce.ce_struct_fields
      (TupleT (MAP (lowered_value_type ce) args)) /\
      eval_operand alen u = SOME (n2w extent)) /\
    (!x w. alen = Var x /\ not_fresh_at en x /\ lookup_var x u = SOME w ==>
      lookup_var x at_add = SOME w)) ==>
  ?w. eval_operand alen at_add = SOME w /\ w2n w < 2 ** 64
Proof
  strip_tac >> Cases_on `args = []`
  >- gvs[compile_create_blueprint_args_def, comp_return_def, eval_operand_def] >>
  qpat_x_assum `args <> [] ==> _` (drule_then strip_assume_tac) >>
  drule_all_then strip_assume_tac abi_blueprint_length_result >>
  drule_then (qspec_then `ce.ce_struct_fields` assume_tac)
    (cj 2 abi_args_fits_size_bound) >>
  `extent < 2 ** 64` by decide_tac >>
  `2 ** 64 < dimword (:256)` by simp[dimword_def] >>
  `extent < dimword (:256)` by metis_tac[LESS_TRANS] >>
  gvs[eval_operand_def, LESS_MOD]
QED
