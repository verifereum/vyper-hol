Theory entryCreateEncodedArgExtent
Ancestors
  entryBlueprintAbiLength createSizeOperandPre exprBodyPreProps exprSimHyps
  allocLimits exprSimAbiEncodeArgsPhysicalCapacity dallocaBlueprintArgs
  vyperTypeArgFits exprLowering compileEnv vyperAST vyperTyping vyperABI
  contractABI list words arithmetic createSizeCtorPayload vyperCreate venomState

(* expr_body_pre carries the selected function's allocation check. The check
   uses annotations; the ALLOCA in the nonempty branch uses the physical types. *)
Theorem encoded_blueprint_tuple_allocation:
  expr_body_pre ce cx env
    (Call ann (CreateTarget (CreateFromBlueprint F) hs rof ks)
      (target::amount::((if hs then [salt] else []) ++ off::args)) df) es /\
  args <> [] ==>
  arg_types_fit (MAP (lowered_value_type ce) args) (MAP expr_type args) /\
  abi_size_bound ce.ce_struct_fields (TupleT (MAP expr_type args)) < 2 ** 64 /\
  abi_size_bound ce.ce_struct_fields
    (TupleT (MAP (lowered_value_type ce) args)) < 2 ** 64
Proof
  strip_tac >>
  drule expr_body_pre_static_facts >> strip_tac >>
  `EVERY (\e. expr_body_pre ce cx env e es) args` by
    (simp[EVERY_MEM] >> rpt strip_tac >>
     `MEM e (target::amount::((if hs then [salt] else []) ++ off::args))` by
       simp[MEM_APPEND] >>
     metis_tac[create_call_operand_body_pre]) >>
  `arg_types_fit (MAP (lowered_value_type ce) args) (MAP expr_type args)` by
    (simp[arg_types_fit_LIST_REL, LIST_REL_EL_EQN, EL_MAP] >>
     rpt strip_tac >>
     qpat_assum `EVERY _ args`
       (qspec_then `n` (drule_then (assume_tac o BETA_RULE)) o
        REWRITE_RULE[EVERY_EL]) >>
     drule_then ACCEPT_TAC expr_body_pre_lowered_fits) >>
  `abi_size_bound ce.ce_struct_fields (TupleT (MAP expr_type args)) < 2 ** 64` by
    (Cases_on `hs` >> gvs[alloc_limits_expr_def, ext_call_alloc_ok_def]) >>
  drule_then assume_tac create_ctor_args_abi_bound >>
  rpt conj_tac >> TRY (first_assum ACCEPT_TAC >> NO_TAC) >>
  irule LESS_EQ_LESS_TRANS >> goal_assum (drule_at Any) >> simp[]
QED

(* In the nonempty case this is the length returned at the encoder exit for
   the replayed physical tuple, not just the size of some typed source value.
   The SSA frame connects that exit to the actual pre-ADD state. *)
Theorem encoded_blueprint_length_at_add:
  expr_body_pre ce cx env
    (Call ann (CreateTarget (CreateFromBlueprint F) hs rof ks)
      (target::amount::((if hs then [salt] else []) ++ off::args)) df) es /\
  compile_create_blueprint_args cfn ce F later args start = ((data,alen),en) /\
  (args <> [] ==>
    sfields_tenv_consistent ce.ce_struct_fields tenv /\
    LIST_REL (\ty tv. evaluate_type tenv ty = SOME tv)
      (MAP (lowered_value_type ce) args) tvs /\
    values_have_types tvs vs /\
    vyper_to_abi_list tenv (MAP (lowered_value_type ce) args) vs = SOME avs /\
    eval_operand alen u = SOME (n2w
      (LENGTH (enc (Tuple (vyper_to_abi_types tenv
        (MAP (lowered_value_type ce) args))) (ListV avs)))) /\
    (!x w. not_fresh_at en x /\ lookup_var x u = SOME w ==>
      lookup_var x at_add = SOME w)) ==>
  ?w. eval_operand alen at_add = SOME w /\ w2n w < 2 ** 64
Proof
  strip_tac >>
  irule abi_blueprint_length_at_add >>
  goal_assum (drule_at Any) >> qexists_tac `u` >>
  strip_tac >>
  drule_all_then strip_assume_tac encoded_blueprint_tuple_allocation >>
  qpat_x_assum `args <> [] ==> _` (drule_then strip_assume_tac) >>
  drule_all abi_blueprint_tuple_extent_bound >> simp[] >> metis_tac[]
QED

(* Adapter for the actual constructor-row replay. Each successful word row
   gives the two value typings via blueprint_ctor_word_row_at; the other rows
   give them with their saved-value representation. The encoder post here is
   the source-byte form returned by create_ctor_payload_length. *)
Theorem encoded_blueprint_replayed_length_at_add:
  expr_body_pre ce cx env
    (Call ann (CreateTarget (CreateFromBlueprint F) hs rof ks)
      (target::amount::((if hs then [salt] else []) ++ off::args)) df) es /\
  compile_create_blueprint_args cfn ce F later args start = ((data,alen),en) /\
  (args <> [] ==>
    sfields_tenv_consistent ce.ce_struct_fields (get_tenv cx) /\
    LENGTH args = LENGTH vs /\ LENGTH args = LENGTH saved /\
    (!i. i < LENGTH args ==> ?tv av.
      evaluate_type (get_tenv cx) (lowered_value_type ce (EL i args)) = SOME tv /\
      evaluate_type (get_tenv cx) (expr_type (EL i args)) = SOME av /\
      arg_type_fits (lowered_value_type ce (EL i args)) (expr_type (EL i args)) /\
      value_has_type tv (EL i vs) /\ value_has_type av (EL i vs)) /\
    encode_create_ctor_args (get_tenv cx) (MAP expr_type args) vs = SOME bytes /\
    eval_operand alen u = SOME (n2w (LENGTH bytes)) /\
    (!x w. not_fresh_at en x /\ lookup_var x u = SOME w ==>
      lookup_var x at_add = SOME w)) ==>
  ?w. eval_operand alen at_add = SOME w /\ w2n w < 2 ** 64
Proof
  strip_tac >> irule abi_blueprint_length_at_add >>
  goal_assum (drule_at Any) >> qexists_tac `u` >> strip_tac >>
  drule_all_then strip_assume_tac encoded_blueprint_tuple_allocation >>
  qpat_x_assum `args <> [] ==> _` (drule_then strip_assume_tac) >>
  `LENGTH bytes <= abi_size_bound ce.ce_struct_fields
      (TupleT (MAP (lowered_value_type ce) args))` by
    (drule_all create_ctor_payload_layout >> simp[] >> metis_tac[]) >>
  simp[] >> metis_tac[]
QED
