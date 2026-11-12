(* Scalar binop support and source equations for immutable roots. *)
Theory immutableAugAssignRootSource
Ancestors
  bodyAugAssignOther supportedExprForms supportedTypes compileEnv vyperState
  vyperInterpreter

Theorem supported_integer_type_word[local]:
  supported_integer_type ty ==> is_word_type ty
Proof
  Cases_on `ty` >> simp[supported_integer_type_def] >>
  rename1 `BaseT bt` >> Cases_on `bt` >>
  simp[supported_integer_type_def, is_word_type_def]
QED

Theorem supported_numeric_type_word[local]:
  supported_numeric_type ty ==> is_word_type ty
Proof
  rw[supported_numeric_type_def] >>
  simp[is_word_type_def, supported_integer_type_word]
QED

Theorem supported_binop_word_type:
  supported_binop bop ty rhs_ty lit nn ==> is_word_type ty
Proof
  Cases_on `bop` >> simp[supported_binop_def] >> rpt strip_tac >>
  gvs[is_word_type_def] >>
  metis_tac[supported_integer_type_word, supported_numeric_type_word,
            supported_word_type_is_word]
QED

Theorem immutable_augassign_root_source:
  get_module_code cx src = SOME ts /\ find_var_decl_by_name id ts = NONE /\
  FLOOKUP (case ALOOKUP es.immutables cx.txn.target of
             NONE => FEMPTY | SOME imms => get_source_immutables src imms) id =
    SOME (tv,iv) ==>
  eval_target_place cx (TopLevelNameTarget (src,id)) es =
    (INL (ImmutablePlace src id []),es) /\
  read_place cx (ImmutablePlace src id []) es = (INL iv,es) /\
  place_type_value cx (ImmutablePlace src id []) es = (INL tv,es)
Proof
  strip_tac >>
  Cases_on `ALOOKUP es.immutables cx.txn.target` >> gvs[] >>
  conj_tac
  >- (simp[Once evaluate_def, bind_def] >>
      simp[Once evaluate_def, lookup_global_def, get_immutables_def,
           get_address_immutables_def, bind_def, lift_option_type_def,
           return_def, get_place_def]) >>
  simp[read_place_def, place_type_value_def, get_immutables_def,
       get_address_immutables_def, bind_def, lift_option_type_def,
       lift_sum_def, return_def, evaluate_subscripts_def, subscripts_type_def]
QED
