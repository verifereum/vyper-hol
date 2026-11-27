Theory bodyFullRawCallRequestGas
Ancestors
  exprSimRawCall exprSimHypsDefs exprSimPrecompiles exprSimSend loweringPosts
  vyperAST vyperInterpreter vyperValue valueEncodingDefs venomExecSemantics
  compileEnv list option words

(* The selected word is already at the call cursor; the list relation
   packages source uint256 range and operand preservation together. *)
Theorem raw_call_selected_gas_word:
  !ks xs vs v.
    LIST_REL (\x v. ?w. eval_operand x t = SOME w /\
                        dest_NumV v = SOME (w2n w)) xs vs /\
    ext_call_kwarg EKGas ks vs = SOME v ==>
    ?x w. ext_call_kwarg EKGas ks xs = SOME x /\
          eval_operand x t = SOME w /\ dest_NumV v = SOME (w2n w)
Proof
  Induct >> Cases_on `xs` >> Cases_on `vs` >>
  simp[ext_call_kwarg_def] >> rpt strip_tac >>
  IF_CASES_TAC >> gvs[] >> metis_tac[]
QED

Theorem raw_call_request_gas_at_entry:
  !mods.
  expr_body_pre_mods mods cenv cx env (Call ann (RawCallTarget flags) (a::d::kws) NONE) es /\
  expr_sim_inv_mods mods cenv cx env esD /\
  eval_exprs cx kws (esD with gas_obs := gsK) = (INL kvs,esK) /\
  typed_args_post H ctx func cenv cx esD s4 t4 esK kws xs kvs tk /\
  (!x w. MEM x xs /\ eval_operand x tk = SOME w ==> eval_operand x t7 = SOME w) /\
  (!p. ext_call_kwarg EKGas flags.rcf_kws xs = SOME p ==> gas_op = p) /\
  eval_operand gas_op t7 = SOME gw ==>
  !g. OPTION_BIND (ext_call_kwarg EKGas flags.rcf_kws kvs) dest_NumV = SOME g ==>
      g = w2n gw
Proof
  strip_tac >>
  drule raw_call_keywords_pre >> strip_tac >>
  `LIST_REL (\e v. ?tv. evaluate_type (get_tenv cx) (expr_type e) = SOME tv /\
                        value_has_type tv v) kws kvs` by
    (irule stack_args_values_typed_body >>
     goal_assum (drule_at Any) >> simp[] >>
     qexistsl [`cenv`,`env`] >> simp[] >> rpt strip_tac >>
     `expr_type e = BaseT (UintT 256) /\
      !st. expr_sim_inv cenv cx env st ==> expr_body_pre cenv cx env e st` by
       fs[EVERY_MEM] >>
     simp[is_word_type_def]) >>
  `LIST_REL (\x v. ?w. eval_operand x t7 = SOME w /\
                       dest_NumV v = SOME (w2n w)) xs kvs` by
    (fs[typed_args_post_def, LIST_REL_EL_EQN, LENGTH_ZIP, EVERY_EL] >>
     rpt strip_tac >>
     `expr_type (EL n kws) = BaseT (UintT 256)` by simp[] >>
     `value_has_type (BaseTV (UintT 256)) (EL n kvs)` by
       (qpat_x_assum `!i. i < LENGTH kws ==> ?tv. _` (qspec_then `n` mp_tac) >>
        simp[vyperValueTheory.evaluate_type_def]) >>
     `eval_operand (EL n xs) tk =
      SOME (typed_val_to_w256 (BaseTV (UintT 256)) (EL n kvs))` by
       (qpat_x_assum `!i. i < LENGTH xs ==> _` (qspec_then `n` mp_tac) >>
        simp[EL_ZIP, vyperValueTheory.evaluate_type_def]) >>
     drule uint256_typed_dest >> strip_tac >>
     first_assum (irule_at (Pat `dest_NumV _ = _`)) >>
     first_x_assum irule >> simp[EL_MEM]) >>
  Cases_on `ext_call_kwarg EKGas flags.rcf_kws kvs` >> simp[] >>
  drule_all raw_call_selected_gas_word >> strip_tac >> gvs[]
QED
