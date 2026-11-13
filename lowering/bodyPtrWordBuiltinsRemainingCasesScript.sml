(* Remaining family dispatch, retaining the conditional operand premise. *)
Theory bodyPtrWordBuiltinsRemainingCases
Ancestors bodyPtrWordBuiltinsRoundingCompose bodyPtrWordBuiltinsScalingCompose
  bodyPtrWordBuiltinsModularCompose bodyPtrPreds exprSimHypsDefs vyperTyping
  vyperTypeSystem vyperAST vyperInterpreter vyperContext list

Theorem body_word_remaining_bad_arity_ptr_ok:
  ((?d. bt = AsWeiValue d) \/ bt = Ceil \/ bt = Floor \/ bt = AddMod \/ bt = MulMod \/ bt = PowMod256) /\
  ~builtin_args_length_ok bt (LENGTH es) ==>
  body_expr_ptr_ok cx (Builtin ty bt es)
Proof
  strip_tac >> gvs[] >> simp[body_expr_ptr_ok_def] >> rpt strip_tac >>
  gvs[expr_body_pre_def, well_typed_expr_def, well_typed_builtin_app_def,
      builtin_args_length_ok_def, MAP_EQ_CONS, MAP_EQ_NIL]
QED

Theorem body_word_remaining_ptr_ok:
  !cx ty bt es.
    ((?d. bt = AsWeiValue d) \/ bt = Ceil \/ bt = Floor \/ bt = AddMod \/ bt = MulMod \/ bt = PowMod256) /\
    (builtin_args_length_ok bt (LENGTH es) ==> body_exprs_ptr_ok cx es) ==>
    body_expr_ptr_ok cx (Builtin ty bt es)
Proof
  rpt gen_tac >> disch_tac >> Cases_on `builtin_args_length_ok bt (LENGTH es)`
  >- (gvs[]
      >- (gvs[builtin_args_length_ok_def] >> Cases_on `es` >> gvs[body_exprs_ptr_ok_def] >>
          irule body_word_scale_singleton_ptr_ok >> simp[])
      >- (gvs[builtin_args_length_ok_def] >> Cases_on `es` >> gvs[body_exprs_ptr_ok_def] >>
          irule (body_word_round_singleton_ptr_ok |> Q.SPEC `cx` |> Q.SPEC `ty` |> Q.SPEC `h` |> Q.SPEC `T` |> SIMP_RULE (srw_ss()) []) >> simp[])
      >- (gvs[builtin_args_length_ok_def] >> Cases_on `es` >> gvs[body_exprs_ptr_ok_def] >>
          irule (body_word_round_singleton_ptr_ok |> Q.SPEC `cx` |> Q.SPEC `ty` |> Q.SPEC `h` |> Q.SPEC `F` |> SIMP_RULE (srw_ss()) []) >> simp[])
      >- suspend "add"
      >- suspend "mul" >> suspend "pow") >>
  irule body_word_remaining_bad_arity_ptr_ok >> simp[]
QED

Resume body_word_remaining_ptr_ok[add]:
  gvs[builtin_args_length_ok_def] >>
  `?a b m. es = [a;b;m]` by (fs[LENGTH_EQ_NUM_compute] >> metis_tac[]) >> gvs[] >>
  irule (body_word_modular_ptr_ok |> Q.INST [`is_mul` |-> `F`] |> SIMP_RULE (srw_ss()) []) >> simp[]
QED
Resume body_word_remaining_ptr_ok[mul]:
  gvs[builtin_args_length_ok_def] >>
  `?a b m. es = [a;b;m]` by (fs[LENGTH_EQ_NUM_compute] >> metis_tac[]) >> gvs[] >>
  irule (body_word_modular_ptr_ok |> Q.INST [`is_mul` |-> `T`] |> SIMP_RULE (srw_ss()) []) >> simp[]
QED
Resume body_word_remaining_ptr_ok[pow]:
  gvs[builtin_args_length_ok_def] >>
  `?a b. es = [a;b]` by (fs[LENGTH_EQ_NUM_compute] >> metis_tac[]) >> gvs[] >>
  irule body_word_pow_ptr_ok >> simp[]
QED
Finalise body_word_remaining_ptr_ok
