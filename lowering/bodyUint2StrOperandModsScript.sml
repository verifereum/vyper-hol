(* The successful forced Uint2Str operand, at its linked endpoint. *)
Theory bodyUint2StrOperandMods
Ancestors
  bodyFullPostsMods bodySimStmtFacts bodyWriteSubscriptSourceMods
  exprSimWordArgs exprSimHypsDefs loweringSlice loweringPosts
  vyperTypeBuiltins vyperTypeExprSoundness vyperTyping vyperValue
  vyperState vyperInterpreter finite_map words integer_word arithmetic compileEnv valueEncoding

Theorem uint2str_operand_endpoint_mods:
  expr_body_pre_mods mods ce cx env e es /\ expr_type e = BaseT (UintT k) /\
  LENGTH (num_to_dec_string (2 ** k - 1)) <= n /\ mid.gas_obs = [] /\
  (!tail. bind (eval_expr cx e) (read_result cx) (es with gas_obs := xs ++ tail) =
          (INL v,mid with gas_obs := tail)) /\
  expr_post_mods H ctx fn ce cx e es sa sm s0 mid v op s ==>
  MAP FDOM es.scopes = MAP FDOM mid.scopes /\
  ?X. v = IntV (&X) /\ X < 2 ** k /\ X < dimword (:256) /\
      eval_operand op s = SOME (n2w X) /\ LENGTH (num_to_dec_string X) <= n
Proof
  strip_tac >>
  `mid with gas_obs := [] = mid` by
    (qpat_assum `mid.gas_obs = []` (SUBST1_TAC o SYM) >> simp[]) >>
  `bind (eval_expr cx e) (read_result cx) (es with gas_obs := xs) = (INL v,mid)` by
    (qpat_x_assum `!tail. bind _ _ _ = _` (qspec_then `[]` mp_tac) >> simp[]) >>
  conj_tac
  >- (drule_then mp_tac (REWRITE_RULE [ETA_THM] forced_eval_expr_preserves_scopes_dom) >> simp[]) >>
  `expr_body_pre_mods mods ce cx env e (es with gas_obs := xs)` by simp[] >>
  drule_all_then strip_assume_tac (REWRITE_RULE [ETA_THM] expr_body_pre_eval_mods) >>
  `?i. v = IntV i /\ 0 <= i /\ Num i < 2 ** k /\
       k <= 256 /\ 0 < k /\ k MOD 8 = 0` by
    (qpat_x_assum `!v'. INL v = INL v' ==> _` (qspec_then `v` mp_tac) >>
     Cases_on `v` >> simp[value_runtime_typed_def, evaluate_type_def, value_has_type_def]) >>
  gvs[] >> qexists_tac `Num i` >> simp[] >>
  conj_tac
  >- (rewrite_tac[dimword_def] >>
      irule LESS_LESS_EQ_TRANS >> qexists_tac `2 ** k` >> simp[EXP_BASE_LE_MONO]) >>
  conj_tac
  >- (`~(i < 0)` by intLib.ARITH_TAC >>
      qhdtm_x_assum `expr_post_mods` (strip_assume_tac o REWRITE_RULE [expr_post_mods_def]) >>
      drule expr_post_word_operand >>
      simp[is_word_type_def, evaluate_type_def, word_value_def, val_to_w256_def, i2w_def]) >>
  drule uint2str_width_bound >> simp[]
QED
