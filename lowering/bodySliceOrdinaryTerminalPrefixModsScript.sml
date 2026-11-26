(* The ordinary Slice operands may consume gas observations before the residual action. *)
Theory bodySliceOrdinaryTerminalPrefixMods
Ancestors
  exprSimSliceSource exprSimDefs vyperInterpreter vyperState vyperContext
  vyperValueOperation vyperValue vyperTypeSystem vyperTyping list words
Libs monadsyntax

Theorem slice_ordinary_terminal_prefix_mods:
  ((expr_type src = BaseT (BytesT bd) /\ v = BytesV bs) \/
   (?m str. expr_type src = BaseT (StringT m) /\ v = StringV str /\
      bs = MAP (n2w o ORD) str)) /\
  slice_operands_ok (Slice n) [src;start;len] /\
  value_runtime_typed env (expr_type src) v /\
  code_slice_source (Slice n) [src;start;len] = NONE /\
  (!tail. eval_exprs cx [src;start;len] (es with gas_obs := prefix ++ tail) =
      (INL [v;IntV (&i);IntV (&k)], ee with gas_obs := tail)) ==>
  (i+k <= LENGTH bs ==> k <= n) /\
  (!tail. eval_expr cx (Builtin ann (Slice n) [src;start;len])
      (es with gas_obs := prefix ++ tail) =
    (do acc <- get_accounts;
        v' <- lift_sum (evaluate_builtin cx acc ann (Slice n)
          (MAP expr_type [src;start;len]) [v;IntV (&i);IntV (&k)]);
        return (Value v') od) (ee with gas_obs := tail))
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  conj_tac
  >- (qpat_x_assum `!tail. eval_exprs _ _ _ = _` (qspec_then `[]` assume_tac) >>
      qpat_x_assum `_ \/ _` (DISJ_CASES_THEN STRIP_ASSUME_TAC)
      >- (strip_tac >> metis_tac[slice_bytes_capacity]) >>
      qpat_x_assum `v = StringV _` SUBST_ALL_TAC >>
      qpat_x_assum `bs = MAP _ _` SUBST_ALL_TAC >>
      simp[] >> strip_tac >> metis_tac[slice_string_capacity]) >>
  qx_gen_tac `tail` >>
  drule_then (pure_once_rewrite_tac o single) slice_eval_ordinary >>
  qpat_x_assum `!tail. eval_exprs _ _ _ = _` (qspec_then `tail` assume_tac) >>
  simp[bind_def]
QED
