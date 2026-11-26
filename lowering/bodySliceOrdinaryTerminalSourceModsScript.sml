(* Source-only terminal action and guarded capacity for ordinary Slice. *)
Theory bodySliceOrdinaryTerminalSourceMods
Ancestors
  bodySliceStringCapacityMods
  exprSimSliceSource exprSimDefs vyperInterpreter vyperState vyperContext
  vyperValueOperation vyperValue vyperTypeSystem vyperTyping
  list words

Theorem slice_ordinary_terminal_source_mods:
  ((expr_type src = BaseT (BytesT bd) /\ v = BytesV bs) \/
   (?m str. expr_type src = BaseT (StringT m) /\ v = StringV str /\
      bs = MAP (n2w o ORD) str)) /\
  slice_operands_ok (Slice n) [src;start;len] /\
  value_runtime_typed env (expr_type src) v /\
  code_slice_source (Slice n) [src;start;len] = NONE /\
  (!tail. eval_exprs cx [src;start;len] (es with gas_obs := tail) =
      (INL [v;IntV (&i);IntV (&k)], ee with gas_obs := tail)) ==>
  (i+k <= LENGTH bs ==> k <= n) /\
  (!tail. eval_expr cx (Builtin ann (Slice n) [src;start;len])
      (es with gas_obs := tail) =
    (do acc <- get_accounts;
        v' <- lift_sum (evaluate_builtin cx acc ann (Slice n)
          (MAP expr_type [src;start;len]) [v;IntV (&i);IntV (&k)]);
        return (Value v') od) (ee with gas_obs := tail))
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  conj_tac
  >- (qpat_x_assum `_ \/ _` (DISJ_CASES_THEN STRIP_ASSUME_TAC)
      >- (strip_tac >>
          qpat_x_assum `!tail. eval_exprs _ _ _ = _`
            (qspec_then `[]` assume_tac) >>
          metis_tac[slice_bytes_capacity])
      >- (qpat_x_assum `v = StringV _` SUBST_ALL_TAC >>
          qpat_x_assum `bs = MAP _ _` SUBST_ALL_TAC >>
          metis_tac[slice_string_capacity_all_tail]))
  >- (qx_gen_tac `tail` >>
      qpat_assum `code_slice_source _ _ = NONE`
        (fn th => assume_tac (MATCH_MP slice_eval_ordinary th)) >>
      qpat_x_assum `!tail. eval_exprs _ _ _ = _` (qspec_then `tail` assume_tac) >>
      simp[bind_def, lift_sum_def, return_def, bind_assoc])
QED
