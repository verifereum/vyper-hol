(* Source normalization and arbitrary-tail replay for the actual AugAssign prefix. *)
Theory augAssignFullSourceReplay
Ancestors
  stmtSimAugAssignPlaceMemory exprSimIfExpWidenedAdapter exprSimMemorySource
  vyperInterpreter vyperState

Theorem augassign_source_bind:
  eval_stmt cx (AugAssign ty bt bop e) =
  bind (eval_target_place cx bt) (\p.
    bind (read_place cx p) (\cur.
      bind (place_type_value cx p) (\ptv.
        bind (bind (eval_expr cx e) (read_result cx)) (\rhs.
          bind (lift_sum (evaluate_binop
            (case type_to_int_bound ty of SOME b => b | NONE => Unsigned 0)
            ptv bop cur rhs)) (write_place cx p)))))
Proof
  simp[Once evaluate_def, bind_assoc, SF ETA_ss]
QED

Theorem augassign_source_prefix_replay:
  (!gs. eval_target_place cx bt (es0 with gas_obs := preT ++ gs) =
    (INL p, st with gas_obs := gs)) /\
  read_place cx p st = (INL cur,st) /\
  place_type_value cx p st = (INL ptv,st) /\
  (!gs. bind (eval_expr cx e) (read_result cx)
    (st with gas_obs := preE ++ gs) = (INL rhs,ee with gas_obs := gs)) ==>
  !gs. eval_stmt cx (AugAssign ty bt bop e)
    (es0 with gas_obs := (preT ++ preE) ++ gs) =
    bind (lift_sum (evaluate_binop
      (case type_to_int_bound ty of SOME b => b | NONE => Unsigned 0)
      ptv bop cur rhs)) (write_place cx p) (ee with gas_obs := gs)
Proof
  strip_tac >>
  `read_result cx (PlaceR p) st = (INL cur,st)` by
    simp[read_result_def] >>
  drule read_result_gas_obs >>
  pure_rewrite_tac[read_result_def] >> strip_tac >>
  drule place_type_value_gas_obs >> strip_tac >>
  gen_tac >>
  rewrite_tac[augassign_source_bind, GSYM listTheory.APPEND_ASSOC] >>
  once_rewrite_tac[bind_def] >> simp[] >>
  ntac 3 (once_rewrite_tac[bind_def] >> simp[]) >>
  rewrite_tac[bind_def]
QED
