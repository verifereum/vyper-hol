(* Transfer statement admissibility through the counted target and pure reads. *)
Theory augAssignPlaceSourcePrefix
Ancestors
  stmtSimAugAssignPlaceMemory stmtSimAugAssignPlaceStorage
  exprSimLen vyperInterpreter gasContext vyperState

Theorem aug_place_memory_reads_replay:
  read_place cx (MemoryPlace id path) mid = (INL cur,mid) /\
  place_type_value cx (MemoryPlace id path) mid = (INL ptv,mid) ==>
  (!gs. read_place cx (MemoryPlace id path) (mid with gas_obs := gs) =
    (INL cur,mid with gas_obs := gs)) /\
  (!gs. place_type_value cx (MemoryPlace id path) (mid with gas_obs := gs) =
    (INL ptv,mid with gas_obs := gs))
Proof
  strip_tac >> conj_tac
  >- simp[exprSimLenTheory.len_rp_obs] >>
  Cases_on `lookup_scopes id mid.scopes` >>
  gvs[place_type_value_def, get_scopes_def, bind_def, return_def,
      lift_option_type_def, lift_sum_def, raise_def] >>
  Cases_on `subscripts_type x.type path` >> gvs[return_def, raise_def]
QED

Theorem aug_place_rhs_suffix_admissible:
  gas_admissible (eval_stmt cx (AugAssign ty bt bop e)) A es /\
  (!tail. eval_target_place cx bt (es with gas_obs := prefix ++ tail) =
    (INL p,mid with gas_obs := tail)) /\
  (!gs. read_place cx p (mid with gas_obs := gs) =
    (INL cur,mid with gas_obs := gs)) /\
  (!gs. place_type_value cx p (mid with gas_obs := gs) =
    (INL ptv,mid with gas_obs := gs)) ==>
  gas_admissible
    (bind (bind (eval_expr cx e) (read_result cx))
      (\rhs. bind (lift_sum (evaluate_binop
        (case type_to_int_bound ty of SOME b => b | NONE => Unsigned 0)
        ptv bop cur rhs)) (write_place cx p))) A mid
Proof
  strip_tac >>
  qpat_x_assum `gas_admissible _ _ _` mp_tac >>
  simp[gas_admissible_def] >> strip_tac >> rpt gen_tac >> strip_tac >>
  qpat_x_assum `!gs res ee. _` (qspec_then `prefix ++ gs` mp_tac) >>
  simp[Once evaluate_def, bind_def] >>
  qpat_x_assum `bind _ _ _ = _` mp_tac >>
  pure_rewrite_tac[bind_assoc] >> simp[bind_def] >> metis_tac[]
QED
