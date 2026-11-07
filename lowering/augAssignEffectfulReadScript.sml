(* Scalar reads at saved storage places.  Successful decoding does not
   assert that the underlying word is a canonical encoding. *)
Theory augAssignEffectfulRead
Ancestors
  valueEncoding vyperStorage vyperState vyperTyping
  vyperTypeStatePreservation gasContext vyperInterpreter stmtSimDefs

Theorem scalar_decode_noncanonical:
  decode_base_from_slot 256w (BaseTV (UintT 8)) = IntV 0 /\
  typed_val_to_w256 (BaseTV (UintT 8))
    (decode_base_from_slot 256w (BaseTV (UintT 8))) <> 256w
Proof
  EVAL_TAC >> simp[SF wordsLib.SIZES_ss] >> EVAL_TAC
QED

Theorem storage_place_read_success_typed:
  evaluate_type (get_tenv cx) ty = SOME tv /\
  read_place cx (StoragePlace tr slot tv) st = (INL cur,st') ==>
  value_has_type tv cur
Proof
  strip_tac >>
  `well_formed_type_value tv` by
    metis_tac[cj 1 evaluate_type_well_formed] >>
  irule read_storage_slot_success_type >>
  gvs[read_place_def] >> goal_assum (drule_at Any) >> simp[]
QED

(* Keep the read and type-value prefix intact; admissibility need not
   imply range validity for a saved, now-dead storage path. *)
Theorem augassign_target_continuation_admissible:
  gas_admissible (eval_stmt cx (AugAssign ty bt bop e))
    (stmt_res_ok lctx) es /\
  (!tail. eval_target_place cx bt (es with gas_obs := prefix ++ tail) =
    (INL p, mid with gas_obs := tail)) ==>
  gas_admissible
    (bind (read_place cx p) (\cur.
       bind (place_type_value cx p) (\ptv.
       bind (eval_expr cx e) (\raw.
       bind (read_result cx raw) (\v.
       bind (lift_sum (evaluate_binop
         (case type_to_int_bound ty of SOME b => b | NONE => Unsigned 0)
         ptv bop cur v)) (write_place cx p))))))
    (stmt_res_ok lctx) mid
Proof
  simp[gas_admissible_def] >> rpt strip_tac >>
  qpat_x_assum `!gs res ee. _`
    (qspec_then `prefix ++ gs` mp_tac) >>
  simp[Once evaluate_def] >> fs[bind_def] >> metis_tac[]
QED
