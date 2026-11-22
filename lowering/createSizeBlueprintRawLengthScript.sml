(* Connect the raw blueprint argument length load to the operand relation at
   the actual preparation cut.  The copied arm exposes the LocMemory unwrap
   endpoint explicitly; no pointer fact is inferred from a matching PC. *)
Theory createSizeBlueprintRawLength
Ancestors
  createSizeByteLength createBlueprintRawCopy

Theorem create_blueprint_raw_arg_actual_length:
  expr_type e = BaseT (BytesT (Dynamic k)) /\
  evaluate_type (get_tenv cx) (BaseT (BytesT (Dynamic k))) =
    SOME (BaseTV (BytesT (Dynamic k))) /\
  compile_expr ce (expr_type e) e ca = (vv,cm) /\
  compile_snapshot_vv ce (exprs_can_mutate ce later) vv cm = (saved,cs) /\
  unwrap_value ce saved cs = (raw_op,cu) /\
  compile_create_blueprint_args compile_expr ce T later [e] ca =
    ((data,len),cb) /\
  run_inst_seq (emitted_insts cu cb) u = OK t /\
  (expr_val_rel cx (BaseT (BytesT (Dynamic k))) (BytesV bytes) raw_op u \/
   ?p. saved = LocatedValue (vv_type vv) (mk_ptr (Var p) LocMemory) /\
       unwrap_value ce saved cs = (Var p,cs) /\
       expr_val_rel cx (BaseT (BytesT (Dynamic k))) (BytesV bytes) (Var p) u)
  ==> eval_operand len t = SOME (n2w (LENGTH bytes))
Proof
  strip_tac
  >- metis_tac[create_blueprint_raw_arg_length_word]
  >- (`(raw_op,cu) = (Var p,cs)` by metis_tac[] >>
      `raw_op = Var p /\ cu = cs` by metis_tac[pairTheory.PAIR_EQ] >>
      metis_tac[create_blueprint_raw_arg_length_word])
QED
