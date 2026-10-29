Theory vyperRawRevert
Ancestors
  vyperInterpreter vyperSmallStep[ignore_grammar] vyperState vyperValue
  vyperValueOperation

(* Revert data is the original byte vector, with no ABI envelope. *)
Theorem raw_revert_bytes:
  eval_exprs cx es st = (INL [BytesV data], st') ==>
  eval_expr cx (Call ty RawRevert es extra) st =
    (INR (Error (RevertData data)), st')
Proof
  strip_tac >> simp[Once evaluate_def, bind_def, ignore_bind_def,
    type_check_def, assert_def, return_def, raise_def,
    lift_option_type_def, dest_BytesV_def]
QED

Theorem raw_revert_argument_error:
  eval_exprs cx es st = (INR ex, st') ==>
  eval_expr cx (Call ty RawRevert es extra) st = (INR ex, st')
Proof
  strip_tac >> simp[Once evaluate_def, bind_def]
QED

Theorem raw_revert_cps_bytes:
  vyperSmallStep$apply_vals cx [BytesV data] st (vyperSmallStep$RawRevertK k) =
    vyperSmallStep$AK cx (vyperSmallStep$ApplyExc (Error (RevertData data))) st k
Proof
  simp[Once vyperSmallStepTheory.apply_vals_def, bind_def, ignore_bind_def,
    type_check_def, assert_def, return_def, raise_def,
    lift_option_type_def, dest_BytesV_def]
QED

(* Kernel tag audit for the data-boundary regression facts. *)
val _ = List.app (fn (name, th) =>
  if null (List.filter (fn s => s <> "DISK_THM")
             (#1 (Tag.dest_tag (Thm.tag th)))) then ()
  else raise Fail ("oracle in raw revert boundary: " ^ name))
  (DB.thms "vyperRawRevert");
