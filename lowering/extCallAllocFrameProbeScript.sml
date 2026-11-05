Theory extCallAllocFrameProbe
Ancestors exprLowering

Theorem intcall_struct_fields_frame_counterexample:
  !c fid.
    (c with ce_func_return_type := K NoneT).ce_struct_fields =
      (c with ce_func_return_type := K (TupleT [])).ce_struct_fields /\
    lowered_value_type (c with ce_func_return_type := K NoneT)
      (Call NoneT (IntCall fid) [] NONE) <>
    lowered_value_type (c with ce_func_return_type := K (TupleT []))
      (Call NoneT (IntCall fid) [] NONE)
Proof
  simp[lowered_value_type_def]
QED

val _ =
  let val (ors,axs) = Tag.dest_tag
        (Thm.tag intcall_struct_fields_frame_counterexample)
  in
    if List.exists (fn s => s <> "DISK_THM") ors orelse not (null axs)
    then raise Fail "Allocation frame probe has oracle dependencies"
    else print "Allocation frame counterexample: no admissions or axioms\n"
  end;
