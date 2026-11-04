Theory abiArgsObserverProbe
Ancestors
  exprLowering compileEnv context vyperAST fragExec venomWf
  venomInst finite_map

Definition observer_probe_start_def:
  observer_probe_start = <| cs_next_var := 0; cs_next_label := 0;
    cs_next_id := 0; cs_current_bb := "@exit_2"; cs_current_insts := [];
    cs_blocks := []; cs_data_sections := [] |>
End

Definition observer_probe_end_def:
  observer_probe_end ce = SND (lower_value compile_expr ce (BaseT BoolT)
    (IfExp (BaseT BoolT) (Literal (BaseT BoolT) (BoolL T))
      (Literal (BaseT BoolT) (BoolL T)) (Literal (BaseT BoolT) (BoolL F)))
    observer_probe_start)
End

Theorem observer_probe_collision:
  let ce = ce with ce_vars := FEMPTY in
  let sb = observer_probe_end ce in
  sb.cs_current_insts = [] /\
  (?bb. MEM bb (emitted_blocks observer_probe_start sb) /\
        bb.bb_label = sb.cs_current_bb) /\
  fn_has_code observer_probe_start sb
    (fn with fn_blocks := sb.cs_blocks) /\
  fn_inst_ids_distinct (fn with fn_blocks := sb.cs_blocks)
Proof
  EVAL_TAC >> rpt conj_tac
  >- (qexists_tac `LAST (observer_probe_end (ce with ce_vars := FEMPTY)).cs_blocks` >> EVAL_TAC)
  >- (rpt strip_tac >> gvs[] >> EVAL_TAC) >>
  CONV_TAC (RAND_CONV (REWR_CONV (GSYM ETA_THM))) >> BETA_TAC >> simp[]
QED

(* The direct uncaptured Label image has no emitted code, even with hostile
   initial labels. This tests only Name, not all forwarding constructors. *)
Theorem observer_probe_name_label:
  FLOOKUP ce.ce_vars id = SOME (PtrVar (Label l) sz) /\
  ~is_word_type (expr_type (Name ann id)) ==>
  lower_value compile_expr ce ty (Name ann id) sa = (Label l,sa) /\
  (!bb. MEM bb (emitted_blocks sa sa) ==> bb.bb_label <> sa.cs_current_bb)
Proof
  simp[lower_value_def, comp_bind_def, Once compile_expr_def,
       compile_expr_body_def, compile_name_vv_def, unwrap_value_def,
       mk_ptr_def, comp_return_def, emitted_blocks_def]
QED
