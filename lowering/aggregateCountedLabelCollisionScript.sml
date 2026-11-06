Theory aggregateCountedLabelCollision
Ancestors
  exprSimAbiGasBridge context compileEnv vyperAST venomExecSemantics

Theorem aggregate_typed_sarray_exit_collision_probe:
  let sa = <| cs_next_var := 0; cs_next_label := 0; cs_next_id := 0;
              cs_current_bb := fresh_label_output "typed_sa_exit" 2;
              cs_current_insts := []; cs_blocks := []; cs_data_sections := [] |> in
  let sb = SND (compile_copy_sarray_typed ce (Var "dst") (BaseT (UintT 256))
                  (Var "src") (TupleT []) 2 sa) in
  let fn = (ARB:ir_function) with fn_blocks := sb.cs_blocks in
  fn_has_code sa sb fn /\ fn_inst_ids_distinct fn /\
  sa.cs_current_bb = sb.cs_current_bb /\ ~frag_gas_free sa sb
Proof
  EVAL_TAC >> rpt strip_tac >> gvs[] >>
  CONV_TAC (RAND_CONV (REWR_CONV (GSYM ETA_AX))) >> simp[]
QED

Theorem aggregate_typed_sarray_completed_collision_probe:
  !lbl. MEM lbl [fresh_label_output "typed_sa_cond" 0;
                fresh_label_output "typed_sa_body" 1] ==>
  let sa = <| cs_next_var := 0; cs_next_label := 0; cs_next_id := 0;
              cs_current_bb := lbl;
              cs_current_insts := []; cs_blocks := []; cs_data_sections := [] |> in
  let sb = SND (compile_copy_sarray_typed ce (Var "dst") (BaseT (UintT 256))
                  (Var "src") (TupleT []) 2 sa) in
  !fn. ~fn_has_code sa sb fn
Proof
  simp[] >> rpt strip_tac >> gvs[] >>
  qpat_x_assum `fn_has_code _ _ _` mp_tac >> EVAL_TAC >>
  rpt strip_tac >> gvs[DISJ_IMP_THM, FORALL_AND_THM] >>
  gvs[]
QED
