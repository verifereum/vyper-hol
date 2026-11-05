(* Interval-local fetch interface; no restriction on unrelated function code. *)
Theory bodyPtrWordBuiltinsIntervalWitness
Ancestors bodyPtrWordBuiltinsIntervalDataflow fragExec
Libs finite_mapLib intReduce

val () = computeLib.upd_compset add_finite_map_compset
val () = computeLib.upd_compset intReduce.add_int_compset

Theorem word_interval_operand_embedding:
  lower_value compile_expr (FST word_interval_start) (BaseT (IntT 256))
    (IfExp (BaseT (IntT 256)) (Name (BaseT BoolT) "b")
      (Literal (BaseT (IntT 256)) (IntL 1))
      (Literal (BaseT (IntT 256)) (IntL 2)))
    (SND word_interval_start) = (op,sm) /\
  fn_has_code (SND word_interval_start) sm fn ==>
  ?entry then_bb else_bb join_bb.
    lookup_block "entry" fn.fn_blocks = SOME entry /\
    lookup_block "@then_0" fn.fn_blocks = SOME then_bb /\
    lookup_block "@else_1" fn.fn_blocks = SOME else_bb /\
    lookup_block "@exit_2" fn.fn_blocks = SOME join_bb /\
    then_bb.bb_label = "@then_0" /\ else_bb.bb_label = "@else_1"
Proof
  EVAL_TAC >> rpt strip_tac >> gvs[fn_has_code_def, emitted_blocks_def] >>
  CONV_TAC (computeLib.RESTR_EVAL_CONV [``lookup_block``]) >>
  gvs[DISJ_IMP_THM, FORALL_AND_THM] >> metis_tac[]
QED

(* The final empty prefix does not restrict instructions run on join entry. *)
Theorem word_interval_operand_join_unrestricted:
  !op sm insts.
  lower_value compile_expr (FST word_interval_start) (BaseT (IntT 256))
    (IfExp (BaseT (IntT 256)) (Name (BaseT BoolT) "b")
      (Literal (BaseT (IntT 256)) (IntL 1))
      (Literal (BaseT (IntT 256)) (IntL 2)))
    (SND word_interval_start) = (op,sm) ==>
  fn_has_code (SND word_interval_start) sm
    (word_interval_function with fn_blocks :=
      <|bb_label := "@exit_2"; bb_instructions := insts|> ::
      FILTER (\bb. bb.bb_label <> "@exit_2") word_interval_function.fn_blocks)
Proof
  EVAL_TAC >> rpt strip_tac >> gvs[fn_has_code_def, emitted_blocks_def] >>
  EVAL_TAC >> rpt strip_tac >> gvs[] >> EVAL_TAC
QED
