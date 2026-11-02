(* TOP-LEVEL: connect the actual LOG split and topic compiler to the declared
   event-field encoding. Non-indexed arguments can have arbitrary types. *)
Theory eventLogSplitProps
Ancestors
  eventTopicsExecProps eventTopicValueProps eventEncodingProps
  stmtLowering compileEnv vyperEvent list
Libs pairLib

Definition select_log_args_def:
  select_log_args wanted [] [] = [] /\
  select_log_args wanted (flag::flags) (x::xs) =
    (if flag = wanted then x::select_log_args wanted flags xs
     else select_log_args wanted flags xs) /\
  select_log_args wanted _ _ = []
End

Theorem select_log_args_MAP:
  !flags xs wanted f.
    select_log_args wanted flags (MAP f xs) =
      MAP f (select_log_args wanted flags xs)
Proof
  Induct_on `flags` >> rpt gen_tac >> Cases_on `xs` >>
  simp[select_log_args_def] >> Cases_on `h = wanted` >> simp[]
QED

Theorem split_log_ops_select:
  !flags args.
    LENGTH flags = LENGTH args ==>
    split_log_ops args flags =
      (MAP (\(arg_op,ty). (arg_op,is_bytestring_type ty))
         (select_log_args T flags args), select_log_args F flags args)
Proof
  Induct_on `flags`
  >- (Cases_on `args` >> simp[split_log_ops_def, select_log_args_def]) >>
  rpt gen_tac >> Cases_on `args` >> simp[] >> strip_tac >>
  rename1 `split_log_ops (arg::rest) (flag::flags)` >>
  PairCases_on `arg` >> Cases_on `flag` >>
  simp[split_log_ops_def, select_log_args_def, LET_THM]
QED

Theorem select_log_args_rel:
  !flags xs ys wanted R.
    LENGTH flags = LENGTH xs /\
    LIST_REL (\(flag,x) y. flag = wanted ==> R x y) (ZIP (flags,xs)) ys ==>
    LIST_REL R (select_log_args wanted flags xs)
      (select_log_args wanted flags ys)
Proof
  Induct_on `flags`
  >- (Cases_on `xs` >> simp[select_log_args_def]) >>
  rpt gen_tac >> Cases_on `xs` >> Cases_on `ys` >> simp[] >> strip_tac >>
  rename1 `LENGTH flags = LENGTH rest` >>
  Cases_on `h = wanted` >> simp[select_log_args_def] >>
  first_x_assum irule >> simp[]
QED

Theorem encode_indexed_event_topics_select:
  !flags tys values.
    LENGTH flags = LENGTH tys /\ LENGTH flags = LENGTH values ==>
    encode_indexed_event_topics flags tys values =
      encode_indexed_event_topics
        (REPLICATE (LENGTH (select_log_args T flags tys)) T)
        (select_log_args T flags tys) (select_log_args T flags values)
Proof
  Induct_on `flags`
  >- (Cases_on `tys` >> Cases_on `values` >>
      simp[encode_indexed_event_topics_def, select_log_args_def]) >>
  rpt gen_tac >> Cases_on `tys` >> Cases_on `values` >> simp[] >>
  strip_tac >> Cases_on `h` >>
  simp[select_log_args_def, encode_indexed_event_topics_def]
QED

Theorem compile_split_log_topics_correct:
  !tenv flags args values field_types cs ops cs' ss.
    LENGTH flags = LENGTH args /\
    LIST_REL (\(flag,arg) v. flag ==> topic_value_rel tenv arg v ss)
      (ZIP (flags,args)) values /\
    LIST_REL event_arg_compatible field_types (MAP SND args) /\
    LIST_REL (\flag ty. flag ==> event_indexable_type ty) flags field_types /\
    compile_log_topic_ops (FST (split_log_ops args flags)) cs = (ops,cs') /\
    fresh_vars_wrt cs ss ==>
    ?out topics.
      run_inst_seq (emitted_insts cs cs') ss = OK out /\
      eval_operands ops out = SOME topics /\
      encode_indexed_event_topics flags field_types values = SOME topics /\
      same_blocks cs cs' /\ fresh_vars_wrt cs' out /\
      (!old w. eval_operand old ss = SOME w ==> eval_operand old out = SOME w) /\
      out with vs_vars := ss.vs_vars = ss
Proof
  rpt gen_tac >> strip_tac >>
  `LENGTH flags = LENGTH values` by
    (qpat_x_assum `LIST_REL _ (ZIP (flags,args)) values`
       (mp_tac o MATCH_MP LIST_REL_LENGTH) >>
     simp[LENGTH_ZIP, arithmeticTheory.MIN_DEF]) >>
  `LIST_REL (\arg v. topic_value_rel tenv arg v ss)
      (select_log_args T flags args) (select_log_args T flags values)` by
    (irule select_log_args_rel >> simp[]) >>
  `split_log_ops args flags =
    (MAP (\(arg_op,ty). (arg_op,is_bytestring_type ty))
       (select_log_args T flags args), select_log_args F flags args)` by
    (irule split_log_ops_select >> simp[]) >>
  fs[] >> drule_all compile_log_topic_ops_correct >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts cs cs') ss = OK final` >>
  rename1 `eval_operands ops final = SOME topics` >>
  `encode_indexed_event_topics flags (MAP SND args) values = SOME topics` by
    (mp_tac (Q.SPECL [`flags`, `MAP SND (args:(operand # type) list)`, `values`]
       encode_indexed_event_topics_select) >>
     simp[select_log_args_MAP]) >>
  `encode_indexed_event_topics flags field_types values =
    encode_indexed_event_topics flags (MAP SND args) values` by
    (irule compatible_indexed_event_topics >> simp[]) >>
  qexistsl_tac [`final`, `topics`] >> simp[]
QED
