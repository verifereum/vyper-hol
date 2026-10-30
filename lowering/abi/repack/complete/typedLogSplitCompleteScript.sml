(* TOP-LEVEL: actual indexed/data splitting preserves checked widening and
   complete type evaluations. The real non-indexed store consequently has
   the complete data-packing contract, without a per-field callback. *)
Theory typedLogSplitComplete
Ancestors
  typedLogDataComplete typedLogDataContract eventLogSplitProps
  context stmtLowering compileEnv compileVyper vyperTypeContract vyperContext
  vyperTypeSystem vyperValue list pair

Theorem log_non_indexed_types_select:
  !flags tys.
    log_non_indexed_types flags tys = select_log_args F flags tys
Proof
  Induct_on `flags` >- (Cases >> simp[log_non_indexed_types_def, select_log_args_def]) >>
  MAP_EVERY qx_gen_tac [`flag`, `tys`] >> Cases_on `tys` >> Cases_on `flag` >>
  simp[log_non_indexed_types_def, select_log_args_def]
QED

Theorem select_log_args_list_rel:
  !flags xs ys wanted R.
    LENGTH flags = LENGTH xs /\ LIST_REL R xs ys ==>
    LIST_REL R (select_log_args wanted flags xs) (select_log_args wanted flags ys)
Proof
  Induct_on `flags`
  >- (Cases >> simp[select_log_args_def]) >>
  rpt gen_tac >> Cases_on `xs` >> Cases_on `ys` >> simp[] >> strip_tac >>
  rename1 `select_log_args wanted (flag::flags) _` >>
  Cases_on `flag = wanted` >> simp[select_log_args_def] >>
  first_x_assum irule >> simp[]
QED

Theorem split_log_data_compatible:
  !flags fts args.
    LENGTH flags = LENGTH args /\
    LIST_REL event_arg_compatible fts (MAP SND (args:(operand # type) list)) ==>
    LIST_REL (\fty arg. event_arg_compatible fty (SND arg))
      (log_non_indexed_types flags fts) (SND (split_log_ops args flags))
Proof
  rpt gen_tac >> strip_tac >>
  `LENGTH flags = LENGTH fts` by (imp_res_tac LIST_REL_LENGTH >> fs[]) >>
  `LIST_REL (\fty arg. event_arg_compatible fty (SND arg)) fts args` by fs[LIST_REL_MAP2] >>
  drule split_log_ops_select >> DISCH_TAC >>
  asm_simp_tac bool_ss [log_non_indexed_types_select, SND] >>
  irule select_log_args_list_rel >> simp[]
QED

Theorem checked_compile_split_log_data_complete:
  !tops in_deploy layouts addr art ctx func cenv flags fts args ftvs atvs buf field_offset cs ret cs'.
    check_contract in_deploy layouts addr [(NONE,tops)] = SOME art /\
    cenv.ce_struct_fields = make_struct_fields_map tops /\
    LENGTH flags = LENGTH args /\ LIST_REL event_arg_compatible fts (MAP SND args) /\
    LIST_REL (\ty tv. evaluate_type (type_env tops) ty = SOME tv) fts ftvs /\
    LIST_REL (\arg tv. evaluate_type (type_env tops) (SND arg) = SOME tv) args atvs /\
    compile_log_store_data cenv (SND (split_log_ops args flags))
      (log_non_indexed_types flags fts) buf field_offset cs = (ret,cs') ==>
    log_data_store_contract ctx func (SND (split_log_ops args flags))
      (select_log_args F flags ftvs) (select_log_args F flags atvs) buf field_offset cs cs'
Proof
  rpt gen_tac >> strip_tac >>
  `LENGTH flags = LENGTH fts` by (imp_res_tac LIST_REL_LENGTH >> fs[]) >>
  drule_all split_log_data_compatible >> DISCH_TAC >>
  `LIST_REL (\ty tv. evaluate_type (type_env tops) ty = SOME tv)
    (log_non_indexed_types flags fts) (select_log_args F flags ftvs)` by
    (simp_tac bool_ss [log_non_indexed_types_select] >>
     irule select_log_args_list_rel >> simp[]) >>
  `LIST_REL (\arg tv. evaluate_type (type_env tops) (SND arg) = SOME tv)
    (SND (split_log_ops args flags)) (select_log_args F flags atvs)` by
    (drule split_log_ops_select >> DISCH_TAC >> asm_simp_tac bool_ss [SND] >>
     irule select_log_args_list_rel >> simp[]) >>
  mp_tac (Q.SPECL [`tops`, `in_deploy`, `layouts`, `addr`, `art`, `ctx`, `func`, `cenv`,
    `log_non_indexed_types flags fts`, `SND (split_log_ops args flags)`,
    `select_log_args F flags ftvs`, `select_log_args F flags atvs`,
    `buf`, `field_offset`, `cs`, `ret`, `cs'`] checked_compile_log_data_complete) >> simp[]
QED
