Theory stmtSimLogDataRun
Ancestors
  exprSimDefs exprSimProps exprSimStack loweringPosts
  stmtSimLogData stmtSimLogDataFrame  valueEncoding valueEncodingDefs compileEnv
  context stmtLowering words list arithmetic emitHelper emitHelperProps
  exprSimBufferStore exprLoweringProps

Definition log_data_layout_def:
  (log_data_layout cx [] [] p mem = T) /\
  (log_data_layout cx [] (v::vs) p mem = F) /\
  (log_data_layout cx (ty::tys) [] p mem = F) /\
  (log_data_layout cx (ty::tys) (v::vs) p mem =
    ?tv. evaluate_type (get_tenv cx) ty = SOME tv /\ val_wf tv v /\
         val_in_memory tv v p mem /\
         log_data_layout cx tys vs (p + type_memory_size tv) mem)
End

Theorem log_data_layout_lengths:
  !tys vs p mem. log_data_layout cx tys vs p mem ==> LENGTH tys = LENGTH vs
Proof
  Induct_on `tys` >> Cases_on `vs` >> simp[log_data_layout_def] >>
  rpt strip_tac >> first_x_assum drule >> simp[]
QED

Theorem log_data_layout_tuple:
  !tys vs p mem. log_data_layout cx tys vs p mem ==>
  ?tvs. LIST_REL (\ty tv. evaluate_type (get_tenv cx) ty = SOME tv) tys tvs /\
    tuple_in_memory vs tvs p mem /\ EVERY2 val_wf tvs vs
Proof
  Induct_on `tys` >> Cases_on `vs` >> simp[log_data_layout_def]
  >- simp[val_in_memory_def] >>
  rpt strip_tac >> rename1 `evaluate_type (get_tenv cx) ty = SOME tv` >>
  first_x_assum drule >> strip_tac >>
  rename1 `LIST_REL _ tys tvs` >>
  qexists_tac `tv::tvs` >> simp[val_in_memory_def]
QED

Theorem log_data_layout_suffix_frame:
  !tys vs p mem. log_data_layout cx tys vs p mem /\
    EVERY supported_scalar_type tys /\
    log_write_frame st (p + SUM (MAP (type_memory_bytes cenv) tys)) n s t /\
    s.vs_memory = mem ==>
    log_data_layout cx tys vs p t.vs_memory
Proof
  Induct_on `tys` >> Cases_on `vs` >> simp[log_data_layout_def] >>
  rpt strip_tac >> rename1 `evaluate_type (get_tenv cx) ty = SOME tv` >>
  `type_memory_bytes cenv ty = type_memory_size tv` by
    (drule_all log_scalar_memory_size >> simp[]) >>
  simp[log_data_layout_def] >> conj_tac
  >- (irule valueEncodingPropsTheory.val_in_memory_mem_agree >>
      simp[] >> qexistsl_tac [`type_memory_size tv`, `s.vs_memory`] >> simp[] >>
      gvs[log_write_frame_def] >> first_x_assum irule >> decide_tac) >>
  first_x_assum irule >> simp[] >>
  `p + type_memory_size tv + SUM (MAP (type_memory_bytes cenv) tys) =
   p + (SUM (MAP (type_memory_bytes cenv) tys) + type_memory_bytes cenv ty)`
    by decide_tac >> metis_tac[]
QED

Theorem compile_log_store_data_shape:
  !xs buf off sa sb. EVERY (supported_scalar_type o SND) xs /\
    compile_log_store_data cenv xs (MAP SND xs) buf off sa = ((),sb) ==>
    same_blocks sa sb /\
    sb.cs_current_insts = sa.cs_current_insts ++ emitted_insts sa sb /\
    sa.cs_next_var <= sb.cs_next_var /\ sa.cs_next_id <= sb.cs_next_id
Proof
  Induct_on `xs`
  >- simp[compile_log_store_data_def, comp_return_def, same_blocks_def,
          emitted_insts_def] >>
  gen_tac >> PairCases_on `h` >> simp[] >> rpt gen_tac >> strip_tac >>
  qpat_x_assum `compile_log_store_data _ _ _ _ _ _ = _` mp_tac >>
  simp[compile_log_store_data_scalar_cons, comp_bind_def, comp_ignore_bind_def,
       pairTheory.pair_case_eq] >>
  Cases_on `emit_op ADD [buf; Lit (n2w off)] sa` >>
  rename1 `emit_op ADD [buf; Lit (n2w off)] sa = (dst,sm)` >>
  Cases_on `compile_store_memory cenv h0 dst h1 h1 sm` >>
  gvs[] >> strip_tac >>
  rename1 `compile_store_memory cenv h0 dst h1 h1 sm = ((),sn)` >>
  drule emit_op_extends >> strip_tac >>
  drule log_data_address_shape >> strip_tac >>
  `sa.cs_next_id <= sm.cs_next_id` by
    (qpat_x_assum `emit_op _ _ _ = _` mp_tac >>
     simp[emit_op_def, comp_bind_def, comp_ignore_bind_def, comp_return_def,
       fresh_var_def, fresh_id_def, emit_def] >> strip_tac >> gvs[]) >>
  drule buffer_store_memory_shape >> strip_tac >>
  first_x_assum drule_all >> strip_tac >>
  `inst_extends sa sm /\ inst_extends sm sn /\ inst_extends sn sb` by
    simp[inst_extends_def] >>
  `inst_extends sm sb` by
    (irule inst_extends_trans >> qexists_tac `sn` >> simp[]) >>
  `inst_extends sa sb` by
    (irule inst_extends_trans >> qexists_tac `sm` >> simp[]) >>
  gvs[inst_extends_def, same_blocks_def] >> decide_tac
QED

Definition log_data_source_def:
  log_data_source cx b cap s (op,ty) v <=>
    supported_scalar_type ty /\
    (?tv. evaluate_type (get_tenv cx) ty = SOME tv /\
      value_has_type tv v /\ val_wf tv v) /\
    expr_val_rel cx ty v op s /\ log_source_apart cx b cap (op,ty) v s
End

Theorem log_data_sources_kept:
  !xs vs. LIST_REL (log_data_source cx b cap s) xs vs /\
    EVERY (\(op,ty). !x. op = Var x ==> not_fresh_at st x) xs /\
    log_write_frame st b cap s t ==>
    LIST_REL (log_data_source cx b cap t) xs vs
Proof
  Induct_on `xs` >- simp[] >>
  gen_tac >> PairCases_on `h` >> Cases_on `vs` >> simp[log_data_source_def] >>
  rpt gen_tac >> strip_tac >> simp[] >> conj_tac
  >- (drule_all log_source_value_kept >> simp[]) >>
  drule_all log_source_apart_kept >> simp[]
QED

Theorem log_data_sources_types:
  !xs vs. LIST_REL (log_data_source cx b cap s) xs vs ==>
    EVERY (supported_scalar_type o SND) xs
Proof
  Induct_on `xs` >- simp[] >>
  gen_tac >> PairCases_on `h` >> Cases_on `vs` >>
  simp[log_data_source_def] >> metis_tac[]
QED

Theorem log_data_fresh_mono:
  EVERY (\(op,ty). !x. op = Var x ==> not_fresh_at sa x) xs /\
  sa.cs_next_var <= sb.cs_next_var ==>
  EVERY (\(op,ty). !x. op = Var x ==> not_fresh_at sb x) xs
Proof
  simp[EVERY_MEM] >> rpt strip_tac >> PairCases_on `e` >> gvs[] >>
  rpt strip_tac >> irule freshWritesTheory.not_fresh_at_mono >> qexists_tac `sa` >>
  simp[] >> first_x_assum drule >> simp[]
QED

Theorem compile_log_store_data_scalar_split:
  supported_scalar_type ty /\
  compile_log_store_data cenv ((src,ty)::xs) (ty::MAP SND xs) buf off sa = ((),sb) ==>
  ?dst sm sn. emit_op ADD [buf; Lit (n2w off)] sa = (dst,sm) /\
    compile_store_memory cenv src dst ty ty sm = ((),sn) /\
    compile_log_store_data cenv xs (MAP SND xs) buf (off + type_memory_bytes cenv ty) sn = ((),sb) /\
    inst_extends sa sn /\ sa.cs_next_var <= sn.cs_next_var
Proof
  strip_tac >> qpat_x_assum `compile_log_store_data _ _ _ _ _ _ = _` mp_tac >>
  simp[compile_log_store_data_scalar_cons, comp_bind_def, comp_ignore_bind_def] >>
  Cases_on `emit_op ADD [buf; Lit (n2w off)] sa` >>
  rename1 `emit_op ADD [buf; Lit (n2w off)] sa = (dst,sm)` >>
  Cases_on `compile_store_memory cenv src dst ty ty sm` >>
  rename1 `compile_store_memory cenv src dst ty ty sm = (u,sn)` >>
  Cases_on `u` >> simp[] >> strip_tac >>
  drule emit_op_extends >> strip_tac >>
  drule log_data_address_shape >> strip_tac >>
  drule buffer_store_memory_shape >> strip_tac >>
  conj_tac
  >- (irule inst_extends_trans >> qexists_tac `sm` >> simp[inst_extends_def]) >>
  decide_tac
QED

Theorem log_write_frame_frontier:
  log_write_frame sb b n s t /\ sa.cs_next_var <= sb.cs_next_var ==>
  log_write_frame sa b n s t
Proof
  simp[log_write_frame_def] >> strip_tac >>
  conj_tac
  >- (rpt strip_tac >>
      `not_fresh_at sb x` by
        (irule freshWritesTheory.not_fresh_at_mono >> qexists_tac `sa` >> simp[]) >>
      metis_tac[]) >> first_assum ACCEPT_TAC
QED

Theorem log_data_layout_cons_suffix:
  supported_scalar_type ty /\ evaluate_type (get_tenv cx) ty = SOME tv /\
  val_wf tv v /\ val_in_memory tv v p s.vs_memory /\
  log_data_layout cx tys vs (p + type_memory_bytes cenv ty) t.vs_memory /\
  log_write_frame st (p + type_memory_bytes cenv ty) n s t ==>
  log_data_layout cx (ty::tys) (v::vs) p t.vs_memory
Proof
  strip_tac >>
  `type_memory_bytes cenv ty = type_memory_size tv` by
    (drule_all log_scalar_memory_size >> simp[]) >>
  gvs[log_data_layout_def] >>
  irule valueEncodingPropsTheory.val_in_memory_mem_agree >> simp[] >>
  qexistsl_tac [`type_memory_size tv`, `s.vs_memory`] >> simp[] >>
  gvs[log_write_frame_def] >> first_x_assum irule >> simp[]
QED

Theorem log_write_frame_join:
  log_write_frame sa p a s q /\ log_write_frame sb (p+a) n q t /\
  sa.cs_next_var <= sb.cs_next_var ==>
  log_write_frame sa p (a+n) s t
Proof
  strip_tac >>
  `log_write_frame sa (p+a) n q t` by
    (drule_all log_write_frame_frontier >> simp[]) >>
  irule log_write_frame_trans >> qexists_tac `q` >> conj_tac
  >- (irule log_write_frame_widen >> goal_assum (drule_at Any) >> decide_tac) >>
  irule log_write_frame_widen >> goal_assum (drule_at Any) >> decide_tac
QED

Theorem compile_log_store_data_run_core[local]:
  !xs vs off sa sb s.
    compile_log_store_data cenv xs (MAP SND xs) buf off sa = ((),sb) /\
    LIST_REL (log_data_source cx b cap s) xs vs /\
    EVERY (\(op,ty). !x. op = Var x ==> not_fresh_at sa x) xs /\
    (!x. buf = Var x ==> not_fresh_at sa x) /\
    eval_operand buf s = SOME (n2w b) /\
    off + SUM (MAP (type_memory_bytes cenv) (MAP SND xs)) <= cap /\
    b + cap < dimword (:256) ==>
    ?t. run_inst_seq (emitted_insts sa sb) s = OK t /\
      log_data_layout cx (MAP SND xs) vs (b + off) t.vs_memory /\
      log_write_frame sa (b + off)
        (SUM (MAP (type_memory_bytes cenv) (MAP SND xs))) s t
Proof
  Induct_on `xs`
  >- (simp[compile_log_store_data_def, comp_return_def] >> rpt strip_tac >>
      gvs[emitted_insts_def, log_data_layout_def, run_inst_seq_def]) >>
  gen_tac >> PairCases_on `h` >> Cases_on `vs` >> simp[] >>
  rpt gen_tac >> strip_tac >>
  rename1 `log_data_source cx b cap s (src,ty) v` >>
  rename1 `LIST_REL (log_data_source cx b cap s) xs vs0` >>
  `supported_scalar_type ty` by gvs[log_data_source_def] >>
  drule_all compile_log_store_data_scalar_split >> strip_tac >>
  qpat_x_assum `log_data_source _ _ _ _ _ _` mp_tac >>
  simp[log_data_source_def] >> strip_tac >>
  `b + off < dimword (:256) /\ type_memory_bytes cenv ty < dimword (:256)`
    by decide_tac >>
  drule_all log_data_field_run >> strip_tac >>
  `type_memory_bytes cenv ty = type_memory_size tv` by
    (drule_all log_scalar_memory_size >> simp[]) >>
  `log_write_frame sa (b + off) (type_memory_bytes cenv ty) s q` by
    (simp[log_write_frame_def] >> rpt strip_tac >>
     first_x_assum irule >> decide_tac) >>
  `log_write_frame sa b cap s q` by
    (irule log_write_frame_widen >> goal_assum (drule_at Any) >> decide_tac) >>
  drule_all log_data_sources_kept >> strip_tac >>
  drule_all log_write_frame_operand >> strip_tac >>
  drule_all log_data_fresh_mono >> strip_tac >>
  `!x. buf = Var x ==> not_fresh_at sn x` by
    (rpt strip_tac >> irule freshWritesTheory.not_fresh_at_mono >>
     qexists_tac `sa` >> simp[]) >>
  `off + type_memory_bytes cenv ty +
     SUM (MAP (type_memory_bytes cenv) (MAP SND xs)) <= cap` by decide_tac >>
  `eval_operand buf q = SOME (n2w b)` by simp[] >>
  first_x_assum drule_all >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts sn sb) q = OK u` >>
  `EVERY (supported_scalar_type o SND) xs` by
    (drule_all log_data_sources_types >> simp[]) >>
  drule_all compile_log_store_data_shape >> strip_tac >>
  `sn.cs_current_insts = sa.cs_current_insts ++ emitted_insts sa sn` by
    gvs[inst_extends_def] >>
  drule_all run_inst_seq_chain >> strip_tac >>
  qexists_tac `u` >> simp[] >> conj_tac
  >- (irule log_data_layout_cons_suffix >> simp[] >>
      qexistsl_tac [`cenv`, `SUM (MAP (type_memory_bytes cenv) (MAP SND xs))`,
                   `q`, `sn`] >> simp[GSYM ADD_ASSOC]) >>
  CONV_TAC (RATOR_CONV (RATOR_CONV (RAND_CONV (REWR_CONV ADD_COMM)))) >>
  irule log_write_frame_join >>
  qexistsl_tac [`q`, `sn`] >> gvs[GSYM ADD_ASSOC]
QED

Theorem compile_log_store_data_run:
  compile_log_store_data cenv xs (MAP SND xs) buf off sa = ((),sb) /\
  LIST_REL (log_data_source cx b cap s) xs vs /\
  EVERY (\(op,ty). !x. op = Var x ==> not_fresh_at sa x) xs /\
  (!x. buf = Var x ==> not_fresh_at sa x) /\
  eval_operand buf s = SOME (n2w b) /\
  off + SUM (MAP (type_memory_bytes cenv) (MAP SND xs)) <= cap /\
  b + cap < dimword (:256) ==>
  inst_extends sa sb /\ sa.cs_next_var <= sb.cs_next_var /\
  ?t. run_inst_seq (emitted_insts sa sb) s = OK t /\
    log_data_layout cx (MAP SND xs) vs (b + off) t.vs_memory /\
    log_write_frame sa (b + off)
      (SUM (MAP (type_memory_bytes cenv) (MAP SND xs))) s t /\
    LIST_REL (log_data_source cx b cap t) xs vs /\
    eval_operand buf t = SOME (n2w b) /\
    (!op ty. MEM (op,ty) xs ==> eval_operand op t = eval_operand op s)
Proof
  strip_tac >> drule_all compile_log_store_data_run_core >> strip_tac >>
  drule_all log_data_sources_types >> strip_tac >>
  drule_all compile_log_store_data_shape >> strip_tac >>
  simp[inst_extends_def] >>
  `log_write_frame sa b cap s t` by
    (irule log_write_frame_widen >> goal_assum (drule_at Any) >> decide_tac) >>
  drule_all log_data_sources_kept >> strip_tac >> simp[] >> conj_tac
  >- (drule_all log_write_frame_operand >> simp[]) >>
  rpt strip_tac >> irule log_write_frame_operand >>
  goal_assum (drule_at Any) >>
  qpat_x_assum `EVERY (\(op,ty). !x. op = Var x ==> _) xs` mp_tac >>
  simp[EVERY_MEM] >>
  disch_then drule >> simp[]
QED
