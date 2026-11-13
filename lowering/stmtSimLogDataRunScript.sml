Theory stmtSimLogDataRun
Ancestors
  exprSimDefs exprSimProps exprSimStack loweringPosts
  stmtSimLogData stmtSimLogDataFrame  valueEncoding valueEncodingDefs compileEnv
  context stmtLowering words list arithmetic emitHelper emitHelperProps
  exprSimBufferStore exprLoweringProps
  annassignRelayoutBounds annassignRelayoutSource wideningZeroLayout
  venomState placeMemoryCopyEffect exprSimMemoryTransport
  placeMemoryPrimitiveForward venomInst

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

(* The Log lowering emits MCOPY even for an empty field. *)
Theorem log_emit_mcopy_encoding[local]:
  !dst src n sa sb s d w tv v.
    emit_void MCOPY [dst; src; Lit (n2w n)] sa = ((),sb) /\
    eval_operand dst s = SOME d /\ eval_operand src s = SOME w /\
    n < dimword (:256) /\ val_in_memory tv v (w2n w) s.vs_memory /\
    val_wf tv v /\ val_footprint tv v <= n ==>
    ?q. run_inst_seq (emitted_insts sa sb) s = OK q /\
      val_in_memory tv v (w2n d) q.vs_memory /\
      (q with vs_memory := s.vs_memory) = s /\
      (!a k. a + k <= w2n d \/ w2n d + n <= a ==>
        mem_bytes_at a k q.vs_memory = mem_bytes_at a k s.vs_memory)
Proof
  rpt strip_tac >>
  `eval_operand (Lit (n2w n)) s = SOME (n2w n)` by
    simp[venomStateTheory.eval_operand_def] >>
  drule_all buffer_emit_mcopy_run >> simp[] >> strip_tac >>
  simp[buffer_mcopy_restore] >> conj_tac
  >- (irule buffer_mcopy_encoding >> simp[]) >>
  rpt strip_tac >> irule buffer_mcopy_exterior >> simp[]
QED

Theorem log_data_store_aggregate_shape[local]:
  compile_store_memory cenv src dst ty ty sa = ((),sb) ==>
  inst_extends sa sb /\ sa.cs_next_var <= sb.cs_next_var /\
  sa.cs_next_id <= sb.cs_next_id
Proof
  simp[compile_store_memory_def] >>
  Cases_on `is_word_type ty` >> simp[]
  >- (strip_tac >> drule emit_void_extends >>
      simp[inst_extends_def, cs_extends_def] >>
      gvs[emit_void_def, comp_bind_def, comp_ignore_bind_def,
          comp_return_def, fresh_id_def, emit_def]) >>
  Cases_on `is_bytestring_type ty` >> simp[]
  >- (strip_tac >> drule buffer_store_bytestring_shape >>
      simp[inst_extends_def]) >>
  Cases_on `type_memory_bytes cenv ty` >>
  simp[compile_copy_memory_def, comp_return_def]
  >- (strip_tac >> gvs[inst_extends_def, same_blocks_def, emitted_insts_def]) >>
  strip_tac >> drule emit_void_extends >>
  simp[inst_extends_def, cs_extends_def] >>
      gvs[emit_void_def, comp_bind_def, comp_ignore_bind_def,
          comp_return_def, fresh_id_def, emit_def]
QED


Theorem log_data_field_aggregate_run[local]:
  emit_op ADD [buf; Lit (n2w off)] sa = (dst,sm) /\
  compile_store_memory cenv src dst ty ty sm = ((),sb) /\
  evaluate_type (get_tenv cx) ty = SOME tv /\
  value_has_type tv v /\ val_wf tv v /\ expr_val_rel cx ty v src s /\
  type_memory_bytes cenv ty = type_memory_size tv /\
  eval_operand buf s = SOME (n2w b) /\ b + off < dimword (:256) /\
  type_memory_bytes cenv ty < dimword (:256) /\
  (!x. src = Var x ==> not_fresh_at sa x) ==>
  ?q. run_inst_seq (emitted_insts sa sb) s = OK q /\
    val_in_memory tv v (b + off) q.vs_memory /\
    log_write_frame sa (b + off) (type_memory_bytes cenv ty) s q
Proof
  strip_tac >> drule_all log_data_address_value >> strip_tac >>
  drule log_data_address_shape >> strip_tac >>
  `!x. src = Var x \/ dst = Var x ==> not_fresh_at sm x` by
    (rpt strip_tac >- (irule freshWritesTheory.not_fresh_at_mono >>
       qexists_tac `sa` >> simp[]) >> simp[]) >>
  `type_memory_size tv < dimword (:256)` by metis_tac[] >>
  drule_all buffer_store_memory_encoding >> simp[] >> strip_tac >>
  drule emit_op_extends >> strip_tac >>
  drule log_data_store_aggregate_shape >> strip_tac >>
  `sb.cs_current_insts = sm.cs_current_insts ++ emitted_insts sm sb` by
    gvs[inst_extends_def] >>
  drule_all run_inst_seq_chain >> strip_tac >>
  `t.vs_memory = s.vs_memory` by
    (qpat_assum `t with vs_vars := _ = s`
      (mp_tac o AP_TERM ``\z. z.vs_memory``) >> simp[]) >>
  qexists_tac `q` >> simp[log_write_frame_def] >>
  conj_tac
  >- (qpat_assum `q with <|vs_memory := _; vs_vars := _|> = t`
      (mp_tac o AP_TERM ``\z. z with vs_vars := s.vs_vars``) >> simp[]) >>
  conj_tac
  >- (rpt strip_tac >>
      `not_fresh_at sm x` by
        (irule freshWritesTheory.not_fresh_at_mono >>
         qexists_tac `sa` >> simp[]) >> metis_tac[]) >>
  metis_tac[ADD_COMM]
QED

Theorem compile_log_store_data_aggregate_split[local]:
  compile_log_store_data cenv ((src,ty)::xs) (ty::MAP SND xs) buf off sa = ((),sb) ==>
  ?dst sm sn. emit_op ADD [buf; Lit (n2w off)] sa = (dst,sm) /\
    compile_store_memory cenv src dst ty ty sm = ((),sn) /\
    compile_log_store_data cenv xs (MAP SND xs) buf (off + type_memory_bytes cenv ty) sn = ((),sb) /\
    inst_extends sa sn /\ sa.cs_next_var <= sn.cs_next_var /\
    sa.cs_next_id <= sn.cs_next_id
Proof
  simp[Once compile_log_store_data_def,
       comp_bind_def, comp_ignore_bind_def] >>
  Cases_on `emit_op ADD [buf; Lit (n2w off)] sa` >> simp[] >>
  rename1 `emit_op ADD [buf; Lit (n2w off)] sa = (dst,sm)` >>
  Cases_on `compile_store_memory cenv src dst ty ty sm` >>
  rename1 `_ sm = (u,sn)` >> Cases_on `u` >> simp[] >> strip_tac >>
  drule emit_op_extends >> strip_tac >>
  drule log_data_address_shape >> strip_tac >>
  drule log_data_store_aggregate_shape >> strip_tac >>
  `inst_extends sa sm` by simp[inst_extends_def] >>
  `sa.cs_next_id <= sm.cs_next_id` by
    (qpat_x_assum `emit_op _ _ _ = _` mp_tac >>
     simp[emit_op_def, comp_bind_def, comp_ignore_bind_def, comp_return_def,
          fresh_var_def, fresh_id_def, emit_def] >> strip_tac >> gvs[]) >>
  conj_tac
  >- (irule inst_extends_trans >> qexists_tac `sm` >> simp[]) >> decide_tac
QED

Theorem compile_log_store_data_aggregate_shape:
  !xs buf off sa sb.
    compile_log_store_data cenv xs (MAP SND xs) buf off sa = ((),sb) ==>
    inst_extends sa sb /\ sa.cs_next_var <= sb.cs_next_var /\
    sa.cs_next_id <= sb.cs_next_id
Proof
  Induct_on `xs`
  >- simp[compile_log_store_data_def, comp_return_def, inst_extends_def,
          same_blocks_def, emitted_insts_def] >>
  gen_tac >> PairCases_on `h` >> simp[] >> rpt gen_tac >> strip_tac >>
  drule compile_log_store_data_aggregate_split >> strip_tac >>
  first_x_assum drule >> strip_tac >> conj_tac
  >- (irule inst_extends_trans >> qexists_tac `sn` >> simp[]) >> decide_tac
QED

Theorem log_data_aggregate_sources_kept[local]:
  !xs vs.
    LIST_REL (\(op,ty) v.
      (?tv. evaluate_type (get_tenv cx) ty = SOME tv /\
        value_has_type tv v /\ val_wf tv v /\
        type_memory_bytes cenv ty = type_memory_size tv) /\
      expr_val_rel cx ty v op s /\ log_source_apart cx b cap (op,ty) v s) xs vs /\
    EVERY (\(op,ty). !x. op = Var x ==> not_fresh_at st x) xs /\
    log_write_frame st b cap s t ==>
    LIST_REL (\(op,ty) v.
      (?tv. evaluate_type (get_tenv cx) ty = SOME tv /\
        value_has_type tv v /\ val_wf tv v /\
        type_memory_bytes cenv ty = type_memory_size tv) /\
      expr_val_rel cx ty v op t /\ log_source_apart cx b cap (op,ty) v t) xs vs
Proof
  Induct_on `xs` >- simp[] >>
  gen_tac >> PairCases_on `h` >> Cases_on `vs` >> simp[] >>
  rpt gen_tac >> strip_tac >>
  first_x_assum drule_all >> strip_tac >> simp[] >> conj_tac
  >- (drule_all log_source_value_kept >> simp[]) >>
  drule_all log_source_apart_kept >> simp[]
QED

Theorem log_data_layout_aggregate_cons[local]:
  evaluate_type (get_tenv cx) ty = SOME tv /\ val_wf tv v /\
  type_memory_bytes cenv ty = type_memory_size tv /\
  val_in_memory tv v p s.vs_memory /\
  log_data_layout cx tys vs (p + type_memory_bytes cenv ty) t.vs_memory /\
  log_write_frame st (p + type_memory_bytes cenv ty) n s t ==>
  log_data_layout cx (ty::tys) (v::vs) p t.vs_memory
Proof
  strip_tac >> gvs[log_data_layout_def] >>
  irule valueEncodingPropsTheory.val_in_memory_mem_agree >> simp[] >>
  qexistsl_tac [`type_memory_size tv`, `s.vs_memory`] >> simp[] >>
  gvs[log_write_frame_def] >> first_x_assum irule >> simp[]
QED

Theorem compile_log_store_data_aggregate_core[local]:
  !xs vs off sa sb s.
    compile_log_store_data cenv xs (MAP SND xs) buf off sa = ((),sb) /\
    LIST_REL (\(op,ty) v.
      (?tv. evaluate_type (get_tenv cx) ty = SOME tv /\
        value_has_type tv v /\ val_wf tv v /\
        type_memory_bytes cenv ty = type_memory_size tv) /\
      expr_val_rel cx ty v op s /\ log_source_apart cx b cap (op,ty) v s) xs vs /\
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
  rename1 `evaluate_type (get_tenv cx) ty = SOME tv` >>
  rename1 `expr_val_rel cx ty v src s` >>
  drule compile_log_store_data_aggregate_split >> strip_tac >>
  `b + off < dimword (:256) /\ type_memory_bytes cenv ty < dimword (:256)`
    by decide_tac >>
  drule_all log_data_field_aggregate_run >> strip_tac >>
  `log_write_frame sa b cap s q` by
    (irule log_write_frame_widen >> goal_assum (drule_at Any) >> decide_tac) >>
  drule_all log_data_aggregate_sources_kept >> strip_tac >>
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
  drule compile_log_store_data_aggregate_shape >> strip_tac >>
  `sn.cs_current_insts = sa.cs_current_insts ++ emitted_insts sa sn /\
   sb.cs_current_insts = sn.cs_current_insts ++ emitted_insts sn sb` by
    gvs[inst_extends_def] >>
  drule_all run_inst_seq_chain >> strip_tac >>
  qexists_tac `u` >> simp[] >> conj_tac
  >- (irule log_data_layout_aggregate_cons >> simp[] >>
      qexistsl_tac [`cenv`, `SUM (MAP (type_memory_bytes cenv) (MAP SND xs))`,
                   `q`, `sn`] >> simp[GSYM ADD_ASSOC]) >>
  CONV_TAC (RATOR_CONV (RATOR_CONV (RAND_CONV (REWR_CONV ADD_COMM)))) >>
  irule log_write_frame_join >>
  qexistsl_tac [`q`, `sn`] >> gvs[GSYM ADD_ASSOC]
QED

(* Actual types determine both the tuple stride and the captured source value.
   The whole destination window is disjoint from all nonword footprints. *)
Theorem compile_log_store_data_aggregate_run:
  compile_log_store_data cenv xs (MAP SND xs) buf off sa = ((),sb) /\
  LIST_REL (\(op,ty) v.
    (?tv. evaluate_type (get_tenv cx) ty = SOME tv /\
      value_has_type tv v /\ val_wf tv v /\
      type_memory_bytes cenv ty = type_memory_size tv) /\
    expr_val_rel cx ty v op s /\ log_source_apart cx b cap (op,ty) v s) xs vs /\
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
    LIST_REL (\(op,ty) v.
      (?tv. evaluate_type (get_tenv cx) ty = SOME tv /\
        value_has_type tv v /\ val_wf tv v /\
        type_memory_bytes cenv ty = type_memory_size tv) /\
      expr_val_rel cx ty v op t /\ log_source_apart cx b cap (op,ty) v t) xs vs /\
    eval_operand buf t = SOME (n2w b) /\
    (!op ty. MEM (op,ty) xs ==> eval_operand op t = eval_operand op s)
Proof
  strip_tac >> drule_all compile_log_store_data_aggregate_core >> strip_tac >>
  drule compile_log_store_data_aggregate_shape >> strip_tac >> simp[] >>
  `log_write_frame sa b cap s t` by
    (irule log_write_frame_widen >> goal_assum (drule_at Any) >> decide_tac) >>
  drule_all log_data_aggregate_sources_kept >> strip_tac >> simp[] >> conj_tac
  >- (drule_all log_write_frame_operand >> simp[]) >>
  rpt strip_tac >> irule log_write_frame_operand >>
  goal_assum (drule_at Any) >>
  qpat_x_assum `EVERY (\(op,ty). !x. op = Var x ==> _) xs` mp_tac >>
  simp[EVERY_MEM] >> disch_then drule >> simp[]
QED

(* A different-layout aggregate cannot use the empty-footprint alternative. *)
Theorem log_declared_source_separated[local]:
  type_widens_to (get_tenv cx) lty dty /\
  evaluate_type (get_tenv cx) lty = SOME ltv /\
  evaluate_type (get_tenv cx) dty = SOME dtv /\ lty <> dty /\
  ~is_word_type lty /\ ~is_bytestring_type lty /\
  eval_operand op s = SOME w /\
  log_source_apart cx b n (op,lty) v s ==>
  w2n w + type_memory_size ltv <= b \/ b+n <= w2n w
Proof
  strip_tac >>
  `type_memory_size ltv <> 0` by
    metis_tac[type_widens_to_zero_layout] >>
  `val_footprint ltv v = type_memory_size ltv` by
    (irule nonbytes_evaluated_val_footprint >> metis_tac[]) >>
  gvs[log_source_apart_def] >> metis_tac[]
QED

Theorem log_declared_relayout_run[local]:
  ~is_word_type dty /\ ~is_bytestring_type dty /\
  ~is_word_type lty /\ ~is_bytestring_type lty /\ dty <> lty /\
  compile_store_memory cenv src dst dty lty sa = ((),sb) /\
  acyclic_struct_metadata cenv.ce_struct_fields /\
  sfields_tenv_consistent cenv.ce_struct_fields (get_tenv cx) /\
  (!name fields. FLOOKUP cenv.ce_struct_fields name = SOME fields ==>
    ALL_DISTINCT (MAP FST fields) /\
    EVERY (\(fname,fty,sz). !tv.
      evaluate_type (get_tenv cx) fty = SOME tv ==>
      sz = type_memory_size tv) fields) /\
  type_widens_to (get_tenv cx) lty dty /\
  evaluate_type (get_tenv cx) lty = SOME ltv /\
  evaluate_type (get_tenv cx) dty = SOME dtv /\
  value_has_type ltv v /\ value_has_type dtv v /\
  val_wf ltv v /\ val_wf dtv v /\
  (!x. src = Var x ==> not_fresh_at sa x) /\
  (!x. dst = Var x ==> not_fresh_at sa x) /\
  eval_operand src s = SOME sw /\ eval_operand dst s = SOME dw /\
  expr_val_rel cx lty v src s /\
  log_source_apart cx (w2n dw) (type_memory_size dtv) (src,lty) v s /\
  w2n sw + type_memory_size ltv < dimword (:256) /\
  w2n dw + type_memory_size dtv < dimword (:256) /\
  fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?t. val_in_memory dtv v (w2n dw) t.vs_memory /\
    typed_copy_effect ctx func sa sb s t (w2n dw) (type_memory_size dtv)
Proof
  strip_tac >>
  `w2n sw + type_memory_size ltv <= w2n dw \/
   w2n dw + type_memory_size dtv <= w2n sw` by
    (irule log_declared_source_separated >> goal_assum (drule_at Any) >>
     simp[] >> metis_tac[]) >>
  `val_in_memory ltv v (w2n sw) s.vs_memory` by
    gvs[expr_val_rel_def] >>
  irule compile_store_memory_relayout_effect >> simp[] >>
  qpat_assum `compile_store_memory _ _ _ _ _ _ = _` (irule_at Any) >>
  simp[] >> qexistsl_tac [`get_tenv cx`, `ltv`] >> simp[ADD_COMM] >>
  first_assum ACCEPT_TAC
QED

Theorem log_declared_effect_operand[local]:
  typed_copy_effect ctx func sa sb s t b n /\
  (!x. op = Var x ==> not_fresh_at sa x) /\
  (!lab. op <> Label lab) ==>
  eval_operand op t = eval_operand op s
Proof
  strip_tac >> Cases_on `op` >> gvs[eval_operand_def] >>
  metis_tac[typed_copy_effect_lookup]
QED

Theorem log_declared_effect_source[local]:
  typed_copy_effect ctx func sa sb s t b n /\
  (!x. op = Var x ==> not_fresh_at sa x) /\
  (!lab. op <> Label lab) /\
  log_source_apart cx b n (op,lty) v s /\
  evaluate_type (get_tenv cx) lty = SOME tv /\ val_wf tv v /\
  expr_val_rel cx lty v op s ==>
  expr_val_rel cx lty v op t /\ log_source_apart cx b n (op,lty) v t
Proof
  strip_tac >>
  `eval_operand op t = eval_operand op s` by
    metis_tac[log_declared_effect_operand] >>
  reverse conj_tac >- gvs[log_source_apart_def] >>
  Cases_on `is_word_type lty`
  >- gvs[expr_val_rel_def] >>
  `?w. eval_operand op s = SOME w` by gvs[expr_val_rel_def] >>
  irule expr_val_rel_footprint_agree >> simp[] >>
  qexists_tac `s` >> simp[] >>
  `val_footprint tv v = 0 \/ w2n w + val_footprint tv v <= b \/
    b + n <= w2n w` by gvs[log_source_apart_def] >>
  Cases_on `val_footprint tv v = 0` >- simp[mem_bytes_at_def] >>
  metis_tac[typed_copy_effect_bytes]
QED

Theorem log_declared_address_effect[local]:
  emit_op ADD [buf; Lit (n2w off)] sa = (dst,sb) /\
  eval_operand buf s = SOME (n2w b) /\ fn_has_code sa sb func /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?t. eval_operand dst t = SOME (n2w (b+off)) /\
    typed_copy_effect ctx func sa sb s t d n
Proof
  strip_tac >> drule_all log_data_address_run >> strip_tac >>
  rename1 `run_inst_seq _ s = OK u` >>
  `sb.cs_current_bb = sa.cs_current_bb /\
   sb.cs_current_insts = sa.cs_current_insts ++ emitted_insts sa sb /\
   EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
     (emitted_insts sa sb) /\
   EVERY (\i. i.inst_opcode <> GAS) (emitted_insts sa sb)` by
    (qpat_x_assum `emit_op _ _ _ = _` mp_tac >>
     simp[emit_op_def, comp_bind_def, comp_ignore_bind_def, comp_return_def,
          fresh_id_def, fresh_var_def, emit_def] >> strip_tac >>
     gvs[emitted_insts_def, DROP_APPEND, mk_inst_def, is_terminator_def]) >>
  `gas_marked_path F ctx func s 0
    (OK (u with vs_inst_idx := LENGTH sb.cs_current_insts))` by
    (irule straight_line_zero_gas_path >> simp[] >>
     qexistsl_tac [`emitted_insts sa sb`, `sa`] >> simp[]) >>
  qexists_tac `u with vs_inst_idx := LENGTH sb.cs_current_insts` >>
  gvs[typed_copy_effect_def, eval_operand_def, lookup_var_def] >>
  gvs[venom_state_component_equality]
QED

Theorem log_declared_same_type_opcodes[local]:
  compile_store_memory cenv src dst ty ty sa = ((),sb) ==>
  EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
    (emitted_insts sa sb)
Proof
  simp[compile_store_memory_def] >>
  Cases_on `is_word_type ty`
  >- (simp[emit_void_def, comp_bind_def, comp_return_def, fresh_id_def,
           emit_def] >> strip_tac >> gvs[emitted_insts_def, DROP_APPEND,
                                      mk_inst_def, is_terminator_def]) >>
  Cases_on `is_bytestring_type ty`
  >- (simp[compile_store_bytestring_def, compile_bytestring_copy_len_def,
           emit_op_def, emit_void_def, comp_bind_def, comp_ignore_bind_def,
           comp_return_def, fresh_id_def, fresh_var_def, emit_def] >>
      strip_tac >> gvs[emitted_insts_def] >>
      pure_rewrite_tac[GSYM APPEND_ASSOC] >>
      simp[DROP_APPEND, mk_inst_def, is_terminator_def]) >>
  Cases_on `type_memory_bytes cenv ty` >>
  simp[compile_copy_memory_def, emit_void_def, comp_bind_def, comp_return_def,
       fresh_id_def, emit_def] >>
  strip_tac >> gvs[emitted_insts_def, DROP_APPEND, mk_inst_def, is_terminator_def]
QED

Theorem log_declared_same_type_effect[local]:
  compile_store_memory cenv src dst ty ty sa = ((),sb) /\
  evaluate_type (get_tenv cx) ty = SOME tv /\
  value_has_type tv v /\ val_wf tv v /\ expr_val_rel cx ty v src s /\
  type_memory_bytes cenv ty = type_memory_size tv /\
  type_memory_size tv < dimword (:256) /\ eval_operand dst s = SOME dw /\
  (!x. src = Var x \/ dst = Var x ==> not_fresh_at sa x) /\
  fn_has_code sa sb func /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?t. val_in_memory tv v (w2n dw) t.vs_memory /\
    typed_copy_effect ctx func sa sb s t (w2n dw) (type_memory_size tv)
Proof
  strip_tac >> drule_all buffer_store_memory_encoding >> strip_tac >>
  drule_all buffer_store_memory_capacity >> strip_tac >>
  drule buffer_store_memory_shape >> strip_tac >>
  drule log_declared_same_type_opcodes >> strip_tac >>
  drule compile_store_memory_same_type_no_gas >> strip_tac >>
  `sb.cs_current_bb = sa.cs_current_bb` by gvs[same_blocks_def] >>
  `gas_marked_path F ctx func s 0
    (OK (q with vs_inst_idx := LENGTH sb.cs_current_insts))` by
    (irule straight_line_zero_gas_path >> simp[] >>
     qexistsl_tac [`emitted_insts sa sb`, `sa`] >> simp[]) >>
  qexists_tac `q with vs_inst_idx := LENGTH sb.cs_current_insts` >>
  gvs[typed_copy_effect_def, venom_state_component_equality, lookup_var_def] >>
  metis_tac[lookup_var_def]
QED
