(* Compiler stage boundaries for successful event metadata lookup. *)
Theory stmtSimLogTrace
Ancestors
  stmtLowering stmtSimLogArgs stmtSimLogTopics context compileEnv emitHelper
  emitHelperProps exprLoweringProps list words abiBuiltinAllocation fragExec
  venomInst venomExecSemantics

(* The evaluated arguments seen at their source types: the compiler's
   operands, at types that agree with the lowered ones on whether they are
   bytestrings, the one property of a type that topic hashing reads. *)
Definition log_eval_view_def:
  log_eval_view cenv args sa xs sm <=>
    ?ys. compile_log_eval_all cenv args sa = (ys,sm) /\
         LIST_REL (\y x. FST y = FST x /\
                         (is_bytestring_type (SND y) <=> is_bytestring_type (SND x)))
           ys xs
End

Theorem split_log_ops_view:
  !ys xs flags.
    LIST_REL (\y x. FST y = FST x /\
                    (is_bytestring_type (SND y) <=> is_bytestring_type (SND x))) ys xs ==>
    FST (split_log_ops ys flags) = FST (split_log_ops xs flags) /\
    MAP FST (SND (split_log_ops ys flags)) = MAP FST (SND (split_log_ops xs flags))
Proof
  Induct >- (Cases_on `flags` >> simp[split_log_ops_def]) >>
  rpt gen_tac >> Cases_on `xs` >> simp[] >> strip_tac >>
  rename1 `LIST_REL _ ys xs` >>
  Cases_on `flags` >- (PairCases_on `h` >> PairCases_on `h'` >> simp[split_log_ops_def]) >>
  rename1 `split_log_ops _ (flag::flags)` >>
  first_x_assum (drule_then (qspec_then `flags` strip_assume_tac)) >>
  PairCases_on `h` >> PairCases_on `h'` >>
  Cases_on `split_log_ops ys flags` >> Cases_on `split_log_ops xs flags` >>
  Cases_on `flag` >> gvs[split_log_ops_def]
QED

(* A word or bytestring field is stored whatever its source layout type. *)
Theorem compile_log_store_data_view:
  !ys xs tys buf off.
    MAP FST ys = MAP FST xs /\
    EVERY (\t. is_word_type t \/ is_bytestring_type t) tys ==>
    compile_log_store_data cenv ys tys buf off =
    compile_log_store_data cenv xs tys buf off
Proof
  Induct >- (Cases_on `xs` >> simp[]) >>
  rpt gen_tac >> Cases_on `xs` >> simp[] >> strip_tac >>
  Cases_on `tys` >> simp[compile_log_store_data_def] >> gvs[] >>
  rename1 `compile_store_memory _ _ _ ty _` >>
  `!v d. compile_store_memory cenv v d ty (SND h) =
         compile_store_memory cenv v d ty (SND h')` by
    (rw[compile_store_memory_def] >> gvs[]) >>
  first_x_assum (qspecl_then [`t`, `t'`] mp_tac) >> simp[]
QED

Theorem compile_log_empty_trace:
  cenv.ce_event_info (nsid_to_string id) = SOME (h,tys,flags) /\
  log_eval_view cenv args sa xs sm /\
  compile_log_topic_ops (FST (split_log_ops xs flags)) sm = (topics,st) /\
  SND (split_log_ops xs flags) = [] ==>
  (compile_stmt cenv lctx ty (Log id args) sa = ((),sb) <=>
   emit_inst LOG
     (Lit (n2w (LENGTH (Lit (n2w h)::topics))) ::
       REVERSE (Lit (n2w h)::topics) ++ [Lit 0w; Lit 0w]) [] st = ((),sb))
Proof
  strip_tac >> gvs[log_eval_view_def] >>
  drule split_log_ops_view >> disch_then (qspec_then `flags` strip_assume_tac) >>
  gvs[] >> simp[Once compile_stmt_def, comp_bind_def, comp_return_def]
QED

Theorem compile_log_data_trace:
  cenv.ce_event_info (nsid_to_string id) = SOME (h,MAP SND xs,flags) /\
  log_eval_view cenv args sa xs sm /\
  EVERY (supported_scalar_type o SND) xs /\ LENGTH flags = LENGTH xs /\
  compile_log_topic_ops (FST (split_log_ops xs flags)) sm = (topics,st) /\
  SND (split_log_ops xs flags) = data_ops /\ data_ops <> [] ==>
  (compile_stmt cenv lctx ty (Log id args) sa = ((),sb) <=>
   ?src s1 s2 dst s3 len s4.
     compile_alloc_buffer
       (MAX 32 (SUM (MAP (type_memory_bytes cenv) (MAP SND data_ops)))) st = (src,s1) /\
     compile_log_store_data cenv data_ops (MAP SND data_ops) src.buf_operand 0 s1 = ((),s2) /\
     compile_alloc_buffer
       (MAX 32 (abi_size_bound cenv.ce_struct_fields (TupleT (MAP SND data_ops))))
       s2 = (dst,s3) /\
     compile_abi_encode_to_buf dst.buf_operand src.buf_operand
       (type_to_abi_enc_info cenv.ce_struct_fields cenv (TupleT (MAP SND data_ops)))
       s3 = (len,s4) /\
     emit_inst LOG
       (Lit (n2w (LENGTH (Lit (n2w h)::topics))) ::
         REVERSE (Lit (n2w h)::topics) ++ [len;dst.buf_operand]) [] s4 = ((),sb))
Proof
  strip_tac >> gvs[log_eval_view_def] >>
  drule split_log_ops_view >> disch_then (qspec_then `flags` strip_assume_tac) >>
  `log_non_indexed_types flags (MAP SND xs) = MAP SND (SND (split_log_ops xs flags))` by
    simp[split_log_ops_data_types] >>
  `EVERY (\t. is_word_type t \/ is_bytestring_type t)
     (MAP SND (SND (split_log_ops xs flags)))` by
    (`EVERY (supported_scalar_type o SND) (SND (split_log_ops xs flags))` by
       (irule log_split_data_every >> simp[]) >>
     gvs[EVERY_MAP, EVERY_MEM] >> metis_tac[log_scalar_topic_shape]) >>
  `!buf off. compile_log_store_data cenv (SND (split_log_ops ys flags))
       (MAP SND (SND (split_log_ops xs flags))) buf off =
     compile_log_store_data cenv (SND (split_log_ops xs flags))
       (MAP SND (SND (split_log_ops xs flags))) buf off` by
    (rpt gen_tac >> irule compile_log_store_data_view >> simp[]) >>
  `SND (split_log_ops ys flags) <> []` by (strip_tac >> gvs[]) >>
  simp[Once compile_stmt_def, NULL_EQ, comp_bind_def, comp_return_def,
    comp_ignore_bind_def] >>
  rpt (pairarg_tac >> gvs[]) >> simp[]
QED

Theorem log_buffer_trace_code:
  compile_alloc_buffer cap sa = (buf,sb) /\ fn_has_code sa sb func ==>
  inst_extends sa sb /\ buf.buf_size = cap /\
  MEM (mk_inst sa.cs_next_id ALLOCA [Lit (n2w cap)]
    [STRING #"%" (toString sa.cs_next_var)]) (fn_insts func)
Proof
  strip_tac >> drule abi_builtin_alloc_buffer_shape >> strip_tac >>
  drule inst_extends_emit_op >> strip_tac >>
  drule emit_op_extends >> strip_tac >>
  drule emitted_insts_emit_op >> strip_tac >> simp[] >>
  `?bb. lookup_block sa.cs_current_bb func.fn_blocks = SOME bb /\
    get_instruction bb (LENGTH sa.cs_current_insts) =
      SOME (mk_inst sa.cs_next_id ALLOCA [Lit (n2w cap)]
        [STRING #"%" (toString sa.cs_next_var)])` by
    (`sb.cs_current_bb = sa.cs_current_bb` by gvs[inst_extends_def, same_blocks_def] >>
     drule_all fn_has_code_same_block >> simp[] >>
     disch_then (qx_choose_then `bb` strip_assume_tac) >>
     qexists_tac `bb` >> first_x_assum (qspec_then `0` mp_tac) >> simp[]) >>
  irule lookup_block_fn_insts >> goal_assum (drule_at Any) >>
  gvs[get_instruction_def] >> metis_tac[MEM_EL]
QED
