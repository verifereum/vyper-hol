(* Compiler stage boundaries for successful event metadata lookup. *)
Theory stmtSimLogTrace
Ancestors
  stmtLowering stmtSimLogArgs stmtSimLogTopics context compileEnv emitHelper
  emitHelperProps exprLoweringProps list words abiBuiltinAllocation fragExec
  venomInst venomExecSemantics
  eventLoweringStructure

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
