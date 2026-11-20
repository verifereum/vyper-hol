(* The write cut of compile_extcall_store_values, after ADD and unwrap. *)
Theory bodyFullExtCallSlotWrite
Ancestors
  bodyFullExtCallDefaultBytesStore calldataOverwritePtr bodyPtrMakeArrayCopyStep
  assignTuplePtrStoreWord reasonTupleCopyPtr allocaFootprint stmtReasonMemory
  exprSimAbiEncodeMemoryLength logStoreDataOriginPtr typedMemoryCopy
  emitHelperProps exprLoweringProps fragExec venomInst fragGasSeqPtr
  venomState fragExecPtr bodyPtrDefs ptrDiscipline exprSimBufferStore
  words placeMemoryTypedPrimitive venomExecSemantics pred_set ptrSafetyTransport

Theorem slot_void_origin_path[local]:
  emit_void opc ops sa = ((),sb) /\ fn_has_code sa sb fn /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  opc <> INVOKE /\ ~is_terminator opc /\ opc <> GAS /\
  run_inst_seq_mem_ok (emitted_insts sa sb) s /\
  inst_seq_ptr D lo ctx fn PG G tn (emitted_insts sa sb) s Gf tf /\
  step_inst_base (mk_inst sa.cs_next_id opc ops []) s = OK q ==>
  gas_origin_ptr_path (D,lo,explicit,ctx,fn,PG) (s,G,tn) []
    (OK (q with vs_inst_idx := LENGTH sb.cs_current_insts),Gf,tf)
Proof
  strip_tac >> drule emitted_insts_emit_void >> strip_tac >>
  drule emit_void_same_blocks >> strip_tac >>
  `?bb. lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
    isPREFIX (emitted_insts sa sb) (DROP s.vs_inst_idx bb.bb_instructions)` by
    (gvs[fn_has_code_def, same_blocks_def, rich_listTheory.IS_PREFIX_APPEND] >>
     simp[listTheory.DROP_APPEND]) >>
  `run_inst_seq (emitted_insts sa sb) s = OK q` by simp[run_inst_seq_def] >>
  `EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
     (emitted_insts sa sb)` by simp[mk_inst_def] >>
  drule_all run_inst_seq_gas_origin_ptr_path >> simp[mk_inst_def]
QED

(* Zero width still consumes the emitted MCOPY instruction. *)
Theorem slot_flat_copy[local]:
  emit_void MCOPY [Var dst;src;Lit (n2w n)] sa = ((),sb) /\
  fn_has_code sa sb fn /\ (ctx_has_dalloca ctx ==> allocas_below_fmp s) /\ ~s.vs_halted /\
  allocas_from lo s /\ s.vs_current_bb = sa.cs_current_bb /\ s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  eval_operand src s = SOME a /\ lookup_var dst s = SOME b /\
  n < dimword (:256) /\
  (if n = 0 then op_taint tn src = {} /\ op_taint tn (Var dst) = {}
   else (?x. src = Var x /\ ptr_covers G tn x s n) /\ ptr_covers G tn dst s n /\
        w2n a + n <= s.vs_alloca_next /\ w2n b + n <= s.vs_alloca_next) /\
  val_wf tv v /\ val_footprint tv v <= n /\
  (!m. mem_agree_outside tn.t_mem s.vs_memory m ==> val_in_memory tv v (w2n a) m) ==>
  ?q Gf tf.
    (!D. gas_origin_ptr_path (D,lo,explicit,ctx,fn,PG) (s,G,tn) [] (OK q,Gf,tf)) /\
    (!m. mem_agree_outside tf.t_mem q.vs_memory m ==> val_in_memory tv v (w2n b) m) /\
    typed_copy_state_frame sa (w2n b) n s q /\
    (!x. not_fresh_at sa x ==> FLOOKUP Gf x = FLOOKUP G x /\
      op_taint tf (Var x) = op_taint tn (Var x)) /\
    (!i. i < w2n b \/ w2n b+n <= i ==> (i IN tf.t_mem <=> i IN tn.t_mem)) /\
    tf.t_stor = tn.t_stor /\ tf.t_trans = tn.t_trans /\ tf.t_imm = tn.t_imm /\
    q.vs_current_bb = sb.cs_current_bb /\ q.vs_current_bb = s.vs_current_bb /\
    q.vs_inst_idx = LENGTH sb.cs_current_insts /\ ~q.vs_halted
Proof
  strip_tac >> drule emitted_insts_emit_void >> strip_tac >>
  drule emit_void_same_blocks >> strip_tac >>
  `eval_operand (Var dst) s = SOME b /\
   eval_operand (Lit (n2w n)) s = SOME (n2w n)` by simp[eval_operand_def] >>
  `w2n (n2w n : bytes32) = n` by simp[w2n_n2w] >>
  qabbrev_tac `i = mk_inst sa.cs_next_id MCOPY [Var dst;src;Lit (n2w n)] []` >>
  qabbrev_tac `r = mcopy (w2n b) (w2n a) n s` >>
  qabbrev_tac `tf = step_taint i s r tn` >>
  `step_inst_base i s = OK r` by simp[Abbr `i`, Abbr `r`, step_mcopy_eq] >>
  `step_prov PG G i r = G /\ tf.t_var = tn.t_var /\
   tf.t_stor = tn.t_stor /\ tf.t_trans = tn.t_trans /\
   tf.t_mem = (tn.t_mem DIFF {j | w2n b <= j /\ j < w2n b+n}) UNION
      {w2n b+j | j < n /\ w2n a+j IN tn.t_mem}` by
    (mp_tac (Q.SPECL [`PG`,`G`,`tn`,`s`,`sa.cs_next_id`,`Var dst`,`src`,
         `Lit (n2w n)`,`a`,`b`,`n2w n`] mcopy_operand_ghost_frame) >>
     simp[Abbr `i`, Abbr `r`, Abbr `tf`]) >>
  `tf.t_imm = tn.t_imm` by simp[Abbr `tf`, Abbr `i`, step_taint_def, imm_taint_def, mk_inst_def] >>
  `!D. inst_seq_ptr D lo ctx fn PG G tn (emitted_insts sa sb) s G tf` by
    (gen_tac >> simp[inst_seq_ptr_def, Abbr `tf`] >>
     irule ptr_inst_ok_lower_bound_transport >> simp[] >>
     qexists_tac `0` >> simp[Abbr `i`] >> Cases_on `n = 0`
     >- (gvs[] >> irule ptr_inst_ok_mcopy_zero >> metis_tac[]) >>
     gvs[] >> irule ptr_inst_ok_mcopy_operand >> simp[op_taint_def]) >>
  `run_inst_seq_mem_ok (emitted_insts sa sb) s` by
    (irule emit_mcopy_mem_ok >>
     qexistsl_tac [`a`,`b`,`Var dst`,`Lit (n2w n)`,`n2w n`,`src`] >>
     Cases_on `n = 0` >> gvs[]) >>
  qexistsl_tac [`r with vs_inst_idx := LENGTH sb.cs_current_insts`,`G`,`tf`] >>
  conj_tac
  >- (gen_tac >> irule slot_void_origin_path >> simp[mk_inst_def, is_terminator_def] >>
      goal_assum (drule_at (Pat `emit_void _ _ _ = _`)) >>
      gs[Abbr `i`, is_terminator_def, mk_inst_def]) >>
  conj_tac
  >- (mp_tac (Q.SPECL [`tn`,`s`,`sa.cs_next_id`,`Var dst`,`src`,
         `Lit (n2w n)`,`a`,`b`,`n2w n`,`tv`,`v`] reason_mcopy_robust_representation) >>
      simp[Abbr `tf`, Abbr `i`, Abbr `r`]) >>
  conj_tac
  >- (simp[typed_copy_state_frame_def, Abbr `r`] >> conj_tac
      >- simp[mcopy_def, write_memory_with_expansion_def, venom_state_component_equality] >>
      conj_tac >- simp[mcopy_def, write_memory_with_expansion_def, lookup_var_def] >>
      simp[typed_copy_frame_def, mcopy_memory_length] >> rpt strip_tac >>
      irule buffer_mcopy_exterior >> decide_tac) >>
  `sb.cs_current_bb = sa.cs_current_bb` by fs[same_blocks_def] >>
  simp[Abbr `r`, mcopy_def, write_memory_with_expansion_def, op_taint_def] >>
  rw[] >> eq_tac >> rw[] >> gvs[] >> decide_tac
QED

Theorem slot_word_store[local]:
  emit_void MSTORE [Var dst;op] sa = ((),sb) /\ fn_has_code sa sb fn /\
  (ctx_has_dalloca ctx ==> allocas_below_fmp s) /\ ~s.vs_halted /\ allocas_from lo s /\
  s.vs_current_bb = sa.cs_current_bb /\ s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  lookup_var dst s = SOME b /\ ptr_covers G tn dst s 32 /\
  w2n b + 32 <= s.vs_alloca_next /\
  eval_operand op s = SOME (typed_val_to_w256 tv v) /\ op_taint tn op = {} /\
  is_word_type ty /\ evaluate_type tenv ty = SOME tv /\ value_has_type tv v ==>
  ?q Gf tf.
    (!D. gas_origin_ptr_path (D,lo,explicit,ctx,fn,PG) (s,G,tn) [] (OK q,Gf,tf)) /\
    (!m. mem_agree_outside tf.t_mem q.vs_memory m ==> val_in_memory tv v (w2n b) m) /\
    typed_copy_state_frame sa (w2n b) 32 s q /\
    (!x. not_fresh_at sa x ==> FLOOKUP Gf x = FLOOKUP G x /\
      op_taint tf (Var x) = op_taint tn (Var x)) /\
    (!i. i < w2n b \/ w2n b+32 <= i ==> (i IN tf.t_mem <=> i IN tn.t_mem)) /\
    tf.t_stor = tn.t_stor /\ tf.t_trans = tn.t_trans /\ tf.t_imm = tn.t_imm /\
    q.vs_current_bb = sb.cs_current_bb /\ q.vs_current_bb = s.vs_current_bb /\
    q.vs_inst_idx = LENGTH sb.cs_current_insts /\ ~q.vs_halted
Proof
  strip_tac >> drule emitted_insts_emit_void >> strip_tac >>
  drule emit_void_same_blocks >> strip_tac >>
  `sb.cs_current_bb = sa.cs_current_bb` by fs[same_blocks_def] >>
  `eval_operand (Var dst) s = SOME b` by simp[eval_operand_def] >>
  qabbrev_tac `i = mk_inst sa.cs_next_id MSTORE [Var dst;op] []` >>
  qabbrev_tac `r = mstore (w2n b) (typed_val_to_w256 tv v) s` >>
  qabbrev_tac `tf = step_taint i s r tn` >>
  `step_inst_base i s = OK r` by simp[Abbr `i`, Abbr `r`, step_mstore_eq] >>
  `step_prov PG G i r = G /\ tf.t_var = tn.t_var /\
   tf.t_stor = tn.t_stor /\ tf.t_trans = tn.t_trans /\ tf.t_imm = tn.t_imm /\
   tf.t_mem = tn.t_mem DIFF {j | w2n b <= j /\ j < w2n b+32}` by
    (mp_tac (Q.INST [`value` |-> `op`, `id` |-> `sa.cs_next_id`,
       `a` |-> `b`, `w` |-> `typed_val_to_w256 tv v`] mstore_raw_ghost_frame) >>
     simp[Abbr `tf`, Abbr `i`, Abbr `r`]) >>
  `!D. inst_seq_ptr D lo ctx fn PG G tn (emitted_insts sa sb) s G tf` by
    (gen_tac >> simp[inst_seq_ptr_def, Abbr `tf`] >>
     irule ptr_inst_ok_lower_bound_transport >> simp[] >> qexists_tac `0` >>
     simp[Abbr `i`, ptr_inst_ok_mstore]) >>
  `run_inst_seq_mem_ok (emitted_insts sa sb) s` by metis_tac[emit_mstore_mem_ok] >>
  qexistsl_tac [`r with vs_inst_idx := LENGTH sb.cs_current_insts`,`G`,`tf`] >>
  conj_tac
  >- (gen_tac >> irule slot_void_origin_path >> simp[] >>
      goal_assum (drule_at (Pat `emit_void _ _ _ = _`)) >>
      gs[Abbr `i`, is_terminator_def, mk_inst_def]) >>
  conj_tac
  >- (rpt strip_tac >> fs[Abbr `r`] >>
      irule typed_word_store_robust_ptr >> metis_tac[]) >>
  conj_tac
  >- (simp[typed_copy_state_frame_def, Abbr `r`] >> conj_tac
      >- simp[mstore_def, write_memory_with_expansion_def, venom_state_component_equality] >>
      conj_tac >- simp[mstore_def, lookup_var_def] >>
      simp[typed_copy_frame_def, abi_encode_mstore_memory_length] >> rpt strip_tac >>
      irule mem_agree_outside_window >>
      qexists_tac `{j | w2n b <= j /\ j < w2n b+32}` >>
      simp[wordLoadStorePtrTheory.mstore_memory_frame] >> decide_tac) >>
  simp[Abbr `r`, mstore_def, op_taint_def] >> rw[] >> decide_tac
QED

(* The exact delayed write, excluding destination ADD, unwrap and recursion.
   The frame covers the entire typed slot even when the bytestring write
   only uses its rounded runtime extent. No source coverage is needed for
   the emitted zero-width MCOPY. *)
Theorem extcall_tuple_slot_write:
  (if is_word_type ty then emit_void MSTORE [Var dst;src]
   else if is_bytestring_type ty then compile_store_bytestring src (Var dst)
   else emit_void MCOPY [Var dst;src;Lit (n2w (type_memory_bytes ce ty))])
    sa = ((),sb) /\
  evaluate_type (get_tenv cx) ty = SOME tv /\ value_has_type tv v /\
  type_memory_bytes ce ty = type_memory_size tv /\
  fn_has_code sa sb fn /\ (ctx_has_dalloca ctx ==> allocas_below_fmp s) /\ ~s.vs_halted /\
  allocas_from lo s /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\ lookup_var dst s = SOME b /\
  (if is_word_type ty then
     eval_operand src s = SOME (typed_val_to_w256 tv v) /\ op_taint tn src = {} /\
     ptr_covers G tn dst s 32 /\ w2n b + 32 <= s.vs_alloca_next
   else
     val_wf tv v /\ type_memory_size tv < dimword (:256) /\
     (?a. eval_operand src s = SOME a /\
       (!m. mem_agree_outside tn.t_mem s.vs_memory m ==>
            val_in_memory tv v (w2n a) m) /\
       (if type_memory_size tv = 0 then
          op_taint tn src = {} /\ op_taint tn (Var dst) = {}
        else
          (?x. src = Var x /\ ptr_covers G tn x s (type_memory_size tv)) /\
          ptr_covers G tn dst s (type_memory_size tv) /\
          w2n a + type_memory_size tv <= s.vs_alloca_next /\
          w2n b + type_memory_size tv <= s.vs_alloca_next) /\
       (is_bytestring_type ty ==>
          type_memory_size tv + 64 < dimword (:256) /\
          type_memory_size tv <> 0 /\ lo <= s.vs_alloca_next /\
          not_fresh_at sa dst /\ (!x. src = Var x ==> not_fresh_at sa x)))) ==>
  ?q Gf tf.
    (!D. gas_origin_ptr_path (D,lo,explicit,ctx,fn,PG) (s,G,tn) [] (OK q,Gf,tf)) /\
    (!m. mem_agree_outside tf.t_mem q.vs_memory m ==> val_in_memory tv v (w2n b) m) /\
    typed_copy_state_frame sa (w2n b) (type_memory_size tv) s q /\
    (!x. not_fresh_at sa x ==> FLOOKUP Gf x = FLOOKUP G x /\
      op_taint tf (Var x) = op_taint tn (Var x)) /\
    (!i. i < w2n b \/ w2n b+type_memory_size tv <= i ==>
         (i IN tf.t_mem <=> i IN tn.t_mem)) /\
    tf.t_stor = tn.t_stor /\ tf.t_trans = tn.t_trans /\ tf.t_imm = tn.t_imm /\
    q.vs_current_bb = sb.cs_current_bb /\ q.vs_current_bb = s.vs_current_bb /\
    q.vs_inst_idx = LENGTH sb.cs_current_insts /\ ~q.vs_halted
Proof
  strip_tac >> Cases_on `is_word_type ty`
  >- (fs[] >>
      `type_memory_size tv = 32` by metis_tac[exprSimPropsTheory.word_tv_memory_size] >>
      drule_all slot_word_store >>
      disch_then (qspecl_then [`explicit`,`PG`] strip_assume_tac) >>
      qexistsl [`q`,`Gf`,`tf`] >> gs[arithmeticTheory.ADD_COMM] >> metis_tac[]) >>
  fs[] >> Cases_on `is_bytestring_type ty`
  >- (gvs[] >>
      `compile_store_memory ce (Var x) (Var dst) ty ty sa = ((),sb)` by
        simp[contextTheory.compile_store_memory_def] >>
      `lookup_var x s = SOME a` by fs[eval_operand_def] >>
      `w2n a + type_memory_size tv <= s.vs_alloca_next /\
       w2n b + type_memory_size tv <= s.vs_alloca_next` by decide_tac >>
      drule_all (Q.INST [`rt` |-> `ty`, `sty` |-> `ty`, `stv` |-> `tv`,
        `sw` |-> `a`, `dw` |-> `b`] extcall_default_bytes_store_capacity_joint) >>
      disch_then (qspecl_then [`explicit`,`PG`] strip_assume_tac) >>
      rename1 `u with <|vs_vars := s.vs_vars; vs_memory := s.vs_memory;
                       vs_inst_idx := s.vs_inst_idx|> = s` >>
      `u.vs_current_bb = s.vs_current_bb /\ u.vs_prev_bb = s.vs_prev_bb` by
        (qpat_assum `u with <|vs_vars := _; vs_memory := _; vs_inst_idx := _|> = s` mp_tac >> simp[venom_state_component_equality]) >>
      `typed_copy_state_frame sa (w2n b) (type_memory_size tv) s u` by
        (simp[typed_copy_state_frame_def, typed_copy_frame_def] >> conj_tac
         >- (qpat_assum `u with <|vs_vars := _; vs_memory := _; vs_inst_idx := _|> = s`
               mp_tac >> simp[venom_state_component_equality]) >>
         metis_tac[arithmeticTheory.ADD_COMM]) >>
      qexistsl [`u`,`Gf`,`tm`] >> gs[arithmeticTheory.ADD_COMM] >> metis_tac[]) >>
  fs[] >>
  `val_footprint tv v <= type_memory_size tv` by metis_tac[exprSimPropsTheory.val_footprint_le] >>
  `(if type_memory_size tv = 0 then op_taint tn src = {} /\ op_taint tn (Var dst) = {}
    else (?x. src = Var x /\ ptr_covers G tn x s (type_memory_size tv)) /\
         ptr_covers G tn dst s (type_memory_size tv) /\
         w2n a + type_memory_size tv <= s.vs_alloca_next /\
         w2n b + type_memory_size tv <= s.vs_alloca_next)` by
    (qpat_assum `if type_memory_size tv = 0 then _ else _` mp_tac >>
     simp[arithmeticTheory.ADD_COMM]) >>
  drule_all slot_flat_copy >>
  disch_then (qspecl_then [`explicit`,`PG`] strip_assume_tac) >>
  qexistsl [`q`,`Gf`,`tf`] >> gs[arithmeticTheory.ADD_COMM] >> metis_tac[]
QED
