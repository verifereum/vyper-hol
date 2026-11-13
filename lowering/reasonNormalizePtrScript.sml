(* Allocation and copying are composed at the selected checked endpoint. *)
Theory reasonNormalizePtr
Ancestors
  literalAllocPathPtr storageCopyCompilePtr emittedSeqComposePtr reasonCopySourcePtr
  exprSimUnwrap immutableCopyWordsPtr immutableCopySeqPtr normalizerAllocationFrame
  entrySinkExtraction fragGasPathPtr
  exprSimCopy fragExec loweringHalt exprLowering exprLoweringProps
  emitHelper emitHelperProps context compileEnv loweringStateRelDefs localPtrsProps
  moduleLoweringProps venomInst venomState ptrDiscipline ptrSafeRun
  finite_map words arithmetic rich_list list

Theorem allocated_storage_copy_code:
  (loc = LocStorage \/ loc = LocTransient) /\
  compile_alloc_buffer cap sa = (buf,sc) /\
  compile_word_copy_loop src buf.buf_operand n loc LocMemory F sc = (u,sb) /\
  fn_has_code sa sb fn ==>
  fn_has_code sa sc fn /\ fn_has_code sc sb fn /\
  sa.cs_next_var <= sc.cs_next_var
Proof
  strip_tac >>
  `cs_extends sa sc` by metis_tac[compile_alloc_buffer_extends] >>
  `cs_extends sc sb` by
    (qpat_x_assum `compile_word_copy_loop _ _ _ _ _ _ _ = _` mp_tac >>
     Cases_on `loc = LocStorage` >> gvs[] >>
     simp[compile_word_copy_loop_def, compile_word_copy_loop_op_def,
       compile_word_copy_loop_base_def, word_scale_def, compile_ptr_load_def,
       compile_ptr_store_def, emit_op_def, emit_void_def, emit_inst_def,
       fresh_label_def, fresh_var_def, fresh_id_def, emit_def, new_block_def,
       comp_bind_def, comp_ignore_bind_def, comp_return_def] >>
     strip_tac >> gvs[] >> simp[cs_extends_def, IS_PREFIX_APPEND]) >>
  drule compile_alloc_buffer_emission >> strip_tac >>
  drule_all fn_has_code_split >> simp[]
QED

Theorem allocated_storage_copy_path_ptr:
  (loc = LocStorage \/ loc = LocTransient) /\
  compile_alloc_buffer (32*n) sa = (buf,sc) /\
  compile_word_copy_loop src buf.buf_operand n loc LocMemory F sc = (u,sb) /\
  fn_has_code sa sb fn /\ copy_old_operand sa src /\
  eval_operand src s = SOME a /\ op_taint tn src = {} /\
  n < dimword(:256) /\ 32*n < dimword(:256) /\
  ~s.vs_halted /\ ~ctx_has_dalloca ctx /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  alloca_inv s /\ alloca_room ctx fn s /\ fn_inst_ids_distinct fn /\
  (!i w p sz. MEM i (fn_insts fn) /\ i.inst_opcode = ALLOCA /\
    i.inst_operands = [Lit w] /\
    FLOOKUP s.vs_allocas i.inst_id = SOME (p,sz) ==> sz = w2n w) ==>
  ?root b sm Gm tm t Gf tf.
    buf.buf_operand = Var root /\
    gas_path_ptr D 0 ctx fn PG G tn s 0 Gf tf (OK t) /\
    gas_path_ptr D 0 ctx fn PG G tn s 0 Gm tm (OK sm) /\
    sm.vs_accounts = s.vs_accounts /\ sm.vs_transient = s.vs_transient /\
    sm.vs_data_section = s.vs_data_section /\ sm.vs_call_ctx = s.vs_call_ctx /\
    ~t.vs_halted /\ t.vs_current_bb = sb.cs_current_bb /\
    t.vs_inst_idx = LENGTH sb.cs_current_insts /\
    eval_operand buf.buf_operand t = SOME (n2w b) /\
    ptr_covers Gf tf root t (32*n) /\ b+32*n < dimword(:256) /\
    copy_prefix loc a b n sm n t /\
    eval_operand src t = SOME a /\ op_taint tf src = {} /\
    tf.t_stor = tn.t_stor /\ tf.t_trans = tn.t_trans /\ tf.t_imm = tn.t_imm /\
    (0 < n /\ key_taint (if loc = LocTransient then tn.t_trans else tn.t_stor) a = {} ==>
      mem_word_taint tf.t_mem b = {}) /\ 
    (!i h. i < n /\ h < 32 ==>
      (b+32*i+h IN tf.t_mem <=>
       (a+n2w i,h) IN (if loc = LocTransient then tf.t_trans else tf.t_stor))) /\
    (!i. i < b \/ b+32*n <= i ==> (i IN tf.t_mem <=> i IN tm.t_mem)) /\
    (!x. not_fresh_at sa x ==>
      lookup_var x t = lookup_var x s /\ FLOOKUP Gf x = FLOOKUP G x /\
      op_taint tf (Var x) = op_taint tn (Var x)) /\
    alloca_inv t /\ alloca_room ctx fn t /\
    (!aid p sz. FLOOKUP s.vs_allocas aid = SOME (p,sz) ==>
      FLOOKUP t.vs_allocas aid = SOME (p,sz)) /\
    (!i w p sz. MEM i (fn_insts fn) /\ i.inst_opcode = ALLOCA /\
      i.inst_operands = [Lit w] /\
      FLOOKUP t.vs_allocas i.inst_id = SOME (p,sz) ==> sz = w2n w)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all allocated_storage_copy_code >> strip_tac >>
  drule_all compile_alloc_buffer_path_resources_ptr >>
  disch_then (qspecl_then [`tn`,`PG`,`G`,`D`] strip_assume_tac) >>
  rename1 `ptr_covers gm tm root sm (32*n)` >>
  `copy_old_operand sc src` by metis_tac[copy_old_operand_mono] >>
  `eval_operand src sm = SOME a /\ op_taint tm src = {}` by
    (Cases_on `src` >> fs[copy_old_operand_def, eval_operand_def, op_taint_def]) >>
  `w2n (n2w b : bytes32) = b` by simp[] >>
  qpat_x_assum `compile_word_copy_loop _ _ _ _ _ _ _ = _` mp_tac >>
  asm_rewrite_tac[] >> disch_tac >>
  drule_at (Pat `compile_word_copy_loop _ _ _ _ _ _ _ = _`)
    compile_storage_copy_path_ptr >>
  disch_then (drule_at (Pat `ptr_covers _ _ _ _ _`)) >>
  disch_then (drule_at (Pat `alloca_room _ _ _`)) >>
  disch_then (qspecl_then [`n2w b`,`a`,`PG`,`D`] mp_tac) >>
  (impl_tac >- (simp[] >> metis_tac[])) >> strip_tac >>
  `gas_path_ptr D 0 ctx fn PG G tn s 0 Gf tf (OK t)` by
    metis_tac[fragGasPathPtrTheory.gas_path_ptr_then, ADD] >>
  qexistsl [`root`,`b`,`sm`,`gm`,`tm`,`t`,`Gf`,`tf`] >>
  simp[eval_operand_def] >>
  conj_tac >- metis_tac[] >>
  conj_tac
  >- (strip_tac >> irule (INST_TYPE [alpha |-> ``:256``] storage_copy_head_taint) >>
      qexistsl [`if loc = LocTransient then tf.t_trans else tf.t_stor`,`a`,`n`] >>
      simp[] >> rpt strip_tac >>
      qpat_x_assum `!i h. _` (qspecl_then [`i`,`h`] mp_tac) >>
      simp[AC ADD_ASSOC ADD_COMM]) >>
  conj_tac
  >- (rpt strip_tac >>
      qpat_x_assum `!i h. _` (qspecl_then [`i`,`h`] mp_tac) >>
      simp[AC ADD_ASSOC ADD_COMM]) >>
  conj_tac >- metis_tac[] >>
  conj_tac
  >- (rpt strip_tac >>
      `not_fresh_at sc x` by
        (qpat_x_assum `not_fresh_at sa x` mp_tac >>
         simp[not_fresh_at_def] >> metis_tac[LESS_EQ_TRANS]) >>
      metis_tac[]) >>
  metis_tac[]
QED

Theorem allocated_immutable_copy_code:
  compile_alloc_buffer cap sa = (buf,sc) /\
  compile_imm_copy_to_memory F imm src buf.buf_operand n off sc = ((),sb) /\
  fn_has_code sa sb fn ==>
  fn_has_code sa sc fn /\ fn_has_code sc sb fn /\
  sa.cs_next_var <= sc.cs_next_var
Proof
  strip_tac >>
  `!op off. cs_appends (compile_lit_byte_offset op off)` by
    (rpt gen_tac >> Cases_on `op` >>
     rw[compile_lit_byte_offset_def, cs_appends_return, cs_appends_emit_helpers]) >>
  `!n off. cs_appends (compile_imm_copy_to_memory F imm src buf.buf_operand n off)` by
    (Induct >> rw[compile_imm_copy_to_memory_def, cs_appends_return] >>
     rpt (FIRST [irule cs_appends_bind, irule cs_appends_ignore_bind] >>
       rw[compile_imm_load_word_appends, cs_appends_emit_helpers]) >> simp[]) >>
  `cs_extends sc sb` by metis_tac[cs_appends_def] >>
  `cs_extends sa sc` by metis_tac[compile_alloc_buffer_extends] >>
  drule compile_alloc_buffer_emission >> strip_tac >>
  drule_all fn_has_code_split >> simp[]
QED

(* Only compiler observations are extracted here. The ordinary witness is
   discarded; the later checked path selects all runtime and ghost witnesses. *)
Theorem runtime_immutable_registered_sequence:
  compile_imm_copy_to_memory F imm src dst n off sa = ((),sb) /\
  copy_old_operand sa src /\ copy_old_operand sa dst /\
  eval_operand src s = SOME a /\ eval_operand dst s = SOME b /\
  fn_has_code sa sb fn /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  (?bb. lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
    isPREFIX (emitted_insts sa sb) (DROP s.vs_inst_idx bb.bb_instructions)) /\
  sb.cs_current_bb = sa.cs_current_bb /\
  LENGTH sb.cs_current_insts = LENGTH sa.cs_current_insts + LENGTH (emitted_insts sa sb)
Proof
  strip_tac >> drule_all copy_runtime_run >> strip_tac >>
  fs[copy_runtime_frame_def, same_blocks_def] >>
  gvs[fn_has_code_def, emitted_blocks_def, IS_PREFIX_APPEND] >>
  pure_rewrite_tac[GSYM APPEND_ASSOC, DROP_LENGTH_APPEND] >> simp[]
QED

Theorem allocated_runtime_immutable_copy_path_ptr:
  compile_alloc_buffer (32*n) sa = (buf,sc) /\
  compile_imm_copy_to_memory F imm src buf.buf_operand n 0 sc = ((),sb) /\
  fn_has_code sa sb fn /\ copy_old_operand sa src /\
  eval_operand src s = SOME a /\ op_taint tn src = {} /\
  32*n < dimword(:256) /\ ~s.vs_halted /\ ~ctx_has_dalloca ctx /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  alloca_inv s /\ alloca_room ctx fn s /\ fn_inst_ids_distinct fn /\
  (!i w p sz. MEM i (fn_insts fn) /\ i.inst_opcode = ALLOCA /\
    i.inst_operands = [Lit w] /\
    FLOOKUP s.vs_allocas i.inst_id = SOME (p,sz) ==> sz = w2n w) ==>
  ?root b sm Gm tm z t Gf tf.
    buf.buf_operand = Var root /\
    gas_path_ptr D 0 ctx fn PG G tn s 0 Gf tf (OK t) /\
    gas_path_ptr D 0 ctx fn PG G tn s 0 Gm tm (OK sm) /\
    sm.vs_accounts = s.vs_accounts /\ sm.vs_transient = s.vs_transient /\
    sm.vs_data_section = s.vs_data_section /\ sm.vs_call_ctx = s.vs_call_ctx /\
    copy_runtime_frame sc sm sb z /\
    t = z with vs_inst_idx := LENGTH sb.cs_current_insts /\
    ~t.vs_halted /\ t.vs_current_bb = sb.cs_current_bb /\
    t.vs_inst_idx = LENGTH sb.cs_current_insts /\
    eval_operand buf.buf_operand t = SOME (n2w b) /\
    ptr_covers Gf tf root t (32*n) /\ b+32*n < dimword(:256) /\
    t.vs_memory = (immutable_transfers F F a (n2w b) n 0 sm).vs_memory /\
    tf.t_mem = immutable_copy_taints F a (n2w b) n 0 tm.t_mem /\
    tf.t_stor = tn.t_stor /\ tf.t_trans = tn.t_trans /\
    (0 < n ==> mem_word_taint tf.t_mem b = {}) /\
    (!x. not_fresh_at sa x ==>
      lookup_var x t = lookup_var x s /\ FLOOKUP Gf x = FLOOKUP G x /\
      op_taint tf (Var x) = op_taint tn (Var x)) /\
    alloca_inv t /\ alloca_room ctx fn t /\
    (!aid p sz. FLOOKUP s.vs_allocas aid = SOME (p,sz) ==>
      FLOOKUP t.vs_allocas aid = SOME (p,sz)) /\
    (!i w p sz. MEM i (fn_insts fn) /\ i.inst_opcode = ALLOCA /\
      i.inst_operands = [Lit w] /\
      FLOOKUP t.vs_allocas i.inst_id = SOME (p,sz) ==> sz = w2n w)
Proof
  strip_tac >> drule_all allocated_immutable_copy_code >> strip_tac >>
  drule_all compile_alloc_buffer_path_resources_ptr >>
  disch_then (qspecl_then [`tn`,`PG`,`G`,`D`] strip_assume_tac) >>
  rename1 `ptr_covers gm tm root sm (32*n)` >>
  `copy_old_operand sc src` by metis_tac[copy_old_operand_mono] >>
  `eval_operand src sm = SOME a /\ op_taint tm src = {}` by
    (Cases_on `src` >> fs[copy_old_operand_def, eval_operand_def, op_taint_def]) >>
  `w2n (n2w b : bytes32) = b` by simp[] >>
  qpat_x_assum `compile_imm_copy_to_memory _ _ _ _ _ _ _ = _` mp_tac >>
  asm_rewrite_tac[] >> disch_tac >>
  `copy_old_operand sc (Var root)` by simp[copy_old_operand_def] >>
  `eval_operand (Var root) sm = SOME (n2w b)` by simp[eval_operand_def] >>
  drule_all runtime_immutable_registered_sequence >> strip_tac >>
  drule_at (Pat `compile_imm_copy_to_memory _ _ _ _ _ _ _ = _`)
    compile_imm_copy_to_memory_path_ptr >>
  disch_then (drule_at (Pat `ptr_covers _ _ _ _ _`)) >>
  disch_then (drule_at (Pat `lookup_block _ _ = _`)) >>
  disch_then (qspecl_then [`ctx`,`n2w b`,`a`,`PG`,`D`] mp_tac) >>
  (impl_tac >- (simp[] >> decide_tac)) >> strip_tac >>
  suspend "endpoint"
QED
Resume allocated_runtime_immutable_copy_path_ptr[endpoint]:
  rename1 `copy_runtime_frame sc sm sb z` >>
  `ptr_covers Gf tf root z (32*n)` by
    (irule ptr_covers_copy_runtime_frame >> goal_assum (drule_at Any) >>
     qexistsl [`sm`,`sb`] >> simp[]) >>
  drule_all copy_runtime_recorded_resources >> strip_tac >>
  `EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
    (emitted_insts sc sb)` by
    (drule immutable_copy_opcodes >> simp[EVERY_MEM] >> strip_tac >>
     gen_tac >> strip_tac >> first_x_assum drule >> strip_tac >>
     gvs[is_terminator_def]) >>
  `z.vs_current_bb = sm.vs_current_bb /\ ~z.vs_halted` by
    (`run_inst_seq (emitted_insts sc sb) sm = OK z` by
       fs[copy_runtime_frame_def] >>
     drule_all run_inst_seq_preserves_entry_control >> simp[]) >>
  `sm.vs_inst_idx + LENGTH (emitted_insts sc sb) = LENGTH sb.cs_current_insts` by
    simp[] >>
  `gas_path_ptr D 0 ctx fn PG G tn s 0 Gf tf
    (OK (z with vs_inst_idx := LENGTH sb.cs_current_insts))` by
    metis_tac[gas_path_ptr_then, ADD] >>
  qexistsl [`root`,`b`,`sm`,`gm`,`tm`,`z`,
    `z with vs_inst_idx := LENGTH sb.cs_current_insts`,`Gf`,`tf`] >>
  simp[eval_operand_def, lookup_var_def] >>
  conj_tac >- fs[lookup_var_def] >>
  conj_tac >- metis_tac[] >>
  conj_tac
  >- (rpt strip_tac >>
      `not_fresh_at sc x` by
        (qpat_x_assum `not_fresh_at sa x` mp_tac >>
         simp[not_fresh_at_def] >> metis_tac[LESS_EQ_TRANS]) >>
      fs[lookup_var_def] >> metis_tac[]) >>
  conj_tac
  >- (irule alloca_inv_fields >> qexists `z` >> simp[]) >>
  conj_tac
  >- (irule alloca_room_fields >> qexists `z` >> simp[]) >>
  simp[] >> metis_tac[]
QED
Finalise allocated_runtime_immutable_copy_path_ptr

Theorem allocated_storage_string_path_ptr:
  (loc = LocStorage \/ loc = LocTransient) /\
  val_wf (BaseTV (StringT max)) (StringV str) /\
  compile_alloc_buffer (32 * type_slot_size (BaseTV (StringT max))) sa = (buf,sc) /\
  compile_word_copy_loop src buf.buf_operand (type_slot_size (BaseTV (StringT max)))
    loc LocMemory F sc = (u,sb) /\
  fn_has_code sa sb fn /\ copy_old_operand sa src /\
  eval_operand src s = SOME a /\ op_taint tn src = {} /\
  key_taint (if loc = LocTransient then tn.t_trans else tn.t_stor) a = {} /\
  type_slot_size (BaseTV (StringT max)) < dimword(:256) /\
  32 * type_slot_size (BaseTV (StringT max)) < dimword(:256) /\
  ~s.vs_halted /\ ~ctx_has_dalloca ctx /\
  s.vs_current_bb = sa.cs_current_bb /\ s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  alloca_inv s /\ alloca_room ctx fn s /\ fn_inst_ids_distinct fn /\
  (!i w p sz. MEM i (fn_insts fn) /\ i.inst_opcode = ALLOCA /\
    i.inst_operands = [Lit w] /\
    FLOOKUP s.vs_allocas i.inst_id = SOME (p,sz) ==> sz = w2n w) ==>
  ?root b sm t Gf tf.
    sm.vs_accounts = s.vs_accounts /\ sm.vs_transient = s.vs_transient /\
    sm.vs_data_section = s.vs_data_section /\ sm.vs_call_ctx = s.vs_call_ctx /\
    buf.buf_operand = Var root /\
    gas_path_ptr D 0 ctx fn PG G tn s 0 Gf tf (OK t) /\
    ~t.vs_halted /\ t.vs_current_bb = sb.cs_current_bb /\
    t.vs_inst_idx = LENGTH sb.cs_current_insts /\
    eval_operand buf.buf_operand t = SOME (n2w b) /\
    ptr_covers Gf tf root t (val_store_size (BaseTV (StringT max)) (StringV str)) /\
    ptr_covers Gf tf root t (32 * type_slot_size (BaseTV (StringT max))) /\
    b+32 * type_slot_size (BaseTV (StringT max)) < dimword(:256) /\
    copy_prefix loc a b (type_slot_size (BaseTV (StringT max))) sm
      (type_slot_size (BaseTV (StringT max))) t /\
    eval_operand src t = SOME a /\ op_taint tf src = {} /\
    mem_word_taint tf.t_mem b = {} /\
    tf.t_stor = tn.t_stor /\ tf.t_trans = tn.t_trans /\ tf.t_imm = tn.t_imm /\
    (!x. not_fresh_at sa x ==>
      lookup_var x t = lookup_var x s /\ FLOOKUP Gf x = FLOOKUP G x /\
      op_taint tf (Var x) = op_taint tn (Var x)) /\
    alloca_inv t /\ alloca_room ctx fn t /\
    (!aid p sz. FLOOKUP s.vs_allocas aid = SOME (p,sz) ==>
      FLOOKUP t.vs_allocas aid = SOME (p,sz)) /\
    (!i w p sz. MEM i (fn_insts fn) /\ i.inst_opcode = ALLOCA /\
      i.inst_operands = [Lit w] /\
      FLOOKUP t.vs_allocas i.inst_id = SOME (p,sz) ==> sz = w2n w)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all allocated_storage_copy_path_ptr >>
  disch_then (qspecl_then [`PG`,`G`,`D`] strip_assume_tac) >>
  drule string_store_size_slots >> strip_tac >>
  qexistsl [`root`,`b`,`sm`,`t`,`Gf`,`tf`] >> simp[] >>
  reverse conj_tac >- metis_tac[] >>
  irule ptr_covers_mono >> goal_assum (drule_at Any) >> simp[]
QED

Theorem allocated_runtime_immutable_string_path_ptr:
  val_wf (BaseTV (StringT max)) (StringV str) /\
  compile_alloc_buffer (32 * type_slot_size (BaseTV (StringT max))) sa = (buf,sc) /\
  compile_imm_copy_to_memory F imm src buf.buf_operand
    (type_slot_size (BaseTV (StringT max))) 0 sc = ((),sb) /\
  fn_has_code sa sb fn /\ copy_old_operand sa src /\
  eval_operand src s = SOME a /\ op_taint tn src = {} /\
  32 * type_slot_size (BaseTV (StringT max)) < dimword(:256) /\
  ~s.vs_halted /\ ~ctx_has_dalloca ctx /\
  s.vs_current_bb = sa.cs_current_bb /\ s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  alloca_inv s /\ alloca_room ctx fn s /\ fn_inst_ids_distinct fn /\
  (!i w p sz. MEM i (fn_insts fn) /\ i.inst_opcode = ALLOCA /\
    i.inst_operands = [Lit w] /\
    FLOOKUP s.vs_allocas i.inst_id = SOME (p,sz) ==> sz = w2n w) ==>
  ?root b sm z t Gf tf.
    sm.vs_accounts = s.vs_accounts /\ sm.vs_transient = s.vs_transient /\
    sm.vs_data_section = s.vs_data_section /\ sm.vs_call_ctx = s.vs_call_ctx /\
    buf.buf_operand = Var root /\
    gas_path_ptr D 0 ctx fn PG G tn s 0 Gf tf (OK t) /\
    copy_runtime_frame sc sm sb z /\
    t = z with vs_inst_idx := LENGTH sb.cs_current_insts /\
    ~t.vs_halted /\ t.vs_current_bb = sb.cs_current_bb /\
    t.vs_inst_idx = LENGTH sb.cs_current_insts /\
    eval_operand buf.buf_operand t = SOME (n2w b) /\
    ptr_covers Gf tf root t (val_store_size (BaseTV (StringT max)) (StringV str)) /\
    ptr_covers Gf tf root t (32 * type_slot_size (BaseTV (StringT max))) /\
    b+32 * type_slot_size (BaseTV (StringT max)) < dimword(:256) /\
    t.vs_memory = (immutable_transfers F F a (n2w b)
      (type_slot_size (BaseTV (StringT max))) 0 sm).vs_memory /\
    mem_word_taint tf.t_mem b = {} /\
    tf.t_stor = tn.t_stor /\ tf.t_trans = tn.t_trans /\
    (!x. not_fresh_at sa x ==>
      lookup_var x t = lookup_var x s /\ FLOOKUP Gf x = FLOOKUP G x /\
      op_taint tf (Var x) = op_taint tn (Var x)) /\
    alloca_inv t /\ alloca_room ctx fn t /\
    (!aid p sz. FLOOKUP s.vs_allocas aid = SOME (p,sz) ==>
      FLOOKUP t.vs_allocas aid = SOME (p,sz)) /\
    (!i w p sz. MEM i (fn_insts fn) /\ i.inst_opcode = ALLOCA /\
      i.inst_operands = [Lit w] /\
      FLOOKUP t.vs_allocas i.inst_id = SOME (p,sz) ==> sz = w2n w)
Proof
  strip_tac >> drule_all allocated_runtime_immutable_copy_path_ptr >>
  disch_then (qspecl_then [`PG`,`G`,`D`] strip_assume_tac) >>
  drule string_store_size_slots >> strip_tac >>
  qexistsl [`root`,`b`,`sm`,`z`,`t`,`Gf`,`tf`] >> gvs[] >>
  reverse conj_tac >- metis_tac[] >>
  irule ptr_covers_mono >> goal_assum (drule_at Any) >> simp[]
QED
