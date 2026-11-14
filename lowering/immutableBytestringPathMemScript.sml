(* Counted bytestring stores share one path for both constructor bases. *)
Theory immutableBytestringPathMem
Ancestors
  immutableLoopStoreMem immutableLoopOptionMem
  immutableAssignStoreMem immutableCopyExecution immutableWordExecution fragGasSeqMem
  placeCopyControlPath stmtForRangeMemoryParts fragGasPathMem
  bytestringCopyExecution fragExec memContinuation
  instMemFrontier memSafeRun fragExecMem
  context compileEnv emitHelper emitHelperProps loweringStateRelDefs
  exprLoweringProps venomExecSemantics venomState venomInst
  words arithmetic list rich_list finite_map

Theorem bytestring_word_count_mem_ok[local]:
  compile_bytestring_word_count src sa = (out,sb) /\
  eval_operand src s = SOME a /\ w2n a + 32 <= s.vs_alloca_next ==>
  run_inst_seq_mem_ok (emitted_insts sa sb) s
Proof
  strip_tac >>
  gvs[compile_bytestring_word_count_def, emit_op_def,
      comp_bind_def, comp_ignore_bind_def, comp_return_def,
      fresh_id_def, fresh_var_def, emit_def] >>
  simp[emitted_insts_def, DROP_APPEND, SUB_PLUS, run_inst_seq_mem_ok_def,
       mk_inst_def, step_inst_base_opcode_eqs, exec_pure2_def, exec_read1_def,
       SRULE [mk_inst_def] below_frontier_MLOAD,
       below_frontier_no_ranges, inst_dload_in_section_def,
       eval_operand_lit, slot_copy_operand_update]
QED

Theorem bytestring_word_count_mem_path:
  compile_bytestring_word_count src sa = (out,sb) /\
  fn_has_code sa sb func /\
  eval_operand src s = SOME w /\ mload (w2n w) s = n2w len /\
  len + 63 < dimword (:256) /\ w2n w + 32 <= s.vs_alloca_next /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?t. gas_path_mem ctx func s 0 (OK t) /\
      eval_operand out t = SOME (n2w (1 + word_size len)) /\
      (t with <|vs_vars := s.vs_vars; vs_inst_idx := s.vs_inst_idx|>) = s /\
      (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s) /\
      ~t.vs_halted /\ t.vs_current_bb = sb.cs_current_bb /\
      t.vs_inst_idx = LENGTH sb.cs_current_insts
Proof
  strip_tac >> drule_all bytestring_word_count_run >> strip_tac >>
  drule bytestring_word_count_shape >> strip_tac >>
  `?bb. lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
        isPREFIX (emitted_insts sa sb)
          (DROP s.vs_inst_idx bb.bb_instructions)` by
    (fs[fn_has_code_def, same_blocks_def, IS_PREFIX_APPEND] >>
     qexists_tac `l` >> simp[DROP_APPEND, SUB_PLUS]) >>
  `LENGTH (FILTER (\i. i.inst_opcode = GAS) (emitted_insts sa sb)) = 0` by
    (simp[FILTER_EQ_NIL, EVERY_MEM] >> fs[EVERY_MEM]) >>
  `EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
      (emitted_insts sa sb)` by fs[EVERY_MEM] >>
  `run_inst_seq_mem_ok (emitted_insts sa sb) s` by
    (irule bytestring_word_count_mem_ok >> metis_tac[]) >>
  drule_all run_inst_seq_gas_path_mem >> strip_tac >>
  qexists_tac `t with vs_inst_idx := LENGTH sb.cs_current_insts` >>
  fs[same_blocks_def, eval_operand_def, lookup_var_def] >>
  fs[venom_state_component_equality] >>
  qpat_x_assum `!ctx. gas_path_mem _ _ _ _ _` (qspec_then `ctx` mp_tac) >>
  simp[ADD_COMM]
QED

Theorem compile_store_immutable_bytestring_mem_path_option:
  compile_store_immutable_bytestring imm src dst sa = ((),sb) /\
  fn_has_code sa sb func /\ len + 63 < dimword (:256) /\
  (!x. src = Var x \/ dst = Var x \/ (?region. imm = SOME region /\ region = Var x) ==> not_fresh_at sa x) /\
  eval_operand src s = SOME a /\ eval_operand dst s = SOME b /\
  (!region. imm = SOME region ==> eval_operand region s = SOME 0w) /\ mload (w2n a) s = n2w len /\
  (!j. j < 1 + word_size len ==>
       w2n (a+n2w (32*j)) + 32 <= s.vs_alloca_next /\
       w2n (b+n2w (32*j)) + 32 <= s.vs_alloca_next) /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?t. gas_path_mem ctx func s 0 (OK t) /\
      mem_cont_sim ctx func s t /\
      t.vs_allocas = s.vs_allocas /\ t.vs_alloca_next = s.vs_alloca_next /\
      (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s) /\
      (t with <|vs_vars := s.vs_vars;
                vs_current_bb := s.vs_current_bb;
                vs_prev_bb := s.vs_prev_bb;
                vs_inst_idx := s.vs_inst_idx|>) =
        immutable_transfers T T a b (1 + word_size len) 0 s /\
      ~t.vs_halted /\ t.vs_current_bb = sb.cs_current_bb /\
      t.vs_inst_idx = LENGTH sb.cs_current_insts
Proof
  strip_tac >>
  Cases_on `compile_bytestring_word_count src sa` >>
  rename1 `compile_bytestring_word_count src sa = (wc,sm)` >>
  Cases_on `compile_word_copy_loop_base src dst wc LocMemory LocCode T
    imm sm` >>
  rename1 `compile_word_copy_loop_base src dst wc LocMemory LocCode T
    imm sm = (u,sn)` >>
  `sn = sb` by
    fs[compile_store_immutable_bytestring_def, comp_bind_def,
       comp_ignore_bind_def, comp_return_def, pairTheory.UNCURRY] >> gvs[] >>
  drule bytestring_word_count_shape >> strip_tac >>
  `cs_extends sa sm` by
    (irule cs_extends_same_block >> fs[same_blocks_def] >> simp[]) >>
  `ci_mono sm sb` by
    (mp_tac (Q.SPECL [`src`, `dst`, `wc`, `LocMemory`, `LocCode`, `T`,
                      `imm`, `sm`] ci_mono_word_copy) >> simp[]) >>
  `fn_has_code sa sm func /\ fn_has_code sm sb func` by
    (irule fn_has_code_split >> fs[ci_mono_def]) >>
  `!x. not_fresh_at sa x ==> not_fresh_at sm x` by
    (simp[not_fresh_at_def] >> rpt strip_tac >> decide_tac) >>
  `!x. wc = Var x ==> not_fresh_at sm x` by
    (qpat_x_assum `compile_bytestring_word_count _ _ = _` mp_tac >>
     simp[compile_bytestring_word_count_def, emit_op_def,
          comp_bind_def, comp_ignore_bind_def, comp_return_def,
          fresh_id_def, fresh_var_def, emit_def] >>
     strip_tac >> gvs[not_fresh_at_def]) >>
  `1 + word_size len < dimword (:256)` by
    (`(len + 31) DIV 32 <= len + 31` by simp[DIV_LESS_EQ] >>
     fs[vfmConstantsTheory.word_size_def] >> decide_tac) >>
  suspend "execute"
QED

Resume compile_store_immutable_bytestring_mem_path_option[execute]:
  `w2n a + 32 <= s.vs_alloca_next` by
    (qpat_assum `!j. j < _ ==> w2n _ + 32 <= _ /\ _`
       (qspec_then `0` mp_tac) >>
     simp_tac (srw_ss()) [MULT_0, word_0_n2w, WORD_ADD_0, GSYM ADD1] >>
     metis_tac[]) >>
  drule_all bytestring_word_count_mem_path >>
  disch_then (qspec_then `ctx` strip_assume_tac) >>
  rename1 `gas_path_mem ctx func s 0 (OK r)` >>
  `r.vs_labels = s.vs_labels /\ stmtSimStoreCopy$store_copy_normalize s r = s /\
   r.vs_alloca_next = s.vs_alloca_next /\ r.vs_allocas = s.vs_allocas` by
    (fs[venom_state_component_equality,
        stmtSimStoreCopyTheory.store_copy_normalize_def]) >>
  `!p. (!x. p = Var x ==> not_fresh_at sa x) ==>
       eval_operand p r = eval_operand p s` by
    (Cases >> simp[eval_operand_def]) >>
  `eval_operand src r = SOME a /\ eval_operand dst r = SOME b /\
   (!region. imm = SOME region ==> eval_operand region r = SOME 0w)` by metis_tac[] >>
  `!x. src = Var x \/ dst = Var x \/ wc = Var x \/ (?region. imm = SOME region /\ region = Var x) ==>
       not_fresh_at sm x` by metis_tac[] >>
  `!j. j < 1 + word_size len ==>
       w2n (a+n2w (32*j)) + 32 <= r.vs_alloca_next /\
       w2n (b+n2w (32*j)) + 32 <= r.vs_alloca_next` by simp[] >>
  drule_all compile_imm_store_loop_mem_path_option >>
  disch_then (qspec_then `ctx` strip_assume_tac) >>
  `gas_path_mem ctx func s 0 (OK t)` by
    (drule_all gas_path_mem_then >> simp[]) >>
  `mem_cont_sim ctx func s t` by metis_tac[immutable_loop_path_mem_cont] >>
  qexists_tac `t` >> simp[] >>
  qpat_x_assum `(t with <|vs_vars := r.vs_vars; vs_current_bb := r.vs_current_bb;
      vs_prev_bb := r.vs_prev_bb; vs_inst_idx := r.vs_inst_idx|>) = _`
    (mp_tac o AP_TERM ``stmtSimStoreCopy$store_copy_normalize s``) >>
  simp[immutable_transfers_normalize, stmtSimStoreCopyTheory.store_copy_normalize_def]
QED

Finalise compile_store_immutable_bytestring_mem_path_option

Theorem compile_store_immutable_bytestring_mem_path:
  compile_store_immutable_bytestring (SOME region) src dst sa = ((),sb) /\
  fn_has_code sa sb func /\ len + 63 < dimword (:256) /\
  (!x. src = Var x \/ dst = Var x \/ region = Var x ==> not_fresh_at sa x) /\
  eval_operand src s = SOME a /\ eval_operand dst s = SOME b /\
  eval_operand region s = SOME 0w /\ mload (w2n a) s = n2w len /\
  (!j. j < 1 + word_size len ==>
       w2n (a+n2w (32*j)) + 32 <= s.vs_alloca_next /\
       w2n (b+n2w (32*j)) + 32 <= s.vs_alloca_next) /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?t. gas_path_mem ctx func s 0 (OK t) /\
      mem_cont_sim ctx func s t /\
      t.vs_allocas = s.vs_allocas /\ t.vs_alloca_next = s.vs_alloca_next /\
      (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s) /\
      (t with <|vs_vars := s.vs_vars;
                vs_current_bb := s.vs_current_bb;
                vs_prev_bb := s.vs_prev_bb;
                vs_inst_idx := s.vs_inst_idx|>) =
        immutable_transfers T T a b (1 + word_size len) 0 s /\
      ~t.vs_halted /\ t.vs_current_bb = sb.cs_current_bb /\
      t.vs_inst_idx = LENGTH sb.cs_current_insts
Proof
  strip_tac >>
  mp_tac (Q.INST [`imm` |-> `SOME region`]
    (SPEC_ALL compile_store_immutable_bytestring_mem_path_option)) >>
  impl_tac >- (simp[] >> metis_tac[]) >>
  strip_tac >> qexists_tac `t` >> simp[]
QED
