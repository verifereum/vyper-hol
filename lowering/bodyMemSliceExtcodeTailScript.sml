(* Counted external-code slice tail and result capacity. *)
Theory bodyMemSliceExtcodeTail
Ancestors
  bodyMemSliceExtcode bodyMemSliceTerminal bodyMemBiSha256Compose
  exprSimSliceExtcodeContinue exprSimMemDefs exprSimMemUnwrap
  bodyUnopFragMemory allocaHistoryFragment fragGasSeqMem
  venomMemDefs loweringPosts exprLoweringProps exprSimSliceExtcode
  vyperState list rich_list words arithmetic

Theorem slice_extcode_tail_outcome_mem:
  compile_slice_extcode addr sop lop out dst sa = (r,sb) /\
  fn_has_code sa sb func /\ fn_inst_ids_distinct func /\ alloca_history func s /\ ~s.vs_halted /\
  lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
  isPREFIX (emitted_insts sa sb) (DROP s.vs_inst_idx bb.bb_instructions) /\
  s.vs_current_bb = sa.cs_current_bb /\ s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  eval_operand addr s = SOME (typed_val_to_w256 (BaseTV AddressT) (BytesV bs)) /\
  eval_operand sop s = SOME (n2w i) /\ eval_operand lop s = SOME (n2w k) /\
  eval_operand out s = SOME p /\ eval_operand dst s = SOME (p+32w) /\
  (!x. MEM (Var x) [addr;sop;lop;out;dst] ==> not_fresh_at sa x) /\
  accounts_agree cx es.accounts s.vs_accounts /\ accounts_well_typed es.accounts /\
  LENGTH bs = 20 /\ i < dimword (:256) /\ k < dimword (:256) /\ k <= n /\
  stmt_state_rel ctx func cenv cx es s /\ local_ptrs_reserved cenv sa /\
  sbase.cs_next_var <= sa.cs_next_var /\ sbase.cs_next_id <= aid /\
  aid < sa.cs_next_id /\ aid < sb.cs_next_id /\
  MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\ inst.inst_id = aid /\
  FLOOKUP s.vs_allocas aid = SOME (w2n p,cap) /\
  w2n p + cap < dimword (:256) /\ 32+n <= cap /\
  (!nm off sz. local_region cenv es.scopes s nm off sz ==>
    regions_disjoint (w2n p) cap off sz) /\
  (!j off sz. FLOOKUP s.vs_allocas j = SOME (off,sz) /\ j < sbase.cs_next_id ==>
    regions_disjoint (w2n p) cap off sz) /\
  expr_type e = BaseT (BytesT (Dynamic n)) /\ es.gas_obs = [] /\
  evaluate_type (get_tenv cx) (expr_type e) = SOME ftv /\ type_memory_size ftv <= cap ==>
  gas_outcome T tops (ctx,func)
    (do acc <- get_accounts;
        v <- lift_sum (evaluate_slice
          (BytesV (lookup_account (word_of_bytes_be bs) acc).code)
          (IntV (&i)) (IntV (&k)) n);
        return (Value v) od) (es,s)
    (\res ee t. ?tv. res = INL tv /\
       vv_post ctx func cenv cx e es sbase sb s ee tv
         (LocatedValue (expr_type e) (mk_ptr out LocMemory)) t /\
       vv_store_bound cx (expr_type e) (expr_type e) ee tv
         (LocatedValue (expr_type e) (mk_ptr out LocMemory)) t /\
       t.vs_current_bb = sb.cs_current_bb /\ t.vs_inst_idx = LENGTH sb.cs_current_insts /\
       alloca_history func t /\ s.vs_alloca_next <= t.vs_alloca_next)
    (\res ee r. expr_exit res r)
Proof
  strip_tac >> drule_all slice_extcode_account >> strip_tac >>
  `LENGTH (lookup_account (w2w (typed_val_to_w256 (BaseTV AddressT) (BytesV bs)))
      s.vs_accounts).code < dimword (:256)` by
    (simp[wordsTheory.dimword_def] >> decide_tac) >>
  `alloca_inv s` by fs[stmt_state_rel_def] >>
  `w2n p + cap <= s.vs_alloca_next` by
    (fs[alloca_inv_def, alloca_next_valid_def] >> metis_tac[ADD_COMM]) >>
  `w2n (p+32w) = w2n p + 32` by
    (simp[word_add_def, w2n_n2w] >> irule LESS_MOD >> decide_tac) >>
  `run_inst_seq_mem_ok (emitted_insts sa sb) s` by
    (irule slice_extcode_tail_mem_ok >>
     qpat_assum `compile_slice_extcode _ _ _ _ _ _ = _` (irule_at Any) >>
     simp[] >> decide_tac) >>
  `EVERY (\inst. inst.inst_opcode <> INVOKE /\
      ~is_terminator inst.inst_opcode /\ inst.inst_opcode <> GAS)
      (emitted_insts sa sb)` by metis_tac[slice_extcode_zero_code] >>
  Cases_on `i+k <= LENGTH (lookup_account (word_of_bytes_be bs) es.accounts).code`
  >- suspend "success"
  >> suspend "range"
QED

Resume slice_extcode_tail_outcome_mem[range]:
  drule_all slice_extcode_tail_run >> simp[] >> strip_tac >>
  `EVERY (\inst. inst.inst_opcode <> GAS /\ inst.inst_opcode <> INVOKE /\
      ~is_terminator inst.inst_opcode) (emitted_insts sa sb)` by
    fs[EVERY_MEM] >>
  drule_all run_inst_seq_abort_zero_path_mem >>
  disch_then (qspec_then `ctx` strip_assume_tac) >>
  irule slice_terminal_outcome_mem >>
  qexistsl_tac [`Abort Revert_abort (t with vs_inst_idx := j)`,
    `INR (Error (RuntimeError "evaluate_slice range"))`] >>
  simp[get_accounts_def, bind_def, lift_sum_def, return_def,
       exprSimSliceSourceTheory.slice_bytes_nat, fragExecTheory.exit_result_def,
       exprSimDefsTheory.expr_exit_def, raise_def, fragGasModeTheory.gas_marked_path_def] >>
  fs[fragGasModeTheory.gas_marked_path_def]
QED

Resume slice_extcode_tail_outcome_mem[success]:
  `w2n (n2w i : bytes32) + w2n (n2w k : bytes32) <=
    LENGTH (lookup_account (w2w (typed_val_to_w256 (BaseTV AddressT) (BytesV bs)))
      s.vs_accounts).code` by simp[] >>
  `32 + w2n (n2w k : bytes32) <= cap /\ w2n (n2w k : bytes32) <= n` by simp[] >>
  drule_all slice_extcode_tail_vv_post >> strip_tac >>
  suspend "success_path"
QED

Resume slice_extcode_tail_outcome_mem[success_path]:
  drule_all slice_extcode_tail_frame >> strip_tac >> gvs[] >>
  `s.vs_alloca_next <= t.vs_alloca_next` by
    (irule sha256_run_inst_seq_alloca_next_mono >>
     qexists_tac `emitted_insts sa sb` >> simp[] >> fs[EVERY_MEM]) >>
  `EVERY (\inst. inst.inst_opcode <> INVOKE /\
      ~is_terminator inst.inst_opcode) (emitted_insts sa sb)` by fs[EVERY_MEM] >>
  `gas_path_mem ctx func s 0
      (OK (t with vs_inst_idx := s.vs_inst_idx + LENGTH (emitted_insts sa sb)))` by
    (mp_tac (Q.SPECL [`emitted_insts sa sb`, `s`, `t`, `ctx`, `func`, `bb`]
       run_inst_seq_gas_path_mem) >> simp[] >>
     `FILTER (\inst. inst.inst_opcode = GAS) (emitted_insts sa sb) = []` by
       (simp[FILTER_EQ_NIL, EVERY_MEM] >> fs[EVERY_MEM]) >> simp[]) >>
  `?rest. DROP s.vs_inst_idx bb.bb_instructions = emitted_insts sa sb ++ rest` by
    metis_tac[IS_PREFIX_APPEND] >>
  `alloca_history func
      (t with vs_inst_idx := s.vs_inst_idx + LENGTH (emitted_insts sa sb))` by
    (irule alloca_history_run_inst_seq >>
     simp[] >> conj_tac
     >- gvs[] >> fs[EVERY_MEM]) >>
  drule slice_extcode_tail_control >> strip_tac >>
  irule slice_terminal_outcome_mem >>
  qexistsl_tac [`OK (t with vs_inst_idx := LENGTH sb.cs_current_insts)`,
    `INL (Value (BytesV (TAKE k (DROP i
      (lookup_account (word_of_bytes_be bs) es.accounts).code))))`] >>
  simp[get_accounts_def, bind_def, lift_sum_def, return_def,
       exprSimSliceSourceTheory.slice_bytes_nat, LENGTH_APPEND] >>
  `es with gas_obs := [] = es` by
    simp[vyperStateTheory.evaluation_state_component_equality] >>
  `t.vs_current_bb = s.vs_current_bb` by
    metis_tac[fragExecTheory.exec_block_run_inst_seq] >>
  gvs[] >>
  qpat_assum `expr_type e = _` (fn th => rewrite_tac[GSYM th]) >>
  irule vv_store_bound_capacity >>
  simp[contextTheory.mk_ptr_def] >>
  gvs[contextTheory.mk_ptr_def] >>
  goal_assum (drule_at Any) >>
  metis_tac[post_value_type_bytestring, compileEnvTheory.is_bytestring_type_def]
QED

Finalise slice_extcode_tail_outcome_mem
