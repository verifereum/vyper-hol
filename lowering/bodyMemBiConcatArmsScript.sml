(* Memory-safe concat operand arms at their concrete endpoints. *)
Theory bodyMemBiConcatArms
Ancestors
  bodyMemBiConcatFragments bodyMemAggregateBounds exprSimConcatArgs
  allocaHistoryFragment bodyMemBiConcatOperandMemory concatMemory fragGasSeqMem emitHelperProps venomInst
  allocaHistory exprSimConcatStep exprSimConcatStore exprSimConcatPath
  exprSimAlloc exprSimProps exprSimDefs loweringPosts exprLoweringProps
  rich_list valueEncodingProps venomState venomMemProps words arithmetic compileEnv
Libs
  monadsyntax

Theorem concat_fixed_arm_mem:
  !ctx func cenv cx es t sx s2 data_ptr off_ptr x m bs ow k binst B bsz oinst.
    (do offset_op <- emit_op MLOAD [off_ptr];
        dst <- emit_op ADD [data_ptr; offset_op];
        emit_void MSTORE [dst; x];
        new_offset <- emit_op ADD [offset_op; Lit (n2w m)];
        emit_void MSTORE [off_ptr; new_offset]
     od) sx = ((), s2) /\
    fn_has_code sx s2 func /\ fn_inst_ids_distinct func /\ ~t.vs_halted /\
    t.vs_current_bb = sx.cs_current_bb /\
    t.vs_inst_idx = LENGTH sx.cs_current_insts /\
    local_ptrs_reserved cenv sx /\ stmt_state_rel ctx func cenv cx es t /\
    eval_operand data_ptr t = SOME (n2w (B + 32)) /\
    eval_operand off_ptr t = SOME ow /\
    eval_operand x t = SOME (word_of_bytes_be (PAD_RIGHT 0w 32 bs)) /\
    (!z. data_ptr = Var z ==> not_fresh_at sx z) /\
    (!z. off_ptr = Var z ==> not_fresh_at sx z) /\
    (!z. x = Var z ==> not_fresh_at sx z) /\
    MEM binst (fn_insts func) /\ binst.inst_opcode = ALLOCA /\
    FLOOKUP t.vs_allocas binst.inst_id = SOME (B, bsz) /\
    MEM oinst (fn_insts func) /\ oinst.inst_opcode = ALLOCA /\
    FLOOKUP t.vs_allocas oinst.inst_id = SOME (w2n ow, 64) /\
    (!name lb lsz. local_region cenv es.scopes t name lb lsz ==>
       (B + bsz <= lb \/ lb + lsz <= B) /\
       (w2n ow + 64 <= lb \/ lb + lsz <= w2n ow)) /\
    (B + bsz <= w2n ow \/ w2n ow + 64 <= B) /\ B + bsz < dimword (:256) /\
    mload (w2n ow) t = n2w k /\ LENGTH bs = m /\ m <= 32 /\
    32 + k + 32 <= bsz /\ alloca_history func t ==>
    ?t2. gas_path_mem ctx func t 0 (OK t2) /\
      stmt_state_rel ctx func cenv cx es t2 /\ ~t2.vs_halted /\
      t2.vs_current_bb = s2.cs_current_bb /\
      t2.vs_inst_idx = LENGTH s2.cs_current_insts /\
      t2.vs_allocas = t.vs_allocas /\
      (!z. not_fresh_at sx z ==> lookup_var z t2 = lookup_var z t) /\
      mem_bytes_at (B + 32) (k + m) t2.vs_memory =
        mem_bytes_at (B + 32) k t.vs_memory ++ bs /\
      mload (w2n ow) t2 = n2w (k + m) /\
      (!p n. (p + n <= B \/ B + bsz <= p) /\
             (p + n <= w2n ow \/ w2n ow + 64 <= p) ==>
             mem_bytes_at p n t2.vs_memory = mem_bytes_at p n t.vs_memory) /\
      alloca_history func t2 /\ t2.vs_alloca_next = t.vs_alloca_next
Proof
  rpt gen_tac >> disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  `B + bsz <= t.vs_alloca_next /\ w2n ow + 64 <= t.vs_alloca_next` by
    metis_tac[aggregate_alloca_capacity_mem] >>
  `w2n (n2w (B + 32) : bytes32) = B + 32 /\
   w2n (mload (w2n ow) t) = k` by
    (simp[] >> conj_tac >> irule LESS_MOD >> fs[dimword_def]) >>
  drule_all concat_fixed_step_run >> strip_tac >>
  `run_inst_seq_mem_ok (emitted_insts sx s2) t` by
    (drule concat_fixed_operands_mem_ok >>
     disch_then (qspecl_then [`t`, `n2w (B + 32)`, `ow`] mp_tac) >>
     simp[] >> decide_tac) >>
  drule concat_fixed_code_shape >> strip_tac >>
  drule_all concat_code_prefix >> strip_tac >>
  `gas_path_mem ctx func t 0
    (OK (mstore (w2n ow) (mload (w2n ow) t + n2w m)
      (mstore (w2n (n2w (B + 32) + mload (w2n ow) t))
        (word_of_bytes_be (PAD_RIGHT 0w 32 bs)) t) with
       <|vs_vars := V; vs_inst_idx := LENGTH s2.cs_current_insts|>))` by
    (drule_at (Pat `run_inst_seq _ _ = OK _`) run_inst_seq_gas_path_mem >>
     disch_then (qspecl_then [`ctx`, `func`, `bb`] mp_tac) >>
     drule concat_fixed_shape >> strip_tac >>
     gvs[mk_inst_def, is_terminator_def]) >>
  `w2n (n2w (B + 32) + mload (w2n ow) t) = B + 32 + k` by
    (simp[word_add_n2w] >> irule LESS_MOD >> fs[dimword_def]) >>
  qabbrev_tac `a = B + 32 + k` >>
  qabbrev_tac `wd = word_of_bytes_be (PAD_RIGHT 0w 32 bs) : bytes32` >>
  qabbrev_tac `t2 = mstore (w2n ow) (n2w (k + m)) (mstore a wd t) with
    <|vs_vars := V; vs_inst_idx := LENGTH s2.cs_current_insts|>` >>
  qexists_tac `t2` >>
  conj_tac >- (simp[Abbr `t2`, word_add_n2w] >>
    qpat_x_assum `gas_path_mem _ _ _ _ _` mp_tac >>
    simp[Abbr `a`, Abbr `wd`, word_add_n2w]) >>
  conj_tac >- suspend "relation" >>
  conj_tac >- simp[Abbr `t2`, mstore_def] >>
  conj_tac >- (qunabbrev_tac `t2` >> simp_tac (srw_ss()) [mstore_def, LET_THM] >> metis_tac[]) >>
  conj_tac >- simp[Abbr `t2`] >>
  conj_tac >- simp[Abbr `t2`, mstore_def] >>
  conj_tac >- simp[Abbr `t2`, mstore_def, lookup_var_def] >>
  conj_tac >- suspend "payload" >>
  conj_tac >- (irule EQ_TRANS >>
    qexists_tac `mload (w2n ow) (mstore (w2n ow) (n2w (k + m)) (mstore a wd t))` >>
    conj_tac >- simp[Abbr `t2`, mload_def] >> simp[mload_mstore_same]) >>
  conj_tac >- suspend "frame" >>
  conj_tac >- suspend "history" >> simp[Abbr `t2`, mstore_def]
QED

Resume concat_fixed_arm_mem[relation]:
  `stmt_state_rel ctx func cenv cx es (mstore a wd t)` by
    (irule literal_mstore_state_rel >> conj_tac
     >- (qexistsl_tac [`B`, `binst`, `bsz`] >> simp[Abbr `a`] >> metis_tac[]) >>
     first_assum ACCEPT_TAC) >>
  `!name lb lsz. local_region cenv es.scopes (mstore a wd t) name lb lsz <=>
      local_region cenv es.scopes t name lb lsz` by
    simp[local_region_def, lookup_var_def, mstore_def] >>
  `stmt_state_rel ctx func cenv cx es
    (mstore (w2n ow) (n2w (k + m)) (mstore a wd t))` by
    (irule literal_mstore_state_rel >> conj_tac
     >- (qexistsl_tac [`w2n ow`, `oinst`, `64`] >>
         simp[mstore_def] >> metis_tac[]) >>
     first_assum ACCEPT_TAC) >>
  qunabbrev_tac `t2` >>
  `!ss V n. ss with <|vs_vars := V; vs_inst_idx := n|> =
       (ss with vs_vars := V) with vs_inst_idx := n` by simp[] >>
  pop_assum (fn th => once_rewrite_tac[th]) >>
  rewrite_tac[stmt_state_rel_inst_idx] >>
  irule stmt_state_rel_vars_frame >> simp[] >> rpt strip_tac >>
  `not_fresh_at sx p` by
    (qpat_x_assum `local_ptrs_reserved _ _` mp_tac >>
     simp[local_ptrs_reserved_def] >> metis_tac[]) >>
  simp[lookup_var_def, mstore_def]
QED

Resume concat_fixed_arm_mem[payload]:
  qunabbrev_tac `t2` >> simp_tac (srw_ss()) [] >>
  qunabbrev_tac `wd` >> qunabbrev_tac `a` >>
  qpat_x_assum `LENGTH bs = m` (SUBST_ALL_TAC o SYM) >>
  irule concat_fixed_mem >> simp[]
QED

Resume concat_fixed_arm_mem[frame]:
  rpt gen_tac >> disch_tac >> qunabbrev_tac `t2` >>
  simp_tac (srw_ss()) [] >> irule EQ_TRANS >>
  qexists_tac `mem_bytes_at p n (mstore a wd t).vs_memory` >> conj_tac
  >- (irule mstore_mem_bytes_at_disjoint >> decide_tac) >>
  irule mstore_mem_bytes_at_disjoint >> qunabbrev_tac `a` >> decide_tac
QED

Resume concat_fixed_arm_mem[history]:
  `alloca_inv t` by fs[stmt_state_rel_def] >>
  `?rest. DROP t.vs_inst_idx bb.bb_instructions = emitted_insts sx s2 ++ rest` by
    fs[IS_PREFIX_APPEND] >>
  `EVERY (\i. ~is_terminator i.inst_opcode) (emitted_insts sx s2)` by
    (drule concat_fixed_shape >> simp[mk_inst_def, is_terminator_def]) >>
  drule_all alloca_history_run_inst_seq >>
  simp[Abbr `t2`, word_add_n2w]
QED

Finalise concat_fixed_arm_mem
