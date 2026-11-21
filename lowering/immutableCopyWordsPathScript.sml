(* A fixed-size constructor copy to a compiled, unprovenanced address. *)
Theory immutableCopyWordsPath
Ancestors
  bodyImmutableStoreMemory immutableDeployOperandTransfer immutableDeployAssignExecution
  immutableCopyExecution exprPtrCtorImmStore exprSimCopy
  varsExt freshWrites loweringStateRelDefs
  stmtReasonLitFragMemory ctorAbiActualObservations
  fragGasSeqPtr ptrSafeRun ptrDiscipline bodyPtrDefs
  contextCodegenRel codegenRel exprLoweringProps emitHelper
  context fragExecMem bodyLiteralBufferMemory
  oracleExecProps venomExecSemantics venomState venomInst compileEnv
  list rich_list arithmetic words finite_map

Theorem immutable_direct_step_operands[local]:
  MEM i.inst_opcode [ADD; MLOAD; ISTORE] /\ step_inst_base i s = OK u ==>
  eval_operands i.inst_operands s <> NONE /\
  LENGTH i.inst_operands = (if i.inst_opcode = MLOAD then 1 else 2)
Proof
  strip_tac >>
  qpat_x_assum `MEM _ _` mp_tac >> simp[] >> strip_tac
  >- (gvs[cj 1 venomExecSemanticsTheory.step_inst_base_opcode_eqs,
           venomExecSemanticsTheory.exec_pure2_def, AllCaseEqs()] >>
      simp[eval_operands_def])
  >- (gvs[cj 26 venomExecSemanticsTheory.step_inst_base_opcode_eqs,
           venomExecSemanticsTheory.exec_read1_def, AllCaseEqs()] >>
      simp[eval_operands_def])
  >> gvs[cj 36 venomExecSemanticsTheory.step_inst_base_opcode_eqs,
         AllCaseEqs()] >> simp[eval_operands_def]
QED

Theorem immutable_direct_step_ext[local]:
  MEM i.inst_opcode [ADD; MLOAD; ISTORE] /\
  step_inst_base i s = OK u /\ vars_ext s t ==>
  eval_operands i.inst_operands t = eval_operands i.inst_operands s /\
  ?v. step_inst_base i t = OK v /\ vars_ext u v
Proof
  strip_tac >>
  conj_tac
  >- (drule_all immutable_direct_step_operands >> strip_tac >>
      qpat_x_assum `varsExt$vars_ext s t` mp_tac >>
      pure_once_rewrite_tac[varsExtTheory.vars_ext_def] >> strip_tac >>
      qpat_assum `t = _` (fn th => ONCE_REWRITE_TAC[th]) >>
      irule varsExtTheory.eval_operands_vars_ext >> simp[]) >>
  `~is_terminator i.inst_opcode /\ i.inst_opcode <> INVOKE /\
   ~is_ext_call_op i.inst_opcode` by
    (qpat_x_assum `MEM _ _` mp_tac >> simp[] >> strip_tac >>
     simp[is_terminator_def, is_ext_call_op_def]) >>
  drule_all varsExtTheory.step_inst_base_vars_ext_state >>
  simp[varsExtTheory.vars_ext_result_def]
QED

Theorem immutable_direct_step_ranges[local]:
  MEM i.inst_opcode [ADD; MLOAD; ISTORE] /\
  step_inst_base i s = OK u /\ vars_ext s t ==>
  contextCodegenRel$source_memory_read_ranges i t =
    contextCodegenRel$source_memory_read_ranges i s /\
  codegenRel$source_memory_write_ranges i t =
    codegenRel$source_memory_write_ranges i s /\
  (!op. MEM op i.inst_operands ==> eval_operand op t = eval_operand op s)
Proof
  strip_tac >>
  drule_all immutable_direct_step_ext >> strip_tac >>
  drule_all immutable_direct_step_operands >> strip_tac >>
  qpat_x_assum `MEM _ _` mp_tac >> simp[] >> strip_tac
  >- ((gvs[LENGTH_EQ_NUM_compute] >>
      gvs[eval_operands_def, AllCaseEqs(),
          contextCodegenRelTheory.source_memory_read_ranges_def,
          codegenRelTheory.source_memory_write_ranges_def] >> (metis_tac[])))
  >- (gvs[LENGTH_EQ_NUM_compute] >>
      gvs[eval_operands_def, AllCaseEqs(),
          contextCodegenRelTheory.source_memory_read_ranges_def,
          codegenRelTheory.source_memory_write_ranges_def])
  >> gvs[LENGTH_EQ_NUM_compute] >>
  gvs[eval_operands_def, AllCaseEqs(),
      contextCodegenRelTheory.source_memory_read_ranges_def,
      codegenRelTheory.source_memory_write_ranges_def,
      codegenRelTheory.fixed_source_write_range_def] >> metis_tac[]
QED

Theorem immutable_direct_ptr_step[local]:
  MEM i.inst_opcode [ADD; MLOAD; ISTORE] /\
  step_inst_base i s = OK u /\ vars_ext s t /\
  ptr_inst_ok D lo 0 ctx fn G tn i s ==>
  ptr_inst_ok D lo 0 ctx fn G tn i t
Proof
  strip_tac >>
  drule_all immutable_direct_step_ranges >> strip_tac >>
  drule_all immutable_direct_step_ext >> strip_tac >>
  `i.inst_opcode <> INVOKE /\ i.inst_opcode <> CALL /\
   i.inst_opcode <> STATICCALL /\ i.inst_opcode <> CREATE /\
   i.inst_opcode <> CREATE2 /\ i.inst_opcode <> DELEGATECALL` by
    (qpat_x_assum `MEM _ _` mp_tac >> simp[] >> strip_tac >> simp[]) >>
  `v.vs_requests = t.vs_requests` by
    (drule_all oracleExecPropsTheory.step_inst_base_oracle >> simp[]) >>
  `t.vs_current_bb = s.vs_current_bb /\ t.vs_inst_idx = s.vs_inst_idx /\
   t.vs_allocas = s.vs_allocas /\ t.vs_initial_fmp = s.vs_initial_fmp /\
   t.vs_fmp = s.vs_fmp` by
    (qpat_x_assum `varsExt$vars_ext s t` mp_tac >>
     pure_once_rewrite_tac[varsExtTheory.vars_ext_def] >> strip_tac >>
     qpat_assum `t = _` (fn th => ONCE_REWRITE_TAC[th]) >> simp[]) >>
  qpat_x_assum `ptr_inst_ok _ _ _ _ _ _ _ _ _` mp_tac >>
  simp[ptrSafeRunTheory.ptr_inst_ok_def,
       venomExecSemanticsTheory.step_inst_non_invoke] >>
  qpat_x_assum `MEM _ _` mp_tac >> simp[] >> strip_tac >>
  simp[access_ok_def, taint_ok_def, about_to_revert_def,
       contextCodegenRelTheory.in_revert_forward_def,
       allocas_from_def, allocas_below_fmp_def] >>
  strip_tac >> fs[] >> metis_tac[]
QED

Theorem immutable_direct_step_ghosts[local]:
  MEM i.inst_opcode [ADD; MLOAD; ISTORE] /\
  step_inst_base i s = OK u /\ vars_ext s t /\ vars_ext u v ==>
  step_prov PG G i u = step_prov PG G i v /\
  step_taint i s u tn = step_taint i t v tn
Proof
  strip_tac >>
  drule_all immutable_direct_step_ranges >> strip_tac >>
  drule_all immutable_direct_step_operands >> strip_tac >>
  `new_site_bytes s u = new_site_bytes t v` by
    (qpat_x_assum `varsExt$vars_ext u v` mp_tac >>
     qpat_x_assum `varsExt$vars_ext s t` mp_tac >>
     pure_rewrite_tac[varsExtTheory.vars_ext_def] >>
     ntac 2 strip_tac >>
     qpat_assum `t = _` (fn th => ONCE_REWRITE_TAC[th]) >>
     qpat_assum `v = _` (fn th => ONCE_REWRITE_TAC[th]) >>
     simp[new_site_bytes_def]) >>
  qpat_x_assum `MEM _ _` mp_tac >> simp[] >> strip_tac >>
  gvs[LENGTH_EQ_NUM_compute] >>
  simp[step_prov_def, out_prov_def, step_taint_def,
       mem_taint_def, step_writes_def, written_taint_def, out_taint_def,
       store_taint_def, adopt_reset_def, imm_taint_def]
QED

Theorem immutable_direct_nonterminating[local]:
  EVERY (\i. MEM i.inst_opcode [ADD; MLOAD; ISTORE]) code ==>
  EVERY (\i. ~is_terminator i.inst_opcode) code
Proof
  simp[EVERY_MEM] >> strip_tac >> gen_tac >> disch_tac >>
  first_x_assum drule >> simp[] >> strip_tac >> simp[is_terminator_def]
QED

Theorem immutable_direct_sequence_ptr:
  !code s t G tn Gf tnf.
    EVERY (\i. MEM i.inst_opcode [ADD; MLOAD; ISTORE]) code /\
    vars_ext s t /\ (?u. run_inst_seq code s = OK u) /\
    inst_seq_ptr D lo ctx fn PG G tn code s Gf tnf ==>
    inst_seq_ptr D lo ctx fn PG G tn code t Gf tnf
Proof
  Induct >- simp[inst_seq_ptr_def] >>
  rpt gen_tac >> pure_rewrite_tac[EVERY_DEF, BETA_THM] >> strip_tac >>
  qpat_x_assum `run_inst_seq _ _ = OK _` mp_tac >>
  pure_rewrite_tac[exprLoweringPropsTheory.run_inst_seq_def] >>
  Cases_on `step_inst_base h s` >> simp[] >> strip_tac >>
  rename1 `step_inst_base h s = OK v` >>
  qpat_x_assum `(\i. _) h` (assume_tac o BETA_RULE) >>
  drule_all immutable_direct_step_ext >> strip_tac >>
  qpat_x_assum `inst_seq_ptr _ _ _ _ _ _ _ (_::_) _ _ _` mp_tac >>
  pure_rewrite_tac[inst_seq_ptr_def] >> asm_rewrite_tac[] >> strip_tac >>
  drule_all immutable_direct_ptr_step >> strip_tac >>
  drule_all immutable_direct_step_ghosts >> strip_tac >>
  simp[Once inst_seq_ptr_def] >>
  qpat_assum `EVERY _ code` (mp_tac o MATCH_MP immutable_direct_nonterminating) >>
  strip_tac >>
  `?u. run_inst_seq code (v with vs_inst_idx := SUC s.vs_inst_idx) = OK u` by
    simp[fragExecTheory.run_inst_seq_inst_idx, instIdxIndepTheory.exec_result_map_def] >>
  `s.vs_inst_idx = t.vs_inst_idx` by fs[varsExtTheory.vars_ext_def, venom_state_component_equality] >>
  qpat_x_assum `!s t G tn Gf tnf. _` irule >>
  conj_tac >- first_assum ACCEPT_TAC >>
  qexists `v with vs_inst_idx := SUC s.vs_inst_idx` >>
  qpat_x_assum `(case OK v of _ => _ | _ => _ | _ => _ | _ => _ | _ => _)`
    (assume_tac o SRULE []) >>
  qpat_x_assum `!tn PG G. _` (qspecl_then [`tn`, `PG`, `G`] strip_assume_tac) >>
  qpat_assum `step_prov _ _ _ v = _` (fn th => ONCE_REWRITE_TAC[GSYM th]) >>
  qpat_assum `step_taint _ s v _ = _` (fn th => ONCE_REWRITE_TAC[GSYM th]) >>
  `vars_ext (v with vs_inst_idx := SUC s.vs_inst_idx)
            (v' with vs_inst_idx := SUC s.vs_inst_idx)` by
    gvs[varsExtTheory.vars_ext_def, venom_state_component_equality] >>
  simp[]
  >> (gvs[])
QED

Theorem immutable_direct_words_mem_ok:
  !n off sa sb s.
    compile_imm_store_words imm src dst n off sa = ((),sb) /\
    (!x. src = Var x ==> not_fresh_at sa x) /\
    (!x. dst = Var x ==> not_fresh_at sa x) /\
    (!region x. imm = SOME region /\ region = Var x ==> not_fresh_at sa x) /\
    eval_operand src s = SOME a /\ eval_operand dst s = SOME b /\
    (!region. imm = SOME region ==> eval_operand region s = SOME 0w) /\
    w2n a + off + 32*n <= s.vs_alloca_next /\
    w2n b + off + 32*n <= s.vs_alloca_next /\
    w2n a + off + 32*n < dimword (:256) /\
    w2n b + off + 32*n < dimword (:256) ==>
    run_inst_seq_mem_ok (emitted_insts sa sb) s
Proof
  Induct >- simp[compile_imm_store_words_def, comp_return_def, emitted_insts_def,
                 run_inst_seq_mem_ok_def] >>
  rpt gen_tac >> simp[immutable_store_suc, comp_ignore_bind_def,
                       immutable_comp_bind_cases] >> strip_tac >>
  rename1 `immutable_store_one _ _ _ _ sa = (un,c1)` >> Cases_on `un` >>
  drule_all (SRULE [] immutable_store_one_old_execution) >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts sa c1) s = OK s1` >>
  `run_inst_seq_mem_ok (emitted_insts sa c1) s` by
    (irule bodyImmutableStoreMemoryTheory.immutable_direct_one_mem_ok >>
     qexistsl [`a`,`b`,`dst`,`imm`,`off`,`src`] >>
     fs[MULT_CLAUSES] >> decide_tac) >>
  `emitted_insts sa sb = emitted_insts sa c1 ++ emitted_insts c1 sb` by
    (drule immutableDeployAssignExecutionTheory.immutable_store_words_insts >> strip_tac >>
     irule emitted_insts_append >> simp[]) >>
  `s1.vs_alloca_next = s.vs_alloca_next /\ s1.vs_labels = s.vs_labels` by
    (qpat_x_assum `s1 with <|vs_memory := _; vs_vars := _; vs_immutables := _|> = s`
       mp_tac >> simp[venom_state_component_equality]) >>
  `eval_operand src s1 = SOME a /\ eval_operand dst s1 = SOME b /\
   (!region. imm = SOME region ==> eval_operand region s1 = SOME 0w)` by
    (conj_tac >- (irule ctor_actual_old_operand >> qexistsl [`s`,`sa`] >> simp[]) >>
     conj_tac >- (irule ctor_actual_old_operand >> qexistsl [`s`,`sa`] >> simp[]) >>
     rpt strip_tac >> irule ctor_actual_old_operand >>
     qexistsl [`s`,`sa`] >> simp[] >> metis_tac[]) >>
  qpat_assum `emitted_insts sa sb = _` SUBST1_TAC >>
  irule run_inst_seq_mem_ok_append_run >>
  conj_tac >- first_assum ACCEPT_TAC >>
  qexists `s1` >> conj_tac >- first_assum ACCEPT_TAC >>
  qpat_x_assum `!off sa sb s. _` irule >>
  fs[MULT_CLAUSES, not_fresh_at_def] >> qexists `off + 32` >> simp[]
QED

Theorem immutable_copy_words_path:
  compile_imm_store_words imm (Var root) dst n 0 sa = ((),sb) /\
  copy_old_operand sa dst /\ eval_operand dst s = SOME (n2w off) /\
  op_taint tn dst = {} /\ op_prov G dst = NONE /\
  not_fresh_at sa root /\ lookup_var root s = SOME (n2w a) /\
  ptr_covers G tn root s capacity /\
  32*n <= capacity /\ a+capacity < dimword (:256) /\
  off+32*n <= lo /\ lo <= a /\ lo <= s.vs_alloca_next /\
  a+32*n <= s.vs_alloca_next /\ lo < dimword (:256) /\ k <= 32*n /\
  (!base. imm = SOME base ==> eval_operand base s = SOME 0w /\
    copy_old_operand sa base /\ op_taint tn base = {} /\ op_prov G base = NONE) /\
  allocas_from lo s /\ (ctx_has_dalloca ctx ==> allocas_below_fmp s) /\
  fn_has_code sa sb func /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\ s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?u Gf tf.
    (!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG)
      (s,G,tn) [] (OK (u with vs_inst_idx := LENGTH sb.cs_current_insts),Gf,tf)) /\
    run_inst_seq (emitted_insts sa sb) s = OK u /\
    sb.cs_current_insts = sa.cs_current_insts ++ emitted_insts sa sb /\
    same_blocks sa sb /\ sa.cs_next_var <= sb.cs_next_var /\
    (u with <|vs_vars := s.vs_vars; vs_memory := s.vs_memory;
              vs_immutables := s.vs_immutables|>) = s /\
    LENGTH s.vs_memory <= LENGTH u.vs_memory /\
    mem_bytes_at off k u.vs_memory = mem_bytes_at a k s.vs_memory /\
    (!b len. b+len <= off \/ off+32*n <= b ==>
      mem_bytes_at b len u.vs_memory = mem_bytes_at b len s.vs_memory) /\
    u.vs_immutables = (immutable_transfers T T (n2w a) (n2w off) n 0 s).vs_immutables /\
    (!x. x IN tf.t_mem <=>
       if off <= x /\ x < off+32*n then a+(x-off) IN tn.t_mem else x IN tn.t_mem) /\
    tf.t_stor = tn.t_stor /\ tf.t_trans = tn.t_trans /\
    (!p. not_fresh_at sa p ==> lookup_var p u = lookup_var p s /\
      FLOOKUP Gf p = FLOOKUP G p /\ op_taint tf (Var p) = op_taint tn (Var p)) /\
    EVERY (\i. MEM i.inst_opcode [ADD; MLOAD; ISTORE]) (emitted_insts sa sb)
Proof
  strip_tac >>
  `a+k < dimword (:256) /\ off+32*n < dimword (:256) /\ off+32*n <= a` by
    decide_tac >>
  `eval_operand (Var root) s = SOME (n2w a)` by simp[eval_operand_def] >>
  `!x. dst = Var x ==> not_fresh_at sa x` by fs[copy_old_operand_def] >>
  `!base x. imm = SOME base /\ base = Var x ==> not_fresh_at sa x` by
    (rpt strip_tac >> gvs[copy_old_operand_def] >> metis_tac[]) >>
  `!base. imm = SOME base ==> eval_operand base s = SOME 0w` by metis_tac[] >>
  mp_tac (Q.INST [`src` |-> `Var root`, `b` |-> `off`]
    immutable_words_old_prefix_path) >>
  (impl_tac >- simp[]) >> strip_tac >>
  `LENGTH s.vs_memory <= LENGTH u.vs_memory` by
    (drule exprLoweringPropsTheory.run_inst_seq_memory_length >> simp[]) >>
  `w2n (n2w a : bytes32) = a /\ w2n (n2w off : bytes32) = off` by
    (simp[w2n_n2w,LESS_MOD] >> decide_tac) >>
  `lookup_var root (drop_fresh sa s) = SOME (n2w a) /\
   ptr_covers G tn root (drop_fresh sa s) capacity` by
    gvs[varsExtTheory.lookup_var_drop_fresh,ptr_covers_def] >>
  `eval_operand dst (drop_fresh sa s) = SOME (n2w off)` by
    (drule freshWritesTheory.eval_operand_drop_fresh >> simp[]) >>
  `!base. imm = SOME base ==> eval_operand base (drop_fresh sa s) = SOME 0w /\
    copy_old_operand sa base /\ op_taint tn base = {} /\ op_prov G base = NONE` by
    (qx_gen_tac `imm_op:operand` >> strip_tac >>
     qpat_assum `!r. imm = SOME r ==> eval_operand r s = _ /\ _`
       (qspecl_then [`imm_op`] (drule_then strip_assume_tac)) >>
     simp[] >>
     qspecl_then [`imm_op`,`sa`,`s`] mp_tac freshWritesTheory.eval_operand_drop_fresh >>
     fs[copy_old_operand_def]) >>
  `allocas_from lo (drop_fresh sa s) /\
   (ctx_has_dalloca ctx ==> allocas_below_fmp (drop_fresh sa s))` by
    (qpat_assum `allocas_from lo s` mp_tac >>
     qpat_assum `ctx_has_dalloca ctx ==> allocas_below_fmp s` mp_tac >>
     simp_tac bool_ss [varsExtTheory.drop_fresh_def,allocas_from_def,
                       allocas_below_fmp_def,venom_state_accfupds] >> metis_tac[]) >>
  `fresh_vars_wrt sa (drop_fresh sa s)` by simp[varsExtTheory.fresh_vars_wrt_drop_fresh] >>
  `!D. ?Gf tf.
     inst_seq_ptr D lo ctx func PG G tn (emitted_insts sa sb) s Gf tf /\
     EVERY (\i. MEM i.inst_opcode [ADD; MLOAD; ISTORE]) (emitted_insts sa sb) /\
     (!x. x IN tf.t_mem <=>
        if off <= x /\ x < off+32*n then a+(x-off) IN tn.t_mem else x IN tn.t_mem) /\
     tf.t_stor = tn.t_stor /\ tf.t_trans = tn.t_trans /\
     (!p. not_fresh_at sa p ==> FLOOKUP Gf p = FLOOKUP G p /\
          op_taint tf (Var p) = op_taint tn (Var p))` by suspend "ghosts" >>
  qpat_assum `!D. ?Gf tf. _` (qspec_then `ARB:dead` strip_assume_tac) >>
  `!D. inst_seq_ptr D lo ctx func PG G tn (emitted_insts sa sb) s Gf tf` by
    (gen_tac >> qpat_assum `!D. ?Gf tf. _` (qspec_then `D` strip_assume_tac) >>
     `Gf' = Gf /\ tf' = tf` by
       (MATCH_MP_TAC (Q.INST [`D1` |-> `D`,`D2` |-> `ARB:dead`,
         `lo` |-> `lo`,`ctx` |-> `ctx`,`fn` |-> `func`,`PG` |-> `PG`]
         (Q.SPECL [`emitted_insts sa sb`,`s`,`G`,`tn`,`Gf'`,`tf'`,`Gf`,`tf`]
          inst_seq_ptr_ghost_unique)) >> simp[]) >>
     gvs[]) >>
  `run_inst_seq_mem_ok (emitted_insts sa sb) s` by
    (irule immutable_direct_words_mem_ok >>
     qexistsl [`n2w a`,`n2w off`,`dst`,`imm`,`n`,`0`,`Var root`] >>
     simp[] >> decide_tac) >>
  `sb.cs_current_bb = sa.cs_current_bb` by fs[same_blocks_def] >>
  drule_all stmtReasonLitFragMemoryTheory.fn_has_code_code >> strip_tac >>
  `EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
           (emitted_insts sa sb) /\
   FILTER (\i. i.inst_opcode = GAS) (emitted_insts sa sb) = []` by
    (fs[FILTER_EQ_NIL,EVERY_MEM] >> rpt strip_tac >>
     qpat_assum `!i. MEM i (emitted_insts sa sb) ==> i.inst_opcode = ADD \/ _`
       (drule_then strip_assume_tac) >>
     gvs[is_terminator_def]) >>
  qexistsl [`u`,`Gf`,`tf`] >> simp[] >>
  reverse conj_tac
  >- metis_tac[ADD_COMM] >>
  gen_tac >>
  qpat_assum `!D. inst_seq_ptr D lo ctx func PG G tn _ _ _ _`
    (qspec_then `D` assume_tac) >>
  mp_tac (Q.INST [`D` |-> `D`,`lo` |-> `lo`,`PG` |-> `PG`,
     `explicit` |-> `explicit`]
    (Q.SPECL [`emitted_insts sa sb`,`s`,`u`,`G`,`tn`,`Gf`,`tf`,`ctx`,`func`,`bb`]
      run_inst_seq_gas_origin_ptr_path)) >>
  simp[]
QED

Resume immutable_copy_words_path[ghosts]:
  gen_tac >>
  `w2n (n2w off : bytes32) + 0 + 32*n <= lo /\
   lo <= w2n (n2w a : bytes32) /\ 0+32*n <= capacity /\
   w2n (n2w a : bytes32) + capacity < dimword (:256)` by simp[] >>
  drule_all code_ctor_store_range_ptr >>
  disch_then (strip_assume_tac o Q.INST [`fn` |-> `func`] o SPEC_ALL) >>
  qexistsl [`Gf`,`tnf`] >> simp[] >>
  irule immutable_direct_sequence_ptr >>
  conj_tac >- first_assum ACCEPT_TAC >>
  qexists_tac `drop_fresh sa s` >> simp[varsExtTheory.vars_ext_drop_fresh] >>
  conj_tac >- fs[immutable_execution_frame_def] >>
  `(drop_fresh sa s with vs_inst_idx := (drop_fresh sa s).vs_inst_idx) =
    drop_fresh sa s` by simp[venom_state_component_equality] >>
  qpat_assum `!pc. inst_seq_ptr _ _ _ _ _ _ _ _ _ _ _`
    (qspec_then `(drop_fresh sa s).vs_inst_idx` mp_tac) >>
  pop_assum (fn th => rewrite_tac[th])
QED

Finalise immutable_copy_words_path
