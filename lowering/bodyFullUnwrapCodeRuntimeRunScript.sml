(* Joint runtime data-section copy boundary; raw and counted cursors differ. *)
Theory bodyFullUnwrapCodeRuntimeRun
Ancestors
  bodyFullUnwrapRun exprPtrCodeCopyInduction exprPtrCodeCopyIteration
  bodyImmutableCopyMemory exprSimCopy exprLoweringProps fragGasSeqPtr
  fragGasOriginPtr compileEnv context venomState venomInst entrySinkExtraction
  ptrDiscipline list rich_list exprPtrUnwrapAllocation fragExec fragExecMem
  exprPtrUnwrapAllocEntry exprPtrUnwrapAllocSeparation exprPtrUnwrapCodeCopyShape
  bufferAllocationExecution unitTransformDefs memSafeRun codegenRel contextCodegenRel allocationPtr venomMemDefs venomMemProofs exprSimStorageCopy loweringHalt loweringStateRelDefs
  loweringPosts finite_map allocaHistory exprPtrCodeCopyFrame freshWrites exprSimAlloc arithmetic

Theorem runtime_code_copy_range_origin:
  compile_imm_copy_to_memory F imm src (Var root) n off sa = ((),sb) /\
  copy_old_operand sa src /\ not_fresh_at sa root /\
  eval_operand src s = SOME a /\ lookup_var root s = SOME b /\
  op_taint tn src = {} /\ ptr_covers G tn root s capacity /\
  off + 32*n <= capacity /\ w2n b + capacity < dimword(:256) /\
  allocas_from lo s /\ (ctx_has_dalloca ctx ==> allocas_below_fmp s) /\
  w2n b + off + 32*n <= s.vs_alloca_next /\
  w2n a + off + 32*n <= LENGTH s.vs_data_section /\
  w2n a + off + 32*n < dimword(:256) /\
  fn_has_code sa sb func /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?Gf tnf t.
    copy_runtime_frame sa s sb t /\
    gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn) []
      (OK (t with vs_inst_idx := LENGTH sb.cs_current_insts),Gf,tnf) /\
    t.vs_current_bb = sb.cs_current_bb /\ ~t.vs_halted /\
    tnf.t_mem = tn.t_mem DIFF {j | w2n b+off <= j /\ j < w2n b+off+32*n} /\
    tnf.t_stor = tn.t_stor /\ tnf.t_trans = tn.t_trans /\ tnf.t_imm = tn.t_imm /\
    (!p. not_fresh_at sa p ==> FLOOKUP Gf p = FLOOKUP G p /\
      op_taint tnf (Var p) = op_taint tn (Var p)) /\
    allocas_from lo t /\ (ctx_has_dalloca ctx ==> allocas_below_fmp t) /\
    (!p sz. not_fresh_at sa p /\ ptr_covers G tn p s sz ==>
      ptr_covers Gf tnf p t sz)
Proof
  strip_tac >> drule_all code_copy_range_ptr >>
  disch_then (qspecl_then [`func`, `PG`, `D`] strip_assume_tac) >>
  `copy_old_operand sa (Var root)` by simp[copy_old_operand_def] >>
  `eval_operand (Var root) s = SOME b` by simp[eval_operand_def] >>
  `w2n b + off + 32*n < dimword(:256)` by decide_tac >>
  `run_inst_seq_mem_ok (emitted_insts sa sb) s` by
    (irule body_immutable_copy_mem_ok >> metis_tac[]) >>
  drule code_copy_insts >> strip_tac >>
  `EVERY (\i. i.inst_opcode <> INVOKE /\ i.inst_opcode <> GAS /\
               ~is_terminator i.inst_opcode) (emitted_insts sa sb)` by
    (fs[emitted_insts_def, DROP_APPEND, EVERY_MEM] >> rpt strip_tac >>
     first_x_assum drule >> strip_tac >> gvs[is_terminator_def]) >>
  `run_inst_seq (emitted_insts sa sb) s = OK t /\
   sb.cs_current_bb = sa.cs_current_bb /\
   sb.cs_current_insts = sa.cs_current_insts ++ emitted_insts sa sb` by
    fs[copy_runtime_frame_def, same_blocks_def] >>
  `t.vs_current_bb = sb.cs_current_bb /\ ~t.vs_halted` by
    (drule run_inst_seq_preserves_entry_control >>
     impl_tac >- fs[EVERY_MEM] >> simp[]) >>
  `inst_seq_ptr D lo ctx func PG G tn (emitted_insts sa sb) s Gf tnf` by
    (qpat_x_assum `!k. inst_seq_ptr _ _ _ _ _ _ _ _ _ _ _`
       (qspec_then `s.vs_inst_idx` mp_tac) >> simp[]) >>
  `gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn) []
     (OK (t with vs_inst_idx := LENGTH sb.cs_current_insts),Gf,tnf)` by
    (irule emitted_origin_ptr_path >> metis_tac[]) >>
  qexistsl [`Gf`, `tnf`, `t`] >> simp[]
QED

Theorem runtime_code_alloc_origin:
  compile_alloc_buffer nb sb = (buf,mid) /\ fn_has_code sb mid func /\
  allocas_from lo s /\ ~ctx_has_dalloca ctx /\ ~s.vs_halted /\
  s.vs_current_bb = sb.cs_current_bb /\
  s.vs_inst_idx = LENGTH sb.cs_current_insts /\ buf.buf_operand = Var root /\
  step_inst_base (mk_inst sb.cs_next_id ALLOCA [Lit (n2w nb)] [root]) s = OK u /\
  u.vs_requests = s.vs_requests ==>
  gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn) []
    (OK (u with vs_inst_idx := SUC s.vs_inst_idx),
     step_prov PG G (mk_inst sb.cs_next_id ALLOCA [Lit (n2w nb)] [root]) u,
     step_taint (mk_inst sb.cs_next_id ALLOCA [Lit (n2w nb)] [root]) s u tn)
Proof
  strip_tac >> drule unwrap_alloc_generated_code >> strip_tac >> fs[] >>
  drule unwrap_alloc_current_block >> strip_tac >>
  `LENGTH mid.cs_current_insts = SUC s.vs_inst_idx` by simp[] >>
  `ptr_inst_ok D lo 0 ctx func G tn
    (mk_inst sb.cs_next_id ALLOCA [Lit (n2w nb)] [root]) s` by
    (irule unwrap_alloc_ptr_check >> metis_tac[]) >>
  qsuff_tac `gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn) []
    (OK (u with vs_inst_idx := LENGTH mid.cs_current_insts),
     step_prov PG G (mk_inst sb.cs_next_id ALLOCA [Lit (n2w nb)] [root]) u,
     step_taint (mk_inst sb.cs_next_id ALLOCA [Lit (n2w nb)] [root]) s u tn)`
  >- simp[] >>
  irule emitted_origin_ptr_path >> conj_tac >- simp[] >>
  qexistsl [`[mk_inst sb.cs_next_id ALLOCA [Lit (n2w nb)] [root]]`, `sb`] >>
  simp[run_inst_seq_def, inst_seq_ptr_def, mk_inst_def, is_terminator_def,
    run_inst_seq_mem_ok_def, inst_mem_below_frontier_def, inst_dload_in_section_def,
    source_memory_read_ranges_def, source_memory_write_ranges_def]
QED

Theorem runtime_code_copy_origin_execution:
  compile_alloc_buffer nb sb = (buf,mid) /\
  compile_imm_copy_to_memory F imm src buf.buf_operand n 0 mid = ((),sc) /\
  fn_has_code sb mid func /\ fn_has_code mid sc func /\
  fn_inst_ids_distinct func /\ stmt_state_rel H ctx func cenv cx ee s /\
  nb = 32*n /\ nb < dimword(:256) /\ ~ctx_has_dalloca ctx /\
  ~s.vs_halted /\ s.vs_current_bb = sb.cs_current_bb /\
  s.vs_inst_idx = LENGTH sb.cs_current_insts /\
  alloca_history func s /\ allocas_from lo s /\ lo <= s.vs_alloca_next /\
  (!x. src = Var x ==> not_fresh_at sb x) /\
  eval_operand src s = SOME p /\ op_taint tn src = {} /\
  w2n p + 32*n <= LENGTH s.vs_data_section /\
  w2n p + 32*n < dimword(:256) ==>
  ?root u a Gm tm HG tf z d.
    buf.buf_operand = Var root /\
    u = update_var root (n2w (buffer_allocation_base s sb.cs_next_id))
      (buffer_allocation_fields s sb.cs_next_id nb) /\
    step_inst_base (mk_inst sb.cs_next_id ALLOCA [Lit (n2w nb)] [root]) s = OK u /\
    a = u with vs_inst_idx := SUC s.vs_inst_idx /\
    Gm = step_prov PG G (mk_inst sb.cs_next_id ALLOCA [Lit (n2w nb)] [root]) u /\
    tm = step_taint (mk_inst sb.cs_next_id ALLOCA [Lit (n2w nb)] [root]) s u tn /\
    (d:bytes32) = n2w (buffer_allocation_base s sb.cs_next_id) /\
    w2n d + nb < dimword(:256) /\ lookup_var root a = SOME d /\
    copy_runtime_frame mid a sc z /\
    gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn) []
      (OK (z with vs_inst_idx := LENGTH sc.cs_current_insts),HG,tf) /\
    z.vs_current_bb = sc.cs_current_bb /\ ~z.vs_halted /\
    ptr_covers HG tf root z nb /\
    tf.t_mem = tm.t_mem DIFF {j | w2n d <= j /\ j < w2n d+32*n} /\
    tf.t_stor = tm.t_stor /\ tf.t_trans = tm.t_trans /\ tf.t_imm = tm.t_imm /\
    (!x. not_fresh_at mid x ==> FLOOKUP HG x = FLOOKUP Gm x /\
       op_taint tf (Var x) = op_taint tm (Var x)) /\
    (!at len. at+len <= w2n d \/ w2n d+32*n <= at ==>
       mem_bytes_at at len z.vs_memory = mem_bytes_at at len a.vs_memory) /\
    alloca_history func (z with vs_inst_idx := LENGTH sc.cs_current_insts) /\
    s.vs_alloca_next <= z.vs_alloca_next /\ allocas_from lo z /\
    w2n d + nb <= z.vs_alloca_next /\
    (!x. not_fresh_at sb x ==> lookup_var x z = lookup_var x s /\
       FLOOKUP HG x = FLOOKUP G x /\ op_taint tf (Var x) = op_taint tn (Var x))
Proof
  strip_tac >> drule_all unwrap_alloc_entry >>
  disch_then (qspecl_then [`tn`, `PG`, `G`, `D`] strip_assume_tac) >>
  rename1 `buf.buf_operand = Var root` >>
  `!x. src = Var x ==> x <> root` by
    metis_tac[unwrap_alloc_old_operand_distinct] >>
  drule_all unwrap_alloc_old_operand_ghost >>
  disch_then (qspecl_then [`tn`, `SUC s.vs_inst_idx`, `PG`, `G`] mp_tac) >>
  simp[] >> strip_tac >>
  qabbrev_tac `d:bytes32 = n2w (buffer_allocation_base s sb.cs_next_id)` >>
  `w2n d+nb < dimword(:256)` by
    (drule_all unwrap_alloc_site_bound >> simp[Abbr `d`]) >>
  drule_all allocated_copy_operands_old >> strip_tac >>
  `eval_operand src a = SOME p /\ op_taint tnf src = {}` by
    simp[eval_operand_def] >>
  `lookup_var root a = SOME d` by
    (qpat_x_assum `eval_operand buf.buf_operand a = _` mp_tac >>
     simp[eval_operand_def]) >>
  `alloca_inv s` by fs[stmt_state_rel_def] >>
  `allocas_from lo a /\ ~a.vs_halted /\
   s.vs_alloca_next <= a.vs_alloca_next /\
   a.vs_data_section = s.vs_data_section /\ a.vs_requests = s.vs_requests` by
    (simp[buffer_allocation_fields_def, update_var_def] >>
     Cases_on `FLOOKUP s.vs_allocas sb.cs_next_id` >>
     fs[allocas_from_def, FLOOKUP_UPDATE] >> rpt strip_tac >>
     gvs[AllCaseEqs()] >> metis_tac[]) >>
  `w2n d + nb <= a.vs_alloca_next` by
    (drule_all buffer_alloc_code >> strip_tac >>
     Cases_on `FLOOKUP s.vs_allocas sb.cs_next_id`
     >- simp[Abbr `d`, buffer_allocation_base_def,
          buffer_allocation_fields_def, update_var_def, MOD_LESS_EQ] >>
     rename1 `FLOOKUP s.vs_allocas sb.cs_next_id = SOME site` >>
     PairCases_on `site` >>
     drule_all stmt_state_rel_alloca_site_bound >> strip_tac >>
     fs[alloca_inv_def, alloca_next_valid_def] >>
     simp[Abbr `d`, buffer_allocation_base_def,
       buffer_allocation_fields_def, update_var_def] >>
     qpat_x_assum `!aid base sz. _` (qspec_then `sb.cs_next_id` mp_tac) >> simp[]) >>
  `u.vs_requests = s.vs_requests` by
    (simp[buffer_allocation_fields_def, update_var_def] >>
     Cases_on `FLOOKUP s.vs_allocas sb.cs_next_id` >> simp[]) >>
  `gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn) [] (OK a,Gf,tnf)` by
    (drule_all runtime_code_alloc_origin >> simp[] >> metis_tac[]) >>
  qpat_assum `buf.buf_operand = Var root` (fn th =>
    qpat_x_assum `compile_imm_copy_to_memory _ _ _ _ _ _ _ = _`
      (assume_tac o REWRITE_RULE [th])) >>
  `0+32*n <= nb /\ w2n d+0+32*n <= a.vs_alloca_next /\
   w2n p+0+32*n <= LENGTH a.vs_data_section /\
   w2n p+0+32*n < dimword(:256) /\
   (ctx_has_dalloca ctx ==> allocas_below_fmp a)` by gvs[update_var_def] >>
  drule_all runtime_code_copy_range_origin >>
  disch_then (qspecl_then [`explicit`, `PG`, `D`] strip_assume_tac) >>
  `gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn) []
    (OK (t with vs_inst_idx := LENGTH sc.cs_current_insts),Gf',tnf')` by
    (qpat_assum `gas_origin_ptr_path _ (s,G,tn) [] _`
       (mp_tac o MATCH_MP gas_origin_ptr_path_append) >>
     disch_then (qspecl_then [`a`, `Gf`, `tnf`, `[]`] mp_tac) >>
     simp[] >> metis_tac[]) >>
  `copy_old_operand mid (Var root)` by (fs[copy_old_operand_def] >> metis_tac[]) >>
  `eval_operand (Var root) a = SOME d` by simp[eval_operand_def] >>
  `w2n d+32*n < dimword(:256)` by metis_tac[] >>
  `!at len. at+len <= w2n d \/ w2n d+32*n <= at ==>
     mem_bytes_at at len t.vs_memory = mem_bytes_at at len a.vs_memory` by
    (rpt gen_tac >> strip_tac >> irule code_copy_endpoint_exterior >> metis_tac[]) >>
  drule unwrap_alloc_generated_code >> strip_tac >>
  drule unwrap_alloc_current_block >> strip_tac >>
  `LENGTH mid.cs_current_insts = SUC s.vs_inst_idx` by simp[] >>
  `alloca_history func a` by
    (`alloca_history func (u with vs_inst_idx := LENGTH mid.cs_current_insts)` by
       (irule emitted_alloca_history >>
        conj_tac >- simp[] >>
        qexistsl [`[mk_inst sb.cs_next_id ALLOCA [Lit (n2w nb)] [root]]`, `s`, `sb`] >>
        simp[run_inst_seq_def, mk_inst_def, is_terminator_def] >> metis_tac[]) >>
     metis_tac[]) >>
  `alloca_inv a` by
    (`alloca_inv u` by metis_tac[history_base_alloca_inv] >>
     metis_tac[alloca_inv_set_inst_idx]) >>
  drule code_copy_insts >> strip_tac >>
  `EVERY (\i. ~is_terminator i.inst_opcode) (emitted_insts mid sc)` by
    (qpat_assum `sc.cs_current_insts = mid.cs_current_insts ++ _` (fn th =>
       pure_rewrite_tac[emitted_insts_def, th, DROP_LENGTH_APPEND]) >>
     fs[EVERY_MEM] >> rpt strip_tac >>
     qpat_x_assum `!i. MEM i _ ==> i.inst_opcode = ADD \/ _` drule >>
     strip_tac >> gvs[is_terminator_def]) >>
  `alloca_history func (t with vs_inst_idx := LENGTH sc.cs_current_insts)` by
    (irule emitted_alloca_history >>
     conj_tac >- simp[] >>
     qexistsl [`emitted_insts mid sc`, `a`, `mid`] >>
     fs[copy_runtime_frame_def, same_blocks_def]) >>
  `t.vs_alloca_next = a.vs_alloca_next` by
    (qpat_assum `copy_runtime_frame mid a sc t` mp_tac >>
     pure_rewrite_tac[copy_runtime_frame_def] >> strip_tac >> drule copy_static_fields >> simp[]) >>
  `!x. not_fresh_at sb x ==> not_fresh_at mid x /\ x <> root` by
    (drule compile_alloc_buffer_parts >> strip_tac >> metis_tac[]) >>
  `!x. not_fresh_at sb x ==> lookup_var x a = lookup_var x s /\
     FLOOKUP Gf x = FLOOKUP G x /\ op_taint tnf (Var x) = op_taint tn (Var x)` by
    (gen_tac >> disch_tac >>
     `!p. Var x = Var p ==> p <> root` by simp[] >>
     drule_all (Q.INST [`src` |-> `Var x`] unwrap_alloc_old_operand_ghost) >>
     disch_then (qspecl_then [`tn`, `SUC s.vs_inst_idx`, `PG`, `G`] mp_tac) >>
     simp[eval_operand_def, op_prov_def] >> metis_tac[]) >>
  qexistsl [`Gf'`, `tnf'`, `t`] >>
  gvs[Abbr `d`] >>
  conj_tac >- metis_tac[] >>
  fs[copy_runtime_frame_def] >> metis_tac[]
QED
