Theory bodyPtrMakeArrayAllocatedImmutable
Ancestors
  bodyPtrMakeArrayAllocatedOne bodyPtrMakeArrayImmutableResult bodyPtrMakeArrayImmutableCopy
  bodyPtrMakeArrayAllocCursor bodyPtrMakeArrayCopyStateFrame
  bodyPtrMakeArrayMaterialiseFrame bodyPtrDefs exprSimCopy exprSimStorageCopy
  ptrDiscipline fragGasPathPtr emitHelperProps emitHelper context compileEnv
  venomState finite_map pred_set words list valueEncodingProofs
  venomInstProps venomExecSemantics exprLoweringProps fragExec

Theorem literal_straight_run_current_bb:
  run_inst_seq code s = OK z /\
  EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode) code ==>
  z.vs_current_bb = s.vs_current_bb
Proof
  strip_tac >>
  irule (SRULE [] (Q.ISPEC `\s:venom_state. s.vs_current_bb` run_inst_seq_preserves_field)) >>
  qexists_tac `code` >> simp[] >> rpt strip_tac >>
  `i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode` by fs[EVERY_MEM] >>
  `step_inst 0 ARB i ss1 = OK ss2` by simp[step_inst_non_invoke] >>
  metis_tac[step_preserves_control_flow]
QED

Theorem allocated_immutable_runtime_endpoint:
  compile_alloc_buffer (type_memory_size tv) sa = (buf,sm) /\
  buf.buf_operand = Var dst /\
  compile_imm_copy_to_memory F imm src (Var dst) (type_slot_size tv) 0 sm = ((),sb) /\
  stmt_state_rel ctx func cenv cx es s /\ fn_inst_ids_distinct func /\
  local_ptrs_reserved cenv sa /\ type_memory_size tv < dimword(:256) /\
  MEM (mk_inst sa.cs_next_id ALLOCA [Lit (n2w (type_memory_size tv))]
    [STRING #"%" (toString sa.cs_next_var)]) (fn_insts func) /\
  ~ctx_has_dalloca ctx /\ ~s.vs_halted /\
  lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
  isPREFIX (emitted_insts sa sm) (DROP s.vs_inst_idx bb.bb_instructions) /\
  isPREFIX (emitted_insts sm sb) (DROP (SUC s.vs_inst_idx) bb.bb_instructions) /\
  s.vs_current_bb = sa.cs_current_bb /\ s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  copy_old_operand sa src /\ op_taint tn src = {} /\ eval_operand src s = SOME addr /\
  ~cenv.ce_is_ctor /\ immutable_holds cenv cx t (Value v) addr es s0 /\
  evaluate_type (get_tenv cx) t = SOME tv /\
  w2n addr + type_memory_size tv < dimword(:256) /\
  ghost_inv d cenv cx es G tn s /\
  (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) ==>
  ?z H tm b.
    gas_path_ptr D 0 ctx func PG G tn s 0 H tm (OK z) /\
    z.vs_current_bb = sb.cs_current_bb /\ z.vs_inst_idx = LENGTH sb.cs_current_insts /\
    stmt_state_rel ctx func cenv cx es z /\
    lookup_var dst z = SOME (n2w b) /\ ptr_covers H tm dst z (type_memory_size tv) /\
    val_wf tv v /\ val_footprint tv v <= type_memory_size tv /\
    (!m. mem_agree_outside tm.t_mem z.vs_memory m ==> val_in_memory tv v b m) /\
    ghost_inv d cenv cx es H tm z /\ ghost_kept cenv es sa G tn s H tm
Proof
  strip_tac >>
  drule_all (SRULE [] literal_alloc_buffer_cursor_run) >>
  disch_then (qspecl_then [`tn`, `PG`, `G`, `D`] strip_assume_tac) >>
  drule literal_alloc_buffer_cursor_shape >> strip_tac >>
  `eval_operand src a = SOME addr /\ op_taint tm src = {}` by
    (Cases_on `src` >> gvs[copy_old_operand_def, eval_operand_def,
       op_taint_def, lookup_var_def] >> metis_tac[]) >>
  `copy_old_operand sm src /\ copy_old_operand sm (Var dst)` by
    (gvs[copy_old_operand_def] >> metis_tac[]) >>
  `lookup_var dst a = SOME w /\ ptr_covers H tm dst a (type_memory_size tv) /\
    FLOOKUP H dst = SOME (w2n w,type_memory_size tv)` by
    (gvs[eval_operand_def] >> metis_tac[]) >>
  `w2n w + type_memory_size tv <= dimword(:256) /\ allocas_from 0 a` by
    simp[allocas_from_def] >>
  `lookup_block a.vs_current_bb func.fn_blocks = SOME bb /\
   isPREFIX (emitted_insts sm sb) (DROP a.vs_inst_idx bb.bb_instructions)` by fs[] >>
  drule_all immutable_runtime_buffer_ptr_path >>
  disch_then (qspecl_then [`PG`, `D`] strip_assume_tac) >>
  rename1 `copy_runtime_frame sm a sb raw` >>
  drule_all runtime_code_copy_memory_frame >> strip_tac >>
  suspend "post"
QED

Resume allocated_immutable_runtime_endpoint[post]:
  `copy_static raw = copy_static a /\
    (!x. not_fresh_at sm x ==> lookup_var x raw = lookup_var x a)` by
    fs[copy_runtime_frame_def] >>
  `stmt_state_rel ctx func cenv cx es raw` by
    (irule literal_copy_window_stmt_state_rel >>
     qexistsl_tac [`sa.cs_next_id`, `w2n w`, `type_memory_size tv`,
       `STRING #"%" (toString sa.cs_next_var)`, `sa`, `sm`, `a`] >>
     simp[IgnAsm `raw.vs_memory = _`] >> conj_tac >- metis_tac[] >>
     rpt strip_tac >> qpat_x_assum `!off len. _`
       (qspecl_then [`a'`, `len`] mp_tac) >> (impl_tac >- decide_tac) >> simp[]) >>
  `!x. not_fresh_at sa x ==> lookup_var x a = lookup_var x s` by metis_tac[] >>
  `!x. not_fresh_at sa x ==>
    lookup_var x raw = lookup_var x s /\ FLOOKUP Gf x = FLOOKUP G x /\
    op_taint tnf (Var x) = op_taint tn (Var x)` by
    (rpt strip_tac >>
     `not_fresh_at sm x` by metis_tac[] >>
     qpat_x_assum `!p. not_fresh_at sm p ==> _ /\ _ /\ _` (qspec_then `x` mp_tac) >>
     qpat_x_assum `!x. not_fresh_at sa x ==> _ /\ _ /\ _` (qspec_then `x` mp_tac) >>
     simp[op_prov_def]) >>
  `!i. i < w2n w \/ w2n w+type_memory_size tv <= i ==>
    mem_bytes_at i 1 raw.vs_memory = mem_bytes_at i 1 s.vs_memory /\
    (i IN tnf.t_mem <=> i IN tn.t_mem)` by
    (rpt strip_tac >>
     qpat_x_assum `!i. _ \/ _ ==> _ /\ _` (qspec_then `i` mp_tac) >>
     qpat_x_assum `!i. _ \/ _ ==> (_ IN tm.t_mem <=> _)` (qspec_then `i` mp_tac) >> simp[]) >>
  `raw.vs_call_ctx = s.vs_call_ctx /\ raw.vs_accounts = s.vs_accounts /\
   raw.vs_transient = s.vs_transient /\ tnf.t_stor = tn.t_stor /\
   tnf.t_trans = tn.t_trans /\ tnf.t_imm = tn.t_imm` by simp[] >>
  `ghost_inv d cenv cx es Gf tnf raw /\ ghost_kept cenv es sa G tn s Gf tnf` by
    (irule literal_allocated_copy_ghost_post >> simp[IgnAsm `raw.vs_memory = _`] >> conj_tac
     >- (qexistsl_tac [`w2n w`, `type_memory_size tv`, `a`] >>
         conj_tac >- first_assum ACCEPT_TAC >>
         conj_tac >- first_assum ACCEPT_TAC >>
         conj_tac >- (rpt strip_tac >>
           qpat_x_assum `!aid b len. _ /\ FLOOKUP s.vs_allocas aid = _ ==> _` irule >>
           qexists_tac `aid` >> simp[]) >> first_assum ACCEPT_TAC) >>
     qexistsl_tac [`ctx`, `func`] >> simp[]) >>
  suspend "cursor"
QED

Resume allocated_immutable_runtime_endpoint[cursor]:
  drule immutable_runtime_copy_opcodes >> strip_tac >>
  `run_inst_seq (emitted_insts sm sb) a = OK raw /\
   sb.cs_current_insts = sm.cs_current_insts ++ emitted_insts sm sb /\
   same_blocks sm sb` by fs[copy_runtime_frame_def] >>
  drule_all literal_straight_run_current_bb >> strip_tac >>
  `raw.vs_current_bb = sb.cs_current_bb /\
   a.vs_inst_idx + LENGTH (emitted_insts sm sb) = LENGTH sb.cs_current_insts` by
    fs[same_blocks_def] >>
  `ghost_inv d cenv cx es Gf tnf
    (raw with vs_inst_idx := a.vs_inst_idx + LENGTH (emitted_insts sm sb))` by
    (qpat_x_assum `ghost_inv d cenv cx es Gf tnf raw` mp_tac >>
     Cases_on `d`
     >- (simp[NoAsms, ghost_inv_def, stor_taint_ok_def, return_buf_ptr_def,
             ptr_covers_def, lookup_var_def] >> metis_tac[]) >>
     rename1 `ghost_inv (SOME cap) _ _ _ _ _ _` >> PairCases_on `cap` >>
     simp[NoAsms, ghost_inv_def, stor_taint_ok_def, return_buf_ptr_def,
          ptr_covers_def, lookup_var_def] >> metis_tac[]) >>
  `lookup_var dst raw = SOME w` by
    (gvs[copy_old_operand_def] >> metis_tac[]) >>
  qexistsl_tac [`raw with vs_inst_idx := a.vs_inst_idx + LENGTH (emitted_insts sm sb)`,
    `Gf`, `tnf`, `w2n w`] >>
  simp[IgnAsm `raw.vs_memory = _`, stmt_state_rel_inst_idx,
       lookup_var_def, ptr_covers_def] >>
  drule_all gas_path_ptr_then >> fs[lookup_var_def]
QED

Finalise allocated_immutable_runtime_endpoint
