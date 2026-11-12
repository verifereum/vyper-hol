Theory bodyPtrMakeArrayAllocatedImmutable
Ancestors
  bodyPtrMakeArrayAllocatedOne bodyPtrMakeArrayImmutableResult bodyPtrMakeArrayImmutableCopy
  bodyPtrMakeArrayAllocCursor bodyPtrMakeArrayCopyStateFrame bodyPtrMakeArrayExternalPost bodyPtrMakeArrayBufferPost
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

Theorem allocated_immutable_runtime_endpoint_frame:
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
    ghost_inv d cenv cx es H tm z /\ ghost_kept cenv es sa G tn s H tm /\
    (!x. not_fresh_at sa x ==> lookup_var x z = lookup_var x s) /\
    (!esi si e raw vv base.
      post_value_type cenv e = expr_type e /\
      vv_post ctx func cenv cx e esi si sa base es raw vv s /\
      read_result cx raw es = (INL v,es) /\
      MAP FDOM esi.scopes = MAP FDOM es.scopes /\
      local_ptrs_reserved cenv si /\
      si.cs_next_var <= sa.cs_next_var /\ si.cs_next_id <= sa.cs_next_id /\
      ~is_word_type (expr_type e) /\
      evaluate_type (get_tenv cx) (expr_type e) = SOME tv ==>
      expr_post ctx func cenv cx e esi si sb base es v (Var dst) z /\
      (type_memory_bytes cenv (lowered_value_type cenv e) <= type_memory_size tv ==>
       ptr_val_ok cx (expr_type e) v (Var dst) H tm z /\
       ptr_buf_ok cenv e (Var dst) H z))
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

Resume allocated_immutable_runtime_endpoint_frame[post]:
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

Resume allocated_immutable_runtime_endpoint_frame[cursor]:
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
  conj_tac >- (drule_all gas_path_ptr_then >> fs[lookup_var_def]) >>
  fs[lookup_var_def] >> suspend "semantic"
QED

Resume allocated_immutable_runtime_endpoint_frame[semantic]:
  rpt gen_tac >> strip_tac >>
  reverse conj_tac >-
    (strip_tac >>
     qmatch_goalsub_abbrev_tac `ptr_buf_ok _ _ _ _ z` >>
     `lookup_var dst z = SOME w /\ ptr_covers Gf tnf dst z (type_memory_size tv) /\
       (!m. mem_agree_outside tnf.t_mem z.vs_memory m ==> val_in_memory tv v (w2n w) m)` by
       (fs[Abbr `z`, lookup_var_def, ptr_covers_def] >> metis_tac[]) >>
     qspec_then `type_memory_size tv` assume_tac arithmeticTheory.LESS_EQ_REFL >>
     drule_all literal_buffer_pointer_post >> simp[]) >>
  `val_in_memory tv v (w2n w) raw.vs_memory` by
    (first_x_assum irule >> simp[mem_agree_outside_def]) >>
  `ci_mono sa sm` by
    (qspecl_then [`type_memory_size tv`, `sa`] mp_tac ci_mono_compile_alloc_buffer >> simp[]) >>
  `ci_mono sm sb` by
    (qspecl_then [`type_slot_size tv`, `F`, `imm`, `src`, `Var dst`, `0`, `sm`]
       mp_tac ci_mono_compile_imm_copy_to_memory >> simp[]) >>
  `sa.cs_next_var <= sm.cs_next_var /\ sm.cs_next_var <= sb.cs_next_var /\
    sm.cs_next_id <= sb.cs_next_id` by fs[ci_mono_def] >>
  `sa.cs_next_id < sb.cs_next_id` by decide_tac >>
  qmatch_goalsub_abbrev_tac `expr_post _ _ _ _ _ _ _ _ _ _ _ _ z` >>
  `copy_static z = copy_static a /\
    (!x. not_fresh_at sm x ==> lookup_var x z = lookup_var x a) /\
    LENGTH a.vs_memory <= LENGTH z.vs_memory /\
    (!off len. off + len <= w2n w \/ w2n w + type_memory_size tv <= off ==>
      mem_bytes_at off len z.vs_memory = mem_bytes_at off len a.vs_memory) /\
    val_in_memory tv v (w2n w) z.vs_memory /\ eval_operand (Var dst) z = SOME w` by
    (fs[Abbr `z`, copy_static_def, lookup_var_def, eval_operand_def,
       IgnAsm `raw.vs_memory = _`] >> metis_tac[]) >>
  `!x. not_fresh_at sa x ==> lookup_var x a = lookup_var x s` by
    fs[lookup_var_def] >>
  `?inst. MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\
    inst.inst_id = sa.cs_next_id` by
    (qexists_tac `mk_inst sa.cs_next_id ALLOCA [Lit (n2w (type_memory_size tv))]
       [STRING #"%" (toString sa.cs_next_var)]` >> simp[venomInstTheory.mk_inst_def]) >>
  drule_all copy_buffer_read_post_transport >> simp[]
QED

Finalise allocated_immutable_runtime_endpoint_frame

(* The execution-only API remains a projection of the strengthened endpoint. *)
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
  strip_tac >> drule_all allocated_immutable_runtime_endpoint_frame >> metis_tac[]
QED
