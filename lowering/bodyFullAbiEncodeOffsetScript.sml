(* Owned-pointer ADD: one physical step and ghosts, uniform in the horizon. *)
Theory bodyFullAbiEncodeOffset
Ancestors
  fragGasOriginPtrLoop bodyPtrMakeArrayEmission typedCopyPtr
  bodyPtrBytestringBuiltinsAllocation bodyPtrDefs allocationPtr
  localPtrsProps ghostPcTransportPtr abiAllocationHistory
  ptrSafeRun instMemFrontier venomInstProofs compileEnv
  instIdxIndep arithmetic finite_map pred_set words venomState venomInst
  venomExecSemantics ptrDiscipline ptrSafetyTransport emitHelper loweringStateRelDefs exprSimProps

Theorem abi_encode_owned_offset_origin:
  !a b dst root off s base G tn total n lo explicit ctx func PG.
    emit_op ADD [Var root;Lit (n2w off)] a = (dst,b) /\
    fn_has_code a b func /\ ~ctx_has_dalloca ctx /\
    ~s.vs_halted /\ s.vs_current_bb = a.cs_current_bb /\
    s.vs_inst_idx = LENGTH a.cs_current_insts /\ allocas_from lo s /\
    lookup_var root s = SOME base /\ ptr_covers G tn root s total /\
    off+n <= total /\ w2n base+off < dimword(:256) ==>
    ?q t G' tn'. dst = Var q /\
      t = (update_var q (base+n2w off) s with vs_inst_idx := SUC s.vs_inst_idx) /\
      lookup_var q t = SOME (n2w (w2n base+off)) /\
      ptr_covers G' tn' q t n /\
      (!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG)
        (s,G,tn) [] (OK t,G',tn')) /\
      ~t.vs_halted /\ t.vs_current_bb = b.cs_current_bb /\
      t.vs_inst_idx = LENGTH b.cs_current_insts /\ not_fresh_at b q /\
      t.vs_memory = s.vs_memory /\ t.vs_allocas = s.vs_allocas /\
      t.vs_alloca_next = s.vs_alloca_next /\
      (!code. abi_alloca_history code s ==> abi_alloca_history code t) /\
      tn'.t_mem = tn.t_mem /\ tn'.t_stor = tn.t_stor /\
      tn'.t_trans = tn.t_trans /\ tn'.t_imm = tn.t_imm /\
      (!x. x <> q ==> lookup_var x t = lookup_var x s /\
        FLOOKUP G' x = FLOOKUP G x /\
        op_taint tn' (Var x) = op_taint tn (Var x)) /\
      (!op. (!x. op = Var x ==> not_fresh_at a x) ==>
        eval_operand op t = eval_operand op s /\
        op_taint tn' op = op_taint tn op /\ op_prov G' op = op_prov G op) /\
      (!D d ce cx es.
        ghost_inv_at D lo d ce cx es G tn s /\
        (!name x sz. FLOOKUP ce.ce_vars name = SOME (PtrVar (Var x) sz) ==> x <> q) /\
        (!x sz. ce.ce_return_buf = SOME (PtrVar (Var x) sz) ==> x <> q) /\
        (!x sz. ce.ce_return_pc = SOME (PtrVar (Var x) sz) ==> x <> q) /\
        (!x. lo <> 0 /\ ce.ce_imm_alloca = SOME (Var x) ==> x <> q) ==>
        ghost_inv_at D lo d ce cx es G' tn' t) /\
      (!ce es origin G0 tn0 s0.
        ghost_kept_at lo ce es origin G0 tn0 s0 G tn /\
        (!x. not_fresh_at origin x ==> x <> q) ==>
        ghost_kept_at lo ce es origin G0 tn0 s0 G' tn')
Proof
  rpt gen_tac >> strip_tac >>
  drule_all emit_op_fetch_boundary >> strip_tac >>
  rename1 `dst = Var q` >>
  rename1 `lookup_var root s = SOME w` >>
  qabbrev_tac `i = mk_inst a.cs_next_id ADD [Var root;Lit (n2w off)] [q]` >>
  qabbrev_tac `u = update_var q (w+n2w off) s` >>
  qexistsl_tac [`q`, `u with vs_inst_idx := SUC s.vs_inst_idx`,
    `step_prov PG G i u`, `step_taint i s u tn`] >>
  simp[] >> suspend "post"
QED

Resume abi_encode_owned_offset_origin[post]:
  `lookup_var q (u with vs_inst_idx := SUC s.vs_inst_idx) =
    SOME (n2w (w2n w+off))` by
    simp[Abbr `u`, lookup_var_def, update_var_def, GSYM word_add_n2w, FLOOKUP_UPDATE] >>
  `ptr_covers (step_prov PG G i u) (step_taint i s u tn) q
    (u with vs_inst_idx := SUC s.vs_inst_idx) n` by
    (simp[Abbr `i`, Abbr `u`] >> irule (SRULE [] pointer_offset_covers) >>
     simp[eval_operand_def, op_taint_def] >> metis_tac[ADD_COMM]) >>
  `!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn) []
    (OK (u with vs_inst_idx := SUC s.vs_inst_idx),
      step_prov PG G i u, step_taint i s u tn)` by suspend "path" >>
  simp[] >> suspend "frame"
QED

Resume abi_encode_owned_offset_origin[path]:
  gen_tac >>
  `step_inst 0 ctx i s = OK u` by
    simp[Abbr `i`, Abbr `u`, step_inst_non_invoke, mk_inst_def,
      step_inst_base_opcode_eqs, exec_pure2_def, eval_operand_def] >>
  `ptr_safe_step D lo 0 ctx func PG G tn i s` by suspend "safe" >>
  irule step_origin_ptr_path >> simp[] >> qexists_tac `i` >>
  simp[ghost_step_def, Abbr `i`, mk_inst_def, is_terminator_def,
    unitTransformDefsTheory.inst_mem_below_frontier_def,
    memSafeRunTheory.inst_dload_in_section_def,
    contextCodegenRelTheory.source_memory_read_ranges_def,
    codegenRelTheory.source_memory_write_ranges_def] >>
  gvs[mk_inst_def]
QED

Resume abi_encode_owned_offset_origin[safe]:
  simp[ptr_safe_step_def, Abbr `i`, mk_inst_def] >>
  irule ptr_inst_ok_lower_bound_transport >> simp[] >>
  qexists_tac `0` >> simp[] >> irule (SRULE [mk_inst_def] ptr_inst_ok_copy_len_binop) >>
  gvs[ptr_covers_def, op_taint_def]
QED

Resume abi_encode_owned_offset_origin[frame]:
  `!x. x <> q ==> FLOOKUP (step_prov PG G i u) x = FLOOKUP G x /\
    op_taint (step_taint i s u tn) (Var x) = op_taint tn (Var x)` by
    simp[Abbr `i`, Abbr `u`, copy_len_binop_ghost_frame] >>
  `!x. x <> q ==> lookup_var x (u with vs_inst_idx := SUC s.vs_inst_idx) =
    lookup_var x s` by
    simp[Abbr `u`, lookup_var_def, update_var_def, FLOOKUP_UPDATE] >>
  `not_fresh_at b q` by
    (gvs[emit_op_def, fresh_var_def, comp_bind_def, comp_ignore_bind_def,
      comp_return_def, fresh_id_def, emit_def, not_fresh_at_def]) >>
  `~u.vs_halted /\ u.vs_current_bb = b.cs_current_bb /\
    u.vs_memory = s.vs_memory /\ u.vs_allocas = s.vs_allocas /\
    u.vs_alloca_next = s.vs_alloca_next /\
    (!code. abi_alloca_history code s ==>
      abi_alloca_history code (u with vs_inst_idx := SUC s.vs_inst_idx))` by
    simp[Abbr `u`, update_var_def, abi_alloca_history_def] >>
  ` (step_taint i s u tn).t_mem = tn.t_mem /\
    (step_taint i s u tn).t_stor = tn.t_stor /\
    (step_taint i s u tn).t_trans = tn.t_trans /\
    (step_taint i s u tn).t_imm = tn.t_imm` by
    simp[Abbr `i`, Abbr `u`, copy_len_binop_ghost_frame,
      step_taint_def, mk_inst_def, imm_taint_def, step_writes_def, update_var_def] >>
  gvs[] >> conj_tac >- suspend "operands" >>
  conj_tac >- suspend "inv" >>
  simp[ghost_kept_at_def] >> metis_tac[]
QED

Resume abi_encode_owned_offset_origin[operands]:
  gen_tac >> Cases_on `op` >>
  simp[eval_operand_def, op_prov_def, op_taint_def, Abbr `u`, update_var_def] >>
  strip_tac >> rename1 `not_fresh_at a v` >>
  `v <> STRING #"%" (toString a.cs_next_var)` by metis_tac[] >>
  gvs[lookup_var_def, FLOOKUP_UPDATE, update_var_def, op_taint_def]
QED

Resume abi_encode_owned_offset_origin[inv]:
  rpt gen_tac >> strip_tac >>
  `!p sz. p <> STRING #"%" (toString a.cs_next_var) /\
    ptr_covers G tn p s sz ==>
    ptr_covers (step_prov PG G i u) (step_taint i s u tn) p
      (u with vs_inst_idx := LENGTH b.cs_current_insts) sz` by
    (gvs[ptr_covers_def, lookup_var_def] >> metis_tac[]) >>
  qpat_x_assum `ghost_inv_at _ _ _ _ _ _ _ _ _` mp_tac >>
  rewrite_tac[ghost_inv_at_def] >> strip_tac >>
  rewrite_tac[ghost_inv_at_def] >> conj_tac
  >- (rpt gen_tac >> strip_tac >>
      `p <> STRING #"%" (toString a.cs_next_var)` by metis_tac[] >>
      conj_tac >- metis_tac[] >>
      rpt gen_tac >> strip_tac >>
      `lookup_var p s = SOME w'` by metis_tac[lookup_var_def] >>
      first_x_assum drule_all >> gvs[]) >>
  conj_tac
  >- (Cases_on `d` >> simp[return_buf_ptr_def] >> PairCases_on `x` >>
      fs[return_buf_ptr_def] >> metis_tac[lookup_var_def]) >>
  conj_tac >- metis_tac[] >>
  conj_tac >- gvs[stor_taint_ok_at_def, Abbr `u`, update_var_def] >>
  conj_tac >- (rpt strip_tac >> gvs[] >> metis_tac[lookup_var_def]) >>
  conj_tac >- metis_tac[] >>
  gvs[Abbr `u`, update_var_def, allocas_from_def] >> metis_tac[]
QED

Finalise abi_encode_owned_offset_origin
