(* Covered local-field address formation followed by a clean counted load. *)
Theory augAssignPtrFieldLoad
Ancestors
  augAssignPtrLoad typedCopyLoopHeaderPtr ptrCoverage structChildPtr
  fragGasSeqPtr fragGasPathPtr bodyPtrDefs venomInst venomState
  venomExecSemantics ptrSafeRun ptrDiscipline typedCopyPtr
  emitHelperProps emitHelper compileEnv loweringStateRelDefs fragExec loweringPosts
  exprLoweringProps codegenRel contextCodegenRel finite_map words
  exprSimFieldLayout representationCleanPtr valueEncodingProps stmtSimAugAssignAttr
  loweringSlice stmtFragPtr exprSimProps accountsRelProps valueEncoding

Theorem ptr_inst_ok_add_literal:
  op_taint tn (Var src) = {} /\ ~ctx_has_dalloca ctx /\
  lookup_var src s = SOME a ==>
  ptr_inst_ok D 0 fuel ctx fn G tn (mk_inst id ADD [Var src; Lit off] [out]) s
Proof
  strip_tac >>
  simp[ptr_inst_ok_def, access_ok_def, taint_ok_def, allocas_from_def,
       mk_inst_def, source_memory_read_ranges_def, source_memory_write_ranges_def,
       op_taint_def, step_inst_non_invoke] >>
  asm_simp_tac bool_ss [step_inst_base_opcode_eqs, instruction_accessors, instruction_accfupds,
                   combinTheory.K_THM, opcode_case_def] >>
  gvs[exec_pure2_def, eval_operand_def, update_var_def, op_taint_def] >>
  gen_tac >> Cases_on `op` >> gvs[] >> metis_tac[]
QED

Theorem add_literal_path_ptr:
  ~s.vs_halted /\ ~ctx_has_dalloca ctx /\ op_taint tn (Var src) = {} /\
  lookup_var src s = SOME a /\
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  get_instruction bb s.vs_inst_idx = SOME (mk_inst id ADD [Var src; Lit off] [out]) ==>
  gas_path_ptr D 0 ctx fn PG G tn s 0
    (step_prov PG G (mk_inst id ADD [Var src; Lit off] [out]) (update_var out (a + off) s))
    (step_taint (mk_inst id ADD [Var src; Lit off] [out]) s (update_var out (a + off) s) tn)
    (OK ((update_var out (a + off) s) with vs_inst_idx := SUC s.vs_inst_idx))
Proof
  strip_tac >>
  `ptr_inst_ok D 0 0 ctx fn G tn (mk_inst id ADD [Var src; Lit off] [out]) s` by
    (irule ptr_inst_ok_add_literal >> simp[]) >>
  `step_inst_base (mk_inst id ADD [Var src; Lit off] [out]) s =
    OK (update_var out (a + off) s)` by
    simp[step_inst_base_opcode_eqs, mk_inst_def, exec_pure2_def, eval_operand_def] >>
  mp_tac (Q.INST [`lo` |-> `0`, `u` |-> `update_var out (a + off) s`,
    `i` |-> `mk_inst id ADD [Var src; Lit off] [out]`] straight_line_ptr_edge) >>
  gvs[mk_inst_def, is_terminator_def] >> strip_tac >>
  drule (cj 2 gas_path_ptr_rules) >> simp[] >>
  disch_then irule >> irule (cj 1 gas_path_ptr_rules) >> simp[update_var_def]
QED

Theorem add_literal_imm_frame:
  (step_taint (mk_inst id ADD [Var src; Lit off] [out]) s
    (update_var out v s) tn).t_imm = tn.t_imm
Proof
  `new_site_bytes s (update_var out v s) = {}` by
    simp[new_site_bytes_def, update_var_def, FLOOKUP_DEF,
         pred_setTheory.EXTENSION, SF CONJ_ss] >>
  simp[step_taint_def, imm_taint_def, adopt_reset_def, set_var_taint_def,
       mk_inst_def]
QED

Theorem emit_add_literal_path_ptr:
  emit_op ADD [Var src; Lit (n2w off)] sa = (Var out,sb) /\
  fn_has_code sa sb fn /\ ~ctx_has_dalloca ctx /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\ not_fresh_at sa src /\
  ptr_covers G tn src s span /\ lookup_var src s = SOME a /\
  off < span /\ off + n <= span /\ w2n a + off < dimword (:256) ==>
  ?Gf tnf sf.
    gas_path_ptr D 0 ctx fn PG G tn s 0 Gf tnf (OK sf) /\
    sf = update_var out (a + n2w off)
      (s with vs_inst_idx := LENGTH sb.cs_current_insts) /\
    lookup_var out sf = SOME (a + n2w off) /\ ptr_covers Gf tnf out sf n /\
    op_taint tnf (Var out) = {} /\
    ~sf.vs_halted /\ sf.vs_current_bb = sb.cs_current_bb /\
    sf.vs_inst_idx = LENGTH sb.cs_current_insts /\
    sf.vs_memory = s.vs_memory /\ tnf.t_mem = tn.t_mem /\
    tnf.t_stor = tn.t_stor /\ tnf.t_trans = tn.t_trans /\ tnf.t_imm = tn.t_imm /\
    sf.vs_call_ctx = s.vs_call_ctx /\ sf.vs_accounts = s.vs_accounts /\
    sf.vs_transient = s.vs_transient /\
    (!p. not_fresh_at sa p ==>
      lookup_var p sf = lookup_var p s /\ FLOOKUP Gf p = FLOOKUP G p /\
      op_taint tnf (Var p) = op_taint tn (Var p))
Proof
  strip_tac >>
  `sb.cs_blocks = sa.cs_blocks /\ sb.cs_current_bb = sa.cs_current_bb /\
   sb.cs_current_insts = sa.cs_current_insts ++
     [mk_inst sa.cs_next_id ADD [Var src; Lit (n2w off)] [out]] /\
   (!p. not_fresh_at sa p ==> p <> out)` by
    (gvs[emit_op_def, comp_bind_def, comp_ignore_bind_def, comp_return_def,
        fresh_var_def, fresh_id_def, emit_def, not_fresh_at_def] >>
     metis_tac[arithmeticTheory.LESS_EQ_REFL]) >>
  `op_taint tn (Var src) = {} /\ src <> out` by
    (fs[ptr_covers_def] >> metis_tac[]) >>
  drule_all fn_has_code_same_block >> strip_tac >>
  `get_instruction bb s.vs_inst_idx =
     SOME (mk_inst sa.cs_next_id ADD [Var src; Lit (n2w off)] [out])` by
    (first_x_assum (qspec_then `0` mp_tac) >> simp[]) >>
  `lookup_block s.vs_current_bb fn.fn_blocks = SOME bb` by simp[] >>
  drule_all add_literal_path_ptr >> strip_tac >>
  qexistsl_tac [
    `step_prov PG G (mk_inst sa.cs_next_id ADD [Var src; Lit (n2w off)] [out])
      (update_var out (a + n2w off) s)`,
    `step_taint (mk_inst sa.cs_next_id ADD [Var src; Lit (n2w off)] [out]) s
      (update_var out (a + n2w off) s) tn`,
    `(update_var out (a + n2w off) s) with vs_inst_idx := SUC s.vs_inst_idx`] >>
  `ptr_covers
    (step_prov PG G (mk_inst sa.cs_next_id ADD [Var src; Lit (n2w off)] [out])
      (update_var out (a + n2w off) s))
    (step_taint (mk_inst sa.cs_next_id ADD [Var src; Lit (n2w off)] [out]) s
      (update_var out (a + n2w off) s) tn)
    out (update_var out (a + n2w off) s) n` by
    (irule typed_copy_loop_dynamic_offset_covers >> simp[eval_operand_def] >>
     qexists_tac `span` >> simp[]) >>
  simp[add_literal_imm_frame, copy_len_binop_ghost_frame, update_var_def,
       lookup_var_def, FLOOKUP_UPDATE, arithmeticTheory.ADD1,
       ptr_covers_def] >>
  gvs[ptr_covers_def, update_var_def, lookup_var_def, FLOOKUP_UPDATE]
QED

Theorem ghost_inv_scalar_field_clean:
  ghost_inv d cenv cx es G tn s /\
  lookup_scopes name es.scopes = SOME entry /\
  FLOOKUP cenv.ce_vars name = SOME (PtrVar (Var p) sz) /\
  lookup_var p s = SOME a /\
  entry.type = StructTV fs /\ entry.value = StructV vals /\
  fields_layout flds fs /\ struct_has_type fs vals /\
  ALOOKUP fs fld = SOME ftv /\ ALOOKUP vals fld = SOME fv /\ word_value fv ==>
  !i. w2n a + struct_field_offset flds fld <= i /\
      i < w2n a + struct_field_offset flds fld + 32 ==> i NOTIN tn.t_mem
Proof
  strip_tac >> gen_tac >> strip_tac >>
  irule robust_val_in_memory_prim_clean >>
  qexistsl_tac [`w2n a + struct_field_offset flds fld`, `s.vs_memory`, `ftv`, `fv`] >>
  simp[GSYM word_value_def] >> rpt strip_tac >>
  irule fields_in_memory_field >> qexistsl_tac [`fs`, `vals`] >> simp[] >>
  fs[ghost_inv_def] >>
  qpat_x_assum `!name entry p sz. _` drule_all >> strip_tac >>
  first_x_assum drule_all >> simp[val_in_memory_struct]
QED

Theorem emit_field_load_path_ptr:
  emit_op ADD [Var src; Lit (n2w off)] sa = (Var dst,sm) /\
  emit_op MLOAD [Var dst] sm = (Var out,sb) /\
  fn_has_code sa sm fn /\ fn_has_code sm sb fn /\
  ~ctx_has_dalloca ctx /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\ not_fresh_at sa src /\
  ptr_covers G tn src s span /\ lookup_var src s = SOME a /\
  off < span /\ off + 32 <= span /\ w2n a + off < dimword (:256) /\
  (!i. w2n (a + n2w off) <= i /\ i < w2n (a + n2w off) + 32 ==> i NOTIN tn.t_mem) ==>
  ?Gf tnf sf.
    gas_path_ptr D 0 ctx fn PG G tn s 0 Gf tnf (OK sf) /\
    sf = update_var out (mload (w2n (a + n2w off)) s)
      (update_var dst (a + n2w off) (s with vs_inst_idx := LENGTH sb.cs_current_insts)) /\
    lookup_var dst sf = SOME (a + n2w off) /\ ptr_covers Gf tnf dst sf 32 /\
    lookup_var out sf = SOME (mload (w2n (a + n2w off)) s) /\
    op_taint tnf (Var out) = {} /\
    ~sf.vs_halted /\ sf.vs_current_bb = sb.cs_current_bb /\
    sf.vs_inst_idx = LENGTH sb.cs_current_insts /\
    sf.vs_memory = s.vs_memory /\ tnf.t_mem = tn.t_mem /\
    tnf.t_stor = tn.t_stor /\ tnf.t_trans = tn.t_trans /\ tnf.t_imm = tn.t_imm /\
    sf.vs_call_ctx = s.vs_call_ctx /\ sf.vs_accounts = s.vs_accounts /\
    sf.vs_transient = s.vs_transient /\
    (!p. not_fresh_at sa p ==>
      lookup_var p sf = lookup_var p s /\ FLOOKUP Gf p = FLOOKUP G p /\
      op_taint tnf (Var p) = op_taint tn (Var p)) /\
    op_prov Gf (Var out) = NONE
Proof
  strip_tac >>
  `sa.cs_next_var <= sm.cs_next_var /\ not_fresh_at sm dst` by
    gvs[emit_op_def, comp_bind_def, comp_ignore_bind_def, comp_return_def,
        fresh_var_def, fresh_id_def, emit_def, not_fresh_at_def] >>
  `!p. not_fresh_at sa p ==> not_fresh_at sm p` by
    (rpt strip_tac >> irule not_fresh_at_mono >> qexists_tac `sa` >> simp[]) >>
  drule_all (Q.INST [`n` |-> `32`] emit_add_literal_path_ptr) >>
  disch_then (qspecl_then [`PG`, `D`] strip_assume_tac) >>
  rename1 `gas_path_ptr D 0 ctx fn PG G tn s 0 Ga tna (OK u)` >>
  qpat_x_assum `u = _` (mk_asm "address_state") >>
  `!i. w2n (a + n2w off) <= i /\ i < w2n (a + n2w off) + 32 ==>
       i NOTIN tna.t_mem` by simp[] >>
  drule_all emit_mload_path_ptr >>
  disch_then (qspecl_then [`PG`, `D`] strip_assume_tac) >>
  `sf = update_var out (mload (w2n (a + n2w off)) s)
      (update_var dst (a + n2w off) (s with vs_inst_idx := LENGTH sb.cs_current_insts))` by
    (asm "address_state" assume_tac >> gvs[update_var_def, mload_def]) >>
  qpat_x_assum `sf = update_var _ (mload _ u) _` kall_tac >>
  qexistsl_tac [`Gf`, `tnf`, `sf`] >> simp[IgnAsm `sf = _`] >>
  conj_tac >- (drule_all gas_path_ptr_then >> simp[]) >>
  conj_tac >- first_assum ACCEPT_TAC >>
  qpat_x_assum `sf = _` kall_tac >>
  conj_tac
  >- (gvs[ptr_covers_def] >> metis_tac[]) >>
  gvs[mload_def]
QED

Theorem ghost_inv_struct_field_inputs:
  stmt_state_rel ctx fn cenv cx es s /\ ghost_inv d cenv cx es G tn s /\
  FLOOKUP cenv.ce_vars name = SOME (PtrVar (Var p) sz) /\
  lookup_var p s = SOME a /\ lookup_scopes name es.scopes = SOME entry /\
  entry.type = StructTV fs /\ entry.value = StructV vals /\
  fields_layout flds fs /\ struct_has_type fs vals /\
  ALOOKUP fs fld = SOME ftv /\ ALOOKUP vals fld = SOME fv /\
  type_memory_size ftv = 32 /\ word_value fv ==>
  ptr_covers G tn p s sz /\
  struct_field_offset flds fld < sz /\ struct_field_offset flds fld + 32 <= sz /\
  w2n a + struct_field_offset flds fld < dimword (:256) /\
  (!i. w2n (a + n2w (struct_field_offset flds fld)) <= i /\
       i < w2n (a + n2w (struct_field_offset flds fld)) + 32 ==> i NOTIN tn.t_mem)
Proof
  strip_tac >>
  `w2n a + sz <= s.vs_alloca_next /\ type_memory_size entry.type <= sz` by
    (fs[stmt_state_rel_def, state_rel_def, local_ptrs_rel_def] >>
     first_x_assum drule_all >> strip_tac >> gvs[]) >>
  `s.vs_alloca_next < dimword (:256)` by
    (irule alloca_room_next_lt >> qexistsl_tac [`ctx`, `fn`] >>
     gvs[stmt_state_rel_def]) >>
  `struct_field_offset flds fld + type_memory_size ftv <= type_memory_size_fields fs` by
    metis_tac[struct_field_offset_le] >>
  `w2n a + struct_field_offset flds fld < dimword (:256)` by
    (gvs[type_memory_size_def] >> decide_tac) >>
  `w2n (a + n2w (struct_field_offset flds fld)) = w2n a + struct_field_offset flds fld` by
    (irule buffer_offset_no_wrap >> qexists_tac `sz` >>
     gvs[type_memory_size_def]) >>
  conj_tac >- (fs[ghost_inv_def] >> metis_tac[]) >>
  conj_tac >- (gvs[type_memory_size_def] >> decide_tac) >>
  conj_tac >- (gvs[type_memory_size_def] >> decide_tac) >>
  simp[] >> gen_tac >> strip_tac >>
  irule ghost_inv_scalar_field_clean >> metis_tac[arithmeticTheory.ADD_ASSOC]
QED

Theorem augassign_field_load_ptr:
  emit_op ADD [Var src; Lit (n2w off)] sa = (Var dst,sm) /\
  emit_op MLOAD [Var dst] sm = (Var out,sb) /\
  fn_has_code sa sm fn /\ fn_has_code sm sb fn /\
  ~ctx_has_dalloca ctx /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\ not_fresh_at sa src /\
  ptr_covers G tn src s span /\ lookup_var src s = SOME a /\
  off < span /\ off + 32 <= span /\ w2n a + off < dimword (:256) /\
  (!i. w2n (a + n2w off) <= i /\ i < w2n (a + n2w off) + 32 ==> i NOTIN tn.t_mem) /\
  local_ptrs_reserved cenv sa /\ stmt_state_rel ctx fn cenv cx es s /\
  ghost_inv d cenv cx es G tn s /\ ret_pc_ok cenv sa s /\
  (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) ==>
  ?Gf tnf sf.
    gas_path_ptr D 0 ctx fn PG G tn s 0 Gf tnf (OK sf) /\
    stmt_state_rel ctx fn cenv cx es sf /\ ghost_inv d cenv cx es Gf tnf sf /\
    ghost_kept cenv es sa G tn s Gf tnf /\
    lookup_var dst sf = SOME (a + n2w off) /\ ptr_covers Gf tnf dst sf 32 /\
    lookup_var out sf = SOME (mload (w2n (a + n2w off)) s) /\
    op_taint tnf (Var out) = {} /\
    ~sf.vs_halted /\ sf.vs_current_bb = sb.cs_current_bb /\
    sf.vs_inst_idx = LENGTH sb.cs_current_insts /\
    local_ptrs_reserved cenv sb /\ not_fresh_at sb dst /\ not_fresh_at sb out /\
    (!rp. not_fresh_at sa rp ==> lookup_var rp sf = lookup_var rp s) /\
    op_prov Gf (Var out) = NONE
Proof
  strip_tac >>
  drule_all emit_field_load_path_ptr >>
  disch_then (qspecl_then [`PG`, `D`] strip_assume_tac) >>
  `sm.cs_next_var = sa.cs_next_var + 1 /\
   sb.cs_next_var = sm.cs_next_var + 1 /\
   dst = STRCAT "%" (toString sa.cs_next_var) /\
   out = STRCAT "%" (toString sm.cs_next_var)` by
    gvs[emit_op_def, comp_bind_def, comp_ignore_bind_def, comp_return_def,
        fresh_var_def, fresh_id_def, emit_def] >>
  `local_ptrs_reserved cenv sm /\ local_ptrs_reserved cenv sb` by
    (conj_tac >> irule local_ptrs_reserved_next_var >>
     qexists_tac `sa` >> simp[]) >>
  qexistsl_tac [`Gf`, `tnf`, `sf`] >> simp[IgnAsm `sf = _`] >>
  conj_tac
  >- (gvs[] >> simp[stmt_state_rel_inst_idx] >>
      irule stmt_state_rel_update_var >> conj_tac
      >- (irule local_ptrs_reserved_fresh >> qexists_tac `sm` >> simp[]) >>
      irule stmt_state_rel_update_var >> simp[stmt_state_rel_inst_idx] >>
      irule local_ptrs_reserved_fresh >> qexists_tac `sa` >> simp[]) >>
  conj_tac
  >- (qpat_x_assum `sf = _` kall_tac >> irule ghost_inv_load_frame >>
      qexistsl_tac [`G`, `s`, `sa`, `tn`] >> simp[] >>
      gvs[ret_pc_ok_def] >> metis_tac[]) >>
  simp[ghost_kept_def, not_fresh_at_def]
QED
