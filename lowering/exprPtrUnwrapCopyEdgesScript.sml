(* Bounded storage/transient copy instruction boundaries. Loading a slot
   transports taint in dead bytes, rather than assuming the slot clean. *)
Theory exprPtrUnwrapCopyEdges
Ancestors
  fragGasSeqPtr fragGasPathPtr gasCount slotCopyExecution ptrSafeRun ptrDiscipline
  venomExecProps bodyPtrDefs memLocDefs compileEnv vfmConstants
  venomExecSemantics venomInstProofs venomInst venomState finite_map codegenRel contextCodegenRel

Theorem copy_step_immutable_taint:
  inst.inst_opcode <> ISTORE ==>
  (step_taint inst s u tn).t_imm = tn.t_imm
Proof
  simp[step_taint_def, imm_taint_def]
QED

Theorem copy_mk_immutable_taint:
  opc <> ISTORE ==>
  (step_taint (mk_inst id opc args outs) s u tn).t_imm = tn.t_imm
Proof
  simp[copy_step_immutable_taint, mk_inst_def]
QED

Theorem slot_load_output_taint:
  (load = SLOAD \/ load = TLOAD) /\ eval_operand a s = SOME key ==>
  op_taint (step_taint (mk_inst id load [a] [out]) s u tn) (Var out) =
    key_taint (if load = SLOAD then tn.t_stor else tn.t_trans) key
Proof
  strip_tac >>
  gvs[step_taint_def, set_var_taint_def, out_taint_def, op_taint_def,
      mk_inst_def, FLOOKUP_UPDATE]
QED

Theorem slot_load_ghost_frame:
  (load = SLOAD \/ load = TLOAD) ==>
  (step_taint (mk_inst id load [a] [out]) s
    (update_var out value s) tn).t_mem = tn.t_mem /\
  (step_taint (mk_inst id load [a] [out]) s
    (update_var out value s) tn).t_stor = tn.t_stor /\
  (step_taint (mk_inst id load [a] [out]) s
    (update_var out value s) tn).t_trans = tn.t_trans /\
  (step_taint (mk_inst id load [a] [out]) s
    (update_var out value s) tn).t_imm = tn.t_imm
Proof
  strip_tac >>
  gvs[step_taint_def, mem_taint_def, new_site_bytes_def, step_writes_def,
      written_taint_def, source_memory_write_ranges_def, range_bytes_def,
      store_taint_def, imm_taint_def, adopt_reset_def, mk_inst_def, update_var_def,
      FLOOKUP_DEF, pred_setTheory.EXTENSION] >> metis_tac[]
QED

Theorem ptr_inst_ok_slot_load:
  (load = SLOAD \/ load = TLOAD) /\ eval_operand a s = SOME key /\
  op_taint tn a = {} /\ allocas_from lo s /\
  (ctx_has_dalloca ctx ==> allocas_below_fmp s) ==>
  ptr_inst_ok D lo fuel ctx fn G tn (mk_inst id load [a] [out]) s
Proof
  strip_tac >> gvs[] >>
  simp[ptr_inst_ok_def, access_ok_def, taint_ok_def, mk_inst_def,
       source_memory_write_ranges_def, source_memory_read_ranges_def] >>
  simp[step_inst_non_invoke] >>
  asm_simp_tac bool_ss [step_inst_base_opcode_eqs, instruction_accessors, instruction_accfupds,
                   combinTheory.K_THM, opcode_case_def] >>
  simp[exec_read1_def, update_var_def]
QED

Theorem slot_load_counted_edge:
  (load = SLOAD \/ load = TLOAD) /\ eval_operand a s = SOME key /\
  op_taint tn a = {} /\ allocas_from lo s /\
  (ctx_has_dalloca ctx ==> allocas_below_fmp s) /\ ~s.vs_halted /\
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  get_instruction bb s.vs_inst_idx = SOME (mk_inst id load [a] [out]) ==>
  gas_path_ptr_edge D lo ctx fn PG G tn s 0
    (step_prov PG G (mk_inst id load [a] [out])
      (update_var out (slot_copy_word load s key) s))
    (step_taint (mk_inst id load [a] [out]) s
      (update_var out (slot_copy_word load s key) s) tn)
    (OK ((update_var out (slot_copy_word load s key) s)
       with vs_inst_idx := SUC s.vs_inst_idx))
Proof
  strip_tac >>
  `ptr_inst_ok D lo 0 ctx fn G tn (mk_inst id load [a] [out]) s` by
    (irule ptr_inst_ok_slot_load >> simp[]) >>
  drule_at (Pat `ptr_inst_ok _ _ _ _ _ _ _ _ _`) straight_line_ptr_edge >>
  gvs[mk_inst_def, is_terminator_def, step_inst_base_opcode_eqs,
      exec_read1_def, slot_copy_word_def]
QED

Theorem mstore_transferred_taint:
  eval_operand a s = SOME addr /\ eval_operand v s = SOME value ==>
  (step_taint (mk_inst id MSTORE [a;v] []) s
    (mstore (w2n addr) value s) tn).t_mem =
  (tn.t_mem DIFF {j | w2n addr <= j /\ j < w2n addr + 32}) UNION
    {w2n addr + k | k IN op_taint tn v}
Proof
  strip_tac >>
  simp[step_taint_def, mem_taint_def, new_site_bytes_def, step_writes_def,
       written_taint_def, source_memory_write_ranges_def, range_bytes_def,
       fixed_source_write_range_def, mk_inst_def, mstore_def,
       FLOOKUP_DEF, pred_setTheory.EXTENSION] >> metis_tac[]
QED

Theorem ptr_inst_ok_mstore_tainted:
  ptr_covers G tn p s 32 /\ allocas_from lo s /\
  (ctx_has_dalloca ctx ==> allocas_below_fmp s) ==>
  ptr_inst_ok D lo fuel ctx fn G tn (mk_inst id MSTORE [Var p; v] []) s
Proof
  strip_tac >> gvs[ptr_covers_def] >>
  simp[ptr_inst_ok_def, access_ok_def, taint_ok_def,
       mk_inst_def, source_memory_write_ranges_def,
       source_memory_read_ranges_def, fixed_source_write_range_def,
       eval_operand_def] >>
  conj_tac
  >- (Cases_on `eval_operand v s` >> simp[] >>
      rpt strip_tac >> gvs[mem_write_ops_def, mk_inst_def] >> metis_tac[]) >>
  conj_tac
  >- (rpt strip_tac >> Cases_on `op = Var p` >> gvs[] >>
      qexists_tac `Var p` >> simp[]) >>
  simp[step_inst_non_invoke] >>
  asm_simp_tac bool_ss [step_inst_base_opcode_eqs, instruction_accessors, instruction_accfupds,
                   combinTheory.K_THM, opcode_case_def] >>
  simp[exec_write2_def, eval_operand_def, AllCaseEqs(), mstore_def] >>
  rpt strip_tac >> gvs[]
QED

Theorem copy_jnz_counted_edge:
  ~s.vs_halted /\
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  get_instruction bb s.vs_inst_idx =
    SOME (mk_inst id JNZ [op; Label yes; Label no] []) /\
  eval_operand op s = SOME (if b then 1w else 0w) /\
  op_taint tn op = {} /\ allocas_from lo s /\
  (ctx_has_dalloca ctx ==> allocas_below_fmp s) ==>
  gas_path_ptr_edge D lo ctx fn PG G tn s 0 G tn
    (OK (jump_to (if b then yes else no) s))
Proof
  strip_tac >>
  `step_inst 0 ctx (mk_inst id JNZ [op; Label yes; Label no] []) s =
     OK (jump_to (if b then yes else no) s)` by
    (simp[step_inst_non_invoke, mk_inst_def] >>
     drule step_jnz_behavior >>
     disch_then (qspecl_then [`yes`, `no`, `id`] mp_tac) >>
     simp[mk_inst_def] >> Cases_on `b` >> simp[]) >>
  `ptr_safe_step D lo 0 ctx fn PG G tn
     (mk_inst id JNZ [op; Label yes; Label no] []) s` by
    (simp[ptr_safe_step_def, ptr_inst_ok_def, access_ok_def, taint_ok_def,
          source_memory_write_ranges_def, source_memory_read_ranges_def] >>
     simp[mk_inst_def, op_taint_def] >>
     qx_gen_tac `x` >> Cases_on `x = op` >> gvs[op_taint_def] >>
     Cases_on `x` >> simp[]) >>
  rewrite_tac[gas_path_ptr_edge_def] >> simp[] >>
  qexists_tac `0` >>
  simp[gas_count_step_def, mk_inst_def, is_terminator_def] >>
  disj2_tac >> disj1_tac >> qexists_tac `if b then yes else no` >> simp[]
QED

Theorem copy_eq_counted_edge:
  eval_operand (Var ctr) s = SOME x /\ op_taint tn (Var ctr) = {} /\
  allocas_from lo s /\ (ctx_has_dalloca ctx ==> allocas_below_fmp s) /\
  ~s.vs_halted /\ lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  get_instruction bb s.vs_inst_idx =
    SOME (mk_inst id EQ [Var ctr; Lit n] [out]) ==>
  gas_path_ptr_edge D lo ctx fn PG G tn s 0
    (step_prov PG G (mk_inst id EQ [Var ctr; Lit n] [out])
      (update_var out (bool_to_word (x = n)) s))
    (step_taint (mk_inst id EQ [Var ctr; Lit n] [out]) s
      (update_var out (bool_to_word (x = n)) s) tn)
    (OK (update_var out (bool_to_word (x = n)) s
       with vs_inst_idx := SUC s.vs_inst_idx))
Proof
  strip_tac >>
  `step_inst_base (mk_inst id EQ [Var ctr; Lit n] [out]) s =
     OK (update_var out (bool_to_word (x = n)) s)` by
    simp[step_inst_base_opcode_eqs, mk_inst_def, exec_pure2_def, eval_operand_def] >>
  `ptr_inst_ok D lo 0 ctx fn G tn (mk_inst id EQ [Var ctr; Lit n] [out]) s` by
    (simp[ptr_inst_ok_def, access_ok_def, taint_ok_def, mk_inst_def,
          source_memory_write_ranges_def, source_memory_read_ranges_def,
          op_taint_def] >>
     conj_tac >-
       (gen_tac >> Cases_on `op = Var ctr` >> gvs[op_taint_def] >>
        Cases_on `op` >> gvs[]) >>
     simp[GSYM mk_inst_def, step_inst_non_invoke] >>
     asm_rewrite_tac[update_var_def]) >>
  drule_at (Pat `ptr_inst_ok _ _ _ _ _ _ _ _ _`) straight_line_ptr_edge >>
  simp[mk_inst_def, is_terminator_def]
QED
