(* Installed scalar control edges of the external word-copy loop. *)
Theory bodyPtrMakeArrayStorageControl
Ancestors
  bodyPtrMakeArrayExternalLoop ifJumpPtr exprSimStorageCopy
  fragGasSeqPtr fragGasPathPtr venomExecSemantics venomInst venomState
  ptrSafeRun ptrDiscipline codegenRel contextCodegenRel finite_map words
  fragExec exprLoweringProps emitHelperProps rich_list compileEnv

Theorem storage_control_scalar_check:
  (opc = ASSIGN /\ ops = [Lit w] \/
   opc = EQ /\ (?v w. ops = [Var v; Lit w])) /\
  (!op. MEM op ops ==> op_taint tn op = {}) /\
  ~ctx_has_dalloca ctx /\
  step_inst_base (mk_inst id opc ops [out]) s = OK u /\
  u.vs_requests = s.vs_requests ==>
  ptr_inst_ok D 0 fuel ctx fn G tn (mk_inst id opc ops [out]) s
Proof
  strip_tac >> gvs[] >>
  simp[ptr_inst_ok_def, access_ok_def, taint_ok_def, allocas_from_def,
       mk_inst_def, source_memory_write_ranges_def,
       source_memory_read_ranges_def] >>
  simp[GSYM mk_inst_def, step_inst_non_invoke] >> metis_tac[]
QED

Theorem storage_control_scalar_path:
  (opc = ASSIGN /\ ops = [Lit w] \/
   opc = EQ /\ (?v w. ops = [Var v; Lit w])) /\
  (!op. MEM op ops ==> op_taint tn op = {}) /\
  ~ctx_has_dalloca ctx /\ ~s.vs_halted /\
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  get_instruction bb s.vs_inst_idx = SOME (mk_inst id opc ops [out]) /\
  step_inst_base (mk_inst id opc ops [out]) s = OK u /\
  u.vs_requests = s.vs_requests /\ ~u.vs_halted ==>
  gas_path_ptr D 0 ctx fn PG G tn s 0
    (step_prov PG G (mk_inst id opc ops [out]) u)
    (step_taint (mk_inst id opc ops [out]) s u tn)
    (OK (u with vs_inst_idx := SUC s.vs_inst_idx))
Proof
  strip_tac >>
  `ptr_inst_ok D 0 0 ctx fn G tn (mk_inst id opc ops [out]) s` by
    (irule storage_control_scalar_check >> metis_tac[]) >>
  `gas_path_ptr_edge D 0 ctx fn PG G tn s 0
    (step_prov PG G (mk_inst id opc ops [out]) u)
    (step_taint (mk_inst id opc ops [out]) s u tn)
    (OK (u with vs_inst_idx := SUC s.vs_inst_idx))` by
    (mp_tac (Q.INST [`i` |-> `mk_inst id opc ops [out]`,
                     `lo` |-> `0`, `u` |-> `u`] straight_line_ptr_edge) >>
     gvs[mk_inst_def, is_terminator_def]) >>
  drule (cj 2 gas_path_ptr_rules) >>
  disch_then (qspec_then `0` mp_tac) >>
  simp[gas_path_ptr_rules] >> disch_then irule >>
  irule (cj 1 gas_path_ptr_rules) >> simp[]
QED

Theorem storage_control_scalar_ghost:
  (opc = ASSIGN /\ ops = [Lit w] \/
   opc = EQ /\ (?v w. ops = [Var v; Lit w])) /\
  u.vs_allocas = s.vs_allocas /\ u.vs_fmp = s.vs_fmp ==>
  step_prov PG G (mk_inst id opc ops [out]) u = DRESTRICT G (COMPL {out}) /\
  step_taint (mk_inst id opc ops [out]) s u tn =
    (tn with t_var := tn.t_var |+ (out,{}))
Proof
  strip_tac >>
  `new_site_bytes s u = {}` by
    simp[new_site_bytes_def, FLOOKUP_DEF, pred_setTheory.EXTENSION, SF CONJ_ss] >>
  gvs[] >>
  simp[step_prov_def, set_prov_def, out_prov_def, step_taint_def,
       set_var_taint_def, mk_inst_def, mem_taint_def, step_writes_def,
       source_memory_write_ranges_def, written_taint_def, store_taint_def,
       adopt_reset_def, imm_taint_def, range_bytes_def,
       taint_component_equality, out_taint_def, op_prov_def, op_taint_def,
       first_prov_def, eval_operand_def] >>
  Cases_on `lookup_var v s` >> simp[]
QED

Theorem storage_control_assign_path:
  ~ctx_has_dalloca ctx /\ ~s.vs_halted /\
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  get_instruction bb s.vs_inst_idx = SOME (mk_inst id ASSIGN [Lit w] [cv]) ==>
  gas_path_ptr D 0 ctx fn PG G tn s 0
    (DRESTRICT G (COMPL {cv})) (tn with t_var := tn.t_var |+ (cv,{}))
    (OK ((update_var cv w s) with vs_inst_idx := SUC s.vs_inst_idx))
Proof
  strip_tac >>
  `step_inst_base (mk_inst id ASSIGN [Lit w] [cv]) s = OK (update_var cv w s)` by
    simp[Once step_inst_base_def, mk_inst_def, eval_operand_def] >>
  mp_tac (Q.INST [`opc` |-> `ASSIGN`, `ops` |-> `[Lit w]`,
    `out` |-> `cv`, `u` |-> `update_var cv w s`] storage_control_scalar_ghost) >>
  simp[update_var_def] >> strip_tac >>
  mp_tac (Q.INST [`opc` |-> `ASSIGN`, `ops` |-> `[Lit w]`,
    `out` |-> `cv`, `u` |-> `update_var cv w s`] storage_control_scalar_path) >>
  simp[op_taint_def, update_var_def]
QED

Theorem storage_control_eq_path:
  ~ctx_has_dalloca ctx /\ ~s.vs_halted /\
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  get_instruction bb s.vs_inst_idx = SOME (mk_inst id EQ [Var cv; Lit (n2w n)] [tv]) /\
  lookup_var cv s = SOME (n2w k) /\ op_taint tn (Var cv) = {} /\
  k <= n /\ n < dimword(:256) ==>
  gas_path_ptr D 0 ctx fn PG G tn s 0
    (DRESTRICT G (COMPL {tv})) (tn with t_var := tn.t_var |+ (tv,{}))
    (OK ((update_var tv (bool_to_word (k = n)) s) with
      vs_inst_idx := SUC s.vs_inst_idx))
Proof
  strip_tac >>
  `k < dimword(:256)` by decide_tac >>
  `step_inst_base (mk_inst id EQ [Var cv; Lit (n2w n)] [tv]) s =
    OK (update_var tv (bool_to_word (k = n)) s)` by
    simp[Once step_inst_base_def, mk_inst_def, exec_pure2_def,
         eval_operand_def, n2w_11] >>
  mp_tac (Q.INST [`opc` |-> `EQ`, `ops` |-> `[Var cv; Lit (n2w n)]`,
    `out` |-> `tv`, `u` |-> `update_var tv (bool_to_word ((k:num) = n)) s`]
    storage_control_scalar_ghost) >>
  simp[update_var_def] >> strip_tac >>
  mp_tac (Q.INST [`opc` |-> `EQ`, `ops` |-> `[Var cv; Lit (n2w n)]`,
    `out` |-> `tv`, `u` |-> `update_var tv (bool_to_word ((k:num) = n)) s`]
    storage_control_scalar_path) >>
  simp[update_var_def] >> disch_then irule >>
  simp[] >> rpt strip_tac >> gvs[op_taint_def]
QED

Theorem storage_control_emitted_instruction:
  same_blocks sa sb /\ isPREFIX sa.cs_current_insts sb.cs_current_insts /\
  emitted_insts sa sb = [i] /\ fn_has_code sa sb fn ==>
  ?bb. lookup_block sa.cs_current_bb fn.fn_blocks = SOME bb /\
       get_instruction bb (LENGTH sa.cs_current_insts) = SOME i
Proof
  strip_tac >>
  `sb.cs_current_insts = sa.cs_current_insts ++ [i]` by
    gvs[IS_PREFIX_APPEND, emitted_insts_def, DROP_LENGTH_APPEND] >>
  fs[same_blocks_def] >> drule_all fn_has_code_same_block >> simp[] >>
  disch_then (qx_choose_then `bb` strip_assume_tac) >>
  qexists_tac `bb` >> first_x_assum (qspec_then `0` mp_tac) >> simp[]
QED

Theorem storage_control_init:
  same_blocks sa s0 /\ isPREFIX sa.cs_current_insts s0.cs_current_insts /\
  emitted_insts sa s0 = [mk_inst sa.cs_next_id ASSIGN [Lit 0w] [cv]] /\
  emit_inst JMP [Label hdr] [] s0 = ((),sj) /\
  fn_has_code sa s0 fn /\ fn_has_code s0 sj fn /\
  ~ctx_has_dalloca ctx /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  gas_path_ptr D 0 ctx fn PG G tn s 0
    (DRESTRICT G (COMPL {cv})) (tn with t_var := tn.t_var |+ (cv,{}))
    (OK (jump_to hdr (update_var cv 0w s)))
Proof
  strip_tac >>
  drule_all storage_control_emitted_instruction >> strip_tac >>
  `gas_path_ptr D 0 ctx fn PG G tn s 0
    (DRESTRICT G (COMPL {cv})) (tn with t_var := tn.t_var |+ (cv,{}))
    (OK ((update_var cv 0w s) with vs_inst_idx := SUC s.vs_inst_idx))` by
    (irule storage_control_assign_path >> metis_tac[]) >>
  `s0.cs_current_insts = sa.cs_current_insts ++
     [mk_inst sa.cs_next_id ASSIGN [Lit 0w] [cv]]` by
    gvs[IS_PREFIX_APPEND, emitted_insts_def, DROP_LENGTH_APPEND] >>
  `gas_path_ptr D 0 ctx fn PG (DRESTRICT G (COMPL {cv}))
    (tn with t_var := tn.t_var |+ (cv,{}))
    ((update_var cv 0w s) with vs_inst_idx := SUC s.vs_inst_idx) 0
    (DRESTRICT G (COMPL {cv})) (tn with t_var := tn.t_var |+ (cv,{}))
    (OK (jump_to hdr ((update_var cv 0w s) with
      vs_inst_idx := SUC s.vs_inst_idx)))` by
    (drule emit_inst_extends >> strip_tac >>
     irule if_emit_jump_zero_path_ptr >> simp[update_var_def] >>
     qexistsl_tac [`s0`, `sj`] >>
     gvs[update_var_def, same_blocks_def]) >>
  drule_all gas_path_ptr_then >> simp[jump_to_def, update_var_def]
QED

Theorem storage_control_header:
  same_blocks sth stj /\ isPREFIX sth.cs_current_insts stj.cs_current_insts /\
  emitted_insts sth stj = [mk_inst sth.cs_next_id EQ [Var cv; Lit (n2w n)] [tv]] /\
  emit_inst JNZ [Var tv; Label exit; Label loop_body] [] stj = ((),st2) /\
  fn_has_code sth stj fn /\ fn_has_code stj st2 fn /\
  ~ctx_has_dalloca ctx /\ ~s.vs_halted /\
  s.vs_current_bb = sth.cs_current_bb /\
  s.vs_inst_idx = LENGTH sth.cs_current_insts /\
  lookup_var cv s = SOME (n2w k) /\ op_taint tn (Var cv) = {} /\
  k <= n /\ n < dimword(:256) ==>
  gas_path_ptr D 0 ctx fn PG G tn s 0
    (DRESTRICT G (COMPL {tv})) (tn with t_var := tn.t_var |+ (tv,{}))
    (OK (jump_to (if k = n then exit else loop_body)
      (update_var tv (bool_to_word (k = n)) s)))
Proof
  strip_tac >>
  drule_all storage_control_emitted_instruction >> strip_tac >>
  `gas_path_ptr D 0 ctx fn PG G tn s 0
    (DRESTRICT G (COMPL {tv})) (tn with t_var := tn.t_var |+ (tv,{}))
    (OK ((update_var tv (bool_to_word (k = n)) s) with
      vs_inst_idx := SUC s.vs_inst_idx))` by
    (irule storage_control_eq_path >> metis_tac[]) >>
  `stj.cs_current_insts = sth.cs_current_insts ++
    [mk_inst sth.cs_next_id EQ [Var cv; Lit (n2w n)] [tv]]` by
    gvs[IS_PREFIX_APPEND, emitted_insts_def, DROP_LENGTH_APPEND] >>
  `gas_path_ptr D 0 ctx fn PG (DRESTRICT G (COMPL {tv}))
    (tn with t_var := tn.t_var |+ (tv,{}))
    ((update_var tv (bool_to_word (k = n)) s) with
      vs_inst_idx := SUC s.vs_inst_idx) 0
    (DRESTRICT G (COMPL {tv})) (tn with t_var := tn.t_var |+ (tv,{}))
    (OK (jump_to (if k = n then exit else loop_body)
      ((update_var tv (bool_to_word (k = n)) s) with
        vs_inst_idx := SUC s.vs_inst_idx)))` by
    (drule emit_inst_extends >> strip_tac >>
     irule if_jnz_zero_path_ptr >> simp[update_var_def] >>
     qexistsl_tac [`Var tv`, `stj`, `st2`] >>
     Cases_on `k = n` >>
     gvs[update_var_def, same_blocks_def, eval_operand_def, lookup_var_def,
         op_taint_def, FLOOKUP_UPDATE, venomExecSemanticsTheory.bool_to_word_def]) >>
  drule_all gas_path_ptr_then >> simp[jump_to_def, update_var_def]
QED

(* The inputs are precisely the control and extension projections of
   compile_storage_copy_certificate. No compiler recursion is exposed here. *)
Theorem storage_control_layout:
  emit_inst JMP [Label hdr] [] s0 = ((),sj) /\
  new_block hdr sj = (old0,sth) /\
  emit_inst JNZ [Var tv; Label exit; Label loop_body] [] stj = ((),st2) /\
  new_block loop_body st2 = (oldh,stb) /\
  emit_inst JMP [Label hdr] [] ste = ((),st3) /\
  new_block exit st3 = (u,sb) /\
  cs_extends sa s0 /\ cs_extends s0 sb /\
  cs_extends sth stj /\ cs_extends stb ste /\ fn_has_code sa sb fn ==>
  fn_has_code sa s0 fn /\ fn_has_code s0 sj fn /\
  fn_has_code sth stj fn /\ fn_has_code stj st2 fn /\
  fn_has_code stb ste fn /\ fn_has_code ste st3 fn /\
  sth.cs_current_bb = hdr /\ sth.cs_current_insts = [] /\
  stb.cs_current_bb = loop_body /\ stb.cs_current_insts = [] /\
  sb.cs_current_bb = exit /\ sb.cs_current_insts = []
Proof
  strip_tac >>
  `cs_extends s0 sj /\ cs_extends stj st2 /\ cs_extends ste st3` by
    metis_tac[cs_extends_emit_inst] >>
  `cs_extends sj sth /\ cs_extends st2 stb /\ cs_extends st3 sb` by
    metis_tac[cs_extends_new_block] >>
  `cs_extends st2 ste` by metis_tac[cs_extends_trans] >>
  `cs_extends st2 sb` by metis_tac[cs_extends_trans] >>
  `cs_extends stj sb` by metis_tac[cs_extends_trans] >>
  `cs_extends sth sb` by metis_tac[cs_extends_trans] >>
  `cs_extends sj sb` by metis_tac[cs_extends_trans] >>
  `cs_extends sa sj` by metis_tac[cs_extends_trans] >>
  `cs_extends sa sth` by metis_tac[cs_extends_trans] >>
  `cs_extends sa stj` by metis_tac[cs_extends_trans] >>
  `cs_extends sa ste` by metis_tac[cs_extends_trans] >>
  `cs_extends sa stb` by metis_tac[cs_extends_trans] >>
  `cs_extends ste sb` by metis_tac[cs_extends_trans] >>
  rpt conj_tac
  >- metis_tac[fn_has_code_split]
  >- metis_tac[fn_has_code_mid]
  >- metis_tac[fn_has_code_mid]
  >- metis_tac[fn_has_code_mid]
  >- (irule fn_has_code_mid >> goal_assum (drule_at Any) >> metis_tac[])
  >- metis_tac[fn_has_code_mid] >>
  gvs[new_block_def]
QED

Theorem storage_control_result_frame:
  cv <> tv ==>
  copy_static (jump_to lbl (update_var tv w s)) = copy_static s /\
  (jump_to lbl (update_var tv w s)).vs_memory = s.vs_memory /\
  lookup_var cv (jump_to lbl (update_var tv w s)) = lookup_var cv s /\
  op_prov (DRESTRICT G (COMPL {tv})) (Var tv) = NONE /\
  op_taint (tn with t_var := tn.t_var |+ (tv,{})) (Var tv) = {} /\
  (!x. x <> tv ==>
    lookup_var x (jump_to lbl (update_var tv w s)) = lookup_var x s /\
    op_prov (DRESTRICT G (COMPL {tv})) (Var x) = op_prov G (Var x) /\
    op_taint (tn with t_var := tn.t_var |+ (tv,{})) (Var x) = op_taint tn (Var x)) /\
  (tn with t_var := tn.t_var |+ (tv,{})).t_mem = tn.t_mem /\
  (tn with t_var := tn.t_var |+ (tv,{})).t_stor = tn.t_stor /\
  (tn with t_var := tn.t_var |+ (tv,{})).t_trans = tn.t_trans /\
  (tn with t_var := tn.t_var |+ (tv,{})).t_imm = tn.t_imm
Proof
  strip_tac >>
  simp[copy_static_def, jump_to_def, update_var_def, lookup_var_def,
       FLOOKUP_UPDATE, op_prov_def, op_taint_def, FLOOKUP_DRESTRICT]
QED

(* Regression: even an empty copy executes ASSIGN/JMP/EQ/JNZ. There is
   intentionally no destination coverage or memory-access premise. *)
Theorem storage_control_zero_path:
  same_blocks sa s0 /\ isPREFIX sa.cs_current_insts s0.cs_current_insts /\
  emitted_insts sa s0 = [mk_inst sa.cs_next_id ASSIGN [Lit 0w] [cv]] /\
  emit_inst JMP [Label hdr] [] s0 = ((),sj) /\
  same_blocks sth stj /\ isPREFIX sth.cs_current_insts stj.cs_current_insts /\
  emitted_insts sth stj = [mk_inst sth.cs_next_id EQ [Var cv; Lit 0w] [tv]] /\
  emit_inst JNZ [Var tv; Label exit; Label loop_body] [] stj = ((),st2) /\
  sth.cs_current_bb = hdr /\ sth.cs_current_insts = [] /\
  fn_has_code sa s0 fn /\ fn_has_code s0 sj fn /\
  fn_has_code sth stj fn /\ fn_has_code stj st2 fn /\
  ~ctx_has_dalloca ctx /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  gas_path_ptr D 0 ctx fn PG G tn s 0
    (DRESTRICT (DRESTRICT G (COMPL {cv})) (COMPL {tv}))
    (tn with t_var := (tn.t_var |+ (cv,{})) |+ (tv,{}))
    (OK (jump_to exit (update_var tv 1w (jump_to hdr (update_var cv 0w s)))))
Proof
  strip_tac >>
  `gas_path_ptr D 0 ctx fn PG G tn s 0
    (DRESTRICT G (COMPL {cv})) (tn with t_var := tn.t_var |+ (cv,{}))
    (OK (jump_to hdr (update_var cv 0w s)))` by
    (irule storage_control_init >> metis_tac[]) >>
  `gas_path_ptr D 0 ctx fn PG (DRESTRICT G (COMPL {cv}))
    (tn with t_var := tn.t_var |+ (cv,{}))
    (jump_to hdr (update_var cv 0w s)) 0
    (DRESTRICT (DRESTRICT G (COMPL {cv})) (COMPL {tv}))
    (tn with t_var := (tn.t_var |+ (cv,{})) |+ (tv,{}))
    (OK (jump_to exit (update_var tv 1w (jump_to hdr (update_var cv 0w s)))))` by
    (mp_tac (Q.INST [`s` |-> `jump_to hdr (update_var cv 0w s)`,
       `G` |-> `DRESTRICT G (COMPL {cv})`,
       `tn` |-> `tn with t_var := tn.t_var |+ (cv,{})`]
       (Q.INST [`k` |-> `0:num`, `n` |-> `0:num`] storage_control_header)) >>
     simp[jump_to_def, update_var_def, lookup_var_def, FLOOKUP_UPDATE,
          op_taint_def, dimword_def]) >>
  drule_all gas_path_ptr_then >> simp[jump_to_def, update_var_def]
QED
