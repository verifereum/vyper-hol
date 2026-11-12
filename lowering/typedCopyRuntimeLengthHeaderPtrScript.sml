(* Counted loop headers whose limit is a clean runtime operand. *)
Theory typedCopyRuntimeLengthHeaderPtr
Ancestors assignBasePtrStoragePath typedCopyLoopHeaderPtr fragGasPathPtr
  fragGasSeqPtr stateFrame venomState venomInst venomExecSemantics ptrDiscipline
  ptrSafeRun codegenRel contextCodegenRel words finite_map list arithmetic

Theorem runtime_header_test_counted[local]:
  ~s.vs_halted /\ lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  get_instruction bb s.vs_inst_idx = SOME (mk_inst id opc ops [out]) /\
  (opc = LT \/ opc = ISZERO) /\
  (!v. opc = LT /\ MEM (Var v) ops ==> FLOOKUP G v = NONE) /\
  (!op. MEM op ops ==> op_taint tn op = {}) /\ ~ctx_has_dalloca ctx /\
  step_inst_base (mk_inst id opc ops [out]) s = OK (update_var out w s) ==>
  gas_path_ptr D 0 ctx fn PG G tn s 0 (DRESTRICT G (COMPL {out}))
    (tn with t_var := tn.t_var |+ (out,{}))
    (OK ((update_var out w s) with vs_inst_idx := SUC s.vs_inst_idx))
Proof
  strip_tac >>
  `ptr_inst_ok D 0 0 ctx fn G tn (mk_inst id opc ops [out]) s` by
    (gvs[] >> simp[ptr_inst_ok_def,access_ok_def,taint_ok_def,allocas_from_def,
      mk_inst_def,source_memory_write_ranges_def,source_memory_read_ranges_def] >>
     simp[GSYM mk_inst_def,step_inst_non_invoke] >>
     rpt strip_tac >> gvs[] >>
     metis_tac[MEM,FLOOKUP_DEF,optionTheory.NOT_SOME_NONE]) >>
  `step_prov PG G (mk_inst id opc ops [out]) (update_var out w s) =
     DRESTRICT G (COMPL {out}) /\
   step_taint (mk_inst id opc ops [out]) s (update_var out w s) tn =
     (tn with t_var := tn.t_var |+ (out,{}))` by
    (irule typed_copy_loop_arith_ghost_clean >> simp[update_var_def] >> metis_tac[]) >>
  mp_tac (Q.GENL [`u`,`G'`,`tn'`,`r`]
    (Q.INST [`n` |-> `0`,`lo` |-> `0`,
      `i` |-> `mk_inst id opc ops [out]`] gas_path_ptr_step)) >>
  simp[mk_inst_def,is_terminator_def] >> disch_then irule >>
  simp[GSYM mk_inst_def] >> gvs[] >>
  irule (cj 1 gas_path_ptr_rules) >> simp[update_var_def]
QED

Theorem runtime_header_prefix[local]:
  ~s.vs_halted /\ lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  get_instruction bb s.vs_inst_idx = SOME (mk_inst id LT [Var ctr;limit] [lt]) /\
  get_instruction bb (SUC s.vs_inst_idx) = SOME (mk_inst (id+1) ISZERO [Var lt] [done]) /\
  lookup_var ctr s = SOME (n2w i) /\ eval_operand limit s = SOME (n2w n) /\
  i <= n /\ n < dimword(:256) /\ op_taint tn (Var ctr) = {} /\
  op_taint tn limit = {} /\ FLOOKUP G ctr = NONE /\ op_prov G limit = NONE /\
  ALL_DISTINCT [ctr;lt;done] /\ ~ctx_has_dalloca ctx ==>
  ?Gf tf u.
    gas_path_ptr D 0 ctx fn PG G tn s 0 Gf tf (OK u) /\
    lookup_var done u = SOME (bool_to_word (~(i<n))) /\ op_taint tf (Var done) = {} /\
    execution_frame u = execution_frame s /\
    u.vs_accounts = s.vs_accounts /\ u.vs_transient = s.vs_transient /\
    u.vs_call_ctx = s.vs_call_ctx /\ u.vs_memory = s.vs_memory /\
    tf.t_mem = tn.t_mem /\ tf.t_imm = tn.t_imm /\
    tf.t_stor = tn.t_stor /\ tf.t_trans = tn.t_trans /\
    u.vs_current_bb = s.vs_current_bb /\ u.vs_inst_idx = s.vs_inst_idx+2 /\ ~u.vs_halted /\
    (!x. x <> lt /\ x <> done ==> lookup_var x u = lookup_var x s /\
      FLOOKUP Gf x = FLOOKUP G x /\ op_taint tf (Var x) = op_taint tn (Var x))
Proof
  strip_tac >>
  qabbrev_tac `s1 = update_var lt (bool_to_word (i<n)) s with vs_inst_idx := SUC s.vs_inst_idx` >>
  qabbrev_tac `g1 = DRESTRICT G (COMPL {lt})` >>
  qabbrev_tac `t1 = tn with t_var := tn.t_var |+ (lt,{})` >>
  `step_inst_base (mk_inst id LT [Var ctr;limit] [lt]) s =
    OK (update_var lt (bool_to_word (i<n)) s)` by
    (asm_simp_tac bool_ss [step_inst_base_opcode_eqs,mk_inst_def,instruction_accessors,
       instruction_accfupds,combinTheory.K_THM,opcode_case_def] >>
     simp[exec_pure2_def,eval_operand_def,w2n_n2w,LESS_MOD]) >>
  `gas_path_ptr D 0 ctx fn PG G tn s 0 g1 t1 (OK s1)` by
    (simp[Abbr `s1`,Abbr `g1`,Abbr `t1`] >>
     irule runtime_header_test_counted >> simp[] >>
     goal_assum (drule_at Any) >> simp[] >> rpt strip_tac >> gvs[op_prov_def]) >>
  `step_inst_base (mk_inst (id+1) ISZERO [Var lt] [done]) s1 =
    OK (update_var done (bool_to_word (~(i<n))) s1)` by
    (asm_simp_tac bool_ss [step_inst_base_opcode_eqs,mk_inst_def,instruction_accessors,
       instruction_accfupds,combinTheory.K_THM,opcode_case_def] >>
     simp[Abbr `s1`,exec_pure1_def,eval_operand_def,lookup_var_def,
       update_var_def,FLOOKUP_UPDATE,bool_to_word_def] >> Cases_on `i<n` >> simp[]) >>
  `gas_path_ptr D 0 ctx fn PG g1 t1 s1 0 (DRESTRICT g1 (COMPL {done}))
    (t1 with t_var := t1.t_var |+ (done,{}))
    (OK (update_var done (bool_to_word (~(i<n))) s1 with vs_inst_idx := SUC s1.vs_inst_idx))` by
    (irule runtime_header_test_counted >> simp[Abbr `s1`,update_var_def] >>
     qexistsl_tac [`id+1`,`ISZERO`,`[Var lt]`] >>
     gvs[Abbr `t1`,update_var_def,op_taint_def,FLOOKUP_UPDATE]) >>
  qexistsl_tac [`DRESTRICT g1 (COMPL {done})`,`t1 with t_var := t1.t_var |+ (done,{})`,
    `update_var done (bool_to_word (~(i<n))) s1 with vs_inst_idx := SUC s1.vs_inst_idx`] >>
  conj_tac >- (drule_all gas_path_ptr_then >> simp[]) >>
  gvs[Abbr `s1`,Abbr `g1`,Abbr `t1`,ALL_DISTINCT,execution_frame_def,
    update_var_def,lookup_var_def,op_taint_def,FLOOKUP_UPDATE,FLOOKUP_DRESTRICT,ADD1]
QED

Theorem typed_copy_runtime_length_header_counted:
  ~s.vs_halted /\ lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  get_instruction bb s.vs_inst_idx = SOME (mk_inst id LT [Var ctr;limit] [lt]) /\
  get_instruction bb (SUC s.vs_inst_idx) = SOME (mk_inst (id+1) ISZERO [Var lt] [done]) /\
  get_instruction bb (s.vs_inst_idx+2) =
    SOME (mk_inst (id+2) JNZ [Var done;Label exit;Label bodylbl] []) /\
  lookup_var ctr s = SOME (n2w i) /\ eval_operand limit s = SOME (n2w n) /\
  i <= n /\ n < dimword(:256) /\ op_taint tn (Var ctr) = {} /\
  op_taint tn limit = {} /\ FLOOKUP G ctr = NONE /\ op_prov G limit = NONE /\
  ALL_DISTINCT [ctr;lt;done] /\ ~ctx_has_dalloca ctx ==>
  ?Gf tf u.
    gas_path_ptr D 0 ctx fn PG G tn s 0 Gf tf (OK u) /\
    u.vs_current_bb = (if i<n then bodylbl else exit) /\ u.vs_inst_idx = 0 /\ ~u.vs_halted /\
    execution_frame u = execution_frame s /\
    u.vs_accounts = s.vs_accounts /\ u.vs_transient = s.vs_transient /\
    u.vs_call_ctx = s.vs_call_ctx /\ u.vs_memory = s.vs_memory /\
    tf.t_mem = tn.t_mem /\ tf.t_imm = tn.t_imm /\ tf.t_stor = tn.t_stor /\ tf.t_trans = tn.t_trans /\
    (!x. x <> lt /\ x <> done ==> lookup_var x u = lookup_var x s /\
      FLOOKUP Gf x = FLOOKUP G x /\ op_taint tf (Var x) = op_taint tn (Var x))
Proof
  strip_tac >> drule_all runtime_header_prefix >>
  disch_then (qspecl_then [`PG`,`D`] strip_assume_tac) >>
  rename1 `gas_path_ptr D 0 ctx fn PG G tn s 0 g1 t1 (OK s1)` >>
  `lookup_block s1.vs_current_bb fn.fn_blocks = SOME bb /\
   get_instruction bb s1.vs_inst_idx =
     SOME (mk_inst (id+2) JNZ [Var done;Label exit;Label bodylbl] []) /\
   eval_operand (Var done) s1 = SOME (if ~(i<n) then 1w else 0w)` by
    (simp[eval_operand_def] >> Cases_on `i<n` >> simp[bool_to_word_def]) >>
  drule_all assign_base_storage_branch_counted >>
  disch_then (qspecl_then [`g1`,`D`,`PG`] strip_assume_tac) >>
  qexistsl_tac [`g1`,`t1`,`jump_to (if ~(i<n) then exit else bodylbl) s1`] >>
  conj_tac >- (drule_all gas_path_ptr_then >> simp[]) >>
  gvs[jump_to_def,lookup_var_def] >> Cases_on `i<n` >> simp[]
QED
