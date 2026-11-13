(* Counted live-word count for a robust bytestring header. *)
Theory storeSlotsPtrBytesCount
Ancestors storeSlotsPtrInterface assignBasePtrStoragePath
  bodyPtrEnvBuiltinsEdges typedCopyLoopHeaderPtr decoderGhostFramePtr
  context compileEnv loweringStateRelDefs emitHelper emitHelperProps
  stateFrame fragExec venomInst venomState venomExecSemantics ptrSafeRun ptrDiscipline
  fragGasSeqPtr fragGasPathPtr bodyPtrDefs finite_map pred_set list rich_list arithmetic combin words

Theorem store_slots_bytestring_count_shape:
  compile_bytestring_word_count (Var root) sa = (Var out,sb) /\
  fn_has_code sa sb fn ==>
  ?len sum bb.
    sb.cs_current_bb = sa.cs_current_bb /\
    sb.cs_current_insts = sa.cs_current_insts ++
      [mk_inst sa.cs_next_id MLOAD [Var root] [len];
       mk_inst (sa.cs_next_id+1) ADD [Var len;Lit 63w] [sum];
       mk_inst (sa.cs_next_id+2) SHR [Lit 5w;Var sum] [out]] /\
    lookup_block sa.cs_current_bb fn.fn_blocks = SOME bb /\
    (!j. j < LENGTH sb.cs_current_insts ==>
      get_instruction bb j = SOME (EL j sb.cs_current_insts)) /\
    ALL_DISTINCT [len;sum;out] /\
    (!x. not_fresh_at sa x ==> ~MEM x [len;sum;out])
Proof
  simp[compile_bytestring_word_count_def, emit_op_def, emit_inst_def,
    comp_ignore_bind_def, comp_bind_def, comp_return_def, fresh_var_def, fresh_id_def, emit_def] >>
  strip_tac >> gvs[] >> gvs[fn_has_code_def] >>
  qexistsl_tac [`STRING #"%" (toString sa.cs_next_var)`,
    `STRING #"%" (toString (sa.cs_next_var+1))`] >>
  simp[not_fresh_at_def, ALL_DISTINCT] >>
  gvs[IS_PREFIX_APPEND, get_instruction_def] >>
  pure_rewrite_tac[GSYM APPEND_ASSOC] >> simp[EL_APPEND_EQN] >>
  rpt strip_tac >> Cases_on `j < LENGTH sa.cs_current_insts` >- simp[] >>
  `j = LENGTH sa.cs_current_insts \/ j = LENGTH sa.cs_current_insts + 1 \/
   j = LENGTH sa.cs_current_insts + 2` by decide_tac >> gvs[]
QED

Theorem store_slots_clean_shift_counted:
  ~s.vs_halted /\ lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  get_instruction bb s.vs_inst_idx = SOME (mk_inst id SHR [Lit 5w;Var src] [out]) /\
  lookup_var src s = SOME w /\ op_taint tn (Var src) = {} /\
  ~ctx_has_dalloca ctx ==>
  ?Gf tf u.
    gas_path_ptr D 0 ctx fn PG G tn s 0 Gf tf (OK u) /\
    u = (update_var out (w >>> 5) s) with vs_inst_idx := SUC s.vs_inst_idx /\
    lookup_var out u = SOME (w >>> 5) /\ FLOOKUP Gf out = NONE /\ op_taint tf (Var out) = {} /\
    tf.t_mem = tn.t_mem /\ tf.t_imm = tn.t_imm /\ tf.t_stor = tn.t_stor /\ tf.t_trans = tn.t_trans /\
    (!x. x <> out ==> lookup_var x u = lookup_var x s /\
      FLOOKUP Gf x = FLOOKUP G x /\ op_taint tf (Var x) = op_taint tn (Var x))
Proof
  strip_tac >>
  `step_inst_base (mk_inst id SHR [Lit 5w;Var src] [out]) s =
    OK (update_var out (w >>> 5) s)` by
    simp[step_inst_base_opcode_eqs, mk_inst_def, exec_pure2_def, eval_operand_def,
      dimword_def] >>
  `ptr_inst_ok D 0 0 ctx fn G tn (mk_inst id SHR [Lit 5w;Var src] [out]) s` by
    (irule ptr_inst_ok_scalar_builtin >> simp[] >> rpt strip_tac >> gvs[op_taint_def]) >>
  `gas_path_ptr D 0 ctx fn PG G tn s 0
     (step_prov PG G (mk_inst id SHR [Lit 5w;Var src] [out]) (update_var out (w >>> 5) s))
     (step_taint (mk_inst id SHR [Lit 5w;Var src] [out]) s (update_var out (w >>> 5) s) tn)
     (OK ((update_var out (w >>> 5) s) with vs_inst_idx := SUC s.vs_inst_idx))` by
    (irule (SRULE [mk_inst_def, is_terminator_def]
      (Q.INST [`n` |-> `0`, `lo` |-> `0`,
        `i` |-> `mk_inst id SHR [Lit 5w;Var src] [out]`] gas_path_ptr_step)) >>
     simp[GSYM mk_inst_def] >> goal_assum (drule_at Any) >> simp[] >>
     irule (cj 1 gas_path_ptr_rules) >> simp[update_var_def]) >>
  qexistsl_tac [
    `step_prov PG G (mk_inst id SHR [Lit 5w;Var src] [out]) (update_var out (w >>> 5) s)`,
    `step_taint (mk_inst id SHR [Lit 5w;Var src] [out]) s (update_var out (w >>> 5) s) tn`,
    `(update_var out (w >>> 5) s) with vs_inst_idx := SUC s.vs_inst_idx`] >>
  simp[step_prov_def, set_prov_def, out_prov_def, step_taint_def, out_taint_def,
    shift_taint_def, set_var_taint_def, mk_inst_def, eval_operand_def, op_taint_def,
    store_taint_def, imm_taint_def, mem_taint_def, adopt_reset_def,
    step_writes_def, codegenRelTheory.source_memory_write_ranges_def,
    written_taint_def, range_bytes_def, new_site_bytes_def,
    execution_frame_def, update_var_def, lookup_var_def, FLOOKUP_UPDATE, FLOOKUP_DRESTRICT] >>
  gvs[op_taint_def, EXTENSION, FLOOKUP_DEF] >> metis_tac[]
QED

Theorem store_slots_bytestring_count_counted:
  compile_bytestring_word_count (Var root) sa = (Var out,sb) /\ fn_has_code sa sb fn /\
  not_fresh_at sa root /\ lookup_var root s = SOME a /\ ptr_covers G tn root s capacity /\
  32 <= capacity /\ len+63 < dimword (:256) /\ ~ctx_has_dalloca ctx /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\ s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  (!m. mem_agree_outside tn.t_mem s.vs_memory m ==> mem_word_at (w2n a) m = n2w len) ==>
  ?Gf tf u.
    gas_path_ptr D 0 ctx fn PG G tn s 0 Gf tf (OK u) /\
    lookup_var out u = SOME (n2w ((len+63) DIV 32)) /\
    op_taint tf (Var out) = {} /\ FLOOKUP Gf out = NONE /\
    ptr_covers Gf tf root u capacity /\ execution_frame u = execution_frame s /\
    tf.t_mem = tn.t_mem /\ tf.t_imm = tn.t_imm /\ tf.t_stor = tn.t_stor /\ tf.t_trans = tn.t_trans /\
    u.vs_current_bb = sb.cs_current_bb /\ u.vs_inst_idx = LENGTH sb.cs_current_insts /\ ~u.vs_halted /\
    (!x. not_fresh_at sa x ==> lookup_var x u = lookup_var x s /\
      FLOOKUP Gf x = FLOOKUP G x /\ op_taint tf (Var x) = op_taint tn (Var x))
Proof
  strip_tac >> drule_all store_slots_bytestring_count_shape >> strip_tac >>
  rename1 `ALL_DISTINCT [lv;sv;out]` >>
  `root <> lv /\ root <> sv /\ root <> out /\
   ptr_covers G tn root s 32 /\
   lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
   get_instruction bb s.vs_inst_idx = SOME (mk_inst sa.cs_next_id MLOAD [Var root] [lv])` by
    (gvs[ptr_covers_def] >> simp[EL_APPEND_EQN] >> metis_tac[]) >>
  drule_all store_slots_robust_load_counted >>
  disch_then (qspecl_then [`PG`, `D`] strip_assume_tac) >>
  rename1 `gas_path_ptr D 0 ctx fn PG G tn s 0 g1 t1 (OK s1)` >>
  `lookup_block s1.vs_current_bb fn.fn_blocks = SOME bb /\
   get_instruction bb s1.vs_inst_idx = SOME (mk_inst (sa.cs_next_id+1) ADD [Var lv;Lit 63w] [sv]) /\
   eval_operand (Var lv) s1 = SOME (n2w len) /\ eval_operand (Lit 63w) s1 = SOME 63w /\
   op_taint t1 (Lit 63w) = {}` by simp[EL_APPEND_EQN, eval_operand_def, op_taint_def] >>
  drule_all assign_base_storage_add_counted >>
  disch_then (qspecl_then [`g1`, `D`, `PG`] strip_assume_tac) >>
  rename1 `gas_path_ptr D 0 ctx fn PG g1 t1 s1 0 g2 t2 (OK s2)` >>
  `lookup_block s2.vs_current_bb fn.fn_blocks = SOME bb /\
   get_instruction bb s2.vs_inst_idx = SOME (mk_inst (sa.cs_next_id+2) SHR [Lit 5w;Var sv] [out]) /\
   lookup_var sv s2 = SOME (n2w len+63w) /\ ~s2.vs_halted` by
    (gvs[] >> simp[update_var_def, lookup_var_def, FLOOKUP_UPDATE, EL_APPEND_EQN, ADD1]) >>
  drule_all store_slots_clean_shift_counted >>
  disch_then (qspecl_then [`PG`, `g2`, `D`] strip_assume_tac) >>
  rename1 `gas_path_ptr D 0 ctx fn PG g2 t2 s2 0 g3 t3 (OK s3)` >>
  qexistsl_tac [`g3`, `t3`, `s3`] >> conj_tac >-
    (qpat_x_assum `gas_path_ptr _ _ _ _ _ G tn s _ _ _ _`
       (mp_then Any mp_tac gas_path_ptr_then) >> disch_then drule >>
     pure_rewrite_tac [ADD_CLAUSES] >>
     disch_then (mp_then Any mp_tac gas_path_ptr_then) >> disch_then drule >> simp[]) >>
  suspend "resources"
QED

Resume store_slots_bytestring_count_counted[resources]:
  `(n2w len+63w:bytes32) >>> 5 = n2w ((len+63) DIV 32)` by
    (`(len+63) DIV 32 <= len+63` by simp[DIV_LESS_EQ] >>
     `(len+63) DIV 32 < dimword (:256)` by decide_tac >>
     once_rewrite_tac[GSYM w2n_11] >>
     rewrite_tac[word_add_n2w, w2n_lsr, w2n_n2w] >> simp[LESS_MOD]) >>
  `!x. not_fresh_at sa x ==> lookup_var x s3 = lookup_var x s /\
    FLOOKUP g3 x = FLOOKUP G x /\ op_taint t3 (Var x) = op_taint tn (Var x)` by
    (rpt strip_tac >>
     `x <> lv /\ x <> sv /\ x <> out` by metis_tac[MEM] >>
     gvs[lookup_var_def, update_var_def, FLOOKUP_UPDATE] >> metis_tac[]) >>
  `ptr_covers g3 t3 root s3 capacity` by
    (irule ptr_covers_frame >> goal_assum (drule_at Any) >> metis_tac[]) >>
  gvs[execution_frame_def, update_var_def, ADD1]
QED

Finalise store_slots_bytestring_count_counted
