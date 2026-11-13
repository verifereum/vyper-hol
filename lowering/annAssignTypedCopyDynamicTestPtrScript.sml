(* Runtime-register comparisons for dynamic typed-copy traversal. *)
Theory annAssignTypedCopyDynamicTestPtr
Ancestors
  annAssignTypedCopyCountedControlPtr annAssignTypedCopyFixedControlPtr
  assignBasePtrStoragePath assignBasePtrStorageLayout
  exprPtrUnwrapScalarEdges bodyPtrBytestringBuiltinsUintBlocks typedCopyLoopHeaderPtr typedMemoryCopy fragGasPathPtr
  fragGasSeqPtr ptrSafeRun ptrDiscipline bodyPtrDefs venomExecSemantics venomState venomInst
  finite_map pred_set words arithmetic list

Theorem annassign_scalar_register_lt_counted[local]:
  !s fn bb id left right out w tn G ctx D PG.
    ~s.vs_halted /\ lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
    get_instruction bb s.vs_inst_idx =
      SOME (mk_inst id LT [Var left;Var right] [out]) /\
    FLOOKUP G left = NONE /\ FLOOKUP G right = NONE /\
    op_taint tn (Var left) = {} /\ op_taint tn (Var right) = {} /\
    ~ctx_has_dalloca ctx /\
    step_inst_base (mk_inst id LT [Var left;Var right] [out]) s =
      OK (update_var out w s) ==>
    gas_path_ptr D 0 ctx fn PG G tn s 0 (DRESTRICT G (COMPL {out}))
      (tn with t_var := tn.t_var |+ (out,{}))
      (OK (update_var out w s with vs_inst_idx := SUC s.vs_inst_idx))
Proof
  rpt gen_tac >> strip_tac >>
  `ptr_inst_ok D 0 0 ctx fn G tn
    (mk_inst id LT [Var left;Var right] [out]) s` by
    (`left NOTIN FDOM G /\ right NOTIN FDOM G` by gvs[FLOOKUP_DEF] >>
     simp[ptr_inst_ok_def, access_ok_def, taint_ok_def, allocas_from_def,
       mk_inst_def, codegenRelTheory.source_memory_write_ranges_def,
       contextCodegenRelTheory.source_memory_read_ranges_def,
       FLOOKUP_DEF] >>
     simp[GSYM mk_inst_def, step_inst_non_invoke, update_var_def] >>
     metis_tac[]) >>
  `step_prov PG G (mk_inst id LT [Var left;Var right] [out])
     (update_var out w s) = DRESTRICT G (COMPL {out}) /\
   step_taint (mk_inst id LT [Var left;Var right] [out]) s
     (update_var out w s) tn = (tn with t_var := tn.t_var |+ (out,{}))` by
    (irule typed_copy_loop_arith_ghost_clean >> simp[update_var_def]) >>
  mp_tac (Q.GENL [`u`, `G'`, `tn'`, `r`]
    (Q.INST [`n` |-> `0`, `lo` |-> `0`,
      `i` |-> `mk_inst id LT [Var left;Var right] [out]`] gas_path_ptr_step)) >>
  simp[mk_inst_def, is_terminator_def] >>
  disch_then irule >> simp[GSYM mk_inst_def] >>
  gvs[] >> irule (cj 1 gas_path_ptr_rules) >> simp[update_var_def]
QED

Theorem annassign_dynamic_test_exact_counted:
  !s fn bb id ctr bound lt done i n bodylbl exit tn G ctx D PG.
    ~s.vs_halted /\ lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
    get_instruction bb s.vs_inst_idx =
      SOME (mk_inst id LT [Var ctr;Var bound] [lt]) /\
    get_instruction bb (SUC s.vs_inst_idx) =
      SOME (mk_inst (id+1) ISZERO [Var lt] [done]) /\
    get_instruction bb (s.vs_inst_idx+2) =
      SOME (mk_inst (id+2) JNZ [Var done;Label exit;Label bodylbl] []) /\
    lookup_var ctr s = SOME (n2w i) /\ lookup_var bound s = SOME (n2w n) /\
    i <= n /\ n < dimword (:256) /\
    op_taint tn (Var ctr) = {} /\ op_taint tn (Var bound) = {} /\
    FLOOKUP G ctr = NONE /\ FLOOKUP G bound = NONE /\
    ALL_DISTINCT [ctr;lt;done] /\ bound <> lt /\ bound <> done /\
    ~ctx_has_dalloca ctx ==>
    gas_path_ptr D 0 ctx fn PG G tn s 0
      (DRESTRICT (DRESTRICT G (COMPL {lt})) (COMPL {done}))
      (tn with t_var := (tn.t_var |+ (lt,{})) |+ (done,{}))
      (OK (jump_to (if i<n then bodylbl else exit)
        (update_var done (bool_to_word (~(i<n)))
          (update_var lt (bool_to_word (i<n)) s))))
Proof
  rpt gen_tac >> strip_tac >>
  `ctr <> lt /\ ctr <> done` by gvs[ALL_DISTINCT] >>
  `step_inst_base (mk_inst id LT [Var ctr;Var bound] [lt]) s =
    OK (update_var lt (bool_to_word (i<n)) s)` by
    (asm_simp_tac bool_ss [step_inst_base_opcode_eqs,
       mk_inst_def, instruction_accessors, instruction_accfupds,
       combinTheory.K_THM, opcode_case_def] >>
     simp[exec_pure2_def, eval_operand_def, w2n_n2w, LESS_MOD]) >>
  qabbrev_tac `s1 = update_var lt (bool_to_word (i<n)) s
    with vs_inst_idx := SUC s.vs_inst_idx` >>
  qabbrev_tac `g1 = DRESTRICT G (COMPL {lt})` >>
  qabbrev_tac `t1 = tn with t_var := tn.t_var |+ (lt,{})` >>
  `gas_path_ptr D 0 ctx fn PG G tn s 0 g1 t1 (OK s1)` by
    (simp[Abbr `s1`, Abbr `g1`, Abbr `t1`] >>
     irule annassign_scalar_register_lt_counted >> simp[] >>
     goal_assum (drule_at Any) >> simp[]) >>
  qabbrev_tac `s2 = update_var done (bool_to_word (~(i<n))) s1
    with vs_inst_idx := SUC s1.vs_inst_idx` >>
  qabbrev_tac `g2 = DRESTRICT g1 (COMPL {done})` >>
  qabbrev_tac `t2 = t1 with t_var := t1.t_var |+ (done,{})` >>
  `gas_path_ptr D 0 ctx fn PG g1 t1 s1 0 g2 t2 (OK s2)` by
    (simp[Abbr `s2`, Abbr `g2`, Abbr `t2`] >>
     irule assign_base_storage_test_counted >>
     simp[Abbr `s1`, update_var_def] >>
     qexistsl_tac [`id+1`, `ISZERO`, `[Var lt]`] >>
     gvs[Abbr `t1`, update_var_def, lookup_var_def,
         op_taint_def, FLOOKUP_UPDATE] >>
     asm_simp_tac bool_ss [step_inst_base_opcode_eqs, mk_inst_def,
       instruction_accessors, instruction_accfupds, combinTheory.K_THM,
       opcode_case_def] >>
     simp[exec_pure1_def, eval_operand_def, lookup_var_def,
       update_var_def, FLOOKUP_UPDATE, bool_to_word_def] >>
     Cases_on `i<n` >> simp[]) >>
  `gas_path_ptr D 0 ctx fn PG g2 t2 s2 0 g2 t2
    (OK (jump_to (if ~(i<n) then exit else bodylbl) s2))` by
    (irule assign_base_storage_branch_counted >>
     simp[Abbr `s2`, Abbr `s1`, update_var_def] >>
     qexistsl_tac [`id+2`, `Var done`] >>
     simp[Abbr `t2`, eval_operand_def, ADD1,
          lookup_var_def, update_var_def, op_taint_def, FLOOKUP_UPDATE] >>
     Cases_on `i<n` >> simp[bool_to_word_def]) >>
  `gas_path_ptr D 0 ctx fn PG G tn s (0+0+0) g2 t2
    (OK (jump_to (if ~(i<n) then exit else bodylbl) s2))` by
    (metis_tac[gas_path_ptr_then, ADD_CLAUSES]) >>
  gvs[Abbr `g2`, Abbr `g1`, Abbr `t2`, Abbr `t1`,
      Abbr `s2`, Abbr `s1`, jump_to_def, update_var_def] >>
  Cases_on `i<n` >> gvs[]
QED

Theorem annassign_dynamic_test_resources:
  !D ctx fn PG G tn s bb id ctr bound lt done k count bodylbl exit sa off len.
    ~s.vs_halted /\ ~ctx_has_dalloca ctx /\
    lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
    get_instruction bb s.vs_inst_idx =
      SOME (mk_inst id LT [Var ctr;Var bound] [lt]) /\
    get_instruction bb (SUC s.vs_inst_idx) =
      SOME (mk_inst (id+1) ISZERO [Var lt] [done]) /\
    get_instruction bb (s.vs_inst_idx+2) =
      SOME (mk_inst (id+2) JNZ [Var done;Label exit;Label bodylbl] []) /\
    lookup_var ctr s = SOME (n2w k) /\ lookup_var bound s = SOME (n2w count) /\
    op_taint tn (Var ctr) = {} /\ op_taint tn (Var bound) = {} /\
    FLOOKUP G ctr = NONE /\ FLOOKUP G bound = NONE /\
    k <= count /\ count < dimword(:256) /\ ALL_DISTINCT [ctr;lt;done] /\
    bound <> lt /\ bound <> done /\
    (!x. not_fresh_at sa x ==> x <> lt /\ x <> done) ==>
    ?H tm t.
      gas_path_ptr D 0 ctx fn PG G tn s 0 H tm (OK t) /\
      t.vs_current_bb = (if k<count then bodylbl else exit) /\
      t.vs_inst_idx = 0 /\ ~t.vs_halted /\
      lookup_var ctr t = SOME (n2w k) /\ lookup_var bound t = SOME (n2w count) /\
      op_taint tm (Var ctr) = {} /\ op_taint tm (Var bound) = {} /\
      FLOOKUP H ctr = NONE /\ FLOOKUP H bound = NONE /\
      typed_copy_state_frame sa off len s t /\
      t.vs_memory = s.vs_memory /\ tm.t_mem = tn.t_mem /\
      tm.t_stor = tn.t_stor /\ tm.t_trans = tn.t_trans /\ tm.t_imm = tn.t_imm /\
      (!x. x <> lt /\ x <> done ==> lookup_var x t = lookup_var x s /\
        FLOOKUP H x = FLOOKUP G x /\ op_taint tm (Var x) = op_taint tn (Var x))
Proof
  rpt gen_tac >> strip_tac >> rename1 `k <= n` >>
  qexistsl_tac [`DRESTRICT (DRESTRICT G (COMPL {lt})) (COMPL {done})`,
    `tn with t_var := (tn.t_var |+ (lt,{})) |+ (done,{})`,
    `jump_to (if k<n then bodylbl else exit)
      (update_var done (bool_to_word (~(k<n)))
        (update_var lt (bool_to_word (k<n)) s))`] >>
  conj_tac >- (irule annassign_dynamic_test_exact_counted >> simp[] >>
    qexistsl_tac [`bound`,`ctr`,`id`] >> gvs[ALL_DISTINCT]) >>
  gvs[ALL_DISTINCT, jump_to_def, update_var_def, lookup_var_def, FLOOKUP_UPDATE,
       FLOOKUP_DRESTRICT, op_taint_def, typed_copy_state_frame_def,
       typed_copy_frame_def, venom_state_component_equality]
QED

Theorem annassign_dynamic_entry_resources:
  !D ctx fn PG G tn s bb id ctr hdr sa off len.
    ~s.vs_halted /\ ~ctx_has_dalloca ctx /\
    lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
    get_instruction bb s.vs_inst_idx = SOME (mk_inst id ASSIGN [Lit 0w] [ctr]) /\
    get_instruction bb (SUC s.vs_inst_idx) =
      SOME (mk_inst (id+1) JMP [Label hdr] []) /\
    (!x. not_fresh_at sa x ==> x <> ctr) ==>
    ?H tm t.
      gas_path_ptr D 0 ctx fn PG G tn s 0 H tm (OK t) /\
      t.vs_current_bb = hdr /\ t.vs_inst_idx = 0 /\ ~t.vs_halted /\
      lookup_var ctr t = SOME 0w /\ op_taint tm (Var ctr) = {} /\
      FLOOKUP H ctr = NONE /\
      typed_copy_state_frame sa off len s t /\
      t.vs_memory = s.vs_memory /\ tm.t_mem = tn.t_mem /\
      tm.t_stor = tn.t_stor /\ tm.t_trans = tn.t_trans /\ tm.t_imm = tn.t_imm /\
      (!x. x <> ctr ==> lookup_var x t = lookup_var x s /\
        FLOOKUP H x = FLOOKUP G x /\ op_taint tm (Var x) = op_taint tn (Var x))
Proof
  rpt gen_tac >> strip_tac >>
  qexistsl_tac [`DRESTRICT G (COMPL {ctr})`,
    `tn with t_var := tn.t_var |+ (ctr,{})`,
    `jump_to hdr ((update_var ctr 0w s) with vs_inst_idx := SUC s.vs_inst_idx)`] >>
  conj_tac >- (irule assign_base_storage_init_counted >> simp[] >> metis_tac[]) >>
  simp[jump_to_def, update_var_def, lookup_var_def, FLOOKUP_UPDATE,
       FLOOKUP_DRESTRICT, op_taint_def, typed_copy_state_frame_def,
       typed_copy_frame_def, venom_state_component_equality]
QED

Theorem annassign_dynamic_backedge_resources:
  !D ctx fn PG G tn s bb id ctr tmp hdr k sa off len.
    ~s.vs_halted /\ ~ctx_has_dalloca ctx /\
    lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
    get_instruction bb s.vs_inst_idx =
      SOME (mk_inst id ADD [Var ctr;Lit 1w] [tmp]) /\
    get_instruction bb (SUC s.vs_inst_idx) =
      SOME (mk_inst (id+1) ASSIGN [Var tmp] [ctr]) /\
    get_instruction bb (s.vs_inst_idx+2) =
      SOME (mk_inst (id+2) JMP [Label hdr] []) /\
    lookup_var ctr s = SOME (n2w k) /\ op_taint tn (Var ctr) = {} /\
    FLOOKUP G ctr = NONE /\
    ctr <> tmp /\ (!x. not_fresh_at sa x ==> x <> ctr /\ x <> tmp) ==>
    ?H tm t.
      gas_path_ptr D 0 ctx fn PG G tn s 0 H tm (OK t) /\
      t.vs_current_bb = hdr /\ t.vs_inst_idx = 0 /\ ~t.vs_halted /\
      lookup_var ctr t = SOME (n2w (k+1)) /\ op_taint tm (Var ctr) = {} /\
      FLOOKUP H ctr = NONE /\
      typed_copy_state_frame sa off len s t /\
      t.vs_memory = s.vs_memory /\ tm.t_mem = tn.t_mem /\
      tm.t_stor = tn.t_stor /\ tm.t_trans = tn.t_trans /\ tm.t_imm = tn.t_imm /\
      (!x. x <> ctr /\ x <> tmp ==> lookup_var x t = lookup_var x s /\
        FLOOKUP H x = FLOOKUP G x /\ op_taint tm (Var x) = op_taint tn (Var x))
Proof
  rpt gen_tac >> strip_tac >>
  qabbrev_tac `u1 = update_var tmp (n2w (k+1)) s` >>
  qabbrev_tac `s1 = u1 with vs_inst_idx := SUC s.vs_inst_idx` >>
  qabbrev_tac `g1 = step_prov PG G (mk_inst id ADD [Var ctr;Lit 1w] [tmp]) u1` >>
  qabbrev_tac `tn1 = step_taint (mk_inst id ADD [Var ctr;Lit 1w] [tmp]) s u1 tn` >>
  `gas_path_ptr D 0 ctx fn PG G tn s 0 g1 tn1 (OK s1)` by
    (simp[Abbr `s1`, Abbr `g1`, Abbr `tn1`, Abbr `u1`] >>
     irule assign_base_copy_binop_counted >> simp[op_taint_def] >>
     asm_simp_tac bool_ss [step_inst_base_opcode_eqs, mk_inst_def,
       instruction_accessors, instruction_accfupds, combinTheory.K_THM, opcode_case_def] >>
     simp[exec_pure2_def, eval_operand_def, word_add_n2w]) >>
  qabbrev_tac `u2 = update_var ctr (n2w (k+1)) s1` >>
  qabbrev_tac `s2 = u2 with vs_inst_idx := SUC s1.vs_inst_idx` >>
  qabbrev_tac `g2 = step_prov PG g1 (mk_inst (id+1) ASSIGN [Var tmp] [ctr]) u2` >>
  qabbrev_tac `tn2 = step_taint (mk_inst (id+1) ASSIGN [Var tmp] [ctr]) s1 u2 tn1` >>
  `gas_path_ptr_edge D 0 ctx fn PG g1 tn1 s1 0 g2 tn2 (OK s2)` by
    (simp[Abbr `g2`, Abbr `tn2`, Abbr `s2`, Abbr `u2`] >>
     irule bodyPtrBytestringBuiltinsUintBlocksTheory.uint_assign_counted_edge >>
     simp[Abbr `s1`, Abbr `u1`, update_var_def, eval_operand_def,
          lookup_var_def, FLOOKUP_UPDATE]) >>
  `gas_path_ptr D 0 ctx fn PG g2 tn2 s2 0 g2 tn2 (OK (jump_to hdr s2))` by
    (irule assign_base_storage_jump_counted >>
     simp[Abbr `s2`, Abbr `u2`, Abbr `s1`, Abbr `u1`, update_var_def, ADD1] >>
     qexists_tac `id+2` >> simp[]) >>
  `gas_path_ptr D 0 ctx fn PG G tn s 0 g2 tn2 (OK (jump_to hdr s2))` by
    (metis_tac[gas_path_ptr_rules, gas_path_ptr_then, ADD_CLAUSES]) >>
  `FLOOKUP g1 tmp = NONE` by
    (simp[Abbr `g1`, step_prov_def, set_prov_def,
      out_prov_arith_none, op_prov_def, mk_inst_def, FLOOKUP_DRESTRICT]) >>
  `FLOOKUP g2 ctr = NONE` by
    (simp[Abbr `g2`, step_prov_def, set_prov_def,
      out_prov_arith_none, op_prov_def, mk_inst_def, FLOOKUP_DRESTRICT]) >>
  qexistsl_tac [`g2`,`tn2`,`jump_to hdr s2`] >> simp[] >>
  `op_taint tn1 (Var tmp) = {} /\ tn1.t_mem = tn.t_mem /\
   tn1.t_stor = tn.t_stor /\ tn1.t_trans = tn.t_trans /\
   (!x. x <> tmp ==> FLOOKUP g1 x = FLOOKUP G x /\
     op_taint tn1 (Var x) = op_taint tn (Var x))` by
    (simp[Abbr `tn1`, Abbr `g1`, Abbr `u1`,
      typedCopyPtrTheory.copy_len_binop_ghost_frame]) >>
  `op_taint tn2 (Var ctr) = {} /\ tn2.t_mem = tn1.t_mem /\
   tn2.t_stor = tn1.t_stor /\ tn2.t_trans = tn1.t_trans /\
   tn2.t_imm = tn1.t_imm /\
   (!x. x <> ctr ==> FLOOKUP g2 x = FLOOKUP g1 x /\
     op_taint tn2 (Var x) = op_taint tn1 (Var x))` by
    (simp[Abbr `tn2`, Abbr `g2`, Abbr `u2`] >>
     metis_tac[exprPtrUnwrapScalarEdgesTheory.copy_assign_ghost_frame]) >>
  simp[Abbr `s2`, Abbr `u2`, Abbr `s1`, Abbr `u1`, jump_to_def,
    update_var_def, lookup_var_def, FLOOKUP_UPDATE,
    typed_copy_state_frame_def, typed_copy_frame_def] >>
  simp[Abbr `tn1`, step_taint_def, mk_inst_def, set_var_taint_def,
    store_taint_def, adopt_reset_def, step_writes_def, written_taint_def,
    imm_taint_def, mem_taint_def, update_var_def, new_site_bytes_def,
    FLOOKUP_DEF, pred_setTheory.EXTENSION, SF CONJ_ss]
QED
