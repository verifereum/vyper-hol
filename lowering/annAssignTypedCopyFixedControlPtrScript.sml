(* Consumer resource frames for the register-only typed-array loop segments. *)
Theory annAssignTypedCopyFixedControlPtr
Ancestors
  annAssignTypedCopyCountedControlPtr assignBasePtrStorageLayout
  assignBasePtrStoragePath typedMemoryCopy fragGasPathPtr
  exprPtrUnwrapScalarEdges bodyPtrBytestringBuiltinsUintBlocks
  bodyPtrDefs ptrDiscipline venomExecSemantics venomState venomInst
  finite_map words arithmetic list

Theorem annassign_loop_entry_resources:
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

Theorem annassign_loop_test_resources:
  !D ctx fn PG G tn s bb id ctr lt done k count bodylbl exit sa off len.
    ~s.vs_halted /\ ~ctx_has_dalloca ctx /\
    lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
    get_instruction bb s.vs_inst_idx =
      SOME (mk_inst id LT [Var ctr;Lit (n2w count)] [lt]) /\
    get_instruction bb (SUC s.vs_inst_idx) =
      SOME (mk_inst (id+1) ISZERO [Var lt] [done]) /\
    get_instruction bb (s.vs_inst_idx+2) =
      SOME (mk_inst (id+2) JNZ [Var done;Label exit;Label bodylbl] []) /\
    lookup_var ctr s = SOME (n2w k) /\ op_taint tn (Var ctr) = {} /\
    k <= count /\ count < dimword(:256) /\ ALL_DISTINCT [ctr;lt;done] /\
    (!x. not_fresh_at sa x ==> x <> lt /\ x <> done) ==>
    ?H tm t.
      gas_path_ptr D 0 ctx fn PG G tn s 0 H tm (OK t) /\
      t.vs_current_bb = (if k<count then bodylbl else exit) /\
      t.vs_inst_idx = 0 /\ ~t.vs_halted /\
      lookup_var ctr t = SOME (n2w k) /\ op_taint tm (Var ctr) = {} /\
      typed_copy_state_frame sa off len s t /\
      t.vs_memory = s.vs_memory /\ tm.t_mem = tn.t_mem /\
      tm.t_stor = tn.t_stor /\ tm.t_trans = tn.t_trans /\ tm.t_imm = tn.t_imm /\
      (!x. x <> lt /\ x <> done ==> lookup_var x t = lookup_var x s /\
        FLOOKUP H x = FLOOKUP G x /\ op_taint tm (Var x) = op_taint tn (Var x))
Proof
  rpt gen_tac >> strip_tac >>
  rename1 `k <= n` >>
  qexistsl_tac [`DRESTRICT (DRESTRICT G (COMPL {lt})) (COMPL {done})`,
    `tn with t_var := (tn.t_var |+ (lt,{})) |+ (done,{})`,
    `jump_to (if k<n then bodylbl else exit)
      (update_var done (bool_to_word (~(k<n)))
        (update_var lt (bool_to_word (k<n)) s))`] >>
  conj_tac >- (irule annassign_loop_test_exact_counted >> simp[] >>
    qexistsl_tac [`ctr`,`id`] >> gvs[ALL_DISTINCT]) >>
  gvs[ALL_DISTINCT, jump_to_def, update_var_def, lookup_var_def, FLOOKUP_UPDATE,
       FLOOKUP_DRESTRICT, op_taint_def, typed_copy_state_frame_def,
       typed_copy_frame_def, venom_state_component_equality]
QED

Theorem annassign_loop_backedge_resources:
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
    ctr <> tmp /\ (!x. not_fresh_at sa x ==> x <> ctr /\ x <> tmp) ==>
    ?H tm t.
      gas_path_ptr D 0 ctx fn PG G tn s 0 H tm (OK t) /\
      t.vs_current_bb = hdr /\ t.vs_inst_idx = 0 /\ ~t.vs_halted /\
      lookup_var ctr t = SOME (n2w (k+1)) /\ op_taint tm (Var ctr) = {} /\
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
     irule uint_assign_counted_edge >>
     simp[Abbr `s1`, Abbr `u1`, update_var_def, eval_operand_def,
          lookup_var_def, FLOOKUP_UPDATE]) >>
  `gas_path_ptr D 0 ctx fn PG g2 tn2 s2 0 g2 tn2 (OK (jump_to hdr s2))` by
    (irule assign_base_storage_jump_counted >>
     simp[Abbr `s2`, Abbr `u2`, Abbr `s1`, Abbr `u1`, update_var_def, ADD1] >>
     qexists_tac `id+2` >> simp[]) >>
  `gas_path_ptr D 0 ctx fn PG G tn s 0 g2 tn2 (OK (jump_to hdr s2))` by
    (metis_tac[gas_path_ptr_rules, gas_path_ptr_then, ADD_CLAUSES]) >>
  qexistsl_tac [`g2`,`tn2`,`jump_to hdr s2`] >>
  simp[] >>
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
     metis_tac[copy_assign_ghost_frame]) >>
  simp[Abbr `s2`, Abbr `u2`, Abbr `s1`, Abbr `u1`, jump_to_def,
    update_var_def, lookup_var_def, FLOOKUP_UPDATE,
    typed_copy_state_frame_def, typed_copy_frame_def] >>
  simp[Abbr `tn1`, step_taint_def, mk_inst_def, set_var_taint_def,
    store_taint_def, adopt_reset_def, step_writes_def, written_taint_def,
    imm_taint_def, mem_taint_def, update_var_def, new_site_bytes_def,
    FLOOKUP_DEF, pred_setTheory.EXTENSION, SF CONJ_ss]
QED

(* Specialize the address segment's no-write frame to the caller's interval,
   and retain the loop counter alongside the child operand resources. *)
Theorem annassign_loop_address_resources:
  !ctx PG fn D bb sa ctr so doff sp dp sr dr id k ss ds a b S T G tn s off len.
    ~ctx_has_dalloca ctx /\ ~s.vs_halted /\
    lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
    get_instruction bb s.vs_inst_idx =
      SOME (mk_inst id MUL [Var ctr;Lit (n2w ss)] [so]) /\
    get_instruction bb (s.vs_inst_idx+1) =
      SOME (mk_inst (id+1) MUL [Var ctr;Lit (n2w ds)] [doff]) /\
    get_instruction bb (s.vs_inst_idx+2) =
      SOME (mk_inst (id+2) ADD [Var sr;Var so] [sp]) /\
    get_instruction bb (s.vs_inst_idx+3) =
      SOME (mk_inst (id+3) ADD [Var dr;Var doff] [dp]) /\
    lookup_var ctr s = SOME (n2w k) /\ op_taint tn (Var ctr) = {} /\
    lookup_var sr s = SOME a /\ lookup_var dr s = SOME b /\
    ptr_covers G tn sr s S /\ ptr_covers G tn dr s T /\
    ALL_DISTINCT [so;doff;sp;dp] /\
    (!v. MEM v [so;doff;sp;dp] ==> ctr <> v /\ sr <> v /\ dr <> v) /\
    (!v. not_fresh_at sa v ==> ~MEM v [so;doff;sp;dp]) /\
    k*ss < S /\ k*ss+ss <= S /\ k*ds < T /\ k*ds+ds <= T /\
    w2n a+k*ss < dimword(:256) /\ w2n b+k*ds < dimword(:256) ==>
    ?H tm t.
      gas_path_ptr D 0 ctx fn PG G tn s 0 H tm (OK t) /\
      t.vs_current_bb = s.vs_current_bb /\ t.vs_inst_idx = s.vs_inst_idx+4 /\
      ~t.vs_halted /\ lookup_var ctr t = SOME (n2w k) /\
      op_taint tm (Var ctr) = {} /\
      lookup_var sp t = SOME (n2w (w2n a+k*ss)) /\
      lookup_var dp t = SOME (n2w (w2n b+k*ds)) /\
      ptr_covers H tm sp t ss /\ ptr_covers H tm dp t ds /\
      typed_copy_state_frame sa off len s t /\
      t.vs_memory = s.vs_memory /\ tm.t_mem = tn.t_mem /\
      tm.t_stor = tn.t_stor /\ tm.t_trans = tn.t_trans /\ tm.t_imm = tn.t_imm /\
      (!x. ~MEM x [so;doff;sp;dp] ==> lookup_var x t = lookup_var x s /\
        FLOOKUP H x = FLOOKUP G x /\ op_taint tm (Var x) = op_taint tn (Var x))
Proof
  rpt gen_tac >> strip_tac >>
  drule_all annassign_loop_address_counted >>
  disch_then (qspecl_then [`PG`,`D`]
    (qx_choose_then `H` (qx_choose_then `tm` (qx_choose_then `t` strip_assume_tac)))) >>
  qexistsl_tac [`H`,`tm`,`t`] >>
  `~MEM ctr [so;doff;sp;dp]` by (gvs[] >> metis_tac[]) >>
  `typed_copy_state_frame sa off len s t` by
    gvs[typed_copy_state_frame_def, typed_copy_frame_def] >>
  simp[]
QED
