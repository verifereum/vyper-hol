(* Runtime-length memory to storage copies: actual word-element compiler cut. *)
Theory assignTupleDynamicStoragePtr
Ancestors
  assignBasePtrStorageLayout assignBasePtrStorageLoop assignBasePtrStoragePath
  context compileEnv loweringStateRelDefs emitHelper emitHelperProps
  venomInst venomState finite_map list arithmetic ptrSafeRun ptrDiscipline
  venomExecSemantics typedCopyLoopHeaderPtr fragGasPathPtr fragGasSeqPtr stateFrame words

Theorem tuple_dynamic_storage_compile_shape:
  !tr src dst sa z sb.
    compile_dynarray_to_storage src dst 1 32 tr sa = (z,sb) ==>
    ?hdr bodylbl exit len ctr lt done mv off ptr value slot dv nv.
      sb.cs_current_bb = exit /\
      sb.cs_current_insts =
        [mk_inst (sa.cs_next_id+16) (if tr then TSTORE else SSTORE) [dst;Var len] []] /\
      sb.cs_blocks =
        <| bb_label := bodylbl; bb_instructions :=
          [mk_inst (sa.cs_next_id+6) MUL [Var ctr;Lit 32w] [mv];
           mk_inst (sa.cs_next_id+7) ADD [Lit 32w;Var mv] [off];
           mk_inst (sa.cs_next_id+8) ADD [src;Var off] [ptr];
           mk_inst (sa.cs_next_id+9) MLOAD [Var ptr] [value];
           mk_inst (sa.cs_next_id+10) ADD [Var ctr;Lit 1w] [slot];
           mk_inst (sa.cs_next_id+11) ADD [dst;Var slot] [dv];
           mk_inst (sa.cs_next_id+12) (if tr then TSTORE else SSTORE) [Var dv;Var value] [];
           mk_inst (sa.cs_next_id+13) ADD [Var ctr;Lit 1w] [nv];
           mk_inst (sa.cs_next_id+14) ASSIGN [Var nv] [ctr];
           mk_inst (sa.cs_next_id+15) JMP [Label hdr] []] |> ::
        <| bb_label := hdr; bb_instructions :=
          [mk_inst (sa.cs_next_id+3) LT [Var ctr;Var len] [lt];
           mk_inst (sa.cs_next_id+4) ISZERO [Var lt] [done];
           mk_inst (sa.cs_next_id+5) JNZ [Var done;Label exit;Label bodylbl] []] |> ::
        <| bb_label := sa.cs_current_bb; bb_instructions := sa.cs_current_insts ++
          [mk_inst sa.cs_next_id MLOAD [src] [len];
           mk_inst (sa.cs_next_id+1) ASSIGN [Lit 0w] [ctr];
           mk_inst (sa.cs_next_id+2) JMP [Label hdr] []] |> :: sa.cs_blocks /\
      ALL_DISTINCT [len;ctr;lt;done;mv;off;ptr;value;slot;dv;nv] /\
      (!x. not_fresh_at sa x ==>
        ~MEM x [len;ctr;lt;done;mv;off;ptr;value;slot;dv;nv])
Proof
  rpt gen_tac >> Cases_on `tr` >>
  simp[compile_dynarray_to_storage_def, emit_op_def, emit_void_def, emit_inst_def,
    comp_ignore_bind_def, comp_bind_def, comp_return_def, fresh_label_def,
    fresh_var_def, fresh_id_def, emit_def, new_block_def] >> strip_tac >> gvs[] >>
  rpt (goal_assum (drule_at Any)) >>
  simp[mk_inst_def, ALL_DISTINCT, fresh_var_distinct] >>
  rw[not_fresh_at_def] >> first_x_assum irule >> simp[]
QED

(* Unlike the fixed-size loop, the bound operand is a captured register. *)
Theorem tuple_dynamic_lt_counted[local]:
  !s fn bb id left right out w tn G ctx D PG.
    ~s.vs_halted /\ lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
    get_instruction bb s.vs_inst_idx = SOME (mk_inst id LT [left;right] [out]) /\
    op_taint tn left = {} /\ op_taint tn right = {} /\
    op_prov G left = NONE /\ op_prov G right = NONE /\
    ~ctx_has_dalloca ctx /\
    step_inst_base (mk_inst id LT [left;right] [out]) s = OK (update_var out w s) ==>
    gas_path_ptr D 0 ctx fn PG G tn s 0 (DRESTRICT G (COMPL {out}))
      (tn with t_var := tn.t_var |+ (out,{}))
      (OK ((update_var out w s) with vs_inst_idx := SUC s.vs_inst_idx))
Proof
  rpt gen_tac >> strip_tac >>
  `ptr_inst_ok D 0 0 ctx fn G tn (mk_inst id LT [left;right] [out]) s` by
    (simp[ptr_inst_ok_def, access_ok_def, taint_ok_def, allocas_from_def,
       mk_inst_def, codegenRelTheory.source_memory_write_ranges_def,
       contextCodegenRelTheory.source_memory_read_ranges_def] >>
     simp[GSYM mk_inst_def, step_inst_non_invoke] >>
     conj_tac
     >- (rpt gen_tac >> strip_tac >> gvs[op_prov_def, FLOOKUP_DEF]) >>
     metis_tac[]) >>
  `step_prov PG G (mk_inst id LT [left;right] [out]) (update_var out w s) =
      DRESTRICT G (COMPL {out}) /\
   step_taint (mk_inst id LT [left;right] [out]) s (update_var out w s) tn =
      (tn with t_var := tn.t_var |+ (out,{}))` by
    (irule typed_copy_loop_arith_ghost_clean >> simp[update_var_def]) >>
  mp_tac (Q.GENL [`u`, `G'`, `tn'`, `r`]
    (Q.INST [`n` |-> `0`, `lo` |-> `0`,
      `i` |-> `mk_inst id LT [left;right] [out]`] gas_path_ptr_step)) >>
  simp[mk_inst_def, is_terminator_def] >>
  disch_then irule >> simp[GSYM mk_inst_def] >>
  gvs[] >> irule (cj 1 gas_path_ptr_rules) >> simp[update_var_def]
QED

Theorem tuple_dynamic_storage_header_prefix:
  !s fn bb id ctr len lt done i n tn G ctx D PG.
    ~s.vs_halted /\ lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
    get_instruction bb s.vs_inst_idx =
      SOME (mk_inst id LT [Var ctr;Var len] [lt]) /\
    get_instruction bb (SUC s.vs_inst_idx) =
      SOME (mk_inst (id+1) ISZERO [Var lt] [done]) /\
    lookup_var ctr s = SOME (n2w i) /\ lookup_var len s = SOME (n2w n) /\
    i <= n /\ n < dimword (:256) /\
    FLOOKUP G ctr = NONE /\ FLOOKUP G len = NONE /\
    op_taint tn (Var ctr) = {} /\ op_taint tn (Var len) = {} /\
    ALL_DISTINCT [ctr;len;lt;done] /\ ~ctx_has_dalloca ctx ==>
    ?Gf tf u.
      gas_path_ptr D 0 ctx fn PG G tn s 0 Gf tf (OK u) /\
      lookup_var done u = SOME (bool_to_word (~(i<n))) /\
      op_taint tf (Var done) = {} /\
      execution_frame u = execution_frame s /\
      u.vs_accounts = s.vs_accounts /\ u.vs_transient = s.vs_transient /\
      u.vs_call_ctx = s.vs_call_ctx /\ u.vs_memory = s.vs_memory /\
      tf.t_mem = tn.t_mem /\ tf.t_imm = tn.t_imm /\ tf.t_stor = tn.t_stor /\ tf.t_trans = tn.t_trans /\
      u.vs_current_bb = s.vs_current_bb /\ u.vs_inst_idx = s.vs_inst_idx+2 /\ ~u.vs_halted /\
      (!x. x <> lt /\ x <> done ==> lookup_var x u = lookup_var x s /\
        FLOOKUP Gf x = FLOOKUP G x /\ op_taint tf (Var x) = op_taint tn (Var x))
Proof
  rpt gen_tac >> strip_tac >>
  qabbrev_tac `s1 = (update_var lt (bool_to_word (i<n)) s)
    with vs_inst_idx := SUC s.vs_inst_idx` >>
  qabbrev_tac `g1 = DRESTRICT G (COMPL {lt})` >>
  qabbrev_tac `t1 = tn with t_var := tn.t_var |+ (lt,{})` >>
  `step_inst_base (mk_inst id LT [Var ctr;Var len] [lt]) s =
    OK (update_var lt (bool_to_word (i<n)) s)` by
    (asm_simp_tac bool_ss [step_inst_base_opcode_eqs, mk_inst_def, instruction_accessors, instruction_accfupds,
                      combinTheory.K_THM, opcode_case_def] >>
     simp[exec_pure2_def, eval_operand_def, wordsTheory.w2n_n2w, LESS_MOD]) >>
  `gas_path_ptr D 0 ctx fn PG G tn s 0 g1 t1 (OK s1)` by
    (simp[Abbr `s1`, Abbr `g1`, Abbr `t1`] >>
     irule tuple_dynamic_lt_counted >> simp[op_prov_def] >>
     goal_assum (drule_at Any) >> simp[]) >>
  `step_inst_base (mk_inst (id+1) ISZERO [Var lt] [done]) s1 =
     OK (update_var done (bool_to_word (~(i<n))) s1)` by
    (asm_simp_tac bool_ss [step_inst_base_opcode_eqs, mk_inst_def, instruction_accessors, instruction_accfupds,
                      combinTheory.K_THM, opcode_case_def] >>
     simp[Abbr `s1`, exec_pure1_def, eval_operand_def, lookup_var_def,
          execution_frame_def, update_var_def, FLOOKUP_UPDATE, bool_to_word_def] >> Cases_on `i<n` >> simp[]) >>
  `gas_path_ptr D 0 ctx fn PG g1 t1 s1 0 (DRESTRICT g1 (COMPL {done}))
    (t1 with t_var := t1.t_var |+ (done,{}))
    (OK ((update_var done (bool_to_word (~(i<n))) s1) with vs_inst_idx := SUC s1.vs_inst_idx))` by
    (irule assign_base_storage_test_counted >>
     simp[Abbr `s1`, update_var_def] >>
     qexistsl_tac [`id+1`, `ISZERO`, `[Var lt]`] >>
     gvs[Abbr `t1`, execution_frame_def, update_var_def, op_taint_def, FLOOKUP_UPDATE]) >>
  qexistsl_tac [`DRESTRICT g1 (COMPL {done})`, `t1 with t_var := t1.t_var |+ (done,{})`,
    `(update_var done (bool_to_word (~(i<n))) s1) with vs_inst_idx := SUC s1.vs_inst_idx`] >>
  conj_tac >-
    (qpat_x_assum `gas_path_ptr _ _ _ _ _ G tn s _ _ _ _`
       (mp_then Any mp_tac gas_path_ptr_then) >> disch_then drule >> simp[]) >>
  gvs[Abbr `s1`, Abbr `g1`, Abbr `t1`, ALL_DISTINCT, execution_frame_def, update_var_def, lookup_var_def,
      op_taint_def, FLOOKUP_UPDATE, FLOOKUP_DRESTRICT, ADD1]
QED

Theorem tuple_dynamic_storage_header_counted:
  !s fn bb id ctr len lt done i n bodylbl exit tn G ctx D PG.
    ~s.vs_halted /\ lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
    get_instruction bb s.vs_inst_idx = SOME (mk_inst id LT [Var ctr;Var len] [lt]) /\
    get_instruction bb (SUC s.vs_inst_idx) = SOME (mk_inst (id+1) ISZERO [Var lt] [done]) /\
    get_instruction bb (s.vs_inst_idx+2) =
      SOME (mk_inst (id+2) JNZ [Var done;Label exit;Label bodylbl] []) /\
    lookup_var ctr s = SOME (n2w i) /\ lookup_var len s = SOME (n2w n) /\
    i <= n /\ n < dimword (:256) /\
    FLOOKUP G ctr = NONE /\ FLOOKUP G len = NONE /\
    op_taint tn (Var ctr) = {} /\ op_taint tn (Var len) = {} /\
    ALL_DISTINCT [ctr;len;lt;done] /\ ~ctx_has_dalloca ctx ==>
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
  rpt gen_tac >> strip_tac >>
  drule_all tuple_dynamic_storage_header_prefix >>
  disch_then (qspecl_then [`D`, `PG`] mp_tac) >>
  disch_then (qx_choose_then `g1` (qx_choose_then `t1`
    (qx_choose_then `s1` strip_assume_tac))) >>
  `lookup_block s1.vs_current_bb fn.fn_blocks = SOME bb /\
   get_instruction bb s1.vs_inst_idx =
      SOME (mk_inst (id+2) JNZ [Var done;Label exit;Label bodylbl] []) /\
   eval_operand (Var done) s1 = SOME (if ~(i<n) then 1w else 0w)` by
    (simp[eval_operand_def] >> Cases_on `i<n` >> simp[bool_to_word_def]) >>
  drule_all assign_base_storage_branch_counted >>
  disch_then (qspecl_then [`g1`, `D`, `PG`] mp_tac) >> strip_tac >>
  qexistsl_tac [`g1`, `t1`, `jump_to (if ~(i<n) then exit else bodylbl) s1`] >>
  conj_tac >-
    (qpat_x_assum `gas_path_ptr _ _ _ _ _ G tn s _ _ _ _`
       (mp_then Any mp_tac gas_path_ptr_then) >> disch_then drule >> simp[]) >>
  gvs[jump_to_def, lookup_var_def] >> Cases_on `i<n` >> simp[]
QED
