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

Theorem tuple_dynamic_storage_offset_counted:
  !s fn bb id root ctr mv off a i total tn G ctx D PG.
    ~s.vs_halted /\ lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
    get_instruction bb s.vs_inst_idx = SOME (mk_inst id MUL [Var ctr;Lit 32w] [mv]) /\
    get_instruction bb (SUC s.vs_inst_idx) = SOME (mk_inst (id+1) ADD [Lit 32w;Var mv] [off]) /\
    ptr_covers G tn root s total /\ lookup_var root s = SOME a /\
    lookup_var ctr s = SOME (n2w i) /\ op_taint tn (Var ctr) = {} /\
    ALL_DISTINCT [root;ctr;mv;off] /\ ~ctx_has_dalloca ctx ==>
    ?Gf tf u.
      gas_path_ptr D 0 ctx fn PG G tn s 0 Gf tf (OK u) /\
      lookup_var off u = SOME (n2w (32+32*i)) /\ op_taint tf (Var off) = {} /\
      ptr_covers Gf tf root u total /\ lookup_var root u = SOME a /\
      execution_frame u = execution_frame s /\
      u.vs_accounts = s.vs_accounts /\ u.vs_transient = s.vs_transient /\
      u.vs_call_ctx = s.vs_call_ctx /\ u.vs_memory = s.vs_memory /\
      tf.t_mem = tn.t_mem /\ tf.t_imm = tn.t_imm /\ tf.t_stor = tn.t_stor /\ tf.t_trans = tn.t_trans /\
      u.vs_current_bb = s.vs_current_bb /\ u.vs_inst_idx = s.vs_inst_idx+2 /\ ~u.vs_halted /\
      (!x. x <> mv /\ x <> off ==> lookup_var x u = lookup_var x s /\
        FLOOKUP Gf x = FLOOKUP G x /\ op_taint tf (Var x) = op_taint tn (Var x))
Proof
  rpt gen_tac >> strip_tac >>
  `root <> mv /\ ctr <> mv` by gvs[ALL_DISTINCT] >>
  drule_all assign_base_storage_offset_counted >>
  disch_then (qspecl_then [`D`, `PG`] mp_tac) >>
  disch_then (qx_choose_then `g1` (qx_choose_then `t1`
    (qx_choose_then `s1` strip_assume_tac))) >>
  `lookup_block s1.vs_current_bb fn.fn_blocks = SOME bb /\
   get_instruction bb s1.vs_inst_idx = SOME (mk_inst (id+1) ADD [Lit 32w;Var mv] [off]) /\
   eval_operand (Lit 32w) s1 = SOME 32w /\ eval_operand (Var mv) s1 = SOME (n2w (32*i)) /\
   op_taint t1 (Lit 32w) = {}` by simp[eval_operand_def, op_taint_def] >>
  drule_all assign_base_storage_add_counted >>
  disch_then (qspecl_then [`g1`, `D`, `PG`] mp_tac) >>
  disch_then (qx_choose_then `g2` (qx_choose_then `t2`
    (qx_choose_then `s2` strip_assume_tac))) >>
  qexistsl_tac [`g2`, `t2`, `s2`] >>
  conj_tac >-
    (qpat_x_assum `gas_path_ptr _ _ _ _ _ G tn s _ _ _ _`
       (mp_then Any mp_tac gas_path_ptr_then) >> disch_then drule >> simp[]) >>
  gvs[ALL_DISTINCT, execution_frame_def, update_var_def, lookup_var_def,
      FLOOKUP_UPDATE, word_add_n2w, ADD1, bodyPtrDefsTheory.ptr_covers_def] >>
  metis_tac[]
QED

Theorem tuple_dynamic_storage_address_load_counted:
  !s fn bb id root off ptr value a offset total tn G ctx D PG.
    ~s.vs_halted /\ lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
    get_instruction bb s.vs_inst_idx = SOME (mk_inst id ADD [Var root;Var off] [ptr]) /\
    get_instruction bb (SUC s.vs_inst_idx) = SOME (mk_inst (id+1) MLOAD [Var ptr] [value]) /\
    ptr_covers G tn root s total /\ lookup_var root s = SOME a /\
    lookup_var off s = SOME (n2w offset) /\ op_taint tn (Var off) = {} /\
    offset < total /\ offset+32 <= total /\ w2n a+offset < dimword (:256) /\
    ALL_DISTINCT [root;off;ptr;value] /\ ~ctx_has_dalloca ctx ==>
    ?Gf tf u.
      gas_path_ptr D 0 ctx fn PG G tn s 0 Gf tf (OK u) /\
      lookup_var value u = SOME (mload (w2n (a+n2w offset)) s) /\
      op_taint tf (Var value) = mem_word_taint tn.t_mem (w2n (a+n2w offset)) /\
      FLOOKUP Gf value = NONE /\
      execution_frame u = execution_frame s /\
      u.vs_accounts = s.vs_accounts /\ u.vs_transient = s.vs_transient /\
      u.vs_call_ctx = s.vs_call_ctx /\ u.vs_memory = s.vs_memory /\
      tf.t_mem = tn.t_mem /\ tf.t_imm = tn.t_imm /\ tf.t_stor = tn.t_stor /\ tf.t_trans = tn.t_trans /\
      u.vs_current_bb = s.vs_current_bb /\ u.vs_inst_idx = s.vs_inst_idx+2 /\ ~u.vs_halted /\
      (!x. x <> ptr /\ x <> value ==> lookup_var x u = lookup_var x s /\
        FLOOKUP Gf x = FLOOKUP G x /\ op_taint tf (Var x) = op_taint tn (Var x))
Proof
  rpt gen_tac >> strip_tac >>
  rename1 `ALL_DISTINCT [root;off;pvar;value]` >>
  `root <> pvar /\ eval_operand (Var off) s = SOME (n2w offset)` by
    gvs[ALL_DISTINCT, eval_operand_def] >>
  drule_all assign_base_storage_address_counted >>
  disch_then (qspecl_then [`D`, `PG`] mp_tac) >>
  disch_then (qx_choose_then `g1` (qx_choose_then `t1`
    (qx_choose_then `s1` strip_assume_tac))) >>
  `lookup_block s1.vs_current_bb fn.fn_blocks = SOME bb /\
   get_instruction bb s1.vs_inst_idx = SOME (mk_inst (id+1) MLOAD [Var pvar] [value]) /\
   pvar <> value` by gvs[ALL_DISTINCT] >>
  drule_all assign_base_storage_load_counted >>
  disch_then (qspecl_then [`D`, `PG`] mp_tac) >>
  disch_then (qx_choose_then `g2` (qx_choose_then `t2`
    (qx_choose_then `s2` strip_assume_tac))) >>
  qexistsl_tac [`g2`, `t2`, `s2`] >>
  conj_tac >-
    (qpat_x_assum `gas_path_ptr _ _ _ _ _ G tn s _ _ _ _`
       (mp_then Any mp_tac gas_path_ptr_then) >> disch_then drule >> simp[]) >>
  gvs[mload_def, ADD1] >> metis_tac[]
QED

Theorem tuple_dynamic_storage_write_prefix:
  !s fn bb id tr dst ctr slot value dv k i w tn G ctx D PG.
    ~s.vs_halted /\ lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
    get_instruction bb s.vs_inst_idx = SOME (mk_inst id ADD [Var ctr;Lit 1w] [slot]) /\
    get_instruction bb (SUC s.vs_inst_idx) = SOME (mk_inst (id+1) ADD [dst;Var slot] [dv]) /\
    get_instruction bb (s.vs_inst_idx+2) =
      SOME (mk_inst (id+2) (if tr then TSTORE else SSTORE) [Var dv;Var value] []) /\
    eval_operand dst s = SOME k /\ lookup_var ctr s = SOME (n2w i) /\
    lookup_var value s = SOME w /\ op_taint tn dst = {} /\
    op_taint tn (Var ctr) = {} /\ ALL_DISTINCT [ctr;slot;value;dv] /\
    (!x. dst = Var x ==> x <> slot) /\
    ~ctx_has_dalloca ctx /\ ~s.vs_call_ctx.cc_static ==>
    ?Gf tf u.
      gas_path_ptr D 0 ctx fn PG G tn s 0 Gf tf (OK u) /\
      u.vs_memory = s.vs_memory /\ tf.t_mem = tn.t_mem /\ tf.t_imm = tn.t_imm /\
      tf.t_stor = (if tr then tn.t_stor else key_update tn.t_stor (k+n2w (SUC i)) (op_taint tn (Var value))) /\
      tf.t_trans = (if tr then key_update tn.t_trans (k+n2w (SUC i)) (op_taint tn (Var value)) else tn.t_trans) /\
      execution_frame u = execution_frame (if tr then tstore (k+n2w (SUC i)) w s else sstore (k+n2w (SUC i)) w s) /\
      u.vs_accounts = (if tr then s.vs_accounts else (sstore (k+n2w (SUC i)) w s).vs_accounts) /\
      u.vs_transient = (if tr then (tstore (k+n2w (SUC i)) w s).vs_transient else s.vs_transient) /\
      u.vs_current_bb = s.vs_current_bb /\ u.vs_inst_idx = s.vs_inst_idx+3 /\
      u.vs_call_ctx = s.vs_call_ctx /\ ~u.vs_halted /\
      (!x. x <> slot /\ x <> dv ==> lookup_var x u = lookup_var x s /\
        FLOOKUP Gf x = FLOOKUP G x /\ op_taint tf (Var x) = op_taint tn (Var x))
Proof
  rpt gen_tac >> strip_tac >>
  `eval_operand (Var ctr) s = SOME (n2w i) /\
   eval_operand (Lit 1w) s = SOME 1w /\ op_taint tn (Lit 1w) = {}` by
    simp[eval_operand_def, op_taint_def] >>
  drule_all assign_base_storage_add_counted >>
  disch_then (qspecl_then [`G`, `D`, `PG`] mp_tac) >>
  disch_then (qx_choose_then `g1` (qx_choose_then `t1`
    (qx_choose_then `s1` strip_assume_tac))) >>
  `~s1.vs_halted /\ lookup_block s1.vs_current_bb fn.fn_blocks = SOME bb /\
   get_instruction bb s1.vs_inst_idx = SOME (mk_inst (id+1) ADD [dst;Var slot] [dv]) /\
   get_instruction bb (SUC s1.vs_inst_idx) =
     SOME (mk_inst ((id+1)+1) (if tr then TSTORE else SSTORE) [Var dv;Var value] []) /\
   eval_operand dst s1 = SOME k /\ lookup_var slot s1 = SOME (n2w (SUC i)) /\
   lookup_var value s1 = SOME w /\ op_taint t1 dst = {} /\
   dv <> slot /\ dv <> value /\ ~s1.vs_call_ctx.cc_static` by
    (gvs[ALL_DISTINCT, update_var_def, lookup_var_def, FLOOKUP_UPDATE, word_add_n2w, ADD1] >>
     Cases_on `dst` >> gvs[eval_operand_def, op_taint_def, lookup_var_def, FLOOKUP_UPDATE]) >>
  drule_all assign_base_storage_destination_prefix >>
  disch_then (qspecl_then [`g1`, `D`, `PG`] mp_tac) >>
  disch_then (qx_choose_then `g2` (qx_choose_then `t2`
    (qx_choose_then `s2` strip_assume_tac))) >>
  qexistsl_tac [`g2`, `t2`, `s2`] >>
  conj_tac >-
    (qpat_x_assum `gas_path_ptr _ _ _ _ _ G tn s _ _ _ _`
       (mp_then Any mp_tac gas_path_ptr_then) >> disch_then drule >> simp[]) >>
  Cases_on `tr` >>
  gvs[ALL_DISTINCT, execution_frame_def, update_var_def, lookup_var_def, FLOOKUP_UPDATE,
      sstore_def, tstore_def, ADD1] >> metis_tac[]
QED

Theorem tuple_dynamic_storage_load_prefix:
  !s fn bb id root ctr mv off pvar value a i total tn G ctx D PG.
    ~s.vs_halted /\ lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
    get_instruction bb s.vs_inst_idx = SOME (mk_inst id MUL [Var ctr;Lit 32w] [mv]) /\
    get_instruction bb (SUC s.vs_inst_idx) = SOME (mk_inst (id+1) ADD [Lit 32w;Var mv] [off]) /\
    get_instruction bb (s.vs_inst_idx+2) = SOME (mk_inst (id+2) ADD [Var root;Var off] [pvar]) /\
    get_instruction bb (s.vs_inst_idx+3) = SOME (mk_inst (id+3) MLOAD [Var pvar] [value]) /\
    ptr_covers G tn root s total /\ lookup_var root s = SOME a /\
    lookup_var ctr s = SOME (n2w i) /\ op_taint tn (Var ctr) = {} /\
    32+32*i < total /\ 32+32*i+32 <= total /\ w2n a+(32+32*i) < dimword (:256) /\
    ALL_DISTINCT [root;ctr;mv;off;pvar;value] /\ ~ctx_has_dalloca ctx ==>
    ?Gf tf u.
      gas_path_ptr D 0 ctx fn PG G tn s 0 Gf tf (OK u) /\
      lookup_var value u = SOME (mload (w2n (a+n2w (32+32*i))) s) /\
      op_taint tf (Var value) = mem_word_taint tn.t_mem (w2n (a+n2w (32+32*i))) /\
      FLOOKUP Gf value = NONE /\
      execution_frame u = execution_frame s /\
      u.vs_accounts = s.vs_accounts /\ u.vs_transient = s.vs_transient /\
      u.vs_call_ctx = s.vs_call_ctx /\ u.vs_memory = s.vs_memory /\
      tf.t_mem = tn.t_mem /\ tf.t_imm = tn.t_imm /\ tf.t_stor = tn.t_stor /\ tf.t_trans = tn.t_trans /\
      u.vs_current_bb = s.vs_current_bb /\ u.vs_inst_idx = s.vs_inst_idx+4 /\ ~u.vs_halted /\
      (!x. ~MEM x [mv;off;pvar;value] ==> lookup_var x u = lookup_var x s /\
        FLOOKUP Gf x = FLOOKUP G x /\ op_taint tf (Var x) = op_taint tn (Var x))
Proof
  rpt gen_tac >> strip_tac >>
  `ALL_DISTINCT [root;ctr;mv;off]` by gvs[ALL_DISTINCT] >>
  drule_all tuple_dynamic_storage_offset_counted >>
  disch_then (qspecl_then [`D`, `PG`] mp_tac) >>
  disch_then (qx_choose_then `g1` (qx_choose_then `t1`
    (qx_choose_then `s1` strip_assume_tac))) >>
  `lookup_block s1.vs_current_bb fn.fn_blocks = SOME bb /\
   get_instruction bb s1.vs_inst_idx = SOME (mk_inst (id+2) ADD [Var root;Var off] [pvar]) /\
   get_instruction bb (SUC s1.vs_inst_idx) = SOME (mk_inst ((id+2)+1) MLOAD [Var pvar] [value]) /\
   ALL_DISTINCT [root;off;pvar;value]` by gvs[ALL_DISTINCT, ADD1] >>
  drule_all tuple_dynamic_storage_address_load_counted >>
  disch_then (qspecl_then [`D`, `PG`] mp_tac) >>
  disch_then (qx_choose_then `g2` (qx_choose_then `t2`
    (qx_choose_then `s2` strip_assume_tac))) >>
  qexistsl_tac [`g2`, `t2`, `s2`] >>
  conj_tac >-
    (qpat_x_assum `gas_path_ptr _ _ _ _ _ G tn s _ _ _ _`
       (mp_then Any mp_tac gas_path_ptr_then) >> disch_then drule >> simp[]) >>
  gvs[mload_def, ADD1] >> metis_tac[]
QED

Theorem tuple_dynamic_storage_data_prefix:
  !s fn bb id root dst ctr mv off pvar value slot dv a k i total tr tn G ctx D PG.
    ~s.vs_halted /\ lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
    get_instruction bb s.vs_inst_idx = SOME (mk_inst id MUL [Var ctr;Lit 32w] [mv]) /\
    get_instruction bb (SUC s.vs_inst_idx) = SOME (mk_inst (id+1) ADD [Lit 32w;Var mv] [off]) /\
    get_instruction bb (s.vs_inst_idx+2) = SOME (mk_inst (id+2) ADD [Var root;Var off] [pvar]) /\
    get_instruction bb (s.vs_inst_idx+3) = SOME (mk_inst (id+3) MLOAD [Var pvar] [value]) /\
    get_instruction bb (s.vs_inst_idx+4) = SOME (mk_inst (id+4) ADD [Var ctr;Lit 1w] [slot]) /\
    get_instruction bb (s.vs_inst_idx+5) = SOME (mk_inst (id+5) ADD [dst;Var slot] [dv]) /\
    get_instruction bb (s.vs_inst_idx+6) =
      SOME (mk_inst (id+6) (if tr then TSTORE else SSTORE) [Var dv;Var value] []) /\
    ptr_covers G tn root s total /\ lookup_var root s = SOME a /\
    eval_operand dst s = SOME k /\ op_taint tn dst = {} /\
    lookup_var ctr s = SOME (n2w i) /\ op_taint tn (Var ctr) = {} /\
    32+32*i < total /\ 32+32*i+32 <= total /\ w2n a+(32+32*i) < dimword (:256) /\
    ALL_DISTINCT [root;ctr;mv;off;pvar;value;slot;dv] /\
    (!x. dst = Var x ==> ~MEM x [mv;off;pvar;value;slot;dv]) /\
    ~ctx_has_dalloca ctx /\ ~s.vs_call_ctx.cc_static ==>
    ?Gf tf u.
      gas_path_ptr D 0 ctx fn PG G tn s 0 Gf tf (OK u) /\
      u.vs_memory = s.vs_memory /\ tf.t_mem = tn.t_mem /\ tf.t_imm = tn.t_imm /\
      tf.t_stor = (if tr then tn.t_stor else key_update tn.t_stor (k+n2w (SUC i))
        (mem_word_taint tn.t_mem (w2n (a+n2w (32+32*i))))) /\
      tf.t_trans = (if tr then key_update tn.t_trans (k+n2w (SUC i))
        (mem_word_taint tn.t_mem (w2n (a+n2w (32+32*i)))) else tn.t_trans) /\
      execution_frame u = execution_frame
        (if tr then tstore (k+n2w (SUC i)) (mload (w2n (a+n2w (32+32*i))) s) s
         else sstore (k+n2w (SUC i)) (mload (w2n (a+n2w (32+32*i))) s) s) /\
      u.vs_accounts = (if tr then s.vs_accounts else
        (sstore (k+n2w (SUC i)) (mload (w2n (a+n2w (32+32*i))) s) s).vs_accounts) /\
      u.vs_transient = (if tr then
        (tstore (k+n2w (SUC i)) (mload (w2n (a+n2w (32+32*i))) s) s).vs_transient else s.vs_transient) /\
      u.vs_current_bb = s.vs_current_bb /\ u.vs_inst_idx = s.vs_inst_idx+7 /\
      u.vs_call_ctx = s.vs_call_ctx /\ ~u.vs_halted /\
      (!x. ~MEM x [mv;off;pvar;value;slot;dv] ==> lookup_var x u = lookup_var x s /\
        FLOOKUP Gf x = FLOOKUP G x /\ op_taint tf (Var x) = op_taint tn (Var x))
Proof
  rpt gen_tac >> strip_tac >>
  `ALL_DISTINCT [root;ctr;mv;off;pvar;value]` by gvs[ALL_DISTINCT] >>
  drule_all tuple_dynamic_storage_load_prefix >>
  disch_then (qspecl_then [`D`, `PG`] mp_tac) >>
  disch_then (qx_choose_then `g1` (qx_choose_then `t1`
    (qx_choose_then `s1` strip_assume_tac))) >>
  `lookup_block s1.vs_current_bb fn.fn_blocks = SOME bb /\
   get_instruction bb s1.vs_inst_idx = SOME (mk_inst (id+4) ADD [Var ctr;Lit 1w] [slot]) /\
   get_instruction bb (SUC s1.vs_inst_idx) = SOME (mk_inst ((id+4)+1) ADD [dst;Var slot] [dv]) /\
   get_instruction bb (s1.vs_inst_idx+2) =
     SOME (mk_inst ((id+4)+2) (if tr then TSTORE else SSTORE) [Var dv;Var value] []) /\
   eval_operand dst s1 = SOME k /\ op_taint t1 dst = {} /\
   lookup_var ctr s1 = SOME (n2w i) /\ op_taint t1 (Var ctr) = {} /\
   ALL_DISTINCT [ctr;slot;value;dv] /\ (!x. dst = Var x ==> x <> slot) /\
   ~s1.vs_call_ctx.cc_static` by
    (gvs[ALL_DISTINCT, ADD1] >> Cases_on `dst` >>
     gvs[eval_operand_def, op_taint_def] >> metis_tac[]) >>
  drule_all tuple_dynamic_storage_write_prefix >>
  disch_then (qspecl_then [`g1`, `D`, `PG`] mp_tac) >>
  disch_then (qx_choose_then `g2` (qx_choose_then `t2`
    (qx_choose_then `s2` strip_assume_tac))) >>
  qexistsl_tac [`g2`, `t2`, `s2`] >>
  conj_tac >-
    (qpat_x_assum `gas_path_ptr _ _ _ _ _ G tn s _ _ _ _`
       (mp_then Any mp_tac gas_path_ptr_then) >> disch_then drule >> simp[]) >>
  Cases_on `tr` >> gvs[execution_frame_def, sstore_def, tstore_def, mload_def] >> metis_tac[]
QED

Theorem tuple_dynamic_storage_body_counted:
  !s fn bb id root dst ctr mv off pvar value slot dv nv a k i total tr hdr tn G ctx D PG.
    ~s.vs_halted /\ lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
    get_instruction bb s.vs_inst_idx = SOME (mk_inst id MUL [Var ctr;Lit 32w] [mv]) /\
    get_instruction bb (SUC s.vs_inst_idx) = SOME (mk_inst (id+1) ADD [Lit 32w;Var mv] [off]) /\
    get_instruction bb (s.vs_inst_idx+2) = SOME (mk_inst (id+2) ADD [Var root;Var off] [pvar]) /\
    get_instruction bb (s.vs_inst_idx+3) = SOME (mk_inst (id+3) MLOAD [Var pvar] [value]) /\
    get_instruction bb (s.vs_inst_idx+4) = SOME (mk_inst (id+4) ADD [Var ctr;Lit 1w] [slot]) /\
    get_instruction bb (s.vs_inst_idx+5) = SOME (mk_inst (id+5) ADD [dst;Var slot] [dv]) /\
    get_instruction bb (s.vs_inst_idx+6) =
      SOME (mk_inst (id+6) (if tr then TSTORE else SSTORE) [Var dv;Var value] []) /\
    get_instruction bb (s.vs_inst_idx+7) = SOME (mk_inst (id+7) ADD [Var ctr;Lit 1w] [nv]) /\
    get_instruction bb (s.vs_inst_idx+8) = SOME (mk_inst (id+8) ASSIGN [Var nv] [ctr]) /\
    get_instruction bb (s.vs_inst_idx+9) = SOME (mk_inst (id+9) JMP [Label hdr] []) /\
    ptr_covers G tn root s total /\ lookup_var root s = SOME a /\
    eval_operand dst s = SOME k /\ op_taint tn dst = {} /\
    lookup_var ctr s = SOME (n2w i) /\ op_taint tn (Var ctr) = {} /\ FLOOKUP G ctr = NONE /\
    32+32*i < total /\ 32+32*i+32 <= total /\ w2n a+(32+32*i) < dimword (:256) /\
    ALL_DISTINCT [root;ctr;mv;off;pvar;value;slot;dv;nv] /\
    (!x. dst = Var x ==> ~MEM x [ctr;mv;off;pvar;value;slot;dv;nv]) /\
    ~ctx_has_dalloca ctx /\ ~s.vs_call_ctx.cc_static ==>
    ?Gf tf u.
      gas_path_ptr D 0 ctx fn PG G tn s 0 Gf tf (OK u) /\
      lookup_var ctr u = SOME (n2w (SUC i)) /\ FLOOKUP Gf ctr = NONE /\ op_taint tf (Var ctr) = {} /\
      u.vs_memory = s.vs_memory /\ tf.t_mem = tn.t_mem /\ tf.t_imm = tn.t_imm /\
      tf.t_stor = (if tr then tn.t_stor else key_update tn.t_stor (k+n2w (SUC i))
        (mem_word_taint tn.t_mem (w2n (a+n2w (32+32*i))))) /\
      tf.t_trans = (if tr then key_update tn.t_trans (k+n2w (SUC i))
        (mem_word_taint tn.t_mem (w2n (a+n2w (32+32*i)))) else tn.t_trans) /\
      execution_frame u = execution_frame
        (if tr then tstore (k+n2w (SUC i)) (mload (w2n (a+n2w (32+32*i))) s) s
         else sstore (k+n2w (SUC i)) (mload (w2n (a+n2w (32+32*i))) s) s) /\
      u.vs_accounts = (if tr then s.vs_accounts else
        (sstore (k+n2w (SUC i)) (mload (w2n (a+n2w (32+32*i))) s) s).vs_accounts) /\
      u.vs_transient = (if tr then
        (tstore (k+n2w (SUC i)) (mload (w2n (a+n2w (32+32*i))) s) s).vs_transient else s.vs_transient) /\
      u.vs_current_bb = hdr /\ u.vs_inst_idx = 0 /\
      u.vs_call_ctx = s.vs_call_ctx /\ ~u.vs_halted /\
      (!x. ~MEM x [ctr;mv;off;pvar;value;slot;dv;nv] ==> lookup_var x u = lookup_var x s /\
        FLOOKUP Gf x = FLOOKUP G x /\ op_taint tf (Var x) = op_taint tn (Var x))
Proof
  rpt gen_tac >> strip_tac >>
  `ALL_DISTINCT [root;ctr;mv;off;pvar;value;slot;dv] /\
   (!x. dst = Var x ==> ~MEM x [mv;off;pvar;value;slot;dv]) /\ ctr <> nv` by
    (gvs[ALL_DISTINCT] >> metis_tac[]) >>
  drule_all tuple_dynamic_storage_data_prefix >>
  disch_then (qspecl_then [`D`, `PG`] mp_tac) >>
  disch_then (qx_choose_then `g1` (qx_choose_then `t1`
    (qx_choose_then `s1` strip_assume_tac))) >>
  `lookup_block s1.vs_current_bb fn.fn_blocks = SOME bb /\
   get_instruction bb s1.vs_inst_idx = SOME (mk_inst (id+7) ADD [Var ctr;Lit 1w] [nv]) /\
   get_instruction bb (SUC s1.vs_inst_idx) = SOME (mk_inst ((id+7)+1) ASSIGN [Var nv] [ctr]) /\
   lookup_var ctr s1 = SOME (n2w i) /\ FLOOKUP g1 ctr = NONE /\ op_taint t1 (Var ctr) = {}` by
    gvs[ALL_DISTINCT, ADD1] >>
  drule_all assign_base_storage_increment_prefix >>
  disch_then (qspecl_then [`D`, `PG`] mp_tac) >>
  disch_then (qx_choose_then `g2` (qx_choose_then `t2`
    (qx_choose_then `s2` strip_assume_tac))) >>
  `lookup_block s2.vs_current_bb fn.fn_blocks = SOME bb /\
   get_instruction bb s2.vs_inst_idx = SOME (mk_inst (id+9) JMP [Label hdr] [])` by simp[] >>
  drule_all assign_base_storage_jump_counted >>
  disch_then (qspecl_then [`t2`, `g2`, `D`, `PG`] mp_tac) >> strip_tac >>
  qexistsl_tac [`g2`, `t2`, `jump_to hdr s2`] >> conj_tac >-
    (qpat_x_assum `gas_path_ptr _ _ _ _ _ G tn s _ _ _ _`
      (mp_then Any mp_tac gas_path_ptr_then) >> disch_then drule >> simp[] >>
     disch_then (mp_then Any mp_tac gas_path_ptr_then) >> disch_then drule >> simp[]) >>
  gvs[jump_to_def, lookup_var_def, ALL_DISTINCT] >> metis_tac[]
QED

Theorem tuple_dynamic_storage_frame_advance:
  assign_base_store_frame (if tr then LocTransient else LocStorage)
    (a+32w) (k+1w) s0 tn0 i s tn /\
  u.vs_accounts = (if tr then s.vs_accounts else
    (sstore (k+n2w (SUC i)) (mload (w2n (a+n2w (32+32*i))) s) s).vs_accounts) /\
  u.vs_transient = (if tr then
    (tstore (k+n2w (SUC i)) (mload (w2n (a+n2w (32+32*i))) s) s).vs_transient else s.vs_transient) /\
  u.vs_memory = s.vs_memory /\ u.vs_call_ctx = s.vs_call_ctx /\
  tf.t_stor = (if tr then tn.t_stor else key_update tn.t_stor (k+n2w (SUC i))
    (mem_word_taint tn.t_mem (w2n (a+n2w (32+32*i))))) /\
  tf.t_trans = (if tr then key_update tn.t_trans (k+n2w (SUC i))
    (mem_word_taint tn.t_mem (w2n (a+n2w (32+32*i)))) else tn.t_trans) /\
  tf.t_mem = tn.t_mem /\ tf.t_imm = tn.t_imm ==>
  assign_base_store_frame (if tr then LocTransient else LocStorage)
    (a+32w) (k+1w) s0 tn0 (SUC i) u tf
Proof
  strip_tac >> irule assign_base_store_frame_advance >>
  simp[word_add_n2w, GSYM WORD_ADD_ASSOC, ADD1] >>
  goal_assum (drule_at Any) >> simp[]
QED

Theorem tuple_dynamic_storage_loop_remaining[local]:
  !remaining i s G tn.
    i+remaining = n /\ n < dimword (:256) /\ 32+32*n <= capacity /\
    w2n a+32+32*n < dimword (:256) /\ ~ctx_has_dalloca ctx /\
    ~s0.vs_call_ctx.cc_static /\
    lookup_block hdr fn.fn_blocks = SOME hb /\
    lookup_block bodylbl fn.fn_blocks = SOME bb /\
    get_instruction hb 0 = SOME (mk_inst hid LT [Var ctr;Var len] [lt]) /\
    get_instruction hb 1 = SOME (mk_inst (hid+1) ISZERO [Var lt] [done]) /\
    get_instruction hb 2 = SOME (mk_inst (hid+2) JNZ [Var done;Label exit;Label bodylbl] []) /\
    get_instruction bb 0 = SOME (mk_inst bid MUL [Var ctr;Lit 32w] [mv]) /\
    get_instruction bb 1 = SOME (mk_inst (bid+1) ADD [Lit 32w;Var mv] [off]) /\
    get_instruction bb 2 = SOME (mk_inst (bid+2) ADD [Var root;Var off] [pvar]) /\
    get_instruction bb 3 = SOME (mk_inst (bid+3) MLOAD [Var pvar] [value]) /\
    get_instruction bb 4 = SOME (mk_inst (bid+4) ADD [Var ctr;Lit 1w] [slot]) /\
    get_instruction bb 5 = SOME (mk_inst (bid+5) ADD [dst;Var slot] [dv]) /\
    get_instruction bb 6 = SOME (mk_inst (bid+6) (if tr then TSTORE else SSTORE) [Var dv;Var value] []) /\
    get_instruction bb 7 = SOME (mk_inst (bid+7) ADD [Var ctr;Lit 1w] [nv]) /\
    get_instruction bb 8 = SOME (mk_inst (bid+8) ASSIGN [Var nv] [ctr]) /\
    get_instruction bb 9 = SOME (mk_inst (bid+9) JMP [Label hdr] []) /\
    ALL_DISTINCT [root;len;ctr;lt;done;mv;off;pvar;value;slot;dv;nv] /\
    (!x. dst = Var x ==> ~MEM x [ctr;lt;done;mv;off;pvar;value;slot;dv;nv]) /\
    assign_base_store_frame (if tr then LocTransient else LocStorage)
      (a+32w) (k+1w) s0 tn0 i s tn /\
    ptr_covers G tn root s capacity /\ lookup_var root s = SOME a /\
    eval_operand dst s = SOME k /\ op_taint tn dst = {} /\
    lookup_var len s = SOME (n2w n) /\ FLOOKUP G len = NONE /\ op_taint tn (Var len) = {} /\
    lookup_var ctr s = SOME (n2w i) /\ FLOOKUP G ctr = NONE /\ op_taint tn (Var ctr) = {} /\
    s.vs_current_bb = hdr /\ s.vs_inst_idx = 0 /\ ~s.vs_halted ==>
    ?Gf tf u.
      gas_path_ptr D 0 ctx fn PG G tn s 0 Gf tf (OK u) /\
      assign_base_store_frame (if tr then LocTransient else LocStorage)
        (a+32w) (k+1w) s0 tn0 n u tf /\
      ptr_covers Gf tf root u capacity /\ lookup_var root u = SOME a /\
      eval_operand dst u = SOME k /\ op_taint tf dst = {} /\
      lookup_var len u = SOME (n2w n) /\ FLOOKUP Gf len = NONE /\ op_taint tf (Var len) = {} /\
      lookup_var ctr u = SOME (n2w n) /\ FLOOKUP Gf ctr = NONE /\ op_taint tf (Var ctr) = {} /\
      u.vs_current_bb = exit /\ u.vs_inst_idx = 0 /\ ~u.vs_halted /\
      (!x. ~MEM x [ctr;lt;done;mv;off;pvar;value;slot;dv;nv] ==>
        lookup_var x u = lookup_var x s /\ FLOOKUP Gf x = FLOOKUP G x /\
        op_taint tf (Var x) = op_taint tn (Var x))
Proof
  Induct_on `remaining` >> rpt gen_tac >> strip_tac >>
  `i<=n /\ ALL_DISTINCT [ctr;len;lt;done] /\
   lookup_block s.vs_current_bb fn.fn_blocks = SOME hb /\
   get_instruction hb s.vs_inst_idx = SOME (mk_inst hid LT [Var ctr;Var len] [lt]) /\
   get_instruction hb (SUC s.vs_inst_idx) = SOME (mk_inst (hid+1) ISZERO [Var lt] [done]) /\
   get_instruction hb (s.vs_inst_idx+2) = SOME (mk_inst (hid+2) JNZ [Var done;Label exit;Label bodylbl] [])` by
    (gvs[ALL_DISTINCT] >> decide_tac) >>
  drule_all tuple_dynamic_storage_header_counted >>
  disch_then (qspecl_then [`D`, `PG`] mp_tac) >>
  disch_then (qx_choose_then `g1` (qx_choose_then `t1`
    (qx_choose_then `s1` strip_assume_tac))) >>
  `assign_base_store_frame (if tr then LocTransient else LocStorage)
     (a+32w) (k+1w) s0 tn0 i s1 t1` by
    metis_tac[assign_base_store_frame_preserve] >>
  `ptr_covers g1 t1 root s1 capacity /\ lookup_var root s1 = SOME a` by
    (irule assign_base_store_root_transport >> qexistsl_tac [`G`, `s`, `tn`] >> simp[] >> gvs[ALL_DISTINCT]) >>
  `eval_operand dst s1 = SOME k /\ op_taint t1 dst = {}` by
    (Cases_on `dst` >> gvs[eval_operand_def, op_taint_def] >> metis_tac[]) >>
  `lookup_var len s1 = SOME (n2w n) /\ FLOOKUP g1 len = NONE /\ op_taint t1 (Var len) = {} /\
   lookup_var ctr s1 = SOME (n2w i) /\ FLOOKUP g1 ctr = NONE /\ op_taint t1 (Var ctr) = {}` by
    gvs[ALL_DISTINCT] >-
  (qexistsl_tac [`g1`, `t1`, `s1`] >> gvs[] >> metis_tac[]) >>
  `i<n /\ ~s1.vs_call_ctx.cc_static /\
   32+32*i < capacity /\ 32+32*i+32 <= capacity /\
   w2n a+(32+32*i) < dimword (:256) /\
   ALL_DISTINCT [root;ctr;mv;off;pvar;value;slot;dv;nv] /\
   (!x. dst = Var x ==> ~MEM x [ctr;mv;off;pvar;value;slot;dv;nv])` by
    (gvs[assign_base_store_frame_def, ALL_DISTINCT] >> decide_tac) >>
  `lookup_block s1.vs_current_bb fn.fn_blocks = SOME bb /\
   get_instruction bb s1.vs_inst_idx = SOME (mk_inst bid MUL [Var ctr;Lit 32w] [mv]) /\
   get_instruction bb (SUC s1.vs_inst_idx) = SOME (mk_inst (bid+1) ADD [Lit 32w;Var mv] [off]) /\
   get_instruction bb (s1.vs_inst_idx+2) = SOME (mk_inst (bid+2) ADD [Var root;Var off] [pvar]) /\
   get_instruction bb (s1.vs_inst_idx+3) = SOME (mk_inst (bid+3) MLOAD [Var pvar] [value]) /\
   get_instruction bb (s1.vs_inst_idx+4) = SOME (mk_inst (bid+4) ADD [Var ctr;Lit 1w] [slot]) /\
   get_instruction bb (s1.vs_inst_idx+5) = SOME (mk_inst (bid+5) ADD [dst;Var slot] [dv]) /\
   get_instruction bb (s1.vs_inst_idx+6) = SOME (mk_inst (bid+6) (if tr then TSTORE else SSTORE) [Var dv;Var value] []) /\
   get_instruction bb (s1.vs_inst_idx+7) = SOME (mk_inst (bid+7) ADD [Var ctr;Lit 1w] [nv]) /\
   get_instruction bb (s1.vs_inst_idx+8) = SOME (mk_inst (bid+8) ASSIGN [Var nv] [ctr]) /\
   get_instruction bb (s1.vs_inst_idx+9) = SOME (mk_inst (bid+9) JMP [Label hdr] [])` by simp[] >>
  drule_all tuple_dynamic_storage_body_counted >>
  disch_then (qspecl_then [`D`, `PG`] mp_tac) >>
  disch_then (qx_choose_then `g2` (qx_choose_then `t2`
    (qx_choose_then `s2` strip_assume_tac))) >>
  `assign_base_store_frame (if tr then LocTransient else LocStorage)
     (a+32w) (k+1w) s0 tn0 (SUC i) s2 t2` by
    (irule tuple_dynamic_storage_frame_advance >>
     qexistsl_tac [`s1`, `t1`] >> simp[]) >>
  `ptr_covers g2 t2 root s2 capacity /\ lookup_var root s2 = SOME a` by
    (irule assign_base_store_root_transport >> qexistsl_tac [`g1`, `s1`, `t1`] >>
     simp[] >> gvs[ALL_DISTINCT]) >>
  `s2.vs_labels = s1.vs_labels` by
    (qpat_x_assum `execution_frame s2 = _` mp_tac >>
     Cases_on `tr` >> simp[execution_frame_def, sstore_def, tstore_def] >> metis_tac[]) >>
  `eval_operand dst s2 = SOME k /\ op_taint t2 dst = {}` by
    (qpat_x_assum `!i s G tn. _` kall_tac >>
     qpat_x_assum `eval_operand dst s1 = _` mp_tac >>
     qpat_x_assum `op_taint t1 dst = _` mp_tac >>
     Cases_on `dst` >> simp[eval_operand_def, op_taint_def] >> metis_tac[op_taint_def]) >>
  `lookup_var len s2 = SOME (n2w n) /\ FLOOKUP g2 len = NONE /\ op_taint t2 (Var len) = {}` by
    gvs[ALL_DISTINCT] >>
  `SUC i+remaining=n` by decide_tac >>
  first_x_assum (qspecl_then [`SUC i`, `s2`, `g2`, `t2`] mp_tac) >>
  asm_rewrite_tac[] >>
  disch_then (qx_choose_then `gf` (qx_choose_then `tf`
    (qx_choose_then `u` strip_assume_tac))) >>
  qexistsl_tac [`gf`, `tf`, `u`] >> conj_tac >-
    (qpat_x_assum `gas_path_ptr _ _ _ _ _ G tn s _ _ _ _`
      (mp_then Any mp_tac gas_path_ptr_then) >> disch_then drule >> simp[] >>
     disch_then (mp_then Any mp_tac gas_path_ptr_then) >> disch_then drule >> simp[]) >>
  asm_rewrite_tac[] >> simp[] >> metis_tac[]
QED

Theorem tuple_dynamic_storage_init_counted:
  !s fn bb id root len ctr hdr a n capacity tn G ctx D PG loc k.
    ~s.vs_halted /\ lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
    get_instruction bb s.vs_inst_idx = SOME (mk_inst id MLOAD [Var root] [len]) /\
    get_instruction bb (SUC s.vs_inst_idx) = SOME (mk_inst (id+1) ASSIGN [Lit 0w] [ctr]) /\
    get_instruction bb (s.vs_inst_idx+2) = SOME (mk_inst (id+2) JMP [Label hdr] []) /\
    ALL_DISTINCT [root;len;ctr] /\ ~ctx_has_dalloca ctx /\
    ptr_covers G tn root s capacity /\ 32 <= capacity /\ lookup_var root s = SOME a /\
    mload (w2n a) s = n2w n /\ mem_word_taint tn.t_mem (w2n a) = {} ==>
    ?Gf tf u.
      gas_path_ptr D 0 ctx fn PG G tn s 0 Gf tf (OK u) /\
      execution_frame u = execution_frame s /\
      assign_base_store_frame loc (a+32w) (k+1w) s tn 0 u tf /\
      ptr_covers Gf tf root u capacity /\ lookup_var root u = SOME a /\
      lookup_var len u = SOME (n2w n) /\ FLOOKUP Gf len = NONE /\ op_taint tf (Var len) = {} /\
      lookup_var ctr u = SOME 0w /\ FLOOKUP Gf ctr = NONE /\ op_taint tf (Var ctr) = {} /\
      u.vs_current_bb = hdr /\ u.vs_inst_idx = 0 /\ ~u.vs_halted /\
      (!x. ~MEM x [len;ctr] ==> lookup_var x u = lookup_var x s /\
        FLOOKUP Gf x = FLOOKUP G x /\ op_taint tf (Var x) = op_taint tn (Var x))
Proof
  rpt gen_tac >> strip_tac >>
  `ptr_covers G tn root s 32 /\ root <> len` by
    (gvs[bodyPtrDefsTheory.ptr_covers_def, ALL_DISTINCT] >> decide_tac) >>
  drule_all assign_base_mload_counted >>
  disch_then (qspecl_then [`D`, `PG`] mp_tac) >>
  `eval_operand (Var root) s = SOME a` by simp[eval_operand_def] >>
  drule assign_base_mload_ghost >>
  disch_then (qspecl_then [`PG`, `G`, `tn`, `id`, `len`] assume_tac) >>
  strip_tac >> gvs[] >>
  qmatch_asmsub_abbrev_tac `gas_path_ptr D 0 ctx fn PG G tn s 0 g1 t1 (OK s1)` >>
  `~s1.vs_halted /\ lookup_block s1.vs_current_bb fn.fn_blocks = SOME bb /\
   get_instruction bb s1.vs_inst_idx = SOME (mk_inst (id+1) ASSIGN [Lit 0w] [ctr]) /\
   get_instruction bb (SUC s1.vs_inst_idx) = SOME (mk_inst ((id+1)+1) JMP [Label hdr] [])` by
    (simp[Abbr `s1`, update_var_def] >> gvs[ADD1]) >>
  drule_all assign_base_storage_init_counted >>
  disch_then (qspecl_then [`t1`, `g1`, `D`, `PG`] assume_tac) >>
  qexistsl_tac [`DRESTRICT g1 (COMPL {ctr})`, `t1 with t_var := t1.t_var |+ (ctr,{})`,
    `jump_to hdr ((update_var ctr 0w s1) with vs_inst_idx := SUC s1.vs_inst_idx)`] >>
  conj_tac >-
    (qpat_x_assum `gas_path_ptr _ _ _ _ _ G tn s _ _ _ _`
      (mp_then Any mp_tac gas_path_ptr_then) >> disch_then drule >> simp[]) >>
  simp[Abbr `g1`, Abbr `t1`, Abbr `s1`, assign_base_store_frame_def,
    assign_base_store_prefix_zero, assign_base_store_taint_prefix_def,
    execution_frame_def, jump_to_def, update_var_def, lookup_var_def,
    FLOOKUP_UPDATE, FLOOKUP_DRESTRICT, op_taint_def] >>
  gvs[bodyPtrDefsTheory.ptr_covers_def, ALL_DISTINCT, lookup_var_def, op_taint_def,
    FLOOKUP_UPDATE, FLOOKUP_DRESTRICT]
QED

Theorem tuple_dynamic_storage_compiled_counted:
  !tr root dst sa z sb fn s G tn ctx D PG a k n capacity.
    compile_dynarray_to_storage (Var root) dst 1 32 tr sa = (z,sb) /\
    fn_has_code sa sb fn /\ not_fresh_at sa root /\
    (!x. dst = Var x ==> not_fresh_at sa x) /\
    ptr_covers G tn root s capacity /\ lookup_var root s = SOME a /\
    eval_operand dst s = SOME k /\ op_taint tn dst = {} /\
    mload (w2n a) s = n2w n /\ mem_word_taint tn.t_mem (w2n a) = {} /\
    n < dimword (:256) /\ 32+32*n <= capacity /\
    w2n a+32+32*n < dimword (:256) /\
    ~s.vs_halted /\ ~s.vs_call_ctx.cc_static /\ ~ctx_has_dalloca ctx /\
    s.vs_current_bb = sa.cs_current_bb /\ s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
    ?Gf tf u v tv.
      gas_path_ptr D 0 ctx fn PG G tn s 0 Gf tf (OK u) /\
      assign_base_store_frame (if tr then LocTransient else LocStorage)
        (a+32w) (k+1w) s tn n v tv /\
      u = ((if tr then tstore k (n2w n) v else sstore k (n2w n) v)
        with vs_inst_idx := 1) /\
      tf = (if tr then tv with t_trans := key_update tv.t_trans k {}
            else tv with t_stor := key_update tv.t_stor k {}) /\
      ptr_covers Gf tf root u capacity /\ lookup_var root u = SOME a /\
      u.vs_current_bb = sb.cs_current_bb /\
      u.vs_inst_idx = LENGTH sb.cs_current_insts /\ ~u.vs_halted /\
      (!x. not_fresh_at sa x ==> lookup_var x u = lookup_var x s /\
        FLOOKUP Gf x = FLOOKUP G x /\ op_taint tf (Var x) = op_taint tn (Var x))
Proof
  rpt gen_tac >> strip_tac >> drule tuple_dynamic_storage_compile_shape >> strip_tac >>
  gvs[fragExecTheory.fn_has_code_def, fragExecTheory.emitted_blocks_def,
    DISJ_IMP_THM, FORALL_AND_THM] >>
  qmatch_asmsub_abbrev_tac `lookup_block bodylbl fn.fn_blocks = SOME bodyblock` >>
  qmatch_asmsub_abbrev_tac `lookup_block hdr fn.fn_blocks = SOME headerblock` >>
  qmatch_asmsub_abbrev_tac `lookup_block sa.cs_current_bb fn.fn_blocks = SOME initblock` >>
  `ALL_DISTINCT [root;len;ctr] /\ 32 <= capacity /\
   lookup_block s.vs_current_bb fn.fn_blocks = SOME initblock /\
   get_instruction initblock s.vs_inst_idx = SOME (mk_inst sa.cs_next_id MLOAD [Var root] [len]) /\
   get_instruction initblock (SUC s.vs_inst_idx) = SOME (mk_inst (sa.cs_next_id+1) ASSIGN [Lit 0w] [ctr]) /\
   get_instruction initblock (s.vs_inst_idx+2) = SOME (mk_inst (sa.cs_next_id+2) JMP [Label hdr] [])` by
    (simp[Abbr `initblock`, get_instruction_def, EL_APPEND_EQN, ADD1, ALL_DISTINCT] >>
     metis_tac[]) >>
  drule_all tuple_dynamic_storage_init_counted >>
  disch_then (qspecl_then [`D`, `PG`, `if tr then LocTransient else LocStorage`, `k`] mp_tac) >>
  disch_then (qx_choose_then `g1` (qx_choose_then `t1` (qx_choose_then `s1` strip_assume_tac))) >>
  `eval_operand dst s1 = SOME k /\ op_taint t1 dst = {}` by
    (Cases_on `dst` >> gvs[eval_operand_def, op_taint_def] >>
     metis_tac[execution_frame_def]) >>
  `?g2 t2 s2.
    gas_path_ptr D 0 ctx fn PG g1 t1 s1 0 g2 t2 (OK s2) /\
    assign_base_store_frame (if tr then LocTransient else LocStorage)
      (a+32w) (k+1w) s tn n s2 t2 /\
    ptr_covers g2 t2 root s2 capacity /\ lookup_var root s2 = SOME a /\
    eval_operand dst s2 = SOME k /\ op_taint t2 dst = {} /\
    lookup_var len s2 = SOME (n2w n) /\ FLOOKUP g2 len = NONE /\ op_taint t2 (Var len) = {} /\
    lookup_var ctr s2 = SOME (n2w n) /\ FLOOKUP g2 ctr = NONE /\ op_taint t2 (Var ctr) = {} /\
    s2.vs_current_bb = sb.cs_current_bb /\ s2.vs_inst_idx = 0 /\ ~s2.vs_halted /\
    (!x. ~MEM x [ctr;lt;done;mv;off;ptr';value;slot;dv;nv] ==>
      lookup_var x s2 = lookup_var x s1 /\ FLOOKUP g2 x = FLOOKUP g1 x /\
      op_taint t2 (Var x) = op_taint t1 (Var x))` by
    (irule (Q.SPEC `n` tuple_dynamic_storage_loop_remaining) >>
     simp[ALL_DISTINCT] >>
     qexistsl_tac [`bodyblock`, `sa.cs_next_id+6`, `bodylbl`, `sa.cs_next_id+3`] >>
     simp[Abbr `bodyblock`, Abbr `headerblock`, get_instruction_def]) >>
  `lookup_block s2.vs_current_bb fn.fn_blocks = SOME bb /\
   get_instruction bb s2.vs_inst_idx = SOME (mk_inst (sa.cs_next_id+16)
     (if tr then TSTORE else SSTORE) [dst;Var len] []) /\
   eval_operand (Var len) s2 = SOME (n2w n) /\ ~s2.vs_call_ctx.cc_static` by
    (Cases_on `bb.bb_instructions` >>
     gvs[eval_operand_def, get_instruction_def, assign_base_store_frame_def]) >>
  drule_all assign_base_storage_write_counted >>
  disch_then (qspecl_then [`g2`, `D`, `PG`] assume_tac) >>
  qexistsl_tac [`g2`, `s2`, `t2`] >>
  conj_tac >-
    (qpat_x_assum `gas_path_ptr _ _ _ _ _ G tn s _ _ _ _`
      (mp_then Any mp_tac gas_path_ptr_then) >> disch_then drule >> simp[] >>
     disch_then (mp_then Any mp_tac gas_path_ptr_then) >> disch_then drule >> simp[]) >>
  simp[] >> conj_tac >-
    (Cases_on `tr` >> gvs[bodyPtrDefsTheory.ptr_covers_def, lookup_var_def, op_taint_def,
      sstore_def, tstore_def]) >>
  Cases_on `tr` >> simp[sstore_def, tstore_def, lookup_var_def, op_taint_def] >>
  gvs[MEM, lookup_var_def, op_taint_def] >> metis_tac[]
QED
