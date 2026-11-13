(* Operand-general compiler boundary for memory-to-storage word copies. *)
Theory storeSlotsPtrWordCopy
Ancestors storeSlotsPtrInterface assignBasePtrStorageLayout assignBasePtrStoragePath
  assignBasePtrStorageLoop stmtSimStoreCopy
  context compileEnv loweringStateRelDefs emitHelper emitHelperProps
  stateFrame fragExec venomInst venomState venomExecSemantics ptrSafeRun ptrDiscipline
  fragGasSeqPtr fragGasPathPtr bodyPtrDefs finite_map pred_set list rich_list arithmetic combin words

Theorem store_slots_word_copy_op_shape:
  !tr root slot count sa z sb.
    compile_word_copy_loop_op (Var root) slot count LocMemory
      (if tr then LocTransient else LocStorage) F sa = (z,sb) ==>
    ?hdr bodylbl exit ctr done mv sv vv dv nv.
      sb.cs_current_bb = exit /\ sb.cs_current_insts = [] /\
      sb.cs_blocks =
        <| bb_label := bodylbl; bb_instructions :=
          [mk_inst (sa.cs_next_id+4) MUL [Var ctr;Lit 32w] [mv];
           mk_inst (sa.cs_next_id+5) ADD [Var root;Var mv] [sv];
           mk_inst (sa.cs_next_id+6) MLOAD [Var sv] [vv];
           mk_inst (sa.cs_next_id+7) ADD [slot;Var ctr] [dv];
           mk_inst (sa.cs_next_id+8) (if tr then TSTORE else SSTORE) [Var dv;Var vv] [];
           mk_inst (sa.cs_next_id+9) ADD [Var ctr;Lit 1w] [nv];
           mk_inst (sa.cs_next_id+10) ASSIGN [Var nv] [ctr];
           mk_inst (sa.cs_next_id+11) JMP [Label hdr] []] |> ::
        <| bb_label := hdr; bb_instructions :=
          [mk_inst (sa.cs_next_id+2) EQ [Var ctr;count] [done];
           mk_inst (sa.cs_next_id+3) JNZ [Var done;Label exit;Label bodylbl] []] |> ::
        <| bb_label := sa.cs_current_bb; bb_instructions := sa.cs_current_insts ++
          [mk_inst sa.cs_next_id ASSIGN [Lit 0w] [ctr];
           mk_inst (sa.cs_next_id+1) JMP [Label hdr] []] |> :: sa.cs_blocks /\
      ALL_DISTINCT [ctr;done;mv;sv;vv;dv;nv] /\
      (!x. not_fresh_at sa x ==> ~MEM x [ctr;done;mv;sv;vv;dv;nv])
Proof
  rpt gen_tac >> Cases_on `tr` >>
  simp[compile_word_copy_loop_op_def, compile_word_copy_loop_base_def,
    word_scale_def, compile_ptr_load_def, compile_ptr_store_def,
    emit_op_def, emit_void_def, emit_inst_def,
    comp_ignore_bind_def, comp_bind_def, comp_return_def, fresh_label_def,
    fresh_var_def, fresh_id_def, emit_def, new_block_def] >> strip_tac >> gvs[] >>
  rpt (goal_assum (drule_at Any)) >>
  simp[mk_inst_def, ALL_DISTINCT, fresh_var_distinct] >>
  rw[not_fresh_at_def] >> first_x_assum irule >> simp[]
QED

Theorem store_slots_word_copy_op_code:
  !tr root slot count sa z sb fn.
    compile_word_copy_loop_op (Var root) slot count LocMemory
      (if tr then LocTransient else LocStorage) F sa = (z,sb) /\
    fn_has_code sa sb fn ==>
    ?hdr bodylbl ctr done mv sv vv dv nv ib hb bb.
      sb.cs_current_insts = [] /\
      lookup_block sa.cs_current_bb fn.fn_blocks = SOME ib /\
      ib.bb_instructions = sa.cs_current_insts ++
        [mk_inst sa.cs_next_id ASSIGN [Lit 0w] [ctr];
         mk_inst (sa.cs_next_id+1) JMP [Label hdr] []] /\
      lookup_block hdr fn.fn_blocks = SOME hb /\
      hb.bb_instructions =
        [mk_inst (sa.cs_next_id+2) EQ [Var ctr;count] [done];
         mk_inst (sa.cs_next_id+3) JNZ [Var done;Label sb.cs_current_bb;Label bodylbl] []] /\
      lookup_block bodylbl fn.fn_blocks = SOME bb /\
      bb.bb_instructions =
        [mk_inst (sa.cs_next_id+4) MUL [Var ctr;Lit 32w] [mv];
         mk_inst (sa.cs_next_id+5) ADD [Var root;Var mv] [sv];
         mk_inst (sa.cs_next_id+6) MLOAD [Var sv] [vv];
         mk_inst (sa.cs_next_id+7) ADD [slot;Var ctr] [dv];
         mk_inst (sa.cs_next_id+8) (if tr then TSTORE else SSTORE) [Var dv;Var vv] [];
         mk_inst (sa.cs_next_id+9) ADD [Var ctr;Lit 1w] [nv];
         mk_inst (sa.cs_next_id+10) ASSIGN [Var nv] [ctr];
         mk_inst (sa.cs_next_id+11) JMP [Label hdr] []] /\
      ALL_DISTINCT [ctr;done;mv;sv;vv;dv;nv] /\
      (!x. not_fresh_at sa x ==> ~MEM x [ctr;done;mv;sv;vv;dv;nv])
Proof
  rpt gen_tac >> strip_tac >> drule store_slots_word_copy_op_shape >> strip_tac >>
  gvs[fn_has_code_def, emitted_blocks_def, DISJ_IMP_THM, FORALL_AND_THM] >>
  qexistsl_tac [`hdr`, `bodylbl`, `ctr`, `done`, `mv`, `sv`, `vv`, `dv`, `nv`] >>
  simp[]
QED

(* Clean comparisons accept runtime operands, including aliased old inputs. *)
Theorem store_slots_clean_eq_counted:
  ~s.vs_halted /\ lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  get_instruction bb s.vs_inst_idx = SOME (mk_inst id EQ [left;right] [out]) /\
  eval_operand left s = SOME a /\ eval_operand right s = SOME b /\
  op_taint tn left = {} /\ op_taint tn right = {} /\
  op_prov G left = NONE /\ op_prov G right = NONE /\ ~ctx_has_dalloca ctx ==>
  gas_path_ptr D 0 ctx fn PG G tn s 0 (DRESTRICT G (COMPL {out}))
    (tn with t_var := tn.t_var |+ (out,{}))
    (OK ((update_var out (bool_to_word (a=b)) s) with vs_inst_idx := SUC s.vs_inst_idx))
Proof
  strip_tac >>
  `step_inst_base (mk_inst id EQ [left;right] [out]) s =
     OK (update_var out (bool_to_word (a=b)) s)` by
    (asm_simp_tac bool_ss [step_inst_base_opcode_eqs, mk_inst_def, instruction_accessors,
       instruction_accfupds, K_THM, opcode_case_def] >> simp[exec_pure2_def]) >>
  `ptr_inst_ok D 0 0 ctx fn G tn (mk_inst id EQ [left;right] [out]) s` by
    (simp[ptr_inst_ok_def, access_ok_def, taint_ok_def, allocas_from_def,
          mk_inst_def, codegenRelTheory.source_memory_write_ranges_def,
          contextCodegenRelTheory.source_memory_read_ranges_def] >>
     simp[GSYM mk_inst_def, step_inst_non_invoke, update_var_def] >>
     conj_tac >- (rpt strip_tac >> gvs[op_prov_def, FLOOKUP_DEF]) >>
     rpt strip_tac >> metis_tac[]) >>
  `step_prov PG G (mk_inst id EQ [left;right] [out])
      (update_var out (bool_to_word (a=b)) s) = DRESTRICT G (COMPL {out}) /\
   step_taint (mk_inst id EQ [left;right] [out]) s
      (update_var out (bool_to_word (a=b)) s) tn =
      (tn with t_var := tn.t_var |+ (out,{}))` by
    (simp[step_prov_def, set_prov_def, out_prov_def, op_prov_def,
          step_taint_def, set_var_taint_def, out_taint_def, mk_inst_def,
          mem_taint_def, step_writes_def, codegenRelTheory.source_memory_write_ranges_def,
          written_taint_def, range_bytes_def, store_taint_def, adopt_reset_def,
          imm_taint_def, new_site_bytes_def, execution_frame_def, update_var_def,
          EXTENSION, taint_component_equality] >> simp[FLOOKUP_DEF, SF CONJ_ss]) >>
  irule (SRULE [mk_inst_def, is_terminator_def]
    (Q.INST [`n` |-> `0`, `lo` |-> `0`,
      `i` |-> `mk_inst id EQ [left;right] [out]`] gas_path_ptr_step)) >>
  simp[GSYM mk_inst_def] >> goal_assum (drule_at Any) >> simp[] >>
  irule (cj 1 gas_path_ptr_rules) >> simp[update_var_def]
QED

Theorem store_slots_word_copy_header:
  !s fn bb id ctr count done i n bodylbl exit tn G ctx D PG.
    ~s.vs_halted /\ lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
    get_instruction bb s.vs_inst_idx = SOME (mk_inst id EQ [Var ctr;count] [done]) /\
    get_instruction bb (SUC s.vs_inst_idx) =
      SOME (mk_inst (id+1) JNZ [Var done;Label exit;Label bodylbl] []) /\
    lookup_var ctr s = SOME (n2w i) /\ eval_operand count s = SOME (n2w n) /\
    i <= n /\ n < dimword (:256) /\
    op_taint tn (Var ctr) = {} /\ op_taint tn count = {} /\
    FLOOKUP G ctr = NONE /\ op_prov G count = NONE /\ ~ctx_has_dalloca ctx ==>
    ?Gf tf u.
      gas_path_ptr D 0 ctx fn PG G tn s 0 Gf tf (OK u) /\
      u.vs_current_bb = (if i=n then exit else bodylbl) /\ u.vs_inst_idx = 0 /\ ~u.vs_halted /\
      execution_frame u = execution_frame s /\
      u.vs_accounts = s.vs_accounts /\ u.vs_transient = s.vs_transient /\
      u.vs_call_ctx = s.vs_call_ctx /\ u.vs_memory = s.vs_memory /\
      tf.t_mem = tn.t_mem /\ tf.t_imm = tn.t_imm /\ tf.t_stor = tn.t_stor /\ tf.t_trans = tn.t_trans /\
      (!x. x <> done ==> lookup_var x u = lookup_var x s /\
        FLOOKUP Gf x = FLOOKUP G x /\ op_taint tf (Var x) = op_taint tn (Var x))
Proof
  rpt gen_tac >> strip_tac >>
  rename1 `eval_operand cnt s = SOME (n2w n)` >>
  `((n2w i:bytes32) = n2w n) = (i=n)` by simp[n2w_11, LESS_MOD] >>
  qabbrev_tac `s1 = (update_var done (bool_to_word (i=n)) s)
    with vs_inst_idx := SUC s.vs_inst_idx` >>
  qabbrev_tac `g1 = DRESTRICT G (COMPL {done})` >>
  qabbrev_tac `t1 = tn with t_var := tn.t_var |+ (done,{})` >>
  `gas_path_ptr D 0 ctx fn PG G tn s 0 g1 t1 (OK s1)` by
    (simp[Abbr `s1`, Abbr `g1`, Abbr `t1`] >>
     qpat_x_assum `(_ = _) = (i=n)` (fn th => once_rewrite_tac[GSYM th]) >>
     irule store_slots_clean_eq_counted >> simp[] >>
     qexistsl_tac [`id`, `Var ctr`, `cnt`] >>
     simp[eval_operand_def, op_prov_def]) >>
  `lookup_block s1.vs_current_bb fn.fn_blocks = SOME bb /\ ~s1.vs_halted /\
   get_instruction bb s1.vs_inst_idx =
      SOME (mk_inst (id+1) JNZ [Var done;Label exit;Label bodylbl] []) /\
   eval_operand (Var done) s1 = SOME (if i=n then 1w else 0w) /\
   op_taint t1 (Var done) = {}` by
    (simp[Abbr `s1`, Abbr `t1`, execution_frame_def, update_var_def, eval_operand_def, lookup_var_def,
      FLOOKUP_UPDATE, op_taint_def] >> Cases_on `i=n` >> simp[bool_to_word_def]) >>
  drule_all assign_base_storage_branch_counted >>
  disch_then (qspecl_then [`g1`, `D`, `PG`] mp_tac) >> strip_tac >>
  qexistsl_tac [`g1`, `t1`, `jump_to (if i=n then exit else bodylbl) s1`] >>
  conj_tac >-
    (qpat_x_assum `gas_path_ptr _ _ _ _ _ G tn s _ _ _ _`
      (mp_then Any mp_tac gas_path_ptr_then) >> disch_then drule >> simp[]) >>
  gvs[Abbr `s1`, Abbr `g1`, Abbr `t1`, jump_to_def, execution_frame_def, update_var_def,
    lookup_var_def, FLOOKUP_UPDATE, FLOOKUP_DRESTRICT, op_taint_def]
QED

Theorem store_slots_word_copy_prefix:
  !s fn bb id root ctr mv sv vv dv slot a i n total k tr tn G ctx D PG.
    ~s.vs_halted /\ lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
    get_instruction bb s.vs_inst_idx = SOME (mk_inst id MUL [Var ctr;Lit 32w] [mv]) /\
    get_instruction bb (SUC s.vs_inst_idx) = SOME (mk_inst (id+1) ADD [Var root;Var mv] [sv]) /\
    get_instruction bb (s.vs_inst_idx+2) = SOME (mk_inst (id+2) MLOAD [Var sv] [vv]) /\
    get_instruction bb (s.vs_inst_idx+3) = SOME (mk_inst (id+3) ADD [slot;Var ctr] [dv]) /\
    get_instruction bb (s.vs_inst_idx+4) = SOME (mk_inst (id+4) (if tr then TSTORE else SSTORE) [Var dv;Var vv] []) /\
    ptr_covers G tn root s total /\ lookup_var root s = SOME a /\
    lookup_var ctr s = SOME (n2w i) /\ op_taint tn (Var ctr) = {} /\
    ALL_DISTINCT [root;ctr;mv;sv;vv;dv] /\
    (!x. slot = Var x ==> ~MEM x [mv;sv;vv]) /\
    eval_operand slot s = SOME k /\ op_taint tn slot = {} /\
    i<n /\ 32*n <= total /\ w2n a+32*(n-1) < dimword (:256) /\
    ~ctx_has_dalloca ctx /\ ~s.vs_call_ctx.cc_static ==>
    ?Gf tf u.
      gas_path_ptr D 0 ctx fn PG G tn s 0 Gf tf (OK u) /\
      u.vs_memory = s.vs_memory /\ tf.t_mem = tn.t_mem /\ tf.t_imm = tn.t_imm /\
      tf.t_stor = (if tr then tn.t_stor else key_update tn.t_stor (k+n2w i)
        (mem_word_taint tn.t_mem (w2n (a+n2w (32*i))))) /\
      tf.t_trans = (if tr then key_update tn.t_trans (k+n2w i)
        (mem_word_taint tn.t_mem (w2n (a+n2w (32*i)))) else tn.t_trans) /\
      execution_frame u = execution_frame
        (if tr then tstore (k+n2w i) (mload (w2n (a+n2w (32*i))) s) s
         else sstore (k+n2w i) (mload (w2n (a+n2w (32*i))) s) s) /\
      u.vs_accounts = (if tr then s.vs_accounts else
        (sstore (k+n2w i) (mload (w2n (a+n2w (32*i))) s) s).vs_accounts) /\
      u.vs_transient = (if tr then
        (tstore (k+n2w i) (mload (w2n (a+n2w (32*i))) s) s).vs_transient else s.vs_transient) /\
      u.vs_call_ctx = s.vs_call_ctx /\ ~u.vs_halted /\
      u.vs_current_bb = s.vs_current_bb /\ u.vs_inst_idx = s.vs_inst_idx+5 /\
      (!x. ~MEM x [mv;sv;vv;dv] ==> lookup_var x u = lookup_var x s /\
        FLOOKUP Gf x = FLOOKUP G x /\ op_taint tf (Var x) = op_taint tn (Var x))
Proof
  rpt gen_tac >> strip_tac >>
  `ALL_DISTINCT [ctr;mv;sv;vv] /\ ~MEM root [mv;sv;vv] /\ dv <> ctr /\ dv <> vv` by
    gvs[ALL_DISTINCT] >>
  drule_all assign_base_storage_source_prefix >>
  disch_then (qspecl_then [`D`, `PG`] mp_tac) >>
  disch_then (qx_choose_then `g1` (qx_choose_then `t1`
    (qx_choose_then `s1` strip_assume_tac))) >>
  `eval_operand slot s1 = SOME k /\ op_taint t1 slot = {}` by
    (Cases_on `slot` >> gvs[eval_operand_def, op_taint_def] >> metis_tac[]) >>
  `lookup_block s1.vs_current_bb fn.fn_blocks = SOME bb /\
   get_instruction bb s1.vs_inst_idx = SOME (mk_inst (id+3) ADD [slot;Var ctr] [dv]) /\
   get_instruction bb (SUC s1.vs_inst_idx) = SOME (mk_inst ((id+3)+1) (if tr then TSTORE else SSTORE) [Var dv;Var vv] []) /\
   op_taint t1 (Var ctr) = {} /\ ~s1.vs_call_ctx.cc_static` by
    gvs[ALL_DISTINCT, ADD1] >>
  drule_all assign_base_storage_destination_prefix >>
  disch_then (qspecl_then [`g1`, `D`, `PG`] mp_tac) >>
  disch_then (qx_choose_then `g2` (qx_choose_then `t2`
    (qx_choose_then `s2` strip_assume_tac))) >>
  qexistsl_tac [`g2`, `t2`, `s2`] >> conj_tac >-
    (qpat_x_assum `gas_path_ptr _ _ _ _ _ G tn s _ _ _ _`
      (mp_then Any mp_tac gas_path_ptr_then) >> disch_then drule >> simp[]) >>
  Cases_on `tr` >> gvs[ALL_DISTINCT, sstore_def, tstore_def,
    execution_frame_def] >> metis_tac[]
QED

Theorem store_slots_word_copy_body:
  !s fn bb id root ctr mv sv vv dv nv slot a i n total k tr hdr tn G ctx D PG.
    ~s.vs_halted /\ lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
    get_instruction bb s.vs_inst_idx = SOME (mk_inst id MUL [Var ctr;Lit 32w] [mv]) /\
    get_instruction bb (SUC s.vs_inst_idx) = SOME (mk_inst (id+1) ADD [Var root;Var mv] [sv]) /\
    get_instruction bb (s.vs_inst_idx+2) = SOME (mk_inst (id+2) MLOAD [Var sv] [vv]) /\
    get_instruction bb (s.vs_inst_idx+3) = SOME (mk_inst (id+3) ADD [slot;Var ctr] [dv]) /\
    get_instruction bb (s.vs_inst_idx+4) = SOME (mk_inst (id+4) (if tr then TSTORE else SSTORE) [Var dv;Var vv] []) /\
    get_instruction bb (s.vs_inst_idx+5) = SOME (mk_inst (id+5) ADD [Var ctr;Lit 1w] [nv]) /\
    get_instruction bb (s.vs_inst_idx+6) = SOME (mk_inst (id+6) ASSIGN [Var nv] [ctr]) /\
    get_instruction bb (s.vs_inst_idx+7) = SOME (mk_inst (id+7) JMP [Label hdr] []) /\
    ptr_covers G tn root s total /\ lookup_var root s = SOME a /\
    lookup_var ctr s = SOME (n2w i) /\ FLOOKUP G ctr = NONE /\ op_taint tn (Var ctr) = {} /\
    ALL_DISTINCT [root;ctr;mv;sv;vv;dv;nv] /\
    (!x. slot = Var x ==> ~MEM x [mv;sv;vv]) /\
    eval_operand slot s = SOME k /\ op_taint tn slot = {} /\
    i<n /\ 32*n <= total /\ w2n a+32*(n-1) < dimword (:256) /\
    ~ctx_has_dalloca ctx /\ ~s.vs_call_ctx.cc_static ==>
    ?Gf tf u.
      gas_path_ptr D 0 ctx fn PG G tn s 0 Gf tf (OK u) /\
      lookup_var ctr u = SOME (n2w (SUC i)) /\ FLOOKUP Gf ctr = NONE /\
      op_taint tf (Var ctr) = {} /\
      u.vs_memory = s.vs_memory /\ tf.t_mem = tn.t_mem /\ tf.t_imm = tn.t_imm /\
      tf.t_stor = (if tr then tn.t_stor else key_update tn.t_stor (k+n2w i)
        (mem_word_taint tn.t_mem (w2n (a+n2w (32*i))))) /\
      tf.t_trans = (if tr then key_update tn.t_trans (k+n2w i)
        (mem_word_taint tn.t_mem (w2n (a+n2w (32*i)))) else tn.t_trans) /\
      execution_frame u = execution_frame
        (if tr then tstore (k+n2w i) (mload (w2n (a+n2w (32*i))) s) s
         else sstore (k+n2w i) (mload (w2n (a+n2w (32*i))) s) s) /\
      u.vs_accounts = (if tr then s.vs_accounts else
        (sstore (k+n2w i) (mload (w2n (a+n2w (32*i))) s) s).vs_accounts) /\
      u.vs_transient = (if tr then
        (tstore (k+n2w i) (mload (w2n (a+n2w (32*i))) s) s).vs_transient else s.vs_transient) /\
      u.vs_call_ctx = s.vs_call_ctx /\ ~u.vs_halted /\
      u.vs_current_bb = hdr /\ u.vs_inst_idx = 0 /\
      (!x. ~MEM x [ctr;mv;sv;vv;dv;nv] ==> lookup_var x u = lookup_var x s /\
        FLOOKUP Gf x = FLOOKUP G x /\ op_taint tf (Var x) = op_taint tn (Var x))
Proof
  rpt gen_tac >> strip_tac >>
  `ALL_DISTINCT [root;ctr;mv;sv;vv;dv] /\ ctr <> nv` by gvs[ALL_DISTINCT] >>
  drule_all store_slots_word_copy_prefix >>
  disch_then (qspecl_then [`D`, `PG`] mp_tac) >>
  disch_then (qx_choose_then `g1` (qx_choose_then `t1`
    (qx_choose_then `s1` strip_assume_tac))) >>
  `lookup_block s1.vs_current_bb fn.fn_blocks = SOME bb /\
   get_instruction bb s1.vs_inst_idx = SOME (mk_inst (id+5) ADD [Var ctr;Lit 1w] [nv]) /\
   get_instruction bb (SUC s1.vs_inst_idx) = SOME (mk_inst ((id+5)+1) ASSIGN [Var nv] [ctr]) /\
   lookup_var ctr s1 = SOME (n2w i) /\ FLOOKUP g1 ctr = NONE /\ op_taint t1 (Var ctr) = {}` by
    gvs[ALL_DISTINCT, ADD1] >>
  drule_all assign_base_storage_increment_prefix >>
  disch_then (qspecl_then [`D`, `PG`] mp_tac) >>
  disch_then (qx_choose_then `g2` (qx_choose_then `t2`
    (qx_choose_then `s2` strip_assume_tac))) >>
  `lookup_block s2.vs_current_bb fn.fn_blocks = SOME bb /\
   get_instruction bb s2.vs_inst_idx = SOME (mk_inst (id+7) JMP [Label hdr] [])` by simp[] >>
  drule_all assign_base_storage_jump_counted >>
  disch_then (qspecl_then [`t2`, `g2`, `D`, `PG`] mp_tac) >> strip_tac >>
  qexistsl_tac [`g2`, `t2`, `jump_to hdr s2`] >> conj_tac >-
    (qpat_x_assum `gas_path_ptr _ _ _ _ _ G tn s _ _ _ _`
      (mp_then Any mp_tac gas_path_ptr_then) >> disch_then drule >> simp[] >>
     disch_then (mp_then Any mp_tac gas_path_ptr_then) >> disch_then drule >> simp[]) >>
  gvs[jump_to_def, lookup_var_def, ALL_DISTINCT] >> metis_tac[]
QED

(* Internal dense-prefix representation tracks writes, not canonical padding. *)
Theorem store_slots_word_copy_body_frame:
  !s fn bb id root ctr mv sv vv dv nv slot a i n capacity k tr hdr tn G ctx D PG s0 tn0.
    ~s.vs_halted /\ lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
    get_instruction bb s.vs_inst_idx = SOME (mk_inst id MUL [Var ctr;Lit 32w] [mv]) /\
    get_instruction bb (SUC s.vs_inst_idx) = SOME (mk_inst (id+1) ADD [Var root;Var mv] [sv]) /\
    get_instruction bb (s.vs_inst_idx+2) = SOME (mk_inst (id+2) MLOAD [Var sv] [vv]) /\
    get_instruction bb (s.vs_inst_idx+3) = SOME (mk_inst (id+3) ADD [slot;Var ctr] [dv]) /\
    get_instruction bb (s.vs_inst_idx+4) = SOME (mk_inst (id+4) (if tr then TSTORE else SSTORE) [Var dv;Var vv] []) /\
    get_instruction bb (s.vs_inst_idx+5) = SOME (mk_inst (id+5) ADD [Var ctr;Lit 1w] [nv]) /\
    get_instruction bb (s.vs_inst_idx+6) = SOME (mk_inst (id+6) ASSIGN [Var nv] [ctr]) /\
    get_instruction bb (s.vs_inst_idx+7) = SOME (mk_inst (id+7) JMP [Label hdr] []) /\
    ptr_covers G tn root s capacity /\ lookup_var root s = SOME a /\
    lookup_var ctr s = SOME (n2w i) /\ FLOOKUP G ctr = NONE /\ op_taint tn (Var ctr) = {} /\
    ALL_DISTINCT [root;ctr;mv;sv;vv;dv;nv] /\
    (!x. slot = Var x ==> ~MEM x [mv;sv;vv]) /\
    eval_operand slot s = SOME k /\ op_taint tn slot = {} /\
    i<n /\ 32*n <= capacity /\ w2n a+32*(n-1) < dimword (:256) /\
    ~ctx_has_dalloca ctx /\ ~s.vs_call_ctx.cc_static /\
    execution_frame s = execution_frame (store_copy_prefix (if tr then LocTransient else LocStorage) a k s0 i) /\
    assign_base_store_frame (if tr then LocTransient else LocStorage) a k s0 tn0 i s tn ==>
    ?Gf tf u.
      gas_path_ptr D 0 ctx fn PG G tn s 0 Gf tf (OK u) /\
      execution_frame u = execution_frame (store_copy_prefix (if tr then LocTransient else LocStorage) a k s0 (SUC i)) /\
      assign_base_store_frame (if tr then LocTransient else LocStorage) a k s0 tn0 (SUC i) u tf /\
      lookup_var ctr u = SOME (n2w (SUC i)) /\ FLOOKUP Gf ctr = NONE /\
      op_taint tf (Var ctr) = {} /\
      ptr_covers Gf tf root u capacity /\ lookup_var root u = SOME a /\
      u.vs_current_bb = hdr /\ u.vs_inst_idx = 0 /\ ~u.vs_halted /\
      (!x. ~MEM x [ctr;mv;sv;vv;dv;nv] ==> lookup_var x u = lookup_var x s /\
        FLOOKUP Gf x = FLOOKUP G x /\ op_taint tf (Var x) = op_taint tn (Var x))
Proof
  rpt gen_tac >> strip_tac >>
  drule_all store_slots_word_copy_body >>
  disch_then (qspecl_then [`D`, `PG`] mp_tac) >>
  disch_then (qx_choose_then `gf` (qx_choose_then `tf`
    (qx_choose_then `u` strip_assume_tac))) >>
  `assign_base_store_frame (if tr then LocTransient else LocStorage) a k s0 tn0 (SUC i) u tf` by
    (drule_all assign_base_store_frame_advance >> simp[]) >>
  `lookup_var root u = lookup_var root s /\ FLOOKUP gf root = FLOOKUP G root /\
   op_taint tf (Var root) = op_taint tn (Var root)` by
    (gvs[ALL_DISTINCT] >> metis_tac[]) >>
  `ptr_covers gf tf root u capacity /\ lookup_var root u = SOME a` by
    (drule_all assign_base_store_root_transport >> simp[]) >>
  `execution_frame u = execution_frame (store_copy_prefix
     (if tr then LocTransient else LocStorage) a k s0 (SUC i))` by
    (`n2w (32*i) = (n2w i:bytes32)*32w` by
       (once_rewrite_tac[MULT_COMM] >> simp[word_mul_n2w]) >>
     Cases_on `tr` >>
     gvs[assign_base_store_prefix_suc, execution_frame_def,
       sstore_def, tstore_def, venom_state_component_equality,
       assign_base_store_prefix_frame, mload_def]) >>
  qexistsl_tac [`gf`, `tf`, `u`] >> metis_tac[]
QED

Theorem store_slots_word_copy_header_frame:
  !s fn bb id ctr count done i n bodylbl exit tn G ctx D PG loc a k s0 tn0 root capacity.
    ~s.vs_halted /\ lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
    get_instruction bb s.vs_inst_idx = SOME (mk_inst id EQ [Var ctr;count] [done]) /\
    get_instruction bb (SUC s.vs_inst_idx) =
      SOME (mk_inst (id+1) JNZ [Var done;Label exit;Label bodylbl] []) /\
    lookup_var ctr s = SOME (n2w i) /\ FLOOKUP G ctr = NONE /\ op_prov G count = NONE /\
    eval_operand count s = SOME (n2w n) /\ op_taint tn count = {} /\
    i <= n /\ n < dimword (:256) /\ op_taint tn (Var ctr) = {} /\
    ctr <> done /\ root <> done /\ ~ctx_has_dalloca ctx /\
    execution_frame s = execution_frame (store_copy_prefix loc a k s0 i) /\
    assign_base_store_frame loc a k s0 tn0 i s tn /\
    ptr_covers G tn root s capacity /\ lookup_var root s = SOME a ==>
    ?Gf tf u.
      gas_path_ptr D 0 ctx fn PG G tn s 0 Gf tf (OK u) /\
      execution_frame u = execution_frame (store_copy_prefix loc a k s0 i) /\
      assign_base_store_frame loc a k s0 tn0 i u tf /\
      ptr_covers Gf tf root u capacity /\ lookup_var root u = SOME a /\
      lookup_var ctr u = SOME (n2w i) /\ FLOOKUP Gf ctr = NONE /\ op_taint tf (Var ctr) = {} /\
      u.vs_current_bb = (if i=n then exit else bodylbl) /\ u.vs_inst_idx = 0 /\ ~u.vs_halted /\
      (!x. x <> done ==> lookup_var x u = lookup_var x s /\
        FLOOKUP Gf x = FLOOKUP G x /\ op_taint tf (Var x) = op_taint tn (Var x))
Proof
  rpt gen_tac >> strip_tac >>
  drule_all store_slots_word_copy_header >>
  disch_then (qspecl_then [`D`, `PG`] mp_tac) >>
  disch_then (qx_choose_then `gf` (qx_choose_then `tf`
    (qx_choose_then `u` strip_assume_tac))) >>
  `assign_base_store_frame loc a k s0 tn0 i u tf` by
    (drule_all assign_base_store_frame_preserve >> simp[]) >>
  `lookup_var root u = lookup_var root s /\ FLOOKUP gf root = FLOOKUP G root /\
   op_taint tf (Var root) = op_taint tn (Var root)` by metis_tac[] >>
  `ptr_covers gf tf root u capacity /\ lookup_var root u = SOME a` by
    (drule_all assign_base_store_root_transport >> simp[]) >>
  qexistsl_tac [`gf`, `tf`, `u`] >> metis_tac[]
QED
