(* Operand-general compiler boundary for memory-to-storage word copies. *)
Theory storeSlotsPtrWordCopy
Ancestors storeSlotsPtrInterface assignBasePtrStorageLayout assignBasePtrStoragePath
  assignBasePtrStorageLoop assignBasePtrStorageSemantic stmtSimStoreCopy
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

Theorem store_slots_operand_transport:
  u.vs_labels = s.vs_labels /\
  (!x. op = Var x ==> lookup_var x u = lookup_var x s /\
    FLOOKUP H x = FLOOKUP G x /\ op_taint tf (Var x) = op_taint tn (Var x)) ==>
  eval_operand op u = eval_operand op s /\
  op_prov H op = op_prov G op /\ op_taint tf op = op_taint tn op
Proof
  Cases_on `op` >> simp[eval_operand_def, op_prov_def, op_taint_def]
QED

Theorem store_slots_word_copy_loop_remaining[local]:
  !count remaining i s G tn.
    i+remaining = n /\ n < dimword (:256) /\ 32*n <= capacity /\
    w2n a+32*(n-1) < dimword (:256) /\ ~ctx_has_dalloca ctx /\
    ~s0.vs_call_ctx.cc_static /\
    lookup_block hdr fn.fn_blocks = SOME hb /\
    lookup_block bodylbl fn.fn_blocks = SOME bb /\
    get_instruction hb 0 = SOME (mk_inst hid EQ [Var ctr;count] [done]) /\
    get_instruction hb 1 = SOME (mk_inst (hid+1) JNZ [Var done;Label exit;Label bodylbl] []) /\
    get_instruction bb 0 = SOME (mk_inst bid MUL [Var ctr;Lit 32w] [mv]) /\
    get_instruction bb 1 = SOME (mk_inst (bid+1) ADD [Var root;Var mv] [sv]) /\
    get_instruction bb 2 = SOME (mk_inst (bid+2) MLOAD [Var sv] [vv]) /\
    get_instruction bb 3 = SOME (mk_inst (bid+3) ADD [slot;Var ctr] [dv]) /\
    get_instruction bb 4 = SOME (mk_inst (bid+4) (if tr then TSTORE else SSTORE) [Var dv;Var vv] []) /\
    get_instruction bb 5 = SOME (mk_inst (bid+5) ADD [Var ctr;Lit 1w] [nv]) /\
    get_instruction bb 6 = SOME (mk_inst (bid+6) ASSIGN [Var nv] [ctr]) /\
    get_instruction bb 7 = SOME (mk_inst (bid+7) JMP [Label hdr] []) /\
    ALL_DISTINCT [root;ctr;done;mv;sv;vv;dv;nv] /\
    (!x. slot = Var x \/ count = Var x ==> ~MEM x [ctr;done;mv;sv;vv;dv;nv]) /\
    eval_operand slot s = SOME k /\ op_taint tn slot = {} /\
    eval_operand count s = SOME (n2w n) /\ op_taint tn count = {} /\ op_prov G count = NONE /\
    execution_frame s = execution_frame (store_copy_prefix (if tr then LocTransient else LocStorage) a k s0 i) /\
    assign_base_store_frame (if tr then LocTransient else LocStorage) a k s0 tn0 i s tn /\
    ptr_covers G tn root s capacity /\ lookup_var root s = SOME a /\
    lookup_var ctr s = SOME (n2w i) /\ FLOOKUP G ctr = NONE /\ op_taint tn (Var ctr) = {} /\
    s.vs_current_bb = hdr /\ s.vs_inst_idx = 0 /\ ~s.vs_halted ==>
    ?Gf tf u.
      gas_path_ptr D 0 ctx fn PG G tn s 0 Gf tf (OK u) /\
      execution_frame u = execution_frame (store_copy_prefix (if tr then LocTransient else LocStorage) a k s0 n) /\
      assign_base_store_frame (if tr then LocTransient else LocStorage) a k s0 tn0 n u tf /\
      ptr_covers Gf tf root u capacity /\ lookup_var root u = SOME a /\
      lookup_var ctr u = SOME (n2w n) /\ FLOOKUP Gf ctr = NONE /\ op_taint tf (Var ctr) = {} /\
      u.vs_current_bb = exit /\ u.vs_inst_idx = 0 /\ ~u.vs_halted /\
      (!x. ~MEM x [ctr;done;mv;sv;vv;dv;nv] ==> lookup_var x u = lookup_var x s /\
        FLOOKUP Gf x = FLOOKUP G x /\ op_taint tf (Var x) = op_taint tn (Var x))
Proof
  qx_gen_tac `cnt` >> Induct_on `remaining` >> rpt gen_tac >> strip_tac >>
  `ctr <> done /\ root <> done /\ i<=n /\
   lookup_block s.vs_current_bb fn.fn_blocks = SOME hb /\
   get_instruction hb s.vs_inst_idx = SOME (mk_inst hid EQ [Var ctr;cnt] [done]) /\
   get_instruction hb (SUC s.vs_inst_idx) = SOME (mk_inst (hid+1) JNZ [Var done;Label exit;Label bodylbl] [])` by
    (gvs[ALL_DISTINCT] >> decide_tac) >>
  drule_all store_slots_word_copy_header_frame >>
  disch_then (qspecl_then [`D`, `PG`] mp_tac) >>
  disch_then (qx_choose_then `g1` (qx_choose_then `t1`
    (qx_choose_then `s1` strip_assume_tac)))
  >- (qexistsl_tac [`g1`, `t1`, `s1`] >> gvs[] >> metis_tac[]) >>
  `eval_operand slot s1 = SOME k /\ op_taint t1 slot = {} /\
   eval_operand cnt s1 = SOME (n2w n) /\ op_taint t1 cnt = {} /\ op_prov g1 cnt = NONE` by
    (suspend "header_operand_transport") >>
  `i<n /\ ~s1.vs_call_ctx.cc_static /\ ALL_DISTINCT [root;ctr;mv;sv;vv;dv;nv] /\
   (!x. slot = Var x ==> ~MEM x [mv;sv;vv])` by
    (gvs[assign_base_store_frame_def, ALL_DISTINCT] >> metis_tac[MEM, LESS_ADD_SUC]) >>
  `lookup_block s1.vs_current_bb fn.fn_blocks = SOME bb /\
   get_instruction bb s1.vs_inst_idx = SOME (mk_inst bid MUL [Var ctr;Lit 32w] [mv]) /\
   get_instruction bb (SUC s1.vs_inst_idx) = SOME (mk_inst (bid+1) ADD [Var root;Var mv] [sv]) /\
   get_instruction bb (s1.vs_inst_idx+2) = SOME (mk_inst (bid+2) MLOAD [Var sv] [vv]) /\
   get_instruction bb (s1.vs_inst_idx+3) = SOME (mk_inst (bid+3) ADD [slot;Var ctr] [dv]) /\
   get_instruction bb (s1.vs_inst_idx+4) = SOME (mk_inst (bid+4) (if tr then TSTORE else SSTORE) [Var dv;Var vv] []) /\
   get_instruction bb (s1.vs_inst_idx+5) = SOME (mk_inst (bid+5) ADD [Var ctr;Lit 1w] [nv]) /\
   get_instruction bb (s1.vs_inst_idx+6) = SOME (mk_inst (bid+6) ASSIGN [Var nv] [ctr]) /\
   get_instruction bb (s1.vs_inst_idx+7) = SOME (mk_inst (bid+7) JMP [Label hdr] [])` by simp[] >>
  drule_all store_slots_word_copy_body_frame >>
  disch_then (qspecl_then [`D`, `PG`] mp_tac) >>
  disch_then (qx_choose_then `g2` (qx_choose_then `t2`
    (qx_choose_then `s2` strip_assume_tac))) >>
  `eval_operand slot s2 = SOME k /\ op_taint t2 slot = {} /\
   eval_operand cnt s2 = SOME (n2w n) /\ op_taint t2 cnt = {} /\ op_prov g2 cnt = NONE` by
    (suspend "body_operand_transport") >>
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

Resume store_slots_word_copy_loop_remaining[body_operand_transport]:
  qpat_x_assum `!i s G tn. _` kall_tac >>
     `s2.vs_labels = s1.vs_labels` by
       (qpat_x_assum `execution_frame s2 = _`
          mp_tac >>
        qpat_x_assum `execution_frame s1 = _`
          mp_tac >>
        simp[execution_frame_def, assign_base_store_prefix_suc, sstore_def, tstore_def] >>
        rpt strip_tac >> asm_rewrite_tac[] >> Cases_on `tr` >> simp[sstore_def, tstore_def]) >>
     `eval_operand slot s2 = eval_operand slot s1 /\
      op_prov g2 slot = op_prov g1 slot /\ op_taint t2 slot = op_taint t1 slot` by
       (irule store_slots_operand_transport >> simp[] >> metis_tac[MEM]) >>
     `eval_operand cnt s2 = eval_operand cnt s1 /\
      op_prov g2 cnt = op_prov g1 cnt /\ op_taint t2 cnt = op_taint t1 cnt` by
       (irule store_slots_operand_transport >> simp[] >> metis_tac[MEM]) >>
     simp[]
QED

Resume store_slots_word_copy_loop_remaining[header_operand_transport]:
  qpat_x_assum `!i s G tn. _` kall_tac >>
  `s1.vs_labels = s.vs_labels` by
    (qpat_x_assum `execution_frame s1 = _` mp_tac >>
     qpat_x_assum `execution_frame s = _` mp_tac >>
     simp[execution_frame_def] >> rpt strip_tac >> asm_rewrite_tac[]) >>
  `eval_operand slot s1 = eval_operand slot s /\
   op_prov g1 slot = op_prov G slot /\ op_taint t1 slot = op_taint tn slot` by
    (irule store_slots_operand_transport >> simp[] >> metis_tac[MEM]) >>
  `eval_operand cnt s1 = eval_operand cnt s /\
   op_prov g1 cnt = op_prov G cnt /\ op_taint t1 cnt = op_taint tn cnt` by
    (irule store_slots_operand_transport >> simp[] >> metis_tac[MEM]) >>
  simp[]
QED

Finalise store_slots_word_copy_loop_remaining

Theorem store_slots_word_copy_op_prefix_counted:
  !tr root slot count n sa z sb fn s G tn ctx D PG a k capacity.
    compile_word_copy_loop_op (Var root) slot count LocMemory
      (if tr then LocTransient else LocStorage) F sa = (z,sb) /\
    fn_has_code sa sb fn /\ not_fresh_at sa root /\
    (!x. slot = Var x \/ count = Var x ==> not_fresh_at sa x) /\
    ptr_covers G tn root s capacity /\ lookup_var root s = SOME a /\
    eval_operand slot s = SOME k /\ op_taint tn slot = {} /\
    eval_operand count s = SOME (n2w n) /\ op_taint tn count = {} /\ op_prov G count = NONE /\
    ~s.vs_halted /\ ~s.vs_call_ctx.cc_static /\ ~ctx_has_dalloca ctx /\
    s.vs_current_bb = sa.cs_current_bb /\ s.vs_inst_idx = LENGTH sa.cs_current_insts /\
    n < dimword (:256) /\ 32*n <= capacity /\ w2n a+32*(n-1) < dimword (:256) ==>
    ?Gf tf u.
      gas_path_ptr D 0 ctx fn PG G tn s 0 Gf tf (OK u) /\
      execution_frame u = execution_frame (store_copy_prefix (if tr then LocTransient else LocStorage) a k s n) /\
      assign_base_store_frame (if tr then LocTransient else LocStorage) a k s tn n u tf /\
      ptr_covers Gf tf root u capacity /\ lookup_var root u = SOME a /\
      u.vs_current_bb = sb.cs_current_bb /\
      u.vs_inst_idx = LENGTH sb.cs_current_insts /\ ~u.vs_halted /\
      (!x. not_fresh_at sa x ==> lookup_var x u = lookup_var x s /\
        FLOOKUP Gf x = FLOOKUP G x /\ op_taint tf (Var x) = op_taint tn (Var x))
Proof
  rpt gen_tac >> strip_tac >> rename1 `op_prov G cnt = NONE` >>
  drule_all store_slots_word_copy_op_code >> strip_tac >>
  `root <> ctr /\ ALL_DISTINCT [root;ctr;done;mv;sv;vv;dv;nv] /\
   (!x. cnt = Var x \/ slot = Var x ==> ~MEM x [ctr;done;mv;sv;vv;dv;nv])` by
    (gvs[ALL_DISTINCT] >> metis_tac[]) >>
  `get_instruction ib s.vs_inst_idx = SOME (mk_inst sa.cs_next_id ASSIGN [Lit 0w] [ctr]) /\
   get_instruction ib (SUC s.vs_inst_idx) = SOME (mk_inst (sa.cs_next_id+1) JMP [Label hdr] [])` by
    simp[get_instruction_def, EL_APPEND_EQN, ADD1] >>
  `lookup_block s.vs_current_bb fn.fn_blocks = SOME ib` by simp[] >>
  drule_all assign_base_storage_init_frame >>
  disch_then (qspecl_then [`D`, `PG`, `if tr then LocTransient else LocStorage`, `k`] mp_tac) >>
  disch_then (qx_choose_then `g1` (qx_choose_then `t1` (qx_choose_then `s1` strip_assume_tac))) >>
  `eval_operand slot s1 = SOME k /\ op_taint t1 slot = {} /\
   eval_operand cnt s1 = SOME (n2w n) /\ op_taint t1 cnt = {} /\ op_prov g1 cnt = NONE` by
    (suspend "init_operands") >>
  `?gf tf u.
    gas_path_ptr D 0 ctx fn PG g1 t1 s1 0 gf tf (OK u) /\
    execution_frame u = execution_frame (store_copy_prefix (if tr then LocTransient else LocStorage) a k s n) /\
    assign_base_store_frame (if tr then LocTransient else LocStorage) a k s tn n u tf /\
    ptr_covers gf tf root u capacity /\ lookup_var root u = SOME a /\
    lookup_var ctr u = SOME (n2w n) /\ FLOOKUP gf ctr = NONE /\ op_taint tf (Var ctr) = {} /\
    u.vs_current_bb = sb.cs_current_bb /\ u.vs_inst_idx = 0 /\ ~u.vs_halted /\
    (!x. ~MEM x [ctr;done;mv;sv;vv;dv;nv] ==> lookup_var x u = lookup_var x s1 /\
      FLOOKUP gf x = FLOOKUP g1 x /\ op_taint tf (Var x) = op_taint t1 (Var x))` by
    (irule (Q.SPECL [`cnt`, `n`, `0`] store_slots_word_copy_loop_remaining) >>
     simp[get_instruction_def, mk_inst_def] >>
     rpt (goal_assum (drule_at Any)) >>
     gvs[assign_base_store_prefix_zero, execution_frame_def] >> metis_tac[]) >>
  qexistsl_tac [`gf`, `tf`, `u`] >> conj_tac >-
    (qpat_x_assum `gas_path_ptr _ _ _ _ _ G tn s _ _ _ _`
      (mp_then Any mp_tac gas_path_ptr_then) >> disch_then drule >> simp[]) >>
  asm_rewrite_tac[] >> simp[] >> metis_tac[MEM]
QED

Resume store_slots_word_copy_op_prefix_counted[init_operands]:
  `s1.vs_labels = s.vs_labels` by
    (qpat_x_assum `execution_frame s1 = _` mp_tac >> simp[execution_frame_def]) >>
  `eval_operand slot s1 = eval_operand slot s /\
   op_prov g1 slot = op_prov G slot /\ op_taint t1 slot = op_taint tn slot` by
    (irule store_slots_operand_transport >> simp[] >> metis_tac[MEM]) >>
  `eval_operand cnt s1 = eval_operand cnt s /\
   op_prov g1 cnt = op_prov G cnt /\ op_taint t1 cnt = op_taint tn cnt` by
    (irule store_slots_operand_transport >> simp[] >> metis_tac[MEM]) >>
  simp[]
QED

Finalise store_slots_word_copy_op_prefix_counted


Theorem store_slots_word_copy_prefix_frame:
  !n. w2n (a:bytes32)+32*(n-1) < dimword (:256) ==>
    store_slots_ptr_frame tr a k s tn (GENLIST I n)
      (store_copy_prefix (if tr then LocTransient else LocStorage) a k s n)
      (assign_base_store_taint_prefix (if tr then LocTransient else LocStorage) a k tn n)
Proof
  Induct >> strip_tac
  >- simp[assign_base_store_prefix_zero, assign_base_store_taint_prefix_def,
       store_slots_ptr_frame_nil] >>
  `w2n a+32*(n-1) < dimword (:256)` by decide_tac >>
  first_x_assum drule >> strip_tac >>
  `w2n (a+n2w n*32w) = w2n a+32*n` by
    (gvs[] >>
     `n2w n * 32w = (n2w (32*n):bytes32)` by
       (once_rewrite_tac[MULT_COMM] >> simp[word_mul_n2w]) >>
     simp[typedMemoryCopyTheory.typed_copy_offset_nonwrap]) >>
  Cases_on `tr` >>
  fs[store_slots_ptr_frame_def] >>
  simp[store_slots_ptr_frame_def, store_slots_taint_def, GENLIST, FOLDL_SNOC,
      assign_base_store_prefix_suc, assign_base_store_taint_prefix_def] >>
  qpat_x_assum `store_copy_normalize s _ = _` (rewrite_tac o single o GSYM) >>
  simp[store_copy_normalize_def, sstore_def, tstore_def]
QED

Theorem store_slots_word_copy_frame:
  execution_frame u = execution_frame (store_copy_prefix (if tr then LocTransient else LocStorage) a k s n) /\
  assign_base_store_frame (if tr then LocTransient else LocStorage) a k s tn n u tf /\
  w2n a+32*(n-1) < dimword (:256) ==>
  store_slots_ptr_frame tr a k s tn (GENLIST I n) u tf
Proof
  strip_tac >> drule store_slots_normalize_execution_frame >>
  disch_then (qspec_then `s` assume_tac) >>
  drule store_slots_word_copy_prefix_frame >>
  disch_then (qspecl_then [`tr`, `tn`, `s`, `k`] strip_assume_tac) >>
  Cases_on `tr` >>
  gvs[store_slots_ptr_frame_def, assign_base_store_frame_def]
QED

Theorem store_slots_word_copy_op_counted:
  !tr root slot count n sa z sb fn s G tn ctx D PG a k capacity.
    compile_word_copy_loop_op (Var root) slot count LocMemory
      (if tr then LocTransient else LocStorage) F sa = (z,sb) /\
    fn_has_code sa sb fn /\ not_fresh_at sa root /\
    (!x. slot = Var x \/ count = Var x ==> not_fresh_at sa x) /\
    ptr_covers G tn root s capacity /\ lookup_var root s = SOME a /\
    eval_operand slot s = SOME k /\ op_taint tn slot = {} /\
    eval_operand count s = SOME (n2w n) /\ op_taint tn count = {} /\ op_prov G count = NONE /\
    ~s.vs_halted /\ ~s.vs_call_ctx.cc_static /\ ~ctx_has_dalloca ctx /\
    s.vs_current_bb = sa.cs_current_bb /\ s.vs_inst_idx = LENGTH sa.cs_current_insts /\
    n < dimword (:256) /\ 32*n <= capacity /\ w2n a+32*(n-1) < dimword (:256) ==>
    ?Gf tf u.
      gas_path_ptr D 0 ctx fn PG G tn s 0 Gf tf (OK u) /\
      store_slots_ptr_frame tr a k s tn (GENLIST I n) u tf /\
      ptr_covers Gf tf root u capacity /\ lookup_var root u = SOME a /\
      u.vs_allocas = s.vs_allocas /\ u.vs_labels = s.vs_labels /\
      u.vs_call_ctx = s.vs_call_ctx /\ u.vs_alloca_next = s.vs_alloca_next /\
      u.vs_current_bb = sb.cs_current_bb /\
      u.vs_inst_idx = LENGTH sb.cs_current_insts /\ ~u.vs_halted /\
      (!x. not_fresh_at sa x ==> lookup_var x u = lookup_var x s /\
        FLOOKUP Gf x = FLOOKUP G x /\ op_taint tf (Var x) = op_taint tn (Var x))
Proof
  rpt gen_tac >> strip_tac >> drule_all store_slots_word_copy_op_prefix_counted >>
  disch_then (qspecl_then [`D`, `PG`] mp_tac) >>
  disch_then (qx_choose_then `gf` (qx_choose_then `tf` (qx_choose_then `u` strip_assume_tac))) >>
  drule_all store_slots_word_copy_frame >> strip_tac >>
  qexistsl_tac [`gf`, `tf`, `u`] >> asm_rewrite_tac[] >>
  qpat_x_assum `execution_frame u = _` mp_tac >>
  Cases_on `tr` >>
  simp[execution_frame_def, store_copy_prefix_def,
    SRULE [] (Q.INST [`tr` |-> `T`] (SPEC_ALL assign_base_store_backend_fold)),
    SRULE [] (Q.INST [`tr` |-> `F`] (SPEC_ALL assign_base_store_backend_fold))] >>
  rpt strip_tac >> asm_rewrite_tac[]
QED
