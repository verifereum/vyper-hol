(* Counted storage-copy instructions. Loaded words may carry dead-byte taint. *)
Theory assignBasePtrStoragePath
Ancestors
  wordLoadStorePtr assignBasePtrWordStore assignBasePtrStorageCoverage typedCopyPtr
  typedCopyLoopHeaderPtr fragGasPathPtr fragGasSeqPtr fragExecPtr
  ptrDiscipline ptrSafeRun venomExecSemantics venomState venomInst
  stateFrame finite_map pred_set words combin decoderGhostFramePtr arithmetic list

Theorem assign_base_mload_counted:
  !s fn bb id src tmp a tn G ctx D PG.
    ~s.vs_halted /\ lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
    get_instruction bb s.vs_inst_idx =
      SOME (mk_inst id MLOAD [Var src] [tmp]) /\
    ptr_covers G tn src s 32 /\ ~ctx_has_dalloca ctx /\
    lookup_var src s = SOME a ==>
    gas_path_ptr D 0 ctx fn PG G tn s 0
      (step_prov PG G (mk_inst id MLOAD [Var src] [tmp])
        (update_var tmp (mload (w2n a) s) s))
      (step_taint (mk_inst id MLOAD [Var src] [tmp]) s
        (update_var tmp (mload (w2n a) s) s) tn)
      (OK ((update_var tmp (mload (w2n a) s) s) with
        vs_inst_idx := SUC s.vs_inst_idx))
Proof
  rpt gen_tac >> strip_tac >>
  `step_inst_base (mk_inst id MLOAD [Var src] [tmp]) s =
   OK (update_var tmp (mload (w2n a) s) s)` by
    (PURE_ONCE_REWRITE_TAC[step_inst_base_def] >>
     simp[mk_inst_def, exec_read1_def, eval_operand_def]) >>
  `ptr_inst_ok D 0 0 ctx fn G tn
     (mk_inst id MLOAD [Var src] [tmp]) s` by
    (irule ptr_inst_ok_mload >> simp[]) >>
  irule (SRULE [mk_inst_def, is_terminator_def]
    (Q.INST [`n` |-> `0`, `lo` |-> `0`,
      `i` |-> `mk_inst id MLOAD [Var src] [tmp]`] gas_path_ptr_step)) >>
  simp[GSYM mk_inst_def] >> goal_assum (drule_at Any) >> simp[] >>
  irule (cj 1 gas_path_ptr_rules) >> simp[update_var_def]
QED

Theorem assign_base_mload_ghost:
  !PG G tn s id src tmp a.
    eval_operand src s = SOME a ==>
    step_prov PG G (mk_inst id MLOAD [src] [tmp])
      (update_var tmp (mload (w2n a) s) s) = DRESTRICT G (COMPL {tmp}) /\
    step_taint (mk_inst id MLOAD [src] [tmp]) s
      (update_var tmp (mload (w2n a) s) s) tn =
      (tn with t_var := tn.t_var |+ (tmp,mem_word_taint tn.t_mem (w2n a)))
Proof
  rpt strip_tac >>
  simp[step_prov_def, set_prov_def, out_prov_def, step_taint_def,
       set_var_taint_def, out_taint_def, mk_inst_def, mem_taint_def,
       step_writes_def, codegenRelTheory.source_memory_write_ranges_def,
       written_taint_def, range_bytes_def, store_taint_def, adopt_reset_def,
       imm_taint_def, new_site_bytes_def, execution_frame_def, update_var_def, FLOOKUP_DEF,
       EXTENSION, taint_component_equality] >> metis_tac[]
QED

Theorem assign_base_storage_word_counted:
  !s fn bb id tr addr value tn G ctx D PG k w u Gf tf.
    ~s.vs_halted /\ lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
    get_instruction bb s.vs_inst_idx =
      SOME (mk_inst id (if tr then TSTORE else SSTORE) [addr; value] []) /\
    op_taint tn addr = {} /\
    ~ctx_has_dalloca ctx /\ ~s.vs_call_ctx.cc_static /\
    eval_operand addr s = SOME k /\ eval_operand value s = SOME w /\
    u = ((if tr then tstore k w s else sstore k w s)
      with vs_inst_idx := SUC s.vs_inst_idx) /\
    Gf = step_prov PG G (mk_inst id (if tr then TSTORE else SSTORE)
      [addr; value] []) (if tr then tstore k w s else sstore k w s) /\
    tf = step_taint (mk_inst id (if tr then TSTORE else SSTORE)
      [addr; value] []) s (if tr then tstore k w s else sstore k w s) tn ==>
    gas_path_ptr D 0 ctx fn PG G tn s 0 Gf tf (OK u)
Proof
  rpt gen_tac >> strip_tac >>
  `step_inst_base (mk_inst id (if tr then TSTORE else SSTORE)
     [addr; value] []) s =
     OK (if tr then tstore k w s else sstore k w s)` by
    (Cases_on `tr` >> PURE_ONCE_REWRITE_TAC[step_inst_base_def] >>
     pure_rewrite_tac[COND_CLAUSES, mk_inst_def, instruction_accessors,
                      instruction_accfupds, K_THM, opcode_case_def] >>
     simp[exec_write2_def]) >>
  gvs[] >>
  irule (SRULE [] (Q.INST [`n` |-> `0`, `m` |-> `0`]
    (SPEC_ALL (cj 2 gas_path_ptr_rules)))) >>
  qexistsl_tac [
    `step_prov PG G (mk_inst id (if tr then TSTORE else SSTORE) [addr; value] [])
      (if tr then tstore k w s else sstore k w s)`,
    `(if tr then tstore k w s else sstore k w s) with vs_inst_idx := SUC s.vs_inst_idx`,
    `step_taint (mk_inst id (if tr then TSTORE else SSTORE) [addr; value] []) s
      (if tr then tstore k w s else sstore k w s) tn`] >> conj_tac
  >- (Cases_on `tr` >> simp[cj 1 gas_path_ptr_rules, sstore_def, tstore_def]) >>
  irule assign_base_storage_word_edge_ptr >> simp[] >> Cases_on `tr` >> simp[]
QED

Theorem assign_base_copy_binop_counted:
  !s fn bb id opc left right tmp w tn G ctx D PG.
    ~s.vs_halted /\ lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
    get_instruction bb s.vs_inst_idx =
      SOME (mk_inst id opc [left;right] [tmp]) /\
    (opc = MUL \/ opc = ADD \/ opc = AND) /\
    op_taint tn left = {} /\ op_taint tn right = {} /\
    ~ctx_has_dalloca ctx /\
    step_inst_base (mk_inst id opc [left;right] [tmp]) s =
      OK (update_var tmp w s) ==>
    gas_path_ptr D 0 ctx fn PG G tn s 0
      (step_prov PG G (mk_inst id opc [left;right] [tmp]) (update_var tmp w s))
      (step_taint (mk_inst id opc [left;right] [tmp]) s (update_var tmp w s) tn)
      (OK ((update_var tmp w s) with vs_inst_idx := SUC s.vs_inst_idx))
Proof
  rpt gen_tac >> strip_tac >>
  `ptr_inst_ok D 0 0 ctx fn G tn (mk_inst id opc [left;right] [tmp]) s` by
    (Cases_on `opc = MUL`
     >- (irule typed_copy_loop_test_check >> simp[update_var_def] >>
         metis_tac[]) >>
     irule ptr_inst_ok_copy_len_binop >> simp[] >> metis_tac[]) >>
  mp_tac (Q.GENL [`u`, `G'`, `tn'`, `r`]
    (Q.INST [`n` |-> `0`, `lo` |-> `0`,
      `i` |-> `mk_inst id opc [left;right] [tmp]`] gas_path_ptr_step)) >>
  simp[mk_inst_def, is_terminator_def] >>
  disch_then irule >> simp[GSYM mk_inst_def] >>
  gvs[] >> irule (cj 1 gas_path_ptr_rules) >> simp[update_var_def]
QED

Theorem assign_base_storage_offset_counted:
  !s fn bb id root ctr mv a i total tn G ctx D PG.
    ~s.vs_halted /\ lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
    get_instruction bb s.vs_inst_idx =
      SOME (mk_inst id MUL [Var ctr;Lit 32w] [mv]) /\
    ptr_covers G tn root s total /\ lookup_var root s = SOME a /\
    lookup_var ctr s = SOME (n2w i) /\ op_taint tn (Var ctr) = {} /\
    root <> mv /\ ctr <> mv /\ ~ctx_has_dalloca ctx ==>
    ?Gf tf u.
      gas_path_ptr D 0 ctx fn PG G tn s 0 Gf tf (OK u) /\
      lookup_var root u = SOME a /\ lookup_var ctr u = SOME (n2w i) /\
      lookup_var mv u = SOME (n2w (32*i)) /\ op_taint tf (Var mv) = {} /\
      ptr_covers Gf tf root u total /\
      execution_frame u = execution_frame s /\
      u.vs_accounts = s.vs_accounts /\ u.vs_transient = s.vs_transient /\
      u.vs_call_ctx = s.vs_call_ctx /\
      u.vs_memory = s.vs_memory /\ tf.t_mem = tn.t_mem /\ tf.t_imm = tn.t_imm /\
      tf.t_stor = tn.t_stor /\ tf.t_trans = tn.t_trans /\
      u.vs_current_bb = s.vs_current_bb /\
      u.vs_inst_idx = SUC s.vs_inst_idx /\ ~u.vs_halted /\
      (!x. x <> mv ==> lookup_var x u = lookup_var x s /\
         FLOOKUP Gf x = FLOOKUP G x /\ op_taint tf (Var x) = op_taint tn (Var x))
Proof
  rpt gen_tac >> strip_tac >>
  qabbrev_tac `v = update_var mv (n2w (32*i)) s` >>
  `step_inst_base (mk_inst id MUL [Var ctr;Lit 32w] [mv]) s = OK v` by
    (PURE_ONCE_REWRITE_TAC[step_inst_base_def] >>
     pure_rewrite_tac[mk_inst_def, instruction_accessors, instruction_accfupds,
                      K_THM, opcode_case_def] >>
     simp[Abbr `v`, exec_pure2_def, eval_operand_def] >>
     once_rewrite_tac[MULT_COMM] >> simp[word_mul_n2w]) >>
  `gas_path_ptr D 0 ctx fn PG G tn s 0
     (step_prov PG G (mk_inst id MUL [Var ctr;Lit 32w] [mv]) v)
     (step_taint (mk_inst id MUL [Var ctr;Lit 32w] [mv]) s v tn)
     (OK (v with vs_inst_idx := SUC s.vs_inst_idx))` by
    (simp[Abbr `v`] >> irule assign_base_copy_binop_counted >>
     gvs[op_taint_def] >> goal_assum (drule_at Any) >> simp[]) >>
  `step_prov PG G (mk_inst id MUL [Var ctr;Lit 32w] [mv]) v =
     DRESTRICT G (COMPL {mv}) /\
   step_taint (mk_inst id MUL [Var ctr;Lit 32w] [mv]) s v tn =
     (tn with t_var := tn.t_var |+ (mv,{}))` by
    (irule typed_copy_loop_arith_ghost_clean >>
     simp[Abbr `v`, update_var_def] >> rw[] >> gvs[op_taint_def]) >>
  qexistsl_tac [`DRESTRICT G (COMPL {mv})`,
    `tn with t_var := tn.t_var |+ (mv,{})`,
    `v with vs_inst_idx := SUC s.vs_inst_idx`] >>
  gvs[Abbr `v`, execution_frame_def, update_var_def, lookup_var_def, FLOOKUP_UPDATE,
      bodyPtrDefsTheory.ptr_covers_def, op_taint_def, FLOOKUP_DRESTRICT]
QED

Theorem assign_base_storage_address_counted:
  !s fn bb id root offset tmp a off total tn G ctx D PG.
    ~s.vs_halted /\ lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
    get_instruction bb s.vs_inst_idx =
      SOME (mk_inst id ADD [Var root;offset] [tmp]) /\
    ptr_covers G tn root s total /\ lookup_var root s = SOME a /\
    eval_operand offset s = SOME (n2w off) /\ op_taint tn offset = {} /\
    off < total /\ off + 32 <= total /\
    w2n a + off < dimword (:256) /\ root <> tmp /\ ~ctx_has_dalloca ctx ==>
    ?Gf tf u.
      gas_path_ptr D 0 ctx fn PG G tn s 0 Gf tf (OK u) /\
      lookup_var tmp u = SOME (a + n2w off) /\ ptr_covers Gf tf tmp u 32 /\
      ptr_covers Gf tf root u total /\
      execution_frame u = execution_frame s /\
      u.vs_accounts = s.vs_accounts /\ u.vs_transient = s.vs_transient /\
      u.vs_call_ctx = s.vs_call_ctx /\
      u.vs_memory = s.vs_memory /\ tf.t_mem = tn.t_mem /\ tf.t_imm = tn.t_imm /\
      tf.t_stor = tn.t_stor /\ tf.t_trans = tn.t_trans /\
      u.vs_current_bb = s.vs_current_bb /\
      u.vs_inst_idx = SUC s.vs_inst_idx /\ ~u.vs_halted /\
      (!x. x <> tmp ==> lookup_var x u = lookup_var x s /\
         FLOOKUP Gf x = FLOOKUP G x /\ op_taint tf (Var x) = op_taint tn (Var x))
Proof
  rpt gen_tac >> strip_tac >>
  qabbrev_tac `v = update_var tmp (a + n2w off) s` >>
  qabbrev_tac `gf = step_prov PG G (mk_inst id ADD [Var root;offset] [tmp]) v` >>
  qabbrev_tac `tf = step_taint (mk_inst id ADD [Var root;offset] [tmp]) s v tn` >>
  `op_taint tn (Var root) = {}` by gvs[bodyPtrDefsTheory.ptr_covers_def] >>
  `step_inst_base (mk_inst id ADD [Var root;offset] [tmp]) s = OK v` by
    (PURE_ONCE_REWRITE_TAC[step_inst_base_def] >>
     pure_rewrite_tac[mk_inst_def, instruction_accessors, instruction_accfupds,
                      K_THM, opcode_case_def] >>
     simp[Abbr `v`, exec_pure2_def, eval_operand_def]) >>
  `gas_path_ptr D 0 ctx fn PG G tn s 0 gf tf
     (OK (v with vs_inst_idx := SUC s.vs_inst_idx))` by
    (simp[Abbr `v`, Abbr `gf`, Abbr `tf`] >>
     irule assign_base_copy_binop_counted >> simp[] >>
     goal_assum (drule_at Any) >> simp[]) >>
  `ptr_covers gf tf tmp v 32` by
    (simp[Abbr `v`, Abbr `gf`, Abbr `tf`] >>
     irule typed_copy_loop_dynamic_offset_covers >>
     simp[] >> goal_assum (drule_at Any) >> simp[]) >>
  qexistsl_tac [`gf`, `tf`, `v with vs_inst_idx := SUC s.vs_inst_idx`] >>
  simp[bodyPtrDefsTheory.ptr_covers_def, lookup_var_def] >>
  simp[Abbr `gf`, Abbr `tf`, Abbr `v`, execution_frame_def, update_var_def,
       copy_len_binop_ghost_frame, lookup_var_def, FLOOKUP_UPDATE,
       step_prov_other_output, step_taint_other_output, step_taint_def,
       adopt_reset_def, imm_taint_def, mk_inst_def] >>
  gvs[bodyPtrDefsTheory.ptr_covers_def, lookup_var_def, execution_frame_def, update_var_def,
      mk_inst_def, FLOOKUP_UPDATE] >> metis_tac[]
QED

Theorem assign_base_storage_load_counted:
  !s fn bb id src tmp a tn G ctx D PG.
    ~s.vs_halted /\ lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
    get_instruction bb s.vs_inst_idx =
      SOME (mk_inst id MLOAD [Var src] [tmp]) /\
    ptr_covers G tn src s 32 /\ lookup_var src s = SOME a /\
    src <> tmp /\ ~ctx_has_dalloca ctx ==>
    ?Gf tf u.
      gas_path_ptr D 0 ctx fn PG G tn s 0 Gf tf (OK u) /\
      lookup_var tmp u = SOME (mload (w2n a) s) /\
      op_taint tf (Var tmp) = mem_word_taint tn.t_mem (w2n a) /\
      FLOOKUP Gf tmp = NONE /\ ptr_covers Gf tf src u 32 /\
      execution_frame u = execution_frame s /\
      u.vs_accounts = s.vs_accounts /\ u.vs_transient = s.vs_transient /\
      u.vs_call_ctx = s.vs_call_ctx /\
      u.vs_memory = s.vs_memory /\ tf.t_mem = tn.t_mem /\ tf.t_imm = tn.t_imm /\
      tf.t_stor = tn.t_stor /\ tf.t_trans = tn.t_trans /\
      u.vs_current_bb = s.vs_current_bb /\
      u.vs_inst_idx = SUC s.vs_inst_idx /\ ~u.vs_halted /\
      (!x. x <> tmp ==> lookup_var x u = lookup_var x s /\
         FLOOKUP Gf x = FLOOKUP G x /\ op_taint tf (Var x) = op_taint tn (Var x))
Proof
  rpt gen_tac >> strip_tac >>
  drule_all assign_base_mload_counted >>
  disch_then (qspecl_then [`D`, `PG`] mp_tac) >>
  `eval_operand (Var src) s = SOME a` by simp[eval_operand_def] >>
  drule assign_base_mload_ghost >>
  disch_then (qspecl_then [`PG`, `G`, `tn`, `id`, `tmp`] assume_tac) >>
  strip_tac >>
  qexistsl_tac [`DRESTRICT G (COMPL {tmp})`,
    `tn with t_var := tn.t_var |+ (tmp,mem_word_taint tn.t_mem (w2n a))`,
    `(update_var tmp (mload (w2n a) s) s) with vs_inst_idx := SUC s.vs_inst_idx`] >>
  gvs[bodyPtrDefsTheory.ptr_covers_def, execution_frame_def, update_var_def, lookup_var_def,
      op_taint_def, FLOOKUP_UPDATE, FLOOKUP_DRESTRICT]
QED

Theorem assign_base_storage_source_prefix:
  !s fn bb id root ctr mv sv vv a i k total tn G ctx D PG.
    ~s.vs_halted /\ lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
    get_instruction bb s.vs_inst_idx =
      SOME (mk_inst id MUL [Var ctr;Lit 32w] [mv]) /\
    get_instruction bb (SUC s.vs_inst_idx) =
      SOME (mk_inst (id+1) ADD [Var root;Var mv] [sv]) /\
    get_instruction bb (s.vs_inst_idx+2) =
      SOME (mk_inst (id+2) MLOAD [Var sv] [vv]) /\
    ptr_covers G tn root s total /\ lookup_var root s = SOME a /\
    lookup_var ctr s = SOME (n2w i) /\ op_taint tn (Var ctr) = {} /\
    ALL_DISTINCT [ctr;mv;sv;vv] /\ ~MEM root [mv;sv;vv] /\
    i < k /\ 32*k <= total /\ w2n a + 32*(k-1) < dimword (:256) /\
    ~ctx_has_dalloca ctx ==>
    ?Gf tf u.
      gas_path_ptr D 0 ctx fn PG G tn s 0 Gf tf (OK u) /\
      lookup_var ctr u = SOME (n2w i) /\
      lookup_var vv u = SOME (mload (w2n (a + n2w (32*i))) s) /\
      op_taint tf (Var vv) = mem_word_taint tn.t_mem (w2n (a + n2w (32*i))) /\
      FLOOKUP Gf vv = NONE /\
      execution_frame u = execution_frame s /\
      u.vs_accounts = s.vs_accounts /\ u.vs_transient = s.vs_transient /\
      u.vs_call_ctx = s.vs_call_ctx /\
      u.vs_memory = s.vs_memory /\ tf.t_mem = tn.t_mem /\ tf.t_imm = tn.t_imm /\
      tf.t_stor = tn.t_stor /\ tf.t_trans = tn.t_trans /\
      u.vs_current_bb = s.vs_current_bb /\
      u.vs_inst_idx = s.vs_inst_idx+3 /\ ~u.vs_halted /\
      (!x. ~MEM x [mv;sv;vv] ==> lookup_var x u = lookup_var x s /\
         FLOOKUP Gf x = FLOOKUP G x /\ op_taint tf (Var x) = op_taint tn (Var x))
Proof
  rpt gen_tac >> strip_tac >> rename1 `ptr_covers G tn root s capacity` >>
  `root <> mv /\ root <> sv /\ ctr <> mv /\ sv <> vv /\
   32*i < capacity /\ 32*i+32 <= capacity /\
   w2n a + 32*i < dimword (:256)` by
    (gvs[ALL_DISTINCT] >> decide_tac) >>
  drule_all assign_base_storage_offset_counted >>
  disch_then (qspecl_then [`D`, `PG`] mp_tac) >>
  disch_then (qx_choose_then `g1` (qx_choose_then `t1`
    (qx_choose_then `s1` strip_assume_tac))) >>
  `lookup_block s1.vs_current_bb fn.fn_blocks = SOME bb /\
   get_instruction bb s1.vs_inst_idx =
     SOME (mk_inst (id+1) ADD [Var root;Var mv] [sv]) /\
   eval_operand (Var mv) s1 = SOME (n2w (32*i))` by simp[eval_operand_def] >>
  drule_all assign_base_storage_address_counted >>
  disch_then (qspecl_then [`D`, `PG`] mp_tac) >>
  disch_then (qx_choose_then `g2` (qx_choose_then `t2`
    (qx_choose_then `s2` strip_assume_tac))) >>
  `lookup_block s2.vs_current_bb fn.fn_blocks = SOME bb /\
   get_instruction bb s2.vs_inst_idx =
     SOME (mk_inst (id+2) MLOAD [Var sv] [vv])` by simp[ADD1] >>
  drule_all assign_base_storage_load_counted >>
  disch_then (qspecl_then [`D`, `PG`] mp_tac) >>
  disch_then (qx_choose_then `g3` (qx_choose_then `t3`
    (qx_choose_then `s3` strip_assume_tac))) >>
  qexistsl_tac [`g3`, `t3`, `s3`] >>
  conj_tac >-
    (qpat_x_assum `gas_path_ptr _ _ _ _ _ G tn s _ _ _ _`
       (mp_then Any mp_tac gas_path_ptr_then) >>
     disch_then drule >> simp[] >>
     disch_then (mp_then Any mp_tac gas_path_ptr_then) >>
     disch_then drule >> simp[]) >>
  gvs[ALL_DISTINCT, mload_def, ADD1] >> metis_tac[]
QED

Theorem assign_base_storage_write_counted:
  !s fn bb id tr addr value k w tn G ctx D PG.
    ~s.vs_halted /\ lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
    get_instruction bb s.vs_inst_idx =
      SOME (mk_inst id (if tr then TSTORE else SSTORE) [addr;value] []) /\
    eval_operand addr s = SOME k /\ eval_operand value s = SOME w /\
    op_taint tn addr = {} /\ ~ctx_has_dalloca ctx /\ ~s.vs_call_ctx.cc_static ==>
    gas_path_ptr D 0 ctx fn PG G tn s 0 G
      (if tr then tn with t_trans := key_update tn.t_trans k (op_taint tn value)
       else tn with t_stor := key_update tn.t_stor k (op_taint tn value))
      (OK ((if tr then tstore k w s else sstore k w s) with
        vs_inst_idx := SUC s.vs_inst_idx))
Proof
  rpt gen_tac >> strip_tac >>
  `(if tr then tstore k w s else sstore k w s).vs_allocas = s.vs_allocas /\
   (if tr then tstore k w s else sstore k w s).vs_fmp = s.vs_fmp` by
    (Cases_on `tr` >> simp[tstore_def, sstore_def]) >>
  `step_prov PG G (mk_inst id (if tr then TSTORE else SSTORE) [addr;value] [])
       (if tr then tstore k w s else sstore k w s) = G /\
   step_taint (mk_inst id (if tr then TSTORE else SSTORE) [addr;value] []) s
       (if tr then tstore k w s else sstore k w s) tn =
       (if tr then tn with t_trans := key_update tn.t_trans k (op_taint tn value)
        else tn with t_stor := key_update tn.t_stor k (op_taint tn value))` by
    (Cases_on `tr` >> gvs[]
     >- (irule (SRULE [] (Q.SPEC `TSTORE` assign_base_storage_word_ghost)) >> simp[]) >>
     irule (SRULE [] (Q.SPEC `SSTORE` assign_base_storage_word_ghost)) >> simp[]) >>
  irule assign_base_storage_word_counted >> simp[] >>
  goal_assum (drule_at Any) >> simp[] >>
  qexistsl_tac [`id`, `tr`, `value`, `w`] >> simp[]
QED

Theorem assign_base_storage_add_counted:
  !s fn bb id left right out a b tn G ctx D PG.
    ~s.vs_halted /\ lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
    get_instruction bb s.vs_inst_idx =
      SOME (mk_inst id ADD [left;right] [out]) /\
    eval_operand left s = SOME a /\ eval_operand right s = SOME b /\
    op_taint tn left = {} /\ op_taint tn right = {} /\ ~ctx_has_dalloca ctx ==>
    ?Gf tf u.
      gas_path_ptr D 0 ctx fn PG G tn s 0 Gf tf (OK u) /\
      u = (update_var out (a+b) s) with vs_inst_idx := SUC s.vs_inst_idx /\
      op_taint tf (Var out) = {} /\
      (first_prov G [left;right] = NONE ==> FLOOKUP Gf out = NONE) /\
      tf.t_mem = tn.t_mem /\ tf.t_imm = tn.t_imm /\ tf.t_stor = tn.t_stor /\ tf.t_trans = tn.t_trans /\
      (!x. x <> out ==> FLOOKUP Gf x = FLOOKUP G x /\
        op_taint tf (Var x) = op_taint tn (Var x))
Proof
  rpt gen_tac >> strip_tac >>
  `step_inst_base (mk_inst id ADD [left;right] [out]) s =
     OK (update_var out (a+b) s)` by
    (PURE_ONCE_REWRITE_TAC[step_inst_base_def] >>
     pure_rewrite_tac[mk_inst_def, instruction_accessors, instruction_accfupds,
                      K_THM, opcode_case_def] >> simp[exec_pure2_def]) >>
  qexistsl_tac [
    `step_prov PG G (mk_inst id ADD [left;right] [out]) (update_var out (a+b) s)`,
    `step_taint (mk_inst id ADD [left;right] [out]) s (update_var out (a+b) s) tn`,
    `(update_var out (a+b) s) with vs_inst_idx := SUC s.vs_inst_idx`] >>
  conj_tac >- (irule assign_base_copy_binop_counted >> simp[] >>
    goal_assum (drule_at Any) >> simp[]) >>
  `first_prov G [left;right] = NONE ==>
    FLOOKUP (step_prov PG G (mk_inst id ADD [left;right] [out])
      (update_var out (a+b) s)) out = NONE` by
    simp[step_prov_def, set_prov_def, out_prov_def, mk_inst_def, FLOOKUP_DRESTRICT] >>
  `(step_taint (mk_inst id ADD [left;right] [out]) s
      (update_var out (a+b) s) tn).t_imm = tn.t_imm` by
    simp[step_taint_def, adopt_reset_def, imm_taint_def, mk_inst_def] >>
  simp[] >> irule copy_len_binop_ghost_frame >> simp[]
QED

Theorem assign_base_storage_destination_prefix:
  !s fn bb id tr dst ctr vv dv k i w tn G ctx D PG.
    ~s.vs_halted /\ lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
    get_instruction bb s.vs_inst_idx =
      SOME (mk_inst id ADD [dst;Var ctr] [dv]) /\
    get_instruction bb (SUC s.vs_inst_idx) =
      SOME (mk_inst (id+1) (if tr then TSTORE else SSTORE) [Var dv;Var vv] []) /\
    eval_operand dst s = SOME k /\ lookup_var ctr s = SOME (n2w i) /\
    lookup_var vv s = SOME w /\ op_taint tn dst = {} /\
    op_taint tn (Var ctr) = {} /\ dv <> ctr /\ dv <> vv /\
    ~ctx_has_dalloca ctx /\ ~s.vs_call_ctx.cc_static ==>
    ?Gf tf u.
      gas_path_ptr D 0 ctx fn PG G tn s 0 Gf tf (OK u) /\
      u.vs_memory = s.vs_memory /\ tf.t_mem = tn.t_mem /\ tf.t_imm = tn.t_imm /\
      tf.t_stor = (if tr then tn.t_stor else
        key_update tn.t_stor (k+n2w i) (op_taint tn (Var vv))) /\
      tf.t_trans = (if tr then
        key_update tn.t_trans (k+n2w i) (op_taint tn (Var vv)) else tn.t_trans) /\
      execution_frame u = execution_frame (if tr then tstore (k+n2w i) w s else sstore (k+n2w i) w s) /\
      u.vs_accounts = (if tr then s.vs_accounts else (sstore (k+n2w i) w s).vs_accounts) /\
      u.vs_transient = (if tr then (tstore (k+n2w i) w s).vs_transient else s.vs_transient) /\
      u.vs_current_bb = s.vs_current_bb /\ u.vs_inst_idx = s.vs_inst_idx+2 /\
      u.vs_call_ctx = s.vs_call_ctx /\ ~u.vs_halted /\
      (!x. x <> dv ==> lookup_var x u = lookup_var x s /\
        FLOOKUP Gf x = FLOOKUP G x /\ op_taint tf (Var x) = op_taint tn (Var x))
Proof
  rpt gen_tac >> strip_tac >>
  `eval_operand (Var ctr) s = SOME (n2w i)` by simp[eval_operand_def] >>
  drule_all assign_base_storage_add_counted >>
  disch_then (qspecl_then [`G`, `D`, `PG`] mp_tac) >>
  disch_then (qx_choose_then `g1` (qx_choose_then `t1`
    (qx_choose_then `s1` strip_assume_tac))) >>
  `~s1.vs_halted /\ lookup_block s1.vs_current_bb fn.fn_blocks = SOME bb /\
   get_instruction bb s1.vs_inst_idx =
     SOME (mk_inst (id+1) (if tr then TSTORE else SSTORE) [Var dv;Var vv] []) /\
   eval_operand (Var dv) s1 = SOME (k+n2w i) /\
   eval_operand (Var vv) s1 = SOME w /\ ~s1.vs_call_ctx.cc_static` by
    gvs[execution_frame_def, update_var_def, eval_operand_def, lookup_var_def, FLOOKUP_UPDATE] >>
  drule_all assign_base_storage_write_counted >>
  disch_then (qspecl_then [`g1`, `D`, `PG`] mp_tac) >> strip_tac >>
  qexistsl_tac [`g1`,
    `if tr then t1 with t_trans := key_update t1.t_trans (k+n2w i) (op_taint t1 (Var vv))
     else t1 with t_stor := key_update t1.t_stor (k+n2w i) (op_taint t1 (Var vv))`,
    `(if tr then tstore (k+n2w i) w s1 else sstore (k+n2w i) w s1)
       with vs_inst_idx := SUC s1.vs_inst_idx`] >>
  conj_tac >-
    (qpat_x_assum `gas_path_ptr _ _ _ _ _ G tn s _ _ _ _`
       (mp_then Any mp_tac gas_path_ptr_then) >> disch_then drule >> simp[]) >>
  Cases_on `tr` >>
  gvs[execution_frame_def, update_var_def, sstore_def, tstore_def, lookup_var_def, FLOOKUP_UPDATE,
      op_taint_def, ADD1]
QED

Theorem assign_base_storage_assign_counted:
  !s fn bb id src out w tn G ctx D PG.
    ~s.vs_halted /\ lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
    get_instruction bb s.vs_inst_idx = SOME (mk_inst id ASSIGN [Var src] [out]) /\
    lookup_var src s = SOME w /\ FLOOKUP G src = NONE /\
    op_taint tn (Var src) = {} /\ ~ctx_has_dalloca ctx ==>
    gas_path_ptr D 0 ctx fn PG G tn s 0 (DRESTRICT G (COMPL {out}))
      (tn with t_var := tn.t_var |+ (out,{}))
      (OK ((update_var out w s) with vs_inst_idx := SUC s.vs_inst_idx))
Proof
  rpt gen_tac >> strip_tac >>
  `step_inst_base (mk_inst id ASSIGN [Var src] [out]) s = OK (update_var out w s)` by
    (PURE_ONCE_REWRITE_TAC[step_inst_base_def] >>
     pure_rewrite_tac[mk_inst_def, instruction_accessors, instruction_accfupds,
                      K_THM, opcode_case_def] >> simp[eval_operand_def]) >>
  `ptr_inst_ok D 0 0 ctx fn G tn (mk_inst id ASSIGN [Var src] [out]) s` by
    (simp[ptr_inst_ok_def, access_ok_def, taint_ok_def, allocas_from_def,
          mk_inst_def, codegenRelTheory.source_memory_write_ranges_def,
          contextCodegenRelTheory.source_memory_read_ranges_def] >>
     simp[GSYM mk_inst_def, step_inst_non_invoke, update_var_def]) >>
  `step_prov PG G (mk_inst id ASSIGN [Var src] [out]) (update_var out w s) =
      DRESTRICT G (COMPL {out}) /\
   step_taint (mk_inst id ASSIGN [Var src] [out]) s (update_var out w s) tn =
      (tn with t_var := tn.t_var |+ (out,{}))` by
    (simp[step_prov_def, set_prov_def, out_prov_def, op_prov_def,
          step_taint_def, set_var_taint_def, out_taint_def, mk_inst_def,
          mem_taint_def, step_writes_def, codegenRelTheory.source_memory_write_ranges_def,
          written_taint_def, range_bytes_def, store_taint_def, adopt_reset_def,
          imm_taint_def, new_site_bytes_def, execution_frame_def, update_var_def, FLOOKUP_DEF,
          first_prov_def, eval_operand_def, EXTENSION, taint_component_equality] >>
     metis_tac[]) >>
  irule (SRULE [mk_inst_def, is_terminator_def]
    (Q.INST [`n` |-> `0`, `lo` |-> `0`,
      `i` |-> `mk_inst id ASSIGN [Var src] [out]`] gas_path_ptr_step)) >>
  simp[GSYM mk_inst_def] >> goal_assum (drule_at Any) >> simp[] >>
  irule (cj 1 gas_path_ptr_rules) >> simp[update_var_def]
QED

Theorem assign_base_storage_increment_prefix:
  !s fn bb id ctr nv i tn G ctx D PG.
    ~s.vs_halted /\ lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
    get_instruction bb s.vs_inst_idx =
      SOME (mk_inst id ADD [Var ctr;Lit 1w] [nv]) /\
    get_instruction bb (SUC s.vs_inst_idx) =
      SOME (mk_inst (id+1) ASSIGN [Var nv] [ctr]) /\
    lookup_var ctr s = SOME (n2w i) /\ FLOOKUP G ctr = NONE /\
    op_taint tn (Var ctr) = {} /\ ctr <> nv /\ ~ctx_has_dalloca ctx ==>
    ?Gf tf u.
      gas_path_ptr D 0 ctx fn PG G tn s 0 Gf tf (OK u) /\
      lookup_var ctr u = SOME (n2w (SUC i)) /\ FLOOKUP Gf ctr = NONE /\
      op_taint tf (Var ctr) = {} /\
      execution_frame u = execution_frame s /\
      u.vs_accounts = s.vs_accounts /\ u.vs_transient = s.vs_transient /\
      u.vs_call_ctx = s.vs_call_ctx /\
      u.vs_memory = s.vs_memory /\ tf.t_mem = tn.t_mem /\ tf.t_imm = tn.t_imm /\
      tf.t_stor = tn.t_stor /\ tf.t_trans = tn.t_trans /\
      u.vs_current_bb = s.vs_current_bb /\ u.vs_inst_idx = s.vs_inst_idx+2 /\ ~u.vs_halted /\
      (!x. x <> ctr /\ x <> nv ==> lookup_var x u = lookup_var x s /\
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
   get_instruction bb s1.vs_inst_idx = SOME (mk_inst (id+1) ASSIGN [Var nv] [ctr]) /\
   lookup_var nv s1 = SOME (n2w i+1w) /\ FLOOKUP g1 nv = NONE` by
    gvs[execution_frame_def, update_var_def, lookup_var_def, FLOOKUP_UPDATE, first_prov_def, op_prov_def] >>
  drule_all assign_base_storage_assign_counted >>
  disch_then (qspecl_then [`D`, `PG`] mp_tac) >> strip_tac >>
  qexistsl_tac [`DRESTRICT g1 (COMPL {ctr})`, `t1 with t_var := t1.t_var |+ (ctr,{})`,
    `(update_var ctr (n2w i+1w) s1) with vs_inst_idx := SUC s1.vs_inst_idx`] >>
  conj_tac >-
    (qpat_x_assum `gas_path_ptr _ _ _ _ _ G tn s _ _ _ _`
       (mp_then Any mp_tac gas_path_ptr_then) >> disch_then drule >> simp[]) >>
  gvs[execution_frame_def, update_var_def, lookup_var_def, FLOOKUP_UPDATE, FLOOKUP_DRESTRICT,
      op_taint_def, ADD1, word_add_n2w]
QED

Theorem assign_base_storage_jump_counted:
  !s fn bb id lbl tn G ctx D PG.
    ~s.vs_halted /\ lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
    get_instruction bb s.vs_inst_idx = SOME (mk_inst id JMP [Label lbl] []) /\
    ~ctx_has_dalloca ctx ==>
    gas_path_ptr D 0 ctx fn PG G tn s 0 G tn (OK (jump_to lbl s))
Proof
  rpt gen_tac >> strip_tac >>
  `ptr_safe_step D 0 0 ctx fn PG G tn (mk_inst id JMP [Label lbl] []) s` by
    (simp[ptr_safe_step_def, ptr_inst_ok_def, access_ok_def, taint_ok_def,
          allocas_from_def, mk_inst_def, codegenRelTheory.source_memory_write_ranges_def,
          contextCodegenRelTheory.source_memory_read_ranges_def, op_taint_def] >>
     simp[GSYM mk_inst_def, step_inst_non_invoke] >>
     simp[mk_inst_def, venomExecProofsTheory.step_jmp_behavior, jump_to_def]) >>
  `gas_path_ptr_edge D 0 ctx fn PG G tn s 0 G tn (OK (jump_to lbl s))` by
    (rewrite_tac[gas_path_ptr_edge_def] >> simp[] >> qexists_tac `0:num` >>
     simp[step_inst_non_invoke, mk_inst_def, gasCountTheory.gas_count_step_def,
          venomExecProofsTheory.step_jmp_behavior, is_terminator_def] >>
     fs[mk_inst_def] >> metis_tac[]) >>
  `~(jump_to lbl s).vs_halted` by simp[jump_to_def] >>
  metis_tac[gas_path_ptr_rules, ADD_CLAUSES]
QED

Theorem assign_base_storage_test_counted:
  !s fn bb id opc ops out w tn G ctx D PG.
    ~s.vs_halted /\ lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
    get_instruction bb s.vs_inst_idx = SOME (mk_inst id opc ops [out]) /\
    (opc = LT /\ (?v k. ops = [Var v;Lit k]) \/ opc = ISZERO) /\
    (!op. MEM op ops ==> op_taint tn op = {}) /\ ~ctx_has_dalloca ctx /\
    step_inst_base (mk_inst id opc ops [out]) s = OK (update_var out w s) ==>
    gas_path_ptr D 0 ctx fn PG G tn s 0 (DRESTRICT G (COMPL {out}))
      (tn with t_var := tn.t_var |+ (out,{}))
      (OK ((update_var out w s) with vs_inst_idx := SUC s.vs_inst_idx))
Proof
  rpt gen_tac >> strip_tac >>
  `ptr_inst_ok D 0 0 ctx fn G tn (mk_inst id opc ops [out]) s` by
    (irule typed_copy_loop_test_check >> simp[update_var_def] >> metis_tac[]) >>
  `step_prov PG G (mk_inst id opc ops [out]) (update_var out w s) =
      DRESTRICT G (COMPL {out}) /\
   step_taint (mk_inst id opc ops [out]) s (update_var out w s) tn =
      (tn with t_var := tn.t_var |+ (out,{}))` by
    (irule typed_copy_loop_arith_ghost_clean >> simp[update_var_def] >> metis_tac[]) >>
  mp_tac (Q.GENL [`u`, `G'`, `tn'`, `r`]
    (Q.INST [`n` |-> `0`, `lo` |-> `0`,
      `i` |-> `mk_inst id opc ops [out]`] gas_path_ptr_step)) >>
  simp[mk_inst_def, is_terminator_def] >>
  disch_then irule >> simp[GSYM mk_inst_def] >>
  gvs[] >> irule (cj 1 gas_path_ptr_rules) >> simp[update_var_def]
QED

Theorem assign_base_storage_header_prefix:
  !s fn bb id ctr lt done i n tn G ctx D PG.
    ~s.vs_halted /\ lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
    get_instruction bb s.vs_inst_idx =
      SOME (mk_inst id LT [Var ctr;Lit (n2w n)] [lt]) /\
    get_instruction bb (SUC s.vs_inst_idx) =
      SOME (mk_inst (id+1) ISZERO [Var lt] [done]) /\
    lookup_var ctr s = SOME (n2w i) /\ i <= n /\ n < dimword (:256) /\
    op_taint tn (Var ctr) = {} /\ ALL_DISTINCT [ctr;lt;done] /\ ~ctx_has_dalloca ctx ==>
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
  `step_inst_base (mk_inst id LT [Var ctr;Lit (n2w n)] [lt]) s =
    OK (update_var lt (bool_to_word (i<n)) s)` by
    (PURE_ONCE_REWRITE_TAC[step_inst_base_def] >>
     pure_rewrite_tac[mk_inst_def, instruction_accessors, instruction_accfupds,
                      K_THM, opcode_case_def] >>
     simp[exec_pure2_def, eval_operand_def, w2n_n2w, LESS_MOD]) >>
  `gas_path_ptr D 0 ctx fn PG G tn s 0 g1 t1 (OK s1)` by
    (simp[Abbr `s1`, Abbr `g1`, Abbr `t1`] >>
     irule assign_base_storage_test_counted >> simp[] >>
     goal_assum (drule_at Any) >> simp[] >> rpt strip_tac >> gvs[op_taint_def]) >>
  `step_inst_base (mk_inst (id+1) ISZERO [Var lt] [done]) s1 =
     OK (update_var done (bool_to_word (~(i<n))) s1)` by
    (PURE_ONCE_REWRITE_TAC[step_inst_base_def] >>
     pure_rewrite_tac[mk_inst_def, instruction_accessors, instruction_accfupds,
                      K_THM, opcode_case_def] >>
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

Theorem assign_base_storage_branch_counted:
  !s fn bb id op yes no b tn G ctx D PG.
    ~s.vs_halted /\ lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
    get_instruction bb s.vs_inst_idx = SOME (mk_inst id JNZ [op;Label yes;Label no] []) /\
    eval_operand op s = SOME (if b then 1w else 0w) /\
    op_taint tn op = {} /\ ~ctx_has_dalloca ctx ==>
    gas_path_ptr D 0 ctx fn PG G tn s 0 G tn (OK (jump_to (if b then yes else no) s))
Proof
  rpt gen_tac >> strip_tac >>
  drule venomExecProofsTheory.step_jnz_behavior >>
  disch_then (qspecl_then [`yes`, `no`, `id`] assume_tac) >>
  `ptr_safe_step D 0 0 ctx fn PG G tn (mk_inst id JNZ [op;Label yes;Label no] []) s` by
    (simp[ptr_safe_step_def, ptr_inst_ok_def, access_ok_def, taint_ok_def,
          allocas_from_def, mk_inst_def, codegenRelTheory.source_memory_write_ranges_def,
          contextCodegenRelTheory.source_memory_read_ranges_def, op_taint_def] >>
     simp[GSYM mk_inst_def, step_inst_non_invoke] >>
     simp[mk_inst_def, venomExecProofsTheory.step_jnz_behavior, jump_to_def] >>
     Cases_on `b` >> gvs[op_taint_def] >>
     gen_tac >> Cases_on `op' = op` >> gvs[] >>
     Cases_on `op' = Label yes` >> gvs[] >> Cases_on `op' = Label no` >> gvs[]) >>
  `gas_path_ptr_edge D 0 ctx fn PG G tn s 0 G tn
     (OK (jump_to (if b then yes else no) s))` by
    (rewrite_tac[gas_path_ptr_edge_def] >> simp[] >> qexists_tac `0:num` >>
     simp[step_inst_non_invoke, mk_inst_def, gasCountTheory.gas_count_step_def,
          venomExecProofsTheory.step_jnz_behavior, is_terminator_def] >>
     Cases_on `b` >> gvs[mk_inst_def] >> metis_tac[]) >>
  `~(jump_to (if b then yes else no) s).vs_halted` by simp[jump_to_def] >>
  metis_tac[gas_path_ptr_rules, ADD_CLAUSES]
QED

Theorem assign_base_storage_header_counted:
  !s fn bb id ctr lt done i n bodylbl exit tn G ctx D PG.
    ~s.vs_halted /\ lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
    get_instruction bb s.vs_inst_idx =
      SOME (mk_inst id LT [Var ctr;Lit (n2w n)] [lt]) /\
    get_instruction bb (SUC s.vs_inst_idx) =
      SOME (mk_inst (id+1) ISZERO [Var lt] [done]) /\
    get_instruction bb (s.vs_inst_idx+2) =
      SOME (mk_inst (id+2) JNZ [Var done;Label exit;Label bodylbl] []) /\
    lookup_var ctr s = SOME (n2w i) /\ i <= n /\ n < dimword (:256) /\
    op_taint tn (Var ctr) = {} /\ ALL_DISTINCT [ctr;lt;done] /\ ~ctx_has_dalloca ctx ==>
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
  drule_all assign_base_storage_header_prefix >>
  disch_then (qspecl_then [`G`, `D`, `PG`] mp_tac) >>
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

Theorem assign_base_storage_copy_prefix:
  !s fn bb id root ctr mv sv vv dv a i n total k tr tn G ctx D PG.
    ~s.vs_halted /\ lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
    get_instruction bb s.vs_inst_idx = SOME (mk_inst id MUL [Var ctr;Lit 32w] [mv]) /\
    get_instruction bb (SUC s.vs_inst_idx) = SOME (mk_inst (id+1) ADD [Var root;Var mv] [sv]) /\
    get_instruction bb (s.vs_inst_idx+2) = SOME (mk_inst (id+2) MLOAD [Var sv] [vv]) /\
    get_instruction bb (s.vs_inst_idx+3) = SOME (mk_inst (id+3) ADD [Lit k;Var ctr] [dv]) /\
    get_instruction bb (s.vs_inst_idx+4) = SOME (mk_inst (id+4) (if tr then TSTORE else SSTORE) [Var dv;Var vv] []) /\
    ptr_covers G tn root s total /\ lookup_var root s = SOME a /\
    lookup_var ctr s = SOME (n2w i) /\ FLOOKUP G ctr = NONE /\ op_taint tn (Var ctr) = {} /\
    ALL_DISTINCT [root;ctr;mv;sv;vv;dv] /\
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
  `lookup_block s1.vs_current_bb fn.fn_blocks = SOME bb /\
   get_instruction bb s1.vs_inst_idx = SOME (mk_inst (id+3) ADD [Lit k;Var ctr] [dv]) /\
   get_instruction bb (SUC s1.vs_inst_idx) = SOME (mk_inst ((id+3)+1) (if tr then TSTORE else SSTORE) [Var dv;Var vv] []) /\
   eval_operand (Lit k) s1 = SOME k /\ op_taint t1 (Lit k) = {} /\
   op_taint t1 (Var ctr) = {} /\ ~s1.vs_call_ctx.cc_static` by
    gvs[ALL_DISTINCT, eval_operand_def, op_taint_def, ADD1] >>
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

Theorem assign_base_storage_body_counted:
  !s fn bb id root ctr mv sv vv dv nv a i n total k tr hdr tn G ctx D PG.
    ~s.vs_halted /\ lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
    get_instruction bb s.vs_inst_idx = SOME (mk_inst id MUL [Var ctr;Lit 32w] [mv]) /\
    get_instruction bb (SUC s.vs_inst_idx) = SOME (mk_inst (id+1) ADD [Var root;Var mv] [sv]) /\
    get_instruction bb (s.vs_inst_idx+2) = SOME (mk_inst (id+2) MLOAD [Var sv] [vv]) /\
    get_instruction bb (s.vs_inst_idx+3) = SOME (mk_inst (id+3) ADD [Lit k;Var ctr] [dv]) /\
    get_instruction bb (s.vs_inst_idx+4) = SOME (mk_inst (id+4) (if tr then TSTORE else SSTORE) [Var dv;Var vv] []) /\
    get_instruction bb (s.vs_inst_idx+5) = SOME (mk_inst (id+5) ADD [Var ctr;Lit 1w] [nv]) /\
    get_instruction bb (s.vs_inst_idx+6) = SOME (mk_inst (id+6) ASSIGN [Var nv] [ctr]) /\
    get_instruction bb (s.vs_inst_idx+7) = SOME (mk_inst (id+7) JMP [Label hdr] []) /\
    ptr_covers G tn root s total /\ lookup_var root s = SOME a /\
    lookup_var ctr s = SOME (n2w i) /\ FLOOKUP G ctr = NONE /\ op_taint tn (Var ctr) = {} /\
    ALL_DISTINCT [root;ctr;mv;sv;vv;dv;nv] /\
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
  drule_all assign_base_storage_copy_prefix >>
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

(* compile_word_copy_loop uses EQ/JNZ, not the LT/ISZERO header used by
   other copy loops. Keep this boundary tied to that actual emitted shape. *)
Theorem assign_base_storage_eq_counted:
  !s fn bb id ctr done i n tn G ctx D PG.
    ~s.vs_halted /\ lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
    get_instruction bb s.vs_inst_idx = SOME (mk_inst id EQ [Var ctr;Lit (n2w n)] [done]) /\
    lookup_var ctr s = SOME (n2w i) /\ i <= n /\ n < dimword (:256) /\
    op_taint tn (Var ctr) = {} /\ ~ctx_has_dalloca ctx ==>
    gas_path_ptr D 0 ctx fn PG G tn s 0 (DRESTRICT G (COMPL {done}))
      (tn with t_var := tn.t_var |+ (done,{}))
      (OK ((update_var done (bool_to_word (i=n)) s) with vs_inst_idx := SUC s.vs_inst_idx))
Proof
  rpt gen_tac >> strip_tac >>
  `step_inst_base (mk_inst id EQ [Var ctr;Lit (n2w n)] [done]) s =
     OK (update_var done (bool_to_word (i=n)) s)` by
    (PURE_ONCE_REWRITE_TAC[step_inst_base_def] >>
     pure_rewrite_tac[mk_inst_def, instruction_accessors, instruction_accfupds,
                      K_THM, opcode_case_def] >>
     simp[exec_pure2_def, eval_operand_def, n2w_11, LESS_MOD]) >>
  `ptr_inst_ok D 0 0 ctx fn G tn (mk_inst id EQ [Var ctr;Lit (n2w n)] [done]) s` by
    (simp[ptr_inst_ok_def, access_ok_def, taint_ok_def, allocas_from_def,
          mk_inst_def, codegenRelTheory.source_memory_write_ranges_def,
          contextCodegenRelTheory.source_memory_read_ranges_def, op_taint_def] >>
     simp[GSYM mk_inst_def, step_inst_non_invoke, update_var_def] >>
     gvs[op_taint_def] >> Cases >> gvs[]) >>
  `step_prov PG G (mk_inst id EQ [Var ctr;Lit (n2w n)] [done])
      (update_var done (bool_to_word (i=n)) s) = DRESTRICT G (COMPL {done}) /\
   step_taint (mk_inst id EQ [Var ctr;Lit (n2w n)] [done]) s
      (update_var done (bool_to_word (i=n)) s) tn =
      (tn with t_var := tn.t_var |+ (done,{}))` by
    (simp[step_prov_def, set_prov_def, out_prov_def, op_prov_def,
          step_taint_def, set_var_taint_def, out_taint_def, mk_inst_def,
          mem_taint_def, step_writes_def, codegenRelTheory.source_memory_write_ranges_def,
          written_taint_def, range_bytes_def, store_taint_def, adopt_reset_def,
          imm_taint_def, new_site_bytes_def, execution_frame_def, update_var_def, op_taint_def,
          eval_operand_def, EXTENSION, taint_component_equality] >>
     simp[FLOOKUP_DEF, SF CONJ_ss]) >>
  irule (SRULE [mk_inst_def, is_terminator_def]
    (Q.INST [`n` |-> `0`, `lo` |-> `0`,
      `i` |-> `mk_inst id EQ [Var ctr;Lit (n2w n)] [done]`] gas_path_ptr_step)) >>
  simp[GSYM mk_inst_def] >> goal_assum (drule_at Any) >> simp[] >>
  irule (cj 1 gas_path_ptr_rules) >> simp[update_var_def]
QED

Theorem assign_base_storage_copy_header:
  !s fn bb id ctr done i n bodylbl exit tn G ctx D PG.
    ~s.vs_halted /\ lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
    get_instruction bb s.vs_inst_idx = SOME (mk_inst id EQ [Var ctr;Lit (n2w n)] [done]) /\
    get_instruction bb (SUC s.vs_inst_idx) =
      SOME (mk_inst (id+1) JNZ [Var done;Label exit;Label bodylbl] []) /\
    lookup_var ctr s = SOME (n2w i) /\ i <= n /\ n < dimword (:256) /\
    op_taint tn (Var ctr) = {} /\ ctr <> done /\ ~ctx_has_dalloca ctx ==>
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
  qabbrev_tac `s1 = (update_var done (bool_to_word (i=n)) s)
    with vs_inst_idx := SUC s.vs_inst_idx` >>
  qabbrev_tac `g1 = DRESTRICT G (COMPL {done})` >>
  qabbrev_tac `t1 = tn with t_var := tn.t_var |+ (done,{})` >>
  `gas_path_ptr D 0 ctx fn PG G tn s 0 g1 t1 (OK s1)` by
    (simp[Abbr `s1`, Abbr `g1`, Abbr `t1`] >>
     irule assign_base_storage_eq_counted >> simp[] >>
     qexistsl_tac [`ctr`, `id`] >> simp[]) >>
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
