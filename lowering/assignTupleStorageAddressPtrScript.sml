(* Counted memory-to-storage copies with an evaluated destination operand. *)
Theory assignTupleStorageAddressPtr
Ancestors stmtLowering placeStoreCopyPath assignBasePtrStoragePath assignBasePtrStorageLoop assignBasePtrStorageLayout assignTuplePtrStorage context compileEnv
  loweringStateRelDefs emitHelper emitHelperProps stateFrame fragExec venomInst
  venomState venomExecSemantics ptrSafeRun ptrDiscipline fragGasSeqPtr
  fragGasPathPtr bodyPtrDefs words finite_map pred_set list rich_list arithmetic combin

Theorem tuple_storage_address_copy_prefix:
  !s fn bb id root dst ctr mv sv vv dv a i n total k tr tn G ctx D PG.
    ~s.vs_halted /\ lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
    get_instruction bb s.vs_inst_idx = SOME (mk_inst id MUL [Var ctr;Lit 32w] [mv]) /\
    get_instruction bb (SUC s.vs_inst_idx) = SOME (mk_inst (id+1) ADD [Var root;Var mv] [sv]) /\
    get_instruction bb (s.vs_inst_idx+2) = SOME (mk_inst (id+2) MLOAD [Var sv] [vv]) /\
    get_instruction bb (s.vs_inst_idx+3) = SOME (mk_inst (id+3) ADD [dst;Var ctr] [dv]) /\
    get_instruction bb (s.vs_inst_idx+4) = SOME (mk_inst (id+4) (if tr then TSTORE else SSTORE) [Var dv;Var vv] []) /\
    ptr_covers G tn root s total /\ lookup_var root s = SOME a /\
    eval_operand dst s = SOME k /\ op_taint tn dst = {} /\
    (!x. dst = Var x ==> ~MEM x [mv;sv;vv;dv]) /\
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
   get_instruction bb s1.vs_inst_idx = SOME (mk_inst (id+3) ADD [dst;Var ctr] [dv]) /\
   get_instruction bb (SUC s1.vs_inst_idx) = SOME (mk_inst ((id+3)+1) (if tr then TSTORE else SSTORE) [Var dv;Var vv] []) /\
   eval_operand dst s1 = SOME k /\ op_taint t1 dst = {} /\
   op_taint t1 (Var ctr) = {} /\ ~s1.vs_call_ctx.cc_static` by
    (gvs[ALL_DISTINCT, ADD1] >> Cases_on `dst` >>
     gvs[eval_operand_def, op_taint_def] >> metis_tac[]) >>
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

Theorem tuple_storage_address_body_counted:
  !s fn bb id root dst ctr mv sv vv dv nv a i n total k tr hdr tn G ctx D PG.
    ~s.vs_halted /\ lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
    get_instruction bb s.vs_inst_idx = SOME (mk_inst id MUL [Var ctr;Lit 32w] [mv]) /\
    get_instruction bb (SUC s.vs_inst_idx) = SOME (mk_inst (id+1) ADD [Var root;Var mv] [sv]) /\
    get_instruction bb (s.vs_inst_idx+2) = SOME (mk_inst (id+2) MLOAD [Var sv] [vv]) /\
    get_instruction bb (s.vs_inst_idx+3) = SOME (mk_inst (id+3) ADD [dst;Var ctr] [dv]) /\
    get_instruction bb (s.vs_inst_idx+4) = SOME (mk_inst (id+4) (if tr then TSTORE else SSTORE) [Var dv;Var vv] []) /\
    get_instruction bb (s.vs_inst_idx+5) = SOME (mk_inst (id+5) ADD [Var ctr;Lit 1w] [nv]) /\
    get_instruction bb (s.vs_inst_idx+6) = SOME (mk_inst (id+6) ASSIGN [Var nv] [ctr]) /\
    get_instruction bb (s.vs_inst_idx+7) = SOME (mk_inst (id+7) JMP [Label hdr] []) /\
    ptr_covers G tn root s total /\ lookup_var root s = SOME a /\
    eval_operand dst s = SOME k /\ op_taint tn dst = {} /\
    (!x. dst = Var x ==> ~MEM x [ctr;mv;sv;vv;dv;nv]) /\
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
  `ALL_DISTINCT [root;ctr;mv;sv;vv;dv] /\ ctr <> nv /\
   (!x. dst = Var x ==> ~MEM x [mv;sv;vv;dv])` by gvs[ALL_DISTINCT] >>
  drule_all tuple_storage_address_copy_prefix >>
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

Theorem tuple_storage_address_body_frame:
  !s fn bb id root dst ctr mv sv vv dv nv a i n capacity k tr hdr tn G ctx D PG s0 tn0.
    ~s.vs_halted /\ lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
    get_instruction bb s.vs_inst_idx = SOME (mk_inst id MUL [Var ctr;Lit 32w] [mv]) /\
    get_instruction bb (SUC s.vs_inst_idx) = SOME (mk_inst (id+1) ADD [Var root;Var mv] [sv]) /\
    get_instruction bb (s.vs_inst_idx+2) = SOME (mk_inst (id+2) MLOAD [Var sv] [vv]) /\
    get_instruction bb (s.vs_inst_idx+3) = SOME (mk_inst (id+3) ADD [dst;Var ctr] [dv]) /\
    get_instruction bb (s.vs_inst_idx+4) = SOME (mk_inst (id+4) (if tr then TSTORE else SSTORE) [Var dv;Var vv] []) /\
    get_instruction bb (s.vs_inst_idx+5) = SOME (mk_inst (id+5) ADD [Var ctr;Lit 1w] [nv]) /\
    get_instruction bb (s.vs_inst_idx+6) = SOME (mk_inst (id+6) ASSIGN [Var nv] [ctr]) /\
    get_instruction bb (s.vs_inst_idx+7) = SOME (mk_inst (id+7) JMP [Label hdr] []) /\
    ptr_covers G tn root s capacity /\ lookup_var root s = SOME a /\
    eval_operand dst s = SOME k /\ op_taint tn dst = {} /\
    (!x. dst = Var x ==> ~MEM x [ctr;mv;sv;vv;dv;nv]) /\
    lookup_var ctr s = SOME (n2w i) /\ FLOOKUP G ctr = NONE /\ op_taint tn (Var ctr) = {} /\
    ALL_DISTINCT [root;ctr;mv;sv;vv;dv;nv] /\
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
  drule_all tuple_storage_address_body_counted >>
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

Theorem tuple_storage_address_loop_remaining[local]:
  !remaining i s G tn.
    i+remaining = n /\ n < dimword (:256) /\ 32*n <= capacity /\
    w2n a+32*(n-1) < dimword (:256) /\ ~ctx_has_dalloca ctx /\
    ~s0.vs_call_ctx.cc_static /\
    lookup_block hdr fn.fn_blocks = SOME hb /\
    lookup_block bodylbl fn.fn_blocks = SOME bb /\
    get_instruction hb 0 = SOME (mk_inst hid EQ [Var ctr;Lit (n2w n)] [done]) /\
    get_instruction hb 1 = SOME (mk_inst (hid+1) JNZ [Var done;Label exit;Label bodylbl] []) /\
    get_instruction bb 0 = SOME (mk_inst bid MUL [Var ctr;Lit 32w] [mv]) /\
    get_instruction bb 1 = SOME (mk_inst (bid+1) ADD [Var root;Var mv] [sv]) /\
    get_instruction bb 2 = SOME (mk_inst (bid+2) MLOAD [Var sv] [vv]) /\
    get_instruction bb 3 = SOME (mk_inst (bid+3) ADD [dst;Var ctr] [dv]) /\
    get_instruction bb 4 = SOME (mk_inst (bid+4) (if tr then TSTORE else SSTORE) [Var dv;Var vv] []) /\
    get_instruction bb 5 = SOME (mk_inst (bid+5) ADD [Var ctr;Lit 1w] [nv]) /\
    get_instruction bb 6 = SOME (mk_inst (bid+6) ASSIGN [Var nv] [ctr]) /\
    get_instruction bb 7 = SOME (mk_inst (bid+7) JMP [Label hdr] []) /\
    ALL_DISTINCT [root;ctr;done;mv;sv;vv;dv;nv] /\
    eval_operand dst s = SOME k /\ op_taint tn dst = {} /\
    (!x. dst = Var x ==> ~MEM x [ctr;done;mv;sv;vv;dv;nv]) /\
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
  Induct_on `remaining` >> rpt gen_tac >> strip_tac >>
  `ctr <> done /\ root <> done /\ i<=n /\
   lookup_block s.vs_current_bb fn.fn_blocks = SOME hb /\
   get_instruction hb s.vs_inst_idx = SOME (mk_inst hid EQ [Var ctr;Lit (n2w n)] [done]) /\
   get_instruction hb (SUC s.vs_inst_idx) = SOME (mk_inst (hid+1) JNZ [Var done;Label exit;Label bodylbl] [])` by
    (gvs[ALL_DISTINCT] >> decide_tac) >>
  drule_all assign_base_storage_header_frame >>
  disch_then (qspecl_then [`D`, `PG`] mp_tac) >>
  disch_then (qx_choose_then `g1` (qx_choose_then `t1`
    (qx_choose_then `s1` strip_assume_tac)))
  >- (qexistsl_tac [`g1`, `t1`, `s1`] >> gvs[] >> metis_tac[]) >>
  `i<n /\ ~s1.vs_call_ctx.cc_static /\ ALL_DISTINCT [root;ctr;mv;sv;vv;dv;nv] /\
   (!x. dst = Var x ==> ~MEM x [ctr;mv;sv;vv;dv;nv])` by
    (gvs[assign_base_store_frame_def, ALL_DISTINCT] >> decide_tac) >>
  `eval_operand dst s1 = SOME k /\ op_taint t1 dst = {}` by
    (qpat_x_assum `!i s G tn. _` kall_tac >>
     Cases_on `dst` >> gvs[eval_operand_def, op_taint_def] >> metis_tac[]) >>
  `lookup_block s1.vs_current_bb fn.fn_blocks = SOME bb /\
   get_instruction bb s1.vs_inst_idx = SOME (mk_inst bid MUL [Var ctr;Lit 32w] [mv]) /\
   get_instruction bb (SUC s1.vs_inst_idx) = SOME (mk_inst (bid+1) ADD [Var root;Var mv] [sv]) /\
   get_instruction bb (s1.vs_inst_idx+2) = SOME (mk_inst (bid+2) MLOAD [Var sv] [vv]) /\
   get_instruction bb (s1.vs_inst_idx+3) = SOME (mk_inst (bid+3) ADD [dst;Var ctr] [dv]) /\
   get_instruction bb (s1.vs_inst_idx+4) = SOME (mk_inst (bid+4) (if tr then TSTORE else SSTORE) [Var dv;Var vv] []) /\
   get_instruction bb (s1.vs_inst_idx+5) = SOME (mk_inst (bid+5) ADD [Var ctr;Lit 1w] [nv]) /\
   get_instruction bb (s1.vs_inst_idx+6) = SOME (mk_inst (bid+6) ASSIGN [Var nv] [ctr]) /\
   get_instruction bb (s1.vs_inst_idx+7) = SOME (mk_inst (bid+7) JMP [Label hdr] [])` by simp[] >>
  drule_all tuple_storage_address_body_frame >>
  disch_then (qspecl_then [`D`, `PG`] mp_tac) >>
  disch_then (qx_choose_then `g2` (qx_choose_then `t2`
    (qx_choose_then `s2` strip_assume_tac))) >>
  `s2.vs_labels = s1.vs_labels` by
    (qpat_x_assum `execution_frame s2 = _` mp_tac >>
     qpat_x_assum `execution_frame s1 = _` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >>
     simp[execution_frame_def, place_store_prefix_fields] >> metis_tac[]) >>
  `eval_operand dst s2 = SOME k /\ op_taint t2 dst = {}` by
    (qpat_x_assum `!i s G tn. _` kall_tac >>
     Cases_on `dst` >> gvs[eval_operand_def, op_taint_def] >> metis_tac[]) >>
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

Theorem tuple_storage_address_compile_shape:
  !tr root dst n sa u sb.
    compile_word_copy_loop (Var root) dst n LocMemory
      (if tr then LocTransient else LocStorage) F sa = (u,sb) ==>
    ?hdr bodylbl exit ctr done mv sv vv dv nv.
      sb.cs_current_bb = exit /\ sb.cs_current_insts = [] /\
      sb.cs_blocks =
        <| bb_label := bodylbl; bb_instructions :=
          [mk_inst (sa.cs_next_id+4) MUL [Var ctr;Lit 32w] [mv];
           mk_inst (sa.cs_next_id+5) ADD [Var root;Var mv] [sv];
           mk_inst (sa.cs_next_id+6) MLOAD [Var sv] [vv];
           mk_inst (sa.cs_next_id+7) ADD [dst;Var ctr] [dv];
           mk_inst (sa.cs_next_id+8) (if tr then TSTORE else SSTORE) [Var dv;Var vv] [];
           mk_inst (sa.cs_next_id+9) ADD [Var ctr;Lit 1w] [nv];
           mk_inst (sa.cs_next_id+10) ASSIGN [Var nv] [ctr];
           mk_inst (sa.cs_next_id+11) JMP [Label hdr] []] |> ::
        <| bb_label := hdr; bb_instructions :=
          [mk_inst (sa.cs_next_id+2) EQ [Var ctr;Lit (n2w n)] [done];
           mk_inst (sa.cs_next_id+3) JNZ [Var done;Label exit;Label bodylbl] []] |> ::
        <| bb_label := sa.cs_current_bb; bb_instructions := sa.cs_current_insts ++
          [mk_inst sa.cs_next_id ASSIGN [Lit 0w] [ctr];
           mk_inst (sa.cs_next_id+1) JMP [Label hdr] []] |> :: sa.cs_blocks /\
      ALL_DISTINCT [ctr;done;mv;sv;vv;dv;nv] /\
      (!x. not_fresh_at sa x ==> ~MEM x [ctr;done;mv;sv;vv;dv;nv])
Proof
  rpt gen_tac >> Cases_on `tr` >>
  simp[compile_word_copy_loop_def, compile_word_copy_loop_op_def,
    compile_word_copy_loop_base_def, word_scale_def, compile_ptr_load_def,
    compile_ptr_store_def, emit_op_def, emit_void_def, emit_inst_def,
    comp_ignore_bind_def, comp_bind_def, comp_return_def, fresh_label_def,
    fresh_var_def, fresh_id_def, emit_def, new_block_def] >> strip_tac >> gvs[] >>
  rpt (goal_assum (drule_at Any)) >>
  simp[mk_inst_def, ALL_DISTINCT, fresh_var_distinct] >>
  rw[not_fresh_at_def] >> first_x_assum irule >> simp[]
QED

Theorem tuple_storage_address_compile_code:
  !tr root dst n sa u sb fn.
    compile_word_copy_loop (Var root) dst n LocMemory
      (if tr then LocTransient else LocStorage) F sa = (u,sb) /\
    fn_has_code sa sb fn ==>
    ?hdr bodylbl ctr done mv sv vv dv nv ib hb bb.
      sb.cs_current_insts = [] /\
      lookup_block sa.cs_current_bb fn.fn_blocks = SOME ib /\
      ib.bb_instructions = sa.cs_current_insts ++
        [mk_inst sa.cs_next_id ASSIGN [Lit 0w] [ctr];
         mk_inst (sa.cs_next_id+1) JMP [Label hdr] []] /\
      lookup_block hdr fn.fn_blocks = SOME hb /\
      hb.bb_instructions =
        [mk_inst (sa.cs_next_id+2) EQ [Var ctr;Lit (n2w n)] [done];
         mk_inst (sa.cs_next_id+3) JNZ [Var done;Label sb.cs_current_bb;Label bodylbl] []] /\
      lookup_block bodylbl fn.fn_blocks = SOME bb /\
      bb.bb_instructions =
        [mk_inst (sa.cs_next_id+4) MUL [Var ctr;Lit 32w] [mv];
         mk_inst (sa.cs_next_id+5) ADD [Var root;Var mv] [sv];
         mk_inst (sa.cs_next_id+6) MLOAD [Var sv] [vv];
         mk_inst (sa.cs_next_id+7) ADD [dst;Var ctr] [dv];
         mk_inst (sa.cs_next_id+8) (if tr then TSTORE else SSTORE) [Var dv;Var vv] [];
         mk_inst (sa.cs_next_id+9) ADD [Var ctr;Lit 1w] [nv];
         mk_inst (sa.cs_next_id+10) ASSIGN [Var nv] [ctr];
         mk_inst (sa.cs_next_id+11) JMP [Label hdr] []] /\
      ALL_DISTINCT [ctr;done;mv;sv;vv;dv;nv] /\
      (!x. not_fresh_at sa x ==> ~MEM x [ctr;done;mv;sv;vv;dv;nv])
Proof
  rpt gen_tac >> strip_tac >> drule tuple_storage_address_compile_shape >> strip_tac >>
  gvs[fn_has_code_def, emitted_blocks_def, DISJ_IMP_THM, FORALL_AND_THM] >>
  qexistsl_tac [`hdr`, `bodylbl`, `ctr`, `done`, `mv`, `sv`, `vv`, `dv`, `nv`] >> simp[]
QED

Theorem tuple_storage_address_compiled_counted:
  !tr root dst k n sa z sb fn s G tn ctx D PG a capacity.
    compile_word_copy_loop (Var root) dst n LocMemory
      (if tr then LocTransient else LocStorage) F sa = (z,sb) /\
    fn_has_code sa sb fn /\ not_fresh_at sa root /\
    eval_operand dst s = SOME k /\ op_taint tn dst = {} /\
    (!x. dst = Var x ==> not_fresh_at sa x) /\
    ptr_covers G tn root s capacity /\ lookup_var root s = SOME a /\
    ~s.vs_halted /\ ~s.vs_call_ctx.cc_static /\ ~ctx_has_dalloca ctx /\
    s.vs_current_bb = sa.cs_current_bb /\ s.vs_inst_idx = LENGTH sa.cs_current_insts /\
    n < dimword (:256) /\ 32*n <= capacity /\
    w2n a+32*(n-1) < dimword (:256) ==>
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
  rpt gen_tac >> strip_tac >> drule_all tuple_storage_address_compile_code >> strip_tac >>
  `root <> ctr /\ ALL_DISTINCT [root;ctr;done;mv;sv;vv;dv;nv] /\
   (!x. dst = Var x ==> ~MEM x [ctr;done;mv;sv;vv;dv;nv])` by
    (gvs[ALL_DISTINCT] >> metis_tac[]) >>
  `get_instruction ib s.vs_inst_idx = SOME (mk_inst sa.cs_next_id ASSIGN [Lit 0w] [ctr]) /\
   get_instruction ib (SUC s.vs_inst_idx) = SOME (mk_inst (sa.cs_next_id+1) JMP [Label hdr] [])` by
    simp[get_instruction_def, EL_APPEND_EQN, ADD1] >>
  `lookup_block s.vs_current_bb fn.fn_blocks = SOME ib` by simp[] >>
  drule_all assign_base_storage_init_frame >>
  disch_then (qspecl_then [`D`, `PG`, `if tr then LocTransient else LocStorage`, `k`] mp_tac) >>
  disch_then (qx_choose_then `g1` (qx_choose_then `t1` (qx_choose_then `s1` strip_assume_tac))) >>
  `s1.vs_labels = s.vs_labels` by
    (qpat_x_assum `execution_frame s1 = _` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >> simp[execution_frame_def]) >>
  `eval_operand dst s1 = SOME k /\ op_taint t1 dst = {}` by
    (Cases_on `dst` >> gvs[eval_operand_def, op_taint_def] >> metis_tac[]) >>
  `?gf tf u.
    gas_path_ptr D 0 ctx fn PG g1 t1 s1 0 gf tf (OK u) /\
    execution_frame u = execution_frame (store_copy_prefix (if tr then LocTransient else LocStorage) a k s n) /\
    assign_base_store_frame (if tr then LocTransient else LocStorage) a k s tn n u tf /\
    ptr_covers gf tf root u capacity /\ lookup_var root u = SOME a /\
    lookup_var ctr u = SOME (n2w n) /\ FLOOKUP gf ctr = NONE /\ op_taint tf (Var ctr) = {} /\
    u.vs_current_bb = sb.cs_current_bb /\ u.vs_inst_idx = 0 /\ ~u.vs_halted /\
    (!x. ~MEM x [ctr;done;mv;sv;vv;dv;nv] ==> lookup_var x u = lookup_var x s1 /\
      FLOOKUP gf x = FLOOKUP g1 x /\ op_taint tf (Var x) = op_taint t1 (Var x))` by
    (irule (Q.SPECL [`n`, `0`] tuple_storage_address_loop_remaining) >>
     simp[get_instruction_def, mk_inst_def] >>
     rpt (goal_assum (drule_at Any)) >>
     gvs[assign_base_store_prefix_zero, execution_frame_def]) >>
  qexistsl_tac [`gf`, `tf`, `u`] >> conj_tac >-
    (qpat_x_assum `gas_path_ptr _ _ _ _ _ G tn s _ _ _ _`
      (mp_then Any mp_tac gas_path_ptr_then) >> disch_then drule >> simp[]) >>
  asm_rewrite_tac[] >> simp[] >> metis_tac[MEM]
QED

Theorem tuple_storage_address_single_shape:
  !tr root dst sa z sb fn.
    (do loaded <- emit_op MLOAD [Var root];
        emit_void (if tr then TSTORE else SSTORE) [dst;loaded]
     od) sa = (z,sb) /\ fn_has_code sa sb fn ==>
    ?tmp bb.
      sb.cs_current_bb = sa.cs_current_bb /\
      sb.cs_current_insts = sa.cs_current_insts ++
        [mk_inst sa.cs_next_id MLOAD [Var root] [tmp];
         mk_inst (sa.cs_next_id+1) (if tr then TSTORE else SSTORE) [dst;Var tmp] []] /\
      lookup_block sa.cs_current_bb fn.fn_blocks = SOME bb /\
      (!j. j < LENGTH sb.cs_current_insts ==>
        get_instruction bb j = SOME (EL j sb.cs_current_insts)) /\
      (!x. not_fresh_at sa x ==> x <> tmp)
Proof
  rpt gen_tac >>
  simp[emit_op_def, emit_void_def, emit_inst_def, comp_ignore_bind_def,
    comp_bind_def, comp_return_def, fresh_var_def, fresh_id_def, emit_def] >>
  strip_tac >> gvs[] >> gvs[fn_has_code_def] >>
  qexists_tac `STRING #"%" (toString sa.cs_next_var)` >>
  simp[not_fresh_at_def] >>
  gvs[IS_PREFIX_APPEND, get_instruction_def] >>
  pure_rewrite_tac[GSYM APPEND_ASSOC] >>
  simp[EL_APPEND_EQN] >> rpt strip_tac >>
  Cases_on `j < LENGTH sa.cs_current_insts` >- simp[] >>
  `j = LENGTH sa.cs_current_insts \/ j = LENGTH sa.cs_current_insts + 1` by decide_tac >> gvs[]
QED

Theorem tuple_storage_address_single_counted:
  !s fn bb id tr root dst tmp a k tn G ctx D PG.
    ~s.vs_halted /\ lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
    get_instruction bb s.vs_inst_idx = SOME (mk_inst id MLOAD [Var root] [tmp]) /\
    get_instruction bb (SUC s.vs_inst_idx) =
      SOME (mk_inst (id+1) (if tr then TSTORE else SSTORE) [dst;Var tmp] []) /\
    ptr_covers G tn root s 32 /\ lookup_var root s = SOME a /\ root <> tmp /\
    eval_operand dst s = SOME k /\ op_taint tn dst = {} /\
    (!x. dst = Var x ==> x <> tmp) /\
    ~ctx_has_dalloca ctx /\ ~s.vs_call_ctx.cc_static ==>
    ?Gf tf u.
      gas_path_ptr D 0 ctx fn PG G tn s 0 Gf tf (OK u) /\
      execution_frame u = execution_frame
        (store_copy_prefix (if tr then LocTransient else LocStorage) a k s 1) /\
      assign_base_store_frame (if tr then LocTransient else LocStorage) a k s tn 1 u tf /\
      ptr_covers Gf tf root u 32 /\ lookup_var root u = SOME a /\
      u.vs_current_bb = s.vs_current_bb /\ u.vs_inst_idx = s.vs_inst_idx+2 /\ ~u.vs_halted /\
      (!x. x <> tmp ==> lookup_var x u = lookup_var x s /\
        FLOOKUP Gf x = FLOOKUP G x /\ op_taint tf (Var x) = op_taint tn (Var x))
Proof
  rpt gen_tac >> strip_tac >> drule_all assign_base_storage_load_counted >>
  disch_then (qspecl_then [`D`, `PG`] mp_tac) >>
  disch_then (qx_choose_then `g1` (qx_choose_then `t1` (qx_choose_then `s1` strip_assume_tac))) >>
  `s1.vs_labels = s.vs_labels` by
    (qpat_x_assum `execution_frame s1 = _` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >> simp[execution_frame_def]) >>
  `eval_operand dst s1 = SOME k /\ op_taint t1 dst = {}` by
    (Cases_on `dst` >> gvs[eval_operand_def, op_taint_def]) >>
  `~s1.vs_halted /\ lookup_block s1.vs_current_bb fn.fn_blocks = SOME bb /\
   get_instruction bb s1.vs_inst_idx =
     SOME (mk_inst (id+1) (if tr then TSTORE else SSTORE) [dst;Var tmp] []) /\
   eval_operand (Var tmp) s1 = SOME (mload (w2n a) s) /\
   ~s1.vs_call_ctx.cc_static` by simp[eval_operand_def] >>
  drule_all assign_base_storage_write_counted >>
  disch_then (qspecl_then [`g1`, `D`, `PG`] mp_tac) >> strip_tac >>
  qexistsl_tac [`g1`,
    `if tr then t1 with t_trans := key_update t1.t_trans k (op_taint t1 (Var tmp))
     else t1 with t_stor := key_update t1.t_stor k (op_taint t1 (Var tmp))`,
    `(if tr then tstore k (mload (w2n a) s) s1 else sstore k (mload (w2n a) s) s1)
      with vs_inst_idx := SUC s1.vs_inst_idx`] >>
  conj_tac >-
    (qpat_x_assum `gas_path_ptr _ _ _ _ _ G tn s _ _ _ _`
      (mp_then Any mp_tac gas_path_ptr_then) >> disch_then drule >> simp[]) >>
  Cases_on `tr` >> pure_rewrite_tac[ONE] >>
  pure_rewrite_tac[assign_base_store_prefix_suc, assign_base_store_prefix_zero,
    assign_base_store_frame_def, assign_base_store_taint_prefix_def] >>
  gvs[assign_base_store_frame_def, assign_base_store_taint_prefix_def,
    execution_frame_def, sstore_def, tstore_def, lookup_var_def,
    ptr_covers_def, op_taint_def, ADD1, WORD_ADD_0, WORD_MULT_CLAUSES]
QED

Theorem tuple_storage_address_single_compiled_counted:
  !tr root dst k sa z sb fn s G tn ctx D PG a.
    (do loaded <- emit_op MLOAD [Var root];
        emit_void (if tr then TSTORE else SSTORE) [dst;loaded]
     od) sa = (z,sb) /\ fn_has_code sa sb fn /\ not_fresh_at sa root /\
    eval_operand dst s = SOME k /\ op_taint tn dst = {} /\
    (!x. dst = Var x ==> not_fresh_at sa x) /\
    ptr_covers G tn root s 32 /\ lookup_var root s = SOME a /\
    ~s.vs_halted /\ ~s.vs_call_ctx.cc_static /\ ~ctx_has_dalloca ctx /\
    s.vs_current_bb = sa.cs_current_bb /\ s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
    ?Gf tf u.
      gas_path_ptr D 0 ctx fn PG G tn s 0 Gf tf (OK u) /\
      execution_frame u = execution_frame
        (store_copy_prefix (if tr then LocTransient else LocStorage) a k s 1) /\
      assign_base_store_frame (if tr then LocTransient else LocStorage) a k s tn 1 u tf /\
      ptr_covers Gf tf root u 32 /\ lookup_var root u = SOME a /\
      u.vs_current_bb = sb.cs_current_bb /\
      u.vs_inst_idx = LENGTH sb.cs_current_insts /\ ~u.vs_halted /\
      (!x. not_fresh_at sa x ==> lookup_var x u = lookup_var x s /\
        FLOOKUP Gf x = FLOOKUP G x /\ op_taint tf (Var x) = op_taint tn (Var x))
Proof
  rpt gen_tac >> strip_tac >> drule_all tuple_storage_address_single_shape >> strip_tac >>
  `root <> tmp /\ (!x. dst = Var x ==> x <> tmp) /\
   lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
   get_instruction bb s.vs_inst_idx = SOME (mk_inst sa.cs_next_id MLOAD [Var root] [tmp]) /\
   get_instruction bb (SUC s.vs_inst_idx) =
     SOME (mk_inst (sa.cs_next_id+1) (if tr then TSTORE else SSTORE) [dst;Var tmp] [])` by
    (simp[EL_APPEND_EQN] >> metis_tac[ADD1]) >>
  drule_all tuple_storage_address_single_counted >>
  disch_then (qspecl_then [`D`, `PG`] mp_tac) >>
  disch_then (qx_choose_then `gf` (qx_choose_then `tf` (qx_choose_then `u` strip_assume_tac))) >>
  qexistsl_tac [`gf`, `tf`, `u`] >> asm_rewrite_tac[] >> simp[] >> metis_tac[]
QED

Theorem tuple_storage_address_direct_code:
  ~is_bytestring_type ty ==>
  compile_assign_value cenv dst (if tr then LocTransient else LocStorage)
    (Var root) F loc ty ty NONE capacity =
  (if capacity <= 32 then
     do loaded <- emit_op MLOAD [Var root];
        emit_void (if tr then TSTORE else SSTORE) [dst;loaded]
     od
   else do compile_word_copy_loop (Var root) dst (capacity DIV 32) LocMemory
          (if tr then LocTransient else LocStorage) F; return () od)
Proof
  strip_tac >> Cases_on `tr` >>
  simp[FUN_EQ_THM, compile_assign_value_def, comp_bind_def,
    comp_return_def, comp_ignore_bind_def, compile_memory_to_storage_def,
    compile_memory_to_transient_def] >>
  gen_tac >> pairarg_tac >> simp[]
QED

Theorem tuple_storage_address_direct_counted:
  !tr root dst k n cenv ty loc sa z sb fn s G tn ctx D PG a.
    compile_assign_value cenv dst (if tr then LocTransient else LocStorage)
      (Var root) F loc ty ty NONE (32*n) sa = (z,sb) /\
    ~is_bytestring_type ty /\ fn_has_code sa sb fn /\ not_fresh_at sa root /\
    eval_operand dst s = SOME k /\ op_taint tn dst = {} /\
    (!x. dst = Var x ==> not_fresh_at sa x) /\
    ptr_covers G tn root s (32*n) /\ lookup_var root s = SOME a /\
    ~s.vs_halted /\ ~s.vs_call_ctx.cc_static /\ ~ctx_has_dalloca ctx /\
    s.vs_current_bb = sa.cs_current_bb /\ s.vs_inst_idx = LENGTH sa.cs_current_insts /\
    0<n /\ n < dimword (:256) /\ w2n a+32*(n-1) < dimword (:256) ==>
    ?Gf tf u.
      gas_path_ptr D 0 ctx fn PG G tn s 0 Gf tf (OK u) /\
      execution_frame u = execution_frame
        (store_copy_prefix (if tr then LocTransient else LocStorage) a k s n) /\
      assign_base_store_frame (if tr then LocTransient else LocStorage) a k s tn n u tf /\
      ptr_covers Gf tf root u (32*n) /\ lookup_var root u = SOME a /\
      u.vs_current_bb = sb.cs_current_bb /\
      u.vs_inst_idx = LENGTH sb.cs_current_insts /\ ~u.vs_halted /\
      (!x. not_fresh_at sa x ==> lookup_var x u = lookup_var x s /\
        FLOOKUP Gf x = FLOOKUP G x /\ op_taint tf (Var x) = op_taint tn (Var x))
Proof
  rpt gen_tac >> strip_tac >>
  drule tuple_storage_address_direct_code >> strip_tac >>
  Cases_on `32*n <= 32`
  >- (`n=1` by decide_tac >> gvs[] >>
      drule_all tuple_storage_address_single_compiled_counted >>
      disch_then (qspecl_then [`D`, `PG`] mp_tac) >> simp[]) >>
  qpat_x_assum `compile_assign_value _ _ _ _ _ _ _ _ _ _ _ = _` mp_tac >>
  asm_rewrite_tac[] >> simp[comp_ignore_bind_def, comp_bind_def, comp_return_def] >>
  pairarg_tac >> strip_tac >> gvs[] >>
  `n < dimword (:256) /\ 32*n <= 32*n` by decide_tac >>
  drule_all tuple_storage_address_compiled_counted >>
  disch_then (qspecl_then [`D`, `PG`] mp_tac) >>
  disch_then (qx_choose_then `gf` (qx_choose_then `tf` (qx_choose_then `u` strip_assume_tac))) >>
  qexistsl_tac [`gf`, `tf`, `u`] >> asm_rewrite_tac[] >>
  gvs[execution_frame_def]
QED
