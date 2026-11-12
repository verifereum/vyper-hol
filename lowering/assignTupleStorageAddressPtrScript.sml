(* Counted memory-to-storage copies with an evaluated destination operand. *)
Theory assignTupleStorageAddressPtr
Ancestors assignBasePtrStoragePath assignBasePtrStorageLoop assignBasePtrStorageLayout assignTuplePtrStorage context compileEnv
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
