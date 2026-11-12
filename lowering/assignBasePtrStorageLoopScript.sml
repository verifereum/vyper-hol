(* Shared prefix interface for counted memory-to-storage copies. *)
Theory assignBasePtrStorageLoop
Ancestors assignBasePtrStoragePath stmtSimStoreCopy bodyPtrDefs fragGasPathPtr
  ptrDiscipline venomState stateFrame words arithmetic list rich_list finite_map pred_set

(* The existing store_copy_prefix has no ghost component. This recursion
   adds only its missing byte-taint model, leaving scratch variables out. *)
Definition assign_base_store_taint_prefix_def:
  (assign_base_store_taint_prefix loc (b:bytes32) k tn 0 = tn) /\
  (assign_base_store_taint_prefix loc b k tn (SUC i) =
    if loc = LocStorage then
      (assign_base_store_taint_prefix loc b k tn i) with t_stor :=
        key_update (assign_base_store_taint_prefix loc b k tn i).t_stor
          (k+n2w i) (mem_word_taint tn.t_mem (w2n (b+n2w i*32w)))
    else
      (assign_base_store_taint_prefix loc b k tn i) with t_trans :=
        key_update (assign_base_store_taint_prefix loc b k tn i).t_trans
          (k+n2w i) (mem_word_taint tn.t_mem (w2n (b+n2w i*32w))))
End

(* A fieldwise execution/model relation avoids the false full-state equality:
   emitted instructions change the PC, counter and temporary variable taint. *)
Definition assign_base_store_frame_def:
  assign_base_store_frame loc b k s0 tn0 i s tn <=>
    s.vs_accounts = (store_copy_prefix loc b k s0 i).vs_accounts /\
    s.vs_transient = (store_copy_prefix loc b k s0 i).vs_transient /\
    s.vs_memory = s0.vs_memory /\ s.vs_call_ctx = s0.vs_call_ctx /\
    tn.t_stor = (assign_base_store_taint_prefix loc b k tn0 i).t_stor /\
    tn.t_trans = (assign_base_store_taint_prefix loc b k tn0 i).t_trans /\
    tn.t_mem = tn0.t_mem /\ tn.t_imm = tn0.t_imm
End

(* stmtSimStoreCopy's interfaces are local: export the needed equations
   without introducing a second semantic model. *)
Theorem assign_base_store_prefix_zero:
  store_copy_prefix loc b k s0 0 = s0
Proof
  simp[store_copy_prefix_def, COUNT_LIST_def]
QED

Theorem assign_base_store_prefix_suc:
  store_copy_prefix loc b k s0 (SUC i) =
    (if loc = LocStorage then sstore else tstore)
      (k+n2w i) (mload (w2n (b+n2w i*32w)) s0)
      (store_copy_prefix loc b k s0 i)
Proof
  simp[store_copy_prefix_def, COUNT_LIST_SNOC, FOLDL_SNOC]
QED

Theorem assign_base_store_prefix_frame:
  !i. (store_copy_prefix loc b k s0 i).vs_memory = s0.vs_memory /\
      (store_copy_prefix loc b k s0 i).vs_call_ctx = s0.vs_call_ctx
Proof
  Induct >> simp[assign_base_store_prefix_zero, assign_base_store_prefix_suc] >>
  Cases_on `loc = LocStorage` >> gvs[sstore_def, tstore_def]
QED

Theorem assign_base_store_taint_frame:
  !i. (assign_base_store_taint_prefix loc b k tn0 i).t_mem = tn0.t_mem /\
      (assign_base_store_taint_prefix loc b k tn0 i).t_imm = tn0.t_imm /\
      (loc = LocStorage ==> (assign_base_store_taint_prefix loc b k tn0 i).t_trans = tn0.t_trans) /\
      (loc <> LocStorage ==> (assign_base_store_taint_prefix loc b k tn0 i).t_stor = tn0.t_stor)
Proof
  Induct >> simp[assign_base_store_taint_prefix_def] >>
  Cases_on `loc = LocStorage` >> gvs[assign_base_store_taint_prefix_def]
QED

Theorem assign_base_store_frame_zero:
  assign_base_store_frame loc b k s0 tn0 0 s0 tn0
Proof
  simp[assign_base_store_frame_def, assign_base_store_prefix_zero,
    assign_base_store_taint_prefix_def]
QED

Theorem assign_base_store_frame_preserve:
  assign_base_store_frame loc b k s0 tn0 i s tn /\
  u.vs_accounts = s.vs_accounts /\ u.vs_transient = s.vs_transient /\
  u.vs_memory = s.vs_memory /\ u.vs_call_ctx = s.vs_call_ctx /\
  tf.t_stor = tn.t_stor /\ tf.t_trans = tn.t_trans /\
  tf.t_mem = tn.t_mem /\ tf.t_imm = tn.t_imm ==>
  assign_base_store_frame loc b k s0 tn0 i u tf
Proof
  simp[assign_base_store_frame_def]
QED

Theorem assign_base_store_frame_advance:
  assign_base_store_frame (if tr then LocTransient else LocStorage) b k s0 tn0 i s tn /\
  u.vs_accounts = (if tr then s.vs_accounts else
    (sstore (k+n2w i) (mload (w2n (b+n2w (32*i))) s) s).vs_accounts) /\
  u.vs_transient = (if tr then
    (tstore (k+n2w i) (mload (w2n (b+n2w (32*i))) s) s).vs_transient else s.vs_transient) /\
  u.vs_memory = s.vs_memory /\ u.vs_call_ctx = s.vs_call_ctx /\
  tf.t_stor = (if tr then tn.t_stor else key_update tn.t_stor (k+n2w i)
    (mem_word_taint tn.t_mem (w2n (b+n2w (32*i))))) /\
  tf.t_trans = (if tr then key_update tn.t_trans (k+n2w i)
    (mem_word_taint tn.t_mem (w2n (b+n2w (32*i)))) else tn.t_trans) /\
  tf.t_mem = tn.t_mem /\ tf.t_imm = tn.t_imm ==>
  assign_base_store_frame (if tr then LocTransient else LocStorage) b k s0 tn0 (SUC i) u tf
Proof
  `n2w (32*i) = (n2w i:bytes32)*32w` by
    (once_rewrite_tac[MULT_COMM] >> simp[word_mul_n2w]) >>
  Cases_on `tr` >> simp[assign_base_store_frame_def] >> strip_tac >>
  simp[assign_base_store_prefix_suc, assign_base_store_taint_prefix_def,
    sstore_def, tstore_def, assign_base_store_prefix_frame] >>
  gvs[mload_def, sstore_def, tstore_def]
QED

Theorem assign_base_store_root_transport:
  ptr_covers G tn root s capacity /\ lookup_var root s = SOME a /\
  lookup_var root u = lookup_var root s /\ FLOOKUP Gf root = FLOOKUP G root /\
  op_taint tf (Var root) = op_taint tn (Var root) ==>
  ptr_covers Gf tf root u capacity /\ lookup_var root u = SOME a
Proof
  strip_tac >> gvs[ptr_covers_def] >> metis_tac[]
QED

(* Exercise the fieldwise interface against the actual counted body; the
   loop induction need not unfold either prefix model or store semantics. *)
Theorem assign_base_storage_body_frame:
  !s fn bb id root ctr mv sv vv dv nv a i n capacity k tr hdr tn G ctx D PG s0 tn0.
    ~s.vs_halted /\ lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
    get_instruction bb s.vs_inst_idx = SOME (mk_inst id MUL [Var ctr;Lit 32w] [mv]) /\
    get_instruction bb (SUC s.vs_inst_idx) = SOME (mk_inst (id+1) ADD [Var root;Var mv] [sv]) /\
    get_instruction bb (s.vs_inst_idx+2) = SOME (mk_inst (id+2) MLOAD [Var sv] [vv]) /\
    get_instruction bb (s.vs_inst_idx+3) = SOME (mk_inst (id+3) ADD [Lit k;Var ctr] [dv]) /\
    get_instruction bb (s.vs_inst_idx+4) = SOME (mk_inst (id+4) (if tr then TSTORE else SSTORE) [Var dv;Var vv] []) /\
    get_instruction bb (s.vs_inst_idx+5) = SOME (mk_inst (id+5) ADD [Var ctr;Lit 1w] [nv]) /\
    get_instruction bb (s.vs_inst_idx+6) = SOME (mk_inst (id+6) ASSIGN [Var nv] [ctr]) /\
    get_instruction bb (s.vs_inst_idx+7) = SOME (mk_inst (id+7) JMP [Label hdr] []) /\
    ptr_covers G tn root s capacity /\ lookup_var root s = SOME a /\
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
  drule_all assign_base_storage_body_counted >>
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

Theorem assign_base_storage_header_frame:
  !s fn bb id ctr done i n bodylbl exit tn G ctx D PG loc a k s0 tn0 root capacity.
    ~s.vs_halted /\ lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
    get_instruction bb s.vs_inst_idx = SOME (mk_inst id EQ [Var ctr;Lit (n2w n)] [done]) /\
    get_instruction bb (SUC s.vs_inst_idx) =
      SOME (mk_inst (id+1) JNZ [Var done;Label exit;Label bodylbl] []) /\
    lookup_var ctr s = SOME (n2w i) /\ FLOOKUP G ctr = NONE /\
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
  drule_all assign_base_storage_copy_header >>
  disch_then (qspecl_then [`G`, `D`, `PG`] mp_tac) >>
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

Theorem assign_base_storage_loop_remaining[local]:
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
    get_instruction bb 3 = SOME (mk_inst (bid+3) ADD [Lit k;Var ctr] [dv]) /\
    get_instruction bb 4 = SOME (mk_inst (bid+4) (if tr then TSTORE else SSTORE) [Var dv;Var vv] []) /\
    get_instruction bb 5 = SOME (mk_inst (bid+5) ADD [Var ctr;Lit 1w] [nv]) /\
    get_instruction bb 6 = SOME (mk_inst (bid+6) ASSIGN [Var nv] [ctr]) /\
    get_instruction bb 7 = SOME (mk_inst (bid+7) JMP [Label hdr] []) /\
    ALL_DISTINCT [root;ctr;done;mv;sv;vv;dv;nv] /\
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
  `i<n /\ ~s1.vs_call_ctx.cc_static /\ ALL_DISTINCT [root;ctr;mv;sv;vv;dv;nv]` by
    (gvs[assign_base_store_frame_def, ALL_DISTINCT] >> decide_tac) >>
  `lookup_block s1.vs_current_bb fn.fn_blocks = SOME bb /\
   get_instruction bb s1.vs_inst_idx = SOME (mk_inst bid MUL [Var ctr;Lit 32w] [mv]) /\
   get_instruction bb (SUC s1.vs_inst_idx) = SOME (mk_inst (bid+1) ADD [Var root;Var mv] [sv]) /\
   get_instruction bb (s1.vs_inst_idx+2) = SOME (mk_inst (bid+2) MLOAD [Var sv] [vv]) /\
   get_instruction bb (s1.vs_inst_idx+3) = SOME (mk_inst (bid+3) ADD [Lit k;Var ctr] [dv]) /\
   get_instruction bb (s1.vs_inst_idx+4) = SOME (mk_inst (bid+4) (if tr then TSTORE else SSTORE) [Var dv;Var vv] []) /\
   get_instruction bb (s1.vs_inst_idx+5) = SOME (mk_inst (bid+5) ADD [Var ctr;Lit 1w] [nv]) /\
   get_instruction bb (s1.vs_inst_idx+6) = SOME (mk_inst (bid+6) ASSIGN [Var nv] [ctr]) /\
   get_instruction bb (s1.vs_inst_idx+7) = SOME (mk_inst (bid+7) JMP [Label hdr] [])` by simp[] >>
  drule_all assign_base_storage_body_frame >>
  disch_then (qspecl_then [`D`, `PG`] mp_tac) >>
  disch_then (qx_choose_then `g2` (qx_choose_then `t2`
    (qx_choose_then `s2` strip_assume_tac))) >>
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

Theorem assign_base_storage_loop_counted:
  !i s G tn.
    i <= n /\ n < dimword (:256) /\ 32*n <= capacity /\
    w2n a+32*(n-1) < dimword (:256) /\ ~ctx_has_dalloca ctx /\
    ~s0.vs_call_ctx.cc_static /\
    lookup_block hdr fn.fn_blocks = SOME hb /\
    lookup_block bodylbl fn.fn_blocks = SOME bb /\
    get_instruction hb 0 = SOME (mk_inst hid EQ [Var ctr;Lit (n2w n)] [done]) /\
    get_instruction hb 1 = SOME (mk_inst (hid+1) JNZ [Var done;Label exit;Label bodylbl] []) /\
    get_instruction bb 0 = SOME (mk_inst bid MUL [Var ctr;Lit 32w] [mv]) /\
    get_instruction bb 1 = SOME (mk_inst (bid+1) ADD [Var root;Var mv] [sv]) /\
    get_instruction bb 2 = SOME (mk_inst (bid+2) MLOAD [Var sv] [vv]) /\
    get_instruction bb 3 = SOME (mk_inst (bid+3) ADD [Lit k;Var ctr] [dv]) /\
    get_instruction bb 4 = SOME (mk_inst (bid+4) (if tr then TSTORE else SSTORE) [Var dv;Var vv] []) /\
    get_instruction bb 5 = SOME (mk_inst (bid+5) ADD [Var ctr;Lit 1w] [nv]) /\
    get_instruction bb 6 = SOME (mk_inst (bid+6) ASSIGN [Var nv] [ctr]) /\
    get_instruction bb 7 = SOME (mk_inst (bid+7) JMP [Label hdr] []) /\
    ALL_DISTINCT [root;ctr;done;mv;sv;vv;dv;nv] /\
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
  rpt gen_tac >> strip_tac >>
  `i+(n-i)=n` by decide_tac >>
  drule_all assign_base_storage_loop_remaining >>
  disch_then (qspecl_then [`PG`, `D`] mp_tac) >> simp[]
QED
