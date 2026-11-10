(* Normalized counted control for the outer dynamic storage traversal. *)
Theory placeStorageTraversalCounted
Ancestors
  placeStorageControlCounted typedArrayControlCounted typedArrayLoopControlMem typedCopyLoopCounted
  fragGasPathMem fragGasMode placeStorageLayoutCounted placeStorageElementPaths stmtSimStoreCopy venomState venomInst emitHelperProps words list rich_list

Theorem storage_traversal_header:
  ~s.vs_halted /\ s.vs_inst_idx = 0 /\
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  bb.bb_instructions =
    [mk_inst id LT [Var ctr; Var len] [cmp];
     mk_inst (id+1) ISZERO [Var cmp] [done];
     mk_inst (id+2) JNZ [Var done; Label exit; Label body_lbl] []] /\
  lookup_var ctr s = SOME (n2w i) /\ lookup_var len s = SOME (n2w n) /\
  i <= n /\ n < dimword(:256) ==>
  ?q. gas_path_mem ctx fn s 0 (OK q) /\
      store_copy_normalize sbase q = store_copy_normalize sbase s /\
      (!x. x <> cmp /\ x <> done ==> lookup_var x q = lookup_var x s) /\
      ~q.vs_halted /\ q.vs_current_bb = (if i < n then body_lbl else exit) /\
      q.vs_inst_idx = 0
Proof
  strip_tac >>
  `eval_operand (Var ctr) s = SOME (n2w i) /\
   eval_operand (Var len) s = SOME (n2w n)` by simp[eval_operand_def] >>
  drule_all typed_memory_array_condition_path_mem >> strip_tac >>
  first_x_assum (qspec_then `ctx` (irule_at (Pos hd))) >>
  simp[venomStateTheory.jump_to_def, lookup_var_update_var, update_var_def, lookup_var_def,
       finite_mapTheory.FLOOKUP_UPDATE, store_copy_normalize_def]
QED

Theorem storage_traversal_backedge:
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  bb.bb_instructions = prefix ++ typed_sa_backedge_insts id ctr nv hdr /\
  ~s.vs_halted /\ s.vs_inst_idx = LENGTH prefix /\
  lookup_var ctr s = SOME (n2w i) /\ ctr <> nv ==>
  ?q. gas_path_mem ctx fn s 0 (OK q) /\
      store_copy_normalize sbase q = store_copy_normalize sbase s /\
      lookup_var ctr q = SOME (n2w (SUC i)) /\
      (!x. x <> ctr /\ x <> nv ==> lookup_var x q = lookup_var x s) /\
      ~q.vs_halted /\ q.vs_current_bb = hdr /\ q.vs_inst_idx = 0
Proof
  strip_tac >>
  `eval_operand (Var ctr) s = SOME (n2w i)` by simp[eval_operand_def] >>
  drule_all typed_sa_backedge_path >> strip_tac >>
  first_x_assum (qspec_then `ctx` (irule_at (Pos hd))) >>
  simp[typed_sa_backedge_state_def, venomStateTheory.jump_to_def,
       lookup_var_update_var, update_var_def, lookup_var_def,
       finite_mapTheory.FLOOKUP_UPDATE, store_copy_normalize_def]
QED

Theorem storage_traversal_entry:
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  bb.bb_instructions = prefix ++
    [mk_inst id MLOAD [src] [len];
     mk_inst (id+1) ASSIGN [Lit 0w] [ctr];
     mk_inst (id+2) JMP [Label hdr] []] /\
  ~s.vs_halted /\ s.vs_inst_idx = LENGTH prefix /\
  eval_operand src s = SOME p /\ w2n p + 32 <= s.vs_alloca_next /\
  mload (w2n p) s = n2w n /\ ctr <> len ==>
  ?q. gas_path_mem ctx fn s 0 (OK q) /\
      store_copy_normalize s q = s /\
      lookup_var ctr q = SOME 0w /\ lookup_var len q = SOME (n2w n) /\
      (!x. x <> ctr /\ x <> len ==> lookup_var x q = lookup_var x s) /\
      ~q.vs_halted /\ q.vs_current_bb = hdr /\ q.vs_inst_idx = 0
Proof
  strip_tac >> drule_all dyn_storage_entry_path >> strip_tac >>
  first_x_assum (qspec_then `ctx` (irule_at (Pos hd))) >>
  simp[venomStateTheory.jump_to_def, lookup_var_update_var, update_var_def,
       lookup_var_def, finite_mapTheory.FLOOKUP_UPDATE, store_copy_normalize_def]
QED

Theorem storage_traversal_fold_fields:
  H = (\i. FOLDL (\a j. store_copy_prefix loc
           (p + n2w (32 + j*stride)) (d + n2w (1 + j*ew)) a ew)
         sbase (COUNT_LIST i)) /\
  store_copy_normalize sbase s = H j ==>
  s.vs_memory = sbase.vs_memory /\ s.vs_allocas = sbase.vs_allocas /\
  s.vs_alloca_next = sbase.vs_alloca_next /\ s.vs_call_ctx = sbase.vs_call_ctx /\
  s.vs_labels = sbase.vs_labels
Proof
  strip_tac >> drule storage_element_fold_fields >>
  disch_then (qspec_then `j` mp_tac) >>
  qpat_x_assum `store_copy_normalize _ _ = _` (SUBST1_TAC o SYM) >>
  simp[store_copy_normalize_def]
QED

Theorem storage_traversal_round[local]:
  lookup_block hdr fn.fn_blocks = SOME hb /\
  hb.bb_instructions =
    [mk_inst hid LT [Var ctr; Var len] [cmp];
     mk_inst (hid+1) ISZERO [Var cmp] [done];
     mk_inst (hid+2) JNZ [Var done; Label exit; Label body_lbl] []] /\
  lookup_block tail fn.fn_blocks = SOME tb /\
  tb.bb_instructions = prefix ++ typed_sa_backedge_insts tid ctr nv hdr /\
  ctr <> cmp /\ ctr <> done /\ len <> cmp /\ len <> done /\
  len <> ctr /\ len <> nv /\ ctr <> nv /\
  (!x. not_fresh_at sa x ==> x <> cmp /\ x <> done /\ x <> ctr /\ x <> nv) /\
  (!u. store_copy_normalize sbase u = H j /\
       (!x. not_fresh_at sa x ==> lookup_var x u = lookup_var x sbase) /\
       lookup_var ctr u = SOME (n2w j) /\ lookup_var len u = SOME (n2w n) /\
       ~u.vs_halted /\ u.vs_current_bb = body_lbl /\ u.vs_inst_idx = 0 ==>
       ?v. gas_path_mem ctx fn u 0 (OK v) /\
           store_copy_normalize sbase v = H (SUC j) /\
           (!x. not_fresh_at sa x ==> lookup_var x v = lookup_var x sbase) /\
           lookup_var ctr v = SOME (n2w j) /\ lookup_var len v = SOME (n2w n) /\
           ~v.vs_halted /\ v.vs_current_bb = tail /\ v.vs_inst_idx = LENGTH prefix) /\
  j < n /\ n < dimword(:256) /\
  store_copy_normalize sbase s = H j /\
  (!x. not_fresh_at sa x ==> lookup_var x s = lookup_var x sbase) /\
  lookup_var ctr s = SOME (n2w j) /\ lookup_var len s = SOME (n2w n) /\
  ~s.vs_halted /\ s.vs_current_bb = hdr /\ s.vs_inst_idx = 0 ==>
  ?t. gas_path_mem ctx fn s 0 (OK t) /\
      store_copy_normalize sbase t = H (SUC j) /\
      (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x sbase) /\
      lookup_var ctr t = SOME (n2w (SUC j)) /\ lookup_var len t = SOME (n2w n) /\
      ~t.vs_halted /\ t.vs_current_bb = hdr /\ t.vs_inst_idx = 0
Proof
  strip_tac >>
  `?q. gas_path_mem ctx fn s 0 (OK q) /\
       store_copy_normalize sbase q = store_copy_normalize sbase s /\
       (!x. x <> cmp /\ x <> done ==> lookup_var x q = lookup_var x s) /\
       ~q.vs_halted /\ q.vs_current_bb = (if j < n then body_lbl else exit) /\ q.vs_inst_idx = 0` by
    (irule storage_traversal_header >>
     qpat_assum `hb.bb_instructions = _` (irule_at Any) >> simp[]) >>
  fs[] >>
  `lookup_var ctr q = SOME (n2w j) /\ lookup_var len q = SOME (n2w n) /\
   (!x. not_fresh_at sa x ==> lookup_var x q = lookup_var x sbase)` by
    metis_tac[] >>
  qpat_x_assum `!u. _ ==> ?v. _` (qspec_then `q` mp_tac) >>
  simp[] >> disch_then (qx_choose_then `r` strip_assume_tac) >>
  `?t. gas_path_mem ctx fn r 0 (OK t) /\
       store_copy_normalize sbase t = H (SUC j) /\
       lookup_var ctr t = SOME (n2w (SUC j)) /\
       (!x. x <> ctr /\ x <> nv ==> lookup_var x t = lookup_var x r) /\
       ~t.vs_halted /\ t.vs_current_bb = hdr /\ t.vs_inst_idx = 0` by
    metis_tac[storage_traversal_backedge] >>
  `(!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x sbase) /\
   lookup_var len t = SOME (n2w n)` by metis_tac[] >>
  qexists_tac `t` >> simp[] >>
  `gas_path_mem ctx fn s (0+0) (OK r)` by
    (irule gas_path_mem_then >> qexists_tac `q` >> simp[]) >>
  fs[] >>
  `gas_path_mem ctx fn s (0+0) (OK t)` by
    (irule gas_path_mem_then >> qexists_tac `r` >> simp[]) >> gvs[]
QED

Theorem storage_traversal_word_round[local]:
  lookup_block hdr fn.fn_blocks = SOME hb /\
  hb.bb_instructions =
    [mk_inst hid LT [Var ctr; Var len] [cmp];
     mk_inst (hid+1) ISZERO [Var cmp] [done];
     mk_inst (hid+2) JNZ [Var done; Label exit; Label body_lbl] []] /\
  code =
    [mk_inst id MUL [Var ctr; Lit 32w] [mv];
     mk_inst (id+1) ADD [Lit 32w; Var mv] [so];
     mk_inst (id+2) ADD [src; Var so] [sp];
     mk_inst (id+3) MLOAD [Var sp] [v];
     mk_inst (id+4) ADD [Var ctr; Lit 1w] [off];
     mk_inst (id+5) ADD [dst; Var off] [dp];
     mk_inst (id+6) (if tr then TSTORE else SSTORE) [Var dp; Var v] []] /\
  lookup_block body_lbl fn.fn_blocks = SOME bb /\
  bb.bb_instructions = code ++ typed_sa_backedge_insts tid ctr nv hdr /\
  ALL_DISTINCT [ctr; len; cmp; done; nv] /\
  ALL_DISTINCT [ctr; mv; so; sp; v; off; dp] /\
  ~MEM len [mv; so; sp; v; off; dp] /\
  (!x. not_fresh_at sa x ==> ~MEM x [ctr; cmp; done; nv; mv; so; sp; v; off; dp]) /\
  (!x. src = Var x \/ dst = Var x ==> not_fresh_at sa x) /\
  H = (\i. FOLDL (\a j. store_copy_prefix (if tr then LocTransient else LocStorage)
         (p + n2w (32 + j*32)) (d + n2w (1+j)) a 1) sbase (COUNT_LIST i)) /\
  eval_operand src sbase = SOME p /\ eval_operand dst sbase = SOME d /\
  ~sbase.vs_call_ctx.cc_static /\
  w2n (p + n2w (32+j*32)) + 32 <= sbase.vs_alloca_next /\
  j < n /\ n < dimword(:256) /\
  store_copy_normalize sbase s = H j /\
  (!x. not_fresh_at sa x ==> lookup_var x s = lookup_var x sbase) /\
  lookup_var ctr s = SOME (n2w j) /\ lookup_var len s = SOME (n2w n) /\
  ~s.vs_halted /\ s.vs_current_bb = hdr /\ s.vs_inst_idx = 0 ==>
  ?t. gas_path_mem ctx fn s 0 (OK t) /\
      store_copy_normalize sbase t = H (SUC j) /\
      (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x sbase) /\
      lookup_var ctr t = SOME (n2w (SUC j)) /\ lookup_var len t = SOME (n2w n) /\
      ~t.vs_halted /\ t.vs_current_bb = hdr /\ t.vs_inst_idx = 0
Proof
  strip_tac >>
  qpat_x_assum `ALL_DISTINCT [ctr; len; cmp; done; nv]`
    (strip_assume_tac o REWRITE_RULE [ALL_DISTINCT, MEM]) >>
  irule storage_traversal_round >>
  qpat_assum `hb.bb_instructions = _` (irule_at Any) >>
  qpat_assum `bb.bb_instructions = _` (irule_at Any) >>
  qpat_assum `lookup_block body_lbl _ = _` (irule_at Any) >>
  fs[IgnAsm `H = _`, ALL_DISTINCT, MEM] >>
  rpt strip_tac >>
  `u.vs_memory = sbase.vs_memory /\ u.vs_allocas = sbase.vs_allocas /\
   u.vs_alloca_next = sbase.vs_alloca_next /\
   u.vs_call_ctx = sbase.vs_call_ctx /\ u.vs_labels = sbase.vs_labels` by
    (irule (SRULE [] (Q.INST [`ew` |-> `1`, `stride` |-> `32`]
       storage_traversal_fold_fields)) >>
     qpat_assum `store_copy_normalize sbase u = _` (irule_at Any) >>
     simp[] >> metis_tac[]) >>
  `eval_operand src u = SOME p /\ eval_operand dst u = SOME d` by
    (conj_tac >- (Cases_on `src` >> gvs[eval_operand_def] >> metis_tac[]) >>
     Cases_on `dst` >> gvs[eval_operand_def] >> metis_tac[]) >>
  `ALL_DISTINCT [ctr; mv; so; sp; v; off; dp] /\
   (!x. src = Var x \/ dst = Var x ==> ~MEM x [mv; so; sp; v; off; dp]) /\
   (!x. not_fresh_at sa x ==> ~MEM x [mv; so; sp; v; off; dp]) /\
   ~MEM len [mv; so; sp; v; off; dp]` by
    (simp[ALL_DISTINCT, MEM] >> metis_tac[]) >>
  `lookup_block u.vs_current_bb fn.fn_blocks = SOME bb /\
   isPREFIX code (DROP u.vs_inst_idx bb.bb_instructions) /\
   ~u.vs_call_ctx.cc_static /\
   w2n (p + n2w (32+j*32)) + 32 <= u.vs_alloca_next` by
    (simp[IgnAsm `H = _`, IS_PREFIX_APPEND] >> metis_tac[]) >>
  mp_tac (Q.INST [`s` |-> `u`] storage_element_word_path) >>
  (impl_tac >- (simp[ALL_DISTINCT, MEM] >> metis_tac[])) >>
  simp[gas_marked_path_def]
QED

Theorem storage_traversal_word_iteration:
  lookup_block hdr fn.fn_blocks = SOME hb /\
  hb.bb_instructions =
    [mk_inst hid LT [Var ctr; Var len] [cmp];
     mk_inst (hid+1) ISZERO [Var cmp] [done];
     mk_inst (hid+2) JNZ [Var done; Label exit; Label body_lbl] []] /\
  code =
    [mk_inst id MUL [Var ctr; Lit 32w] [mv];
     mk_inst (id+1) ADD [Lit 32w; Var mv] [so];
     mk_inst (id+2) ADD [src; Var so] [sp];
     mk_inst (id+3) MLOAD [Var sp] [v];
     mk_inst (id+4) ADD [Var ctr; Lit 1w] [off];
     mk_inst (id+5) ADD [dst; Var off] [dp];
     mk_inst (id+6) (if tr then TSTORE else SSTORE) [Var dp; Var v] []] /\
  lookup_block body_lbl fn.fn_blocks = SOME bb /\
  bb.bb_instructions = code ++ typed_sa_backedge_insts tid ctr nv hdr /\
  ALL_DISTINCT [ctr; len; cmp; done; nv] /\
  ALL_DISTINCT [ctr; mv; so; sp; v; off; dp] /\
  ~MEM len [mv; so; sp; v; off; dp] /\
  (!x. not_fresh_at sa x ==> ~MEM x [ctr; cmp; done; nv; mv; so; sp; v; off; dp]) /\
  (!x. src = Var x \/ dst = Var x ==> not_fresh_at sa x) /\
  H = (\i. FOLDL (\a j. store_copy_prefix (if tr then LocTransient else LocStorage)
         (p + n2w (32 + j*32)) (d + n2w (1+j)) a 1) sbase (COUNT_LIST i)) /\
  eval_operand src sbase = SOME p /\ eval_operand dst sbase = SOME d /\
  ~sbase.vs_call_ctx.cc_static /\
  (!j. j < n ==> w2n (p + n2w (32+j*32)) + 32 <= sbase.vs_alloca_next) /\
  n < dimword(:256) /\
  store_copy_normalize sbase s = H 0 /\
  (!x. not_fresh_at sa x ==> lookup_var x s = lookup_var x sbase) /\
  lookup_var ctr s = SOME 0w /\ lookup_var len s = SOME (n2w n) /\
  ~s.vs_halted /\ s.vs_current_bb = hdr /\ s.vs_inst_idx = 0 ==>
  ?t. gas_path_mem ctx fn s 0 (OK t) /\
      store_copy_normalize sbase t = H n /\
      (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x sbase) /\
      lookup_var ctr t = SOME (n2w n) /\ lookup_var len t = SOME (n2w n) /\
      ~t.vs_halted /\ t.vs_current_bb = hdr /\ t.vs_inst_idx = 0
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  qabbrev_tac `loop_inv = \j u.
    store_copy_normalize sbase u = H j /\
    (!x. not_fresh_at sa x ==> lookup_var x u = lookup_var x sbase) /\
    lookup_var ctr u = SOME (n2w j) /\ lookup_var len u = SOME (n2w n) /\
    ~u.vs_halted /\ u.vs_current_bb = hdr /\ u.vs_inst_idx = 0` >>
  `?t. gas_path_mem ctx fn s 0 (OK t) /\ loop_inv n t` suffices_by
    simp[Abbr `loop_inv`] >>
  irule (Q.SPECL [`n`, `0`] gas_path_mem_finite_iteration) >>
  simp[Abbr `loop_inv`, IgnAsm `H = _`] >> rpt strip_tac >>
  mp_tac (Q.INST [`s` |-> `u`] storage_traversal_word_round) >>
  (impl_tac >- (simp[] >> metis_tac[])) >> simp[]
QED

Theorem storage_traversal_multi_round[local]:
  lookup_block hdr fn.fn_blocks = SOME hb /\
  hb.bb_instructions =
    [mk_inst hid LT [Var ctr; Var len] [cmp];
     mk_inst (hid+1) ISZERO [Var cmp] [done];
     mk_inst (hid+2) JNZ [Var done; Label exit; Label body_lbl] []] /\
  code =
    [mk_inst id MUL [Var ctr; Lit (n2w em)] [mv];
     mk_inst (id+1) ADD [Lit 32w; Var mv] [so];
     mk_inst (id+2) ADD [src; Var so] [sp];
     mk_inst (id+3) MUL [Var ctr; Lit (n2w ew)] [dm];
     mk_inst (id+4) ADD [Lit 1w; Var dm] [off];
     mk_inst (id+5) ADD [dst; Var off] [dp]] /\
  lookup_block body_lbl fn.fn_blocks = SOME bb /\ isPREFIX code bb.bb_instructions /\
  body_lbl = sc.cs_current_bb /\ LENGTH sc.cs_current_insts = 6 /\
  lookup_block sd.cs_current_bb fn.fn_blocks = SOME tb /\
  tb.bb_instructions = prefix ++ typed_sa_backedge_insts tid ctr nv hdr /\
  LENGTH prefix = LENGTH sd.cs_current_insts /\
  ALL_DISTINCT [ctr; len; cmp; done; nv] /\
  ALL_DISTINCT [ctr; mv; so; sp; dm; off; dp] /\
  ~MEM len [mv; so; sp; dm; off; dp] /\
  (!x. not_fresh_at sa x ==> ~MEM x [ctr; cmp; done; nv; mv; so; sp; dm; off; dp]) /\
  (!x. src = Var x \/ dst = Var x ==> not_fresh_at sa x) /\
  (loc = LocStorage \/ loc = LocTransient) /\
  compile_word_copy_loop (Var sp) (Var dp) ew LocMemory loc F sc = (res,sd) /\
  fn_has_code sc sd fn /\ ew < dimword(:256) /\
  not_fresh_at sc sp /\ not_fresh_at sc dp /\
  not_fresh_at sc ctr /\ not_fresh_at sc len /\
  (!x. not_fresh_at sa x ==> not_fresh_at sc x) /\
  H = (\i. FOLDL (\a j. store_copy_prefix loc
         (p + n2w (32 + j*em)) (d + n2w (1+j*ew)) a ew) sbase (COUNT_LIST i)) /\
  eval_operand src sbase = SOME p /\ eval_operand dst sbase = SOME d /\
  ~sbase.vs_call_ctx.cc_static /\
  w2n (p + n2w (32+j*em)) + 32*ew <= sbase.vs_alloca_next /\
  j < n /\ n < dimword(:256) /\
  store_copy_normalize sbase s = H j /\
  (!x. not_fresh_at sa x ==> lookup_var x s = lookup_var x sbase) /\
  lookup_var ctr s = SOME (n2w j) /\ lookup_var len s = SOME (n2w n) /\
  ~s.vs_halted /\ s.vs_current_bb = hdr /\ s.vs_inst_idx = 0 ==>
  ?t. gas_path_mem ctx fn s 0 (OK t) /\
      store_copy_normalize sbase t = H (SUC j) /\
      (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x sbase) /\
      lookup_var ctr t = SOME (n2w (SUC j)) /\ lookup_var len t = SOME (n2w n) /\
      ~t.vs_halted /\ t.vs_current_bb = hdr /\ t.vs_inst_idx = 0
Proof
  strip_tac >>
  qpat_x_assum `ALL_DISTINCT [ctr; len; cmp; done; nv]`
    (strip_assume_tac o REWRITE_RULE [ALL_DISTINCT, MEM]) >>
  irule storage_traversal_round >>
  qpat_assum `hb.bb_instructions = _` (irule_at Any) >>
  qpat_assum `tb.bb_instructions = _` (irule_at Any) >>
  qpat_assum `lookup_block sd.cs_current_bb _ = _` (irule_at Any) >>
  fs[IgnAsm `H = _`, ALL_DISTINCT, MEM] >> rpt strip_tac >>
  `u.vs_memory = sbase.vs_memory /\ u.vs_allocas = sbase.vs_allocas /\
   u.vs_alloca_next = sbase.vs_alloca_next /\
   u.vs_call_ctx = sbase.vs_call_ctx /\ u.vs_labels = sbase.vs_labels` by
    (irule (Q.INST [`stride` |-> `em`] storage_traversal_fold_fields) >>
     qpat_assum `store_copy_normalize sbase u = _` (irule_at Any) >>
     simp[] >> metis_tac[]) >>
  `eval_operand src u = SOME p /\ eval_operand dst u = SOME d` by
    (conj_tac >- (Cases_on `src` >> gvs[eval_operand_def] >> metis_tac[]) >>
     Cases_on `dst` >> gvs[eval_operand_def] >> metis_tac[]) >>
  qpat_x_assum `isPREFIX code _` (strip_assume_tac o REWRITE_RULE [IS_PREFIX_APPEND]) >>
  mp_tac (Q.INST [`s` |-> `u`] (Q.INST [`u` |-> `res`] storage_element_multi_path)) >>
  (impl_tac >- (simp[ALL_DISTINCT, MEM] >> metis_tac[])) >>
  simp[gas_marked_path_def]
QED

Theorem storage_traversal_multi_iteration[local]:
  lookup_block hdr fn.fn_blocks = SOME hb /\
  hb.bb_instructions =
    [mk_inst hid LT [Var ctr; Var len] [cmp];
     mk_inst (hid+1) ISZERO [Var cmp] [done];
     mk_inst (hid+2) JNZ [Var done; Label exit; Label body_lbl] []] /\
  code =
    [mk_inst id MUL [Var ctr; Lit (n2w em)] [mv];
     mk_inst (id+1) ADD [Lit 32w; Var mv] [so];
     mk_inst (id+2) ADD [src; Var so] [sp];
     mk_inst (id+3) MUL [Var ctr; Lit (n2w ew)] [dm];
     mk_inst (id+4) ADD [Lit 1w; Var dm] [off];
     mk_inst (id+5) ADD [dst; Var off] [dp]] /\
  lookup_block body_lbl fn.fn_blocks = SOME bb /\ isPREFIX code bb.bb_instructions /\
  body_lbl = sc.cs_current_bb /\ LENGTH sc.cs_current_insts = 6 /\
  lookup_block sd.cs_current_bb fn.fn_blocks = SOME tb /\
  tb.bb_instructions = prefix ++ typed_sa_backedge_insts tid ctr nv hdr /\
  LENGTH prefix = LENGTH sd.cs_current_insts /\
  ALL_DISTINCT [ctr; len; cmp; done; nv] /\
  ALL_DISTINCT [ctr; mv; so; sp; dm; off; dp] /\
  ~MEM len [mv; so; sp; dm; off; dp] /\
  (!x. not_fresh_at sa x ==> ~MEM x [ctr; cmp; done; nv; mv; so; sp; dm; off; dp]) /\
  (!x. src = Var x \/ dst = Var x ==> not_fresh_at sa x) /\
  (loc = LocStorage \/ loc = LocTransient) /\
  compile_word_copy_loop (Var sp) (Var dp) ew LocMemory loc F sc = (res,sd) /\
  fn_has_code sc sd fn /\ ew < dimword(:256) /\
  not_fresh_at sc sp /\ not_fresh_at sc dp /\
  not_fresh_at sc ctr /\ not_fresh_at sc len /\
  (!x. not_fresh_at sa x ==> not_fresh_at sc x) /\
  H = (\i. FOLDL (\a j. store_copy_prefix loc
         (p + n2w (32 + j*em)) (d + n2w (1+j*ew)) a ew) sbase (COUNT_LIST i)) /\
  eval_operand src sbase = SOME p /\ eval_operand dst sbase = SOME d /\
  ~sbase.vs_call_ctx.cc_static /\
  (!j. j < n ==> w2n (p + n2w (32+j*em)) + 32*ew <= sbase.vs_alloca_next) /\
  n < dimword(:256) /\
  store_copy_normalize sbase s = H 0 /\
  (!x. not_fresh_at sa x ==> lookup_var x s = lookup_var x sbase) /\
  lookup_var ctr s = SOME 0w /\ lookup_var len s = SOME (n2w n) /\
  ~s.vs_halted /\ s.vs_current_bb = hdr /\ s.vs_inst_idx = 0 ==>
  ?t. gas_path_mem ctx fn s 0 (OK t) /\
      store_copy_normalize sbase t = H n /\
      (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x sbase) /\
      lookup_var ctr t = SOME (n2w n) /\ lookup_var len t = SOME (n2w n) /\
      ~t.vs_halted /\ t.vs_current_bb = hdr /\ t.vs_inst_idx = 0
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  qabbrev_tac `loop_inv = \j u.
    store_copy_normalize sbase u = H j /\
    (!x. not_fresh_at sa x ==> lookup_var x u = lookup_var x sbase) /\
    lookup_var ctr u = SOME (n2w j) /\ lookup_var len u = SOME (n2w n) /\
    ~u.vs_halted /\ u.vs_current_bb = hdr /\ u.vs_inst_idx = 0` >>
  `?t. gas_path_mem ctx fn s 0 (OK t) /\ loop_inv n t` suffices_by
    simp[Abbr `loop_inv`] >>
  irule (Q.SPECL [`n`, `0`] gas_path_mem_finite_iteration) >>
  simp[Abbr `loop_inv`, IgnAsm `H = _`] >> rpt strip_tac >>
  mp_tac (Q.INST [`s` |-> `u`] storage_traversal_multi_round) >>
  (impl_tac >- (simp[] >> metis_tac[])) >> simp[]
QED

Theorem storage_traversal_exit:
  lookup_block hdr fn.fn_blocks = SOME hb /\
  hb.bb_instructions =
    [mk_inst hid LT [Var ctr; Var len] [cmp];
     mk_inst (hid+1) ISZERO [Var cmp] [done];
     mk_inst (hid+2) JNZ [Var done; Label exit; Label body_lbl] []] /\
  lookup_block exit fn.fn_blocks = SOME eb /\
  isPREFIX [mk_inst eid (if tr then TSTORE else SSTORE) [dst; Var len] []]
    eb.bb_instructions /\
  len <> cmp /\ len <> done /\
  (!x. dst = Var x ==> x <> cmp /\ x <> done) /\
  (!x. not_fresh_at sa x ==> x <> cmp /\ x <> done) /\
  store_copy_normalize sbase s = h /\
  (!x. not_fresh_at sa x ==> lookup_var x s = lookup_var x sbase) /\
  eval_operand dst s = SOME d /\ ~s.vs_call_ctx.cc_static /\
  lookup_var ctr s = SOME (n2w n) /\ lookup_var len s = SOME (n2w n) /\
  n < dimword(:256) /\
  ~s.vs_halted /\ s.vs_current_bb = hdr /\ s.vs_inst_idx = 0 ==>
  ?t. gas_path_mem ctx fn s 0 (OK t) /\
      store_copy_normalize sbase t = (if tr then tstore d (n2w n) h else sstore d (n2w n) h) /\
      (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x sbase) /\
      ~t.vs_halted /\ t.vs_current_bb = exit /\ t.vs_inst_idx = 1
Proof
  strip_tac >>
  `?q. gas_path_mem ctx fn s 0 (OK q) /\
       store_copy_normalize sbase q = store_copy_normalize sbase s /\
       (!x. x <> cmp /\ x <> done ==> lookup_var x q = lookup_var x s) /\
       ~q.vs_halted /\ q.vs_current_bb = exit /\ q.vs_inst_idx = 0` by
    (mp_tac (Q.INST [`i` |-> `n`, `bb` |-> `hb`, `id` |-> `hid`]
       storage_traversal_header) >> simp[]) >>
  `q.vs_call_ctx = s.vs_call_ctx /\ q.vs_labels = s.vs_labels` by
    (qpat_x_assum `store_copy_normalize sbase q = store_copy_normalize sbase s`
       (mp_tac o Q.AP_TERM `(\u. (u.vs_call_ctx,u.vs_labels))`) >>
     simp[NoAsms, store_copy_normalize_def]) >>
  `eval_operand dst q = SOME d /\ eval_operand (Var len) q = SOME (n2w n)` by
    (simp[eval_operand_def] >> Cases_on `dst` >> gvs[eval_operand_def] >> metis_tac[]) >>
  `gas_path_mem ctx fn q 0
      (OK ((if tr then tstore d (n2w n) q else sstore d (n2w n) q)
        with vs_inst_idx := q.vs_inst_idx + 1))` by
    (irule dyn_storage_length_store_path >> simp[] >>
     qexistsl_tac [`dst`, `eid`, `Var len`] >> fs[IS_PREFIX_APPEND]) >>
  qexists_tac `(if tr then tstore d (n2w n) q else sstore d (n2w n) q)
     with vs_inst_idx := 1` >>
  conj_tac >- (irule (SRULE [] (Q.INST [`n` |-> `0`, `m` |-> `0`] gas_path_mem_then)) >>
               qexists_tac `q` >> gvs[]) >>
  conj_tac
  >- (Cases_on `tr` >> simp[store_copy_normalize_idx,
        SRULE [] (Q.INST [`loc` |-> `LocStorage`] store_copy_normalize_store),
        SRULE [] (Q.INST [`loc` |-> `LocTransient`] store_copy_normalize_store)]) >>
  Cases_on `tr` >> fs[tstore_def, sstore_def, lookup_var_def] >> metis_tac[]
QED
