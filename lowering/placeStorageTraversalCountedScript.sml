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
