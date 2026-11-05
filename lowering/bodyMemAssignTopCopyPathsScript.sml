(* Frame boundaries for counted memory-to-storage execution. *)
Theory bodyMemAssignTopCopyPaths
Ancestors
  bodyMemAssignTopCopyLoop stmtSimStoreCopy fragGasSeqMem fragGasMode fragGasPathMem
  context compileEnv emitHelper emitHelperProps exprLoweringProps
  fragExec venomExecSemantics venomState venomInst
  words arithmetic list rich_list finite_map

Theorem topcopy_prefix_zero[simp]:
  store_copy_prefix loc b k sbase 0 = sbase
Proof
  simp[store_copy_prefix_def, COUNT_LIST_def]
QED

Theorem topcopy_prefix_suc:
  store_copy_prefix loc b k sbase (SUC i) =
    (if loc = LocStorage then sstore else tstore)
      (k + n2w i) (mload (w2n (b + n2w i * 32w)) sbase)
      (store_copy_prefix loc b k sbase i)
Proof
  simp[store_copy_prefix_def, COUNT_LIST_SNOC, FOLDL_SNOC]
QED

Theorem topcopy_prefix_memory[simp]:
  (store_copy_prefix loc b k sbase i).vs_memory = sbase.vs_memory
Proof
  Induct_on `i` >> simp[topcopy_prefix_suc] >>
  Cases_on `loc = LocStorage` >> gvs[sstore_def, tstore_def]
QED

Theorem topcopy_prefix_labels[simp]:
  (store_copy_prefix loc b k sbase i).vs_labels = sbase.vs_labels
Proof
  Induct_on `i` >> simp[topcopy_prefix_suc] >>
  Cases_on `loc = LocStorage` >> gvs[sstore_def, tstore_def]
QED

Theorem topcopy_prefix_call_ctx[simp]:
  (store_copy_prefix loc b k sbase i).vs_call_ctx = sbase.vs_call_ctx
Proof
  Induct_on `i` >> simp[topcopy_prefix_suc] >>
  Cases_on `loc = LocStorage` >> gvs[sstore_def, tstore_def]
QED

Theorem topcopy_prefix_frontier[simp]:
  (store_copy_prefix loc b k sbase i).vs_alloca_next = sbase.vs_alloca_next
Proof
  Induct_on `i` >> simp[topcopy_prefix_suc] >>
  Cases_on `loc = LocStorage` >> gvs[sstore_def, tstore_def]
QED

Theorem topcopy_normalize_jump[simp]:
  store_copy_normalize sbase (jump_to l s) = store_copy_normalize sbase s
Proof
  simp[store_copy_normalize_def, jump_to_def]
QED

Theorem topcopy_normalize_idx[simp]:
  store_copy_normalize sbase (s with vs_inst_idx := idx) =
    store_copy_normalize sbase s
Proof
  simp[store_copy_normalize_def]
QED

Theorem topcopy_normalize_update[simp]:
  store_copy_normalize sbase (update_var v w s) = store_copy_normalize sbase s
Proof
  simp[store_copy_normalize_def, update_var_def]
QED

Theorem topcopy_normalize_store:
  store_copy_normalize sbase
    ((if loc = LocStorage then sstore else tstore) key value s) =
  (if loc = LocStorage then sstore else tstore) key value
    (store_copy_normalize sbase s)
Proof
  Cases_on `loc = LocStorage` >>
  simp[store_copy_normalize_def, sstore_def, tstore_def]
QED

Theorem topcopy_frame_base[simp]:
  store_copy_frame sa loc b k sbase 0 sbase
Proof
  simp[store_copy_frame_def, store_copy_normalize_def]
QED

Theorem topcopy_frame_jump[simp]:
  store_copy_frame sa loc b k sbase i (jump_to l s) =
    store_copy_frame sa loc b k sbase i s
Proof
  simp[store_copy_frame_def, jump_to_def, store_copy_normalize_def, lookup_var_def]
QED

Theorem topcopy_frame_idx[simp]:
  store_copy_frame sa loc b k sbase i (s with vs_inst_idx := idx) =
    store_copy_frame sa loc b k sbase i s
Proof
  simp[store_copy_frame_def, lookup_var_def]
QED

Theorem topcopy_frame_update:
  store_copy_frame sa loc b k sbase i s /\
  (!x. not_fresh_at sa x ==> x <> v) ==>
  store_copy_frame sa loc b k sbase i (update_var v w s)
Proof
  simp[store_copy_frame_def, lookup_var_update_var] >> metis_tac[]
QED

Theorem topcopy_frame_memory:
  store_copy_frame sa loc b k sbase i s ==> s.vs_memory = sbase.vs_memory
Proof
  strip_tac >> fs[store_copy_frame_def] >>
  qpat_x_assum `store_copy_normalize _ _ = _`
    (mp_tac o Q.AP_TERM `\s. s.vs_memory`) >>
  simp[store_copy_normalize_def]
QED

Theorem topcopy_frame_labels:
  store_copy_frame sa loc b k sbase i s ==> s.vs_labels = sbase.vs_labels
Proof
  strip_tac >> fs[store_copy_frame_def] >>
  qpat_x_assum `store_copy_normalize _ _ = _`
    (mp_tac o Q.AP_TERM `\s. s.vs_labels`) >>
  simp[store_copy_normalize_def]
QED

Theorem topcopy_frame_call_ctx:
  store_copy_frame sa loc b k sbase i s ==> s.vs_call_ctx = sbase.vs_call_ctx
Proof
  strip_tac >> fs[store_copy_frame_def] >>
  qpat_x_assum `store_copy_normalize _ _ = _`
    (mp_tac o Q.AP_TERM `\s. s.vs_call_ctx`) >>
  simp[store_copy_normalize_def]
QED

Theorem topcopy_frame_frontier:
  store_copy_frame sa loc b k sbase i s ==> s.vs_alloca_next = sbase.vs_alloca_next
Proof
  strip_tac >> fs[store_copy_frame_def] >>
  qpat_x_assum `store_copy_normalize _ _ = _`
    (mp_tac o Q.AP_TERM `\s. s.vs_alloca_next`) >>
  simp[store_copy_normalize_def]
QED

Theorem topcopy_frame_operand:
  store_copy_frame sa loc b k sbase i s /\
  (!x. op = Var x ==> not_fresh_at sa x) /\
  eval_operand op sbase = SOME w ==>
  eval_operand op s = SOME w
Proof
  strip_tac >> drule topcopy_frame_labels >> strip_tac >>
  Cases_on `op` >> gvs[eval_operand_def, store_copy_frame_def] >>
  metis_tac[]
QED

Theorem topcopy_frame_load:
  store_copy_frame sa loc b k sbase i s ==> mload addr s = mload addr sbase
Proof
  strip_tac >> drule topcopy_frame_memory >> simp[mload_def]
QED

Theorem topcopy_frame_store:
  store_copy_frame sa loc b k sbase i s ==>
  store_copy_frame sa loc b k sbase (SUC i)
    ((if loc = LocStorage then sstore else tstore)
      (k + n2w i) (mload (w2n (b + n2w i * 32w)) sbase) s)
Proof
  simp[store_copy_frame_def, topcopy_prefix_suc, topcopy_normalize_store] >>
  strip_tac >> Cases_on `loc = LocStorage` >>
  gvs[sstore_def, tstore_def, lookup_var_def]
QED

Theorem topcopy_frame_index_bound:
  store_copy_frame sa loc b k sbase i s /\
  w2n b + 32*n <= sbase.vs_alloca_next /\ i < n ==>
  w2n b + 32*(i+1) <= s.vs_alloca_next
Proof
  strip_tac >> drule topcopy_frame_frontier >> decide_tac
QED

Theorem topcopy_source_run:
  !sa loc b k sbase i s src cv mv sv vv id.
    store_copy_frame sa loc b k sbase i s /\
    eval_operand src sbase = SOME b /\
    (!x. src = Var x ==> not_fresh_at sa x) /\
    eval_operand (Var cv) s = SOME (n2w i) /\
    ALL_DISTINCT [cv;mv;sv;vv] /\
    (!x. not_fresh_at sa x ==> ~MEM x [mv;sv;vv]) ==>
    ?t. run_inst_seq
      [mk_inst id MUL [Var cv; Lit 32w] [mv];
       mk_inst (id+1) ADD [src; Var mv] [sv];
       mk_inst (id+2) MLOAD [Var sv] [vv]] s = OK t /\
      store_copy_frame sa loc b k sbase i t /\
      eval_operand (Var cv) t = SOME (n2w i) /\
      eval_operand (Var vv) t =
        SOME (mload (w2n (b + n2w i * 32w)) sbase) /\
      t.vs_current_bb = s.vs_current_bb /\
      t.vs_inst_idx = s.vs_inst_idx /\ t.vs_halted = s.vs_halted
Proof
  rpt gen_tac >> strip_tac >>
  qabbrev_tac `s1 = update_var mv (n2w i * 32w) s` >>
  `store_copy_frame sa loc b k sbase i s1` by
    (simp[Abbr `s1`] >> irule topcopy_frame_update >> gvs[] >> metis_tac[]) >>
  `eval_operand src s1 = SOME b` by
    (irule topcopy_frame_operand >> metis_tac[]) >>
  `store_copy_frame sa loc b k sbase i
      (update_var sv (b + n2w i * 32w) s1)` by
    (irule topcopy_frame_update >> gvs[] >> metis_tac[]) >>
  `mload (w2n (b + n2w i * 32w))
      (update_var sv (b + n2w i * 32w) s1) =
    mload (w2n (b + n2w i * 32w)) sbase` by
    (drule_all topcopy_frame_load >> simp[]) >>
  qexists_tac `update_var vv (mload (w2n (b + n2w i * 32w)) sbase)
                (update_var sv (b + n2w i * 32w) s1)` >>
  conj_tac
  >- (`step_inst_base (mk_inst id MUL [Var cv; Lit 32w] [mv]) s = OK s1` by
        (simp[Abbr `s1`] >> irule step_MUL >> simp[eval_operand_lit]) >>
      `step_inst_base (mk_inst (id+1) ADD [src; Var mv] [sv]) s1 =
         OK (update_var sv (b + n2w i * 32w) s1)` by
        (irule step_ADD >> simp[Abbr `s1`, eval_operand_update_var]) >>
      `step_inst_base (mk_inst (id+2) MLOAD [Var sv] [vv])
         (update_var sv (b + n2w i * 32w) s1) =
       OK (update_var vv (mload (w2n (b + n2w i * 32w)) sbase)
             (update_var sv (b + n2w i * 32w) s1))` by
        simp[stepInstBaseLib.simp_opcode_clause ``MLOAD``, mk_inst_def,
             exec_read1_def, eval_operand_update_var] >>
      simp[run_inst_seq_def]) >>
  conj_tac
  >- (irule topcopy_frame_update >> gvs[] >> metis_tac[]) >>
  gvs[eval_operand_def, lookup_var_update_var, ALL_DISTINCT,
      update_var_def, Abbr `s1`]
QED

Theorem topcopy_destination_run:
  !sa loc b k sbase i s dst cv vv dv id.
    store_copy_frame sa loc b k sbase i s /\
    eval_operand dst sbase = SOME k /\
    (!x. dst = Var x ==> not_fresh_at sa x) /\
    eval_operand (Var cv) s = SOME (n2w i) /\
    eval_operand (Var vv) s = SOME (mload (w2n (b + n2w i * 32w)) sbase) /\
    ALL_DISTINCT [cv;vv;dv] /\
    (!x. not_fresh_at sa x ==> x <> dv) /\
    ~sbase.vs_call_ctx.cc_static ==>
    ?t. run_inst_seq
      [mk_inst id ADD [dst; Var cv] [dv];
       mk_inst (id+1) (if loc = LocStorage then SSTORE else TSTORE)
         [Var dv; Var vv] []] s = OK t /\
      store_copy_frame sa loc b k sbase (SUC i) t /\
      eval_operand (Var cv) t = SOME (n2w i) /\
      t.vs_current_bb = s.vs_current_bb /\
      t.vs_inst_idx = s.vs_inst_idx /\ t.vs_halted = s.vs_halted
Proof
  rpt gen_tac >> strip_tac >>
  `eval_operand dst s = SOME k` by
    (drule_all topcopy_frame_operand >> simp[]) >>
  qabbrev_tac `s1 = update_var dv (k + n2w i) s` >>
  `store_copy_frame sa loc b k sbase i s1` by
    (simp[Abbr `s1`] >> irule topcopy_frame_update >> metis_tac[]) >>
  qexists_tac `(if loc = LocStorage then sstore else tstore)
    (k + n2w i) (mload (w2n (b + n2w i * 32w)) sbase) s1` >>
  conj_tac
  >- (`step_inst_base (mk_inst id ADD [dst; Var cv] [dv]) s = OK s1` by
        (simp[Abbr `s1`] >> irule step_ADD >> simp[]) >>
      simp[run_inst_seq_def] >>
      fs[ALL_DISTINCT, eval_operand_def] >>
      `~(update_var dv (k + n2w i) s).vs_call_ctx.cc_static` by
        (drule topcopy_frame_call_ctx >> gvs[Abbr `s1`, update_var_def]) >>
      Cases_on `loc = LocStorage` >>
      qpat_x_assum `~(update_var _ _ _).vs_call_ctx.cc_static` (fn th =>
        simp[th, stepInstBaseLib.simp_opcode_clause ``SSTORE``,
             stepInstBaseLib.simp_opcode_clause ``TSTORE``, mk_inst_def,
             exec_write2_def, eval_operand_def, lookup_var_update_var,
             Abbr `s1`])) >>
  conj_tac >- (irule topcopy_frame_store >> simp[]) >>
  Cases_on `loc = LocStorage` >>
  gvs[sstore_def, tstore_def, eval_operand_def, lookup_var_def,
      update_var_def, Abbr `s1`, ALL_DISTINCT, FLOOKUP_UPDATE]
QED

Theorem topcopy_increment_run:
  !sa loc b k sbase i s cv nv id.
    store_copy_frame sa loc b k sbase (SUC i) s /\
    eval_operand (Var cv) s = SOME (n2w i) /\ cv <> nv /\
    (!x. not_fresh_at sa x ==> x <> cv /\ x <> nv) ==>
    ?t. run_inst_seq
      [mk_inst id ADD [Var cv; Lit 1w] [nv];
       mk_inst (id+1) ASSIGN [Var nv] [cv]] s = OK t /\
      store_copy_frame sa loc b k sbase (SUC i) t /\
      eval_operand (Var cv) t = SOME (n2w (SUC i)) /\
      t.vs_current_bb = s.vs_current_bb /\
      t.vs_inst_idx = s.vs_inst_idx /\ t.vs_halted = s.vs_halted
Proof
  rpt gen_tac >> strip_tac >>
  qabbrev_tac `s1 = update_var nv (n2w i + 1w) s` >>
  `store_copy_frame sa loc b k sbase (SUC i) s1` by
    (simp[Abbr `s1`] >> irule topcopy_frame_update >> metis_tac[]) >>
  qexists_tac `update_var cv (n2w i + 1w) s1` >> conj_tac
  >- (`step_inst_base (mk_inst id ADD [Var cv; Lit 1w] [nv]) s = OK s1` by
        (simp[Abbr `s1`] >> irule step_ADD >> simp[eval_operand_lit]) >>
      simp[run_inst_seq_def, stepInstBaseLib.simp_opcode_clause ``ASSIGN``,
           mk_inst_def, eval_operand_update_var, Abbr `s1`]) >>
  conj_tac >- (irule topcopy_frame_update >> metis_tac[]) >>
  simp[eval_operand_update_var, update_var_def, Abbr `s1`,
       arithmeticTheory.ADD1, wordsTheory.word_add_n2w]
QED

Theorem topcopy_body_run:
  !sa loc b k sbase i s src dst cv mv sv vv dv nv id.
    store_copy_frame sa loc b k sbase i s /\
    eval_operand src sbase = SOME b /\ eval_operand dst sbase = SOME k /\
    (!x. src = Var x \/ dst = Var x ==> not_fresh_at sa x) /\
    eval_operand (Var cv) s = SOME (n2w i) /\
    ALL_DISTINCT [cv;mv;sv;vv;dv;nv] /\
    (!x. not_fresh_at sa x ==> ~MEM x [cv;mv;sv;vv;dv;nv]) /\
    ~sbase.vs_call_ctx.cc_static ==>
    ?t. run_inst_seq
      [mk_inst id MUL [Var cv; Lit 32w] [mv];
       mk_inst (id+1) ADD [src; Var mv] [sv];
       mk_inst (id+2) MLOAD [Var sv] [vv];
       mk_inst (id+3) ADD [dst; Var cv] [dv];
       mk_inst (id+4) (if loc = LocStorage then SSTORE else TSTORE) [Var dv; Var vv] [];
       mk_inst (id+5) ADD [Var cv; Lit 1w] [nv];
       mk_inst (id+6) ASSIGN [Var nv] [cv]] s = OK t /\
      store_copy_frame sa loc b k sbase (SUC i) t /\
      eval_operand (Var cv) t = SOME (n2w (SUC i)) /\
      t.vs_current_bb = s.vs_current_bb /\
      t.vs_inst_idx = s.vs_inst_idx /\ t.vs_halted = s.vs_halted
Proof
  rpt gen_tac >> strip_tac >>
  `ALL_DISTINCT [cv;mv;sv;vv] /\ ALL_DISTINCT [cv;vv;dv] /\ cv <> nv` by
    gvs[ALL_DISTINCT] >>
  `(!x. src = Var x ==> not_fresh_at sa x) /\
   (!x. dst = Var x ==> not_fresh_at sa x) /\
   (!x. not_fresh_at sa x ==> ~MEM x [mv;sv;vv]) /\
   (!x. not_fresh_at sa x ==> x <> dv) /\
   (!x. not_fresh_at sa x ==> x <> cv /\ x <> nv)` by
    (gvs[] >> metis_tac[]) >>
  drule_all topcopy_source_run >>
  disch_then (qspec_then `id` (qx_choose_then `s1` strip_assume_tac)) >>
  drule_all topcopy_destination_run >>
  disch_then (qspec_then `id+3` (qx_choose_then `s2` strip_assume_tac)) >>
  drule_all topcopy_increment_run >>
  disch_then (qspec_then `id+5` (qx_choose_then `t` strip_assume_tac)) >>
  qexists_tac `t` >> simp[] >>
  qpat_x_assum `run_inst_seq _ s = OK s1`
    (assume_tac o SRULE [] o MATCH_MP run_inst_seq_append) >>
  qpat_x_assum `run_inst_seq _ s1 = OK s2`
    (assume_tac o SRULE [arithmeticTheory.ADD_ASSOC] o MATCH_MP run_inst_seq_append) >>
  gvs[arithmeticTheory.ADD_ASSOC]
QED

Theorem topcopy_singleton_run:
  !loc src dst s b k v id.
    (loc = LocStorage \/ loc = LocTransient) /\
    eval_operand src s = SOME b /\ eval_operand dst s = SOME k /\
    (!x. dst = Var x ==> x <> v) /\ ~s.vs_call_ctx.cc_static ==>
    ?t. run_inst_seq
      [mk_inst id MLOAD [src] [v];
       mk_inst (id+1) (if loc = LocStorage then SSTORE else TSTORE)
         [dst; Var v] []] s = OK t /\
      store_copy_normalize s t =
        (if loc = LocStorage then sstore else tstore) k (mload (w2n b) s) s /\
      (!x. x <> v ==> lookup_var x t = lookup_var x s) /\
      t.vs_current_bb = s.vs_current_bb /\
      t.vs_inst_idx = s.vs_inst_idx /\ t.vs_halted = s.vs_halted
Proof
  rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
  qabbrev_tac `u = update_var v (mload (w2n b) s) s` >>
  `eval_operand dst u = SOME k` by
    (Cases_on `dst` >> gvs[Abbr `u`, eval_operand_def,
      lookup_var_def, update_var_def, FLOOKUP_UPDATE]) >>
  `step_inst_base (mk_inst id MLOAD [src] [v]) s = OK u` by
    simp[Abbr `u`, stepInstBaseLib.simp_opcode_clause ``MLOAD``,
         mk_inst_def, exec_read1_def] >>
  qexists_tac `(if loc = LocStorage then sstore else tstore)
    k (mload (w2n b) s) u` >>
  conj_tac
  >- (simp[run_inst_seq_def] >> Cases_on `loc = LocStorage` >>
      simp[stepInstBaseLib.simp_opcode_clause ``SSTORE``,
           stepInstBaseLib.simp_opcode_clause ``TSTORE``, mk_inst_def,
           exec_write2_def, Abbr `u`, eval_operand_update_var, update_var_def] >>
      Cases_on `dst` >> gvs[eval_operand_def, lookup_var_def,
                            update_var_def, FLOOKUP_UPDATE]) >>
  Cases_on `loc = LocStorage` >>
  simp[Abbr `u`, store_copy_normalize_def, sstore_def, tstore_def,
       update_var_def, lookup_var_def, FLOOKUP_UPDATE,
       venom_state_component_equality]
QED
