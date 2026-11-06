(* Frame boundaries for counted memory-to-storage execution. *)
Theory bodyMemAssignTopCopyPaths
Ancestors
  bodyMemAssignTopCopyCompiler bodyMemAssignTopCopyLoop stmtSimStoreCopy fragGasSeqMem fragGasMode fragGasPathMem
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

Theorem topcopy_seq_path:
  !code s t ctx func bb.
    ~s.vs_halted /\
    lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
    isPREFIX code (DROP s.vs_inst_idx bb.bb_instructions) /\
    EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode) code /\
    EVERY (\i. i.inst_opcode <> GAS) code /\
    run_inst_seq_mem_ok code s /\
    run_inst_seq code s = OK t ==>
    gas_marked_path T ctx func s 0
      (OK (t with vs_inst_idx := s.vs_inst_idx + LENGTH code))
Proof
  rpt strip_tac >> drule_all run_inst_seq_gas_path_mem >>
  `FILTER (\i. i.inst_opcode = GAS) code = []` by
    (gvs[EVERY_MEM, FILTER_EQ_NIL] >> metis_tac[]) >>
  simp[gas_marked_path_def]
QED

Theorem topcopy_jump_path:
  ~s.vs_halted /\
  lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
  get_instruction bb s.vs_inst_idx = SOME inst /\
  (inst.inst_opcode = JMP \/ inst.inst_opcode = JNZ) /\
  step_inst_base inst s = OK (jump_to lbl s) ==>
  gas_marked_path T ctx func s 0 (OK (jump_to lbl s))
Proof
  strip_tac >>
  `gas_path_mem_edge ctx func s 0 (OK (jump_to lbl s))` by
    (simp[gas_path_mem_edge_def] >> qexists_tac `0` >>
     simp[step_inst_non_invoke, gasCountTheory.gas_count_step_def,
          memSafeRunTheory.mem_safe_step_non_invoke,
          unitTransformDefsTheory.inst_mem_below_frontier_def,
          unitMemInvTheory.inst_mem_ranges_def,
          contextCodegenRelTheory.source_memory_read_ranges_def,
          codegenRelTheory.source_memory_write_ranges_def,
          memSafeRunTheory.inst_dload_in_section_def,
          is_terminator_def] >> metis_tac[]) >>
  simp[gas_marked_path_def] >>
  drule (cj 2 gas_path_mem_rules) >>
  disch_then (qspec_then `0` mp_tac) >> simp[] >>
  disch_then irule >> irule (cj 1 gas_path_mem_rules) >>
  simp[jump_to_def]
QED

Theorem topcopy_singleton_path:
  !loc src dst s b k v id ctx func bb.
    (loc = LocStorage \/ loc = LocTransient) /\
    eval_operand src s = SOME b /\ eval_operand dst s = SOME k /\
    (!x. dst = Var x ==> x <> v) /\ ~s.vs_call_ctx.cc_static /\
    ~s.vs_halted /\ w2n b + 32 <= s.vs_alloca_next /\
    lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
    isPREFIX
      [mk_inst id MLOAD [src] [v];
       mk_inst (id+1) (if loc = LocStorage then SSTORE else TSTORE)
         [dst; Var v] []] (DROP s.vs_inst_idx bb.bb_instructions) ==>
    ?t. gas_marked_path T ctx func s 0 (OK t) /\
      store_copy_normalize s t =
        (if loc = LocStorage then sstore else tstore) k (mload (w2n b) s) s /\
      (!x. x <> v ==> lookup_var x t = lookup_var x s) /\
      t.vs_current_bb = s.vs_current_bb /\
      t.vs_inst_idx = s.vs_inst_idx + 2 /\ ~t.vs_halted
Proof
  rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
  `dst <> Var v` by metis_tac[] >>
  mp_tac (Q.SPECL [`loc`, `src`, `dst`, `s`, `b`, `k`, `v`, `id`]
    topcopy_singleton_run) >> simp[] >>
  disch_then (qx_choose_then `u` strip_assume_tac) >>
  `run_inst_seq_mem_ok
      [mk_inst id MLOAD [src] [v];
       mk_inst (id+1) (if loc = LocStorage then SSTORE else TSTORE)
         [dst; Var v] []] s` by
    (irule body_mem_storage_singleton_mem_ok >> metis_tac[]) >>
  drule_at (Pat `run_inst_seq _ _ = _`) topcopy_seq_path >>
  disch_then (qspecl_then [`ctx`, `func`, `bb`] mp_tac) >>
  impl_tac
  >- (Cases_on `loc = LocStorage` >> simp[mk_inst_def, is_terminator_def]) >>
  strip_tac >> qexists_tac `u with vs_inst_idx := s.vs_inst_idx + 2` >>
  gvs[lookup_var_def]
QED

Theorem topcopy_instruction_prefix[local]:
  !code idx bb.
    (!j. j < LENGTH code ==> get_instruction bb (idx+j) = SOME (EL j code)) ==>
    isPREFIX code (DROP idx bb.bb_instructions)
Proof
  Induct >> simp[] >> rpt strip_tac >>
  `get_instruction bb idx = SOME h` by
    (first_x_assum (qspec_then `0` mp_tac) >> simp[]) >>
  `idx < LENGTH bb.bb_instructions /\ EL idx bb.bb_instructions = h` by
    gvs[get_instruction_def, AllCaseEqs()] >>
  `?rest. DROP idx bb.bb_instructions = h::rest` by
    (Cases_on `DROP idx bb.bb_instructions`
     >- (qpat_x_assum `DROP _ _ = []` (mp_tac o Q.AP_TERM `LENGTH`) >>
         simp[LENGTH_DROP]) >>
     qpat_x_assum `DROP _ _ = _::_` (mp_tac o Q.AP_TERM `HD`) >>
     simp[HD_DROP]) >>
  `DROP (idx+1) bb.bb_instructions = rest` by
    (qpat_x_assum `DROP _ _ = _` (mp_tac o Q.AP_TERM `DROP 1`) >>
     simp[DROP_DROP]) >>
  simp[] >>
  qpat_x_assum `!idx bb. _` (qspecl_then [`idx+1`, `bb`] mp_tac) >>
  simp[] >> disch_then irule >> gen_tac >> strip_tac >>
  first_x_assum (qspec_then `SUC j` mp_tac) >> simp[GSYM ADD1]
QED

Theorem topcopy_body_path:
  !ctx func bb sa loc b k sbase i s src dst cv mv sv vv dv nv id.
    store_copy_frame sa loc b k sbase i s /\ ~sbase.vs_call_ctx.cc_static /\
    (loc = LocStorage \/ loc = LocTransient) /\
    w2n b + 32*(i+1) <= sbase.vs_alloca_next /\
    eval_operand src sbase = SOME b /\ eval_operand dst sbase = SOME k /\
    (!x. src = Var x \/ dst = Var x ==> not_fresh_at sa x) /\
    eval_operand (Var cv) s = SOME (n2w i) /\
    ALL_DISTINCT [cv;mv;sv;vv;dv;nv] /\
    (!x. not_fresh_at sa x ==> ~MEM x [cv;mv;sv;vv;dv;nv]) /\
    ~s.vs_halted /\
    lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
    get_instruction bb s.vs_inst_idx = SOME (mk_inst id MUL [Var cv;Lit 32w] [mv]) /\
    get_instruction bb (s.vs_inst_idx+1) = SOME (mk_inst (id+1) ADD [src;Var mv] [sv]) /\
    get_instruction bb (s.vs_inst_idx+2) = SOME (mk_inst (id+2) MLOAD [Var sv] [vv]) /\
    get_instruction bb (s.vs_inst_idx+3) = SOME (mk_inst (id+3) ADD [dst;Var cv] [dv]) /\
    get_instruction bb (s.vs_inst_idx+4) = SOME (mk_inst (id+4)
      (if loc = LocStorage then SSTORE else TSTORE) [Var dv;Var vv] []) /\
    get_instruction bb (s.vs_inst_idx+5) = SOME (mk_inst (id+5) ADD [Var cv;Lit 1w] [nv]) /\
    get_instruction bb (s.vs_inst_idx+6) = SOME (mk_inst (id+6) ASSIGN [Var nv] [cv]) ==>
    ?t. gas_marked_path T ctx func s 0 (OK t) /\
      store_copy_frame sa loc b k sbase (SUC i) t /\
      eval_operand (Var cv) t = SOME (n2w (SUC i)) /\
      t.vs_current_bb = s.vs_current_bb /\
      t.vs_inst_idx = s.vs_inst_idx+7 /\ ~t.vs_halted
Proof
  rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all topcopy_body_run >>
  disch_then (qspec_then `id` (qx_choose_then `u` strip_assume_tac)) >>
  qpat_assum `run_inst_seq _ s = OK u`
    (fn th => mp_tac th) >>
  qmatch_goalsub_abbrev_tac `run_inst_seq code s` >> strip_tac >>
  `isPREFIX code (DROP s.vs_inst_idx bb.bb_instructions)` by
    (irule topcopy_instruction_prefix >> simp[Abbr `code`] >>
     rpt strip_tac >>
     `j=0 \/ j=1 \/ j=2 \/ j=3 \/ j=4 \/ j=5 \/ j=6` by decide_tac >>
     gvs[]) >>
  `eval_operand src s = SOME b` by
    (irule topcopy_frame_operand >> metis_tac[]) >>
  `s.vs_alloca_next = sbase.vs_alloca_next` by
    metis_tac[topcopy_frame_frontier] >>
  `run_inst_seq_mem_ok code s` by
    (simp[Abbr `code`] >> irule body_mem_storage_iteration_mem_ok_modular >>
     gvs[] >> metis_tac[]) >>
  drule_at (Pat `run_inst_seq _ _ = _`) topcopy_seq_path >>
  disch_then (qspecl_then [`ctx`, `func`, `bb`] mp_tac) >>
  impl_tac
  >- (Cases_on `loc = LocStorage` >>
      simp[Abbr `code`, mk_inst_def, is_terminator_def]) >>
  strip_tac >> qexists_tac `u with vs_inst_idx := s.vs_inst_idx+7` >>
  gvs[Abbr `code`, eval_operand_def, lookup_var_def]
QED

Theorem topcopy_header_path:
  !ctx func bb sa loc b k sbase i n s cv tv id exit loop_body.
    store_copy_frame sa loc b k sbase i s /\
    eval_operand (Var cv) s = SOME (n2w i) /\
    cv <> tv /\ (!x. not_fresh_at sa x ==> x <> tv) /\
    i <= n /\ n < dimword (:256) /\ ~s.vs_halted /\
    lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
    get_instruction bb s.vs_inst_idx =
      SOME (mk_inst id EQ [Var cv;Lit (n2w n)] [tv]) /\
    get_instruction bb (SUC s.vs_inst_idx) =
      SOME (mk_inst (id+1) JNZ [Var tv;Label exit;Label loop_body] []) ==>
    ?t. gas_marked_path T ctx func s 0 (OK t) /\
      store_copy_frame sa loc b k sbase i t /\
      eval_operand (Var cv) t = SOME (n2w i) /\
      t.vs_current_bb = (if i = n then exit else loop_body) /\
      t.vs_inst_idx = 0 /\ ~t.vs_halted
Proof
  rpt gen_tac >> strip_tac >>
  `((n2w i:bytes32) = n2w n) = (i = n)` by
    (`i < dimword (:256)` by decide_tac >> simp[n2w_11, LESS_MOD]) >>
  qabbrev_tac `u = update_var tv (bool_to_word (i = n)) s` >>
  qabbrev_tac `r = u with vs_inst_idx := SUC s.vs_inst_idx` >>
  `step_inst_base (mk_inst id EQ [Var cv;Lit (n2w n)] [tv]) s = OK u` by
    (simp[Abbr `u`] >>
     qpat_assum `(n2w i = n2w n) = (i = n)`
       (fn th => once_rewrite_tac [GSYM th]) >>
     irule step_EQ >> simp[eval_operand_lit]) >>
  `gas_path_mem_edge ctx func s 0 (OK r)` by
    (drule_at (Pat `step_inst_base _ _ = _`) straight_line_mem_edge >>
     disch_then (qspecl_then [`func`, `ctx`, `bb`] mp_tac) >>
     simp[mk_inst_def, is_terminator_def, Abbr `r`,
          memSafeRunTheory.inst_dload_in_section_def] >>
     disch_then irule >>
     irule instMemFrontierTheory.below_frontier_no_ranges >> simp[mk_inst_def]) >>
  `gas_marked_path T ctx func s 0 (OK r)` by
    (simp[gas_marked_path_def] >>
     drule (cj 2 gas_path_mem_rules) >>
     disch_then (qspec_then `0` mp_tac) >> simp[] >>
     disch_then irule >> irule (cj 1 gas_path_mem_rules) >>
     simp[Abbr `r`, Abbr `u`, update_var_def]) >>
  `eval_operand (Var tv) r = SOME (bool_to_word (i = n)) /\
   r.vs_current_bb = s.vs_current_bb /\ r.vs_inst_idx = SUC s.vs_inst_idx /\
   ~r.vs_halted` by
    simp[Abbr `r`, Abbr `u`, eval_operand_def, lookup_var_update_var,
         update_var_def, lookup_var_def, FLOOKUP_UPDATE] >>
  `step_inst_base (mk_inst (id+1) JNZ [Var tv;Label exit;Label loop_body] []) r =
    OK (jump_to (if i = n then exit else loop_body) r)` by
    (simp[stepInstBaseLib.simp_opcode_clause ``JNZ``, mk_inst_def] >>
     Cases_on `i = n` >> gvs[bool_to_word_def]) >>
  `gas_marked_path T ctx func r 0
    (OK (jump_to (if i = n then exit else loop_body) r))` by
    (irule topcopy_jump_path >> simp[] >>
     qexistsl_tac [`bb`, `mk_inst (id+1) JNZ [Var tv;Label exit;Label loop_body] []`] >>
     simp[mk_inst_def]) >>
  qexists_tac `jump_to (if i = n then exit else loop_body) r` >>
  conj_tac
  >- (irule (SRULE [] (Q.INST [`n` |-> `0`, `m` |-> `0`] gas_marked_path_then)) >>
      qexists_tac `r` >> simp[]) >>
  `store_copy_frame sa loc b k sbase i u` by
    (simp[Abbr `u`] >> irule topcopy_frame_update >> metis_tac[]) >>
  simp[Abbr `r`, Abbr `u`, jump_to_def, eval_operand_def,
       lookup_var_update_var, update_var_def] >>
  gvs[eval_operand_def, lookup_var_def, FLOOKUP_UPDATE]
QED

Theorem topcopy_loop_induction:
  !n cv sa loc b k sbase hdr loop_body exit ctx func remaining i s.
    (!j u. j <= n /\ store_copy_frame sa loc b k sbase j u /\
       eval_operand (Var cv) u = SOME (n2w j) /\ ~u.vs_halted /\
       u.vs_current_bb = hdr /\ u.vs_inst_idx = 0 ==>
       ?v. gas_marked_path T ctx func u 0 (OK v) /\
         store_copy_frame sa loc b k sbase j v /\
         eval_operand (Var cv) v = SOME (n2w j) /\ ~v.vs_halted /\
         v.vs_current_bb = (if j=n then exit else loop_body) /\ v.vs_inst_idx = 0) /\
    (!j u. j < n /\ store_copy_frame sa loc b k sbase j u /\
       eval_operand (Var cv) u = SOME (n2w j) /\ ~u.vs_halted /\
       u.vs_current_bb = loop_body /\ u.vs_inst_idx = 0 ==>
       ?v. gas_marked_path T ctx func u 0 (OK v) /\
         store_copy_frame sa loc b k sbase (SUC j) v /\
         eval_operand (Var cv) v = SOME (n2w (SUC j)) /\ ~v.vs_halted /\
         v.vs_current_bb = hdr /\ v.vs_inst_idx = 0) /\
    i + remaining = n /\ store_copy_frame sa loc b k sbase i s /\
    eval_operand (Var cv) s = SOME (n2w i) /\ ~s.vs_halted /\
    s.vs_current_bb = hdr /\ s.vs_inst_idx = 0 ==>
    ?t. gas_marked_path T ctx func s 0 (OK t) /\
      store_copy_frame sa loc b k sbase n t /\ ~t.vs_halted /\
      t.vs_current_bb = exit /\ t.vs_inst_idx = 0
Proof
  ntac 12 gen_tac >> Induct >> rpt gen_tac >> strip_tac
  >- (gvs[] >> qpat_x_assum `!j u. j <= i /\ _ ==> _`
        (qspecl_then [`i`, `s`] mp_tac) >> simp[] >> metis_tac[]) >>
  `i < n /\ i <= n` by decide_tac >>
  qpat_assum `!j u. j <= n /\ _ ==> _`
    (qspecl_then [`i`, `s`] mp_tac) >>
  impl_tac >- simp[] >>
  disch_then (qx_choose_then `v` strip_assume_tac) >>
  qpat_x_assum `!j u. j < n /\ _ ==> _`
    (fn th => assume_tac th >> mp_tac th) >>
  disch_then (qspecl_then [`i`, `v`] mp_tac) >>
  impl_tac >- simp[] >>
  disch_then (qx_choose_then `w` strip_assume_tac) >>
  qpat_x_assum `!i s. (!j u. _) /\ _ ==> _`
    (qspecl_then [`SUC i`, `w`] mp_tac) >>
  impl_tac >- (gvs[] >> metis_tac[]) >>
  disch_then (qx_choose_then `t` strip_assume_tac) >> qexists_tac `t` >> simp[] >>
  metis_tac[gas_marked_path_then, ADD_CLAUSES]
QED

Theorem topcopy_init_path:
  !ctx func bb sa loc b k s cv id.
    ~s.vs_halted /\ (!x. not_fresh_at sa x ==> x <> cv) /\
    lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
    get_instruction bb s.vs_inst_idx = SOME (mk_inst id ASSIGN [Lit 0w] [cv]) ==>
    ?t. gas_marked_path T ctx func s 0 (OK t) /\
      store_copy_frame sa loc b k s 0 t /\
      eval_operand (Var cv) t = SOME 0w /\
      t.vs_current_bb = s.vs_current_bb /\
      t.vs_inst_idx = SUC s.vs_inst_idx /\ ~t.vs_halted
Proof
  rpt gen_tac >> strip_tac >>
  qabbrev_tac `u = update_var cv 0w s` >>
  `run_inst_seq [mk_inst id ASSIGN [Lit 0w] [cv]] s = OK u` by
    simp[Abbr `u`, run_inst_seq_def,
         stepInstBaseLib.simp_opcode_clause ``ASSIGN``, mk_inst_def, eval_operand_lit] >>
  `isPREFIX [mk_inst id ASSIGN [Lit 0w] [cv]]
    (DROP s.vs_inst_idx bb.bb_instructions)` by
    (irule topcopy_instruction_prefix >> simp[]) >>
  `run_inst_seq_mem_ok [mk_inst id ASSIGN [Lit 0w] [cv]] s` by
    (simp[fragExecMemTheory.run_inst_seq_mem_ok_last] >>
     irule instMemFrontierTheory.below_frontier_no_ranges >> simp[mk_inst_def]) >>
  drule_at (Pat `run_inst_seq _ _ = _`) topcopy_seq_path >>
  disch_then (qspecl_then [`ctx`, `func`, `bb`] mp_tac) >>
  simp[mk_inst_def, is_terminator_def] >> strip_tac >>
  `store_copy_frame sa loc b k s 0 u` by
    (simp[Abbr `u`] >> irule topcopy_frame_update >> simp[] >> metis_tac[]) >>
  qexists_tac `u with vs_inst_idx := SUC s.vs_inst_idx` >>
  gvs[Abbr `u`, ADD1, eval_operand_def, lookup_var_update_var, update_var_def,
      lookup_var_def, FLOOKUP_UPDATE]
QED

Theorem topcopy_compile_loop_path:
  !ctx func loc src dst n sa u sb sbase b k.
    (loc = LocStorage \/ loc = LocTransient) /\
    compile_word_copy_loop src dst n LocMemory loc F sa = (u,sb) /\
    fn_has_code sa sb func /\ n < dimword (:256) /\
    w2n b + 32*n <= sbase.vs_alloca_next /\
    (!x. src = Var x \/ dst = Var x ==> not_fresh_at sa x) /\
    eval_operand src sbase = SOME b /\ eval_operand dst sbase = SOME k /\
    ~sbase.vs_halted /\ ~sbase.vs_call_ctx.cc_static /\
    sbase.vs_current_bb = sa.cs_current_bb /\
    sbase.vs_inst_idx = LENGTH sa.cs_current_insts ==>
    ?t. gas_marked_path T ctx func sbase 0 (OK t) /\
      store_copy_frame sa loc b k sbase n t /\ ~t.vs_halted /\
      t.vs_current_bb = sb.cs_current_bb /\
      t.vs_inst_idx = LENGTH sb.cs_current_insts
Proof
  rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all topcopy_code_certificate >> strip_tac >>
  map_every (fn q => qpat_x_assum q kall_tac)
    [`compile_word_copy_loop _ _ _ _ _ _ _ = _`, `fn_has_code _ _ _`] >>
  `!j s. j <= n /\ store_copy_frame sa loc b k sbase j s /\
     eval_operand (Var cv) s = SOME (n2w j) /\ ~s.vs_halted /\
     s.vs_current_bb = hdr /\ s.vs_inst_idx = 0 ==>
     ?t. gas_marked_path T ctx func s 0 (OK t) /\
       store_copy_frame sa loc b k sbase j t /\
       eval_operand (Var cv) t = SOME (n2w j) /\ ~t.vs_halted /\
       t.vs_current_bb = (if j=n then exit else loop_body) /\ t.vs_inst_idx = 0` by
    (suspend "header") >>
  `!j s. j < n /\ store_copy_frame sa loc b k sbase j s /\
     eval_operand (Var cv) s = SOME (n2w j) /\ ~s.vs_halted /\
     s.vs_current_bb = loop_body /\ s.vs_inst_idx = 0 ==>
     ?t. gas_marked_path T ctx func s 0 (OK t) /\
       store_copy_frame sa loc b k sbase (SUC j) t /\
       eval_operand (Var cv) t = SOME (n2w (SUC j)) /\ ~t.vs_halted /\
       t.vs_current_bb = hdr /\ t.vs_inst_idx = 0` by
    (suspend "body") >>
  suspend "entry"
QED

Resume topcopy_compile_loop_path[header]:
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `!j. j < 8 ==> _` kall_tac >>
  qpat_x_assum `!j. j < 2 ==> get_instruction ebb _ = _` kall_tac >>
  `cv <> tv /\ (!x. not_fresh_at sa x ==> x <> tv)` by
    (fs[ALL_DISTINCT] >> metis_tac[]) >>
  `get_instruction hbb s.vs_inst_idx = SOME (mk_inst hi EQ [Var cv;Lit (n2w n)] [tv])` by
    (first_x_assum (qspec_then `0` mp_tac) >> simp[]) >>
  `get_instruction hbb (SUC s.vs_inst_idx) =
     SOME (mk_inst (hi+1) JNZ [Var tv;Label exit;Label loop_body] [])` by
    (qpat_x_assum `!j. j < 2 ==> _` (qspec_then `1` mp_tac) >> simp[]) >>
  `lookup_block s.vs_current_bb func.fn_blocks = SOME hbb` by simp[] >>
  drule_all topcopy_header_path >>
  disch_then (qspec_then `ctx` mp_tac) >> metis_tac[]
QED

Resume topcopy_compile_loop_path[body]:
  qpat_x_assum `!j s. j <= n /\ _ ==> _` kall_tac >>
  qpat_x_assum `!j. j < 2 ==> get_instruction ebb _ = _` kall_tac >>
  qpat_x_assum `!j. j < 2 ==> get_instruction hbb _ = _` kall_tac >>
  rpt gen_tac >> strip_tac >>
  `?r. gas_marked_path T ctx func s 0 (OK r) /\
       store_copy_frame sa loc b k sbase (SUC j) r /\
       eval_operand (Var cv) r = SOME (n2w (SUC j)) /\
       r.vs_current_bb = s.vs_current_bb /\
       r.vs_inst_idx = s.vs_inst_idx+7 /\ ~r.vs_halted` by
    (`w2n b + 32*(j+1) <= sbase.vs_alloca_next` by decide_tac >>
     irule topcopy_body_path >> simp[] >>
     qexistsl_tac [`dst`, `dv`, `bi`, `mv`, `nv`, `src`, `sv`, `vv`] >>
     simp[] >> fs[ALL_DISTINCT] >> metis_tac[]) >>
  `gas_marked_path T ctx func r 0 (OK (jump_to hdr r))` by
    (irule topcopy_jump_path >>
     simp[mk_inst_def, stepInstBaseLib.simp_opcode_clause ``JMP``]) >>
  qexists_tac `jump_to hdr r` >> conj_tac
  >- (irule (SRULE [] (Q.INST [`n` |-> `0`, `m` |-> `0`] gas_marked_path_then)) >>
      qexists_tac `r` >> simp[]) >>
  gvs[jump_to_def, eval_operand_def, lookup_var_def]
QED

Resume topcopy_compile_loop_path[entry]:
  qpat_x_assum `!j. j < 8 ==> _` kall_tac >>
  qpat_x_assum `!j. j < 2 ==> get_instruction hbb _ = _` kall_tac >>
  `!x. not_fresh_at sa x ==> x <> cv` by (fs[] >> metis_tac[]) >>
  `~not_fresh_at sa cv` by metis_tac[] >>
  qpat_assum `!j. j < 2 ==> _` (qspec_then `0` (assume_tac o SRULE [])) >>
  qpat_assum `!j. j < 2 ==> _` (qspec_then `1` (assume_tac o SRULE [])) >>
  `?r. gas_marked_path T ctx func sbase 0 (OK r) /\
       store_copy_frame sa loc b k sbase 0 r /\
       eval_operand (Var cv) r = SOME 0w /\
       r.vs_current_bb = sbase.vs_current_bb /\
       r.vs_inst_idx = SUC sbase.vs_inst_idx /\ ~r.vs_halted` by
    (irule topcopy_init_path >> simp[] >> qexists_tac `ei` >> simp[]) >>
  `gas_marked_path T ctx func r 0 (OK (jump_to hdr r))` by
    (irule topcopy_jump_path >>
     simp[ADD1, mk_inst_def, stepInstBaseLib.simp_opcode_clause ``JMP``]) >>
  `?t. gas_marked_path T ctx func (jump_to hdr r) 0 (OK t) /\
       store_copy_frame sa loc b k sbase n t /\ ~t.vs_halted /\
       t.vs_current_bb = exit /\ t.vs_inst_idx = 0` by
    (irule topcopy_loop_induction >>
     conj_tac >- simp[jump_to_def] >>
     conj_tac >- simp[jump_to_def] >>
     qexistsl_tac [`cv`, `hdr`, `0`, `loop_body`, `n`] >>
     simp[] >> gvs[jump_to_def, eval_operand_def, lookup_var_def]) >>
  qexists_tac `t` >> simp[] >>
  irule (SRULE [] (Q.INST [`n` |-> `0`, `m` |-> `0`] gas_marked_path_then)) >>
  qexists_tac `r` >> simp[] >>
  irule (SRULE [] (Q.INST [`n` |-> `0`, `m` |-> `0`] gas_marked_path_then)) >>
  qexists_tac `jump_to hdr r` >> simp[]
QED

Finalise topcopy_compile_loop_path

val _ = List.app (fn (name, th) =>
  let val (oracles, axioms) = Tag.dest_tag (Thm.tag th)
  in
    if null axioms andalso List.all (fn s => s = "DISK_THM") oracles
    then print (name ^ ": kernel dependency audit passed\n")
    else raise Fail (name ^ " has oracle or axiom dependencies")
  end)
  [("topcopy_compile_loop_path", topcopy_compile_loop_path),
   ("topcopy_singleton_path", topcopy_singleton_path),
   ("topcopy_code_certificate", topcopy_code_certificate)];
