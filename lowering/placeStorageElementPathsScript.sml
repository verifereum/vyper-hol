(* Normalized storage-element folds and their counted execution paths. *)
Theory placeStorageElementPaths
Ancestors
  placeStorageLayoutCounted bodyMemAssignTopCopyPaths exprSimAggregateLayout
  stmtSimStoreCopy bodyMemAssignTopCopySuffix venomState venomInst fragGasMode
  compileEnv context fragGasPathMem words list rich_list

Theorem storage_element_normalize_prefix[local]:
  !i. store_copy_normalize sbase (store_copy_prefix loc b k s i) =
      store_copy_prefix loc b k (store_copy_normalize sbase s) i
Proof
  Induct >> simp[topcopy_prefix_suc, topcopy_normalize_store] >>
  simp[store_copy_normalize_def, mload_def]
QED

Theorem storage_element_normalize_frame:
  store_copy_normalize sbase s = a /\
  store_copy_frame sc loc b k s ew t ==>
  store_copy_normalize sbase t = store_copy_prefix loc b k a ew
Proof
  strip_tac >> gvs[store_copy_frame_def] >>
  qpat_x_assum `store_copy_normalize s t = _`
    (mp_tac o Q.AP_TERM `store_copy_normalize sbase`) >>
  simp[storage_element_normalize_prefix, store_copy_normalize_def]
QED

Theorem storage_element_fold_suc:
  H = (\i. FOLDL (\a j. store_copy_prefix loc
           (p + n2w (32 + j*stride)) (d + n2w (1 + j*ew)) a ew)
         sbase (COUNT_LIST i)) ==>
  H (SUC j) = store_copy_prefix loc
    (p + n2w (32 + j*stride)) (d + n2w (1 + j*ew)) (H j) ew
Proof
  simp[COUNT_LIST_SNOC, FOLDL_SNOC]
QED

Theorem storage_element_prefix_allocations[local]:
  (store_copy_prefix loc b k s i).vs_allocas = s.vs_allocas /\
  (store_copy_prefix loc b k s i).vs_alloca_next = s.vs_alloca_next
Proof
  irule topcopy_normalize_allocations >>
  simp[storage_element_normalize_prefix, store_copy_normalize_def] >>
  metis_tac[]
QED

Theorem storage_element_fold_fields:
  H = (\i. FOLDL (\a j. store_copy_prefix loc
           (p + n2w (32 + j*stride)) (d + n2w (1 + j*ew)) a ew)
         sbase (COUNT_LIST i)) ==>
  !j. (H j).vs_memory = sbase.vs_memory /\
      (H j).vs_allocas = sbase.vs_allocas /\
      (H j).vs_alloca_next = sbase.vs_alloca_next /\
      (H j).vs_call_ctx = sbase.vs_call_ctx
Proof
  strip_tac >> Induct
  >- simp[COUNT_LIST_def] >>
  drule storage_element_fold_suc >>
  disch_then (qspec_then `j` SUBST1_TAC) >>
  simp[storage_element_prefix_allocations]
QED

Theorem storage_element_normalize_vars_idx[local]:
  store_copy_normalize sbase (s with <|vs_vars := vs; vs_inst_idx := ix|>) =
  store_copy_normalize sbase s
Proof
  simp[store_copy_normalize_def]
QED

Theorem storage_element_normalize_load[local]:
  mload a (store_copy_normalize sbase s) = mload a s
Proof
  simp[store_copy_normalize_def, mload_def]
QED

Theorem storage_element_normalize_one[local]:
  store_copy_normalize sbase
    ((if tr then tstore else sstore) k (mload (w2n b) s) s) =
  store_copy_prefix (if tr then LocTransient else LocStorage) b k
    (store_copy_normalize sbase s) 1
Proof
  CONV_TAC (RAND_CONV (RAND_CONV numLib.num_CONV)) >>
  Cases_on `tr` >>
  simp[topcopy_prefix_suc, topcopy_normalize_store,
       storage_element_normalize_load, WORD_ADD_0, WORD_MULT_CLAUSES,
       store_copy_normalize_def, sstore_def, tstore_def]
QED

Theorem storage_element_word_path:
  code =
    [mk_inst id MUL [Var ctr; Lit 32w] [mv];
     mk_inst (id+1) ADD [Lit 32w; Var mv] [so];
     mk_inst (id+2) ADD [src; Var so] [sp];
     mk_inst (id+3) MLOAD [Var sp] [v];
     mk_inst (id+4) ADD [Var ctr; Lit 1w] [off];
     mk_inst (id+5) ADD [dst; Var off] [dp];
     mk_inst (id+6) (if tr then TSTORE else SSTORE) [Var dp; Var v] []] /\
  ALL_DISTINCT [ctr; mv; so; sp; v; off; dp] /\
  (!x. src = Var x \/ dst = Var x ==> ~MEM x [mv; so; sp; v; off; dp]) /\
  (!x. not_fresh_at sa x ==> ~MEM x [mv; so; sp; v; off; dp]) /\
  ~MEM len [mv; so; sp; v; off; dp] /\
  H = (\i. FOLDL (\a j. store_copy_prefix
         (if tr then LocTransient else LocStorage)
         (p + n2w (32 + j*32)) (d + n2w (1 + j)) a 1)
       sbase (COUNT_LIST i)) /\
  store_copy_normalize sbase s = H j /\
  (!x. not_fresh_at sa x ==> lookup_var x s = lookup_var x sbase) /\
  eval_operand src s = SOME p /\ eval_operand dst s = SOME d /\
  lookup_var ctr s = SOME (n2w j) /\ lookup_var len s = SOME (n2w n) /\
  ~s.vs_call_ctx.cc_static /\ ~s.vs_halted /\
  w2n (p + n2w (32 + j*32)) + 32 <= s.vs_alloca_next /\
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  isPREFIX code (DROP s.vs_inst_idx bb.bb_instructions) ==>
  ?q. gas_marked_path T ctx fn s 0 (OK q) /\
      store_copy_normalize sbase q = H (SUC j) /\
      (!x. not_fresh_at sa x ==> lookup_var x q = lookup_var x sbase) /\
      lookup_var ctr q = SOME (n2w j) /\
      lookup_var len q = SOME (n2w n) /\
      ~q.vs_halted /\ q.vs_current_bb = s.vs_current_bb /\
      q.vs_inst_idx = s.vs_inst_idx + 7
Proof
  strip_tac >>
  `32w + n2w j * 32w = (n2w (32 + j*32):bytes32)` by
    simp[word_add_n2w, word_mul_n2w] >>
  `n2w j + 1w = (n2w (1+j):bytes32)` by
    simp[word_add_n2w, arithmeticTheory.ADD_COMM] >>
  `w2n (p + (32w + n2w j * 32w)) + 32 <= s.vs_alloca_next` by gvs[] >>
  drule_all dyn_storage_word_body_path >>
  disch_then (qspec_then `ctx` (qx_choose_then `q` strip_assume_tac)) >>
  `H (SUC j) = store_copy_prefix (if tr then LocTransient else LocStorage)
     (p + n2w (32 + j*32)) (d + n2w (1+j)) (H j) 1` by
    (qpat_x_assum `H = _` (fn th => rewrite_tac[th]) >>
     simp[COUNT_LIST_SNOC, FOLDL_SNOC]) >>
  qpat_x_assum `H = _` kall_tac >>
  `store_copy_normalize sbase q = H (SUC j)` by
    (qpat_x_assum `(q with <|vs_vars := _; vs_inst_idx := _|>) = _`
       (mp_tac o Q.AP_TERM `store_copy_normalize sbase`) >>
     simp[storage_element_normalize_vars_idx] >>
     rewrite_tac[GSYM COND_RAND, GSYM COND_RATOR] >>
     simp[storage_element_normalize_one]) >>
  qexists_tac `q` >> simp[gas_marked_path_def] >>
  conj_tac >- gvs[] >>
  qpat_x_assum `(q with <|vs_vars := _; vs_inst_idx := _|>) = _` mp_tac >>
  Cases_on `tr` >> simp[venom_state_component_equality, sstore_def, tstore_def]
QED

Theorem storage_element_multi_copy:
  (loc = LocStorage \/ loc = LocTransient) /\
  compile_word_copy_loop src dst ew LocMemory loc F sc = (u,sd) /\
  fn_has_code sc sd fn /\ ew < dimword (:256) /\
  w2n b + 32*ew <= s.vs_alloca_next /\
  (!x. src = Var x \/ dst = Var x ==> not_fresh_at sc x) /\
  not_fresh_at sc ctr /\ not_fresh_at sc len /\
  (!x. not_fresh_at sa x ==> not_fresh_at sc x) /\
  eval_operand src s = SOME b /\ eval_operand dst s = SOME k /\
  ~s.vs_halted /\ ~s.vs_call_ctx.cc_static /\
  s.vs_current_bb = sc.cs_current_bb /\
  s.vs_inst_idx = LENGTH sc.cs_current_insts /\
  H = (\i. FOLDL (\a j. store_copy_prefix loc
         (p + n2w (32 + j*em)) (d + n2w (1 + j*ew)) a ew)
       sbase (COUNT_LIST i)) /\
  b = p + n2w (32 + j*em) /\ k = d + n2w (1 + j*ew) /\
  store_copy_normalize sbase s = H j /\
  (!x. not_fresh_at sa x ==> lookup_var x s = lookup_var x sbase) /\
  lookup_var ctr s = SOME (n2w j) /\ lookup_var len s = SOME (n2w n) ==>
  ?t. gas_marked_path T ctx fn s 0 (OK t) /\
      store_copy_normalize sbase t = H (SUC j) /\
      (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x sbase) /\
      lookup_var ctr t = SOME (n2w j) /\
      lookup_var len t = SOME (n2w n) /\
      ~t.vs_halted /\ t.vs_current_bb = sd.cs_current_bb /\
      t.vs_inst_idx = LENGTH sd.cs_current_insts
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all topcopy_compile_loop_path >>
  disch_then (qspec_then `ctx` (qx_choose_then `t` strip_assume_tac)) >>
  `H (SUC j) = store_copy_prefix loc b k (H j) ew` by
    (drule storage_element_fold_suc >> simp[]) >>
  qpat_x_assum `H = _` kall_tac >>
  `store_copy_normalize sbase t = H (SUC j)` by
    (drule_all storage_element_normalize_frame >> simp[]) >>
  qexists_tac `t` >> simp[] >>
  fs[store_copy_frame_def] >> metis_tac[]
QED
