(* Operational storage copies: contents and frame share the counted endpoint. *)
Theory exprExtRequestStoragePath
Ancestors
  exprSimStorageCopy exprExtRequestMaterialize fragGasSeq fragGasMode
  fragGasPath fragExec exprLoweringProps emitHelperProps emitHelper exprLowering context compileEnv
  venomExecSemantics venomInst venomState venomInstProofs
  immutableMemoryFrame venomMemProps list rich_list arithmetic words
Libs
  monadsyntax

Theorem extrequest_storage_load[local]:
  (loc = LocStorage \/ loc = LocTransient) /\
  eval_operand src s = SOME a ==>
  step_inst_base
    (mk_inst id (if loc = LocStorage then SLOAD else TLOAD) [src] [v]) s =
  OK (update_var v (copy_runtime_word loc s a) s)
Proof
  strip_tac >> gvs[]
  >- simp[copy_runtime_word_def, step_SLOAD] >>
  simp[copy_runtime_word_def] >>
  pure_once_rewrite_tac[step_inst_base_def] >>
  pure_rewrite_tac[mk_inst_def] >>
  simp[exec_read1_def]
QED

Theorem extrequest_storage_word_run:
  (loc = LocStorage \/ loc = LocTransient) /\
  eval_operand src s = SOME a /\ eval_operand dst s = SOME (n2w b) /\
  (!x. dst = Var x ==> x <> v) /\ b+32 < 2**256 ==>
  run_inst_seq
    [mk_inst id (if loc = LocStorage then SLOAD else TLOAD) [src] [v];
     mk_inst (id+1) MSTORE [dst; Var v] []] s =
  OK (mstore b (copy_runtime_word loc s a)
       (update_var v (copy_runtime_word loc s a) s))
Proof
  strip_tac >>
  `step_inst_base
     (mk_inst id (if loc = LocStorage then SLOAD else TLOAD) [src] [v]) s =
   OK (update_var v (copy_runtime_word loc s a) s)` by
    (irule extrequest_storage_load >> simp[]) >>
  simp[Once run_inst_seq_def] >>
  `eval_operand dst (update_var v (copy_runtime_word loc s a) s) = SOME (n2w b)` by
    (Cases_on `dst` >> gvs[eval_operand_def, update_var_def, lookup_var_def, finite_mapTheory.FLOOKUP_UPDATE]) >>
  `b < dimword (:256)` by (fs[dimword_def]) >>
  `step_inst_base (mk_inst (id+1) MSTORE [dst; Var v] [])
     (update_var v (copy_runtime_word loc s a) s) =
   OK (mstore b (copy_runtime_word loc s a)
        (update_var v (copy_runtime_word loc s a) s))` by
    (mp_tac (Q.SPECL [`dst`, `Var v`, `n2w b`, `copy_runtime_word loc s a`,
                     `id+1`, `update_var v (copy_runtime_word loc s a) s`]
             step_MSTORE) >>
     simp[eval_operand_def, lookup_var_def, update_var_def,
          finite_mapTheory.FLOOKUP_UPDATE, w2n_n2w]) >>
  gvs[run_inst_seq_def]
QED

Theorem extrequest_storage_word_path:
  (loc = LocStorage \/ loc = LocTransient) /\
  (do v <- emit_op (if loc = LocStorage then SLOAD else TLOAD) [src];
      emit_void MSTORE [dst; v] od) sa = (u,sb) /\
  fn_has_code sa sb func /\
  (!x. src = Var x \/ dst = Var x ==> not_fresh_at sa x) /\
  eval_operand src s = SOME a /\ eval_operand dst s = SOME (n2w b) /\
  b+32 < 2**256 /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?t. gas_marked_path F ctx func s 0 (OK t) /\
      t.vs_current_bb = sb.cs_current_bb /\
      t.vs_inst_idx = LENGTH sb.cs_current_insts /\
      copy_prefix loc a b 1 s 1 t /\
      LENGTH s.vs_memory <= LENGTH t.vs_memory /\
      copy_static t = copy_static s /\
      (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s)
Proof
  strip_tac >> drule storage_copy_word_layout >> strip_tac >>
  qmatch_asmsub_abbrev_tac `mk_inst (sa.cs_next_id + 1) MSTORE [dst; Var v] []` >>
  `!x. dst = Var x ==> x <> v` by metis_tac[] >>
  `run_inst_seq (emitted_insts sa sb) s =
   OK (mstore b (copy_runtime_word loc s a)
       (update_var v (copy_runtime_word loc s a) s))` by
    (qpat_x_assum `emitted_insts _ _ = _` (fn th => pure_rewrite_tac[th]) >>
     irule extrequest_storage_word_run >> simp[] >> metis_tac[]) >>
  `sb.cs_current_insts = sa.cs_current_insts ++ emitted_insts sa sb` by
    gvs[emitted_insts_def, IS_PREFIX_APPEND, DROP_APPEND] >>
  `EVERY (\i. i.inst_opcode <> GAS /\ i.inst_opcode <> INVOKE /\
              ~is_terminator i.inst_opcode) (emitted_insts sa sb)` by
    simp[mk_inst_def, is_terminator_def] >>
  drule_all extrequest_straight_run_path >> strip_tac >>
  `copy_prefix loc a b 1 s 1
     (mstore b (copy_runtime_word loc s a)
       (update_var v (copy_runtime_word loc s a) s))` by
    (irule (SRULE [WORD_ADD_0] (Q.INST [`k` |-> `0`] copy_prefix_extend)) >>
     simp[copy_prefix_update_var, copy_prefix_zero]) >>
  `LENGTH s.vs_memory <= LENGTH
     (mstore b (copy_runtime_word loc s a)
       (update_var v (copy_runtime_word loc s a) s)).vs_memory` by
    simp[LENGTH_mstore_eq, update_var_def] >>
  qexists_tac `mstore b (copy_runtime_word loc s a)
    (update_var v (copy_runtime_word loc s a) s) with
     vs_inst_idx := LENGTH sb.cs_current_insts` >>
  gvs[copy_prefix_idx, LENGTH_mstore_eq, same_blocks_def] >>
  simp[copy_static_def, lookup_var_def, mstore_def, update_var_def,
       finite_mapTheory.FLOOKUP_UPDATE] >> metis_tac[]
QED

(* A terminator path deliberately stops at the raw jump destination. *)
Theorem extrequest_storage_jump_path:
  lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
  get_instruction bb s.vs_inst_idx = SOME inst /\
  (inst.inst_opcode = JMP \/ inst.inst_opcode = JNZ) /\
  step_inst_base inst s = OK (jump_to lbl s) /\ ~s.vs_halted ==>
  gas_marked_path F ctx func s 0 (OK (jump_to lbl s))
Proof
  strip_tac >>
  `gas_path_edge ctx func s 0 (OK (jump_to lbl s))` by
    (simp[gas_path_edge_def] >> qexists_tac `0` >>
     simp[step_inst_non_invoke, gasCountTheory.gas_count_step_def,
          is_terminator_def] >>
     disj2_tac >> disj1_tac >> qexists_tac `lbl` >> simp[]) >>
  simp[gas_marked_path_def] >>
  `~(jump_to lbl s).vs_halted` by simp[jump_to_def] >>
  metis_tac[gas_path_rules, ADD_CLAUSES]
QED

Theorem extrequest_storage_body_path:
  (loc = LocStorage \/ loc = LocTransient) /\
  fn_has_code sa sb func /\ same_blocks sa sb /\
  isPREFIX sa.cs_current_insts sb.cs_current_insts /\
  emitted_insts sa sb =
    [mk_inst sa.cs_next_id ADD [src; Var cv] [sv];
     mk_inst (sa.cs_next_id+1) (if loc = LocStorage then SLOAD else TLOAD) [Var sv] [vv];
     mk_inst (sa.cs_next_id+2) MUL [Var cv; Lit 32w] [mv];
     mk_inst (sa.cs_next_id+3) ADD [dst; Var mv] [dv];
     mk_inst (sa.cs_next_id+4) MSTORE [Var dv; Var vv] [];
     mk_inst (sa.cs_next_id+5) ADD [Var cv; Lit 1w] [nv];
     mk_inst (sa.cs_next_id+6) ASSIGN [Var nv] [cv]] /\
  eval_operand src s = SOME a /\ eval_operand dst s = SOME (n2w b) /\
  eval_operand (Var cv) s = SOME (n2w k) /\
  ALL_DISTINCT [cv;sv;vv;mv;dv;nv] /\
  (!x. src = Var x \/ dst = Var x ==> ~MEM x [cv;sv;vv;mv;dv;nv]) /\
  copy_prefix loc a b n sbase k s /\ k < n /\ b+32*n < 2**256 /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?t. gas_marked_path F ctx func s 0 (OK t) /\
      t.vs_current_bb = sb.cs_current_bb /\
      t.vs_inst_idx = LENGTH sb.cs_current_insts /\
      eval_operand (Var cv) t = SOME (n2w (k+1)) /\
      eval_operand src t = SOME a /\ eval_operand dst t = SOME (n2w b) /\
      copy_prefix loc a b n sbase (k+1) t /\
      LENGTH s.vs_memory <= LENGTH t.vs_memory /\
      copy_static t = copy_static s /\
      (!x. ~MEM x [cv;sv;vv;mv;dv;nv] ==> lookup_var x t = lookup_var x s)
Proof
  strip_tac >>
  `?t. run_inst_seq (emitted_insts sa sb) s = OK t /\
       eval_operand (Var cv) t = SOME (n2w k + 1w) /\
       eval_operand src t = SOME a /\ eval_operand dst t = SOME (n2w b) /\
       (!x. ~MEM x [cv;sv;vv;mv;dv;nv] ==> lookup_var x t = lookup_var x s) /\
       t.vs_current_bb = s.vs_current_bb /\
       t.vs_inst_idx = s.vs_inst_idx /\ t.vs_halted = s.vs_halted /\
       t.vs_labels = s.vs_labels` by
    (qpat_x_assum `emitted_insts _ _ = _` (fn th => pure_rewrite_tac[th]) >>
     irule storage_copy_body_run >> fs[] >> metis_tac[]) >>
  qpat_assum `emitted_insts _ _ = _`
    (fn th => qpat_assum `run_inst_seq _ _ = OK _`
       (assume_tac o PURE_REWRITE_RULE [th])) >>
  `copy_prefix loc a b n sbase (k+1) t` by
    (drule_at (Pat `run_inst_seq _ _ = OK _`) storage_copy_body_prefix >>
     disch_then irule >> fs[] >> metis_tac[]) >>
  `copy_static t = copy_static s /\
   t.vs_memory = (mstore (w2n (n2w b + n2w k * 32w : bytes32))
      (copy_runtime_word loc s (a+n2w k)) s).vs_memory` by
    (drule_at (Pat `run_inst_seq _ _ = OK _`) storage_copy_body_run_effect >>
     disch_then (qspecl_then [`n2w k`, `n2w b`, `a`] mp_tac) >>
     (impl_tac >- (fs[] >> metis_tac[])) >> strip_tac >> gvs[]) >>
  `LENGTH s.vs_memory <= LENGTH t.vs_memory` by simp[LENGTH_mstore_eq] >>
  `sb.cs_current_insts = sa.cs_current_insts ++ emitted_insts sa sb` by
    gvs[emitted_insts_def, IS_PREFIX_APPEND, DROP_APPEND] >>
  `EVERY (\i. i.inst_opcode <> GAS /\ i.inst_opcode <> INVOKE /\
              ~is_terminator i.inst_opcode) (emitted_insts sa sb)` by
    simp[mk_inst_def, is_terminator_def] >>
  drule_all extrequest_straight_run_path >> strip_tac >>
  qexists_tac `t with vs_inst_idx := LENGTH sb.cs_current_insts` >>
  gvs[copy_prefix_idx, same_blocks_def, word_add_n2w] >>
  fs[copy_static_def, lookup_var_def]
QED

(* A bounded iteration composes the very witnesses returned by both phases. *)
Theorem extrequest_storage_iterate_path[local]:
  !remaining k s.
  (!j q. j <= n /\ Inv j q /\ ~q.vs_halted /\
          q.vs_current_bb = hdr /\ q.vs_inst_idx = 0 ==>
     ?r. gas_marked_path F ctx func q 0 (OK r) /\ Inv j r /\
         ~r.vs_halted /\ r.vs_inst_idx = 0 /\
         r.vs_current_bb = (if j = n then exit_lbl else body_lbl)) /\
  (!j q. j < n /\ Inv j q /\ ~q.vs_halted /\
          q.vs_current_bb = body_lbl /\ q.vs_inst_idx = 0 ==>
     ?r. gas_marked_path F ctx func q 0 (OK r) /\ Inv (j+1) r /\
         ~r.vs_halted /\ r.vs_current_bb = hdr /\ r.vs_inst_idx = 0) /\
  k + remaining = n /\ Inv k s /\ ~s.vs_halted /\
  s.vs_current_bb = hdr /\ s.vs_inst_idx = 0 ==>
  ?t. gas_marked_path F ctx func s 0 (OK t) /\ Inv n t /\
      ~t.vs_halted /\ t.vs_current_bb = exit_lbl /\ t.vs_inst_idx = 0
Proof
  Induct_on `remaining`
  >- (rpt strip_tac >> gvs[] >>
      qpat_x_assum `!j q. j <= k /\ _ ==> _`
        (qspecl_then [`k`, `s`] mp_tac) >> simp[] >> metis_tac[]) >>
  rpt strip_tac >>
  `k < n` by decide_tac >>
  qpat_assum `!j q. j <= n /\ _ ==> _`
    (qspecl_then [`k`, `s`] mp_tac) >>
  (impl_tac >- simp[]) >> disch_then (qx_choose_then `r` strip_assume_tac) >>
  `r.vs_current_bb = body_lbl` by simp[] >>
  qpat_assum `!j q. j < n /\ _ ==> _`
    (qspecl_then [`k`, `r`] mp_tac) >>
  (impl_tac >- simp[]) >> disch_then (qx_choose_then `r'` strip_assume_tac) >>
  qpat_x_assum `!k s. _ /\ _ /\ k + remaining = n /\ _ ==> _`
    (qspecl_then [`k+1`, `r'`] mp_tac) >>
  (impl_tac >- (simp[] >> decide_tac)) >> strip_tac >>
  qexists_tac `t` >> simp[] >>
  metis_tac[gas_marked_path_then, ADD_CLAUSES]
QED

Theorem extrequest_storage_test_path:
  fn_has_code sa sb func /\ same_blocks sa sb /\
  isPREFIX sa.cs_current_insts sb.cs_current_insts /\
  emitted_insts sa sb = [mk_inst sa.cs_next_id EQ [Var cv; Lit (n2w n)] [tv]] /\
  storage_copy_inv cv ds loc a b n sbase k s /\
  cv <> tv /\ MEM tv ds /\ k <= n /\ n < 2**256 /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?t. gas_marked_path F ctx func s 0 (OK t) /\
      storage_copy_test cv tv ds loc a b n sbase k t /\
      ~t.vs_halted /\ t.vs_current_bb = sb.cs_current_bb /\
      t.vs_inst_idx = LENGTH sb.cs_current_insts
Proof
  strip_tac >>
  `eval_operand (Var cv) s = SOME (n2w k)` by fs[storage_copy_inv_def] >>
  `n2w k = (n2w n : bytes32) <=> k = n` by
    (`k < dimword (:256) /\ n < dimword (:256)` by
       (fs[dimword_def] >> decide_tac) >> simp[n2w_11]) >>
  `run_inst_seq (emitted_insts sa sb) s =
     OK (update_var tv (bool_to_word (k = n)) s)` by
    (simp[Once run_inst_seq_def] >>
     `step_inst_base (mk_inst sa.cs_next_id EQ [Var cv; Lit (n2w n)] [tv]) s =
        OK (update_var tv (bool_to_word (k = n)) s)` by
       (drule step_EQ >> disch_then (qspecl_then [`Lit (n2w n)`] mp_tac) >>
        simp[eval_operand_def]) >>
     simp[run_inst_seq_def]) >>
  `sb.cs_current_insts = sa.cs_current_insts ++ emitted_insts sa sb` by
    gvs[emitted_insts_def, IS_PREFIX_APPEND, DROP_APPEND] >>
  `EVERY (\i. i.inst_opcode <> GAS /\ i.inst_opcode <> INVOKE /\
              ~is_terminator i.inst_opcode) (emitted_insts sa sb)` by
    simp[mk_inst_def, is_terminator_def] >>
  drule_all extrequest_straight_run_path >> strip_tac >>
  qexists_tac `update_var tv (bool_to_word (k = n)) s with
                vs_inst_idx := LENGTH sb.cs_current_insts` >>
  gvs[same_blocks_def] >>
  fs[storage_copy_test_def, storage_copy_inv_def, storage_copy_frame_def,
     copy_prefix_def, copy_static_def, eval_operand_def, lookup_var_def,
     update_var_def, finite_mapTheory.FLOOKUP_UPDATE] >> metis_tac[]
QED

Theorem extrequest_storage_inv_control[local]:
  storage_copy_inv cv ds loc a b n sbase k s ==>
  storage_copy_inv cv ds loc a b n sbase k (jump_to lbl s) /\
  storage_copy_inv cv ds loc a b n sbase k (s with vs_inst_idx := idx)
Proof
  simp[storage_copy_inv_def, storage_copy_frame_def, copy_prefix_def,
       copy_static_def, jump_to_def, eval_operand_def, lookup_var_def] >>
  metis_tac[]
QED

Theorem extrequest_storage_init_path:
  fn_has_code sa sb func /\ same_blocks sa sb /\
  isPREFIX sa.cs_current_insts sb.cs_current_insts /\
  emitted_insts sa sb = [mk_inst sa.cs_next_id ASSIGN [Lit 0w] [cv]] /\
  MEM cv ds /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?t. gas_marked_path F ctx func s 0 (OK t) /\
      storage_copy_inv cv ds loc a b n s 0 t /\
      ~t.vs_halted /\ t.vs_current_bb = sb.cs_current_bb /\
      t.vs_inst_idx = LENGTH sb.cs_current_insts
Proof
  strip_tac >>
  `run_inst_seq (emitted_insts sa sb) s = OK (update_var cv 0w s)` by
    simp[run_inst_seq_def, step_inst_base_opcode_eqs, eval_operand_def] >>
  `sb.cs_current_insts = sa.cs_current_insts ++ emitted_insts sa sb` by
    gvs[emitted_insts_def, IS_PREFIX_APPEND, DROP_APPEND] >>
  `EVERY (\i. i.inst_opcode <> GAS /\ i.inst_opcode <> INVOKE /\
              ~is_terminator i.inst_opcode) (emitted_insts sa sb)` by
    simp[mk_inst_def, is_terminator_def] >>
  drule_all extrequest_straight_run_path >> strip_tac >>
  qexists_tac `update_var cv 0w s with vs_inst_idx := LENGTH sb.cs_current_insts` >>
  gvs[same_blocks_def] >>
  simp[storage_copy_inv_def, storage_copy_frame_def, copy_prefix_zero,
       copy_prefix_update_var, copy_prefix_idx,
       eval_operand_def, lookup_var_def, update_var_def,
       finite_mapTheory.FLOOKUP_UPDATE] >> metis_tac[]
QED

Theorem extrequest_storage_jmp_inv[local]:
  lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
  get_instruction bb s.vs_inst_idx = SOME (mk_inst id JMP [Label hdr] []) /\
  storage_copy_inv cv ds loc a b n sbase k s /\ ~s.vs_halted ==>
  gas_marked_path F ctx func s 0 (OK (jump_to hdr s)) /\
  storage_copy_inv cv ds loc a b n sbase k (jump_to hdr s)
Proof
  strip_tac >> conj_tac
  >- (irule extrequest_storage_jump_path >>
      goal_assum (drule_at Any) >> simp[mk_inst_def, step_inst_base_opcode_eqs]) >>
  metis_tac[extrequest_storage_inv_control]
QED

Theorem extrequest_storage_jnz_inv[local]:
  lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
  get_instruction bb s.vs_inst_idx =
    SOME (mk_inst id JNZ [Var tv; Label exit_lbl; Label body_lbl] []) /\
  storage_copy_test cv tv ds loc a b n sbase k s /\ ~s.vs_halted ==>
  gas_marked_path F ctx func s 0
    (OK (jump_to (if k = n then exit_lbl else body_lbl) s)) /\
  storage_copy_inv cv ds loc a b n sbase k
    (jump_to (if k = n then exit_lbl else body_lbl) s)
Proof
  strip_tac >> fs[storage_copy_test_def] >> conj_tac
  >- (irule extrequest_storage_jump_path >>
      goal_assum (drule_at Any) >>
      simp[mk_inst_def, step_inst_base_opcode_eqs] >>
      Cases_on `k = n` >> fs[bool_to_word_def]) >>
  metis_tac[extrequest_storage_inv_control]
QED

Theorem extrequest_storage_inv_step[local]:
  storage_copy_inv cv ds loc a b n sbase k s /\
  eval_operand (Var cv) t = SOME (n2w (k+1)) /\
  copy_prefix loc a b n sbase (k+1) t /\
  LENGTH s.vs_memory <= LENGTH t.vs_memory /\
  (!x. ~MEM x ds ==> lookup_var x t = lookup_var x s) /\
  t.vs_labels = s.vs_labels ==>
  storage_copy_inv cv ds loc a b n sbase (k+1) t
Proof
  rw[storage_copy_inv_def, storage_copy_frame_def] >> metis_tac[LESS_EQ_TRANS]
QED

Theorem extrequest_storage_loop_path:
  (loc = LocStorage \/ loc = LocTransient) /\
  compile_word_copy_loop src dst n loc LocMemory F sa = (u,sb) /\
  fn_has_code sa sb func /\
  (!x. src = Var x \/ dst = Var x ==> not_fresh_at sa x) /\
  eval_operand src sbase = SOME a /\ eval_operand dst sbase = SOME (n2w b) /\
  n < 2**256 /\ b+32*n < 2**256 /\ ~sbase.vs_halted /\
  sbase.vs_current_bb = sa.cs_current_bb /\
  sbase.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?t. gas_marked_path F ctx func sbase 0 (OK t) /\
      copy_prefix loc a b n sbase n t /\
      LENGTH sbase.vs_memory <= LENGTH t.vs_memory /\
      copy_static t = copy_static sbase /\
      (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x sbase) /\
      t.vs_current_bb = sb.cs_current_bb /\
      t.vs_inst_idx = LENGTH sb.cs_current_insts
Proof
  disch_then (CONJUNCTS_THEN2 assume_tac strip_assume_tac) >>
  drule_at (Pat `compile_word_copy_loop _ _ _ _ _ _ _ = _`)
    compile_storage_copy_certificate >>
  (impl_tac >- simp[]) >> strip_tac >>
  `fn_has_code sa s0 func` by
    metis_tac[fn_has_code_mid, cs_extends_refl] >>
  `fn_has_code s0 sb func` by metis_tac[fn_has_code_split] >>
  drule_all frag_exec_loop_layout >> strip_tac >>
  qmatch_asmsub_abbrev_tac `ALL_DISTINCT ds` >>
  `!j q. j <= n /\ storage_copy_inv cv ds loc a b n sbase j q /\
         ~q.vs_halted /\ q.vs_current_bb = hdr /\ q.vs_inst_idx = 0 ==>
     ?r. gas_marked_path F ctx func q 0 (OK r) /\
         storage_copy_inv cv ds loc a b n sbase j r /\
         ~r.vs_halted /\ r.vs_inst_idx = 0 /\
         r.vs_current_bb = (if j = n then exit else loop_body)` by
    suspend "header" >>
  `!j q. j < n /\ storage_copy_inv cv ds loc a b n sbase j q /\
         ~q.vs_halted /\ q.vs_current_bb = loop_body /\ q.vs_inst_idx = 0 ==>
     ?r. gas_marked_path F ctx func q 0 (OK r) /\
         storage_copy_inv cv ds loc a b n sbase (j+1) r /\
         ~r.vs_halted /\ r.vs_current_bb = hdr /\ r.vs_inst_idx = 0` by
    suspend "body" >>
  `?r. gas_marked_path F ctx func sbase 0 (OK r) /\
       storage_copy_inv cv ds loc a b n sbase 0 r /\
       ~r.vs_halted /\ r.vs_current_bb = hdr /\ r.vs_inst_idx = 0` by
    suspend "init" >>
  qspecl_then [`n`, `0`, `r`] mp_tac
    (Q.INST [`Inv` |-> `storage_copy_inv cv ds loc a b n sbase`,
             `exit_lbl` |-> `exit`, `body_lbl` |-> `loop_body`]
       extrequest_storage_iterate_path) >>
  (impl_tac >- simp[]) >> strip_tac >>
  qexists_tac `t` >>
  qpat_x_assum `loc = LocStorage \/ loc = LocTransient` kall_tac >>
  qpat_x_assum `!j q. j <= n /\ _ ==> _` kall_tac >>
  qpat_x_assum `!j q. j < n /\ _ ==> _` kall_tac >>
  gvs[storage_copy_inv_def, storage_copy_frame_def] >>
  conj_tac >- metis_tac[gas_marked_path_then, ADD_CLAUSES] >>
  fs[copy_prefix_def] >> metis_tac[]
QED

Resume extrequest_storage_loop_path[header]:
  rpt gen_tac >> strip_tac >>
  `cv <> tv /\ MEM tv ds` by
    (qpat_x_assum `ALL_DISTINCT ds` mp_tac >> simp[Abbr `ds`]) >>
  `q.vs_current_bb = sth.cs_current_bb /\
   q.vs_inst_idx = LENGTH sth.cs_current_insts` by simp[] >>
  drule_all extrequest_storage_test_path >>
  disch_then (qspec_then `ctx` strip_assume_tac) >>
  `lookup_block t.vs_current_bb func.fn_blocks = SOME bb' /\
   get_instruction bb' t.vs_inst_idx =
     SOME (mk_inst stj.cs_next_id JNZ [Var tv; Label exit; Label loop_body] [])`
    by simp[] >>
  drule_all extrequest_storage_jnz_inv >>
  disch_then (qspec_then `ctx` strip_assume_tac) >>
  `gas_marked_path F ctx func q 0
      (OK (jump_to (if j = n then exit else loop_body) t))` by
    (drule_all gas_marked_path_then >> simp[]) >>
  qexists_tac `jump_to (if j = n then exit else loop_body) t` >>
  simp[] >> simp[jump_to_def]
QED
Resume extrequest_storage_loop_path[body]:
  rpt gen_tac >> strip_tac >>
  `!x. src = Var x \/ dst = Var x ==> ~MEM x ds` by metis_tac[] >>
  `eval_operand src q = SOME a /\ eval_operand dst q = SOME (n2w b)` by
    (qpat_assum `storage_copy_inv _ _ _ _ _ _ _ _ _`
       (strip_assume_tac o REWRITE_RULE [storage_copy_inv_def, storage_copy_frame_def]) >>
     conj_tac >> irule storage_copy_operand_frame >>
     goal_assum (drule_at Any) >> metis_tac[]) >>
  `ALL_DISTINCT [cv;sv;vv;mv;dv;nv] /\
   (!x. src = Var x \/ dst = Var x ==> ~MEM x [cv;sv;vv;mv;dv;nv])` by
    (conj_tac
     >- (qpat_x_assum `ALL_DISTINCT ds` mp_tac >> simp[Abbr `ds`]) >>
     qpat_x_assum `!x. src = Var x \/ dst = Var x ==> ~MEM x ds` mp_tac >>
     simp_tac (srw_ss()) [Abbr `ds`, MEM] >> metis_tac[]) >>
  `eval_operand (Var cv) q = SOME (n2w j) /\
   copy_prefix loc a b n sbase j q` by fs[storage_copy_inv_def] >>
  `q.vs_current_bb = stb.cs_current_bb /\
   q.vs_inst_idx = LENGTH stb.cs_current_insts` by simp[] >>
  drule_all extrequest_storage_body_path >>
  disch_then (qspec_then `ctx` strip_assume_tac) >>
  `~t.vs_halted /\ t.vs_labels = q.vs_labels` by
    metis_tac[copy_static_fields] >>
  `storage_copy_inv cv ds loc a b n sbase (j+1) t` by
    (irule extrequest_storage_inv_step >> goal_assum (drule_at Any) >>
     simp[] >> simp[Abbr `ds`] >> metis_tac[]) >>
  `lookup_block t.vs_current_bb func.fn_blocks = SOME bb'' /\
   get_instruction bb'' t.vs_inst_idx =
     SOME (mk_inst ste.cs_next_id JMP [Label hdr] [])` by simp[] >>
  drule_all extrequest_storage_jmp_inv >>
  disch_then (qspec_then `ctx` strip_assume_tac) >>
  `gas_marked_path F ctx func q 0 (OK (jump_to hdr t))` by
    (drule_all gas_marked_path_then >> simp[]) >>
  qexists_tac `jump_to hdr t` >> simp[] >> simp[jump_to_def]
QED
Resume extrequest_storage_loop_path[init]:
  `MEM cv ds` by simp[Abbr `ds`] >>
  drule_all extrequest_storage_init_path >>
  disch_then (qspecl_then [`n`, `loc`, `ctx`, `b`, `a`] mp_tac) >>
  strip_tac >>
  `lookup_block t.vs_current_bb func.fn_blocks = SOME bb /\
   get_instruction bb t.vs_inst_idx =
     SOME (mk_inst s0.cs_next_id JMP [Label hdr] [])` by simp[] >>
  drule_all extrequest_storage_jmp_inv >>
  disch_then (qspec_then `ctx` strip_assume_tac) >>
  `gas_marked_path F ctx func sbase 0 (OK (jump_to hdr t))` by
    (drule_all gas_marked_path_then >> simp[]) >>
  qexists_tac `jump_to hdr t` >> simp[] >> simp[jump_to_def]
QED
Finalise extrequest_storage_loop_path

Theorem extrequest_storage_suffix_path:
  (loc = LocStorage \/ loc = LocTransient) /\
  (if n = 1 then
     do v <- emit_op (if loc = LocStorage then SLOAD else TLOAD) [src];
        emit_void MSTORE [dst; v] od
   else do compile_word_copy_loop src dst n loc LocMemory F; return () od)
    sa = (u,sb) /\
  fn_has_code sa sb func /\
  (!x. src = Var x \/ dst = Var x ==> not_fresh_at sa x) /\
  eval_operand src sbase = SOME a /\ eval_operand dst sbase = SOME (n2w b) /\
  n < 2**256 /\ b+32*n < 2**256 /\ ~sbase.vs_halted /\
  sbase.vs_current_bb = sa.cs_current_bb /\
  sbase.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?t. gas_marked_path F ctx func sbase 0 (OK t) /\
      copy_prefix loc a b n sbase n t /\
      LENGTH sbase.vs_memory <= LENGTH t.vs_memory /\
      copy_static t = copy_static sbase /\
      (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x sbase) /\
      t.vs_current_bb = sb.cs_current_bb /\
      t.vs_inst_idx = LENGTH sb.cs_current_insts
Proof
  disch_then (CONJUNCTS_THEN2 assume_tac strip_assume_tac) >>
  Cases_on `n = 1`
  >- (qpat_x_assum `n = 1` SUBST_ALL_TAC >>
      qpat_x_assum `(if _ then _ else _) sa = _` mp_tac >>
      pure_rewrite_tac [REFL_CLAUSE, COND_CLAUSES] >> strip_tac >>
      rule_assum_tac (PURE_REWRITE_RULE [MULT_RIGHT_1]) >>
      drule_all extrequest_storage_word_path >>
      disch_then (qspec_then `ctx` strip_assume_tac) >>
      qexists_tac `t` >> simp[]) >>
  qpat_x_assum `(if _ then _ else _) sa = _` mp_tac >>
  simp[comp_ignore_bind_def, comp_bind_def, comp_return_def] >>
  pairarg_tac >> simp[] >> strip_tac >>
  qpat_x_assum `cs' = sb` SUBST_ALL_TAC >>
  drule_all extrequest_storage_loop_path >>
  disch_then (qspec_then `ctx` mp_tac) >> simp[]
QED
