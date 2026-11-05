(* Composition of the checked ABI suffix. Semantic observations use ordinary
   run endpoints; subsequent pointer checks use counted endpoint cursors. *)
Theory revertReasonSuffixPathPtr
Ancestors
  revertReasonSuffixPtr revertReasonPrefixFramePtr fragGasSeqPtr
  instSeqComposePtr ghostPcTransportPtr valueEncodingProps pred_set instIdxIndep
  revertReasonPrefixPtr revertAllocationPtr
  typedCopyPtr decoderGhostFramePtr typedCopyLoopHeaderPtr finite_map ptrDiscipline
  mstoreOperandStep revertReasonLayout exprLoweringProps fragExec bodyPtrDefs revertReasonCopyPtr
  venomMemProps venomState venomInst venomExecSemantics words arithmetic list

Theorem alloca_store_literal_taint_bound:
  n < dimword(:256) /\
  step_inst_base (mk_inst id ALLOCA [Lit (n2w n)] [out]) s = OK sa /\
  step_inst_base (mk_inst (id+1) MSTORE [Var out; Lit value] []) sa = OK t /\
  FLOOKUP sa.vs_allocas id = SOME (c,n) /\
  inst_seq_ptr D lo ctx fn PG G tn
    [mk_inst id ALLOCA [Lit (n2w n)] [out];
     mk_inst (id+1) MSTORE [Var out; Lit value] []] s Gf tnf ==>
  tnf.t_mem SUBSET tn.t_mem UNION {i | c <= i /\ i < c+n}
Proof
  strip_tac >>
  qmatch_asmsub_abbrev_tac `inst_seq_ptr D lo ctx fn PG G tn [i;j] s Gf tnf` >>
  qabbrev_tac `tn1 = step_taint i s sa tn` >>
  `tn1.t_mem SUBSET tn.t_mem UNION {i | c <= i /\ i < c+n}` by
    (simp[Abbr `tn1`, Abbr `i`] >>
     irule alloca_step_memory_taint_bound >> goal_assum (drule_at Any) >> simp[]) >>
  `step_inst_base j (sa with vs_inst_idx := SUC s.vs_inst_idx) =
     OK (t with vs_inst_idx := SUC s.vs_inst_idx)` by
    (simp[Abbr `j`, step_inst_inst_idx_indep, mk_inst_def, is_terminator_def,
       exec_result_map_def]) >>
  `tnf = step_taint j sa t tn1` by
    (qpat_x_assum `inst_seq_ptr _ _ _ _ _ _ _ _ _ _ _` mp_tac >>
     simp[inst_seq_ptr_def] >>
     simp[Abbr `tn1`] >> metis_tac[]) >>
  `tnf.t_mem SUBSET tn1.t_mem` by
    (simp[Abbr `j`] >> irule mstore_literal_memory_taint_bound >>
     goal_assum (drule_at Any) >> fs[Abbr `j`]) >>
  metis_tac[SUBSET_TRANS]
QED

Theorem alloca_store_literal_head_frame:
  32 <= n /\ n < dimword(:256) /\ c < dimword(:256) /\
  step_inst_base (mk_inst id ALLOCA [Lit (n2w n)] [out]) s = OK sa /\
  lookup_var out sa = SOME (n2w c) /\
  FLOOKUP sa.vs_allocas id = SOME (c,n) /\
  run_inst_seq [mk_inst id ALLOCA [Lit (n2w n)] [out];
    mk_inst (id+1) MSTORE [Var out; Lit value] []] s = OK t /\
  inst_seq_ptr D lo ctx fn PG G tn
    [mk_inst id ALLOCA [Lit (n2w n)] [out];
     mk_inst (id+1) MSTORE [Var out; Lit value] []] s Gf tnf /\
  (a+32 <= c \/ c+n <= a) /\
  (!j. a <= j /\ j < a+32 ==> j NOTIN tn.t_mem) ==>
  mload a t = mload a s /\
  (!j. a <= j /\ j < a+32 ==> j NOTIN tnf.t_mem)
Proof
  strip_tac >> (
  `step_inst_base (mk_inst (id+1) MSTORE [Var out; Lit value] []) sa =
     OK (mstore (w2n (n2w c : bytes32)) value sa)` by
    (irule step_mstore_operands >> simp[eval_operand_def]) >>
  `c MOD dimword(:256) = c` by (irule LESS_MOD >> simp[]) >>
  fs[w2n_n2w] >>
  `t = mstore c value sa` by
    (qpat_x_assum `run_inst_seq _ _ = _` mp_tac >>
     simp[NoAsms, run_inst_seq_def] >> asm_rewrite_tac[] >>
     simp[NoAsms] >> asm_rewrite_tac[] >> simp[NoAsms]) >>
  `tnf.t_mem SUBSET tn.t_mem UNION {i | c <= i /\ i < c+n}` by
    (drule_all alloca_store_literal_taint_bound >> simp[]) >>
  conj_tac
  >- (drule alloca_step_data_frame >> strip_tac >>
      rewrite_tac[GSYM mem_word_at_eq_mload] >>
      `a+32 <= c \/ c+32 <= a` by decide_tac >>
      simp[mstore_mem_word_at_disjoint]) >>
  rpt strip_tac >>
  `j NOTIN tn.t_mem` by simp[] >>
  `~(c <= j /\ j < c+n)` by decide_tac >>
  fs[SUBSET_DEF] >> metis_tac[])
QED

Theorem revert_reason_size_cell_checks:
  (FLOOKUP s.vs_allocas (id+5) = NONE ==>
     s.vs_alloca_next+32 < dimword(:256)) /\
  (!a sz. FLOOKUP s.vs_allocas (id+5) = SOME (a,sz) ==>
     sz = 32 /\ a+32 < dimword(:256)) /\
  ~ctx_has_dalloca ctx /\
  step_inst_base (mk_inst (id+5) ALLOCA [Lit 32w]
     [STRING #"%" (toString ((v:num)+4))]) s = OK sa /\
  run_inst_seq (TAKE 2 (revert_reason_suffix id v b p q)) s = OK t ==>
  ?Gf tnf c.
    inst_seq_ptr D 0 ctx fn PG G tn
      (TAKE 2 (revert_reason_suffix id v b p q)) s Gf tnf /\
    lookup_var (STRING #"%" (toString ((v:num)+4))) t = SOME c /\
    ptr_covers Gf tnf (STRING #"%" (toString ((v:num)+4))) t 32 /\
    mload (w2n c) t = 32w /\
    (!i. w2n c <= i /\ i < w2n c+32 ==> i NOTIN tnf.t_mem) /\
    (!x C. x <> STRING #"%" (toString ((v:num)+4)) /\
       ptr_covers G tn x s C ==>
       lookup_var x t = lookup_var x s /\ ptr_covers Gf tnf x t C) /\
    (!z head. FLOOKUP sa.vs_allocas (id+5) = SOME (z,32) /\
       (head+32 <= z \/ z+32 <= head) /\
       (!i. head <= i /\ i < head+32 ==> i NOTIN tn.t_mem) ==>
       c = n2w z /\ mload head t = mload head s /\
       (!i. head <= i /\ i < head+32 ==> i NOTIN tnf.t_mem))
Proof
  strip_tac >>
  `!z. FLOOKUP sa.vs_allocas (id+5) = SOME (z,32) ==>
     lookup_var (STRING #"%" (toString ((v:num)+4))) sa = SOME (n2w z) /\
     z+32 < dimword(:256)` by
    (gen_tac >> strip_tac >>
     drule_all (SRULE [] (Q.INST [`n` |-> `32`] alloca_bounds_site)) >> simp[]) >>
  drule_all (SRULE [] (Q.INST [`id` |-> `id+5`, `n` |-> `32`,
    `out` |-> `STRING #"%" (toString ((v:num)+4))`, `value` |-> `32w`]
      alloca_store_literal_checks)) >>
  disch_then (strip_assume_tac o SPEC_ALL) >>
  qpat_x_assum `!a sz. _` kall_tac >>
  qpat_x_assum `FLOOKUP _ _ = NONE ==> _` kall_tac >>
  `step_inst_base (mk_inst (id+6) MSTORE
      [Var (STRING #"%" (toString ((v:num)+4))); Lit 32w] []) sa =
      OK (mstore (w2n a) 32w sa)` by
    (irule step_mstore_operands >> simp[eval_operand_def]) >>
  `t = mstore (w2n a) 32w sa` by
    (qpat_x_assum `run_inst_seq _ _ = _` mp_tac >>
     simp[NoAsms, revert_reason_suffix_def, run_inst_seq_def] >>
     asm_rewrite_tac[] >> simp[NoAsms] >>
     qpat_assum `step_inst_base (mk_inst _ MSTORE _ _) _ = _` SUBST1_TAC >>
     simp[NoAsms]) >>
  qexistsl_tac [`Gf`, `tnf`, `a`] >>
  conj_asm1_tac
  >- fs[revert_reason_suffix_def, ADD_ASSOC] >>
  conj_tac >- fs[lookup_var_def, mstore_def] >>
  conj_tac >- fs[ptr_covers_def, eval_operand_def, lookup_var_def] >>
  conj_tac >- simp[mload_mstore_same] >>
  conj_tac >- simp[] >> conj_tac
  >- (rpt gen_tac >> strip_tac >>
      irule inst_seq_ptr_live_pointer_frame >>
      goal_assum (drule_at Any) >> goal_assum (drule_at Any) >>
      simp[revert_reason_suffix_def, mk_inst_def, is_terminator_def]) >>
  suspend "head"
QED

Resume revert_reason_size_cell_checks[head]:
  rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
  qpat_x_assum `!z. _` drule >> strip_tac >>
  `a = n2w z` by fs[] >> simp[] >>
  `z < dimword(:256)` by decide_tac >>
  fs[revert_reason_suffix_def, ADD_ASSOC] >>
  drule_at (Pat `inst_seq_ptr _ _ _ _ _ _ _ _ _ _ _`)
    (SRULE [GSYM ADD_ASSOC] (Q.INST [`id` |-> `id+5`, `n` |-> `32`]
      alloca_store_literal_head_frame)) >>
  disch_then (qspecl_then [`mstore z 32w sa`, `sa`, `z`, `head`] mp_tac) >>
  simp[]
QED

Finalise revert_reason_size_cell_checks

Theorem offset_add_clean_load_checks:
  lookup_var bas s = SOME P /\ lookup_var off s = SOME (n2w n) /\
  lookup_var src s = SOME Q /\ ptr_covers G tn bas s (n+C) /\
  ptr_covers G tn src s 32 /\ op_taint tn (Var off) = {} /\
  w2n P+n+C < dimword(:256) /\ n < dimword(:256) /\
  (!j. w2n Q <= j /\ j < w2n Q+32 ==> j NOTIN tn.t_mem) /\
  src <> addr /\ bas <> addr /\ 0 < C /\ addr <> len /\ ~ctx_has_dalloca ctx /\
  run_inst_seq [mk_inst id ADD [Var bas; Var off] [addr];
    mk_inst (id+1) MLOAD [Var src] [len]] s = OK t ==>
  ?Gf tnf.
    inst_seq_ptr D 0 ctx fn PG G tn
      [mk_inst id ADD [Var bas; Var off] [addr];
       mk_inst (id+1) MLOAD [Var src] [len]] s Gf tnf /\
    lookup_var addr t = SOME (P+n2w n) /\ ptr_covers Gf tnf addr t C /\
    lookup_var len t = SOME (mload (w2n Q) s) /\
    op_taint tnf (Var len) = {} /\ tnf.t_mem = tn.t_mem /\
    (!a. mload a t = mload a s) /\
    (!x. x <> addr /\ x <> len ==>
      lookup_var x t = lookup_var x s /\ op_taint tnf (Var x) = op_taint tn (Var x) /\
      (!K. ptr_covers G tn x s K ==> ptr_covers Gf tnf x t K))
Proof
  strip_tac >>
  qmatch_goalsub_abbrev_tac `inst_seq_ptr _ _ _ _ _ _ _ [i;j] _ _ _` >>
  `op_taint tn (Var bas) = {}` by fs[ptr_covers_def] >>
  `step_inst_base i s = OK (update_var addr (P+n2w n) s)` by
    (simp[Abbr `i`, mk_inst_def] >> PURE_ONCE_REWRITE_TAC[step_inst_base_def] >>
     PURE_REWRITE_TAC[instruction_accfupds, combinTheory.K_THM, opcode_case_def] >>
     simp[exec_pure2_def, eval_operand_def]) >>
  `ptr_inst_ok D 0 0 ctx fn G tn i s` by
    (simp[Abbr `i`] >> irule ptr_inst_ok_copy_len_binop >> simp[]) >>
  simp[Once inst_seq_ptr_def] >>
  qmatch_goalsub_abbrev_tac `inst_seq_ptr _ _ _ _ _ g1 t1 _ s1 _ _` >>
  `t1.t_mem = tn.t_mem` by
    simp[Abbr `t1`, Abbr `i`, cj 2 copy_len_binop_ghost_frame] >>
  `lookup_var src s1 = SOME Q /\ ptr_covers g1 t1 src s1 32` by
    (conj_tac
     >- (simp[Abbr `s1`, lookup_var_def, update_var_def, FLOOKUP_UPDATE] >>
         fs[lookup_var_def]) >>
     simp[Abbr `g1`, Abbr `t1`, Abbr `s1`] >> irule ptr_covers_step_frame >>
     simp[Abbr `i`, mk_inst_def, lookup_var_def, update_var_def, FLOOKUP_UPDATE] >>
     fs[lookup_var_def]) >>
  `ptr_covers g1 t1 addr s1 C` by
    (simp[Abbr `g1`, Abbr `t1`, Abbr `s1`, Abbr `i`] >>
     irule typed_copy_loop_dynamic_offset_covers >>
     simp[eval_operand_def, w2n_n2w, LESS_MOD] >> qexists_tac `n+C` >> simp[]) >>
  suspend "load"
QED

Resume offset_add_clean_load_checks[load]:
  `step_inst_base j s1 = OK (update_var len (mload (w2n Q) s1) s1)` by
    (simp[Abbr `j`, mk_inst_def] >> PURE_ONCE_REWRITE_TAC[step_inst_base_def] >>
     PURE_REWRITE_TAC[instruction_accfupds, combinTheory.K_THM, opcode_case_def] >>
     simp[exec_read1_def, eval_operand_def]) >>
  `ptr_inst_ok D 0 0 ctx fn g1 t1 j s1` by
    (simp[Abbr `j`] >> irule ptr_inst_ok_mload >> simp[]) >>
  `t = update_var len (mload (w2n Q) s) (update_var addr (P+n2w n) s)` by
    (qpat_x_assum `run_inst_seq _ s = OK t` mp_tac >>
     simp[Once run_inst_seq_def] >>
     simp[NoAsms, run_inst_seq_def] >>
     simp[Abbr `j`, mk_inst_def] >> PURE_ONCE_REWRITE_TAC[step_inst_base_def] >>
     PURE_REWRITE_TAC[instruction_accfupds, combinTheory.K_THM, opcode_case_def] >>
     fs[exec_read1_def, eval_operand_def, update_var_def, lookup_var_def,
        FLOOKUP_UPDATE, mload_def]) >>
  simp[inst_seq_ptr_def] >>
  qmatch_goalsub_abbrev_tac `step_prov PG g1 j sf` >>
  qabbrev_tac `gf = step_prov PG g1 j sf` >>
  qabbrev_tac `tf = step_taint j s1 sf t1` >>
  `op_taint tf (Var len) = {} /\ tf.t_mem = t1.t_mem` by
    (simp[Abbr `tf`, Abbr `j`, Abbr `sf`] >> conj_tac
     >- (irule (cj 1 mload_ghost_clean) >> simp[eval_operand_def]) >>
     irule EQ_TRANS >> qexists_tac `t1.t_mem` >> conj_tac
     >- (irule (cj 2 mload_ghost_clean) >> simp[eval_operand_def]) >> simp[]) >>
  `!x cap. x <> len /\ ptr_covers g1 t1 x s1 cap ==> ptr_covers gf tf x t cap` by
    (rpt gen_tac >> strip_tac >>
     `ptr_covers gf tf x (update_var len (mload (w2n Q) s1) s1) cap` by
       (simp[Abbr `gf`, Abbr `tf`, Abbr `sf`] >> irule ptr_covers_step_frame >>
        simp[Abbr `j`, mk_inst_def, lookup_var_def, update_var_def, FLOOKUP_UPDATE]) >>
     fs[Abbr `s1`, ptr_covers_def, eval_operand_def, lookup_var_def,
        update_var_def, mload_def]) >>
  suspend "frames"
QED

Resume offset_add_clean_load_checks[frames]:
  `ptr_covers gf tf addr t C` by (first_x_assum irule >> simp[]) >>
  gvs[] >>
  simp[update_var_def, lookup_var_def, FLOOKUP_UPDATE, mload_def] >>
  rpt gen_tac >> strip_tac >> conj_tac
  >- (simp[Abbr `tf`, Abbr `j`, Abbr `t1`, Abbr `i`, step_taint_def,
        set_var_taint_def, op_taint_def, mk_inst_def, FLOOKUP_UPDATE]) >>
  qx_gen_tac `cap` >> strip_tac >>
  `ptr_covers g1 t1 x s1 cap` by
    (simp[Abbr `g1`, Abbr `t1`, Abbr `s1`] >> irule ptr_covers_step_frame >>
     simp[Abbr `i`, mk_inst_def, lookup_var_def, update_var_def, FLOOKUP_UPDATE]) >>
  qpat_x_assum `!x cap. _` (qspecl_then [`x`, `cap`] mp_tac) >>
  simp[update_var_def, mload_def]
QED

Finalise offset_add_clean_load_checks

Theorem revert_reason_seven_checks:
  lookup_var b s = SOME B /\ lookup_var p s = SOME P /\
  lookup_var q s = SOME Q /\
  ptr_covers G tn b s (64+ms) /\
  ptr_covers G tn p s (32+ms) /\ ptr_covers G tn q s ms /\
  mload (w2n Q) s = n2w L /\
  (!j. w2n Q <= j /\ j < w2n Q+32 ==> j NOTIN tn.t_mem) /\
  32 + contractABI$ceil32 L <= ms /\ L+63 < dimword(:256) /\
  64+ms < dimword(:256) /\ w2n B+64+ms < dimword(:256) /\
  w2n P+32+ms < dimword(:256) /\
  (!k. 4 <= k /\ k <= 20 ==>
    b <> STRING #"%" (toString ((v:num)+k)) /\
    p <> STRING #"%" (toString (v+k)) /\
    q <> STRING #"%" (toString (v+k))) /\
  ~ctx_has_dalloca ctx /\
  (FLOOKUP s.vs_allocas (id+5) = NONE ==>
     s.vs_alloca_next+32 < dimword(:256)) /\
  (!a sz. FLOOKUP s.vs_allocas (id+5) = SOME (a,sz) ==>
     sz=32 /\ a+32 < dimword(:256)) /\
  step_inst_base (mk_inst (id+5) ALLOCA [Lit 32w]
    [STRING #"%" (toString (v+4))]) s = OK sa /\
  FLOOKUP sa.vs_allocas (id+5) = SOME (c,32) /\
  (w2n Q+32 <= c \/ c+32 <= w2n Q) /\
  run_inst_seq (TAKE 7 (revert_reason_suffix id v (Var b) (Var p) (Var q))) s = OK u ==>
  ?G7 tn7.
    inst_seq_ptr D 0 ctx fn PG G tn
      (TAKE 7 (revert_reason_suffix id v (Var b) (Var p) (Var q))) s G7 tn7 /\
    lookup_var b u = SOME B /\ lookup_var p u = SOME P /\ lookup_var q u = SOME Q /\
    ptr_covers G7 tn7 b u (64+ms) /\
    ptr_covers G7 tn7 p u (32+ms) /\ ptr_covers G7 tn7 q u ms /\
    lookup_var (STRING #"%" (toString (v+4))) u = SOME (n2w c) /\
    ptr_covers G7 tn7 (STRING #"%" (toString (v+4))) u 32 /\
    mload c u = 32w /\ (!j. c <= j /\ j < c+32 ==> j NOTIN tn7.t_mem) /\
    lookup_var (STRING #"%" (toString (v+5))) u = SOME Q /\
    ptr_covers G7 tn7 (STRING #"%" (toString (v+5))) u ms /\
    lookup_var (STRING #"%" (toString (v+6))) u = SOME P /\
    ptr_covers G7 tn7 (STRING #"%" (toString (v+6))) u (32+ms) /\
    lookup_var (STRING #"%" (toString (v+7))) u = SOME 32w /\
    op_taint tn7 (Var (STRING #"%" (toString (v+7)))) = {} /\
    lookup_var (STRING #"%" (toString (v+8))) u = SOME (P+32w) /\
    ptr_covers G7 tn7 (STRING #"%" (toString (v+8))) u ms /\
    lookup_var (STRING #"%" (toString (v+9))) u = SOME (n2w L) /\
    op_taint tn7 (Var (STRING #"%" (toString (v+9)))) = {} /\
    mload (w2n Q) u = n2w L /\
    (!j. w2n Q <= j /\ j < w2n Q+32 ==> j NOTIN tn7.t_mem)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  qabbrev_tac `xs = TAKE 2 (revert_reason_suffix id v (Var b) (Var p) (Var q))` >>
  qabbrev_tac `ys = TAKE 5 (DROP 2 (revert_reason_suffix id v (Var b) (Var p) (Var q)))` >>
  `TAKE 7 (revert_reason_suffix id v (Var b) (Var p) (Var q)) = xs ++ ys` by
    simp[NoAsms, Abbr `xs`, Abbr `ys`, revert_reason_suffix_def] >>
  `?s2. run_inst_seq xs s = OK s2 /\ run_inst_seq ys s2 = OK u` by
    (Cases_on `run_inst_seq xs s`
     >- (drule run_inst_seq_append >> disch_then (qspec_then `ys` assume_tac) >>
         qexists_tac `v'` >> simp[NoAsms] >> metis_tac[]) >>
     qpat_x_assum `run_inst_seq (TAKE 7 _) _ = _` mp_tac >>
     asm_rewrite_tac[] >> simp[run_inst_seq_append_err]) >>
  `run_inst_seq (TAKE 2 (revert_reason_suffix id v (Var b) (Var p) (Var q))) s = OK s2` by
    metis_tac[] >>
  drule_all revert_reason_size_cell_checks >>
  disch_then (qspecl_then [`tn`, `fn`, `PG`, `G`, `D`] mp_tac) >>
  disch_then (qx_choose_then `g2` (qx_choose_then `tn2` (qx_choose_then `A` strip_assume_tac))) >>
  `c+32 < dimword(:256)` by
    (drule_all (Q.INST [`n` |-> `32`] alloca_bounds_site) >>
     simp[NoAsms]) >>
  qpat_x_assum `!a sz. FLOOKUP s.vs_allocas _ = _ ==> _` kall_tac >>
  qpat_x_assum `FLOOKUP s.vs_allocas _ = NONE ==> _` kall_tac >>
  suspend "after_cell"
QED

Resume revert_reason_seven_checks[after_cell]:
  `A = n2w c /\ mload (w2n Q) s2 = n2w L /\
   (!j. w2n Q <= j /\ j < w2n Q+32 ==> j NOTIN tn2.t_mem)` by
    (qpat_x_assum `!z head. _` (qspecl_then [`c`, `w2n Q`] mp_tac) >>
     simp[]) >>
  `lookup_var b s2 = SOME B /\ ptr_covers g2 tn2 b s2 (64+ms)` by
    (qpat_assum `!x C. _` (qspecl_then [`b`, `64+ms`] mp_tac) >> simp[]) >>
  `lookup_var p s2 = SOME P /\ ptr_covers g2 tn2 p s2 (32+ms)` by
    (qpat_assum `!x C. _` (qspecl_then [`p`, `32+ms`] mp_tac) >> simp[]) >>
  `lookup_var q s2 = SOME Q /\ ptr_covers g2 tn2 q s2 ms` by
    (qpat_assum `!x C. _` (qspecl_then [`q`, `ms`] mp_tac) >> simp[]) >>
  qpat_x_assum `!x C. _` kall_tac >>
  qpat_x_assum `!z head. _` kall_tac >>
  suspend "aliases"
QED

Resume revert_reason_seven_checks[aliases]:
  qabbrev_tac `s2c = s2 with vs_inst_idx := s.vs_inst_idx+2` >>
  qabbrev_tac `as3 = TAKE 3 ys` >>
  qabbrev_tac `as2 = DROP 3 ys` >>
  `ys = as3 ++ as2` by simp[NoAsms, Abbr `as3`, Abbr `as2`] >>
  `?s5. run_inst_seq as3 s2 = OK s5 /\ run_inst_seq as2 s5 = OK u` by
    (Cases_on `run_inst_seq as3 s2`
     >- (drule run_inst_seq_append >> disch_then (qspec_then `as2` assume_tac) >>
         qexists_tac `v'` >> simp[NoAsms] >> metis_tac[]) >>
     qpat_x_assum `run_inst_seq ys _ = _` mp_tac >>
     asm_rewrite_tac[] >> simp[run_inst_seq_append_err]) >>
  `EVERY (\i. ~is_terminator i.inst_opcode) as3` by
    simp[NoAsms, Abbr `as3`, Abbr `ys`, revert_reason_suffix_def,
      mk_inst_def, is_terminator_def] >>
  `run_inst_seq as3 s2c = OK (s5 with vs_inst_idx := s.vs_inst_idx+2)` by
    simp[Abbr `s2c`, run_inst_seq_inst_idx, exec_result_map_def] >>
  suspend "alias_post"
QED

Resume revert_reason_seven_checks[alias_post]:
  qabbrev_tac `aq = STRING #"%" (toString (v+5))` >>
  qabbrev_tac `ap = STRING #"%" (toString (v+6))` >>
  qabbrev_tac `dst = STRING #"%" (toString (v+7))` >>
  qabbrev_tac `cell = STRING #"%" (toString (v+4))` >>
  qabbrev_tac `s5c = s5 with vs_inst_idx := s.vs_inst_idx+2` >>
  `?g5 tn5.
    inst_seq_ptr D 0 ctx fn PG g2 tn2 as3 s2c g5 tn5 /\
    op_taint tn5 (Var dst) = {} /\ tn5.t_mem = tn2.t_mem /\
    lookup_var aq s5c = SOME Q /\ lookup_var ap s5c = SOME P /\
    lookup_var dst s5c = SOME (mload (w2n A) s2c) /\
    (!C. ptr_covers g2 tn2 q s2c C ==> ptr_covers g5 tn5 aq s5c C) /\
    (!C. ptr_covers g2 tn2 p s2c C ==> ptr_covers g5 tn5 ap s5c C) /\
    (!x C. x <> aq /\ x <> ap /\ x <> dst /\ ptr_covers g2 tn2 x s2c C ==>
       lookup_var x s5c = lookup_var x s2c /\ ptr_covers g5 tn5 x s5c C) /\
    (!a. mload a s5c = mload a s2c)` by
    (simp[NoAsms, Abbr `as3`, Abbr `ys`, revert_reason_suffix_def] >>
     simp[NoAsms, Abbr `aq`, Abbr `ap`, Abbr `dst`, Abbr `cell`] >>
     irule (SRULE [GSYM ADD_ASSOC] (Q.INST [`id` |-> `id+7`] alias_pair_load_checks)) >>
     `op_taint tn2 (Var p) = {} /\ op_taint tn2 (Var q) = {}` by
       fs[ptr_covers_def] >>
     `p <> STRING #"%" (toString (v+5))` by
       (qpat_x_assum `!k. 4 <= k /\ k <= 20 ==> _`
          (qspec_then `5` mp_tac) >> simp[]) >>
     fs[lookup_var_def] >>
     simp[Abbr `s2c`, lookup_var_def, ASCIInumbersTheory.toString_inj] >>
     qpat_x_assum `run_inst_seq _ (s2 with vs_inst_idx := _) = OK s5c` mp_tac >>
     simp[NoAsms, revert_reason_suffix_def]) >>
  suspend "alias_frames"
QED

Resume revert_reason_seven_checks[alias_frames]:
  `ptr_covers g5 tn5 aq s5c ms /\ ptr_covers g5 tn5 ap s5c (32+ms)` by
    (conj_tac
     >- (first_x_assum irule >> simp[Abbr `s2c`]) >>
     first_x_assum irule >> simp[Abbr `s2c`]) >>
  `lookup_var dst s5c = SOME 32w` by
    fs[Abbr `s2c`, mload_def] >>
  `(!x. x = b \/ x = p \/ x = q ==> x <> aq /\ x <> ap /\ x <> dst) /\
   cell <> aq /\ cell <> ap /\ cell <> dst` by
    (qpat_assum `!k. 4 <= k /\ k <= 20 ==> _` (qspec_then `5` assume_tac) >>
     qpat_assum `!k. 4 <= k /\ k <= 20 ==> _` (qspec_then `6` assume_tac) >>
     qpat_assum `!k. 4 <= k /\ k <= 20 ==> _` (qspec_then `7` assume_tac) >>
     fs[Abbr `aq`, Abbr `ap`, Abbr `dst`, Abbr `cell`,
        ASCIInumbersTheory.toString_inj] >> metis_tac[]) >>
  `lookup_var b s5c = SOME B /\ ptr_covers g5 tn5 b s5c (64+ms)` by
    (qpat_assum `!x C. _` (qspecl_then [`b`, `64+ms`] mp_tac) >>
     simp[Abbr `s2c`, lookup_var_def] >> fs[lookup_var_def]) >>
  `lookup_var p s5c = SOME P /\ ptr_covers g5 tn5 p s5c (32+ms)` by
    (qpat_assum `!x C. _` (qspecl_then [`p`, `32+ms`] mp_tac) >>
     simp[Abbr `s2c`, lookup_var_def] >> fs[lookup_var_def]) >>
  `lookup_var q s5c = SOME Q /\ ptr_covers g5 tn5 q s5c ms` by
    (qpat_assum `!x C. _` (qspecl_then [`q`, `ms`] mp_tac) >>
     simp[Abbr `s2c`, lookup_var_def] >> fs[lookup_var_def]) >>
  `lookup_var cell s5c = SOME A /\ ptr_covers g5 tn5 cell s5c 32` by
    (qpat_assum `!x C. _` (qspecl_then [`cell`, `32`] mp_tac) >>
     simp[Abbr `s2c`, lookup_var_def] >> fs[lookup_var_def]) >>
  suspend "last_pair"
QED

Resume revert_reason_seven_checks[last_pair]:
  qabbrev_tac `addr = STRING #"%" (toString (v+8))` >>
  qabbrev_tac `len = STRING #"%" (toString (v+9))` >>
  qabbrev_tac `s5d = s5 with vs_inst_idx := s.vs_inst_idx+5` >>
  qabbrev_tac `ud = u with vs_inst_idx := s.vs_inst_idx+5` >>
  `EVERY (\i. ~is_terminator i.inst_opcode) as2` by
    simp[NoAsms, Abbr `as2`, Abbr `ys`, revert_reason_suffix_def,
      mk_inst_def, is_terminator_def] >>
  `run_inst_seq as2 s5d = OK ud` by
    simp[Abbr `s5d`, Abbr `ud`, run_inst_seq_inst_idx, exec_result_map_def] >>
  `?g7 tn7.
    inst_seq_ptr D 0 ctx fn PG g5 tn5 as2 s5d g7 tn7 /\
    lookup_var addr ud = SOME (P+32w) /\ ptr_covers g7 tn7 addr ud ms /\
    lookup_var len ud = SOME (mload (w2n Q) s5d) /\
    op_taint tn7 (Var len) = {} /\ tn7.t_mem = tn5.t_mem /\
    (!a. mload a ud = mload a s5d) /\
    (!x. x <> addr /\ x <> len ==>
      lookup_var x ud = lookup_var x s5d /\
      op_taint tn7 (Var x) = op_taint tn5 (Var x) /\
      (!K. ptr_covers g5 tn5 x s5d K ==> ptr_covers g7 tn7 x ud K))` by
    (simp[NoAsms, Abbr `as2`, Abbr `ys`, revert_reason_suffix_def] >>
     simp[NoAsms, Abbr `addr`, Abbr `len`] >>
     irule (SRULE [GSYM ADD_ASSOC]
       (Q.INST [`id` |-> `id+10`, `n` |-> `32`] offset_add_clean_load_checks)) >>
     simp[Abbr `s5d`, Abbr `s5c`, lookup_var_def] >>
     conj_tac
     >- (qpat_x_assum `run_inst_seq _ (s5 with vs_inst_idx := _) = OK ud` mp_tac >>
         simp[NoAsms, revert_reason_suffix_def, Abbr `aq`, Abbr `dst`]) >>
     qpat_assum `lookup_var p (s5 with vs_inst_idx := _) = SOME P` mp_tac >>
     qpat_assum `lookup_var dst (s5 with vs_inst_idx := _) = SOME 32w` mp_tac >>
     qpat_assum `lookup_var aq (s5 with vs_inst_idx := _) = SOME Q` mp_tac >>
     qpat_assum `ptr_covers g5 tn5 p (s5 with vs_inst_idx := _) (32+ms)` mp_tac >>
     qpat_assum `ptr_covers g5 tn5 aq (s5 with vs_inst_idx := _) ms` mp_tac >>
     simp[NoAsms, lookup_var_def, ptr_covers_def] >>
     rpt strip_tac >> gvs[AllCaseEqs()] >> decide_tac) >>
  suspend "seven_frames"
QED


Resume revert_reason_seven_checks[seven_frames]:
  `inst_seq_ptr D 0 ctx fn PG g2 tn2 (as3 ++ as2) s2c g7 tn7` by
    (irule inst_seq_ptr_append_ok >> (conj_tac >- simp[]) >>
     qexistsl [`g5`, `s5c`, `tn5`] >>
     simp[Abbr `s5d`, Abbr `s5c`, Abbr `s2c`, Abbr `as3`, Abbr `ys`,
       revert_reason_suffix_def]) >>
  `inst_seq_ptr D 0 ctx fn PG G tn (xs ++ ys) s g7 tn7` by
    (irule inst_seq_ptr_append_ok >>
     (conj_tac >- simp[Abbr `xs`, revert_reason_suffix_def, mk_inst_def, is_terminator_def]) >>
     qexistsl [`g2`, `s2`, `tn2`] >>
     simp[Abbr `xs`, Abbr `s2c`, Abbr `ys`, revert_reason_suffix_def,
       mk_inst_def, is_terminator_def] >> fs[Abbr `ys`]) >>
  qexistsl [`g7`, `tn7`] >>
  simp[Abbr `addr`, Abbr `len`, GSYM lookup_var_def] >>
  suspend "endpoint_frames"
QED

Resume revert_reason_seven_checks[endpoint_frames]:
  `!x. x = b \/ x = p \/ x = q \/ x = cell \/ x = aq \/ x = ap \/ x = dst ==>
     x <> STRING #"%" (toString (v+8)) /\
     x <> STRING #"%" (toString (v+9))` by
    (qpat_assum `!k. 4 <= k /\ k <= 20 ==> _` (qspec_then `8` assume_tac) >>
     qpat_assum `!k. 4 <= k /\ k <= 20 ==> _` (qspec_then `9` assume_tac) >>
     simp[DISJ_IMP_THM, FORALL_AND_THM,
       Abbr `cell`, Abbr `aq`, Abbr `ap`, Abbr `dst`,
       ASCIInumbersTheory.toString_inj]) >>
  `!x. x = b \/ x = p \/ x = q \/ x = cell \/ x = aq \/ x = ap \/ x = dst ==>
     lookup_var x u = lookup_var x s5c /\
     op_taint tn7 (Var x) = op_taint tn5 (Var x) /\
     (!K. ptr_covers g5 tn5 x s5c K ==> ptr_covers g7 tn7 x u K)` by
    (rpt gen_tac >> strip_tac >>
     qpat_x_assum `!x. x <> _ /\ x <> _ ==> _` (qspec_then `x` mp_tac) >>
     simp[Abbr `ud`, Abbr `s5d`, Abbr `s5c`, lookup_var_def] >> metis_tac[]) >>
  suspend "frame_finish"
QED

Resume revert_reason_seven_checks[frame_finish]:
  qpat_assum `!x. x = b \/ _ ==> lookup_var _ _ = _ /\ _` (qspec_then `b` assume_tac) >>
  qpat_assum `!x. x = b \/ _ ==> lookup_var _ _ = _ /\ _` (qspec_then `p` assume_tac) >>
  qpat_assum `!x. x = b \/ _ ==> lookup_var _ _ = _ /\ _` (qspec_then `q` assume_tac) >>
  qpat_assum `!x. x = b \/ _ ==> lookup_var _ _ = _ /\ _` (qspec_then `cell` assume_tac) >>
  qpat_assum `!x. x = b \/ _ ==> lookup_var _ _ = _ /\ _` (qspec_then `aq` assume_tac) >>
  qpat_assum `!x. x = b \/ _ ==> lookup_var _ _ = _ /\ _` (qspec_then `ap` assume_tac) >>
  qpat_assum `!x. x = b \/ _ ==> lookup_var _ _ = _ /\ _` (qspec_then `dst` assume_tac) >>
  `c < dimword(:256)` by decide_tac >>
  qpat_assum `!a. mload a ud = _` (qspec_then `c` assume_tac) >>
  qpat_assum `!a. mload a ud = _` (qspec_then `w2n Q` assume_tac) >>
  qpat_assum `!a. mload a s5c = _` (qspec_then `c` assume_tac) >>
  qpat_assum `!a. mload a s5c = _` (qspec_then `w2n Q` assume_tac) >>
  fs[Abbr `ud`, Abbr `s5d`, Abbr `s5c`, Abbr `s2c`,
    lookup_var_def, mload_def, LESS_MOD] >>
  qpat_x_assum `inst_seq_ptr _ _ _ _ _ _ _ (xs ++ ys) _ _ _` mp_tac >>
  asm_rewrite_tac[APPEND_ASSOC]
QED

Finalise revert_reason_seven_checks
