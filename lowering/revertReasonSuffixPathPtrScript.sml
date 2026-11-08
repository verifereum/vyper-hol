(* Composition of the checked ABI suffix. Semantic observations use ordinary
   run endpoints; subsequent pointer checks use counted endpoint cursors. *)
Theory revertReasonSuffixPathPtr
Ancestors
  finalAbortSeqPtr revertReasonSuffixPtr revertReasonPrefixFramePtr fragGasSeqPtr
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
    (irule alloca_store_literal_taint_bound >>
     conj_tac >- simp[] >>
     goal_assum (drule_at Any) >> goal_assum (drule_at Any) >>
     goal_assum (drule_at Any) >> simp[]) >>
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
     mp_tac (Q.INST [`id` |-> `id+5`, `n` |-> `32`,
       `out` |-> `STRING #"%" (toString ((v:num)+4))`, `t` |-> `sa`,
       `c` |-> `z`] alloca_bounds_site) >>
     impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC) >>
     disch_then ACCEPT_TAC) >>
  mp_tac (Q.INST [`id` |-> `id+5`, `n` |-> `32`,
    `out` |-> `STRING #"%" (toString ((v:num)+4))`, `value` |-> `32w`,
    `s1` |-> `sa`] alloca_store_literal_checks) >>
  impl_tac
  >- (rpt conj_tac >| [first_assum ACCEPT_TAC, first_assum ACCEPT_TAC,
        DECIDE_TAC, first_assum ACCEPT_TAC, first_assum ACCEPT_TAC]) >>
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
    (simp[Abbr `i`, mk_inst_def] >> asm_simp_tac bool_ss [step_inst_base_opcode_eqs, instruction_accfupds, combinTheory.K_THM, opcode_case_def, venomInstTheory.instruction_accessors] >>
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
     simp[eval_operand_def, w2n_n2w, LESS_MOD] >>
     conj_tac >-
       (qpat_assum `w2n P + n + C < dimword(:256)` mp_tac >>
        simp[NoAsms, dimword_def] >> decide_tac) >> qexists_tac `n+C` >>
     conj_tac >- decide_tac >> conj_tac >- decide_tac >>
     first_assum ACCEPT_TAC) >>
  suspend "load"
QED

Resume offset_add_clean_load_checks[load]:
  `step_inst_base j s1 = OK (update_var len (mload (w2n Q) s1) s1)` by
    (simp[Abbr `j`, mk_inst_def] >> asm_simp_tac bool_ss [step_inst_base_opcode_eqs, instruction_accfupds, combinTheory.K_THM, opcode_case_def, venomInstTheory.instruction_accessors] >>
     simp[exec_read1_def, eval_operand_def]) >>
  `ptr_inst_ok D 0 0 ctx fn g1 t1 j s1` by
    (simp[Abbr `j`] >> irule ptr_inst_ok_mload >> simp[]) >>
  `t = update_var len (mload (w2n Q) s) (update_var addr (P+n2w n) s)` by
    (qpat_x_assum `run_inst_seq _ s = OK t` mp_tac >>
     simp[Once run_inst_seq_def] >>
     simp[NoAsms, run_inst_seq_def] >>
     simp[Abbr `j`, mk_inst_def] >> asm_simp_tac bool_ss [step_inst_base_opcode_eqs, instruction_accfupds, combinTheory.K_THM, opcode_case_def, venomInstTheory.instruction_accessors] >>
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
    (irule run_inst_seq_append_ok_split >> metis_tac[]) >>
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
    (irule run_inst_seq_append_ok_split >> metis_tac[]) >>
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
     >- (qpat_assum `w2n P + 32 + ms < dimword (:256)` mp_tac >>
         simp[NoAsms, dimword_def] >> decide_tac) >>
     conj_tac
     >- (qpat_x_assum `run_inst_seq _ (s5 with vs_inst_idx := _) = OK ud` mp_tac >>
         simp[NoAsms, revert_reason_suffix_def, Abbr `aq`, Abbr `dst`]) >>
     qpat_assum `lookup_var p (s5 with vs_inst_idx := _) = SOME P` mp_tac >>
     qpat_assum `lookup_var dst (s5 with vs_inst_idx := _) = SOME 32w` mp_tac >>
     qpat_assum `lookup_var aq (s5 with vs_inst_idx := _) = SOME Q` mp_tac >>
     qpat_assum `ptr_covers g5 tn5 p (s5 with vs_inst_idx := _) (32+ms)` mp_tac >>
     qpat_assum `ptr_covers g5 tn5 aq (s5 with vs_inst_idx := _) ms` mp_tac >>
     qpat_assum `32 + ceil32 L <= ms` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >>
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

Theorem revert_reason_suffix_checks:
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
  run_inst_seq (TAKE 22 (revert_reason_suffix id v (Var b) (Var p) (Var q))) s = OK t ==>
  ?Gf tnf. inst_seq_ptr D 0 ctx fn PG G tn
    (revert_reason_suffix id v (Var b) (Var p) (Var q)) s Gf tnf
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  qabbrev_tac `xs = TAKE 7 (revert_reason_suffix id v (Var b) (Var p) (Var q))` >>
  qabbrev_tac `ys = TAKE 15 (DROP 7 (revert_reason_suffix id v (Var b) (Var p) (Var q)))` >>
  `TAKE 22 (revert_reason_suffix id v (Var b) (Var p) (Var q)) = xs ++ ys` by
    simp[NoAsms, Abbr `xs`, Abbr `ys`, revert_reason_suffix_def] >>
  `?s7. run_inst_seq xs s = OK s7 /\ run_inst_seq ys s7 = OK t` by
    (irule run_inst_seq_append_ok_split >> metis_tac[]) >>
  `run_inst_seq (TAKE 7 (revert_reason_suffix id v (Var b) (Var p) (Var q))) s = OK s7` by
    metis_tac[] >>
  drule_all revert_reason_seven_checks >>
  disch_then (qspecl_then [`fn`, `PG`, `D`] mp_tac) >>
  disch_then (qx_choose_then `g7` (qx_choose_then `tn7` strip_assume_tac)) >>
  qpat_x_assum `!a sz. FLOOKUP s.vs_allocas _ = _ ==> _` kall_tac >>
  qpat_x_assum `FLOOKUP s.vs_allocas _ = NONE ==> _` kall_tac >>
  suspend "round"
QED

Resume revert_reason_suffix_checks[round]:
  qpat_x_assum `lookup_var b s = _` kall_tac >>
  qpat_x_assum `lookup_var p s = _` kall_tac >>
  qpat_x_assum `lookup_var q s = _` kall_tac >>
  qpat_x_assum `ptr_covers G tn b s _` kall_tac >>
  qpat_x_assum `ptr_covers G tn p s _` kall_tac >>
  qpat_x_assum `ptr_covers G tn q s _` kall_tac >>
  qpat_x_assum `mload _ s = _` kall_tac >>
  qpat_x_assum `!j. _ ==> j NOTIN tn.t_mem` kall_tac >>
  qabbrev_tac `rs = TAKE 2 ys` >>
  qabbrev_tac `zs = DROP 2 ys` >>
  `ys = rs ++ zs` by simp[NoAsms, Abbr `rs`, Abbr `zs`] >>
  `?s9. run_inst_seq rs s7 = OK s9 /\ run_inst_seq zs s9 = OK t` by
    (irule run_inst_seq_append_ok_split >> metis_tac[]) >>
  qabbrev_tac `s7c = s7 with vs_inst_idx := s.vs_inst_idx+7` >>
  qabbrev_tac `s9c = s9 with vs_inst_idx := s.vs_inst_idx+7` >>
  `EVERY (\i. ~is_terminator i.inst_opcode) rs` by
    simp[NoAsms, Abbr `rs`, Abbr `ys`, revert_reason_suffix_def,
      mk_inst_def, is_terminator_def] >>
  `run_inst_seq rs s7c = OK s9c` by
    simp[Abbr `s7c`, Abbr `s9c`, run_inst_seq_inst_idx, exec_result_map_def] >>
  suspend "round_post"
QED

Resume revert_reason_suffix_checks[round_post]:
  qabbrev_tac `tmp = STRING #"%" (toString (v+10))` >>
  qabbrev_tac `rnd = STRING #"%" (toString (v+11))` >>
  `?g9 tn9.
    inst_seq_ptr D 0 ctx fn PG g7 tn7 rs s7c g9 tn9 /\
    op_taint tn9 (Var rnd) = {} /\ tn9.t_mem = tn7.t_mem /\
    (!u. run_inst_seq rs s7c = OK u ==>
      lookup_var rnd u = SOME (n2w (contractABI$ceil32 L)) /\
      (!a. mload a u = mload a s7c) /\
      (!x. x <> tmp /\ x <> rnd ==>
        lookup_var x u = lookup_var x s7c /\
        op_taint tn9 (Var x) = op_taint tn7 (Var x) /\
        (!C. ptr_covers g7 tn7 x s7c C ==> ptr_covers g9 tn9 x u C)))` by
    (simp[NoAsms, Abbr `rs`, Abbr `ys`, revert_reason_suffix_def,
       Abbr `tmp`, Abbr `rnd`] >>
     irule (SRULE [GSYM ADD_ASSOC]
       (Q.INST [`id` |-> `id+12`] round_ceil32_checks)) >>
     fs[Abbr `s7c`, lookup_var_def]) >>
  first_x_assum (drule_then strip_assume_tac) >>
  suspend "round_frames"
QED

Resume revert_reason_suffix_checks[round_frames]:
  `!x. x = b \/ x = p \/ x = q \/
       (?k. 4 <= k /\ k <= 9 /\ x = STRING #"%" (toString (v+k))) ==>
     x <> tmp /\ x <> rnd` by
    (rpt gen_tac >> strip_tac >>
     fs[Abbr `tmp`, Abbr `rnd`, ASCIInumbersTheory.toString_inj] >>
     qpat_assum `!k. 4 <= k /\ k <= 20 ==> _` (qspec_then `10` assume_tac) >>
     qpat_assum `!k. 4 <= k /\ k <= 20 ==> _` (qspec_then `11` assume_tac) >>
     fs[]) >>
  `!x. x = b \/ x = p \/ x = q \/
       (?k. 4 <= k /\ k <= 9 /\ x = STRING #"%" (toString (v+k))) ==>
     lookup_var x s9 = lookup_var x s7 /\
     op_taint tn9 (Var x) = op_taint tn7 (Var x) /\
     (!C. ptr_covers g7 tn7 x s7 C ==> ptr_covers g9 tn9 x s9 C)` by
    (rpt gen_tac >> strip_tac >>
     qpat_x_assum `!x. x <> tmp /\ x <> rnd ==> _` (qspec_then `x` mp_tac) >>
     simp[Abbr `s9c`, Abbr `s7c`, lookup_var_def] >> metis_tac[]) >>
  qpat_x_assum `!x. x <> tmp /\ x <> rnd ==> _` kall_tac >>
  qpat_x_assum `!x. x = b \/ _ ==> x <> tmp /\ _` kall_tac >>
  suspend "padding_entry"
QED

Resume revert_reason_suffix_checks[padding_entry]:
  qabbrev_tac `pad = TAKE 4 zs` >>
  qabbrev_tac `rest = DROP 4 zs` >>
  `zs = pad ++ rest` by simp[NoAsms, Abbr `pad`, Abbr `rest`] >>
  `?s13. run_inst_seq pad s9 = OK s13 /\ run_inst_seq rest s13 = OK t` by
    (irule run_inst_seq_append_ok_split >> metis_tac[]) >>
  qabbrev_tac `s9d = s9 with vs_inst_idx := s.vs_inst_idx+9` >>
  `EVERY (\i. ~is_terminator i.inst_opcode) pad` by
    simp[NoAsms, Abbr `pad`, Abbr `zs`, Abbr `ys`, revert_reason_suffix_def,
      mk_inst_def, is_terminator_def] >>
  `run_inst_seq pad s9d = OK (s13 with vs_inst_idx := s.vs_inst_idx+9)` by
    simp[Abbr `s9d`, run_inst_seq_inst_idx, exec_result_map_def] >>
  suspend "padding_post"
QED

Resume revert_reason_suffix_checks[padding_post]:
  qabbrev_tac `endvar = STRING #"%" (toString (v+12))` >>
  qabbrev_tac `countvar = STRING #"%" (toString (v+13))` >>
  `!k. 4 <= k /\ k <= 9 ==>
     lookup_var (STRING #"%" (toString (v+k))) s9 =
       lookup_var (STRING #"%" (toString (v+k))) s7 /\
     op_taint tn9 (Var (STRING #"%" (toString (v+k)))) =
       op_taint tn7 (Var (STRING #"%" (toString (v+k)))) /\
     (!C. ptr_covers g7 tn7 (STRING #"%" (toString (v+k))) s7 C ==>
       ptr_covers g9 tn9 (STRING #"%" (toString (v+k))) s9 C)` by
    (gen_tac >> strip_tac >>
     qpat_assum `!x. x = b \/ _ ==> _`
       (qspec_then `STRING #"%" (toString (v+k))` mp_tac) >>
     impl_tac >- (disj2_tac >> disj2_tac >> disj2_tac >> qexists `k` >> simp[]) >>
     simp[]) >>
  qpat_assum `!k. 4 <= k /\ k <= 9 ==> _` (qspec_then `5` assume_tac) >>
  qpat_assum `!k. 4 <= k /\ k <= 9 ==> _` (qspec_then `8` assume_tac) >>
  qpat_assum `!k. 4 <= k /\ k <= 9 ==> _` (qspec_then `9` assume_tac) >>
  `L <= contractABI$ceil32 L` by simp[contractABITheory.le_ceil32] >>
  `?g13 tn13. inst_seq_ptr D 0 ctx fn PG g9 tn9 pad s9d g13 tn13 /\
    (!u. run_inst_seq pad s9d = OK u ==>
      (!x. x <> endvar /\ x <> countvar ==>
        lookup_var x u = lookup_var x s9d /\
        op_taint tn13 (Var x) = op_taint tn9 (Var x) /\
        (!C. ptr_covers g9 tn9 x s9d C ==> ptr_covers g13 tn13 x u C)))` by
    (simp[NoAsms, Abbr `pad`, Abbr `zs`, Abbr `ys`, revert_reason_suffix_def,
       Abbr `endvar`, Abbr `countvar`] >>
     irule (SRULE [GSYM ADD_ASSOC]
       (Q.INST [`id` |-> `id+14`, `capbytes` |-> `ms`,
          `R` |-> `contractABI$ceil32 L`, `a` |-> `P+32w`] zero_pad_copy_checks)) >>
     gnvs[Abbr `rnd`, ASCIInumbersTheory.toString_inj] >>
     qexistsl [`L`, `P`, `ms`] >>
     gnvs[Abbr `s9d`, Abbr `s9c`, lookup_var_def] >>
     `w2n (P+32w:bytes32) = w2n P+32` by
       (`w2n P+32 < dimword(:256)` by
          (simp[NoAsms, dimword_def] >> decide_tac) >>
        simp[wordsTheory.w2n_add_2, w2n_n2w, LESS_MOD]) >>
     qspec_then `L` assume_tac (GEN_ALL contractABITheory.le_ceil32) >>
     conj_tac >- decide_tac >>
     conj_tac >- (asm_rewrite_tac[] >> decide_tac) >>
     `ptr_covers g9 tn9 (STRING #"%" (toString (v+5))) s9 ms` by
       (qpat_x_assum `FLOOKUP s9.vs_vars (STRING #"%" (toString (v+5))) = SOME Q /\ _`
          strip_assume_tac >> first_x_assum irule >> simp[]) >>
     pop_assum mp_tac >> pure_rewrite_tac[ptr_covers_def] >>
     disch_then strip_assume_tac >> conj_tac >- fs[] >>
     qexistsl [`w`, `b'`, `sz'`] >> simp[] >> decide_tac) >>
  first_x_assum (drule_then strip_assume_tac) >>
  suspend "padding_frames"
QED

Resume revert_reason_suffix_checks[padding_frames]:
  `!x. x = b \/ x = p \/ x = q \/
       (?k. 4 <= k /\ k <= 9 /\ x = STRING #"%" (toString (v+k))) ==>
     x <> endvar /\ x <> countvar` by
    (rpt gen_tac >> strip_tac >>
     fs[Abbr `endvar`, Abbr `countvar`, ASCIInumbersTheory.toString_inj] >>
     qpat_assum `!k. 4 <= k /\ k <= 20 ==> _` (qspec_then `12` assume_tac) >>
     qpat_assum `!k. 4 <= k /\ k <= 20 ==> _` (qspec_then `13` assume_tac) >> fs[]) >>
  `!x. x = b \/ x = p \/ x = q \/
       (?k. 4 <= k /\ k <= 9 /\ x = STRING #"%" (toString (v+k))) ==>
     lookup_var x s13 = lookup_var x s7 /\
     op_taint tn13 (Var x) = op_taint tn7 (Var x) /\
     (!C. ptr_covers g7 tn7 x s7 C ==> ptr_covers g13 tn13 x s13 C)` by
    (gen_tac >> disch_tac >>
     qpat_assum `!x. x = b \/ _ ==> lookup_var _ s9 = _ /\ _`
       (qspec_then `x` mp_tac) >>
     impl_tac >- asm_rewrite_tac[] >> disch_then strip_assume_tac >>
     qpat_assum `!x. x <> endvar /\ x <> countvar ==> _` (qspec_then `x` mp_tac) >>
     impl_tac >- metis_tac[] >>
     simp[Abbr `s9d`, lookup_var_def] >>
     fs[lookup_var_def] >> metis_tac[]) >>
  qpat_x_assum `!x. x <> endvar /\ x <> countvar ==> _` kall_tac >>
  qpat_x_assum `!x. x = b \/ _ ==> x <> endvar /\ _` kall_tac >>
  suspend "second_round"
QED

Resume revert_reason_suffix_checks[second_round]:
  qabbrev_tac `rs2 = TAKE 2 rest` >>
  qabbrev_tac `rest2 = DROP 2 rest` >>
  `rest = rs2 ++ rest2` by simp[NoAsms, Abbr `rs2`, Abbr `rest2`] >>
  `?s15. run_inst_seq rs2 s13 = OK s15 /\ run_inst_seq rest2 s15 = OK t` by
    (irule run_inst_seq_append_ok_split >> metis_tac[]) >>
  qabbrev_tac `s13c = s13 with vs_inst_idx := s.vs_inst_idx+13` >>
  `EVERY (\i. ~is_terminator i.inst_opcode) rs2` by
    simp[NoAsms, Abbr `rs2`, Abbr `rest`, Abbr `zs`, Abbr `ys`,
      revert_reason_suffix_def, mk_inst_def, is_terminator_def] >>
  `run_inst_seq rs2 s13c = OK (s15 with vs_inst_idx := s.vs_inst_idx+13)` by
    simp[Abbr `s13c`, run_inst_seq_inst_idx, exec_result_map_def] >>
  suspend "second_round_post"
QED

Resume revert_reason_suffix_checks[second_round_post]:
  qabbrev_tac `tmp2 = STRING #"%" (toString (v+14))` >>
  qabbrev_tac `rnd2 = STRING #"%" (toString (v+15))` >>
  qpat_assum `!x. x = b \/ _ ==> lookup_var _ s13 = _ /\ _`
    (qspec_then `STRING #"%" (toString (v+9))` mp_tac) >>
  impl_tac >- (rpt disj2_tac >> qexists `9` >> simp[]) >>
  disch_then strip_assume_tac >>
  `?g15 tn15.
    inst_seq_ptr D 0 ctx fn PG g13 tn13 rs2 s13c g15 tn15 /\
    op_taint tn15 (Var rnd2) = {} /\ tn15.t_mem = tn13.t_mem /\
    (!u. run_inst_seq rs2 s13c = OK u ==>
      lookup_var rnd2 u = SOME (n2w (contractABI$ceil32 L)) /\
      (!a. mload a u = mload a s13c) /\
      (!x. x <> tmp2 /\ x <> rnd2 ==>
        lookup_var x u = lookup_var x s13c /\
        op_taint tn15 (Var x) = op_taint tn13 (Var x) /\
        (!C. ptr_covers g13 tn13 x s13c C ==> ptr_covers g15 tn15 x u C)))` by
    (simp[NoAsms, Abbr `rs2`, Abbr `rest`, Abbr `zs`, Abbr `ys`,
       revert_reason_suffix_def, Abbr `tmp2`, Abbr `rnd2`] >>
     irule (SRULE [GSYM ADD_ASSOC]
       (Q.INST [`id` |-> `id+18`] round_ceil32_checks)) >>
     fs[Abbr `s13c`, lookup_var_def]) >>
  first_x_assum (drule_then strip_assume_tac) >>
  suspend "second_round_frames"
QED

Resume revert_reason_suffix_checks[second_round_frames]:
  `!x. x = b \/ x = p \/ x = q \/
       (?k. 4 <= k /\ k <= 9 /\ x = STRING #"%" (toString (v+k))) ==>
     x <> tmp2 /\ x <> rnd2` by
    (rpt gen_tac >> strip_tac >>
     fs[Abbr `tmp2`, Abbr `rnd2`, ASCIInumbersTheory.toString_inj] >>
     qpat_assum `!k. 4 <= k /\ k <= 20 ==> _` (qspec_then `14` assume_tac) >>
     qpat_assum `!k. 4 <= k /\ k <= 20 ==> _` (qspec_then `15` assume_tac) >> fs[]) >>
  `!x. x = b \/ x = p \/ x = q \/
       (?k. 4 <= k /\ k <= 9 /\ x = STRING #"%" (toString (v+k))) ==>
     lookup_var x s15 = lookup_var x s7 /\
     op_taint tn15 (Var x) = op_taint tn7 (Var x) /\
     (!C. ptr_covers g7 tn7 x s7 C ==> ptr_covers g15 tn15 x s15 C)` by
    (gen_tac >> disch_tac >>
     qpat_assum `!x. x = b \/ _ ==> lookup_var _ s13 = _ /\ _`
       (qspec_then `x` mp_tac) >>
     impl_tac >- asm_rewrite_tac[] >> disch_then strip_assume_tac >>
     qpat_assum `!x. x <> tmp2 /\ x <> rnd2 ==> _` (qspec_then `x` mp_tac) >>
     impl_tac >- metis_tac[] >>
     simp[Abbr `s13c`, lookup_var_def] >> fs[lookup_var_def] >> metis_tac[]) >>
  qpat_x_assum `!x. x <> tmp2 /\ x <> rnd2 ==> _` kall_tac >>
  qpat_x_assum `!x. x = b \/ _ ==> x <> tmp2 /\ _` kall_tac >>
  suspend "size_add"
QED

Resume revert_reason_suffix_checks[size_add]:
  qabbrev_tac `sizeadd = TAKE 1 rest2` >>
  qabbrev_tac `rest3 = DROP 1 rest2` >>
  `rest2 = sizeadd ++ rest3` by simp[NoAsms, Abbr `sizeadd`, Abbr `rest3`] >>
  `?s16. run_inst_seq sizeadd s15 = OK s16 /\ run_inst_seq rest3 s16 = OK t` by
    (irule run_inst_seq_append_ok_split >> metis_tac[]) >>
  qabbrev_tac `s15c = s15 with vs_inst_idx := s.vs_inst_idx+15` >>
  `EVERY (\i. ~is_terminator i.inst_opcode) sizeadd` by
    simp[NoAsms, Abbr `sizeadd`, Abbr `rest2`, Abbr `rest`, Abbr `zs`, Abbr `ys`,
      revert_reason_suffix_def, mk_inst_def, is_terminator_def] >>
  `run_inst_seq sizeadd s15c = OK (s16 with vs_inst_idx := s.vs_inst_idx+15)` by
    simp[Abbr `s15c`, run_inst_seq_inst_idx, exec_result_map_def] >>
  qabbrev_tac `szvar = STRING #"%" (toString (v+16))` >>
  `?g16 tn16. inst_seq_ptr D 0 ctx fn PG g15 tn15 sizeadd s15c g16 tn16 /\
    op_taint tn16 (Var szvar) = {} /\
    (!u. run_inst_seq sizeadd s15c = OK u ==>
      lookup_var szvar u = SOME (32w+n2w (contractABI$ceil32 L)) /\
      (!x. x <> szvar ==>
        lookup_var x u = lookup_var x s15c /\
        op_taint tn16 (Var x) = op_taint tn15 (Var x) /\
        (!C. ptr_covers g15 tn15 x s15c C ==> ptr_covers g16 tn16 x u C)))` by
    (simp[NoAsms, Abbr `sizeadd`, Abbr `rest2`, Abbr `rest`, Abbr `zs`, Abbr `ys`,
       revert_reason_suffix_def, Abbr `szvar`] >>
     irule (ONCE_REWRITE_RULE [wordsTheory.WORD_ADD_COMM]
       (Q.INST [`a` |-> `32w:bytes32`, `b` |-> `n2w (contractABI$ceil32 L):bytes32`] clean_add_checks)) >>
     fs[Abbr `s15c`, Abbr `rnd2`, lookup_var_def, eval_operand_def, op_taint_def]) >>
  first_x_assum (drule_then strip_assume_tac) >>
  suspend "size_add_frames"
QED

Resume revert_reason_suffix_checks[size_add_frames]:
  `!x. x = b \/ x = p \/ x = q \/
       (?k. 4 <= k /\ k <= 9 /\ x = STRING #"%" (toString (v+k))) ==>
     x <> szvar` by
    (rpt gen_tac >> strip_tac >>
     fs[Abbr `szvar`, ASCIInumbersTheory.toString_inj] >>
     qpat_assum `!k. 4 <= k /\ k <= 20 ==> _` (qspec_then `16` assume_tac) >> fs[]) >>
  `!x. x = b \/ x = p \/ x = q \/
       (?k. 4 <= k /\ k <= 9 /\ x = STRING #"%" (toString (v+k))) ==>
     lookup_var x s16 = lookup_var x s7 /\
     op_taint tn16 (Var x) = op_taint tn7 (Var x) /\
     (!C. ptr_covers g7 tn7 x s7 C ==> ptr_covers g16 tn16 x s16 C)` by
    (gen_tac >> disch_tac >>
     qpat_assum `!x. x = b \/ _ ==> lookup_var _ s15 = _ /\ _`
       (qspec_then `x` mp_tac) >>
     impl_tac >- asm_rewrite_tac[] >> disch_then strip_assume_tac >>
     qpat_assum `!x. x <> szvar ==> _` (qspec_then `x` mp_tac) >>
     impl_tac >- metis_tac[] >>
     simp[Abbr `s15c`, lookup_var_def] >> fs[lookup_var_def] >> metis_tac[]) >>
  qpat_x_assum `!x. x <> szvar ==> _` kall_tac >>
  qpat_x_assum `!x. x = b \/ _ ==> x <> szvar` kall_tac >>
  suspend "offset_store"
QED

Resume revert_reason_suffix_checks[offset_store]:
  qabbrev_tac `offstore = TAKE 1 rest3` >>
  qabbrev_tac `rest4 = DROP 1 rest3` >>
  `rest3 = offstore ++ rest4` by simp[NoAsms, Abbr `offstore`, Abbr `rest4`] >>
  `?s17. run_inst_seq offstore s16 = OK s17 /\ run_inst_seq rest4 s17 = OK t` by
    (irule run_inst_seq_append_ok_split >> metis_tac[]) >>
  qabbrev_tac `s16c = s16 with vs_inst_idx := s.vs_inst_idx+16` >>
  `EVERY (\i. ~is_terminator i.inst_opcode) offstore` by
    simp[NoAsms, Abbr `offstore`, Abbr `rest3`, Abbr `rest2`, Abbr `rest`,
      Abbr `zs`, Abbr `ys`, revert_reason_suffix_def, mk_inst_def, is_terminator_def] >>
  `run_inst_seq offstore s16c = OK (s17 with vs_inst_idx := s.vs_inst_idx+16)` by
    simp[Abbr `s16c`, run_inst_seq_inst_idx, exec_result_map_def] >>
  qpat_assum `!x. x = b \/ _ ==> lookup_var _ s16 = _ /\ _`
    (qspec_then `STRING #"%" (toString (v+6))` mp_tac) >>
  impl_tac >- (rpt disj2_tac >> qexists `6` >> simp[]) >>
  disch_then strip_assume_tac >>
  qpat_assum `!x. x = b \/ _ ==> lookup_var _ s16 = _ /\ _`
    (qspec_then `STRING #"%" (toString (v+7))` mp_tac) >>
  impl_tac >- (rpt disj2_tac >> qexists `7` >> simp[]) >>
  disch_then strip_assume_tac >>
  suspend "offset_store_post"
QED

Resume revert_reason_suffix_checks[offset_store_post]:
  qabbrev_tac `ap = STRING #"%" (toString (v+6))` >>
  qabbrev_tac `offset = STRING #"%" (toString (v+7))` >>
  `?g17 tn17. inst_seq_ptr D 0 ctx fn PG g16 tn16 offstore s16c g17 tn17 /\
    (!i. w2n P <= i /\ i < w2n P+32 ==> i NOTIN tn17.t_mem) /\
    tn17.t_mem SUBSET tn16.t_mem /\
    (!x C. ptr_covers g16 tn16 x s16c C ==>
      ptr_covers g17 tn17 x (mstore (w2n P) 32w s16c) C) /\
    (!u. run_inst_seq offstore s16c = OK u ==>
      (!x. lookup_var x u = lookup_var x s16c /\
        op_taint tn17 (Var x) = op_taint tn16 (Var x) /\
        (!C. ptr_covers g16 tn16 x s16c C ==> ptr_covers g17 tn17 x u C)))` by
    (simp[NoAsms, Abbr `offstore`, Abbr `rest3`, Abbr `rest2`, Abbr `rest`,
       Abbr `zs`, Abbr `ys`, revert_reason_suffix_def] >>
     irule mstore_clean_checks >>
     rule_assum_tac (PURE_REWRITE_RULE [lookup_var_def]) >>
     simp[Abbr `s16c`, lookup_var_def, eval_operand_def] >>
     first_x_assum irule >>
     qpat_x_assum `ptr_covers g7 tn7 ap s7 (32+ms)` mp_tac >>
     pure_rewrite_tac[ptr_covers_def] >> disch_then strip_assume_tac >>
     conj_tac >- simp[] >> qexistsl [`w`, `b'`, `sz'`] >> simp[] >> decide_tac) >>
  first_x_assum (drule_then strip_assume_tac) >>
  suspend "offset_store_frames"
QED

Resume revert_reason_suffix_checks[offset_store_frames]:
  `!x. lookup_var x s17 = lookup_var x s16 /\
       op_taint tn17 (Var x) = op_taint tn16 (Var x) /\
       (!C. ptr_covers g16 tn16 x s16 C ==> ptr_covers g17 tn17 x s17 C)` by
    (gen_tac >> qpat_x_assum `!x. lookup_var _ (s17 with vs_inst_idx := _) = _ /\ _`
       (qspec_then `x` mp_tac) >>
     simp[Abbr `s16c`, lookup_var_def]) >>
  qpat_x_assum `!x. lookup_var _ (s17 with vs_inst_idx := _) = _ /\ _` kall_tac >>
  qpat_assum `!x. lookup_var _ s17 = _ /\ _` (qspec_then `szvar` strip_assume_tac) >>
  qpat_assum `!x. lookup_var _ s17 = _ /\ _` (qspec_then `offset` strip_assume_tac) >>
  `lookup_var szvar s17 = SOME (n2w (32+contractABI$ceil32 L)) /\
    op_taint tn17 (Var szvar) = {} /\
    lookup_var offset s17 = SOME 32w /\ op_taint tn17 (Var offset) = {}` by
    fs[lookup_var_def, GSYM word_add_n2w] >>
  suspend "totvar_add"
QED

Resume revert_reason_suffix_checks[totvar_add]:
  qabbrev_tac `totvaradd = TAKE 1 rest4` >>
  qabbrev_tac `rest5 = DROP 1 rest4` >>
  `rest4 = totvaradd ++ rest5` by simp[NoAsms, Abbr `totvaradd`, Abbr `rest5`] >>
  `?s18. run_inst_seq totvaradd s17 = OK s18 /\ run_inst_seq rest5 s18 = OK t` by
    (irule run_inst_seq_append_ok_split >> metis_tac[]) >>
  qabbrev_tac `s17c = s17 with vs_inst_idx := s.vs_inst_idx+17` >>
  `EVERY (\i. ~is_terminator i.inst_opcode) totvaradd` by
    simp[NoAsms, Abbr `totvaradd`, Abbr `rest4`, Abbr `rest3`, Abbr `rest2`,
      Abbr `rest`, Abbr `zs`, Abbr `ys`, revert_reason_suffix_def,
      mk_inst_def, is_terminator_def] >>
  `run_inst_seq totvaradd s17c = OK (s18 with vs_inst_idx := s.vs_inst_idx+17)` by
    simp[Abbr `s17c`, run_inst_seq_inst_idx, exec_result_map_def] >>
  suspend "totvar_add_post"
QED

Resume revert_reason_suffix_checks[totvar_add_post]:
  qabbrev_tac `totvar = STRING #"%" (toString (v+17))` >>
  `?g18 tn18. inst_seq_ptr D 0 ctx fn PG g17 tn17 totvaradd s17c g18 tn18 /\
    op_taint tn18 (Var totvar) = {} /\
    (!u. run_inst_seq totvaradd s17c = OK u ==>
      lookup_var totvar u = SOME (32w+n2w (32+contractABI$ceil32 L)) /\
      (!x. x <> totvar ==>
        lookup_var x u = lookup_var x s17c /\
        op_taint tn18 (Var x) = op_taint tn17 (Var x) /\
        (!C. ptr_covers g17 tn17 x s17c C ==> ptr_covers g18 tn18 x u C)))` by
    (simp[NoAsms, Abbr `totvaradd`, Abbr `rest4`, Abbr `rest3`, Abbr `rest2`,
       Abbr `rest`, Abbr `zs`, Abbr `ys`, revert_reason_suffix_def, Abbr `totvar`] >>
     irule (ONCE_REWRITE_RULE [wordsTheory.WORD_ADD_COMM]
       (Q.INST [`a` |-> `32w:bytes32`, `b` |-> `n2w (contractABI$ceil32 L+32):bytes32`] clean_add_checks)) >>
     fs[Abbr `s17c`, Abbr `szvar`, Abbr `offset`, lookup_var_def, eval_operand_def]) >>
  first_x_assum (drule_then strip_assume_tac) >>
  `lookup_var totvar s18 = SOME (n2w (64+contractABI$ceil32 L))` by
    (qpat_assum `lookup_var totvar (s18 with vs_inst_idx := _) = SOME _` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >>
     simp[lookup_var_def, GSYM word_add_n2w, GSYM ADD_ASSOC] >>
     wordsLib.WORD_DECIDE_TAC) >>
  suspend "cell_update"
QED

Resume revert_reason_suffix_checks[cell_update]:
  qabbrev_tac `cell = STRING #"%" (toString (v+4))` >>
  qabbrev_tac `loaded = STRING #"%" (toString (v+18))` >>
  `cell <> totvar` by simp[Abbr `cell`, Abbr `totvar`, ASCIInumbersTheory.toString_inj] >>
  qpat_assum `!x. x = b \/ _ ==> lookup_var _ s16 = _ /\ _`
    (qspec_then `cell` mp_tac) >>
  impl_tac >- (rpt disj2_tac >> qexists `4` >> simp[Abbr `cell`]) >>
  disch_then strip_assume_tac >>
  qpat_assum `!x. lookup_var _ s17 = _ /\ _` (qspec_then `cell` strip_assume_tac) >>
  qpat_assum `!x. x <> totvar ==> _` (qspec_then `cell` mp_tac) >>
  simp[NoAsms, Abbr `s17c`, lookup_var_def] >> strip_tac >>
  `lookup_var cell s18 = SOME (n2w c) /\ ptr_covers g18 tn18 cell s18 32` by
    (fs[lookup_var_def] >> first_x_assum irule >> first_x_assum irule >>
     first_x_assum irule >> simp[]) >>
  suspend "cell_run"
QED

Resume revert_reason_suffix_checks[cell_run]:
  qabbrev_tac `cellops = TAKE 2 rest5` >>
  qabbrev_tac `tailops = DROP 2 rest5` >>
  `rest5 = cellops ++ tailops` by simp[NoAsms, Abbr `cellops`, Abbr `tailops`] >>
  `?s20. run_inst_seq cellops s18 = OK s20 /\ run_inst_seq tailops s20 = OK t` by
    (irule run_inst_seq_append_ok_split >> metis_tac[]) >>
  qabbrev_tac `s18c = s18 with vs_inst_idx := s.vs_inst_idx+18` >>
  `EVERY (\i. ~is_terminator i.inst_opcode) cellops` by
    simp[NoAsms, Abbr `cellops`, Abbr `rest5`, Abbr `rest4`, Abbr `rest3`,
      Abbr `rest2`, Abbr `rest`, Abbr `zs`, Abbr `ys`, revert_reason_suffix_def,
      mk_inst_def, is_terminator_def] >>
  `run_inst_seq cellops s18c = OK (s20 with vs_inst_idx := s.vs_inst_idx+18)` by
    simp[Abbr `s18c`, run_inst_seq_inst_idx, exec_result_map_def] >>
  `?g20 tn20. inst_seq_ptr D 0 ctx fn PG g18 tn18 cellops s18c g20 tn20 /\
    op_taint tn20 (Var loaded) = {} /\
    (!u. run_inst_seq cellops s18c = OK u ==>
      lookup_var loaded u = SOME (n2w (64+contractABI$ceil32 L)) /\
      (!x. x <> loaded ==>
        lookup_var x u = lookup_var x s18c /\
        op_taint tn20 (Var x) = op_taint tn18 (Var x) /\
        (!C. ptr_covers g18 tn18 x s18c C ==> ptr_covers g20 tn20 x u C)))` by
    (simp[NoAsms, Abbr `cellops`, Abbr `rest5`, Abbr `rest4`, Abbr `rest3`,
       Abbr `rest2`, Abbr `rest`, Abbr `zs`, Abbr `ys`, revert_reason_suffix_def,
       Abbr `cell`, Abbr `loaded`] >>
     irule (SRULE [GSYM ADD_ASSOC]
       (Q.INST [`id` |-> `id+23`] store_load_clean_checks)) >>
     simp[NoAsms, Abbr `s18c`, GSYM ADD_COMM] >>
     qpat_assum `lookup_var totvar s18 = SOME _` mp_tac >>
     qpat_assum `op_taint tn18 (Var totvar) = {}` mp_tac >>
     qpat_assum `lookup_var _ s18 = SOME (n2w c)` mp_tac >>
     qpat_assum `ptr_covers g18 tn18 _ s18 32` mp_tac >>
     qpat_assum `~ctx_has_dalloca ctx` mp_tac >>
     simp[NoAsms, Abbr `totvar`] >>
     POP_ASSUM_LIST (K ALL_TAC) >>
     simp[eval_operand_def, lookup_var_def] >> metis_tac[]) >>
  first_x_assum (drule_then strip_assume_tac) >>
  suspend "tail_checks"
QED

Resume revert_reason_suffix_checks[tail_checks]:
  `b <> totvar /\ b <> loaded` by
    (qpat_assum `!k. 4 <= k /\ k <= 20 ==> _` (qspec_then `17` assume_tac) >>
     qpat_assum `!k. 4 <= k /\ k <= 20 ==> _` (qspec_then `18` assume_tac) >>
     fs[Abbr `totvar`, Abbr `loaded`]) >>
  qpat_assum `!x. x = b \/ _ ==> lookup_var _ s16 = _ /\ _`
    (qspec_then `b` mp_tac) >>
  impl_tac >- simp[] >> disch_then strip_assume_tac >>
  qpat_assum `!x. lookup_var _ s17 = _ /\ _` (qspec_then `b` strip_assume_tac) >>
  qpat_assum `!x. x <> totvar ==> _` (qspec_then `b` mp_tac) >>
  simp[NoAsms, lookup_var_def] >> strip_tac >>
  qpat_assum `!x. x <> loaded ==> _` (qspec_then `b` mp_tac) >>
  simp[NoAsms, Abbr `s18c`, lookup_var_def] >> strip_tac >>
  `lookup_var b s20 = SOME B /\ ptr_covers g20 tn20 b s20 (64+ms)` by
    (fs[lookup_var_def] >> first_x_assum irule >> first_x_assum irule >>
     first_x_assum irule >> first_x_assum irule >> simp[]) >>
  suspend "tail_post"
QED

Resume revert_reason_suffix_checks[tail_post]:
  qabbrev_tac `s20c = s20 with vs_inst_idx := s.vs_inst_idx+20` >>
  `?gf tf. inst_seq_ptr D 0 ctx fn PG g20 tn20
    (DROP 20 (revert_reason_suffix id v (Var b) (Var p) (Var q))) s20c gf tf` by
    (simp[NoAsms, revert_reason_suffix_def] >>
     irule (SRULE [GSYM ADD_ASSOC]
       (Q.INST [`id` |-> `id+25`, `capbytes` |-> `64+ms`,
         `k` |-> `64+contractABI$ceil32 L`] revert_abi_tail_checks)) >>
     simp[Abbr `s20c`, Abbr `loaded`, lookup_var_def] >>
     conj_tac
     >- (qexists `B` >> fs[lookup_var_def] >> decide_tac) >>
     qexistsl [`L`, `ms`] >>
     fs[lookup_var_def] >> decide_tac) >>
  suspend "compose"
QED

Resume revert_reason_suffix_checks[compose]:
  `revert_reason_suffix id v (Var b) (Var p) (Var q) =
    xs ++ (rs ++ (pad ++ (rs2 ++ (sizeadd ++ (offstore ++
      (totvaradd ++ (cellops ++ DROP 20 (revert_reason_suffix id v (Var b) (Var p) (Var q)))))))))` by
    simp[NoAsms, Abbr `xs`, Abbr `rs`, Abbr `pad`, Abbr `rs2`, Abbr `sizeadd`,
      Abbr `offstore`, Abbr `totvaradd`, Abbr `cellops`, Abbr `rest5`, Abbr `rest4`,
      Abbr `rest3`, Abbr `rest2`, Abbr `rest`, Abbr `zs`, Abbr `ys`, revert_reason_suffix_def] >>
  qexistsl [`gf`, `tf`] >> pop_assum SUBST1_TAC >>
  irule inst_seq_ptr_append_ok >>
  (conj_tac >- simp[Abbr `xs`, revert_reason_suffix_def, mk_inst_def, is_terminator_def]) >>
  qexistsl [`g7`, `s7`, `tn7`] >>
  simp[Abbr `xs`, revert_reason_suffix_def, GSYM lookup_var_def] >>
  suspend "compose_round"
QED

Resume revert_reason_suffix_checks[compose_round]:
  pure_rewrite_tac[GSYM APPEND_ASSOC] >>
  irule inst_seq_ptr_append_ok >> (conj_tac >- simp[]) >>
  qexistsl [`g9`, `s9c`, `tn9`] >> simp[] >>
  simp[Abbr `rs`, Abbr `ys`, revert_reason_suffix_def, Abbr `s9c`, Abbr `s7c`] >>
  suspend "compose_padding"
QED

Resume revert_reason_suffix_checks[compose_padding]:
  pure_rewrite_tac[GSYM APPEND_ASSOC] >>
  irule inst_seq_ptr_append_ok >> (conj_tac >- simp[]) >>
  qexistsl [`g13`, `s13 with vs_inst_idx := s.vs_inst_idx+9`, `tn13`] >>
  simp[Abbr `s9d`] >>
  simp[Abbr `pad`, Abbr `zs`, revert_reason_suffix_def] >>
  suspend "compose_second_round"
QED

Resume revert_reason_suffix_checks[compose_second_round]:
  pure_rewrite_tac[GSYM APPEND_ASSOC] >>
  irule inst_seq_ptr_append_ok >> (conj_tac >- simp[]) >>
  qexistsl [`g15`, `s15 with vs_inst_idx := s.vs_inst_idx+13`, `tn15`] >>
  simp[Abbr `s13c`] >>
  simp[Abbr `rs2`, Abbr `rest`, revert_reason_suffix_def] >>
  suspend "compose_size"
QED

Resume revert_reason_suffix_checks[compose_size]:
  pure_rewrite_tac[GSYM APPEND_ASSOC] >>
  irule inst_seq_ptr_append_ok >> (conj_tac >- simp[]) >>
  qexistsl [`g16`, `s16 with vs_inst_idx := s.vs_inst_idx+15`, `tn16`] >>
  simp[Abbr `s15c`] >>
  simp[Abbr `sizeadd`, Abbr `rest2`, revert_reason_suffix_def] >>
  suspend "compose_store"
QED

Resume revert_reason_suffix_checks[compose_store]:
  pure_rewrite_tac[GSYM APPEND_ASSOC] >>
  irule inst_seq_ptr_append_ok >> (conj_tac >- simp[]) >>
  qexistsl [`g17`, `s17 with vs_inst_idx := s.vs_inst_idx+16`, `tn17`] >>
  simp[Abbr `s16c`] >>
  simp[Abbr `offstore`, Abbr `rest3`, revert_reason_suffix_def] >>
  suspend "compose_total"
QED

Resume revert_reason_suffix_checks[compose_total]:
  pure_rewrite_tac[GSYM APPEND_ASSOC] >>
  irule inst_seq_ptr_append_ok >> (conj_tac >- simp[]) >>
  qexistsl [`g18`, `s18 with vs_inst_idx := s.vs_inst_idx+17`, `tn18`] >>
  simp[] >>
  simp[Abbr `totvaradd`, Abbr `rest4`, revert_reason_suffix_def] >>
  suspend "compose_cell"
QED

Resume revert_reason_suffix_checks[compose_cell]:
  pure_rewrite_tac[GSYM APPEND_ASSOC] >>
  irule inst_seq_ptr_append_ok >> (conj_tac >- simp[]) >>
  qexistsl [`g20`, `s20 with vs_inst_idx := s.vs_inst_idx+18`, `tn20`] >>
  simp[] >>
  simp[Abbr `cellops`, Abbr `rest5`, revert_reason_suffix_def, Abbr `s20c`] >>
  qpat_assum `inst_seq_ptr _ _ _ _ _ g20 tn20 (DROP 20 _) _ gf tf` mp_tac >>
  simp[NoAsms, revert_reason_suffix_def, Abbr `loaded`]
QED

Finalise revert_reason_suffix_checks

Theorem revert_reason_suffix_path_ptr:
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
  run_inst_seq (TAKE 22 (revert_reason_suffix id v (Var b) (Var p) (Var q))) s = OK t /\
  ~s.vs_halted /\ lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  isPREFIX (revert_reason_suffix id v (Var b) (Var p) (Var q))
    (DROP s.vs_inst_idx bb.bb_instructions) /\
  run_inst_seq (revert_reason_suffix id v (Var b) (Var p) (Var q)) s = Abort a z ==>
  ?Gf tnf j. gas_path_ptr D 0 ctx fn PG G tn s 0 Gf tnf
    (Abort a (z with vs_inst_idx := j))
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all revert_reason_suffix_checks >>
  disch_then (qspecl_then [`fn`, `PG`, `D`] strip_assume_tac) >>
  qabbrev_tac `xs = TAKE 22 (revert_reason_suffix id v (Var b) (Var p) (Var q))` >>
  qabbrev_tac `i = mk_inst (id+27) REVERT
    [Var (STRING #"%" (toString (v+19))); Var (STRING #"%" (toString (v+20)))] []` >>
  `xs ++ [i] = revert_reason_suffix id v (Var b) (Var p) (Var q)` by
    simp[NoAsms, Abbr `xs`, Abbr `i`, revert_reason_suffix_def] >>
  `!j opc ops outs. (mk_inst j opc ops outs).inst_opcode = opc` by
    simp[mk_inst_def] >>
  `MAP (\h. h.inst_opcode) xs =
    [ALLOCA; MSTORE; ADD; ADD; MLOAD; ADD; MLOAD; ADD; AND; ADD; MSTORE;
     ADD; MCOPY; ADD; AND; ADD; MSTORE; ADD; MSTORE; MLOAD; ADD; ADD]` by
    (simp[NoAsms, Abbr `xs`, GSYM MAP_TAKE] >>
     pure_rewrite_tac[revert_reason_suffix_def, MAP] >>
     BETA_TAC >>
     qpat_assum `!j opc ops outs. _ = opc` (fn th => pure_rewrite_tac[th]) >>
     simp[NoAsms]) >>
  `EVERY (\h. h.inst_opcode <> INVOKE /\ ~is_terminator h.inst_opcode) xs` by
    (`EVERY (\opc. opc <> INVOKE /\ ~is_terminator opc)
       (MAP (\h. h.inst_opcode) xs)` by simp[is_terminator_def] >>
     qpat_x_assum `EVERY _ (MAP _ xs)` mp_tac >>
     simp[NoAsms, EVERY_MAP, combinTheory.o_DEF]) >>
  `LENGTH (FILTER (\h. h.inst_opcode = GAS) xs) = 0` by
    (`EVERY (\opc. opc <> GAS) (MAP (\h. h.inst_opcode) xs)` by simp[] >>
     qpat_x_assum `EVERY _ (MAP _ xs)` mp_tac >>
     simp[NoAsms, EVERY_MAP, combinTheory.o_DEF, EVERY_MEM,
          LENGTH_NIL, FILTER_EQ_NIL]) >>
  `i.inst_opcode <> INVOKE /\ i.inst_opcode <> GAS` by
    simp[NoAsms, Abbr `i`, mk_inst_def] >>
  qspecl_then [`xs`, `i`] mp_tac
    (Q.INST [`lo` |-> `0`] run_inst_seq_final_abort_gas_path_ptr) >>
  qpat_assum `xs ++ [i] = _` (fn th => pure_rewrite_tac[th]) >>
  disch_then drule_all >> strip_tac >>
  qexistsl [`Gf`, `tnf`, `j`] >>
  qpat_x_assum `gas_path_ptr _ _ _ _ _ _ _ _ _ _ _ _` mp_tac >>
  qpat_assum `LENGTH (FILTER _ xs) = 0` (fn th => pure_rewrite_tac[th]) >>
  simp[NoAsms]
QED
