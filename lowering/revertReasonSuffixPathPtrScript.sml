(* Composition of the checked ABI suffix. Semantic observations use ordinary
   run endpoints; subsequent pointer checks use counted endpoint cursors. *)
Theory revertReasonSuffixPathPtr
Ancestors
  revertReasonSuffixPtr revertReasonPrefixFramePtr fragGasSeqPtr
  instSeqComposePtr ghostPcTransportPtr valueEncodingProps pred_set instIdxIndep
  revertReasonPrefixPtr revertAllocationPtr
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
