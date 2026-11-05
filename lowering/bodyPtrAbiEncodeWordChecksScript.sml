(* Concrete primitive encoder instruction checks. *)
Theory bodyPtrAbiEncodeWordChecks
Ancestors
  bodyPtrAbiEncodePrimitive typedCopyPtr ghostPcTransportPtr
  fragGasSeqPtr fragExecPtr venomExecSemantics venomInst venomState

Theorem abi_encode_word_sequence_checks:
  ptr_covers G tn src s 32 /\ ptr_covers G tn dst s 32 /\
  lookup_var src s = SOME a /\ tmp <> dst /\
  (!i. w2n a <= i /\ i < w2n a + 32 ==> i NOTIN tn.t_mem) /\
  ~ctx_has_dalloca ctx ==>
  ?Gf tnf. inst_seq_ptr D 0 ctx fn PG G tn
    [mk_inst id MLOAD [Var src] [tmp];
     mk_inst (id+1) MSTORE [Var dst;Var tmp] []] s Gf tnf
Proof
  strip_tac >> drule_all mload_then_mstore_ok >>
  disch_then (qspecl_then [`D`, `fn`, `PG`, `id`, `0`] strip_assume_tac) >>
  `ptr_inst_ok D 0 0 ctx fn
    (step_prov PG G (mk_inst id MLOAD [Var src] [tmp])
      (update_var tmp (mload (w2n a) s) s))
    (step_taint (mk_inst id MLOAD [Var src] [tmp]) s
      (update_var tmp (mload (w2n a) s) s) tn)
    (mk_inst (id+1) MSTORE [Var dst;Var tmp] [])
    (update_var tmp (mload (w2n a) s) s with vs_inst_idx := SUC s.vs_inst_idx)` by
    (irule ptr_inst_ok_mstore >> simp[] >> conj_tac
     >- (irule (cj 1 mload_ghost_clean) >> simp[eval_operand_def] >> metis_tac[]) >>
     irule mload_preserves_ptr_covers >> simp[]) >>
  simp[inst_seq_ptr_def] >>
  simp[Once step_inst_base_def, mk_inst_def, exec_read1_def,
       eval_operand_def, eval_operands_def] >>
  asm_rewrite_tac[GSYM mk_inst_def] >>
  qmatch_goalsub_abbrev_tac `step_inst_base store loaded` >>
  Cases_on `step_inst_base store loaded` >> simp[]
QED
