(* Checked allocation-prefix boundaries, including reused allocation sites. *)
Theory revertReasonPrefixPtr
Ancestors
  revertReasonLayout allocationPtr typedCopyPtr fragExec fragGasSeqPtr ghostPcTransportPtr
  loweringSlice exprLoweringProps bodyPtrDefs fragExecPtr venomExecSemantics venomInst venomState
  ptrDiscipline finite_map words arithmetic exprSimAlloc localPtrsProps compileEnv

Theorem alloca_store_offset_alloca_checks:
  stmt_state_rel ctx func cenv cx es s /\
  MEM (mk_inst id ALLOCA [Lit (n2w n)] [out]) (fn_insts func) /\
  32 <= n /\ n < dimword(:256) /\ ~ctx_has_dalloca ctx /\
  step_inst_base (mk_inst id ALLOCA [Lit (n2w n)] [out]) s = OK s1 ==>
  ?Gf tnf.
    inst_seq_ptr D 0 ctx func PG G tn
      [mk_inst id ALLOCA [Lit (n2w n)] [out];
       mk_inst (id+1) MSTORE [Var out; Lit value] [];
       mk_inst (id+2) ADD [Var out; Lit off] [p];
       mk_inst (id+3) ALLOCA [Lit sz] [q]] s Gf tnf
Proof
  strip_tac >>
  qmatch_goalsub_abbrev_tac `inst_seq_ptr _ _ _ _ _ _ _ [i;j;k;l] _ _ _` >>
  `ptr_covers (step_prov PG G i s1)
      (step_taint i s s1 tn) out s1 n` by
    (unabbrev_all_tac >> irule alloca_step_ptr_covers >> metis_tac[]) >>
  `ptr_covers (step_prov PG G i s1)
      (step_taint i s s1 tn) out s1 32` by
    (gvs[ptr_covers_def] >> metis_tac[LESS_EQ_TRANS]) >>
  simp[Once inst_seq_ptr_def, Abbr `i`, ptr_inst_ok_alloca] >>
  simp[Once inst_seq_ptr_def] >>
  qmatch_goalsub_abbrev_tac `ptr_inst_ok _ _ _ _ _ g1 t1 _ _` >>
  `ptr_inst_ok D 0 0 ctx func g1 t1 j
      (s1 with vs_inst_idx := SUC s.vs_inst_idx)` by
    (simp[Abbr `j`] >> irule ptr_inst_ok_mstore >>
     simp[op_taint_def, Abbr `g1`, Abbr `t1`]) >>
  `?a. lookup_var out s1 = SOME a /\ op_taint t1 (Var out) = {}` by
    gvs[ptr_covers_def, eval_operand_def] >>
  `step_inst_base j (s1 with vs_inst_idx := SUC s.vs_inst_idx) =
     OK ((mstore (w2n a) value s1) with vs_inst_idx := SUC s.vs_inst_idx)` by
    (simp[Abbr `j`] >> PURE_ONCE_REWRITE_TAC[step_inst_base_def] >>
     simp[mk_inst_def, exec_write2_def, eval_operand_def, mstore_def]) >>
  simp[] >>
  qmatch_goalsub_abbrev_tac `inst_seq_ptr _ _ _ _ _ g2 t2 _ s2 _ _` >>
  `op_taint t2 (Var out) = {}` by
    (simp[Abbr `t2`, Abbr `j`, op_taint_def, mstore_ghost_frame,
          eval_operand_def] >> gvs[op_taint_def]) >>
  simp[Once inst_seq_ptr_def] >>
  `ptr_inst_ok D 0 0 ctx func g2 t2 k s2` by
    (simp[Abbr `k`] >> irule ptr_inst_ok_copy_len_binop >>
     simp[op_taint_def] >> gvs[op_taint_def]) >>
  Cases_on `step_inst_base k s2` >> simp[] >>
  simp[inst_seq_ptr_def, Abbr `l`, ptr_inst_ok_alloca] >>
  Cases_on `step_inst_base (mk_inst (id+3) ALLOCA [Lit sz] [q])
    (v with vs_inst_idx := SUC s2.vs_inst_idx)` >> simp[]

QED

Theorem revert_reason_prefix_path_ptr:
  stmt_state_rel ctx func cenv cx es s /\
  MEM (mk_inst id ALLOCA [Lit (n2w (64+ms))]
    [STRING #"%" (toString v)]) (fn_insts func) /\
  64+ms < dimword(:256) /\ ~ctx_has_dalloca ctx /\
  ~s.vs_halted /\
  lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
  isPREFIX (revert_reason_prefix id v ms)
    (DROP s.vs_inst_idx bb.bb_instructions) /\
  run_inst_seq (revert_reason_prefix id v ms) s = OK t ==>
  ?Gf tnf. gas_path_ptr D 0 ctx func PG G tn s 0 Gf tnf
    (OK (t with vs_inst_idx := s.vs_inst_idx + 4))
Proof
  strip_tac >>
  `?s1. step_inst_base (mk_inst id ALLOCA [Lit (n2w (64+ms))]
     [STRING #"%" (toString v)]) s = OK s1` by
    (qpat_x_assum `run_inst_seq _ _ = _` mp_tac >>
     simp[revert_reason_prefix_def, Once run_inst_seq_def, AllCaseEqs()] >>
     metis_tac[]) >>
  `?Gf tnf. inst_seq_ptr D 0 ctx func PG G tn
      (revert_reason_prefix id v ms) s Gf tnf` by
    (simp[revert_reason_prefix_def] >>
     irule alloca_store_offset_alloca_checks >>
     gvs[ADD_COMM] >> metis_tac[]) >>
  qexistsl_tac [`Gf`, `tnf`] >>
  `EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
      (revert_reason_prefix id v ms)` by
    simp[revert_reason_prefix_def, mk_inst_def, is_terminator_def] >>
  drule_all run_inst_seq_gas_path_ptr >>
  simp[revert_reason_prefix_def, mk_inst_def]
QED

Theorem stmt_state_rel_mstore_alloca:
  stmt_state_rel ctx func cenv cx es s /\ fn_inst_ids_distinct func /\
  MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\
  inst.inst_outputs = [p] /\ not_local_ptr cenv es.scopes p /\
  FLOOKUP s.vs_allocas inst.inst_id = SOME (b,sz) /\
  b <= a /\ a+32 <= b+sz ==>
  stmt_state_rel ctx func cenv cx es (mstore a w s)
Proof
  strip_tac >> irule literal_mstore_state_rel >> simp[] >>
  qexistsl_tac [`b`, `inst`, `sz`] >> simp[] >>
  rpt strip_tac >>
  `regions_disjoint b sz lb lsz` by
    (irule local_ptrs_rel_alloca_disjoint >>
     gvs[stmt_state_rel_def, state_rel_def] >> metis_tac[]) >>
  gvs[regions_disjoint_def]
QED

Theorem alloca_mstore_literal_state_rel:
  stmt_state_rel ctx func cenv cx es s /\ fn_inst_ids_distinct func /\
  MEM (mk_inst id ALLOCA [Lit (n2w n)] [out]) (fn_insts func) /\
  not_local_ptr cenv es.scopes out /\ 32 <= n /\ n < dimword(:256) /\
  step_inst_base (mk_inst id ALLOCA [Lit (n2w n)] [out]) s = OK s1 ==>
  ?b. lookup_var out s1 = SOME (n2w b) /\ b+n < dimword(:256) /\
      stmt_state_rel ctx func cenv cx es (mstore b value s1)
Proof
  strip_tac >>
  `exec_alloca (mk_inst id ALLOCA [Lit (n2w n)] [out]) s (n2w n:bytes32) = OK s1` by
    (qpat_x_assum `step_inst_base _ _ = _` mp_tac >>
     PURE_ONCE_REWRITE_TAC[step_inst_base_def] >>
     simp[mk_inst_def] >> strip_tac >> first_x_assum ACCEPT_TAC) >>
  `stmt_state_rel ctx func cenv cx es s1` by
    (drule_at (Pat `exec_alloca _ _ _ = _`) stmt_state_rel_exec_alloca >>
     gvs[mk_inst_def] >> metis_tac[]) >>
  drule_all alloca_step_site >> strip_tac >>
  qexists_tac `b` >> conj_tac >- gvs[eval_operand_def] >>
  simp[] >> irule stmt_state_rel_mstore_alloca >> simp[] >>
  qexistsl_tac [`b`, `mk_inst id ALLOCA [Lit (n2w n)] [out]`, `out`, `n`] >>
  simp[mk_inst_def]
QED

