(* A shared checked selector allocation/store suffix. *)
Theory bodyPtrEnvBuiltinsSelectorSuffix
Ancestors bodyPtrEnvBuiltinsSelectorBuffer bodyPtrEnvBuiltinsAllocation
  bodyPtrEnvBuiltinsEdges allocationPtr typedCopyPtr loweringSlice
  ghostPcTransportPtr fragExecPtr fragExec fragGasSeqPtr ptrDiscipline venomState
  venomExecSemantics venomInst compileEnv exprLoweringProps exprSimProps
  finite_map pred_set list words

(* Package the complete allocation stage before the store-tail certificate. *)
Theorem selector_allocation_certificate:
  stmt_state_rel ctx fn cenv cx es s /\ ghost_inv d cenv cx es G tn s /\
  fn_inst_ids_distinct fn /\
  MEM (mk_inst ia ALLOCA [Lit 64w] [p]) (fn_insts fn) /\
  ~ctx_has_dalloca ctx /\ local_ptrs_reserved cenv sa /\ ~not_fresh_at sa p /\
  (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  step_inst_base (mk_inst ia ALLOCA [Lit 64w] [p]) s = OK s1 ==>
  ?G1 tn1 b.
    inst_seq_ptr D 0 ctx fn PG G tn [mk_inst ia ALLOCA [Lit 64w] [p]] s G1 tn1 /\
    stmt_state_rel ctx fn cenv cx es s1 /\ ghost_inv d cenv cx es G1 tn1 s1 /\
    ghost_kept cenv es sa G tn s G1 tn1 /\ ptr_covers G1 tn1 p s1 64 /\
    eval_operand (Var p) s1 = SOME (n2w b) /\ b+64 < dimword (:256) /\
    (!name lb sz. local_region cenv es.scopes s1 name lb sz ==>
       lb+sz <= b \/ b+64 <= lb)
Proof
  strip_tac >>
  `64 < dimword (:256)` by simp[dimword_def] >>
  `not_local_ptr cenv es.scopes p` by
    (gvs[local_ptrs_reserved_def, not_local_ptr_def] >> metis_tac[]) >>
  drule_all alloca_step_site >> strip_tac >>
  qexistsl_tac [`step_prov PG G (mk_inst ia ALLOCA [Lit 64w] [p]) s1`,
    `step_taint (mk_inst ia ALLOCA [Lit 64w] [p]) s s1 tn`, `b`] >>
  conj_tac
  >- (simp[inst_seq_ptr_def] >> irule ptr_inst_ok_alloca >> simp[]) >>
  `stmt_state_rel ctx fn cenv cx es s1` by suspend "state_rel" >>
  conj_tac >- simp[] >> conj_tac
  >- (irule alloca_step_ghost_inv >> simp[] >> metis_tac[]) >>
  conj_tac
  >- (irule alloca_step_ghost_kept >> simp[] >> metis_tac[]) >>
  conj_tac >- (irule alloca_step_ptr_covers >> metis_tac[]) >>
  simp[] >> suspend "separation"
QED

Resume selector_allocation_certificate[state_rel]:
  `exec_alloca (mk_inst ia ALLOCA [Lit 64w] [p]) s (64w:256 word) = OK s1` by
    (qpat_x_assum `step_inst_base _ _ = _` mp_tac >>
     PURE_ONCE_REWRITE_TAC[step_inst_base_def] >> simp[mk_inst_def]) >>
  drule_at (Pat `exec_alloca _ _ _ = _`) stmt_state_rel_exec_alloca >>
  simp[mk_inst_def] >> strip_tac >>
  gvs[mk_inst_def] >> first_x_assum drule_all >> simp[]
QED

Resume selector_allocation_certificate[separation]:
  rpt gen_tac >> strip_tac >>
  drule_all alloca_step_frame_effects >>
  disch_then (qspecl_then [`PG`, `G`, `tn`] strip_assume_tac) >>
  `local_region cenv es.scopes s name lb sz` by
    (gvs[local_region_def, not_local_ptr_def] >> metis_tac[]) >>
  `lookup_var p s1 = SOME (n2w b)` by fs[eval_operand_def] >>
  `lb + sz <= w2n (n2w b:256 word) \/ w2n (n2w b:256 word) + 64 <= lb` by
    (irule selector_alloca_local_disjoint >> simp[] >> metis_tac[]) >>
  `b < dimword (:256)` by decide_tac >> gvs[]
QED

Finalise selector_allocation_certificate
