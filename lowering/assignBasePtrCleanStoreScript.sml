(* Counted clean scalar stores, with representation framing at the same endpoint. *)
Theory assignBasePtrCleanStore
Ancestors wordLoadStorePtr assignBasePtrLocalStore assignBasePtrWordStore assignBasePtrLiteralGhost
  typedCopyPtr robustCopyTransportPtr fragGasPathPtr fragGasSeqPtr
  bodyPtrDefs valueEncodingProofs valueEncodingProps venomMemProofs
  venomState venomExecSemantics venomInst ptrDiscipline words pred_set
  ghostPcTransportPtr

Theorem assign_base_clean_mstore_robust:
  !PG G tn s id dst value a w tv v.
    lookup_var dst s = SOME a /\ eval_operand value s = SOME w /\
    op_taint tn value = {} /\ val_wf tv v /\ val_footprint tv v <= 32 /\
    val_in_memory tv v (w2n a) (mstore (w2n a) w s).vs_memory ==>
    !mem. mem_agree_outside
      (step_taint (mk_inst id MSTORE [Var dst; value] []) s
        (mstore (w2n a) w s) tn).t_mem
      (mstore (w2n a) w s).vs_memory mem ==>
      val_in_memory tv v (w2n a) mem
Proof
  rpt gen_tac >> strip_tac >> drule_all mstore_ghost_frame >>
  disch_then (qspecl_then [`PG`, `G`, `id`] strip_assume_tac) >>
  simp[] >> rpt strip_tac >>
  irule assign_base_ptr_clean_window_robust_value >> conj_tac >- simp[] >>
  qexistsl_tac [`(mstore (w2n a) w s).vs_memory`, `32`, `tn.t_mem`] >> simp[]
QED

Theorem assign_base_clean_mstore_exterior:
  !PG G tn s id dst value a w tv v b.
    lookup_var dst s = SOME a /\ eval_operand value s = SOME w /\
    op_taint tn value = {} /\ val_wf tv v /\
    (!i. b <= i /\ i < b + val_footprint tv v ==>
      ~(w2n a <= i /\ i < w2n a + 32)) /\
    (!mem. mem_agree_outside tn.t_mem s.vs_memory mem ==>
      val_in_memory tv v b mem) ==>
    !mem. mem_agree_outside
      (step_taint (mk_inst id MSTORE [Var dst; value] []) s
        (mstore (w2n a) w s) tn).t_mem
      (mstore (w2n a) w s).vs_memory mem ==>
      val_in_memory tv v b mem
Proof
  rpt gen_tac >> strip_tac >> drule_all mstore_ghost_frame >>
  disch_then (qspecl_then [`PG`, `G`, `id`] strip_assume_tac) >>
  simp[] >> rpt strip_tac >> irule robust_val_in_memory_exterior_frame >>
  conj_tac >- simp[] >>
  qexistsl_tac [`s.vs_memory`, `(mstore (w2n a) w s).vs_memory`,
    `tn.t_mem`, `tn.t_mem DIFF {i | w2n a <= i /\ i < w2n a + 32}`,
    `{i | w2n a <= i /\ i < w2n a + 32}`] >>
  simp[] >> rpt strip_tac >> irule mstore_mem_bytes_at_disjoint >>
  fs[] >> decide_tac
QED

Theorem assign_base_clean_mstore_counted:
  !s fn bb id dst value tn G ctx D PG a w tv v u Gf tf.
    ~s.vs_halted /\ lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
    get_instruction bb s.vs_inst_idx =
      SOME (mk_inst id MSTORE [Var dst; value] []) /\
    ptr_covers G tn dst s 32 /\ op_taint tn value = {} /\
    ~ctx_has_dalloca ctx /\ lookup_var dst s = SOME a /\
    eval_operand value s = SOME w /\ val_wf tv v /\
    val_footprint tv v <= 32 /\
    val_in_memory tv v (w2n a) (mstore (w2n a) w s).vs_memory /\
    u = (mstore (w2n a) w s with vs_inst_idx := SUC s.vs_inst_idx) /\
    Gf = step_prov PG G (mk_inst id MSTORE [Var dst; value] [])
      (mstore (w2n a) w s) /\
    tf = step_taint (mk_inst id MSTORE [Var dst; value] []) s
      (mstore (w2n a) w s) tn ==>
    gas_path_ptr D 0 ctx fn PG G tn s 0 Gf tf (OK u) /\
    (!mem. mem_agree_outside tf.t_mem u.vs_memory mem ==>
      val_in_memory tv v (w2n a) mem) /\
    (!cenv es sa. ghost_kept cenv es sa G tn s Gf tf) /\
    (!q. eval_operand q u = eval_operand q s) /\
    u.vs_allocas = s.vs_allocas
Proof
  rpt gen_tac >> strip_tac >>
  `step_inst_base (mk_inst id MSTORE [Var dst; value] []) s =
     OK (mstore (w2n a) w s)` by
    (PURE_ONCE_REWRITE_TAC[step_inst_base_def] >>
     simp[mk_inst_def, exec_write2_def, eval_operand_def]) >>
  drule_all assign_base_mstore_edge_ptr >>
  disch_then (qspecl_then [`D`, `PG`] assume_tac) >>
  gvs[] >> conj_tac
  >- (irule (SRULE [] (Q.INST [`n` |-> `0`, `m` |-> `0`]
        (SPEC_ALL (cj 2 gas_path_ptr_rules)))) >>
      goal_assum (drule_at Any) >>
      simp[cj 1 gas_path_ptr_rules, mstore_def]) >>
  conj_tac >- metis_tac[assign_base_clean_mstore_robust] >>
  rpt gen_tac >> irule assign_base_ptr_clean_mstore_kept >>
  simp[ghost_kept_def]
QED
