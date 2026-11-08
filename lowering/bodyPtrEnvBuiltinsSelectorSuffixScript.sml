(* A shared checked selector allocation/store suffix. *)
Theory bodyPtrEnvBuiltinsSelectorSuffix
Ancestors bodyPtrEnvBuiltinsSelectorBuffer bodyPtrEnvBuiltinsAllocation
  bodyPtrEnvBuiltinsEdges allocationPtr typedCopyPtr loweringSlice
  ghostPcTransportPtr decoderGhostFramePtr loweringHalt fragExecPtr fragExec fragGasSeqPtr ptrDiscipline venomState
  venomExecSemantics venomInst compileEnv exprLoweringProps exprSimProps
  bodyPtrDefs localPtrsProps instIdxIndep finite_map pred_set list words

(* Allocation is size-parametric: selector buffers and fixed hash scratch use
   the same certificate, with their respective sizes 64 and 32. *)
Theorem builtin_allocation_certificate:
  stmt_state_rel ctx fn cenv cx es s /\ ghost_inv d cenv cx es G tn s /\
  fn_inst_ids_distinct fn /\ n < dimword (:256) /\
  MEM (mk_inst ia ALLOCA [Lit (n2w n)] [p]) (fn_insts fn) /\
  ~ctx_has_dalloca ctx /\ local_ptrs_reserved cenv sa /\ ~not_fresh_at sa p /\
  (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  step_inst_base (mk_inst ia ALLOCA [Lit (n2w n)] [p]) s = OK s1 ==>
  ?G1 tn1 b.
    inst_seq_ptr D 0 ctx fn PG G tn [mk_inst ia ALLOCA [Lit (n2w n)] [p]] s G1 tn1 /\
    stmt_state_rel ctx fn cenv cx es s1 /\ ghost_inv d cenv cx es G1 tn1 s1 /\
    ghost_kept cenv es sa G tn s G1 tn1 /\ ptr_covers G1 tn1 p s1 n /\
    eval_operand (Var p) s1 = SOME (n2w b) /\ b+n < dimword (:256) /\
    (!name lb sz. local_region cenv es.scopes s1 name lb sz ==>
       lb+sz <= b \/ b+n <= lb)
Proof
  strip_tac >>
  `not_local_ptr cenv es.scopes p` by
    (gvs[local_ptrs_reserved_def, not_local_ptr_def] >> metis_tac[]) >>
  drule_all alloca_step_site >> strip_tac >>
  qexistsl_tac [`step_prov PG G (mk_inst ia ALLOCA [Lit (n2w n)] [p]) s1`,
    `step_taint (mk_inst ia ALLOCA [Lit (n2w n)] [p]) s s1 tn`, `b`] >>
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

Resume builtin_allocation_certificate[state_rel]:
  `exec_alloca (mk_inst ia ALLOCA [Lit (n2w n)] [p]) s (n2w n:256 word) = OK s1` by
    (qpat_x_assum `step_inst_base _ _ = _` mp_tac >>
     simp[step_inst_base_opcode_eqs, mk_inst_def]) >>
  drule_at (Pat `exec_alloca _ _ _ = _`) stmt_state_rel_exec_alloca >>
  simp[mk_inst_def] >> strip_tac >>
  gvs[mk_inst_def] >> first_x_assum drule_all >> simp[]
QED

Resume builtin_allocation_certificate[separation]:
  rpt gen_tac >> strip_tac >>
  drule_all alloca_step_frame_effects >>
  disch_then (qspecl_then [`PG`, `G`, `tn`] strip_assume_tac) >>
  `local_region cenv es.scopes s name lb sz` by
    (gvs[local_region_def, not_local_ptr_def] >> metis_tac[]) >>
  `lookup_var p s1 = SOME (n2w b)` by fs[eval_operand_def] >>
  `lb + sz <= w2n (n2w b:256 word) \/ w2n (n2w b:256 word) + n <= lb` by
    (irule selector_alloca_local_disjoint >> simp[] >> metis_tac[]) >>
  `b < dimword (:256)` by decide_tac >> gvs[]
QED

Finalise builtin_allocation_certificate

(* Internal tail: the ordinary run fixes the final state; no clean allocation
   is assumed.  The two stores establish the clean result window. *)
Theorem selector_store_tail_certificate[local]:
  code = [mk_inst il MSTORE [Var p; Lit 4w] [];
          mk_inst ip ADD [Var p; Lit 32w] [q];
          mk_inst iw MSTORE [Var q; value] []] /\
  ~ctx_has_dalloca ctx /\
  local_ptrs_rel fn cenv es.scopes s /\ ghost_inv d cenv cx es G tn s /\
  ghost_kept cenv es sa G0 tn0 s0 G tn /\
  local_ptrs_reserved cenv sa /\ ~not_fresh_at sa q /\ p <> q /\
  (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!x. value = Var x ==> x <> q) /\
  eval_operand value s = SOME w /\ op_taint tn value = {} /\
  lookup_var p s = SOME (n2w b) /\ b+64 < dimword (:256) /\
  ptr_covers G tn p s 64 /\
  (!name lb sz. local_region cenv es.scopes s name lb sz ==>
     lb+sz <= b \/ b+64 <= lb) /\
  LENGTH bs = 4 /\ TAKE 4 (word_to_bytes w T) = bs /\
  run_inst_seq code s = OK t ==>
  ?G' tn'. inst_seq_ptr D 0 ctx fn PG G tn code (s with vs_inst_idx := k) G' tn' /\
    ghost_inv d cenv cx es G' tn' t /\
    ghost_kept cenv es sa G0 tn0 s0 G' tn' /\
    ptr_val_ok cx (BaseT (BytesT (Dynamic 4))) (BytesV bs) (Var p) G' tn' t /\
    ptr_buf_ok cenv (Builtin (BaseT (BytesT (Dynamic 4))) MethodId args) (Var p) G' t
Proof
  strip_tac >> gvs[] >>
  `b < dimword (:256)` by decide_tac >>
  `b+32 < dimword (:256)` by decide_tac >>
  qabbrev_tac `s1 = mstore b 4w s` >>
  qabbrev_tac `s2 = update_var q (n2w (b+32)) s1` >>
  `step_inst_base (mk_inst il MSTORE [Var p; Lit 4w] []) s = OK s1` by
    (simp[step_inst_base_opcode_eqs, mk_inst_def, exec_write2_def, eval_operand_def, Abbr `s1`]) >>
  `lookup_var p s1 = SOME (n2w b) /\ eval_operand value s1 = SOME w` by
    (simp[Abbr `s1`, mstore_def, lookup_var_def, eval_operand_def] >>
     Cases_on `value` >> gvs[eval_operand_def, lookup_var_def]) >>
  `step_inst_base (mk_inst ip ADD [Var p; Lit 32w] [q]) s1 = OK s2` by
    (simp[step_inst_base_opcode_eqs, mk_inst_def, exec_pure2_def, eval_operand_def, Abbr `s2`,
          wordsTheory.word_add_n2w]) >>
  `lookup_var q s2 = SOME (n2w (b+32)) /\ eval_operand value s2 = SOME w` by
    (simp[Abbr `s2`, lookup_var_def, update_var_def, FLOOKUP_UPDATE] >>
     Cases_on `value` >> gvs[eval_operand_def, lookup_var_def, update_var_def,
       FLOOKUP_UPDATE]) >>
  `step_inst_base (mk_inst iw MSTORE [Var q; value] []) s2 =
   OK (mstore (b+32) w s2)` by
    (simp[step_inst_base_opcode_eqs, mk_inst_def, exec_write2_def, eval_operand_def]) >>
  `t = mstore (b+32) w s2` by gvs[run_inst_seq_def] >>
  qabbrev_tac `tn1 = step_taint (mk_inst il MSTORE [Var p; Lit 4w] []) s s1 tn` >>
  qabbrev_tac `G2 = step_prov PG G (mk_inst ip ADD [Var p; Lit 32w] [q]) s2` >>
  qabbrev_tac `tn2 = step_taint (mk_inst ip ADD [Var p; Lit 32w] [q]) s1 s2 tn1` >>
  qabbrev_tac `tn3 = step_taint (mk_inst iw MSTORE [Var q; value] []) s2 t tn2` >>
  `step_prov PG G (mk_inst il MSTORE [Var p; Lit 4w] []) s1 = G /\
   tn1.t_var = tn.t_var /\ tn1.t_mem = tn.t_mem DIFF {i | b <= i /\ i < b+32} /\
   tn1.t_stor = tn.t_stor /\ tn1.t_trans = tn.t_trans /\ tn1.t_imm = tn.t_imm`
    by suspend "first_frame" >>
  `ptr_covers G2 tn2 q s2 32` by suspend "offset" >>
  `op_taint tn2 value = {}` by suspend "value_clean" >>
  qexistsl_tac [`G2`, `tn3`] >>
  conj_tac >- suspend "checks" >>
  conj_tac >- suspend "ghost_inv" >>
  conj_tac >- suspend "kept" >>
  suspend "result"
QED

Resume selector_store_tail_certificate[checks]:
  `ptr_covers G tn p s 32` by
    (gvs[ptr_covers_def] >> decide_tac) >>
  `ptr_inst_ok D 0 0 ctx fn G tn (mk_inst il MSTORE [Var p; Lit 4w] [])
     (s with vs_inst_idx := k)` by
    (irule ptr_inst_ok_mstore >> simp[op_taint_def]) >>

  `op_taint tn1 (Var p) = {}` by
    (gvs[ptr_covers_def, op_taint_def]) >>
  `~is_terminator (mk_inst il MSTORE [Var p; Lit 4w] []).inst_opcode` by
    simp[mk_inst_def, is_terminator_def] >>
  simp[Once inst_seq_ptr_def, Abbr `tn1`, step_inst_inst_idx_indep,
       exec_result_map_def] >>
  simp[Once inst_seq_ptr_def] >> conj_tac
  >- (irule ptr_inst_ok_copy_len_binop >> simp[op_taint_def]) >>
  `~is_terminator (mk_inst ip ADD [Var p; Lit 32w] [q]).inst_opcode` by
    simp[mk_inst_def, is_terminator_def] >>
  `step_prov PG G (mk_inst ip ADD [Var p; Lit 32w] [q]) s2 = G2` by
    simp[Abbr `G2`] >>
  `step_taint (mk_inst ip ADD [Var p; Lit 32w] [q]) s1 s2
     (step_taint (mk_inst il MSTORE [Var p; Lit 4w] []) s s1 tn) = tn2` by
    simp[Abbr `tn2`] >>
  simp[step_inst_inst_idx_indep, exec_result_map_def] >>
  simp[Once inst_seq_ptr_def] >> conj_tac
  >- (irule ptr_inst_ok_mstore >> simp[]) >>
  `~is_terminator (mk_inst iw MSTORE [Var q; value] []).inst_opcode` by
    simp[mk_inst_def, is_terminator_def] >>
  simp[step_inst_inst_idx_indep, exec_result_map_def, inst_seq_ptr_def] >>
  conj_tac
  >- (qpat_assum `lookup_var q s2 = _` (mp_then Any mp_tac mstore_ghost_frame) >>
      simp[] >> strip_tac >> sym_tac >> first_x_assum (irule o cj 1) >>
      simp[] >> qexists_tac `tn2` >> simp[]) >>
  simp[Abbr `tn3`]
QED

Resume selector_store_tail_certificate[value_clean]:
  Cases_on `value` >>
  gvs[Abbr `tn2`, Abbr `s2`, copy_len_binop_ghost_frame] >>
  gvs[op_taint_def]
QED

Resume selector_store_tail_certificate[offset]:
  `op_taint tn2 (Var q) = {}` by
    simp[Abbr `tn2`, Abbr `s2`, copy_len_binop_ghost_frame] >>
  gvs[ptr_covers_def] >>
  simp[Abbr `G2`, step_prov_def, set_prov_def, out_prov_def,
    first_prov_def, op_prov_def, mk_inst_def, FLOOKUP_UPDATE] >>
  decide_tac
QED

Resume selector_store_tail_certificate[first_frame]:
  qpat_assum `lookup_var p s = _` (mp_then Any mp_tac mstore_ghost_frame) >>
  simp[eval_operand_def, op_taint_def] >> strip_tac >>
  simp[Abbr `tn1`, Abbr `s1`] >> conj_tac
  >- (first_x_assum (irule o cj 1) >> simp[eval_operand_def]) >>
  conj_tac >- (first_x_assum (irule o cj 2) >> simp[eval_operand_def]) >>
  conj_tac >- (first_x_assum (irule o cj 5) >> simp[eval_operand_def]) >>
  conj_tac >- (first_x_assum (irule o cj 3) >> simp[eval_operand_def]) >>
  conj_tac >- (first_x_assum (irule o cj 4) >> simp[eval_operand_def]) >>
  simp[mstore_imm_taint]
QED

Resume selector_store_tail_certificate[ghost_inv]:
  `ghost_inv d cenv cx es G tn1 s1` by
    (simp[Abbr `s1`] >> irule ghost_inv_mstore_clean >> simp[] >>
     conj_tac >- (rpt strip_tac >> first_x_assum drule >> decide_tac) >>
     conj_tac >- metis_tac[] >> qexists_tac `tn` >> simp[]) >>
  `ghost_inv d cenv cx es G2 tn2 s2` by
    (simp[Abbr `G2`, Abbr `tn2`] >> irule single_output_ghost_inv >>
     simp[Abbr `s2`, copy_len_binop_ghost_frame, update_var_def] >>
     qexists_tac `sa` >> simp[] >> rpt strip_tac >>
     `x <> q` by metis_tac[] >>
     simp[lookup_var_def, FLOOKUP_UPDATE]) >>
  `not_local_ptr cenv es.scopes q` by
    (gvs[local_ptrs_reserved_def, not_local_ptr_def] >> metis_tac[]) >>
  `local_ptrs_rel fn cenv es.scopes s1` by
    (simp[Abbr `s1`] >> irule local_ptrs_rel_mstore >> simp[] >>
     rpt strip_tac >> first_x_assum drule >> decide_tac) >>
  `local_ptrs_rel fn cenv es.scopes s2` by
    (simp[Abbr `s2`] >> irule local_ptrs_rel_update_var >>
     metis_tac[not_local_ptr_scope]) >>
  `!name lb sz. local_region cenv es.scopes s2 name lb sz ==>
     lb+sz <= b+32 \/ b+64 <= lb` by suspend "second_separation" >>
  simp[Abbr `tn3`] >>
  qpat_assum `lookup_var q s2 = _` (mp_then Any mp_tac mstore_ghost_frame) >>
  simp[] >> strip_tac >>
  irule ghost_inv_mstore_clean >> simp[] >>
  conj_tac >- (rpt strip_tac >>
    qpat_x_assum `!name lb sz. local_region _ _ s2 _ _ _ ==> _` drule >> simp[]) >>
  conj_tac >- metis_tac[] >>
  qexists_tac `tn2` >> simp[mstore_imm_taint]
QED

Resume selector_store_tail_certificate[second_separation]:
  rpt gen_tac >> strip_tac >>
  `local_region cenv es.scopes s name lb sz` by
    (qpat_x_assum `local_region _ _ s2 _ _ _` mp_tac >>
     simp[local_region_def, Abbr `s2`, Abbr `s1`,
       update_var_def, lookup_var_def, mstore_def, FLOOKUP_UPDATE] >>
     rpt strip_tac >>
     `p' <> q` by metis_tac[not_local_ptr_def] >>
     gvs[] >> metis_tac[]) >>
  qpat_x_assum `!name lb sz. local_region _ _ s _ _ _ ==> _` drule >> decide_tac
QED

Resume selector_store_tail_certificate[kept]:
  `ghost_kept cenv es sa G0 tn0 s0 G tn1` by
    (irule ghost_kept_clean_suffix >> qexistsl_tac [`G`, `tn`] >>
     simp[op_taint_def, SUBSET_DEF]) >>
  `ghost_kept cenv es sa G0 tn0 s0 G2 tn2` by
    (simp[Abbr `G2`, Abbr `tn2`] >> irule single_output_ghost_kept >>
     simp[Abbr `s2`, copy_len_binop_ghost_frame]) >>
  qpat_assum `lookup_var q s2 = _` (mp_then Any mp_tac mstore_ghost_frame) >>
  simp[] >> strip_tac >>
  simp[Abbr `tn3`] >> irule ghost_kept_clean_suffix >>
  qexistsl_tac [`G2`, `tn2`] >> simp[op_taint_def, SUBSET_DEF]
QED

Resume selector_store_tail_certificate[result]:
  `tn3.t_var = tn2.t_var /\
   tn3.t_mem = tn2.t_mem DIFF {i | b+32 <= i /\ i < b+64}` by
    (qpat_assum `lookup_var q s2 = _` (mp_then Any mp_tac mstore_ghost_frame) >>
     simp[] >> strip_tac >> simp[Abbr `tn3`]) >>
  `tn2.t_mem = tn1.t_mem` by
    simp[Abbr `tn2`, Abbr `s2`, copy_len_binop_ghost_frame] >>
  `lookup_var p t = SOME (n2w b)` by
    (qpat_x_assum `t = _` SUBST1_TAC >>
     simp[NoAsms, mstore_def, lookup_var_def] >>
     simp[Abbr `s2`, lookup_var_def, update_var_def, FLOOKUP_UPDATE] >>
     fs[lookup_var_def]) >>
  `ptr_covers G2 tn3 p t 64` by suspend "result_coverage" >>
  conj_tac
  >- (irule selector_buffer_ptr_val >> simp[] >>
      `!i. b <= i /\ i < b+64 ==> i NOTIN tn3.t_mem` by
        (simp[] >> rpt strip_tac >> gvs[] >> decide_tac) >>
      `(mstore (b+32) w s2).vs_memory =
         (mstore (b+32) w (mstore b 4w s)).vs_memory` by
        (
         `s2.vs_memory = (mstore b 4w s).vs_memory` by
           simp[NoAsms, Abbr `s2`, Abbr `s1`, update_var_def] >>
         PURE_ONCE_REWRITE_TAC[mstore_def] >>
         asm_rewrite_tac[] >> simp[NoAsms, LET_THM]) >>
      simp[] >> simp[Abbr `s1`] >> rpt strip_tac >>
      irule selector_buffer_robust >> simp[] >>
      qexistsl_tac [`s`, `tn3.t_mem`, `w`] >> simp[]) >>
  irule selector_buffer_ptr_buf >> qexists_tac `tn3` >> simp[]
QED

Resume selector_store_tail_certificate[result_coverage]:
  `FLOOKUP G2 p = FLOOKUP G p` by
    simp[Abbr `G2`, step_prov_other_output, mk_inst_def] >>
  `op_taint tn2 (Var p) = op_taint tn1 (Var p)` by
    simp[Abbr `tn2`, step_taint_other_output, mk_inst_def] >>
  gvs[ptr_covers_def, op_taint_def] >>
  simp[Abbr `s2`, Abbr `s1`, mstore_def, update_var_def]
QED

Finalise selector_store_tail_certificate

Theorem selector_suffix_certificate:
  code = [mk_inst ia ALLOCA [Lit 64w] [p];
          mk_inst il MSTORE [Var p; Lit 4w] [];
          mk_inst ip ADD [Var p; Lit 32w] [q];
          mk_inst iw MSTORE [Var q; value] []] /\
  stmt_state_rel ctx fn cenv cx es s /\ ghost_inv d cenv cx es G tn s /\
  fn_inst_ids_distinct fn /\
  MEM (mk_inst ia ALLOCA [Lit 64w] [p]) (fn_insts fn) /\
  ~ctx_has_dalloca ctx /\ local_ptrs_reserved cenv sa /\
  ~not_fresh_at sa p /\ ~not_fresh_at sa q /\ p <> q /\
  (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!x. value = Var x ==> x <> p /\ x <> q) /\
  eval_operand value s = SOME w /\ op_taint tn value = {} /\
  LENGTH bs = 4 /\ TAKE 4 (word_to_bytes w T) = bs /\
  run_inst_seq code s = OK t ==>
  ?G' tn'. inst_seq_ptr D 0 ctx fn PG G tn code s G' tn' /\
    ghost_inv d cenv cx es G' tn' t /\
    ghost_kept cenv es sa G tn s G' tn' /\
    ptr_val_ok cx (BaseT (BytesT (Dynamic 4))) (BytesV bs) (Var p) G' tn' t /\
    ptr_buf_ok cenv (Builtin (BaseT (BytesT (Dynamic 4))) MethodId args) (Var p) G' t
Proof
  strip_tac >> gvs[] >>
  qpat_x_assum `run_inst_seq _ _ = _` mp_tac >>
  simp[Once run_inst_seq_def] >>
  Cases_on `step_inst_base (mk_inst ia ALLOCA [Lit 64w] [p]) s` >>
  simp[] >> strip_tac >> rename1 `step_inst_base _ s = OK s1` >>
  `64 < dimword (:256)` by simp[dimword_def] >>
  drule_all builtin_allocation_certificate >>
  disch_then (qspecl_then [`PG`, `D`] strip_assume_tac) >>
  `local_ptrs_rel fn cenv es.scopes s1` by
    fs[stmt_state_rel_def, state_rel_def] >>
  `eval_operand value s1 = SOME w /\ op_taint tn1 value = {}` by
    suspend "value_frame" >>
  `?G' tn'. inst_seq_ptr D 0 ctx fn PG G1 tn1
     [mk_inst il MSTORE [Var p; Lit 4w] [];
      mk_inst ip ADD [Var p; Lit 32w] [q];
      mk_inst iw MSTORE [Var q; value] []]
       (s1 with vs_inst_idx := SUC s.vs_inst_idx) G' tn' /\
     ghost_inv d cenv cx es G' tn' t /\
     ghost_kept cenv es sa G tn s G' tn' /\
     ptr_val_ok cx (BaseT (BytesT (Dynamic 4)))
       (BytesV (TAKE 4 (word_to_bytes w T))) (Var p) G' tn' t /\
     ptr_buf_ok cenv (Builtin (BaseT (BytesT (Dynamic 4))) MethodId args)
       (Var p) G' t` by
    (irule selector_store_tail_certificate >> simp[eval_operand_def] >>
     conj_tac
     >- (qexistsl_tac [`il`, `ip`, `iw`, `q`, `value`, `w`] >> metis_tac[]) >>
     qexists_tac `b` >> fs[eval_operand_def] >> metis_tac[]) >>
  qexistsl_tac [`G'`, `tn'`] >> simp[] >> suspend "checks"
QED

Resume selector_suffix_certificate[value_frame]:
  `64 < dimword (:256)` by simp[dimword_def] >>
  drule_all alloca_step_frame_effects >>
  disch_then (qspecl_then [`PG`, `G`, `tn`] strip_assume_tac) >>
  qpat_x_assum `inst_seq_ptr _ _ _ _ _ _ _ [_] _ _ _` mp_tac >>
  simp[inst_seq_ptr_def] >> strip_tac >>
  qspecl_then [`ia`, `64w`, `p`, `s`] strip_assume_tac step_alloca_frame >>
  gvs[] >> Cases_on `value` >> gvs[eval_operand_def, op_taint_def] >>
  metis_tac[op_taint_def]
QED

Resume selector_suffix_certificate[checks]:
  qpat_x_assum `inst_seq_ptr _ _ _ _ _ _ _ [_] _ _ _`
    (strip_assume_tac o SRULE [inst_seq_ptr_def]) >>
  PURE_ONCE_REWRITE_TAC[inst_seq_ptr_def] >>
  gvs[]
QED

Finalise selector_suffix_certificate
