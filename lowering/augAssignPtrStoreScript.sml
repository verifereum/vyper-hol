(* Counted clean scalar stores; source-update invariant transport is separate. *)
Theory augAssignPtrStore
Ancestors
  augAssignPtrLoad typedCopyPtr fragExecPtr fragGasSeqPtr fragGasPathPtr
  bodyPtrDefs venomInst venomState venomExecSemantics ptrSafeRun
  ptrDiscipline emitHelperProps emitHelper compileEnv fragExec
  finite_map words loweringSlice robustCopyTransportPtr valueEncoding valueEncodingProps
  valueEncodingProofs list venomMemProofs exprSimProps localPtrsProps
  stmtSimAssignStore vyperLookup

Theorem mstore_path_ptr:
  ~s.vs_halted /\ ~ctx_has_dalloca ctx /\
  ptr_covers G tn dst s 32 /\ op_taint tn value = {} /\
  lookup_var dst s = SOME a /\ eval_operand value s = SOME w /\
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  get_instruction bb s.vs_inst_idx = SOME (mk_inst id MSTORE [Var dst; value] []) ==>
  gas_path_ptr D 0 ctx fn PG G tn s 0
    (step_prov PG G (mk_inst id MSTORE [Var dst; value] []) (mstore (w2n a) w s))
    (step_taint (mk_inst id MSTORE [Var dst; value] []) s (mstore (w2n a) w s) tn)
    (OK ((mstore (w2n a) w s) with vs_inst_idx := SUC s.vs_inst_idx))
Proof
  strip_tac >>
  `ptr_inst_ok D 0 0 ctx fn G tn (mk_inst id MSTORE [Var dst; value] []) s` by
    (irule ptr_inst_ok_mstore >> simp[]) >>
  `step_inst_base (mk_inst id MSTORE [Var dst; value] []) s =
    OK (mstore (w2n a) w s)` by
    simp[step_inst_base_def, mk_inst_def, exec_write2_def, eval_operand_def] >>
  mp_tac (Q.INST [`lo` |-> `0`, `u` |-> `mstore (w2n (a:256 word)) w s`,
    `i` |-> `mk_inst id MSTORE [Var dst; value] []`] straight_line_ptr_edge) >>
  gvs[mk_inst_def, is_terminator_def] >> strip_tac >>
  drule (cj 2 gas_path_ptr_rules) >> simp[] >>
  disch_then irule >> irule (cj 1 gas_path_ptr_rules) >> simp[mstore_def]
QED

Theorem emit_mstore_path_ptr:
  emit_void MSTORE [Var dst; value] sa = ((),sb) /\
  fn_has_code sa sb fn /\ ~ctx_has_dalloca ctx /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  ptr_covers G tn dst s 32 /\ op_taint tn value = {} /\
  lookup_var dst s = SOME a /\ eval_operand value s = SOME w ==>
  ?tnf sf.
    gas_path_ptr D 0 ctx fn PG G tn s 0 G tnf (OK sf) /\
    sf = (mstore (w2n a) w s) with vs_inst_idx := LENGTH sb.cs_current_insts /\
    tnf = step_taint (mk_inst sa.cs_next_id MSTORE [Var dst; value] []) s
      (mstore (w2n a) w s) tn /\
    tnf.t_mem = tn.t_mem DIFF {i | w2n a <= i /\ i < w2n a + 32} /\
    tnf.t_var = tn.t_var /\ tnf.t_stor = tn.t_stor /\ tnf.t_trans = tn.t_trans /\
    ~sf.vs_halted /\ sf.vs_current_bb = sb.cs_current_bb /\
    sf.vs_inst_idx = LENGTH sb.cs_current_insts /\
    (!p. lookup_var p sf = lookup_var p s)
Proof
  strip_tac >>
  `sb.cs_current_bb = sa.cs_current_bb /\
   sb.cs_current_insts = sa.cs_current_insts ++
     [mk_inst sa.cs_next_id MSTORE [Var dst; value] []]` by
    gvs[emit_void_def, comp_bind_def, comp_ignore_bind_def, comp_return_def,
        fresh_id_def, emit_def] >>
  drule_all fn_has_code_same_block >> strip_tac >>
  `get_instruction bb s.vs_inst_idx =
    SOME (mk_inst sa.cs_next_id MSTORE [Var dst; value] [])` by
    (first_x_assum (qspec_then `0` mp_tac) >> simp[]) >>
  `lookup_block s.vs_current_bb fn.fn_blocks = SOME bb` by simp[] >>
  drule_all mstore_path_ptr >>
  disch_then (qspecl_then [`PG`, `D`] strip_assume_tac) >>
  drule_all mstore_ghost_frame >>
  disch_then (qspecl_then [`PG`, `G`, `sa.cs_next_id`] strip_assume_tac) >>
  qexistsl_tac [
    `step_taint (mk_inst sa.cs_next_id MSTORE [Var dst; value] []) s
      (mstore (w2n a) w s) tn`,
    `(mstore (w2n a) w s) with vs_inst_idx := SUC s.vs_inst_idx`] >>
  gvs[mstore_def, lookup_var_def, arithmeticTheory.ADD1]
QED

Theorem mstore_robust_exterior:
  val_wf tv v /\
  (!i. p <= i /\ i < p + val_footprint tv v ==> ~(off <= i /\ i < off + 32)) /\
  (!m. mem_agree_outside tainted s.vs_memory m ==> val_in_memory tv v p m) ==>
  !m. mem_agree_outside (tainted DIFF {i | off <= i /\ i < off + 32})
    (mstore off w s).vs_memory m ==> val_in_memory tv v p m
Proof
  rpt strip_tac >> irule robust_val_in_memory_exterior_frame >>
  simp[] >> goal_assum (drule_at Any) >>
  qexistsl_tac [`s.vs_memory`, `tainted`, `{i | off <= i /\ i < off + 32}`] >>
  simp[] >> mp_tac (Q.SPECL [`s`, `off`, `w`] mstore_memory_frame) >>
  simp[mem_agree_outside_def]
QED

Theorem mstore_robust_scalar:
  word_value v ==>
  !m. mem_agree_outside (tainted DIFF {i | off <= i /\ i < off + 32})
    (mstore off (val_to_w256 v) s).vs_memory m ==> val_in_memory tv v off m
Proof
  strip_tac >> rpt strip_tac >>
  `mem_bytes_at off 32 m =
    mem_bytes_at off 32 (mstore off (val_to_w256 v) s).vs_memory` by
    (irule LIST_EQ >> simp[] >> rpt strip_tac >> rename1 `j < 32` >>
     `off + j NOTIN (tainted DIFF {i | off <= i /\ i < off + 32})` by simp[] >>
     `mem_bytes_at (off+j) 1 (mstore off (val_to_w256 v) s).vs_memory =
      mem_bytes_at (off+j) 1 m` by
       (fs[mem_agree_outside_def] >> metis_tac[]) >>
     qpat_x_assum `mem_bytes_at _ 1 _ = mem_bytes_at _ 1 _` mp_tac >>
     simp[LIST_EQ_REWRITE, EL_mem_bytes_at]) >>
  `mem_word_at off m = val_to_w256 v` by
    (simp[NoAsms, mem_word_at_def, GSYM mem_bytes_at_def] >>
     metis_tac[mstore_mem_word_at_same, mem_word_at_def, mem_bytes_at_def]) >>
  gvs[word_value_def, val_in_memory_def]
QED

(* Source updates supply only the local-value clause. The remaining ghost
   components are insensitive to a memory-only store with no variable outputs. *)
Theorem ghost_inv_mstore_transport:
  ghost_inv d cenv cx es G tn s /\
  lookup_var dst s = SOME a /\ eval_operand value s = SOME w /\
  op_taint tn value = {} /\
  (!name entry p sz.
    lookup_scopes name es'.scopes = SOME entry /\
    FLOOKUP cenv.ce_vars name = SOME (PtrVar (Var p) sz) ==>
    ptr_covers G tn p s sz /\
    !b mem. lookup_var p s = SOME b /\
      mem_agree_outside (tn.t_mem DIFF {i | w2n a <= i /\ i < w2n a + 32})
        (mstore (w2n a) w s).vs_memory mem ==>
      val_in_memory entry.type entry.value (w2n b) mem) ==>
  ghost_inv d cenv cx es' G
    (step_taint (mk_inst id MSTORE [Var dst; value] []) s (mstore (w2n a) w s) tn)
    ((mstore (w2n a) w s) with vs_inst_idx := pc)
Proof
  strip_tac >>
  drule_all mstore_ghost_frame >>
  disch_then (qspecl_then [`PG`, `G`, `id`] strip_assume_tac) >>
  ` (step_taint (mk_inst id MSTORE [Var dst; value] []) s
      (mstore (w2n a) w s) tn).t_imm = tn.t_imm` by
    simp[step_taint_def, imm_taint_def, adopt_reset_def, mk_inst_def] >>
  gvs[ghost_inv_def, ptr_covers_def, op_taint_def, stor_taint_ok_def,
      mstore_def, lookup_var_def] >>
  conj_tac >- metis_tac[] >>
  Cases_on `d` >> gvs[return_buf_ptr_def] >>
  PairCases_on `x` >> gvs[return_buf_ptr_def, ptr_covers_def, op_taint_def,
    mstore_def, lookup_var_def]
QED

Theorem ghost_kept_mstore:
  ghost_kept cenv es sa G0 tn0 s0 G tn /\
  lookup_var dst s = SOME a /\ eval_operand value s = SOME w /\
  op_taint tn value = {} ==>
  ghost_kept cenv es sa G0 tn0 s0 G
    (step_taint (mk_inst id MSTORE [Var dst; value] []) s (mstore (w2n a) w s) tn)
Proof
  strip_tac >> drule_all mstore_ghost_frame >>
  disch_then (qspecl_then [`[]:(num # num) option list`,
    `FEMPTY:string |-> (num # num)`, `id`] strip_assume_tac) >>
  gvs[ghost_kept_def, op_taint_def] >>
  metis_tac[pred_setTheory.IN_DIFF]
QED

(* The live-local layout, rather than a global disjointness assumption,
   separates the written scalar from every other local's footprint. *)
Theorem local_word_store_exterior:
  local_ptrs_rel fn cenv scopes s /\ name <> other /\
  lookup_scopes name scopes = SOME entry /\
  FLOOKUP cenv.ce_vars name = SOME (PtrVar (Var p) sz) /\
  lookup_var p s = SOME a /\ 32 <= sz /\
  lookup_scopes other scopes = SOME e /\
  FLOOKUP cenv.ce_vars other = SOME (PtrVar (Var q) sq) /\
  lookup_var q s = SOME b ==>
  val_wf e.type e.value /\
  (!i. w2n b <= i /\ i < w2n b + val_footprint e.type e.value ==>
    ~(w2n a <= i /\ i < w2n a + 32))
Proof
  strip_tac >>
  `local_region cenv scopes s name (w2n a) sz /\
   local_region cenv scopes s other (w2n b) sq` by
    (simp[local_region_def] >> metis_tac[]) >>
  `regions_disjoint (w2n a) sz (w2n b) sq` by
    (fs[local_ptrs_rel_def] >> metis_tac[]) >>
  `val_wf e.type e.value /\ type_memory_size e.type <= sq` by
    (fs[local_ptrs_rel_def] >> metis_tac[]) >>
  drule val_footprint_le >> fs[regions_disjoint_def] >> decide_tac
QED

Theorem ghost_local_word_store:
  ghost_inv d cenv cx es G tn s /\
  local_ptrs_rel fn cenv es.scopes s /\
  lookup_scopes name es.scopes = SOME entry /\
  FLOOKUP cenv.ce_vars name = SOME (PtrVar (Var p) sz) /\
  lookup_var p s = SOME a /\ 32 <= sz /\ word_value v /\
  lookup_scopes name scopes' = SOME (entry with <|value := v; popped := []|>) /\
  (!n. n <> name ==> lookup_scopes n scopes' = lookup_scopes n es.scopes) ==>
  !n e q sq.
    lookup_scopes n scopes' = SOME e /\
    FLOOKUP cenv.ce_vars n = SOME (PtrVar (Var q) sq) ==>
    ptr_covers G tn q s sq /\
    !b mem. lookup_var q s = SOME b /\
      mem_agree_outside (tn.t_mem DIFF {i | w2n a <= i /\ i < w2n a + 32})
        (mstore (w2n a) (val_to_w256 v) s).vs_memory mem ==>
      val_in_memory e.type e.value (w2n b) mem
Proof
  strip_tac >> rpt gen_tac >> strip_tac >>
  Cases_on `n = name`
  >- (gvs[] >> conj_tac
      >- (fs[ghost_inv_def] >> metis_tac[]) >>
      rpt strip_tac >> gvs[] >> irule mstore_robust_scalar >> simp[] >>
      goal_assum (drule_at Any)) >>
  `lookup_scopes n es.scopes = SOME e` by metis_tac[] >>
  conj_tac >- (fs[ghost_inv_def] >> metis_tac[]) >>
  rpt strip_tac >> irule mstore_robust_exterior >>
  conj_tac
  >- (fs[local_ptrs_rel_def] >> metis_tac[]) >>
  qexistsl_tac [`w2n a`, `s`, `tn.t_mem`, `val_to_w256 v`] >>
  simp[] >> conj_tac
  >- (fs[ghost_inv_def] >> metis_tac[]) >>
  `name <> n` by simp[] >>
  drule_all local_word_store_exterior >> simp[]
QED

Theorem ghost_inv_write_local_word:
  ghost_inv d cenv cx es G tn s /\
  local_ptrs_rel fn cenv es.scopes s /\
  find_containing_scope name es.scopes = SOME (pre, env, entry, rest) /\
  FLOOKUP cenv.ce_vars name = SOME (PtrVar (Var p) sz) /\
  lookup_var p s = SOME a /\ 32 <= sz /\ word_value v /\
  eval_operand value s = SOME (val_to_w256 v) /\ op_taint tn value = {} ==>
  ghost_inv d cenv cx
    (es with scopes := pre ++ (env |+ (name, entry with <|value := v; popped := []|>)) :: rest)
    G (step_taint (mk_inst id MSTORE [Var p; value] []) s
      (mstore (w2n a) (val_to_w256 v) s) tn)
    ((mstore (w2n a) (val_to_w256 v) s) with vs_inst_idx := pc)
Proof
  strip_tac >>
  drule find_containing_scope_lookup >> strip_tac >>
  drule find_containing_scope_pre_none >> strip_tac >>
  drule find_containing_scope_structure >> strip_tac >>
  irule ghost_inv_mstore_transport >> simp[] >>
  conj_tac
  >- (rpt gen_tac >> strip_tac >> irule ghost_local_word_store >> simp[] >>
      goal_assum (drule_at Any) >>
      qpat_assum `ghost_inv _ _ _ _ _ _ _` (irule_at Any) >>
      qpat_assum `local_ptrs_rel _ _ _ _` (irule_at Any) >>
      qpat_assum `lookup_var p s = SOME a` (irule_at Any) >>
      qpat_assum `FLOOKUP cenv.ce_vars name = SOME (PtrVar (Var p) sz)` (irule_at Any) >>
      qpat_assum `lookup_scopes name es.scopes = SOME entry` (irule_at Any) >>
      qexists_tac `pre ++ (env |+ (name, entry with <|value := v; popped := []|>)) :: rest` >>
      simp[lookup_scopes_update, lookup_scopes_update_other]) >>
  metis_tac[]
QED
