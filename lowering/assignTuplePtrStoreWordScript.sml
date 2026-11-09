(* Clean scalar writes supply the updated binding's robust representation. *)
Theory assignTuplePtrStoreWord
Ancestors
  assignTuplePtrStoreFrame stmtSimDeclStore robustCopyTransportPtr exprSimProps
  typedCopyPtr bodyPtrDefs list venomMemProofs valueEncodingProofs
  assignTuplePtrPrefix fragExecPtr venomInst venomExecSemantics venomState
  compileEnv

Theorem val_in_memory_clean_footprint_ptr:
  val_in_memory tv v off mem /\ val_wf tv v /\
  (!i. off <= i /\ i < off + val_footprint tv v ==> i NOTIN dirty) ==>
  !m. mem_agree_outside dirty mem m ==> val_in_memory tv v off m
Proof
  rpt strip_tac >> irule val_in_memory_footprint_agree >>
  conj_tac >- simp[] >> qexists `mem` >> simp[] >>
  irule LIST_EQ >> simp[] >> rpt strip_tac >>
  rename1 `i < val_footprint tv v` >>
  `off+i NOTIN dirty` by (first_x_assum irule >> decide_tac) >>
  `mem_bytes_at (off+i) 1 mem = mem_bytes_at (off+i) 1 m` by
    metis_tac[mem_agree_outside_def] >>
  pop_assum mp_tac >> simp[LIST_EQ_REWRITE, EL_mem_bytes_at]
QED

Theorem typed_word_store_robust_ptr:
  is_word_type ty /\ evaluate_type tenv ty = SOME tv /\
  value_has_type tv v ==>
  !m. mem_agree_outside
    (dirty DIFF {i | off <= i /\ i < off + 32})
    (mstore off (typed_val_to_w256 tv v) s).vs_memory m ==>
    val_in_memory tv v off m
Proof
  rpt gen_tac >> strip_tac >>
  drule_all typed_word_store >>
  disch_then (qspecl_then [`off`, `s`] strip_assume_tac) >>
  rpt strip_tac >> irule val_in_memory_clean_footprint_ptr >>
  conj_tac >- simp[] >> goal_assum (drule_at Any) >> simp[] >>
  rpt strip_tac >>
  `val_footprint tv v <= type_memory_size tv` by metis_tac[val_footprint_le] >>
  simp[] >> decide_tac
QED

Theorem store_lays_out_robust_ptr:
  store_lays_out etv dtv v ==>
  !m. mem_agree_outside
    (dirty DIFF {i | off <= i /\ i < off + 32})
    (mstore off (typed_val_to_w256 etv v) s).vs_memory m ==>
    val_in_memory dtv v off m
Proof
  strip_tac >> fs[store_lays_out_def] >>
  rpt strip_tac >> irule val_in_memory_clean_footprint_ptr >>
  conj_tac >- simp[] >>
  qexistsl_tac [`dirty DIFF {i | off <= i /\ i < off+32}`,
    `(mstore off (typed_val_to_w256 etv v) s).vs_memory`] >> simp[] >>
  `val_footprint dtv v <= type_memory_size dtv` by metis_tac[val_footprint_le] >>
  rpt strip_tac >> simp[] >> decide_tac
QED

Theorem emit_mstore_zero_path_ptr:
  emit_inst MSTORE [Var dst; value] [] sa = ((),sb) /\
  fn_has_code sa sb func /\ ~ctx_has_dalloca ctx /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\ ~s.vs_halted /\
  ptr_covers G tn dst s 32 /\ lookup_var dst s = SOME a /\
  eval_operand value s = SOME w /\ op_taint tn value = {} ==>
  gas_path_ptr D 0 ctx func PG G tn s 0
    (step_prov PG G (mk_inst sa.cs_next_id MSTORE [Var dst; value] [])
      (mstore (w2n a) w s))
    (step_taint (mk_inst sa.cs_next_id MSTORE [Var dst; value] []) s
      (mstore (w2n a) w s) tn)
    (OK (mstore (w2n a) w s with vs_inst_idx := SUC s.vs_inst_idx))
Proof
  strip_tac >> irule emit_inst_zero_path_ptr >>
  simp[is_terminator_def] >> conj_tac
  >- simp[step_inst_base_opcode_eqs, mk_inst_def, exec_write2_def, eval_operand_def] >>
  irule ptr_inst_ok_mstore >> simp[]
QED

Theorem local_region_other_footprint_ptr:
  local_ptrs_rel func cenv scopes s /\
  local_region cenv scopes s id dst cap /\ n <= cap /\
  name <> id /\ lookup_scopes name scopes = SOME entry /\
  FLOOKUP cenv.ce_vars name = SOME (PtrVar (Var p) sz) /\
  lookup_var p s = SOME w ==>
  val_wf entry.type entry.value /\
  (!i. w2n w <= i /\ i < w2n w + val_footprint entry.type entry.value ==>
       i NOTIN {j | dst <= j /\ j < dst+n})
Proof
  strip_tac >>
  `type_memory_size entry.type <= sz /\ val_wf entry.type entry.value` by
    (fs[local_ptrs_rel_def] >> metis_tac[]) >>
  `local_region cenv scopes s name (w2n w) sz` by
    simp[local_region_def] >>
  `regions_disjoint dst cap (w2n w) sz` by
    (fs[local_ptrs_rel_def] >> metis_tac[]) >>
  `val_footprint entry.type entry.value <= type_memory_size entry.type` by
    metis_tac[val_footprint_le] >>
  gvs[regions_disjoint_def] >> rpt strip_tac >> simp[] >> decide_tac
QED
