(* Shared word-load/store execution, independent of the invoking compiler. *)
Theory wordLoadStorePtr
Ancestors
  typedCopyCompatibilityPtr normalizationPrefixPtr fragExecPtr bodyPtrDefs ptrSafeRun ptrDiscipline
  venomExecSemantics venomInstProofs venomInst venomState
  contextCodegenRelProps finite_map memLocDefs codegenRel contextCodegenRel fragExec
  typedCopyAgreement emitHelper compileEnv valueEncodingProps representationCleanPtr
  ptrCoverage allocationPtr exprLoweringProps typedCopyLayoutPtr exprSimBufferStore

Theorem ptr_inst_ok_mload:
  !D ctx fn G tn s id src tmp fuel.
    ptr_covers G tn src s 32 /\ ~ctx_has_dalloca ctx ==>
    ptr_inst_ok D 0 fuel ctx fn G tn
      (mk_inst id MLOAD [Var src] [tmp]) s
Proof
  rpt strip_tac >> gvs[ptr_covers_def] >>
  simp[ptr_inst_ok_def, access_ok_def, taint_ok_def, allocas_from_def,
       mk_inst_def, source_memory_write_ranges_def,
       source_memory_read_ranges_def,
       eval_operand_def] >>
  conj_tac >- (rpt strip_tac >> gvs[] >> simp[mem_read_ops_def] >> metis_tac[]) >>
  simp[step_inst_non_invoke] >>
  PURE_ONCE_REWRITE_TAC[step_inst_base_def] >>
  pure_rewrite_tac[instruction_accessors, instruction_accfupds, opcode_case_def] >>
  simp[exec_read1_def, eval_operand_def, AllCaseEqs(), mload_def,
       update_var_def] >> rpt strip_tac >> gvs[]
QED

Theorem mload_ghost_clean:
  !PG G tn s id src tmp a.
    eval_operand src s = SOME a /\
    (!i. w2n a <= i /\ i < w2n a + 32 ==> i NOTIN tn.t_mem) ==>
    op_taint (step_taint (mk_inst id MLOAD [src] [tmp]) s
      (update_var tmp (mload (w2n a) s) s) tn) (Var tmp) = {} /\
    (step_taint (mk_inst id MLOAD [src] [tmp]) s
      (update_var tmp (mload (w2n a) s) s) tn).t_mem = tn.t_mem /\
    (step_taint (mk_inst id MLOAD [src] [tmp]) s
      (update_var tmp (mload (w2n a) s) s) tn).t_stor = tn.t_stor /\
    (step_taint (mk_inst id MLOAD [src] [tmp]) s
      (update_var tmp (mload (w2n a) s) s) tn).t_trans = tn.t_trans
Proof
  rpt strip_tac >>
  gvs[step_taint_def, set_var_taint_def, out_taint_def, op_taint_def,
      mk_inst_def, mem_word_taint_def, mem_taint_def, new_site_bytes_def,
      step_writes_def, written_taint_def, source_memory_write_ranges_def,
      range_bytes_def, update_var_def, store_taint_def, adopt_reset_def,
      FLOOKUP_UPDATE, FLOOKUP_DEF, pred_setTheory.EXTENSION]
  >- (gen_tac >> Cases_on `x < 32` >> simp[] >>
      first_x_assum irule >> decide_tac) >>
  metis_tac[]
QED

Theorem mload_preserves_ptr_covers:
  !PG G tn s id src tmp dst a n.
    tmp <> dst /\ ptr_covers G tn dst s n ==>
    ptr_covers
      (step_prov PG G (mk_inst id MLOAD [src] [tmp])
        (update_var tmp (mload (w2n a) s) s))
      (step_taint (mk_inst id MLOAD [src] [tmp]) s
        (update_var tmp (mload (w2n a) s) s) tn)
      dst (update_var tmp (mload (w2n a) s) s) n
Proof
  rpt strip_tac >>
  gvs[ptr_covers_def, step_prov_def, set_prov_def, out_prov_def,
      step_taint_def, set_var_taint_def, op_taint_def, mk_inst_def,
      update_var_def, lookup_var_def, FLOOKUP_DRESTRICT, FLOOKUP_UPDATE]
QED

Theorem mload_then_mstore_ok:
  !D ctx fn PG G tn s id src dst tmp a fuel.
    ptr_covers G tn src s 32 /\ ptr_covers G tn dst s 32 /\
    lookup_var src s = SOME a /\ tmp <> dst /\
    (!i. w2n a <= i /\ i < w2n a + 32 ==> i NOTIN tn.t_mem) /\
    ~ctx_has_dalloca ctx ==>
    ptr_inst_ok D 0 fuel ctx fn G tn
      (mk_inst id MLOAD [Var src] [tmp]) s /\
    ptr_inst_ok D 0 fuel ctx fn
      (step_prov PG G (mk_inst id MLOAD [Var src] [tmp])
        (update_var tmp (mload (w2n a) s) s))
      (step_taint (mk_inst id MLOAD [Var src] [tmp]) s
        (update_var tmp (mload (w2n a) s) s) tn)
      (mk_inst (id+1) MSTORE [Var dst; Var tmp] [])
      (update_var tmp (mload (w2n a) s) s)
Proof
  rpt strip_tac
  >- (irule ptr_inst_ok_mload >> simp[]) >>
  irule ptr_inst_ok_mstore >> simp[] >> conj_tac
  >- (irule (cj 1 mload_ghost_clean) >> simp[eval_operand_def] >> metis_tac[]) >>
  irule mload_preserves_ptr_covers >> simp[]
QED

Theorem ptr_fragment_step:
  !cx ctx PG sa sb inst P Q R.
    sb.cs_current_bb = sa.cs_current_bb /\
    sb.cs_current_insts = sa.cs_current_insts ++ [inst] /\
    inst.inst_opcode <> INVOKE /\ ~is_terminator inst.inst_opcode /\
    (!G tn s. P G tn s ==>
       ?t. step_inst_base inst s = OK t /\
           t.vs_current_bb = s.vs_current_bb /\ t.vs_halted = s.vs_halted /\
           (!fuel fn. ~ctx_has_dalloca ctx ==>
             ptr_inst_ok (cx_dead cx) 0 fuel ctx fn G tn inst s) /\
           Q (step_prov PG G inst t) (step_taint inst s t tn)
             (t with vs_inst_idx := SUC s.vs_inst_idx)) ==>
    frag_exec_ptr cx ctx PG sa sb P Q R
Proof
  rpt gen_tac >> strip_tac >> simp[frag_exec_ptr_def] >> rpt strip_tac >>
  drule_all fn_has_code_same_block >> strip_tac >>
  `get_instruction bb s.vs_inst_idx = SOME inst` by
    (qpat_x_assum `!i. _` (qspec_then `0` mp_tac) >> simp[]) >>
  first_x_assum drule >> strip_tac >>
  disj1_tac >>
  qexistsl_tac [`step_prov PG G inst t`, `step_taint inst s t tn`,
               `t with vs_inst_idx := SUC s.vs_inst_idx`] >>
  simp[] >> rpt strip_tac >> qexists_tac `fuel` >> gvs[] >>
  conj_tac >- (simp[run_from_def, Once exec_block_def, step_inst_non_invoke]) >>
  simp[ghost_run_def, Once ghost_block_def, ghost_step_def,
       step_inst_non_invoke] >>
  strip_tac >> fs[ptr_safe_run_def] >>
  simp[Once ptr_safe_block_def, ptr_safe_step_def, step_inst_non_invoke,
       ghost_step_def] >> gvs[]
QED

Theorem mload_frag_ptr:
  !cx ctx PG sa sb id src tmp P Q R.
    sb.cs_current_bb = sa.cs_current_bb /\
    sb.cs_current_insts = sa.cs_current_insts ++
      [mk_inst id MLOAD [Var src] [tmp]] /\
    (!G tn s. P G tn s ==>
       ptr_covers G tn src s 32 /\
       !a. lookup_var src s = SOME a ==>
         Q (step_prov PG G (mk_inst id MLOAD [Var src] [tmp])
              (update_var tmp (mload (w2n a) s) s))
           (step_taint (mk_inst id MLOAD [Var src] [tmp]) s
              (update_var tmp (mload (w2n a) s) s) tn)
           ((update_var tmp (mload (w2n a) s) s) with
              vs_inst_idx := SUC s.vs_inst_idx)) ==>
    frag_exec_ptr cx ctx PG sa sb P Q R
Proof
  rpt strip_tac >> irule ptr_fragment_step >> simp[] >>
  simp[mk_inst_def, is_terminator_def] >> rpt strip_tac >>
  `?a. lookup_var src s = SOME a` by
    (first_x_assum drule >> simp[ptr_covers_def] >> metis_tac[]) >>
  qexists_tac `update_var tmp (mload (w2n a) s) s` >>
  conj_tac >-
    (PURE_ONCE_REWRITE_TAC[step_inst_base_def] >>
     simp[mk_inst_def, exec_read1_def, eval_operand_def]) >>
  simp[update_var_def] >> conj_tac
  >- (rpt strip_tac >> irule (SRULE [mk_inst_def] ptr_inst_ok_mload) >> metis_tac[]) >>
  first_x_assum drule >> simp[mk_inst_def, update_var_def]
QED

Theorem mstore_frag_ptr:
  !cx ctx PG sa sb id dst value P Q R.
    sb.cs_current_bb = sa.cs_current_bb /\
    sb.cs_current_insts = sa.cs_current_insts ++
      [mk_inst id MSTORE [Var dst; value] []] /\
    (!G tn s. P G tn s ==>
       ptr_covers G tn dst s 32 /\ op_taint tn value = {} /\
       ?a w. lookup_var dst s = SOME a /\ eval_operand value s = SOME w /\
         Q (step_prov PG G (mk_inst id MSTORE [Var dst; value] [])
              (mstore (w2n a) w s))
           (step_taint (mk_inst id MSTORE [Var dst; value] []) s
              (mstore (w2n a) w s) tn)
           ((mstore (w2n a) w s) with vs_inst_idx := SUC s.vs_inst_idx)) ==>
    frag_exec_ptr cx ctx PG sa sb P Q R
Proof
  rpt strip_tac >> irule ptr_fragment_step >> simp[is_terminator_def] >>
  rpt strip_tac >> first_x_assum drule >> strip_tac >>
  qexists_tac `mstore (w2n a) w s` >>
  conj_tac >-
    (PURE_ONCE_REWRITE_TAC[step_inst_base_def] >>
     simp[mk_inst_def, exec_write2_def, eval_operand_def]) >>
  simp[mstore_def] >> rpt strip_tac >>
  irule ptr_inst_ok_mstore >> simp[]
QED

Theorem mstore_ghost_frame:
  !PG G tn s id dst value a w.
    lookup_var dst s = SOME a /\ eval_operand value s = SOME w /\
    op_taint tn value = {} ==>
    step_prov PG G (mk_inst id MSTORE [Var dst; value] [])
      (mstore (w2n a) w s) = G /\
    (step_taint (mk_inst id MSTORE [Var dst; value] []) s
      (mstore (w2n a) w s) tn).t_var = tn.t_var /\
    (step_taint (mk_inst id MSTORE [Var dst; value] []) s
      (mstore (w2n a) w s) tn).t_stor = tn.t_stor /\
    (step_taint (mk_inst id MSTORE [Var dst; value] []) s
      (mstore (w2n a) w s) tn).t_trans = tn.t_trans /\
    (step_taint (mk_inst id MSTORE [Var dst; value] []) s
      (mstore (w2n a) w s) tn).t_mem =
      tn.t_mem DIFF {i | w2n a <= i /\ i < w2n a + 32}
Proof
  rpt strip_tac >>
  simp[step_prov_def, set_prov_def, out_prov_def, step_taint_def,
       mk_inst_def, set_var_taint_def, finite_mapTheory.DRESTRICT_UNIV,
       store_taint_def, adopt_reset_def, mem_taint_def, step_writes_def,
       source_memory_write_ranges_def, fixed_source_write_range_def,
       eval_operand_def, written_taint_def, range_bytes_def, new_site_bytes_def,
       mstore_def, FLOOKUP_DEF, pred_setTheory.EXTENSION] >> metis_tac[]
QED

Theorem mstore_memory_frame:
  !s off w.
    mem_agree_outside {i | off <= i /\ i < off + 32}
      (mstore off w s).vs_memory s.vs_memory
Proof
  rpt gen_tac >> simp[mem_agree_outside_def] >> rpt strip_tac >>
  irule mstore_mem_bytes_at_disjoint >> decide_tac
QED

Theorem word_load_store_framed_frag_ptr:
  !cx ctx PG R sa sm sb id src dst tmp G tn s a b.
    sm.cs_current_bb = sa.cs_current_bb /\
    sm.cs_current_insts = sa.cs_current_insts ++ [mk_inst id MLOAD [Var src] [tmp]] /\
    sb.cs_current_bb = sm.cs_current_bb /\
    sb.cs_current_insts = sm.cs_current_insts ++ [mk_inst (id+1) MSTORE [Var dst;Var tmp] []] /\
    cs_extends sa sm /\ cs_extends sm sb /\
    (!p. not_fresh_at sa p ==> tmp <> p) /\ not_fresh_at sa dst /\
    ptr_covers G tn src s 32 /\ ptr_covers G tn dst s 32 /\
    lookup_var src s = SOME a /\ lookup_var dst s = SOME b /\
    (!i. w2n a <= i /\ i < w2n a+32 ==> i NOTIN tn.t_mem) ==>
    ?Gf tnf sf.
      frag_exec_ptr cx ctx PG sa sb
        (\g t v. g=G /\ t=tn /\ v=s) (\g t v. g=Gf /\ t=tnf /\ v=sf) R /\
      sf = (mstore (w2n b) (mload (w2n a) s)
        (update_var tmp (mload (w2n a) s) s)) with
          vs_inst_idx := SUC (SUC s.vs_inst_idx) /\
      sf.vs_memory = (mstore (w2n b) (mload (w2n a) s) s).vs_memory /\
      mem_agree_outside {i | w2n b <= i /\ i < w2n b+32} sf.vs_memory s.vs_memory /\
      tnf.t_mem = tn.t_mem DIFF {i | w2n b <= i /\ i < w2n b+32} /\
      tnf.t_stor = tn.t_stor /\ tnf.t_trans = tn.t_trans /\ tnf.t_imm = tn.t_imm /\
      sf.vs_allocas = s.vs_allocas /\ sf.vs_alloca_next = s.vs_alloca_next /\
      sf.vs_accounts = s.vs_accounts /\ sf.vs_transient = s.vs_transient /\
      sf.vs_call_ctx = s.vs_call_ctx /\ sf.vs_data_section = s.vs_data_section /\
      sf.vs_logs = s.vs_logs /\ sf.vs_requests = s.vs_requests /\
      sf.vs_pending_deletions = s.vs_pending_deletions /\
      (!p. not_fresh_at sa p ==> lookup_var p sf = lookup_var p s /\
        FLOOKUP Gf p = FLOOKUP G p /\ op_taint tnf (Var p) = op_taint tn (Var p))
Proof
  rpt gen_tac >> strip_tac >>
  `tmp <> dst` by metis_tac[] >>
  qabbrev_tac `s1 = update_var tmp (mload (w2n a) s) s` >>
  qabbrev_tac `G1 = step_prov PG G (mk_inst id MLOAD [Var src] [tmp]) s1` >>
  qabbrev_tac `tn1 = step_taint (mk_inst id MLOAD [Var src] [tmp]) s s1 tn` >>
  qabbrev_tac `v1 = s1 with vs_inst_idx := SUC s.vs_inst_idx` >>
  `ptr_covers G1 tn1 dst s1 32` by
    (simp[Abbr `G1`, Abbr `tn1`, Abbr `s1`] >>
     irule mload_preserves_ptr_covers >> simp[]) >>
  `op_taint tn1 (Var tmp) = {} /\ tn1.t_mem = tn.t_mem /\
   tn1.t_stor = tn.t_stor /\ tn1.t_trans = tn.t_trans` by
    (simp[Abbr `tn1`, Abbr `s1`] >> irule mload_ghost_clean >>
     simp[eval_operand_def]) >>
  `lookup_var dst v1 = SOME b /\
   eval_operand (Var tmp) v1 = SOME (mload (w2n a) s)` by
    (simp[Abbr `v1`, Abbr `s1`, update_var_def, lookup_var_def,
          eval_operand_def, FLOOKUP_UPDATE] >> gvs[lookup_var_def]) >>
  qabbrev_tac `s2 = mstore (w2n b) (mload (w2n a) s) v1` >>
  qabbrev_tac `G2 = step_prov PG G1
    (mk_inst (id+1) MSTORE [Var dst; Var tmp] []) s2` >>
  qabbrev_tac `tn2 = step_taint (mk_inst (id+1) MSTORE [Var dst; Var tmp] [])
    v1 s2 tn1` >>
  qexistsl_tac [`G2`, `tn2`, `s2 with vs_inst_idx := SUC v1.vs_inst_idx`] >>
  conj_tac >-
    (irule frag_exec_ptr_seq >>
     qexistsl_tac [`\g t v. g = G1 /\ t = tn1 /\ v = v1`, `sm`] >>
     simp[] >> conj_tac >-
       (irule mload_frag_ptr >> simp[] >>
        qexistsl_tac [`id`, `src`, `tmp`] >>
        simp[Abbr `G1`, Abbr `tn1`, Abbr `v1`, Abbr `s1`]) >>
     irule mstore_frag_ptr >> simp[] >>
     qexistsl_tac [`dst`, `id+1`, `Var tmp`] >>
     simp[Abbr `G2`, Abbr `tn2`, Abbr `s2`] >>
     gvs[Abbr `v1`, ptr_covers_def, lookup_var_def]) >>
  `s2.vs_memory = (mstore (w2n b) (mload (w2n a) s) s).vs_memory` by
    simp[Abbr `s2`, Abbr `v1`, Abbr `s1`, mstore_def, update_var_def] >>
  simp[mstore_memory_frame, Abbr `tn2`, Abbr `s2`, mstore_ghost_frame] >>
  simp[Abbr `v1`, Abbr `s1`, update_var_def, mstore_def] >>
  conj_tac >- simp[step_taint_def, imm_taint_def, mk_inst_def,
    Abbr `tn1`, update_var_def, step_writes_def] >>
  rpt strip_tac >>
  `tmp <> p` by metis_tac[] >>
  simp[Abbr `G2`, Abbr `G1`, Abbr `tn1`,
       step_prov_def, set_prov_def, out_prov_def, step_taint_def,
       set_var_taint_def, op_taint_def, mk_inst_def, update_var_def,
       lookup_var_def, mstore_def, FLOOKUP_UPDATE, FLOOKUP_DRESTRICT]
QED
