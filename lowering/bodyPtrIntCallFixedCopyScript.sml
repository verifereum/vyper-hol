(* Counted fixed-size copies, with robust representation transport. *)
Theory bodyPtrIntCallFixedCopy
Ancestors
  annAssignPtrCopy robustCopyTransportPtr fragGasSeqPtr
  context emitHelper exprLoweringProps valueEncodingProps
  compileEnv venomState venomInst venomMemProofs pred_set
  valueEncoding fragGasPathPtr fragGasSeqAbort rich_list list arithmetic
  ptrDiscipline venomMemDefs venomExecSemantics

Theorem compile_copy_memory_robust_counted:
  !D ctx fn PG sa sb src dst n G tn s a b tv v bb.
    compile_copy_memory (Var dst) (Var src) n sa = ((),sb) /\
    lookup_var src s = SOME a /\ lookup_var dst s = SOME b /\
    n < dimword(:256) /\
    ptr_covers G tn src s n /\ ptr_covers G tn dst s n /\
    val_wf tv v /\ val_footprint tv v <= n /\
    (!m. mem_agree_outside tn.t_mem s.vs_memory m ==>
      val_in_memory tv v (w2n a) m) /\
    ~ctx_has_dalloca ctx /\ ~s.vs_halted /\
    lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
    isPREFIX (emitted_insts sa sb) (DROP s.vs_inst_idx bb.bb_instructions) ==>
    ?Gf tnf sf.
      gas_path_ptr D 0 ctx fn PG G tn s 0 Gf tnf
        (OK (sf with vs_inst_idx :=
          s.vs_inst_idx + LENGTH (emitted_insts sa sb))) /\
      Gf = G /\ tnf.t_var = tn.t_var /\
      tnf.t_stor = tn.t_stor /\ tnf.t_trans = tn.t_trans /\
      (!p. lookup_var p sf = lookup_var p s) /\
      mem_bytes_at (w2n b) n sf.vs_memory =
        mem_bytes_at (w2n a) n s.vs_memory /\
      (!i. i < n ==> (w2n b+i IN tnf.t_mem <=> w2n a+i IN tn.t_mem)) /\
      (!i. ~(w2n b <= i /\ i < w2n b+n) ==>
        mem_bytes_at i 1 sf.vs_memory = mem_bytes_at i 1 s.vs_memory /\
        (i IN tnf.t_mem <=> i IN tn.t_mem)) /\
      (!m. mem_agree_outside tnf.t_mem sf.vs_memory m ==>
        val_in_memory tv v (w2n b) m)
Proof
  rpt gen_tac >> strip_tac >> Cases_on `n`
  >- (gvs[compile_copy_memory_def, comp_return_def, emitted_insts_def] >>
      qexistsl [`tn`, `s`] >> simp[mem_bytes_at_def] >>
      conj_tac
      >- (irule (cj 1 gas_path_ptr_rules) >> simp[]) >>
      rpt strip_tac >> irule robust_val_in_memory_copy_transport >>
      simp[] >> qexistsl [`s.vs_memory`, `s.vs_memory`, `0`, `w2n a`, `tn.t_mem`, `tn.t_mem`] >>
      simp[mem_bytes_at_def]) >>
  rename1 `compile_copy_memory _ _ (SUC k) _ = _` >>
  `emitted_insts sa sb =
    [mk_inst sa.cs_next_id MCOPY [Var dst;Var src;Lit (n2w (SUC k))] []]` by
    (gvs[compile_copy_memory_def, emit_void_def, comp_bind_def,
         comp_return_def, fresh_id_def, emit_def, emitted_insts_def,
         DROP_APPEND]) >>
  qpat_x_assum `emitted_insts sa sb = _`
    (fn th => RULE_ASSUM_TAC (PURE_REWRITE_RULE [th]) >>
              pure_rewrite_tac [th]) >>
  drule instruction_prefix_cursor >> strip_tac >>
  qabbrev_tac `inst = mk_inst sa.cs_next_id MCOPY
    [Var dst; Var src; Lit (n2w (SUC k))] []` >>
  qabbrev_tac `sc = mcopy (w2n b) (w2n a) (SUC k) s` >>
  qabbrev_tac `tf = step_taint inst s sc tn` >>
  qexistsl [`G`, `tf`, `sc`] >>
  conj_tac
  >- (simp[Abbr `tf`, Abbr `inst`, Abbr `sc`, ADD1] >>
      irule (PURE_REWRITE_RULE [ADD1] annassign_mcopy_path_ptr) >>
      simp[eval_operand_def, op_taint_def, wordsTheory.w2n_n2w] >>
      fs[ADD1]) >>
  qpat_assum `lookup_var src s = SOME a`
    (mp_then Any mp_tac annassign_static_mcopy_ghost_ptr) >>
  simp[] >>
  disch_then (qspecl_then [`PG`, `G`, `tn`, `sa.cs_next_id`] mp_tac) >>
  strip_tac >>
  simp[Abbr `tf`, Abbr `inst`, Abbr `sc`] >>
  conj_tac
  >- simp[lookup_var_def, mcopy_def, write_memory_with_expansion_def] >>
  conj_tac >- simp[mcopy_mem_bytes_at_same] >>
  conj_tac
  >- (gen_tac >> disch_tac >> conj_tac
      >- (irule mcopy_mem_bytes_at_disjoint >> decide_tac) >>
      eq_tac >> strip_tac >> gvs[] >>
      metis_tac[ADD_COMM, LE_ADD, LESS_MONO_ADD]) >>
  rpt strip_tac >> irule robust_val_in_memory_copy_transport >>
  conj_tac >- simp[] >>
  qexistsl [`s.vs_memory`, `(mcopy (w2n b) (w2n a) (SUC k) s).vs_memory`,
    `SUC k`, `w2n a`, `tn.t_mem`,
    `tn.t_mem DIFF {i | w2n b <= i /\ i < SUC k + w2n b} UNION
     {i + w2n b | i < SUC k /\ i + w2n a IN tn.t_mem}`] >>
  simp[mcopy_mem_bytes_at_same]
QED
