(* Counted copies retain source taint; they do not manufacture cleanliness. *)
Theory bodyPtrStructLitCopyPath
Ancestors robustCopyTransportPtr batchCopyRobustPtr fragGasSeqPtr fragExecPtr fragGasPathPtr
  typedCopyPtr venomInst venomExecSemantics venomState ptrDiscipline words
  fragExec emitHelperProps context emitHelper compileEnv valueEncodingProps pred_set

Theorem mcopy_operand_counted_path:
  !D ctx fn PG G tn s bb id dst src n a b.
    ~s.vs_halted /\
    lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
    get_instruction bb s.vs_inst_idx =
      SOME (mk_inst id MCOPY [Var dst; Var src; Lit (n2w n)] []) /\
    lookup_var src s = SOME a /\ lookup_var dst s = SOME b /\
    n < dimword(:256) /\ ptr_covers G tn src s n /\
    ptr_covers G tn dst s n /\ ~ctx_has_dalloca ctx ==>
    gas_path_ptr D 0 ctx fn PG G tn s 0
      (step_prov PG G (mk_inst id MCOPY [Var dst; Var src; Lit (n2w n)] [])
        (mcopy (w2n b) (w2n a) n s))
      (step_taint (mk_inst id MCOPY [Var dst; Var src; Lit (n2w n)] [])
        s (mcopy (w2n b) (w2n a) n s) tn)
      (OK ((mcopy (w2n b) (w2n a) n s) with vs_inst_idx := SUC s.vs_inst_idx))
Proof
  rpt gen_tac >> strip_tac >>
  `gas_path_ptr_edge D 0 ctx fn PG G tn s 0
      (step_prov PG G (mk_inst id MCOPY [Var dst; Var src; Lit (n2w n)] [])
        (mcopy (w2n b) (w2n a) n s))
      (step_taint (mk_inst id MCOPY [Var dst; Var src; Lit (n2w n)] [])
        s (mcopy (w2n b) (w2n a) n s) tn)
      (OK ((mcopy (w2n b) (w2n a) n s) with vs_inst_idx := SUC s.vs_inst_idx))` by
    (qpat_assum `get_instruction _ _ = SOME _`
       (mp_then Any mp_tac straight_line_ptr_edge) >>
     simp[mk_inst_def, is_terminator_def] >> disch_then irule >>
     conj_tac
     >- simp[step_inst_base_opcode_eqs, mk_inst_def, eval_operand_def, w2n_n2w] >>
     conj_tac >- simp[] >>
     irule (SRULE [mk_inst_def] ptr_inst_ok_mcopy_operand) >>
     simp[eval_operand_def, op_taint_def, w2n_n2w]) >>
  drule (cj 2 gas_path_ptr_rules) >>
  disch_then (qspec_then `0` mp_tac) >> simp[] >>
  disch_then irule >> irule (cj 1 gas_path_ptr_rules) >>
  simp[mcopy_def, write_memory_with_expansion_def]
QED

Theorem copy_memory_emitted_code:
  !dst src n sa sb.
    compile_copy_memory dst src n sa = ((),sb) ==>
    sb.cs_current_bb = sa.cs_current_bb /\
    sb.cs_current_insts = sa.cs_current_insts ++
      (if n = 0 then [] else
       [mk_inst sa.cs_next_id MCOPY [dst; src; Lit (n2w n)] []])
Proof
  rpt gen_tac >> Cases_on `n` >>
  simp[compile_copy_memory_def, comp_return_def, emit_void_def,
    emit_inst_def, fresh_id_def, emit_def, comp_bind_def,
    comp_ignore_bind_def] >> strip_tac >> gvs[]
QED

Theorem copy_memory_emitted_instruction:
  !dst src n sa sb fn.
    compile_copy_memory dst src n sa = ((),sb) /\ n <> 0 /\
    fn_has_code sa sb fn ==>
    sb.cs_current_bb = sa.cs_current_bb /\
    LENGTH sb.cs_current_insts = SUC (LENGTH sa.cs_current_insts) /\
    ?bb. lookup_block sa.cs_current_bb fn.fn_blocks = SOME bb /\
      get_instruction bb (LENGTH sa.cs_current_insts) =
        SOME (mk_inst sa.cs_next_id MCOPY [dst; src; Lit (n2w n)] [])
Proof
  rpt gen_tac >> strip_tac >>
  drule copy_memory_emitted_code >> strip_tac >> gvs[] >>
  drule_all fn_has_code_same_block >> strip_tac >>
  qexists_tac `bb` >> simp[] >>
  first_x_assum (qspec_then `0` mp_tac) >> simp[]
QED

Theorem compile_copy_memory_robust_counted:
 !D ctx fn PG sa sb src dst n G tn s a b tv v.
  compile_copy_memory (Var dst) (Var src) n sa = ((),sb) /\
  fn_has_code sa sb fn /\ ~ctx_has_dalloca ctx /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  lookup_var src s = SOME a /\ lookup_var dst s = SOME b /\
  n < dimword(:256) /\
  ptr_covers G tn src s n /\ ptr_covers G tn dst s n /\
  val_wf tv v /\ val_footprint tv v <= n /\
  (!m. mem_agree_outside tn.t_mem s.vs_memory m ==>
       val_in_memory tv v (w2n a) m) ==>
  ?Gf tnf sf.
   gas_path_ptr D 0 ctx fn PG G tn s 0 Gf tnf (OK sf) /\
   ~sf.vs_halted /\ sf.vs_current_bb = sb.cs_current_bb /\
   sf.vs_inst_idx = LENGTH sb.cs_current_insts /\
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
  >- (gvs[compile_copy_memory_def, comp_return_def] >>
      qexistsl_tac [`tn`, `s`] >> simp[] >>
      conj_tac >- (irule (cj 1 gas_path_ptr_rules) >> simp[]) >>
      simp[valueEncodingTheory.mem_bytes_at_def] >>
      rpt strip_tac >> irule robust_val_in_memory_copy_transport >>
      conj_tac >- simp[] >>
      qexistsl_tac [`s.vs_memory`, `s.vs_memory`, `0`, `w2n a`,
                    `tn.t_mem`, `tn.t_mem`] >>
      simp[valueEncodingTheory.mem_bytes_at_def]) >>
  suspend "positive"
QED

Resume compile_copy_memory_robust_counted[positive]:
  rename1 `compile_copy_memory _ _ (SUC k) _ = _` >>
  drule copy_memory_emitted_instruction >> simp[] >>
  disch_then drule >> strip_tac >>
  qabbrev_tac `inst = mk_inst sa.cs_next_id MCOPY
    [Var dst; Var src; Lit (n2w (SUC k))] []` >>
  qabbrev_tac `sc = mcopy (w2n b) (w2n a) (SUC k) s` >>
  qabbrev_tac `tf = step_taint inst s sc tn` >>
  qexistsl_tac [`tf`, `sc with vs_inst_idx := SUC s.vs_inst_idx`] >>
  conj_tac
  >- (map_every qunabbrev_tac [`tf`, `sc`, `inst`] >>
      pure_rewrite_tac [mk_inst_def] >>
      irule (SRULE [step_prov_def, set_prov_def, out_prov_def,
        mk_inst_def, finite_mapTheory.DRESTRICT_UNIV]
        mcopy_operand_counted_path) >>
      simp[mk_inst_def]) >>
  ntac 3 (conj_tac >-
    simp[Abbr `sc`, mcopy_def, write_memory_with_expansion_def]) >>
  suspend "frames"
QED

Resume compile_copy_memory_robust_counted[frames]:
  `eval_operand (Var dst) s = SOME b` by simp[eval_operand_def] >>
  `eval_operand (Var src) s = SOME a` by simp[eval_operand_def] >>
  `eval_operand (Lit (n2w (SUC k))) s = SOME (n2w (SUC k):bytes32)`
    by simp[eval_operand_def] >>
  qpat_assum `eval_operand (Var dst) s = SOME b`
    (mp_then Any mp_tac mcopy_operand_ghost_frame) >>
  disch_then (fn th => qpat_assum `eval_operand (Var src) s = SOME a`
    (mp_then Any mp_tac th)) >>
  disch_then (fn th => qpat_assum `eval_operand (Lit _) s = SOME _`
    (mp_then Any mp_tac th)) >>
  disch_then (qspecl_then [`PG`, `G`, `tn`, `sa.cs_next_id`] mp_tac) >>
  simp[w2n_n2w] >> strip_tac >>
  simp[Abbr `tf`, Abbr `inst`, Abbr `sc`] >>
  conj_tac
  >- simp[lookup_var_def, mcopy_def, write_memory_with_expansion_def] >>
  conj_tac >- simp[mcopy_mem_bytes_at_same] >>
  conj_tac
  >- (gen_tac >> disch_tac >> conj_tac
      >- (irule mcopy_mem_bytes_at_disjoint >> decide_tac) >>
      eq_tac >> strip_tac >> gvs[] >> metis_tac[arithmeticTheory.ADD_COMM,
        arithmeticTheory.LE_ADD, arithmeticTheory.LESS_MONO_ADD]) >>
  rpt strip_tac >> irule robust_val_in_memory_copy_transport >>
  conj_tac >- simp[] >>
  qexistsl_tac [`s.vs_memory`, `(mcopy (w2n b) (w2n a) (SUC k) s).vs_memory`,
    `SUC k`, `w2n a`, `tn.t_mem`,
    `tn.t_mem DIFF {i | w2n b <= i /\ i < SUC k + w2n b} UNION
     {i + w2n b | i < SUC k /\ i + w2n a IN tn.t_mem}`] >>
  simp[mcopy_mem_bytes_at_same]
QED

Finalise compile_copy_memory_robust_counted
