(* The emitted batch copy transports robust representations, including padding. *)
Theory batchCopyRobustPtr
Ancestors typedCopyPtr robustCopyTransportPtr valueEncodingProps
  context emitHelper emitHelperProps pred_set compileEnv
  venomState venomInst venomExecSemantics ptrDiscipline

Theorem compile_copy_memory_robust_frag_ptr:
 !cx ctx PG R sa sb src dst n G tn s a b tv v.
  compile_copy_memory (Var dst) (Var src) n sa = ((),sb) /\
  lookup_var src s = SOME a /\ lookup_var dst s = SOME b /\
  n < dimword(:256) /\
  ptr_covers G tn src s n /\ ptr_covers G tn dst s n /\
  val_wf tv v /\ val_footprint tv v <= n /\
  (!m. mem_agree_outside tn.t_mem s.vs_memory m ==>
       val_in_memory tv v (w2n a) m) ==>
  ?Gf tnf sf.
   frag_exec_ptr cx ctx PG sa sb
     (\g t st. g = G /\ t = tn /\ st = s)
     (\g t st. g = Gf /\ t = tnf /\ st = sf) R /\
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
      conj_tac
      >- (simp[bodyPtrDefsTheory.frag_exec_ptr_def] >> rpt strip_tac >>
          disj1_tac >> metis_tac[]) >>
      simp[valueEncodingTheory.mem_bytes_at_def] >>
      rpt strip_tac >> irule robust_val_in_memory_copy_transport >>
      conj_tac >- simp[] >>
      qexistsl_tac [`s.vs_memory`, `s.vs_memory`, `0`, `w2n a`,
                    `tn.t_mem`, `tn.t_mem`] >>
      simp[valueEncodingTheory.mem_bytes_at_def]) >>
  suspend "positive"
QED

Resume compile_copy_memory_robust_frag_ptr[positive]:
  rename1 `compile_copy_memory _ _ (SUC k) _ = _` >>
  qabbrev_tac `inst = mk_inst sa.cs_next_id MCOPY
    [Var dst; Var src; Lit (n2w (SUC k))] []` >>
  qabbrev_tac `sc = mcopy (w2n b) (w2n a) (SUC k) s` >>
  qabbrev_tac `tf = step_taint inst s sc tn` >>
  qexistsl_tac [`G`, `tf`, `sc with vs_inst_idx := SUC s.vs_inst_idx`] >>
  conj_tac
  >- (irule mcopy_operand_frag_ptr >>
      conj_tac
      >- (gvs[compile_copy_memory_def, emit_void_def, emit_inst_def,
              fresh_id_def, emit_def, comp_bind_def, comp_return_def]) >>
      qexistsl_tac [`Lit (n2w (SUC k))`, `dst`, `sa.cs_next_id`, `src`] >>
      conj_tac
      >- (simp[] >> rpt strip_tac >> gvs[] >>
          qexists_tac `n2w (SUC k)` >>
          simp[eval_operand_def, op_taint_def, wordsTheory.w2n_n2w,
               Abbr `tf`, Abbr `inst`, Abbr `sc`] >>
          simp[step_prov_def, set_prov_def, out_prov_def,
               mk_inst_def, finite_mapTheory.DRESTRICT_UNIV]) >>
      gvs[compile_copy_memory_def, emit_void_def, emit_inst_def,
          fresh_id_def, emit_def, comp_bind_def, comp_return_def]) >>
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
  simp[wordsTheory.w2n_n2w] >>
  strip_tac >>
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

Finalise compile_copy_memory_robust_frag_ptr
