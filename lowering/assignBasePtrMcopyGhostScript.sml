(* MCOPY frames the ghost outside its natural destination interval. *)
Theory assignBasePtrMcopyGhost
Ancestors assignBasePtrCopyPath assignBasePtrMcopyTransport
  assignBasePtrLiteralGhost assignBasePtrLiteralOutcome bodyPtrDefs
  typedCopyPtr robustCopyTransportPtr localPtrsProps exprLoweringProps
  venomState venomExecSemantics venomInst ptrDiscipline words pred_set
  valueEncodingProps valueEncodingProofs finite_map ghostPcTransportPtr allocationPtr compileEnv loweringStateRelDefs venomMemProofs

Theorem assign_base_mcopy_imm_taint[local]:
  !tn s id dst src count_op b a n.
    (step_taint (mk_inst id MCOPY [dst;src;count_op] []) s
      (mcopy b a n s) tn).t_imm = tn.t_imm
Proof
  rpt gen_tac >>
  simp[step_taint_def, mk_inst_def, set_var_taint_def, store_taint_def,
       adopt_reset_def, step_writes_def, written_taint_def, imm_taint_def]
QED

Theorem assign_base_mcopy_ghost_inv:
  !func kind cenv cx es PG G tn s id dst src count_op b a n.
    local_ptrs_rel func cenv es.scopes s /\
    ghost_inv kind cenv cx es G tn s /\
    eval_operand dst s = SOME b /\ eval_operand src s = SOME a /\
    eval_operand count_op s = SOME n /\
    (!name base sz. local_region cenv es.scopes s name base sz ==>
      regions_disjoint (w2n b) (w2n n) base sz) ==>
    ghost_inv kind cenv cx es
      (step_prov PG G (mk_inst id MCOPY [dst;src;count_op] [])
        (mcopy (w2n b) (w2n a) (w2n n) s))
      (step_taint (mk_inst id MCOPY [dst;src;count_op] []) s
        (mcopy (w2n b) (w2n a) (w2n n) s) tn)
      (mcopy (w2n b) (w2n a) (w2n n) s)
Proof
  rpt gen_tac >> strip_tac >>
  mp_tac (SPEC_ALL mcopy_operand_ghost_frame) >> simp[] >> strip_tac >>
  asm_rewrite_tac[] >>
  qmatch_goalsub_abbrev_tac `ghost_inv kind cenv cx es G tf u` >>
  `tf.t_imm = tn.t_imm` by simp[Abbr `tf`, Abbr `u`, assign_base_mcopy_imm_taint] >>
  `!x. op_taint tf (Var x) = op_taint tn (Var x)` by simp[Abbr `tf`, op_taint_def] >>
  `!x. lookup_var x u = lookup_var x s` by
    simp[Abbr `u`, mcopy_def, write_memory_with_expansion_def, lookup_var_def] >>
  `!p sz. ptr_covers G tn p s sz ==> ptr_covers G tf p u sz` by
    simp[ptr_covers_def, Abbr `u`, mcopy_def, write_memory_with_expansion_def] >>
  rewrite_tac[ghost_inv_def] >> conj_tac >- suspend "locals" >>
  qpat_x_assum `ghost_inv _ _ _ _ _ _ _` mp_tac >>
  simp[ghost_inv_def] >> strip_tac >> conj_tac
  >- (Cases_on `kind` >> simp[return_buf_ptr_def] >>
      PairCases_on `x` >> fs[return_buf_ptr_def] >> metis_tac[]) >>
  gvs[stor_taint_ok_def, Abbr `u`, mcopy_def, write_memory_with_expansion_def]
QED

Resume assign_base_mcopy_ghost_inv[locals]:
  rpt gen_tac >> strip_tac >> conj_tac
  >- (fs[ghost_inv_def] >> first_x_assum drule_all >> simp[]) >>
  rpt gen_tac >> strip_tac >>
  qabbrev_tac `writes = {i | w2n b <= i /\ i < w2n b + w2n n}` >>
  `!name base sz i. local_region cenv es.scopes s name base sz /\
      base <= i /\ i < base + sz ==> i NOTIN writes` by
    (rpt gen_tac >> strip_tac >>
     qpat_x_assum `!name base sz. _` drule >>
     simp[Abbr `writes`, regions_disjoint_def] >> decide_tac) >>
  `!i. i NOTIN writes ==> mem_bytes_at i 1 u.vs_memory = mem_bytes_at i 1 s.vs_memory` by
    (rpt strip_tac >> simp[Abbr `u`] >> irule mcopy_mem_bytes_at_disjoint >>
     fs[Abbr `writes`] >> decide_tac) >>
  `!i. i NOTIN writes ==> (i IN tf.t_mem <=> i IN tn.t_mem)` by
    (rpt strip_tac >> fs[Abbr `tf`, Abbr `writes`] >>
     eq_tac >> strip_tac >> gvs[] >> decide_tac) >>
  `lookup_var p s = SOME w` by metis_tac[] >>
  drule_all assign_base_ptr_local_robust_frame >> simp[]
QED

Finalise assign_base_mcopy_ghost_inv

Theorem assign_base_mcopy_ghost_kept:
  !cenv es frame_sa PG G tn s id dst src count_op b a n.
    eval_operand dst s = SOME b /\ eval_operand src s = SOME a /\
    eval_operand count_op s = SOME n /\
    (!aid off sz. FLOOKUP s.vs_allocas aid = SOME (off,sz) /\
       aid < frame_sa.cs_next_id /\
       (!name base len. local_region cenv es.scopes s name base len ==>
         off + sz <= base \/ base + len <= off) ==>
       regions_disjoint (w2n b) (w2n n) off sz) /\
    (!name base sz. local_region cenv es.scopes s name base sz ==>
      regions_disjoint (w2n b) (w2n n) base sz) ==>
    ghost_kept cenv es frame_sa G tn s
      (step_prov PG G (mk_inst id MCOPY [dst;src;count_op] [])
        (mcopy (w2n b) (w2n a) (w2n n) s))
      (step_taint (mk_inst id MCOPY [dst;src;count_op] []) s
        (mcopy (w2n b) (w2n a) (w2n n) s) tn)
Proof
  rpt gen_tac >> strip_tac >>
  mp_tac (SPEC_ALL mcopy_operand_ghost_frame) >> simp[] >> strip_tac >>
  simp[ghost_kept_def, op_taint_def] >> conj_tac
  >- (rpt strip_tac >>
      qpat_x_assum `!aid off sz. _` drule_all >>
      fs[regions_disjoint_def] >> gvs[] >> decide_tac) >>
  rpt strip_tac >> qpat_x_assum `!name base sz. _` drule >>
  fs[regions_disjoint_def] >> gvs[] >> decide_tac
QED


Theorem assign_base_mcopy_nat_ghost_inv:
  !func kind cenv cx es PG G tn s id dst src b a nn.
    local_ptrs_rel func cenv es.scopes s /\ ghost_inv kind cenv cx es G tn s /\
    lookup_var dst s = SOME b /\ lookup_var src s = SOME a /\
    nn < dimword (:256) /\
    (!name base sz. local_region cenv es.scopes s name base sz ==>
      regions_disjoint (w2n b) nn base sz) ==>
    ghost_inv kind cenv cx es
      (step_prov PG G (mk_inst id MCOPY [Var dst;Var src;Lit (n2w nn)] [])
        (mcopy (w2n b) (w2n a) nn s))
      (step_taint (mk_inst id MCOPY [Var dst;Var src;Lit (n2w nn)] []) s
        (mcopy (w2n b) (w2n a) nn s) tn)
      (mcopy (w2n b) (w2n a) nn s)
Proof
  rpt gen_tac >> strip_tac >> qabbrev_tac `cw = (n2w nn : bytes32)` >>
  `w2n cw = nn` by simp[Abbr `cw`, w2n_n2w] >>
  `n2w nn = cw` by simp[Abbr `cw`] >>
  asm_rewrite_tac[] >>
  qpat_assum `w2n cw = nn` (fn th => once_rewrite_tac[GSYM th]) >>
  irule assign_base_mcopy_ghost_inv >> simp[eval_operand_def] >> metis_tac[]
QED

Theorem assign_base_mcopy_nat_ghost_kept:
  !cenv es frame_sa PG G tn s id dst src b a nn.
    lookup_var dst s = SOME b /\ lookup_var src s = SOME a /\
    nn < dimword (:256) /\
    (!aid off sz. FLOOKUP s.vs_allocas aid = SOME (off,sz) /\
       aid < frame_sa.cs_next_id /\
       (!name base len. local_region cenv es.scopes s name base len ==>
         off + sz <= base \/ base + len <= off) ==>
       regions_disjoint (w2n b) nn off sz) /\
    (!name base sz. local_region cenv es.scopes s name base sz ==>
      regions_disjoint (w2n b) nn base sz) ==>
    ghost_kept cenv es frame_sa G tn s
      (step_prov PG G (mk_inst id MCOPY [Var dst;Var src;Lit (n2w nn)] [])
        (mcopy (w2n b) (w2n a) nn s))
      (step_taint (mk_inst id MCOPY [Var dst;Var src;Lit (n2w nn)] []) s
        (mcopy (w2n b) (w2n a) nn s) tn)
Proof
  rpt gen_tac >> strip_tac >> qabbrev_tac `cw = (n2w nn : bytes32)` >>
  `w2n cw = nn` by simp[Abbr `cw`, w2n_n2w] >>
  `n2w nn = cw` by simp[Abbr `cw`] >> asm_rewrite_tac[] >>
  qpat_assum `w2n cw = nn` (fn th => once_rewrite_tac[GSYM th]) >>
  irule assign_base_mcopy_ghost_kept >> simp[eval_operand_def] >> metis_tac[]
QED

Theorem assign_base_copy_memory_ghost_endpoint_ptr:
  !dst src n sa sb fn s b a G tn D ctx PG tv v u Gf tf kind cenv cx es frame_sa.
    0 < n /\ n < dimword (:256) /\
    compile_copy_memory (Var dst) (Var src) n sa = ((),sb) /\
    fn_has_code sa sb fn /\ s.vs_current_bb = sa.cs_current_bb /\
    s.vs_inst_idx = LENGTH sa.cs_current_insts /\ ~s.vs_halted /\
    ~ctx_has_dalloca ctx /\ ptr_covers G tn dst s n /\
    ptr_covers G tn src s n /\
    lookup_var dst s = SOME b /\ lookup_var src s = SOME a /\
    val_wf tv v /\ val_footprint tv v <= n /\
    (!m. mem_agree_outside tn.t_mem s.vs_memory m ==>
      val_in_memory tv v (w2n a) m) /\
    u = ((mcopy (w2n b) (w2n a) n s) with
      vs_inst_idx := LENGTH sb.cs_current_insts) /\
    Gf = step_prov PG G
      (mk_inst sa.cs_next_id MCOPY [Var dst;Var src;Lit (n2w n)] [])
      (mcopy (w2n b) (w2n a) n s) /\
    tf = step_taint
      (mk_inst sa.cs_next_id MCOPY [Var dst;Var src;Lit (n2w n)] [])
      s (mcopy (w2n b) (w2n a) n s) tn /\
    local_ptrs_rel fn cenv es.scopes s /\ ghost_inv kind cenv cx es G tn s /\
    (!name base sz. local_region cenv es.scopes s name base sz ==>
      regions_disjoint (w2n b) n base sz) /\
    (!aid off sz. FLOOKUP s.vs_allocas aid = SOME (off,sz) /\
       aid < frame_sa.cs_next_id /\
       (!name base len. local_region cenv es.scopes s name base len ==>
         off + sz <= base \/ base + len <= off) ==>
       regions_disjoint (w2n b) n off sz) ==>
    gas_path_ptr D 0 ctx fn PG G tn s 0 Gf tf (OK u) /\
    (!m. mem_agree_outside tf.t_mem u.vs_memory m ==>
      val_in_memory tv v (w2n b) m) /\
    ghost_inv kind cenv cx es Gf tf u /\
    ghost_kept cenv es frame_sa G tn s Gf tf
Proof
  rpt gen_tac >> strip_tac >>
  drule_all assign_base_copy_memory_robust_endpoint_ptr >>
  disch_then (qspec_then `D` strip_assume_tac) >>
  simp[] >> gvs[] >> simp[assign_base_ptr_ghost_index] >> conj_tac
  >- (irule assign_base_mcopy_nat_ghost_inv >> simp[] >> metis_tac[]) >>
  irule assign_base_mcopy_nat_ghost_kept >> simp[] >> metis_tac[]
QED
