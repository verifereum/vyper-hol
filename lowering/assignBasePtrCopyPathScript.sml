(* Counted direct-copy staging, retaining the actual endpoint and ghost. *)
Theory assignBasePtrCopyPath
Ancestors assignBasePtrMcopy assignBasePtrMcopyTransport fragGasPathPtr
  fragGasSeqPtr context emitHelper emitHelperProps exprLoweringProps
  fragExec fragExecPtr venomExecSemantics venomState venomInst ptrDiscipline
  words list rich_list compileEnv exprSimMemoryTransport typedCopyPtr
  valueEncoding bodyPtrDefs finite_map

Theorem assign_base_copy_memory_code:
  !dst src n sa sb fn s.
    0 < n /\ compile_copy_memory dst src n sa = ((),sb) /\
    fn_has_code sa sb fn /\ s.vs_current_bb = sa.cs_current_bb /\
    s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
    ?bb. lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
      get_instruction bb s.vs_inst_idx =
        SOME (mk_inst sa.cs_next_id MCOPY [dst;src;Lit (n2w n)] []) /\
      LENGTH sb.cs_current_insts = SUC s.vs_inst_idx
Proof
  rpt gen_tac >> strip_tac >> Cases_on `n` >> gvs[] >>
  gvs[compile_copy_memory_def, emit_void_def, comp_bind_def,
      comp_ignore_bind_def, fresh_id_def, emit_def, comp_return_def,
      fn_has_code_def, IS_PREFIX_APPEND] >>
  simp[get_instruction_def, EL_APPEND_EQN]
QED

Theorem assign_base_copy_memory_path_ptr:
  !dst src n sa sb fn s d a G tn D ctx PG.
    0 < n /\ n < dimword (:256) /\
    compile_copy_memory (Var dst) (Var src) n sa = ((),sb) /\
    fn_has_code sa sb fn /\ s.vs_current_bb = sa.cs_current_bb /\
    s.vs_inst_idx = LENGTH sa.cs_current_insts /\ ~s.vs_halted /\
    ~ctx_has_dalloca ctx /\ ptr_covers G tn dst s n /\
    ptr_covers G tn src s n /\
    lookup_var dst s = SOME d /\ lookup_var src s = SOME a ==>
    gas_path_ptr D 0 ctx fn PG G tn s 0
      (step_prov PG G
        (mk_inst sa.cs_next_id MCOPY [Var dst;Var src;Lit (n2w n)] [])
        (mcopy (w2n d) (w2n a) n s))
      (step_taint
        (mk_inst sa.cs_next_id MCOPY [Var dst;Var src;Lit (n2w n)] [])
        s (mcopy (w2n d) (w2n a) n s) tn)
      (OK ((mcopy (w2n d) (w2n a) n s) with
        vs_inst_idx := LENGTH sb.cs_current_insts))
Proof
  rpt gen_tac >> strip_tac >>
  drule_all assign_base_copy_memory_code >> strip_tac >>
  `step_inst_base
     (mk_inst sa.cs_next_id MCOPY [Var dst;Var src;Lit (n2w n)] []) s =
     OK (mcopy (w2n d) (w2n a) n s)` by
    (PURE_ONCE_REWRITE_TAC[step_inst_base_def] >>
     simp[mk_inst_def, eval_operand_def]) >>
  `ptr_inst_ok D 0 0 ctx fn G tn
     (mk_inst sa.cs_next_id MCOPY [Var dst;Var src;Lit (n2w n)] []) s` by
    (irule ptr_inst_ok_mcopy_operand >> simp[eval_operand_def, op_taint_def]) >>
  irule (SRULE [mk_inst_def, is_terminator_def]
    (Q.INST [`n` |-> `0`, `lo` |-> `0`,
      `i` |-> `mk_inst sa.cs_next_id MCOPY [Var dst;Var src;Lit (n2w n)] []`]
      gas_path_ptr_step)) >>
  simp[GSYM mk_inst_def] >>
  goal_assum (drule_at Any) >> gvs[] >>
  irule (cj 1 gas_path_ptr_rules) >> simp[]
QED

Theorem assign_base_copy_memory_robust_endpoint_ptr:
  !dst src n sa sb fn s d a G tn D ctx PG tv v u Gf tf.
    0 < n /\ n < dimword (:256) /\
    compile_copy_memory (Var dst) (Var src) n sa = ((),sb) /\
    fn_has_code sa sb fn /\ s.vs_current_bb = sa.cs_current_bb /\
    s.vs_inst_idx = LENGTH sa.cs_current_insts /\ ~s.vs_halted /\
    ~ctx_has_dalloca ctx /\ ptr_covers G tn dst s n /\
    ptr_covers G tn src s n /\
    lookup_var dst s = SOME d /\ lookup_var src s = SOME a /\
    val_wf tv v /\ val_footprint tv v <= n /\
    (!m. mem_agree_outside tn.t_mem s.vs_memory m ==>
         val_in_memory tv v (w2n a) m) /\
    u = ((mcopy (w2n d) (w2n a) n s) with
         vs_inst_idx := LENGTH sb.cs_current_insts) /\
    Gf = step_prov PG G
      (mk_inst sa.cs_next_id MCOPY [Var dst;Var src;Lit (n2w n)] [])
      (mcopy (w2n d) (w2n a) n s) /\
    tf = step_taint
      (mk_inst sa.cs_next_id MCOPY [Var dst;Var src;Lit (n2w n)] [])
      s (mcopy (w2n d) (w2n a) n s) tn ==>
    gas_path_ptr D 0 ctx fn PG G tn s 0 Gf tf (OK u) /\
    (!m. mem_agree_outside tf.t_mem u.vs_memory m ==>
         val_in_memory tv v (w2n d) m)
Proof
  rpt gen_tac >> strip_tac >> gvs[] >> conj_tac
  >- (irule assign_base_copy_memory_path_ptr >> simp[]) >>
  mp_tac (Q.SPECL [`Var dst`, `Var src`, `Lit (n2w n)`, `s`,
    `d`, `a`, `n2w n`] assign_base_mcopy_robust_destination) >>
  simp[eval_operand_def] >>
  disch_then (qspecl_then [`sa.cs_next_id`, `tn`, `tv`, `v`] mp_tac) >>
  simp[]
QED


Theorem assign_base_copy_memory_robust_path_ptr:
  !dst src n sa sb fn s d a G tn D ctx PG tv v.
    n < dimword (:256) /\
    compile_copy_memory (Var dst) (Var src) n sa = ((),sb) /\
    fn_has_code sa sb fn /\ s.vs_current_bb = sa.cs_current_bb /\
    s.vs_inst_idx = LENGTH sa.cs_current_insts /\ ~s.vs_halted /\
    ~ctx_has_dalloca ctx /\ ptr_covers G tn dst s n /\
    ptr_covers G tn src s n /\
    lookup_var dst s = SOME d /\ lookup_var src s = SOME a /\
    val_wf tv v /\ val_footprint tv v <= n /\
    (!m. mem_agree_outside tn.t_mem s.vs_memory m ==>
         val_in_memory tv v (w2n a) m) ==>
    ?Gf tf u. gas_path_ptr D 0 ctx fn PG G tn s 0 Gf tf (OK u) /\
      (!m. mem_agree_outside tf.t_mem u.vs_memory m ==>
           val_in_memory tv v (w2n d) m)
Proof
  rpt gen_tac >> strip_tac >> Cases_on `n = 0`
  >- (gvs[compile_copy_memory_def, comp_return_def] >>
      qexistsl_tac [`G`, `tn`, `s`] >>
      simp[cj 1 gas_path_ptr_rules] >> rpt strip_tac >>
      irule valueCopyTheory.val_in_memory_relocate >> simp[] >>
      qexistsl_tac [`w2n a`, `0`, `m`] >> simp[mem_bytes_at_def]) >>
  `0 < n` by decide_tac >>
  drule_all (SRULE [] assign_base_copy_memory_robust_endpoint_ptr) >>
  disch_then (qspecl_then [`D`, `PG`] strip_assume_tac) >>
  qpat_assum `gas_path_ptr _ _ _ _ _ _ _ _ _ _ _ _`
    (irule_at Any) >> simp[]
QED
