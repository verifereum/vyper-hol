(* ABI-static array staging: static rigidity supplies representation identity. *)
Theory bodyPtrIntCallStaticArrayCopy
Ancestors
  bodyPtrIntCallFixedCopy bodyPtrStructLitCopyPath
  typedNormalizeStaticRigidity assignTuplePtrLocalFixedCopy
  valueEncodingTyping exprSimProps typedCopyPtr
  context emitHelper compileEnv valueEncodingProps venomMemDefs
  venomExecSemantics finite_map pred_set words fragGasPathPtr
  annAssignPtrCopy robustCopyTransportPtr venomState ptrDiscipline

Theorem intcall_static_array_fast_counted:
  !D ctx fn PG ce sa sb src dst st dt tenv stv dtv cnt v G tn s a b.
    compile_copy_sarray_typed ce (Var dst) dt (Var src) st cnt sa = ((),sb) /\
    arg_type_fits st dt /\ ~is_abi_dynamic ce.ce_struct_fields dt /\
    type_memory_bytes ce st = type_memory_bytes ce dt /\
    evaluate_type tenv st = SOME stv /\ evaluate_type tenv dt = SOME dtv /\
    type_memory_bytes ce dt = type_memory_size dtv /\
    value_has_type (ArrayTV stv (Fixed cnt)) v /\
    fn_has_code sa sb fn /\
    lookup_var src s = SOME a /\ lookup_var dst s = SOME b /\
    ptr_covers G tn src s (cnt * type_memory_size stv) /\
    ptr_covers G tn dst s (cnt * type_memory_size dtv) /\
    w2n a + val_footprint (ArrayTV stv (Fixed cnt)) v < dimword (:256) /\
    w2n b + cnt * type_memory_size dtv < dimword (:256) /\
    (!m. mem_agree_outside tn.t_mem s.vs_memory m ==>
      val_in_memory (ArrayTV stv (Fixed cnt)) v (w2n a) m) /\
    ~ctx_has_dalloca ctx /\ ~s.vs_halted /\
    s.vs_current_bb = sa.cs_current_bb /\
    s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
    ?H tf z.
      gas_path_ptr D 0 ctx fn PG G tn s 0 H tf (OK z) /\
      z.vs_current_bb = sb.cs_current_bb /\
      z.vs_inst_idx = LENGTH sb.cs_current_insts /\ ~z.vs_halted /\
      (!m. mem_agree_outside tf.t_mem z.vs_memory m ==>
        val_in_memory (ArrayTV dtv (Fixed cnt)) v (w2n b) m) /\
      tf.t_stor = tn.t_stor /\ tf.t_trans = tn.t_trans /\ tf.t_imm = tn.t_imm /\
      z.vs_allocas = s.vs_allocas /\ z.vs_alloca_next = s.vs_alloca_next /\
      z.vs_fmp = s.vs_fmp /\ z.vs_accounts = s.vs_accounts /\
      z.vs_transient = s.vs_transient /\ z.vs_call_ctx = s.vs_call_ctx /\
      (!x. lookup_var x z = lookup_var x s /\ FLOOKUP H x = FLOOKUP G x /\
        op_taint tf (Var x) = op_taint tn (Var x)) /\
      (!i. ~(w2n b <= i /\ i < w2n b + cnt * type_memory_size dtv) ==>
        mem_bytes_at i 1 z.vs_memory = mem_bytes_at i 1 s.vs_memory /\
        (i IN tf.t_mem <=> i IN tn.t_mem))
Proof
  rpt gen_tac >> strip_tac >>
  drule_all arg_type_fits_static_identity >> strip_tac >> gvs[] >>
  `val_wf (ArrayTV dtv (Fixed cnt)) v` by
    metis_tac[value_has_type_val_wf] >>
  `val_footprint (ArrayTV dtv (Fixed cnt)) v <= cnt * type_memory_size dtv` by
    (drule exprSimPropsTheory.val_footprint_le >> simp[valueEncodingTheory.type_memory_size_def]) >>
  `compile_copy_memory (Var dst) (Var src) (cnt * type_memory_size dtv) sa = ((),sb)` by
    gvs[Once compile_store_memory_typed_def] >>
  qabbrev_tac `n = cnt * type_memory_size dtv` >>
  `n < dimword (:256)` by decide_tac >>
  Cases_on `n = 0`
  >- (qpat_x_assum `compile_copy_memory _ _ _ _ = _` mp_tac >>
      asm_rewrite_tac[compile_copy_memory_def, comp_return_def] >>
      strip_tac >> gvs[] >>
      (qexistsl_tac [`G`, `tn`, `s`] >> simp[] >> conj_tac
       >- (irule (cj 1 gas_path_ptr_rules) >> simp[]) >>
       rpt strip_tac >> irule robust_val_in_memory_copy_transport >>
       conj_tac >- simp[] >>
       qexistsl_tac [`s.vs_memory`, `s.vs_memory`, `0`, `w2n a`, `tn.t_mem`, `tn.t_mem`] >>
       simp[valueEncodingTheory.mem_bytes_at_def])) >>
  drule_all copy_memory_emitted_instruction >> strip_tac >>
  qabbrev_tac `sc = mcopy (w2n b) (w2n a) n s` >>
  qabbrev_tac `inst = mk_inst sa.cs_next_id MCOPY [Var dst;Var src;Lit (n2w n)] []` >>
  qabbrev_tac `tf = step_taint inst s sc tn` >>
  qexistsl_tac [`G`, `tf`, `sc with vs_inst_idx := SUC s.vs_inst_idx`] >>
  conj_tac
  >- (simp[Abbr `tf`, Abbr `inst`, Abbr `sc`] >>
      qpat_assum `s.vs_inst_idx = _` (fn th => once_rewrite_tac[GSYM th]) >>
      irule (REWRITE_RULE [GSYM arithmeticTheory.ADD1] annassign_mcopy_path_ptr) >>
      simp[eval_operand_def, op_taint_def, w2n_n2w]) >>
  `tf.t_var = tn.t_var /\ tf.t_stor = tn.t_stor /\
   tf.t_trans = tn.t_trans /\ tf.t_imm = tn.t_imm /\
   (!i. i < n ==> (w2n b+i IN tf.t_mem <=> w2n a+i IN tn.t_mem)) /\
   (!i. ~(w2n b <= i /\ i < w2n b+n) ==> (i IN tf.t_mem <=> i IN tn.t_mem))` by
    (irule mcopy_operand_taint_frames_ptr >>
     qexistsl_tac [`Lit (n2w n)`, `Var dst`, `sa.cs_next_id`, `n2w n`, `s`, `Var src`] >>
     simp[Abbr `tf`, Abbr `inst`, Abbr `sc`, eval_operand_def, w2n_n2w]) >>
  `!m. mem_agree_outside tf.t_mem sc.vs_memory m ==>
    val_in_memory (ArrayTV dtv (Fixed cnt)) v (w2n b) m` by
    (rpt strip_tac >> irule robust_val_in_memory_copy_transport >>
     conj_tac >- simp[] >>
     qexistsl_tac [`s.vs_memory`, `sc.vs_memory`, `n`, `w2n a`, `tn.t_mem`, `tf.t_mem`] >>
     simp[Abbr `sc`, mcopy_mem_bytes_at_same]) >>
  `!i. ~(w2n b <= i /\ i < w2n b+n) ==>
    mem_bytes_at i 1 sc.vs_memory = mem_bytes_at i 1 s.vs_memory` by
    (rpt strip_tac >> simp[Abbr `sc`] >>
     irule mcopy_mem_bytes_at_disjoint >> decide_tac) >>
  simp[] >>
  simp[Abbr `sc`, mcopy_def, write_memory_with_expansion_def,
       lookup_var_def, op_taint_def]
QED
