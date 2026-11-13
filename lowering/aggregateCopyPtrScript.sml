(* Counted flat aggregate copying retains the concrete endpoint's full frame. *)
Theory aggregateCopyPtr
Ancestors
  assignBasePtrCopyPath assignBasePtrBytesPost typedMemoryCopy typedCopyPtr
  valueCopy valueEncoding valueEncodingDefs valueEncodingProps exprSimProps
  exprSimBufferStore exprLoweringProps context compileEnv bodyPtrDefs
  fragGasPathPtr ptrDiscipline venomState venomExecSemantics venomInst
  emitHelper emitHelperProps words finite_map pred_set list arithmetic

Theorem compile_copy_memory_counted_frame_ptr:
  !tv v n a b dst src dw sw fn G tn s ctx D PG.
    type_memory_size tv = n /\ val_wf tv v /\
    compile_copy_memory (Var dst) src n a = ((),b) /\
    not_fresh_at a dst /\ (!x. src = Var x ==> not_fresh_at a x) /\
    lookup_var dst s = SOME dw /\ eval_operand src s = SOME sw /\
    op_taint tn (Var dst) = {} /\ op_taint tn src = {} /\
    (0 < n ==> ptr_covers G tn dst s n) /\
    (0 < n ==> ?p. src = Var p /\ ptr_covers G tn p s n) /\
    w2n dw+n < dimword (:256) /\ w2n sw+n < dimword (:256) /\
    (!m. mem_agree_outside tn.t_mem s.vs_memory m ==>
      val_in_memory tv v (w2n sw) m) /\
    fn_has_code a b fn /\ s.vs_current_bb = a.cs_current_bb /\
    s.vs_inst_idx = LENGTH a.cs_current_insts /\ ~s.vs_halted /\
    ~ctx_has_dalloca ctx ==>
    ?H tt t.
      gas_path_ptr D 0 ctx fn PG G tn s 0 H tt (OK t) /\
      t.vs_current_bb = b.cs_current_bb /\
      t.vs_inst_idx = LENGTH b.cs_current_insts /\ ~t.vs_halted /\
      (!m. mem_agree_outside tt.t_mem t.vs_memory m ==>
        val_in_memory tv v (w2n dw) m) /\
      typed_copy_state_frame a (w2n dw) n s t /\
      (!x. not_fresh_at a x ==> lookup_var x t = lookup_var x s /\
        FLOOKUP H x = FLOOKUP G x /\ op_taint tt (Var x) = op_taint tn (Var x)) /\
      tt.t_stor = tn.t_stor /\ tt.t_trans = tn.t_trans /\ tt.t_imm = tn.t_imm /\
      (!i. ~(w2n dw <= i /\ i < w2n dw+n) ==>
        (i IN tt.t_mem <=> i IN tn.t_mem))
Proof
  rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
  `val_footprint tv v <= n` by metis_tac[val_footprint_le] >>
  qpat_x_assum `type_memory_size tv = n` kall_tac >>
  Cases_on `n = 0`
  >- (gnvs[compile_copy_memory_def, comp_return_def] >>
      qexistsl_tac [`G`,`tn`,`s`] >>
      simp[cj 1 gas_path_ptr_rules, typed_copy_state_frame_refl] >> rpt strip_tac >>
      irule valueCopyTheory.val_in_memory_relocate >> simp[] >>
      qexistsl_tac [`w2n sw`,`0`,`m`] >> simp[mem_bytes_at_def]) >>
  `0 < n` by decide_tac >>
  `?p. src = Var p /\ ptr_covers G tn p s n` by metis_tac[] >>
  gnvs[eval_operand_def] >>
  rename1 `compile_copy_memory (Var dst) (Var p) _ a = _` >>
  `n < dimword (:256)` by decide_tac >>
  drule_all assign_base_copy_memory_path_ptr >>
  disch_then (qspecl_then [`D`,`PG`] assume_tac) >>
  `b.cs_current_bb = a.cs_current_bb` by
    (drule buffer_copy_memory_shape >> simp[same_blocks_def] >> metis_tac[]) >>
  `eval_operand (Var dst) s = SOME dw /\
   eval_operand (Var p) s = SOME sw /\
   eval_operand (Lit (n2w n)) s = SOME (n2w n) /\
   (s with vs_vars := s.vs_vars) = s /\
   (!x. not_fresh_at a x ==> lookup_var x s = lookup_var x s) /\
   val_footprint tv v <= w2n (n2w n:bytes32)` by simp[eval_operand_def] >>
  qabbrev_tac `u = mcopy (w2n dw) (w2n sw) n s` >>
  qabbrev_tac `tf = step_taint
    (mk_inst a.cs_next_id MCOPY [Var dst;Var p;Lit (n2w n)] []) s u tn` >>
  `u.vs_current_bb = b.cs_current_bb /\ ~u.vs_halted` by
    simp[Abbr `u`, mcopy_def, write_memory_with_expansion_def] >>
  `u = mcopy (w2n dw) (w2n sw) (w2n (n2w n:bytes32)) s /\
   tf = step_taint
    (mk_inst a.cs_next_id MCOPY [Var dst;Var p;Lit (n2w n)] []) s u tn` by
    simp[Abbr `u`, Abbr `tf`] >>
  mp_tac (Q.SPECL [`Var dst`,`Var p`,`Lit (n2w n)`,
    `s`,`s`,`dw`,`sw`,`n2w n`,`a.cs_next_id`,
    `u`,`tn`,`tf`,`PG`,`G`,`a`,`tv`,`v`,`LENGTH b.cs_current_insts`]
      assign_base_bytes_mcopy_post) >>
  (impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)) >> strip_tac >>
  qpat_x_assum `u = mcopy _ _ _ _` kall_tac >>
  qpat_x_assum `tf = step_taint _ _ _ _` kall_tac >>
  `gas_path_ptr D 0 ctx fn PG G tn s 0 G tf
    (OK (u with vs_inst_idx := LENGTH b.cs_current_insts))` by metis_tac[] >>
  `!x. op_taint tf (Var x) = op_taint tn (Var x)` by simp[op_taint_def] >>
  qexistsl_tac [`G`,`tf`,`u with vs_inst_idx := LENGTH b.cs_current_insts`] >>
  gnvs[w2n_n2w, LESS_MOD] >>
  rpt strip_tac >>
  metis_tac[DECIDE ``~(d <= i /\ i < d+n) ==> i < d \/ d+n <= i``, ADD_COMM]
QED
