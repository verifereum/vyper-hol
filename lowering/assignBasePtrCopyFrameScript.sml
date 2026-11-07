(* Counted MCOPY and its frame share the explicit execution endpoint. *)
Theory assignBasePtrCopyFrame
Ancestors assignBasePtrCopyPath typedMemoryCopy valueCopy
  fragGasPathPtr bodyPtrDefs context words compileEnv valueEncoding

Theorem assign_base_copy_memory_framed_robust_path_ptr:
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
      typed_copy_state_frame sa (w2n d) n s u /\
      (!m. mem_agree_outside tf.t_mem u.vs_memory m ==>
           val_in_memory tv v (w2n d) m)
Proof
  rpt gen_tac >> strip_tac >> Cases_on `n = 0`
  >- (gvs[compile_copy_memory_def, comp_return_def] >>
      qexistsl_tac [`G`, `tn`, `s`] >>
      simp[cj 1 gas_path_ptr_rules] >> rpt strip_tac >>
      irule val_in_memory_relocate >> simp[] >>
      qexistsl_tac [`w2n a`, `0`, `m`] >> simp[mem_bytes_at_def]) >>
  `0 < n` by decide_tac >>
  drule_all (SRULE [] assign_base_copy_memory_robust_endpoint_ptr) >>
  disch_then (qspecl_then [`D`, `PG`] strip_assume_tac) >>
  qpat_assum `gas_path_ptr _ _ _ _ _ _ _ _ _ _ _ _`
    (irule_at Any) >> simp[typed_copy_mcopy_state_frame]
QED
