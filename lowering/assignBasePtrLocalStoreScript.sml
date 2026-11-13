(* Robust value boundary for a scalar write to an existing local. *)
Theory assignBasePtrLocalStore
Ancestors assignBasePtrWordStore assignBasePtrLiteralGhost stmtSimAssignStore
  robustCopyTransportPtr typedCopyPtr bodyPtrDefs valueEncodingProofs
  valueEncodingProps ptrDiscipline venomMemProofs venomState venomInst
  pred_set words list exprSimMemoryTransport exprLoweringProps compileEnv
  vyperLookup finite_map localPtrsProps

Theorem assign_base_ptr_clean_window_robust_value:
  !tv v a n tn memory mem.
    val_wf tv v /\ val_footprint tv v <= n /\
    val_in_memory tv v a memory /\
    mem_agree_outside (tn DIFF {i | a <= i /\ i < a + n}) memory mem ==>
    val_in_memory tv v a mem
Proof
  rpt gen_tac >> strip_tac >>
  irule val_in_memory_relocate_footprint >> conj_tac >- simp[] >>
  qexistsl_tac [`memory`, `a`] >> simp[] >>
  irule LIST_EQ >> simp[] >> rpt strip_tac >>
  gvs[EL_mem_bytes_at, mem_agree_outside_def] >>
  qpat_x_assum `!i. _ ==> mem_bytes_at i 1 _ = _`
    (qspec_then `a+x` mp_tac) >>
  simp[LIST_EQ_REWRITE, EL_mem_bytes_at] >> decide_tac
QED

