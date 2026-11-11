(* Counted flat copying transports a robust value without cleaning padding. *)
Theory typedCopyFlatPathPtr
Ancestors
  annAssignPtrCopy robustCopyTransportPtr bodyPtrDefs valueEncodingProofs
  valueEncodingDefs venomMemProofs venomState ptrDiscipline
  context emitHelper emitHelperProps fragExec finite_map pred_set arithmetic

Theorem compile_copy_memory_robust_path_ptr:
 !D ctx func PG G tn s dst src a b n sa sb tv v.
  compile_copy_memory (Var dst) (Var src) n sa = ((),sb) /\
  fn_has_code sa sb func /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  ~s.vs_halted /\ ~ctx_has_dalloca ctx /\ n < dimword (:256) /\
  lookup_var src s = SOME a /\ lookup_var dst s = SOME b /\
  ptr_covers G tn src s n /\ ptr_covers G tn dst s n /\
  val_wf tv v /\ val_footprint tv v <= n /\
  (!m. mem_agree_outside tn.t_mem s.vs_memory m ==>
       val_in_memory tv v (w2n a) m) ==>
  ?sf tnf.
   gas_path_ptr D 0 ctx func PG G tn s 0 G tnf (OK sf) /\
   sf.vs_current_bb = sb.cs_current_bb /\
   sf.vs_inst_idx = LENGTH sb.cs_current_insts /\ ~sf.vs_halted /\
   (sf with <|vs_memory := s.vs_memory; vs_inst_idx := s.vs_inst_idx|>) = s /\
   (tnf with t_mem := tn.t_mem) = tn /\
   (!p. lookup_var p sf = lookup_var p s) /\
   mem_bytes_at (w2n b) n sf.vs_memory = mem_bytes_at (w2n a) n s.vs_memory /\
   (!i. i < n ==> (w2n b+i IN tnf.t_mem <=> w2n a+i IN tn.t_mem)) /\
   (!i. ~(w2n b <= i /\ i < w2n b+n) ==>
     mem_bytes_at i 1 sf.vs_memory = mem_bytes_at i 1 s.vs_memory /\
     (i IN tnf.t_mem <=> i IN tn.t_mem)) /\
   (!m. mem_agree_outside tnf.t_mem sf.vs_memory m ==>
        val_in_memory tv v (w2n b) m)
Proof
 rpt gen_tac >> strip_tac >>
 drule_all annassign_compile_copy_path_ptr >>
 disch_then (qspecl_then [`D`,`PG`] strip_assume_tac) >>
 `mem_bytes_at (w2n b) n s'.vs_memory =
    mem_bytes_at (w2n a) n s.vs_memory` by
  (Cases_on `n = 0` >- simp[mem_bytes_at_def] >>
   simp[mcopy_mem_bytes_at_same]) >>
 `!i. i < n ==> (w2n b+i IN tn'.t_mem <=> w2n a+i IN tn.t_mem)` by
  (rpt strip_tac >> simp[] >> eq_tac >> strip_tac >> gvs[] >> decide_tac) >>
 `!i. ~(w2n b <= i /\ i < w2n b+n) ==>
    mem_bytes_at i 1 s'.vs_memory = mem_bytes_at i 1 s.vs_memory /\
    (i IN tn'.t_mem <=> i IN tn.t_mem)` by
  (gen_tac >> disch_tac >> conj_tac
   >- (Cases_on `n = 0` >> simp[] >>
       irule mcopy_mem_bytes_at_disjoint >> decide_tac) >>
   simp[] >> eq_tac >> strip_tac >> gvs[] >> decide_tac) >>
 qexistsl [`s'`,`tn'`] >> simp[] >> rpt strip_tac >>
 irule robust_val_in_memory_copy_transport >> conj_tac >- simp[] >>
 qexistsl [`s.vs_memory`,`s'.vs_memory`,`n`,`w2n a`,`tn.t_mem`,
   `tn'.t_mem`] >> simp[]
QED
