(* Region-containment interfaces for the callee's memory certificate. *)
Theory bodyIntCallFrameBoundary
Ancestors
  intCallFrame compileEnv venomState valueEncoding list pair finite_map arithmetic

Theorem callee_writes_above_contained:
  !lo lo' excl excl' m m'.
    callee_writes_above lo' excl' m m' /\ lo <= lo' /\
    EVERY (\(b,n). lo <= b \/
      ?eb en. MEM (eb,en) excl /\ eb <= b /\ b+n <= eb+en) excl' ==>
    callee_writes_above lo excl m m'
Proof
  rw[callee_writes_above_def] >> first_x_assum irule >>
  gvs[EVERY_MEM, FORALL_PROD, regions_disjoint_def] >>
  rpt strip_tac >> res_tac >> gvs[] >>
  first_x_assum drule >> strip_tac >> decide_tac
QED

Theorem callee_writes_above_alloc_window:
  !lo excl allocs n m mem mem'.
    callee_writes_above lo excl mem mem' /\
    EVERY (\(eb,esz). lo <= eb \/
      ?aid off asz. FLOOKUP allocs aid = SOME (off,asz) /\
        n <= aid /\ aid < m /\ off <= eb /\ eb+esz <= off+asz) excl ==>
    !b sz. b+sz <= lo /\
      (!aid off asz. FLOOKUP allocs aid = SOME (off,asz) /\
         n <= aid /\ aid < m ==> regions_disjoint b sz off asz) ==>
      mem_bytes_at b sz mem' = mem_bytes_at b sz mem
Proof
  rpt gen_tac >> strip_tac >> rpt gen_tac >> strip_tac >>
  qpat_x_assum `callee_writes_above _ _ _ _`
    (irule o REWRITE_RULE [callee_writes_above_def]) >> simp[] >>
  gvs[EVERY_MEM, FORALL_PROD] >> rpt strip_tac >>
  first_x_assum drule >> strip_tac
  >- simp[regions_disjoint_def] >>
  first_x_assum drule_all >>
  simp[regions_disjoint_def] >> decide_tac
QED
