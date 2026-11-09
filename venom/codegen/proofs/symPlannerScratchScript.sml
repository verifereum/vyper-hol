(* Occurrence-indexed scratch slots: operand equality is immaterial. *)
Theory symPlannerScratch
Ancestors
  symPlannerBase doSwapSim contextCodegenRelProps list rich_list

Definition scratch_kinds_ok_def:
  scratch_kinds_ok fn ret items offsets labs <=>
  LIST_REL (\op off. ?sv. op_kind_ok fn ret op sv /\ mem_sval_at labs off sv)
    items offsets
End

Theorem scratch_kinds_ok_nil:
  scratch_kinds_ok fn ret [] [] labs
Proof
  simp[scratch_kinds_ok_def]
QED

Theorem scratch_kinds_ok_cons:
  scratch_kinds_ok fn ret (op::items) (off::offsets) labs <=>
  (?sv. op_kind_ok fn ret op sv /\ mem_sval_at labs off sv) /\
  scratch_kinds_ok fn ret items offsets labs
Proof
  simp[scratch_kinds_ok_def]
QED

Theorem scratch_kinds_ok_load:
  scratch_kinds_ok fn ret items offsets ss.sym_mem_labels /\
  k < LENGTH items /\ EL k offsets < dimword(:256) /\
  ss.sym_stack = Val (n2w (EL k offsets)) :: stk ==>
  ?last v. sym_mload ss = SymOK last /\
    last.sym_stack = v :: stk /\ op_kind_ok fn ret (EL k items) v /\
    last.sym_mem_labels = ss.sym_mem_labels /\
    last.sym_base.as_pc = ss.sym_base.as_pc + 1
Proof
  rw[scratch_kinds_ok_def, LIST_REL_EL_EQN] >>
  first_x_assum (qspec_then `k` mp_tac) >>
  metis_tac[sym_mload_kind]
QED

Theorem scratch_kinds_ok_two_equal:
  op_kind_ok fn ret op a /\ op_kind_ok fn ret op b /\
  mem_sval_at labs off a /\ mem_sval_at labs at b ==>
  scratch_kinds_ok fn ret [op;op] [off;at] labs
Proof
  simp[scratch_kinds_ok_cons, scratch_kinds_ok_nil] >> metis_tac[]
QED

Theorem scratch_kinds_ok_transport:
  scratch_kinds_ok fn ret items offsets labs /\
  (!off sv. MEM off offsets /\ mem_sval_at labs off sv ==> mem_sval_at labs' off sv) ==>
  scratch_kinds_ok fn ret items offsets labs'
Proof
  rw[scratch_kinds_ok_def, LIST_REL_EL_EQN] >>
  qpat_x_assum `!n. n < LENGTH items ==> _` (qspec_then `n` mp_tac) >>
  metis_tac[MEM_EL]
QED

Theorem scratch_kinds_ok_save:
  scratch_kinds_ok fn ret items offsets labs /\
  EVERY (\at. off+32 <= at \/ at+32 <= off) offsets /\
  (!at sv. (off+32 <= at \/ at+32 <= off) ==>
      (mem_sval_at labs' at sv <=> mem_sval_at labs at sv)) /\
  op_kind_ok fn ret op v /\ mem_sval_at labs' off v ==>
  scratch_kinds_ok fn ret (op::items) (off::offsets) labs'
Proof
  rw[scratch_kinds_ok_cons, EVERY_MEM] >- metis_tac[] >>
  metis_tac[scratch_kinds_ok_transport]
QED

Theorem sym_mstore_scratch_cons:
  scratch_kinds_ok fn ret items offsets ss.sym_mem_labels /\
  EVERY (\at. off+32 <= at \/ at+32 <= off) offsets /\
  op_kind_ok fn ret op v /\
  ss.sym_stack = Val (n2w off) :: v :: stk /\ off < dimword(:256) ==>
  ?last. sym_mstore ss = SymOK last /\ last.sym_stack = stk /\
    scratch_kinds_ok fn ret (op::items) (off::offsets) last.sym_mem_labels /\
    (!i. ~in_mem_range off 32 i ==>
       FLOOKUP last.sym_mem_labels i = FLOOKUP ss.sym_mem_labels i) /\
    (!at sv. (off+32 <= at \/ at+32 <= off) ==>
       (mem_sval_at last.sym_mem_labels at sv <=> mem_sval_at ss.sym_mem_labels at sv)) /\
    last.sym_base.as_pc = ss.sym_base.as_pc + 1
Proof
  rpt strip_tac >> drule_all sym_mstore_kind >>
  metis_tac[scratch_kinds_ok_save]
QED
