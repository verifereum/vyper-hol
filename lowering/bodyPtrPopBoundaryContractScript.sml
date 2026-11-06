Theory bodyPtrPopBoundaryContract
Ancestors
  bodyPtrPopGuardedWindow bodyPtrPopWindow emitHelper venomInst list rich_list

(* A complete window alone forgets a guard waiting for its decrement.
   Factor that linked residual once for compositional compiler boundaries. *)
Definition pop_guard4_def:
  pop_guard4 xs <=>
    ?p tr h a b c i0 i1 i2 i3.
      xs = p ++
        [mk_inst i0 (if tr then TLOAD else SLOAD) [Var h] [a];
         mk_inst i1 ISZERO [Var a] [b];
         mk_inst i2 ISZERO [Var b] [c];
         mk_inst i3 ASSERT [Var c] []]
End

(* Both clauses are needed: the second prevents a later unchecked SUB
   from completing a window, even when that SUB emits no ASSERT. *)
Definition pop_boundary_clean_def:
  pop_boundary_clean xs <=> ~occurs5 pop_guarded5 xs /\ ~pop_guard4 xs
End

Theorem pop_boundary_clean_nil[simp]:
  pop_boundary_clean []
Proof
  simp[pop_boundary_clean_def, pop_guard4_def, occurs5_short]
QED

Theorem pop_boundary_clean_windows:
  pop_boundary_clean xs ==> ~occurs5 pop_guarded5 xs
Proof
  simp[pop_boundary_clean_def]
QED

Theorem pop_boundary_clean_residual:
  pop_boundary_clean xs ==> ~pop_guard4 xs
Proof
  simp[pop_boundary_clean_def]
QED

Theorem pop_guard4_snoc_no_assert:
  i.inst_opcode <> ASSERT ==> ~pop_guard4 (xs ++ [i])
Proof
  simp[pop_guard4_def] >> rpt strip_tac >>
  gvs[GSYM APPEND_ASSOC, mk_inst_def]
QED

Theorem pop_guarded5_tail_residual:
  4 <= LENGTH xs /\ pop_guarded5 (tail4 xs ++ [i]) ==> pop_guard4 xs
Proof
  simp[pop_guarded5_snoc, pop_guard4_def] >> rpt strip_tac >>
  qexists_tac `TAKE (LENGTH xs - 4) xs` >>
  qexistsl_tac [`tr`,`h`,`a`,`b`,`c`,`i0`,`i1`,`i2`,`i3`] >>
  qpat_x_assum `tail4 xs = _` (SUBST1_TAC o SYM) >>
  simp[tail4_def, TAKE_DROP]
QED

Theorem pop_boundary_clean_snoc_no_assert:
  pop_boundary_clean xs /\ i.inst_opcode <> ASSERT ==>
  pop_boundary_clean (xs ++ [i])
Proof
  simp[pop_boundary_clean_def, occurs5_snoc] >> rpt strip_tac
  >- metis_tac[pop_guarded5_tail_residual]
  >> metis_tac[pop_guard4_snoc_no_assert]
QED

Theorem pop_boundary_clean_append_no_assert:
  pop_boundary_clean xs /\ EVERY (\i. i.inst_opcode <> ASSERT) ys ==>
  pop_boundary_clean (xs ++ ys)
Proof
  qid_spec_tac `xs` >> Induct_on `ys` using SNOC_INDUCT
  >- simp[] >>
  simp[SNOC_APPEND, EVERY_APPEND] >> rpt strip_tac >>
  irule pop_boundary_clean_snoc_no_assert >> simp[]
QED
