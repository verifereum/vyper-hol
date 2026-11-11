(* Successful internal packaging retains any delimiter-free prefix. *)
Theory entryPrefixRetention
Ancestors
  vyperCompiler list

Theorem split_blocks_at_prefix:
  !pre tail.
    ~MEM lbl (MAP (\bb. bb.bb_label) pre) ==>
    split_blocks_at lbl (pre ++ tail) =
      OPTION_MAP (\(p,s). (pre ++ p,s)) (split_blocks_at lbl tail)
Proof
  Induct >> simp[split_blocks_at_def] >> rpt strip_tac >>
  simp[AllCaseEqs()] >>
  Cases_on `split_blocks_at lbl tail` >> simp[] >>
  rename1 `SOME p` >> Cases_on `p` >> simp[]
QED

Theorem package_internal_blocks_prefix:
  (!d. MEM d ds ==> ~MEM (FST d) (MAP (\bb. bb.bb_label) pre)) /\
  package_internal_blocks ds (pre ++ tail) = SOME (entry,fs) ==>
  ?rest. entry = pre ++ rest
Proof
  Cases_on `ds` >- (simp[package_internal_blocks_def] >> metis_tac[]) >>
  rename1 `h::t` >> PairCases_on `h` >>
  simp[package_internal_blocks_def] >> strip_tac >>
  `~MEM h0 (MAP (\bb. bb.bb_label) pre)` by metis_tac[pairTheory.FST] >>
  gvs[split_blocks_at_prefix, AllCaseEqs()] >>
  PairCases_on `z` >> gvs[] >> metis_tac[]
QED

Theorem package_internal_blocks_prefix_mem:
  (!d. MEM d ds ==> ~MEM (FST d) (MAP (\bb. bb.bb_label) pre)) /\
  package_internal_blocks ds (pre ++ tail) = SOME (entry,fs) /\
  MEM bb pre ==> MEM bb entry
Proof
  metis_tac[package_internal_blocks_prefix, MEM_APPEND]
QED
