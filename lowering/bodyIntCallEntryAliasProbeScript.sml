(* Frozen-entry audit: parameter separation does not mention the return buffer.
   This is an interface probe, not a counterexample to the whole seam. *)
Theory bodyIntCallEntryAliasProbe
Ancestors
  intCallCallee compileEnv venomMemDefs finite_map arithmetic words list

Theorem singleton_internal_args_allows_return_alias:
  FLOOKUP ce.ce_vars name = SOME (MemLoc po psz) /\
  type_memory_size entry.type <= psz /\ val_wf entry.type entry.value /\
  w2n (rb:bytes32) + psz <= frontier /\
  val_in_memory entry.type entry.value (w2n rb) mem ==>
  internal_args_rel ce [(name,F)] (FEMPTY |+ (name,entry)) 1
    [rb;rb] frontier mem
Proof
  simp[internal_args_rel_def, dimword_def] >> rpt strip_tac >>
  qexists_tac `entry` >> simp[FLOOKUP_UPDATE]
QED

Theorem positive_return_alias_not_separated:
  0 < dn /\ 0 < psz ==>
  ~compileEnv$regions_disjoint off dn off psz
Proof
  simp[compileEnvTheory.regions_disjoint_def]
QED
