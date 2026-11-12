(* The entry projection does not inspect uncalled internal functions. *)
Theory deployOutcomesFreeEntry
Ancestors
  vyperCompiler list venomInst

Theorem split_blocks_at_partition:
  !blocks label pre suf.
    split_blocks_at label blocks = SOME (pre,suf) ==>
    blocks = pre ++ suf
Proof
  Induct_on `blocks` >> simp[split_blocks_at_def] >> rpt gen_tac >>
  IF_CASES_TAC >> simp[AllCaseEqs()] >> rpt strip_tac >> gvs[] >>
  first_x_assum drule >> simp[]
QED

Theorem package_internal_blocks_entry_every:
  !ds blocks entry fs P.
    package_internal_blocks ds blocks = SOME (entry,fs) /\
    EVERY P blocks ==> EVERY P entry
Proof
  Cases_on `ds` >> simp[package_internal_blocks_def] >>
  rename1 `d::rest` >> PairCases_on `d` >>
  simp[package_internal_blocks_def, AllCaseEqs()] >> rpt strip_tac >> gvs[] >>
  drule split_blocks_at_partition >> strip_tac >> gvs[]
QED

Theorem extract_context_entry_every:
  extract_context_with_internals label internals st = SOME (ctx,data) /\
  (!entry fs.
    package_internal_blocks (internal_fn_descriptors internals)
      (REVERSE st.cs_blocks ++
        [<|bb_label := st.cs_current_bb;
           bb_instructions := st.cs_current_insts|>]) = SOME (entry,fs) ==>
    EVERY (\bb. EVERY P bb.bb_instructions) entry) ==>
  ?fn. ctx.ctx_entry = SOME label /\
       lookup_function label ctx.ctx_functions = SOME fn /\
       EVERY P (fn_insts fn)
Proof
  simp[extract_context_with_internals_def, AllCaseEqs()] >>
  rpt strip_tac >> gvs[] >>
  qexists_tac `mk_raw_function label entry_blocks` >>
  simp[mk_venom_context_def, lookup_function_def, mk_raw_function_def,
       fn_insts_def, EVERY_fn_insts_blocks, FIND_thm]
QED
