(* Root installation preserves the user prefix and body; its middle is
   made only of the optional incoming root and return-PC parameter. *)
Theory fmpStageCoverMemRoot
Ancestors
  fmpStepLayout fmpLowerDefs callLayoutDefs venomInst list

Theorem fmp_cover_root_middle:
  split_fmp_entry fn = SOME (FmpEntryLayout users oldpc suffix) /\
  fmp_make_root_layout ctx fn info runner s =
    SOME (FmpRootLayout n root newpc s') /\
  entry.bb_instructions = users ++ OPTION_TO_LIST oldpc ++ tail /\
  fmp_install_root ctx fn (FmpRootLayout n root newpc s') (entry::rest) =
    SOME (out,s'') /\
  P INITIAL_FMP /\ P FMP_PARAM /\ P RETPC_PARAM /\
  EVERY (\x. P x.inst_opcode) (OPTION_TO_LIST oldpc) ==>
  ?middle.
    out = (entry with bb_instructions := users ++ middle ++ tail)::rest /\
    LENGTH middle = LENGTH (OPTION_TO_LIST oldpc) +
                    LENGTH (OPTION_TO_LIST root) /\
    EVERY (\x. P x.inst_opcode) middle
Proof
  strip_tac >> drule_all fmp_make_root_layout_prefix >> strip_tac >> gvs[] >>
  drule_all fmp_install_root_exact_prefix >> strip_tac >> gvs[] >>
  qexists_tac `if fn_is_context_entry ctx fn then
    OPTION_TO_LIST newpc ++ OPTION_TO_LIST root
    else OPTION_TO_LIST root ++ OPTION_TO_LIST newpc` >>
  simp[] >>
  qpat_x_assum `fmp_make_root_layout _ _ _ _ _ = _` mp_tac >>
  simp[fmp_make_root_layout_def] >>
  Cases_on `info.fi_needs_fmp` >>
  Cases_on `fn_is_context_entry ctx fn` >>
  Cases_on `oldpc` >>
  simp[AllCaseEqs(), OPTION_TO_LIST_def, set_param_index_def, mk_inst_def] >>
  rpt strip_tac >> gvs[OPTION_TO_LIST_def, set_param_index_def, mk_inst_def]
QED
