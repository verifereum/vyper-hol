Theory rawReturnHeader
Ancestors
  e2eDefs supportedProgram entryDispatchProps vyperTypeContract vyperInterpreter

Theorem check_contract_none_return_plain[local]:
  !in_deploy layouts addr mods art src tls vis mut nr rr name args defaults body.
  check_contract in_deploy layouts addr mods = SOME art /\
  MEM (src,tls) mods /\
  MEM (FunctionDecl vis mut nr rr name args defaults NoneT body) tls ==>
  ~rr
Proof
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `check_contract _ _ _ _ = _` mp_tac >>
  simp[check_contract_def, listTheory.EVERY_MEM] >> strip_tac >>
  qpat_x_assum `!x. MEM x mods ==> check_module _ _ _ _ _ _ x` drule >>
  simp[check_module_def, listTheory.EVERY_MEM] >> strip_tac >>
  qpat_x_assum `!x. MEM x tls ==> check_toplevel_decl _ _ _ x` drule >>
  simp[check_toplevel_decl_def, function_header_ok_def]
QED

Theorem source_typing_none_return_plain:
  !tops am tx mut nr args defaults body.
    source_typing_ok tops am tx /\ supported_program tops /\
    lookup_function NONE tx.function_name External tops =
      SOME (mut, nr, args, defaults, NoneT, body) ==>
    ~lookup_raw_return_or_F (NONE : num option) tx.function_name External tops
Proof
  rpt gen_tac >> strip_tac >>
  drule lookup_function_external_raw_cases >> strip_tac
  >- (gvs[source_typing_ok_def, lookup_raw_return_or_F_def] >>
      drule check_contract_none_return_plain >>
      Cases_on `rr` >> simp[listTheory.MEM] >> metis_tac[]) >>
  `ALL_DISTINCT (FLAT (MAP (external_name_keys_toplevel (NONE:num option)) tops))` by
    (fs[source_typing_ok_def] >> drule check_contract_external_names_distinct >>
     simp[contract_keys_def]) >>
  `lookup_raw_return (NONE:num option) tx.function_name External tops = NONE` by
    metis_tac[public_getter_raw_return_none] >>
  simp[lookup_raw_return_or_F_def]
QED
