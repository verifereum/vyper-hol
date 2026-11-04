Theory rawReturnHeader
Ancestors
  e2eDefs supportedProgram supportedDecls vyperTypeContract vyperInterpreter

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

Theorem supported_lookup_none_raw[local]:
  !ts ambient name mut nr args defaults body.
  EVERY (supported_declaration_header ambient) ts /\
  lookup_function (NONE : num option) name External ts =
    SOME (mut,nr,args,defaults,NoneT,body) ==>
  ?rr. MEM (FunctionDecl External mut nr rr name args defaults NoneT body) ts /\
       lookup_raw_return (NONE : num option) name External ts = SOME rr
Proof
  Induct_on `ts` >- simp[lookup_function_def] >>
  rpt gen_tac >> Cases_on `h`
  >- (simp[listTheory.EVERY_DEF, lookup_function_def, lookup_raw_return_def,
           listTheory.MEM] >>
      Cases_on `s = name /\ f = External` >> gvs[] >> metis_tac[])
  >- (Cases_on `v` >>
      simp[listTheory.EVERY_DEF, lookup_function_def, lookup_raw_return_def,
           listTheory.MEM, supported_public_variables_rejected] >>
      metis_tac[])
  >- (simp[listTheory.EVERY_DEF, supported_hashmap_header_contract] >>
      strip_tac >> gvs[lookup_function_def, lookup_raw_return_def,
                      listTheory.MEM] >> metis_tac[])
  >> simp[listTheory.EVERY_DEF, lookup_function_def, lookup_raw_return_def,
          listTheory.MEM] >> metis_tac[]
QED

Theorem source_typing_none_return_plain:
  !tops am tx mut nr args defaults body.
    source_typing_ok tops am tx /\ supported_program tops /\
    lookup_function NONE tx.function_name External tops =
      SOME (mut, nr, args, defaults, NoneT, body) ==>
    ~lookup_raw_return_or_F (NONE : num option) tx.function_name External tops
Proof
  rpt gen_tac >> strip_tac >>
  `EVERY (supported_declaration_header tops) tops` by
    gvs[supported_program_def, supported_declaration_headers_def] >>
  drule_all supported_lookup_none_raw >> strip_tac >>
  gvs[source_typing_ok_def] >>
  `~rr` by
    (drule check_contract_none_return_plain >>
     simp[listTheory.MEM] >>
     Cases_on `rr` >> simp[] >> metis_tac[]) >>
  simp[lookup_raw_return_or_F_def]
QED
