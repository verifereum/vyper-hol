Theory rawReturnHeader
Ancestors
  e2eDefs supportedProgram supportedDecls supportedTypes vyperGetter vyperTypeContract vyperInterpreter

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

Theorem supported_build_getter_return:
  !e kt vt n args ret exp tops.
    supported_hashmap_value tops vt /\
    build_getter e kt vt n = (args,ret,exp) ==> ret <> NoneT
Proof
  recInduct build_getter_ind >> rpt strip_tac
  >- (qpat_x_assum `build_getter _ _ _ _ = _` mp_tac >>
      once_rewrite_tac[build_getter_def] >>
      Cases_on `vt` >> simp[Once build_getter_def] >>
      gvs[supported_hashmap_value_def]
      >- (rename1 `supported_storage_type tops (ArrayT t b)` >>
          Cases_on `b` >> gvs[supported_storage_array_depth] >>
          pairarg_tac >> gvs[] >> metis_tac[])
      >> gvs[supported_storage_type_def, Once supported_nested_type_def,
             supported_full_word_type_def])
  >> qpat_x_assum `build_getter _ _ _ _ = _` mp_tac >>
  simp[Once build_getter_def] >>
  pairarg_tac >> gvs[supported_hashmap_value_def] >> metis_tac[]
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
  >- (Cases_on `v`
      >- (Cases_on `v0` >> Cases_on `o'` >>
          simp[listTheory.EVERY_DEF, supported_declaration_header_def] >>
          (rpt strip_tac >> reverse (Cases_on `s = name`)
          >- (gvs[lookup_function_def, lookup_raw_return_def, listTheory.MEM] >>
              metis_tac[]) >>
          gvs[lookup_function_def, lookup_raw_return_def, listTheory.MEM] >>
          Cases_on `t` >> gvs[getter_def]
          >- (Cases_on `b'` >> gvs[supported_storage_array_depth] >>
              pairarg_tac >> gvs[] >>
              metis_tac[supported_build_getter_return, supported_hashmap_value_def])
          >> gvs[supported_storage_type_def, Once supported_nested_type_def,
                 supported_full_word_type_def]))
      >> simp[listTheory.EVERY_DEF, lookup_function_def, lookup_raw_return_def,
              listTheory.MEM] >> metis_tac[])
  >- (simp[listTheory.EVERY_DEF, supported_hashmap_header_contract] >>
      strip_tac >> Cases_on `v` >>
      gvs[lookup_function_def, lookup_raw_return_def, listTheory.MEM]
      >- (reverse (Cases_on `s = name`)
          >- (gvs[] >> metis_tac[]) >>
          gvs[getter_def] >>
          qpat_x_assum `(\(args,ret,exp). _) _ = _` mp_tac >>
          pairarg_tac >> gvs[] >>
          metis_tac[supported_build_getter_return])
      >> metis_tac[])
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
