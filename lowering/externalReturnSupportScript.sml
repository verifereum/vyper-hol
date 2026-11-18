Theory externalReturnSupport
Ancestors
  e2eDefs vyperTypeContractGetter vyperTypeContractContext vyperTypeContract
  vyperTypeContractStaticMaps
  vyperGetter vyperInterpreter vyperTypeSystem vyperContext list

Theorem return_checked_getter_type[local]:
  check_contract F
    (layouts:(address # (storage_layout # storage_layout)) list)
    (addr:160 word) mods = SOME art /\
  ALOOKUP mods src = SOME ts /\ module_allocated layouts addr src ts /\
  MEM decl ts /\ is_public_getter_decl fn decl /\
  external_getter_tuple src decl = SOME (mut,nr,args,dflts,ret,stmts) ==>
  check_value_type (type_env_all_modules mods) (Type ret)
Proof
  strip_tac >>
  `check_toplevel_decl mods art src decl` by
    metis_tac[check_contract_toplevel_decl_MEM] >>
  Cases_on `decl` >>
  gvs[is_public_getter_decl_def, external_getter_tuple_def]
  >~ [`check_toplevel_decl _ _ _ (VariableDecl vis vmut id typ slot)`]
  >- (Cases_on `vis` >> gvs[external_getter_tuple_def] >>
      Cases_on `is_ArrayT typ` >> gvs[getter_def]
      >- (rpt (pairarg_tac >> gvs[]) >>
          `check_value_type (type_env_all_modules mods) (Type typ)` by
            (Cases_on `vmut` >>
             gvs[check_toplevel_decl_def, check_value_type_def]) >>
          metis_tac[check_value_type_ArrayT_type, build_getter_ret_checked]) >>
      Cases_on `vmut` >> gvs[check_toplevel_decl_def, check_value_type_def]) >>
  rename1 `check_toplevel_decl _ _ _ (HashMapDecl vis tr id kt vt slot)` >>
  Cases_on `vis` >> gvs[external_getter_tuple_def, getter_def] >>
  rpt (pairarg_tac >> gvs[]) >>
  `check_value_type (type_env_all_modules mods) vt` by
    gvs[check_toplevel_decl_def] >>
  metis_tac[build_getter_ret_checked]
QED

Theorem return_selected_type_assignable:
  source_typing_ok tops am tx /\ ret <> NoneT /\
  lookup_function NONE name External tops =
    SOME (mut,nr,args,dflts,ret,fbody) ==>
  assignable_type (type_env tops) ret
Proof
  strip_tac >> drule lookup_function_External_cases >> strip_tac
  >- (gvs[source_typing_ok_def] >>
      drule check_contract_function_return_type >>
      simp[vyperContextTheory.type_env_all_modules_def, vyperContextTheory.type_env_def] >>
      metis_tac[]) >>
  gvs[source_typing_ok_def] >>
  `module_allocated am.layouts tx.target NONE tops` by
    (drule check_contract_main_module_allocated >> simp[]) >>
  `ALOOKUP [(NONE,tops)] (NONE:num option) = SOME tops` by simp[] >>
  drule_all return_checked_getter_type >>
  simp[check_value_type_def, vyperContextTheory.type_env_all_modules_def,
       vyperContextTheory.type_env_def]
QED
