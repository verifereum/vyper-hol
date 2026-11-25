Theory linkedCompiledCalleeSource
Ancestors
  bodyFullShadowInternalRun bodyFullShadowInternalCode
  linkedInternalSelection linkedCheckedDeclarationNames whitelistCheckerSelectorProps
  vyperTypeContractContext vyperTypeContract compileUnit compileVyper compileEnv
  moduleLowering constSubstMods loweringShapeDefs venomInst list pair option alist

Theorem linked_compiled_callee_source_member:
  check_contract is_ctor layouts addr mods = SOME art /\
  classify_functions_unit mods exps = (exts,ints,fb,ctor,imp_ctors) /\
  (!pkg. MEM pkg srcs ==> MEM pkg (ints ++ imp_ctors)) /\
  ips = MAP (set_internal_package_target rp.rpol_target o
    package_internal_fn_unit mods T (K global_nonreentrant_slot) is_ctor
      (if is_ctor then imm_len_mods mods else 0)) srcs /\
  name = (if is_ctor then "__deploy" else "__entry") /\
  extract_context_with_internals name ips final = SOME (raw,data) /\
  ctx.ctx_functions = raw.ctx_functions /\
  ALOOKUP mods src = SOME tops /\
  (vis = Internal \/ (mode /\ src <> NONE /\ vis = Deploy)) /\
  MEM (FunctionDecl vis mut nr rr fname args dflts ret ss) tops /\
  venomInst$lookup_function
    (internal_fn_label (build_func_ids_mods 0 mods (nsid_to_string (src,fname)))
      (nsid_to_string (src,fname)) (MAP SND args) mode)
    ctx.ctx_functions = SOME callee ==>
  mode = is_ctor /\ MEM (src,subst_consts_fn_mods (consts_env_mods mods)
    (mut,nr,rr,fname,args,dflts,ret,ss)) srcs
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  qpat_x_assum `ctx.ctx_functions = raw.ctx_functions`
    (fn eq => RULE_ASSUM_TAC (PURE_REWRITE_RULE [eq])) >>
  `ALL_DISTINCT (MAP FST mods)` by
    (drule check_contract_namespaces_ok >> simp[contract_namespaces_ok_def]) >>
  `!src tops. ALOOKUP mods src = SOME tops ==> supported_declaration_names tops` by
    (qx_genl_tac [`owner`,`decls`] >> strip_tac >>
     `MEM (owner,decls) mods` by
       (qpat_assum `ALOOKUP mods owner = SOME decls` (MATCH_ACCEPT_TAC o MATCH_MP ALOOKUP_MEM)) >>
     `supported_selectors_distinct decls` by
       drule_all_then ACCEPT_TAC check_contract_module_selectors_distinct >>
     drule_all check_contract_supported_declaration_names_mods >> simp[]) >>
  `?selected. MEM selected srcs /\
     internal_fn_label (build_func_ids_mods 0 mods (nsid_to_string (src,fname)))
       (nsid_to_string (src,fname)) (MAP SND args) mode =
     FST (set_internal_package_target rp.rpol_target
       (package_internal_fn_unit mods T (K global_nonreentrant_slot) is_ctor
         (if is_ctor then imm_len_mods mods else 0) selected))` by
    (qpat_assum `lookup_function _ raw.ctx_functions = SOME callee`
      (mp_tac o MATCH_MP lookup_function_mem) >>
     qpat_assum `extract_context_with_internals name ips final = SOME (raw,data)`
       (PURE_REWRITE_TAC o single o MATCH_MP extract_context_internal_names) >>
     qpat_assum `ips = MAP _ srcs` SUBST1_TAC >>
     simp[internal_fn_descriptors_map, GSYM MAP_MAP_o, MEM_MAP] >>
     disch_then strip_assume_tac
     >- (qpat_x_assum `internal_fn_label _ _ _ _ = (if is_ctor then _ else _)` mp_tac >>
         Cases_on `is_ctor` >> simp[internal_fn_label_def]) >>
     rename1 `MEM packed srcs` >> qexists_tac `packed` >>
     PairCases_on `packed` >>
     fs[package_internal_fn_unit_def, set_internal_package_target_def]) >>
  PairCases_on `selected` >>
  qpat_x_assum `internal_fn_label _ _ _ _ = FST _` mp_tac >>
  simp[package_internal_fn_unit_def, set_internal_package_target_def] >>
  strip_tac >>
  `mode = is_ctor` by drule_then ACCEPT_TAC internal_fn_label_mode >>
  `MEM (selected0,selected1,selected2,selected3,selected4,selected5,
        selected6,selected7,selected8) (ints ++ imp_ctors)` by
    (qpat_assum `!pkg. MEM pkg srcs ==> _` irule >> first_assum ACCEPT_TAC) >>
  qpat_x_assum `internal_fn_label _ _ _ _ = _`
    (assume_tac o GSYM o MATCH_MP internal_fn_label_id_11) >>
  `(selected0,selected1,selected2,selected3,selected4,selected5,
     selected6,selected7,selected8) =
    (src,subst_consts_fn_mods (consts_env_mods mods)
      (mut,nr,rr,fname,args,dflts,ret,ss))` by
    (mp_tac (Q.INST [`exps` |-> `exps`,`exts` |-> `exts`,`ints` |-> `ints`,
       `fb` |-> `fb`,`ctor` |-> `ctor`,`imp_ctors` |-> `imp_ctors`,
       `tops` |-> `tops`,`vis` |-> `vis`,`src'` |-> `selected0`,
       `picked` |-> `(selected1,selected2,selected3,selected4,selected5,
                       selected6,selected7,selected8)`,
       `stmts` |-> `ss`] checked_classified_internal_id_unique) >>
     `vis <> External` by fs[] >>
     simp[fn_decl_name_def] >>
     disch_then (fn unique =>
       qpat_assum `!s ts. ALOOKUP mods s = SOME ts ==> supported_declaration_names ts`
         (ACCEPT_TAC o MATCH_MP unique))) >>
  asm_rewrite_tac[] >>
  qpat_x_assum `(selected0,_,_,_,_,_,_,_,_) = _`
    (fn eq => PURE_REWRITE_TAC [GSYM eq]) >>
  first_assum ACCEPT_TAC
QED
