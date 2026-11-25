(* Discharge the linked contract invariant's support premises from checking. *)
Theory linkedContractInvProducer
Ancestors
  linkedCheckedContractInv linkedCheckedDeclarationNames
  whitelistLinkedConstProps whitelistLinkedHeaderProps whitelistLinkedBodyProps
  whitelistCheckerSelectorProps bodyCallSupport bodyInvSplit
  e2eModsDefs e2eDefs compileUnit compileEnv vyperContext
  alist list pair option

Theorem checked_linked_contract_inv:
  check_contract cx.in_deploy cx.layouts cx.txn.target mods = SOME art /\
  check_contract F cx.layouts cx.txn.target mods = SOME runtime_art /\
  exports_ok cx.layouts cx.txn.target mods exps /\
  ALOOKUP cx.sources cx.txn.target = SOME mods /\
  IS_SOME (ALOOKUP mods NONE) /\
  cx.layouts = am.layouts /\ cx.txn.target = tx.target /\
  cx.nonreentrant_slot = lookup_nonreentrant_slot cx.layouts cx.txn.target /\
  layouts_agree_mods mods exps am tx /\
  (if cx.in_deploy then
     lower_vyper_deploy_unit_mods mods exps rp rbc = SOME unit
   else lower_vyper_runtime_unit_mods mods exps rp = SOME unit) /\
  (cx.in_deploy ==>
     IS_SOME (FST (SND (SND (SND (classify_functions_unit mods exps)))))) /\
  (vis = Deploy <=> cx.in_deploy) ==>
  contract_inv mods exps unit.cu_context
    (build_compile_env_unit mods src vis mut name args ret ss T
       with ce_target := rp.rpol_target) cx
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `!tops. ALOOKUP mods NONE = SOME tops ==> layouts_agree tops am cx.txn` by
    (rpt strip_tac >>
     `MEM (NONE,tops) mods` by (irule ALOOKUP_MEM >> asm_rewrite_tac[]) >>
     qpat_assum `cx.txn.target = tx.target` (fn same_target =>
       simp_tac bool_ss [layouts_agree_def, same_target]) >>
     qpat_assum `layouts_agree_mods mods exps am tx`
       (mp_tac o List.last o CONJUNCTS o REWRITE_RULE [layouts_agree_mods_def]) >>
     Cases_on `ALOOKUP am.layouts tx.target`
     >- (simp[] >> metis_tac[]) >>
     rename1 `ALOOKUP am.layouts tx.target = SOME layout` >> PairCases_on `layout` >>
     simp[] >> metis_tac[]) >>
  `check_contract F am.layouts cx.txn.target mods = SOME runtime_art` by
    (qpat_assum `cx.layouts = am.layouts` (SUBST1_TAC o SYM) >>
     FIRST_ASSUM ACCEPT_TAC) >>
  `!src tops. ALOOKUP mods src = SOME tops ==>
     supported_module_headers tops /\
     (src = NONE ==> supported_declaration_headers tops)` by
    (rpt gen_tac >> strip_tac >>
     `MEM (src,tops) mods` by (irule ALOOKUP_MEM >> asm_rewrite_tac[]) >>
     drule_all_then assume_tac check_contract_module_selectors_distinct >>
     drule_all_then strip_assume_tac check_contract_supported_declaration_names_mods >>
     drule_all_then assume_tac check_contract_linked_supported_consts >>
     mp_tac (Q.INST [`art` |-> `runtime_art`, `src` |-> `src`,
        `tops` |-> `tops`, `tx` |-> `cx.txn`]
       (SPEC_ALL check_contract_linked_supported_declaration_headers)) >>
     impl_tac >- (asm_rewrite_tac[] >> strip_tac >> gvs[]) >>
     simp[supported_module_headers_def]) >>
  `!owner tops v m lock raw fn_name formals defaults result code.
     ALOOKUP mods owner = SOME tops /\
     MEM (FunctionDecl v m lock raw fn_name formals defaults result code) tops /\
     (owner = NONE \/ context_function_live cx (owner,fn_name)) ==>
     supported_declaration_body tops
       (FunctionDecl v m lock raw fn_name formals defaults result code) /\
     (cx.in_deploy ==> supported_deploy_declaration tops
       (FunctionDecl v m lock raw fn_name formals defaults result code))` by
    (rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
     `owner = NONE ==> layouts_agree tops am cx.txn` by
       (strip_tac >> gvs[]) >>
     mp_tac (Q.INST [`runtime_art` |-> `runtime_art`, `art` |-> `art`,
       `am` |-> `am`, `src` |-> `owner`, `vis` |-> `v`, `mut` |-> `m`,
       `nr` |-> `lock`, `rr` |-> `raw`, `name` |-> `fn_name`,
       `args` |-> `formals`, `dflts` |-> `defaults`, `ret` |-> `result`,
       `ss` |-> `code`]
       (SPEC_ALL check_contract_linked_supported_function_body)) >>
     simp[Once EQ_SYM_EQ]) >>
  mp_tac (Q.INST [`art` |-> `art`, `runtime_art` |-> `runtime_art`,
      `rbc` |-> `rbc`, `am` |-> `am`, `tx` |-> `tx`]
    (SPEC_ALL linked_checked_contract_inv)) >>
  impl_tac >- asm_rewrite_tac[] >>
  disch_then ACCEPT_TAC
QED
