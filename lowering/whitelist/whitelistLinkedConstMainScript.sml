Theory whitelistLinkedConstMain
Ancestors
  alist list pair finite_map vyperAST vyperInterpreter vyperTypeContract
  vyperTypeContractContext vyperTypeSystem constSubst constSubstCorrect
  whitelistCheckerConsts

Triviality checked_main_consts_fold:
  check_contract F layouts addr mods = SOME art /\ ALOOKUP mods NONE = SOME tops ==>
  ?imms A. constants_fold_module mods imms NONE tops FEMPTY = SOME A
Proof
  strip_tac >>
  `contract_constants_ok mods` by gvs[check_contract_def] >>
  `MEM (NONE,tops) (constants_order mods)` by
    (simp[MEM_constants_order] >> metis_tac[ALOOKUP_MEM]) >>
  qpat_x_assum `MEM _ (constants_order _)`
    (strip_assume_tac o REWRITE_RULE[MEM_SPLIT]) >>
  Cases_on `initial_immutables (type_env_all_modules mods) mods` >>
  gvs[contract_constants_ok_def, optionTheory.IS_SOME_EXISTS] >>
  drule constants_fold_append >> strip_tac >>
  fs[constants_fold_def, AllCaseEqs()] >> metis_tac[]
QED

Theorem main_const_replacement_facts:
  check_contract F layouts addr mods = SOME art /\
  ALOOKUP mods NONE = SOME tops /\
  MEM (id,r) (module_consts_env tops []) ==>
  constant_expr mods r /\ const_local_refs r = [] /\
  well_typed_expr (artifact_env art mods NONE) r
Proof
  strip_tac >>
  drule_all checked_main_consts_fold >> strip_tac >>
  `ALL_DISTINCT (MAP FST (module_consts_env tops []))` by
    (drule_all checked_module_consts_env_agrees >> simp[const_acc_agrees_def]) >>
  `!n e. MEM (n,e) (module_consts_env tops []) ==>
         ALOOKUP (module_consts_env tops []) n = SOME e /\
         constant_expr mods e /\ const_local_refs e = [] /\ no_neg_exp_expr e`
    by (rpt gen_tac >> strip_tac >>
        `ALOOKUP (module_consts_env tops []) n = SOME e` by
          (irule ALOOKUP_ALL_DISTINCT_MEM >> simp[]) >>
        drule_all checked_module_consts_env_replacement >> strip_tac >>
        metis_tac[constant_value_no_neg_exp]) >>
  `EVERY (no_neg_exp_expr o SND) (module_consts_env tops [])` by
    (rw[EVERY_MEM, FORALL_PROD] >> metis_tac[]) >>
  first_x_assum drule >> strip_tac >> simp[] >>
  drule_all checked_module_consts_env_replacement_typed >> simp[]
QED
