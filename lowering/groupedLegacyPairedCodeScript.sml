(* The selected legacy package has matching installed real and shadow bodies. *)
Theory groupedLegacyPairedCode
Ancestors
  groupedRuntimeBodyCode gasShadowRuntimeBodies gasShadowRuntimeOps
  gasShadowModuleDefs gasShadowState gasShadow exprLoweringProps
  entryRejectAllocationIds selectedEntryPrefixCode entryPtrSeamRegister
  moduleLowering compileEnv emitHelper list pair
  gasShadowRuntimeRegisterEnv gasShadowCompileStmtBase

val shadow_job = ``\job. case job of
  ExternalLegacyJob package => ExternalLegacyJob (gas_shadow_external_package package)
| ExternalCommonJob common kwvars => ExternalCommonJob
    (common with <| ec_env := gas_shadow_env T common.ec_env;
                    ec_body := MAP gas_shadow_stmt common.ec_body |>)
    (MAP (\(n,p,ty,e). (n,p,ty,gas_shadow_expr e)) kwvars)``;

val paired_statement = ``
  MEM (ExternalLegacyJob (lbl,ce,pa,m,pay,nr,key,ut,view,ss,rt)) jobs /\
  compile_external_jobs jobs sd = ((),sx) /\
  compile_external_jobs (MAP ^shadow_job jobs) shd = ((),shx) /\
  gas_shadow_state sd shd /\ cs_extends sx se /\ cs_extends shx she /\
  (!bb. MEM bb (all_blocks se) ==> lookup_block bb.bb_label fn.fn_blocks = SOME bb) /\
  (!bb. MEM bb (all_blocks she) ==> lookup_block bb.bb_label shfn.fn_blocks = SOME bb) ==>
  ?checks reg cf sa done sha shdone.
    checks.cs_current_bb = lbl /\ checks.cs_current_insts = [] /\ ci_mono sd checks /\
    compile_entry_checks m pay checks = ((),reg) /\ fn_has_code checks reg fn /\
    compile_register_positional_args ce pa 4 reg = (cf,sa) /\ fn_has_code reg sa fn /\
    ~block_is_terminated sa /\
    compile_guarded_body cf nr key ut view ss rt sa = ((),done) /\
    fn_has_code sa done fn /\ gas_shadow_state sa sha /\
    compile_guarded_body (gas_shadow_env T cf) nr key ut view (MAP gas_shadow_stmt ss)
      rt sha = ((),shdone) /\
    fn_has_code sha shdone shfn``;

val (paired_input, paired_output) = boolSyntax.dest_imp paired_statement;
val (paired_witnesses, paired_facts) = boolSyntax.strip_exists paired_output;
val paired_done = valOf (List.find (fn v => fst (dest_var v) = "done") paired_witnesses);

Theorem grouped_legacy_paired_code_with_end:
  ^paired_input ==>
  ^(boolSyntax.list_mk_exists (paired_witnesses, ``^paired_facts /\ cs_extends ^paired_done se``))
Proof
  strip_tac >>
  qpat_x_assum `MEM (ExternalLegacyJob _) jobs`
    (qx_choosel_then [`pre`,`post`] SUBST_ALL_TAC o REWRITE_RULE [Once MEM_SPLIT]) >>
  drule_at (Pat `compile_external_jobs _ sd = _`) grouped_legacy_job_code_with_end >>
  disch_then (qspecl_then [`se`,`fn`] mp_tac) >>
  (impl_tac >- asm_rewrite_tac[]) >>
  disch_then (qx_choosel_then [`start`,`checks`,`reg`,`sa`,`done`,`cf`] strip_assume_tac) >>
  qpat_x_assum `compile_external_jobs (MAP _ _) shd = _`
    (assume_tac o SIMP_RULE (srw_ss()) [MAP_APPEND,gas_shadow_external_package_def]) >>
  drule_at (Pat `compile_external_jobs _ shd = _`) grouped_legacy_job_code_with_end >>
  disch_then (qspecl_then [`she`,`shfn`] mp_tac) >>
  (impl_tac >- asm_rewrite_tac[]) >>
  disch_then (qx_choosel_then [`shstart`,`shchecks`,`shreg`,`sha`,`shdone`,`shcf`]
    strip_assume_tac) >>
  suspend "synchronise"
QED

Resume grouped_legacy_paired_code_with_end[synchronise]:
  `gas_shadow_state start shstart` by
    (qspecl_then [`T`,`pre`]
       (drule_then (mp_tac o SPEC_ALL) o Q.SPECL [`sd`,`shd`] o
        REWRITE_RULE [gas_shadow_compiles_def])
       gas_shadow_compiles_compile_external_jobs >>
     asm_rewrite_tac[SND]) >>
  `gas_shadow_state checks shchecks` by
    (qspec_then `lbl` mp_tac (GEN_ALL gas_shadow_compiles_new_block) >>
     simp_tac (srw_ss()) [gas_shadow_compiles_def] >>
     disch_then (qspecl_then [`start`,`shstart`] mp_tac) >>
     asm_rewrite_tac[SND] >> strip_tac >> asm_rewrite_tac[]) >>
  `gas_shadow_state reg shreg` by
    (mp_tac (Q.INST [`min_cds` |-> `m`, `payable` |-> `pay`]
       gas_shadow_compiles_compile_entry_checks) >>
     simp_tac (srw_ss()) [gas_shadow_compiles_def] >>
     disch_then (qspecl_then [`checks`,`shchecks`] mp_tac) >>
     asm_rewrite_tac[SND]) >>
  `gas_shadow_env T cf = shcf /\ gas_shadow_state sa sha` by
    (qspecl_then [`pa`,`ce`,`4`]
       (drule_then (mp_tac o SPEC_ALL) o Q.SPECL [`reg`,`shreg`] o
        REWRITE_RULE [gas_shadow_compiles_env_def])
       (Q.INST [`sd` |-> `T`] gas_shadow_compiles_env_register_positional_args) >>
     asm_rewrite_tac[FST,SND]) >>
  qexistsl_tac [`checks`,`reg`,`cf`,`sa`,`done`,`sha`,`shdone`] >>
  asm_rewrite_tac[] >> conj_tac
  >- (irule ci_mono_trans >> qexists_tac `start` >> conj_tac
      >- (qspecl_then [`pre`,`sd`] mp_tac compile_external_jobs_ci_mono >> simp[]) >>
      qspecl_then [`lbl`,`start`] mp_tac ci_mono_new_block >> simp[]) >>
  `~block_is_terminated checks` by simp[block_is_terminated_def] >>
  `~block_is_terminated reg` by (irule compile_entry_checks_open >> metis_tac[]) >>
  metis_tac[registration_noop_or_open]
QED

Finalise grouped_legacy_paired_code_with_end

Theorem grouped_legacy_paired_code:
  ^paired_statement
Proof
  disch_then (mp_tac o MATCH_MP grouped_legacy_paired_code_with_end) >>
  disch_then (qx_choosel_then [`checks`,`reg`,`cf`,`sa`,`done`,`sha`,`shdone`] strip_assume_tac) >>
  qexistsl_tac [`checks`,`reg`,`cf`,`sa`,`done`,`sha`,`shdone`] >> asm_rewrite_tac[]
QED
