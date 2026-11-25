(* Recover paired internal body intervals from a linked unit's two compiler runs. *)
Theory linkedShadowBodyInvRuns
Ancestors
  bodyFullShadowBodyInv bodyFullShadowInternalCode gasShadowState
  gasShadowModuleDefs gasShadowUnitExtract gasShadowInternal gasShadow
  compileUnit moduleLowering compileVyper compileEnv constSubstMods
  loweringShapeDefs fragExec bodyFullShadowInternalRun vyperCompiler venomInst venomWf
  list alist pair

Theorem shadow_body_inv_mods_from_internal_runs:
  (if is_ctor then lower_vyper_deploy_unit_mods mods exps rp bc = SOME unit
   else lower_vyper_runtime_unit_mods mods exps rp = SOME unit) /\
  name = (if is_ctor then "__deploy" else "__entry") /\
  (!src tops mode vis mut nr rr fname args dflts ret ss callee.
    ALOOKUP mods src = SOME tops /\
    (vis = Internal \/ (mode /\ src <> NONE /\ vis = Deploy)) /\
    MEM (FunctionDecl vis mut nr rr fname args dflts ret ss) tops /\
    lookup_function
      (internal_fn_label (build_func_ids_mods 0 mods (nsid_to_string (src,fname)))
         (nsid_to_string (src,fname)) (MAP SND args) mode)
      unit.cu_context.ctx_functions = SOME callee ==>
    mode = is_ctor /\ MEM (src,subst_consts_fn_mods (consts_env_mods mods)
      (mut,nr,rr,fname,args,dflts,ret,ss)) srcs) /\
  ips = MAP (set_internal_package_target rp.rpol_target o
    package_internal_fn_unit mods T (K global_nonreentrant_slot) is_ctor
      (if is_ctor then imm_len_mods mods else 0)) srcs /\
  compile_internal_fn_bodies ips start = ((),run_end) /\
  compile_internal_fn_bodies (MAP gas_shadow_internal_package ips)
    startS = ((),run_endS) /\
  extract_context_with_internals name ips run_end = SOME (raw,data) /\
  extract_context_with_internals name (MAP gas_shadow_internal_package ips)
    run_endS = SOME (rawS,dataS) /\
  unit.cu_context.ctx_functions = raw.ctx_functions /\
  shadow_unit.cu_context.ctx_functions = rawS.ctx_functions /\
  gas_shadow_context unit.cu_context shadow_unit.cu_context /\
  lowering_context_ok unit.cu_context /\ lowering_context_ok shadow_unit.cu_context /\
  gas_shadow_state start startS /\
  EVERY (\bb. ~internal_label_ok bb.bb_label) (all_blocks start) /\
  EVERY (\bb. ~internal_label_ok bb.bb_label) (all_blocks startS) ==>
  shadow_body_inv_mods mods exps unit.cu_context shadow_unit.cu_context
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  PURE_REWRITE_TAC [shadow_body_inv_mods_def] >>
  conj_tac >- first_assum ACCEPT_TAC >>
  qx_genl_tac [`src`,`tops`,`mode`,`vis`,`mut`,`nr`,`rr`,`fname`,`args`,
               `dflts`,`ret`,`ss`,`callee`] >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  qpat_assum `!src tops mode vis mut nr rr fname args dflts ret ss callee. _`
    (qspecl_then [`src`,`tops`,`mode`,`vis`,`mut`,`nr`,`rr`,`fname`,
       `args`,`dflts`,`ret`,`ss`,`callee`] mp_tac) >>
  impl_tac >- asm_rewrite_tac[] >>
  disch_then (CONJUNCTS_THEN2 SUBST_ALL_TAC assume_tac) >>
  qabbrev_tac `source = (src,subst_consts_fn_mods (consts_env_mods mods)
    (mut,nr,rr,fname,args,dflts,ret,ss))` >>
  `MEM source srcs` by simp[Abbr `source`] >>
  `EVERY (\d. internal_label_ok (FST d)) (internal_fn_descriptors ips)` by
    (qpat_assum `ips = MAP _ srcs` SUBST1_TAC >>
     simp[unit_package_internal_labels]) >>
  `ALL_DISTINCT (MAP FST (internal_fn_descriptors ips))` by
    (qpat_assum `extract_context_with_internals name ips run_end = SOME (raw,data)`
       (strip_assume_tac o MATCH_MP extract_context_internal_names) >>
     qpat_assum `lowering_context_ok unit.cu_context`
       (mp_tac o PURE_REWRITE_RULE [lowering_context_ok_def, ctx_fn_names_def]) >>
     asm_rewrite_tac[] >> simp[]) >>
  `gas_shadow_state run_end run_endS` by
    (qspec_then `ips` mp_tac gas_shadow_compile_internal_fn_bodies >>
     rewrite_tac[gas_shadow_compiles_def] >>
     disch_then (qspecl_then [`start`,`startS`] mp_tac) >> gvs[]) >>
  `gas_shadow_context raw rawS` by
    (qspecl_then [`run_end`,`run_endS`,`name`,`ips`] mp_tac
       gas_shadow_extract_context_with_internals >>
     gvs[optionTheory.OPTREL_def]) >>
  qabbrev_tac `pkg = set_internal_package_target rp.rpol_target
    (package_internal_fn_unit mods T (K global_nonreentrant_slot) is_ctor
      (if is_ctor then imm_len_mods mods else 0) source)` >>
  `MEM pkg ips` by
    (qpat_assum `ips = MAP _ srcs` SUBST1_TAC >>
     simp[MEM_MAP] >> qexists_tac `source` >> simp[Abbr `pkg`]) >>
  qpat_x_assum `ips = MAP _ srcs` kall_tac >>
  qpat_x_assum `MEM pkg ips` (strip_assume_tac o REWRITE_RULE [MEM_SPLIT]) >>
  rename1 `ips = xs ++ pkg::ys` >>
  PairCases_on `pkg` >>
  rename1 `Abbrev ((label,ce,params,has_rb,nr',key,trans,view,ctor,ilen,compiled_ss,rt) = _)` >>
  `set_internal_package_target rp.rpol_target
    (package_internal_fn_unit mods T (K global_nonreentrant_slot) is_ctor
      (if is_ctor then imm_len_mods mods else 0) source) =
    (label,ce,params,has_rb,nr',key,trans,view,ctor,ilen,compiled_ss,rt)` by
    (qpat_assum `Abbrev ((label,ce,params,has_rb,nr',key,trans,view,ctor,ilen,
        compiled_ss,rt) = _)` (mp_tac o REWRITE_RULE [markerTheory.Abbrev_def]) >> simp[]) >>
  `label = internal_fn_label
        (build_func_ids_mods 0 mods (nsid_to_string (src,fname)))
        (nsid_to_string (src,fname)) (MAP SND args) is_ctor /\
   compiled_ss = subst_consts_stmts_mods (consts_env_mods mods) ss` by
    (qpat_assum `set_internal_package_target _ _ = _` mp_tac >>
     simp_tac (srw_ss()) [Abbr `source`, subst_consts_fn_mods_def,
       package_internal_fn_unit_def, LET_THM, set_internal_package_target_def]) >>
  mp_tac (Q.INST [`pkg` |-> `(label,ce,params,has_rb,nr',key,trans,view,ctor,ilen,compiled_ss,rt)`,
    `nr` |-> `nr'`, `ss` |-> `compiled_ss`, `ctx` |-> `raw`, `sctx` |-> `rawS`,
    `sdata` |-> `dataS`, `sips` |-> `MAP gas_shadow_internal_package ips`]
    (REWRITE_RULE [GSYM APPEND_ASSOC, APPEND] selected_internal_shadow_code)) >>
  impl_tac >-
    (map_every (fn pattern => qpat_assum pattern
       (map_every assume_tac o CONJUNCTS o PURE_REWRITE_RULE
         [lowering_context_ok_def, ctx_fn_names_def, fn_labels_def]))
       [`lowering_context_ok unit.cu_context`,
        `lowering_context_ok shadow_unit.cu_context`] >>
     qpat_assum `ips = xs ++ _` (fn split =>
     qpat_assum `unit.cu_context.ctx_functions = raw.ctx_functions` (fn real_fns =>
     qpat_assum `shadow_unit.cu_context.ctx_functions = rawS.ctx_functions` (fn shadow_fns =>
     qpat_assum `label = internal_fn_label _ _ _ _` (fn label_eq =>
       let
         val norm = [split, SYM real_fns, SYM shadow_fns, label_eq,
                     GSYM APPEND_ASSOC, APPEND, MAP_APPEND, listTheory.MAP,
                     ctx_inst_ids_distinct_def]
         fun accept_normalized th =
           FIRST (map ACCEPT_TAC
             (CONJUNCTS (SIMP_RULE (srw_ss()) [EVERY_CONJ]
               (PURE_REWRITE_RULE norm th))))
       in
         PURE_REWRITE_TAC norm >> rpt conj_tac >>
         FIRST [first_assum accept_normalized, TRY REFL_TAC]
       end))))) >>
  strip_tac >>
  `ctx_inst_ids_distinct unit.cu_context` by fs[lowering_context_ok_def] >>
  qexistsl_tac [`rp`,`unit`,`label`,`ce`,`params`,`has_rb`,`nr'`,`key`,
    `trans`,`view`,`ctor`,`ilen`,`compiled_ss`,`rt`,
    `before`,`old`,`entry`,`final`,`sf`,
    `beforeS`,`oldS`,`entryS`,`finalS`] >>
  asm_rewrite_tac[] >>
  Cases_on `is_ctor` >> fs[] >>
  qexists_tac `bc` >> FIRST_ASSUM ACCEPT_TAC
QED
