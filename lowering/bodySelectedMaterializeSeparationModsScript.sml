(* Separation at the actual post-scratch cursor of a selected internal call. *)
Theory bodySelectedMaterializeSeparationMods
Ancestors
  intCallCallee bodyInvSplit bodySimFull exprLoweringProps loweringPosts
  loweringStateRelDefs compileEnv venomState ptrDiscipline vyperState

(* Scratch preserves the variables used by the materialized local pointers.
   Only its new allocation sites need a separate lower bound. *)
Theorem materialized_prelock_ranges[local]:
  mat_inv callee mat_ce penv materialized mat_state f0 mr /\
  es.scopes = [penv] /\ body_ce.ce_vars = mat_ce.ce_vars /\
  local_ptrs_reserved mat_ce materialized /\
  (!q. not_fresh_at materialized q ==> lookup_var q at_pro = lookup_var q mat_state) /\
  mat_state.vs_alloca_next <= at_pro.vs_alloca_next /\
  (!aid b sz. FLOOKUP at_pro.vs_allocas aid = SOME (b,sz) ==>
    FLOOKUP mat_state.vs_allocas aid = SOME (b,sz) \/ mat_state.vs_alloca_next <= b) ==>
  f0 <= at_pro.vs_alloca_next /\ allocas_from f0 at_pro /\
  (!n b sz. local_region body_ce es.scopes at_pro n b sz ==>
    f0 <= b \/ mr n = SOME (b,sz))
Proof
  strip_tac >>
  qpat_x_assum `mat_inv _ _ _ _ _ _ _`
    (strip_assume_tac o REWRITE_RULE [mat_inv_def]) >>
  conj_tac >- decide_tac >> conj_tac
  >- (simp[allocas_from_def] >> rpt strip_tac >>
      qpat_assum `!aid b sz. FLOOKUP at_pro.vs_allocas aid = _ ==> _`
        (drule_then strip_assume_tac) >>
      metis_tac[arithmeticTheory.LESS_EQ_TRANS]) >>
  rpt gen_tac >> disch_tac >>
  qpat_assum `!n b sz. local_region mat_ce _ mat_state n b sz ==> _` irule >>
  qpat_x_assum `local_region body_ce _ at_pro _ _ _` mp_tac >>
  simp[local_region_def] >> strip_tac >>
  `not_fresh_at materialized p` by metis_tac[local_ptrs_reserved_def] >>
  qpat_assum `!q. not_fresh_at materialized q ==> _` (drule_then assume_tac) >>
  qexistsl_tac [`entry`, `p`, `w`] >> gvs[]
QED

Theorem materialized_protected_range[local]:
  t.vs_alloca_next <= f0 /\ f0 <= at_pro.vs_alloca_next /\
  allocas_from f0 at_pro /\ (off:num) + width <= t.vs_alloca_next /\
  (!i b sz. MEM i (fn_insts caller) /\ i.inst_opcode = ALLOCA /\
    FLOOKUP t.vs_allocas i.inst_id = SOME (b,sz) ==>
    loweringStateRelDefs$regions_disjoint off width b sz) /\
  (!n b sz. local_region ce scopes at_pro n b sz ==>
    f0 <= b \/ ?i base len. MEM i (fn_insts caller) /\ i.inst_opcode = ALLOCA /\
      FLOOKUP t.vs_allocas i.inst_id = SOME (base,len) /\
      base <= b /\ b + sz <= base + len) ==>
  (off:num) + width <= at_pro.vs_alloca_next /\
  (!aid b sz. FLOOKUP at_pro.vs_allocas aid = SOME (b,sz) ==>
    loweringStateRelDefs$regions_disjoint off width b sz) /\
  (!n b sz. local_region ce scopes at_pro n b sz ==>
    loweringStateRelDefs$regions_disjoint off width b sz)
Proof
  strip_tac >> conj_tac >- decide_tac >> conj_tac
  >- (rpt strip_tac >>
      qpat_assum `allocas_from f0 at_pro` (drule_then assume_tac o REWRITE_RULE [allocas_from_def]) >>
      simp[loweringStateRelDefsTheory.regions_disjoint_def] >> decide_tac) >>
  rpt strip_tac >>
  qpat_assum `!n b sz. local_region ce scopes at_pro n b sz ==> _`
    (drule_then strip_assume_tac)
  >- (simp[loweringStateRelDefsTheory.regions_disjoint_def] >> decide_tac) >>
  qpat_assum `!i b sz. MEM i (fn_insts caller) /\ _ ==> _` drule_all >>
  simp[loweringStateRelDefsTheory.regions_disjoint_def] >> decide_tac
QED

Theorem materialized_qualified_immutable_sep[local]:
  immutable_alloca_sep_mods caller cenv cx old t /\
  cenv.ce_modules = body_ce.ce_modules /\ cenv.ce_is_ctor = body_ce.ce_is_ctor /\
  cenv.ce_module_vars = body_ce.ce_module_vars /\
  cenv.ce_module_var_type = body_ce.ce_module_var_type /\ old.immutables = es.immutables /\
  t.vs_alloca_next <= f0 /\ f0 <= at_pro.vs_alloca_next /\ allocas_from f0 at_pro /\
  (!n b sz. local_region body_ce es.scopes at_pro n b sz ==>
    f0 <= b \/ ?i base len. MEM i (fn_insts caller) /\ i.inst_opcode = ALLOCA /\
      FLOOKUP t.vs_allocas i.inst_id = SOME (base,len) /\
      base <= b /\ b + sz <= base + len) ==>
  immutable_alloca_sep_mods callee body_ce cx es at_pro
Proof
  simp[immutable_alloca_sep_mods_def] >> strip_tac >> rpt gen_tac >> disch_tac >>
  rename1 `ALOOKUP body_ce.ce_modules src = SOME tops` >>
  qpat_x_assum `!src tops. _ ==> immutable_alloca_sep caller _ _ _ _`
    (qspecl_then [`src`, `tops`] mp_tac) >>
  simp[immutable_alloca_sep_def, immutable_decl_sep_alt] >> strip_tac >>
  `!off width. (off:num) + width <= t.vs_alloca_next /\
      (!i b sz. MEM i (fn_insts caller) /\ i.inst_opcode = ALLOCA /\
        FLOOKUP t.vs_allocas i.inst_id = SOME (b,sz) ==>
        loweringStateRelDefs$regions_disjoint off width b sz) ==>
      (off:num) + width <= at_pro.vs_alloca_next /\
      (!aid b sz. FLOOKUP at_pro.vs_allocas aid = SOME (b,sz) ==>
        loweringStateRelDefs$regions_disjoint off width b sz) /\
      (!n b sz. local_region (body_ce with ce_module := src) es.scopes at_pro n b sz ==>
        loweringStateRelDefs$regions_disjoint off width b sz)` by
    (rpt gen_tac >> disch_tac >> irule materialized_protected_range >>
     qexistsl_tac [`caller`, `f0`, `t`] >> asm_rewrite_tac[] >>
     simp[local_region_def] >>
     qpat_assum `!n b sz. local_region body_ce _ _ _ _ _ ==> _`
       (mp_tac o REWRITE_RULE [local_region_def]) >> simp[]) >>
  Cases_on `body_ce.ce_is_ctor` >> fs[] >> conj_tac
  >- (rpt gen_tac >> strip_tac >>
      qpat_assum `!name ty tv off. _ ==> _` (drule_all_then strip_assume_tac) >>
      qpat_assum `!off width. _ ==> _` irule >>
      reverse conj_tac >- first_assum ACCEPT_TAC >> rpt strip_tac >>
      qpat_assum `!aid b sz. FLOOKUP t.vs_allocas aid = _ ==> _`
        (drule_then ACCEPT_TAC)) >>
  rpt gen_tac >> strip_tac >>
  qpat_assum `!name tv v off. _ ==> _` (drule_all_then strip_assume_tac) >>
  qpat_assum `!off width. _ ==> _` (qspecl_then [`off`, `type_memory_size tv`] mp_tac) >>
  (impl_tac >- (conj_tac >> first_assum ACCEPT_TAC)) >>
  strip_tac >> asm_rewrite_tac[] >>
  rpt strip_tac >>
  qpat_assum `!aid b sz. FLOOKUP at_pro.vs_allocas aid = _ ==> _`
    (drule_then ACCEPT_TAC)
QED

(* The low locals are classified by the same parameter indices as their
   caller allocation and return-buffer separation witnesses at the INVOKE. *)
Theorem selected_materialize_separation_mods:
  immutable_alloca_sep_mods caller cenv cx old t /\
  cenv.ce_modules = body_ce.ce_modules /\ cenv.ce_is_ctor = body_ce.ce_is_ctor /\
  cenv.ce_module_vars = body_ce.ce_module_vars /\
  cenv.ce_module_var_type = body_ce.ce_module_var_type /\ old.immutables = es.immutables /\
  t.vs_alloca_next <= f0 /\
  mat_inv callee mat_ce penv materialized mat_state f0 mr /\
  es.scopes = [penv] /\ body_ce.ce_vars = mat_ce.ce_vars /\
  local_ptrs_reserved mat_ce materialized /\
  (!q. not_fresh_at materialized q ==> lookup_var q at_pro = lookup_var q mat_state) /\
  mat_state.vs_alloca_next <= at_pro.vs_alloca_next /\
  (!aid b sz. FLOOKUP at_pro.vs_allocas aid = SOME (b,sz) ==>
    FLOOKUP mat_state.vs_allocas aid = SOME (b,sz) \/ mat_state.vs_alloca_next <= b) /\
  idx = (if has_rb then 1 else 0) /\
  (!n b sz. mr n = SOME (b,sz) ==>
    ?i off. i < LENGTH params /\ ~SND (EL i params) /\ FST (EL i params) = n /\
      FLOOKUP ce_args.ce_vars n = SOME (MemLoc off sz) /\ b = w2n (EL (idx + i) argv)) /\
  (!i off sz. i < LENGTH params /\ ~SND (EL i params) /\
    FLOOKUP ce_args.ce_vars (FST (EL i params)) = SOME (MemLoc off sz) ==>
    ?inst base len. MEM inst (fn_insts caller) /\ inst.inst_opcode = ALLOCA /\
      FLOOKUP t.vs_allocas inst.inst_id = SOME (base,len) /\
      base <= w2n (EL (idx + i) argv) /\ w2n (EL (idx + i) argv) + sz <= base + len) /\
  dret = (if has_rb then SOME (HD argv,type_memory_size rtv) else NONE) /\
  (has_rb ==> ?base len. op_prov G (HD arg_ops) = SOME (base,len) /\
    base <= w2n (HD argv) /\ w2n (HD argv) + type_memory_size rtv <= base + len /\
    base + len <= t.vs_alloca_next /\ lo <= base) /\
  (has_rb ==> !i off sz. i < LENGTH params /\ ~SND (EL i params) /\
    FLOOKUP ce_args.ce_vars (FST (EL i params)) = SOME (MemLoc off sz) ==>
    loweringStateRelDefs$regions_disjoint (w2n (HD argv)) (type_memory_size rtv)
      (w2n (EL (1 + i) argv)) sz) ==>
  immutable_alloca_sep_mods callee body_ce cx es at_pro /\
  return_buf_sep dret body_ce es at_pro /\
  f0 <= at_pro.vs_alloca_next /\ allocas_from f0 at_pro /\
  (!n b sz. local_region body_ce es.scopes at_pro n b sz ==>
    f0 <= b \/ ?i base len. MEM i (fn_insts caller) /\ i.inst_opcode = ALLOCA /\
      FLOOKUP t.vs_allocas i.inst_id = SOME (base,len) /\
      base <= b /\ b + sz <= base + len)
Proof
  strip_tac >>
  qpat_x_assum `idx = _` SUBST_ALL_TAC >>
  drule_all_then strip_assume_tac materialized_prelock_ranges >>
  `!n b sz. local_region body_ce es.scopes at_pro n b sz ==>
    f0 <= b \/ ?i base len. MEM i (fn_insts caller) /\ i.inst_opcode = ALLOCA /\
      FLOOKUP t.vs_allocas i.inst_id = SOME (base,len) /\
      base <= b /\ b + sz <= base + len` by
    (rpt strip_tac >>
     qpat_assum `!n b sz. local_region _ _ _ _ _ _ ==> _` (drule_then strip_assume_tac)
     >- simp[] >> disj2_tac >>
     qpat_assum `!n b sz. mr n = SOME (b,sz) ==> _` (drule_then strip_assume_tac) >>
     qpat_x_assum `FST (EL i params) = n` (SUBST_ALL_TAC o SYM) >>
     qpat_assum `!i off sz. i < LENGTH params /\ _ ==> ?inst base len. _`
       (drule_all_then strip_assume_tac) >>
     rename1 `FLOOKUP t.vs_allocas site.inst_id = SOME (site_base,site_len)` >>
     qexistsl_tac [`site`, `site_base`, `site_len`] >> fs[]) >>
  conj_tac
  >- (irule materialized_qualified_immutable_sep >>
      qexistsl_tac [`caller`, `cenv`, `f0`, `old`, `t`] >> asm_rewrite_tac[]) >>
  reverse conj_tac >- asm_rewrite_tac[] >>
  Cases_on `has_rb` >> gvs[return_buf_sep_def] >>
  `w2n (HD argv) + type_memory_size rtv <= f0` by decide_tac >>
  conj_tac
  >- (simp[allocas_from_def] >> rpt strip_tac >>
      qpat_assum `allocas_from f0 at_pro`
        (drule_then assume_tac o REWRITE_RULE [allocas_from_def]) >> decide_tac) >>
  rpt strip_tac >>
  qpat_assum `!n b sz. local_region _ _ _ _ _ _ ==> _ \/ mr _ = _`
    (drule_then strip_assume_tac)
  >- (simp[loweringStateRelDefsTheory.regions_disjoint_def] >> decide_tac) >>
  qpat_assum `!n b sz. mr n = SOME (b,sz) ==> _` (drule_then strip_assume_tac) >>
  qpat_x_assum `FST (EL i params) = n` (SUBST_ALL_TAC o SYM) >>
  qpat_assum `!i off sz. i < LENGTH params /\ _ ==> loweringStateRelDefs$regions_disjoint _ _ _ _`
    drule_all >> simp[]
QED
