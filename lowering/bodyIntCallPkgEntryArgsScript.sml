(* Entry-state and memory boundaries for staged internal-call arguments. *)
Theory bodyIntCallPkgEntryArgs
Ancestors
  bodyIntCallPkgEntryMetadata bodyIntCallStageEntryMemory bodyIntCallStagePackage
  bodyIntCallPackageGlobals bodyIntCallImmutableBoundary bodyIntCallStageOwned
  exprLoweringProps intCallCallee venomExecProofs vyperState list words finite_map

Theorem internal_package_entry_globals:
  stmt_state_rel ctx func caller cx (es with scopes := prev) t /\
  ce.ce_module = caller.ce_module /\
  ce.ce_module_vars = caller.ce_module_vars /\
  ce.ce_is_ctor = caller.ce_is_ctor ==>
  (ce.ce_is_ctor ==> IS_SOME (FLOOKUP t.vs_labels "runtime_begin")) /\
  state_rel func ce cx (es with scopes := []) t /\
  internal_immutable_regions ce cx es t.vs_alloca_next
Proof
  strip_tac >>
  `state_rel func caller cx (es with scopes := prev) t /\
   immutable_base_zero caller t` by fs[stmt_state_rel_def] >>
  drule_all package_globals_state_rel >>
  drule_all package_initialized_immutable_regions >>
  gvs[immutable_base_zero_alt, internal_immutable_regions_def] >> metis_tac[]
QED

Theorem staged_entry_args_rel:
  EVERY (staged_arg caller func es a sm t) D /\ alloca_inv t /\
  ALL_DISTINCT (MAP FST params) /\ FDOM env = set (MAP FST params) /\
  LENGTH params = LENGTH D /\
  LENGTH ((if has_rb then [rbw] else []) ++ ws) < dimword (:256) /\
  eval_operands (MAP (\(ty,tv,v,flag,op). op) D) t = SOME ws /\
  (!i. i < LENGTH D ==>
    (\(ty,tv,v,flag,op).
      flag = SND (EL i params) /\ evaluate_type tenv ty = SOME tv /\
      (flag ==> is_word_type ty) /\
      FLOOKUP env (FST (EL i params)) =
        SOME <|assignable := T; type := tv; value := v; popped := []|> /\
      ?off. FLOOKUP ce.ce_vars (FST (EL i params)) =
        SOME (MemLoc off (type_memory_size tv))) (EL i D)) /\
  (!i j. i < LENGTH D /\ j < LENGTH D /\ i <> j ==>
    (\(ty,tv,v,flag,op) (ty',tv',v',flag',op').
      ~flag /\ ~flag' ==>
      !w w'. eval_operand op t = SOME w /\ eval_operand op' t = SOME w' ==>
      regions_disjoint (w2n w) (type_memory_size tv)
        (w2n w') (type_memory_size tv')) (EL i D) (EL j D)) ==>
  internal_args_rel ce params env (if has_rb then 1 else 0)
    ((if has_rb then [rbw] else []) ++ ws) t.vs_alloca_next t.vs_memory
Proof
  strip_tac >> drule_all staged_args_internal_rel >>
  Cases_on `has_rb` >> simp[]
QED

Theorem staged_entry_memory:
  EVERY (staged_arg caller func es a sm t) D /\
  LENGTH params = LENGTH D /\
  eval_operands (MAP (\(ty,tv,v,flag,op). op) D) t = SOME ws /\
  (!i. i < LENGTH D ==>
    (\(ty,tv,v,flag,op).
      flag = SND (EL i params) /\
      ?off. FLOOKUP ce.ce_vars (FST (EL i params)) =
        SOME (MemLoc off (type_memory_size tv))) (EL i D)) /\
  stmt_state_rel ctx func caller cx es t /\
  ce.ce_module = caller.ce_module /\
  ce.ce_module_vars = caller.ce_module_vars /\
  ce.ce_is_ctor = caller.ce_is_ctor /\
  lo <= a.cs_next_id /\ sm.cs_next_id <= hi /\
  (has_rb ==> ?rid off cap.
    FLOOKUP t.vs_allocas rid = SOME (off,cap) /\ rid < a.cs_next_id /\
    rbw = n2w off /\ off < dimword (:256) /\ rsz <= cap) ==>
  (!i po psz.
    i < LENGTH params /\ ~SND (EL i params) /\
    FLOOKUP ce.ce_vars (FST (EL i params)) = SOME (MemLoc po psz) ==>
    ?aid off asz.
      FLOOKUP t.vs_allocas aid = SOME (off,asz) /\
      (?inst. MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\
        inst.inst_id = aid) /\
      lo <= aid /\ aid < hi /\
      off <= w2n (EL ((if has_rb then 1 else 0) + i)
        ((if has_rb then [rbw] else []) ++ ws)) /\
      w2n (EL ((if has_rb then 1 else 0) + i)
        ((if has_rb then [rbw] else []) ++ ws)) + psz <= off + asz) /\
  (has_rb ==> !i po psz.
    i < LENGTH params /\ ~SND (EL i params) /\
    FLOOKUP ce.ce_vars (FST (EL i params)) = SOME (MemLoc po psz) ==>
    regions_disjoint (w2n rbw) rsz
      (w2n (EL (1 + i) ([rbw] ++ ws))) psz) /\
  (ce.ce_is_ctor ==> !i po psz nm tv iv io.
    i < LENGTH params /\ ~SND (EL i params) /\
    FLOOKUP ce.ce_vars (FST (EL i params)) = SOME (MemLoc po psz) /\
    FLOOKUP ce.ce_module_vars (ce.ce_module,nm) = SOME (ImmutableLoc io) /\
    FLOOKUP (case ALOOKUP es.immutables cx.txn.target of
      NONE => FEMPTY | SOME imms => get_source_immutables ce.ce_module imms) nm =
      SOME (tv,iv) ==>
    regions_disjoint io (type_memory_size tv)
      (w2n (EL ((if has_rb then 1 else 0) + i)
        ((if has_rb then [rbw] else []) ++ ws))) psz)
Proof
  strip_tac >>
  `alloca_inv t` by fs[stmt_state_rel_def] >>
  conj_tac
  >- (rpt gen_tac >> strip_tac >>
      drule_all staged_memory_parameter_allocation >> strip_tac >>
      Cases_on `has_rb` >> simp[] >>
      qexistsl_tac [`aid`,`off`,`asz`] >>
      simp[GSYM arithmeticTheory.ADD1] >> metis_tac[arithmeticTheory.LESS_EQ_TRANS,
        arithmeticTheory.LESS_LESS_EQ_TRANS]) >>
  conj_tac
  >- (strip_tac >> rpt gen_tac >> strip_tac >>
      first_x_assum drule >> strip_tac >> gvs[] >>
      `i < LENGTH params` by simp[] >>
      drule_all staged_memory_parameter_return_disjoint >>
      simp[GSYM arithmeticTheory.ADD1]) >>
  rpt strip_tac >>
  `caller.ce_is_ctor` by metis_tac[] >>
  `FLOOKUP caller.ce_module_vars (caller.ce_module,nm) = SOME (ImmutableLoc io)` by
    metis_tac[] >>
  `FLOOKUP (case ALOOKUP es.immutables cx.txn.target of
    NONE => FEMPTY | SOME imms => get_source_immutables caller.ce_module imms) nm =
      SOME (tv,iv)` by metis_tac[] >>
  drule_all staged_memory_parameter_immutable_disjoint >>
  Cases_on `has_rb` >> simp[GSYM arithmeticTheory.ADD1]
QED

Theorem entry_return_immutable_disjoint:
  stmt_state_rel ctx func caller cx es t /\ caller.ce_is_ctor /\
  ce.ce_module = caller.ce_module /\
  ce.ce_module_vars = caller.ce_module_vars /\
  FLOOKUP t.vs_allocas rid = SOME (off,cap) /\
  MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\
  inst.inst_id = rid /\ rsz <= cap /\
  FLOOKUP ce.ce_module_vars (ce.ce_module,nm) = SOME (ImmutableLoc io) /\
  FLOOKUP (case ALOOKUP es.immutables cx.txn.target of
    NONE => FEMPTY | SOME imms => get_source_immutables ce.ce_module imms) nm =
      SOME (tv,iv) ==>
  regions_disjoint io (type_memory_size tv) off rsz
Proof
  strip_tac >>
  `FLOOKUP caller.ce_module_vars (caller.ce_module,nm) = SOME (ImmutableLoc io) /\
   FLOOKUP (case ALOOKUP es.immutables cx.txn.target of
     NONE => FEMPTY | SOME imms => get_source_immutables caller.ce_module imms) nm =
       SOME (tv,iv)` by metis_tac[] >>
  drule_all initialized_immutable_regions >> strip_tac >>
  qpat_x_assum `!inst b sz. _` (qspec_then `inst` mp_tac) >>
  simp[compileEnvTheory.regions_disjoint_def] >> decide_tac
QED
