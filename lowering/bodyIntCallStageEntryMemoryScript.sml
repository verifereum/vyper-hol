(* Indexed memory-parameter ownership at the single staging endpoint. *)
Theory bodyIntCallStageEntryMemory
Ancestors
  bodyIntCallStagePackage bodyIntCallStageReturn bodyIntCallStageOwned
  venomExecProofs tupleLoadProps compileEnv list pair finite_map
  bodyIntCallImmutableBoundary

Theorem staged_memory_parameter:
  EVERY (staged_arg caller func es a sm s) D /\
  LENGTH params = LENGTH D /\
  eval_operands (MAP (\(ty,tv,v,flag,op). op) D) s = SOME ws /\
  (!i. i < LENGTH D ==>
    (\(ty,tv,v,flag,op).
      flag = SND (EL i params) /\
      ?off. FLOOKUP ce.ce_vars (FST (EL i params)) =
        SOME (MemLoc off (type_memory_size tv))) (EL i D)) /\
  i < LENGTH params /\ ~SND (EL i params) /\
  FLOOKUP ce.ce_vars (FST (EL i params)) = SOME (MemLoc po psz) ==>
  ?ty tv v op.
    staged_arg caller func es a sm s (ty,tv,v,F,op) /\
    eval_operand op s = SOME (EL i ws) /\ psz = type_memory_size tv
Proof
  strip_tac >>
  qpat_x_assum `!i. i < LENGTH D ==> _` (qspec_then `i` mp_tac) >>
  (impl_tac >- simp[]) >> disch_tac >>
  qpat_x_assum `EVERY _ D` mp_tac >> simp[EVERY_EL] >>
  disch_then (qspec_then `i` mp_tac) >>
  (impl_tac >- simp[]) >> disch_tac >>
  `eval_operand ((\(ty,tv,v,flag,op). op) (EL i D)) s = SOME (EL i ws)` by
    (drule eval_operands_index >>
     disch_then (qspec_then `i` mp_tac) >> simp[EL_MAP]) >>
  Cases_on `EL i D` >> rename1 `(ty,rest)` >> PairCases_on `rest` >>
  gvs[] >> metis_tac[]
QED

Theorem staged_memory_parameter_allocation:
  EVERY (staged_arg caller func es a sm s) D /\
  LENGTH params = LENGTH D /\
  eval_operands (MAP (\(ty,tv,v,flag,op). op) D) s = SOME ws /\
  (!i. i < LENGTH D ==>
    (\(ty,tv,v,flag,op).
      flag = SND (EL i params) /\
      ?off. FLOOKUP ce.ce_vars (FST (EL i params)) =
        SOME (MemLoc off (type_memory_size tv))) (EL i D)) /\
  i < LENGTH params /\ ~SND (EL i params) /\
  FLOOKUP ce.ce_vars (FST (EL i params)) = SOME (MemLoc po psz) ==>
  ?aid off asz.
    FLOOKUP s.vs_allocas aid = SOME (off,asz) /\
    (?inst. MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\
            inst.inst_id = aid) /\
    a.cs_next_id <= aid /\ aid < sm.cs_next_id /\
    off <= w2n (EL i ws) /\ w2n (EL i ws) + psz <= off + asz
Proof
  strip_tac >> drule_all staged_memory_parameter >> strip_tac >>
  gvs[staged_arg_def] >>
  qexistsl_tac [`inst.inst_id`,`off`,`sz`] >> simp[] >> metis_tac[]
QED

Theorem staged_memory_parameter_return_disjoint:
  EVERY (staged_arg caller func es a sm s) D /\
  LENGTH params = LENGTH D /\
  eval_operands (MAP (\(ty,tv,v,flag,op). op) D) s = SOME ws /\
  (!i. i < LENGTH D ==>
    (\(ty,tv,v,flag,op).
      flag = SND (EL i params) /\
      ?off. FLOOKUP ce.ce_vars (FST (EL i params)) =
        SOME (MemLoc off (type_memory_size tv))) (EL i D)) /\
  i < LENGTH params /\ ~SND (EL i params) /\
  FLOOKUP ce.ce_vars (FST (EL i params)) = SOME (MemLoc po psz) /\
  alloca_inv s /\ rid < a.cs_next_id /\
  FLOOKUP s.vs_allocas rid = SOME (rb,cap) /\ rsz <= cap ==>
  regions_disjoint rb rsz (w2n (EL i ws)) psz
Proof
  strip_tac >> drule_all staged_memory_parameter >> strip_tac >> gvs[] >>
  drule_all staged_arg_old_allocation_disjoint >> simp[]
QED

Theorem staged_memory_parameter_immutable_disjoint:
  EVERY (staged_arg caller func es a sm s) D /\
  LENGTH params = LENGTH D /\
  eval_operands (MAP (\(ty,tv,v,flag,op). op) D) s = SOME ws /\
  (!i. i < LENGTH D ==>
    (\(ty,tv,v,flag,op).
      flag = SND (EL i params) /\
      ?off. FLOOKUP ce.ce_vars (FST (EL i params)) =
        SOME (MemLoc off (type_memory_size tv))) (EL i D)) /\
  i < LENGTH params /\ ~SND (EL i params) /\
  FLOOKUP ce.ce_vars (FST (EL i params)) = SOME (MemLoc po psz) /\
  stmt_state_rel ctx func caller cx es s /\ caller.ce_is_ctor /\
  FLOOKUP caller.ce_module_vars (caller.ce_module,nm) = SOME (ImmutableLoc io) /\
  FLOOKUP (case ALOOKUP es.immutables cx.txn.target of
    NONE => FEMPTY | SOME imms => get_source_immutables caller.ce_module imms) nm =
    SOME (itv,iv) ==>
  regions_disjoint io (type_memory_size itv) (w2n (EL i ws)) psz
Proof
  strip_tac >> drule_all staged_memory_parameter_allocation >> strip_tac >>
  drule_all initialized_immutable_regions >> strip_tac >>
  gvs[] >>
  qpat_x_assum `!inst b sz. MEM inst _ /\ _ ==> _`
    (qspec_then `inst` mp_tac) >>
  simp[regions_disjoint_def] >> decide_tac
QED
