Theory groupedEntryCommon
Ancestors
  fragGasOriginPtrLoop fragFuel fragExec emitHelperProps venomExecSemantics
  venomState venomInst loweringStateRelDefs selectedAcceptedFold
  entryStateRel moduleLowering bodyPtrDefs valueEncoding valueEncodingTyping ptrDiscipline exprSimProps
  finite_map alist list words

Theorem grouped_entry_jump_to_common:
  emit_inst JMP [Label st.cs_current_bb] [] cut = ((),term) /\
  fn_has_code cut term fn /\ at_point cut s /\
  st.cs_current_insts = [] /\
  ~s.vs_halted /\ allocas_from lo s /\
  (ctx_has_dalloca ctx ==> allocas_below_fmp s) ==>
  at_point st (jump_to st.cs_current_bb s) /\
  !D exp. gas_origin_ptr_path (D,lo,exp,ctx,fn,PG)
    (s,G,tn) [] (OK (jump_to st.cs_current_bb s),G,tn)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  conj_tac >- simp[at_point_def, jump_to_def] >>
  drule emit_inst_extends >> strip_tac >>
  mp_tac (Q.SPECL [`cut`,`term`,`fn`,
    `[mk_inst cut.cs_next_id JMP [Label st.cs_current_bb] []]`] fn_has_code_same_block) >>
  impl_tac >- asm_rewrite_tac[] >>
  disch_then (qx_choose_then `bb` strip_assume_tac) >>
  qpat_assum `!i. i < _ ==> _` (qspec_then `0` mp_tac) >>
  fs[at_point_def] >> strip_tac >>
  rpt gen_tac >> irule jmp_origin_ptr_path >> asm_rewrite_tac[] >>
  qexistsl_tac [`bb`,`cut.cs_next_id`] >> simp[]
QED

Theorem grouped_jump_registration_owners:
  selected_registration_owners fn names tvs vals i ce cut s G tn /\
  cut.cs_next_id <= st.cs_next_id ==>
  selected_registration_owners fn names tvs vals i ce st
    (jump_to st.cs_current_bb s) G tn
Proof
  simp[selected_registration_owners_def, jump_to_def, lookup_var_def, ptr_covers_def] >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  gen_tac >> strip_tac >>
  qpat_assum `!j. j < i ==> _` (drule_then strip_assume_tac) >>
  qexistsl_tac [`aid`,`q`,`p`] >> asm_rewrite_tac[] >>
  conj_tac >- decide_tac >>
  metis_tac[]
QED

Theorem grouped_initialized_keyword_owners:
  ALL_DISTINCT (MAP (\(name,_,_,_). name) vars) /\
  LIST_REL (\(name,dst,ty,e) (aid,q,p,tv).
    dst = Var q /\ type_memory_bytes ce ty = type_memory_size tv /\
    MEM (mk_inst aid ALLOCA [Lit (n2w (type_memory_size tv))] [q]) (fn_insts fn))
    vars slots /\
  LIST_REL (\(aid,q,p,tv) v.
    aid < st.cs_next_id /\ FLOOKUP s.vs_allocas aid = SOME (p,type_memory_size tv) /\
    lookup_var q s = SOME (n2w p) /\ ptr_covers G tn q s (type_memory_size tv) /\
    value_has_type tv v /\
    (!mem. mem_agree_outside tn.t_mem s.vs_memory mem ==>
      val_in_memory tv v p mem)) slots vals ==>
  selected_registration_owners fn
    (MAP (\(name,_,_,_). name) vars) (MAP (\(_,_,_,tv). tv) slots)
    vals (LENGTH vars) (compile_register_kwarg_vars ce vars) st s G tn
Proof
  simp_tac bool_ss [selected_registration_owners_def, LIST_REL_EL_EQN] >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  gen_tac >> strip_tac >>
  `j < LENGTH slots` by decide_tac >>
  `?name dst ty e. EL j vars = (name,dst,ty,e)` by metis_tac[pairTheory.PAIR] >>
  `?aid q p tv. EL j slots = (aid,q,p,tv)` by metis_tac[pairTheory.PAIR] >>
  `j < LENGTH vars` by decide_tac >>
  qpat_assum `EL j vars = _` (fn vars_eq =>
    qpat_assum `EL j slots = _` (fn slots_eq =>
      qpat_assum `j < LENGTH vars` (fn bound =>
        qpat_assum `!n. n < LENGTH vars ==> _`
          (map_every assume_tac o CONJUNCTS o
           SIMP_RULE (srw_ss()) [vars_eq,slots_eq] o
           (fn th => MATCH_MP th bound))))) >>
  qpat_assum `EL j slots = _` (fn slots_eq =>
    qpat_assum `j < LENGTH slots` (fn bound =>
      qpat_assum `!n. n < LENGTH slots ==> _`
        (map_every assume_tac o CONJUNCTS o
         SIMP_RULE (srw_ss()) [slots_eq] o
         (fn th => MATCH_MP th bound)))) >>
  `value_has_type tv (EL j vals)` by first_assum ACCEPT_TAC >>
  drule (cj 1 value_has_type_val_wf) >> strip_tac >>
  qexistsl_tac [`aid`,`q`,`p`] >>
  asm_simp_tac (srw_ss()) [EL_MAP, val_footprint_le] >>
  simp[cj 2 compile_register_kwarg_vars_cenv] >>
  `ALOOKUP (MAP (\(id,op,ty,e). (id,PtrVar op (type_memory_bytes ce ty)))
    (REVERSE vars)) name = SOME (PtrVar (Var q) (type_memory_size tv))` suffices_by simp[] >>
  irule ALOOKUP_ALL_DISTINCT_MEM >>
  conj_tac
  >- (qpat_assum `ALL_DISTINCT _` mp_tac >>
      simp[MAP_MAP_o, combinTheory.o_DEF, LIST_EQ_REWRITE, EL_MAP, MAP_REVERSE,
        pairTheory.LAMBDA_PROD]) >>
  simp[MEM_MAP, MEM_REVERSE, pairTheory.EXISTS_PROD] >>
  qexistsl_tac [`ty`,`e`] >>
  asm_rewrite_tac[] >>
  metis_tac[MEM_EL]
QED
