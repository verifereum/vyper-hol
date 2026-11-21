Theory groupedEntryCommon
Ancestors
  fragGasOriginPtrLoop fragFuel fragExec emitHelperProps venomExecSemantics
  venomState venomInst loweringStateRelDefs selectedAcceptedFold
  entryStateRel moduleLowering bodyPtrDefs valueEncoding valueEncodingTyping ptrDiscipline
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
