(* Compose the site and slice witnesses for consecutive linked ABI rows. *)
Theory bodyAbiTupleEffectSitesMods
Ancestors
  bodyAbiTupleBufferStateMods abiEncoderRegisteredEffect exprLoweringProps
  venomInst venomState finite_map pred_set list pair

Theorem abi_tuple_effect_sites_trans_mods:
  abi_tuple_row_effects_mods ce ee func shared pbase capacity dst_offset cursor_site
    a u Gu tu c z Gz tz ==>
  abi_tuple_row_effects_mods ce ee func shared pbase capacity dst_offset cursor_site
    c z Gz tz e q Gq tq ==>
  (!I L J M.
    abi_encoder_registered_effect I L u z /\
    abi_encoder_registered_effect J M z q /\
    (!i. EVERY (\(b,n). i < b \/ b+n <= i) L /\
      (!aid b n. aid IN I /\ FLOOKUP z.vs_allocas aid = SOME (b,n) ==>
        i < b \/ b+n <= i) /\ i IN tz.t_mem ==> i IN tu.t_mem) /\
    (!i. EVERY (\(b,n). i < b \/ b+n <= i) M /\
      (!aid b n. aid IN J /\ FLOOKUP q.vs_allocas aid = SOME (b,n) ==>
        i < b \/ b+n <= i) /\ i IN tq.t_mem ==> i IN tz.t_mem) ==>
    abi_encoder_registered_effect (I UNION J) (L ++ M) u q /\
    (!i. EVERY (\(b,n). i < b \/ b+n <= i) (L ++ M) /\
      (!aid b n. aid IN I UNION J /\ FLOOKUP q.vs_allocas aid = SOME (b,n) ==>
        i < b \/ b+n <= i) /\ i IN tq.t_mem ==> i IN tu.t_mem)) ==>
  ?ids outs.
    shared NOTIN ids /\
    EVERY (\(b,n). pbase+dst_offset <= b /\ b+n <= pbase+capacity) outs /\
    (cursor_site IN ids ==>
      cursor_site < e.cs_next_id /\ ?slot. FLOOKUP q.vs_allocas cursor_site = SOME (slot,32)) /\
    (!aid. aid IN ids ==>
      (aid <> cursor_site ==> a.cs_next_id <= aid /\ aid < e.cs_next_id) /\
      ?inst x. MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\
        inst.inst_id = aid /\ inst.inst_outputs = [x] /\ not_local_ptr ce ee.scopes x) /\
    abi_encoder_registered_effect ids outs u q /\
    (!i. EVERY (\(b,n). i < b \/ b+n <= i) outs /\
      (!aid b n. aid IN ids /\ FLOOKUP q.vs_allocas aid = SOME (b,n) ==>
        i < b \/ b+n <= i) /\ i IN tq.t_mem ==> i IN tu.t_mem)
Proof
  disch_then (strip_assume_tac o REWRITE_RULE [abi_tuple_row_effects_mods_def]) >>
  rename1 `abi_encoder_registered_effect ids1 outs1 u z` >>
  disch_then (strip_assume_tac o REWRITE_RULE [abi_tuple_row_effects_mods_def]) >>
  rename1 `abi_encoder_registered_effect ids2 outs2 z q` >>
  disch_then (mk_asm "sequence") >>
  `a.cs_next_id <= c.cs_next_id /\ c.cs_next_id <= e.cs_next_id` by
    fs[ci_mono_def] >>
  qexistsl [`ids1 UNION ids2`,`outs1 ++ outs2`] >>
  conj_tac >- simp[IN_UNION] >>
  conj_tac >- simp[] >>
  conj_tac >-
    (pure_rewrite_tac [IN_UNION] >> disch_then DISJ_CASES_TAC
     >- (qpat_assum `cursor_site IN ids1 ==> _` (drule_then strip_assume_tac) >>
         conj_tac >- metis_tac[arithmeticTheory.LESS_LESS_EQ_TRANS] >>
         qexists `slot` >> irule abi_encoder_registered_effect_allocated >>
         metis_tac[])
     >> metis_tac[]) >>
  conj_tac >-
    (gen_tac >> pure_rewrite_tac [IN_UNION] >> disch_then DISJ_CASES_TAC
     >- (qpat_assum `!aid. aid IN ids1 ==> _` (drule_then strip_assume_tac) >>
         conj_tac >- metis_tac[arithmeticTheory.LESS_LESS_EQ_TRANS] >> metis_tac[])
     >> qpat_assum `!aid. aid IN ids2 ==> _` (drule_then strip_assume_tac) >>
     conj_tac >- metis_tac[arithmeticTheory.LESS_EQ_TRANS] >> metis_tac[]) >>
  asm_x "sequence" (qspecl_then [`ids1`,`outs1`,`ids2`,`outs2`] irule) >>
  rpt conj_tac >> first_assum ACCEPT_TAC
QED
