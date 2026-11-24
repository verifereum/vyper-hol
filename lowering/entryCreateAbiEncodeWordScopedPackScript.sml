(* Confine the actual word-packing execution without changing its witness. *)
Theory entryCreateAbiEncodeWordScopedPack
Ancestors
  bodyFullAbiEncodeWordPackRun bodyFullAbiEncodeWordPackData
  entryCreateAbiWordInventory entryCreateAdminSequence entryCreateCompletedCut
  entryCreateFocusSpec
  gasSummary vyperStorageFootprint vyperState list

Theorem abi_encode_word_scoped_pack_suffix:
  abi_word_pack_inputs (meth,sm,out,sb) (ctx,func,ce,cx,lo)
    (es,sa,s0,G0,tn0) (ee,t,G1,tn1) (at,av) (H0,Hentry,op,word) /\
  storage_trace_domain cx st0 ee.storage_trace /\
  (!tail. source (ee with gas_obs := tail) = (res,ee with gas_obs := tail)) /\
  (!p q packed Gp tnp H.
     abi_word_pack_witness (meth,sm,out,sb) (ctx,func,ce,cx,lo)
       (es,sa,s0,G0,tn0) (ee,t,G1,tn1) (at,av)
       (d,gas_explicit_sites ctx shadow_ctx,PG) p q packed Gp tnp /\
     valid_horizon cx st0 H ee.storage_trace ==>
     Q H res (ee with gas_obs := []) Gp tnp packed) ==>
  ?p q packed Gp tnp.
    abi_word_pack_witness (meth,sm,out,sb) (ctx,func,ce,cx,lo)
      (es,sa,s0,G0,tn0) (ee,t,G1,tn1) (at,av)
      (d,gas_explicit_sites ctx shadow_ctx,PG) p q packed Gp tnp /\
    create_operand_full_scope sm sb (gas_explicit_sites ctx shadow_ctx)
      ctx func t [] (OK packed) /\
    (!H. valid_horizon cx st0 H ee.storage_trace ==>
       Q H res (ee with gas_obs := []) Gp tnp packed) /\
    scoped_operand_outcome (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
      (cx_tops cx) cx st0 sm sb source (ee with gas_obs := [],t,G1,tn1) Q R
Proof
  strip_tac >>
  drule abi_encode_word_pack_run >>
  disch_then (qspecl_then [`d`,`gas_explicit_sites ctx shadow_ctx`,`PG`]
    (qx_choosel_then [`p`,`q`,`packed`,`Gp`,`tnp`] strip_assume_tac)) >>
  qpat_assum `abi_word_pack_inputs _ _ _ _ _ _`
    (strip_assume_tac o REWRITE_RULE [abi_word_pack_inputs_def]) >>
  drule abi_encode_word_pack_inventory >> strip_tac >>
  `create_operand_full_scope sm sb (gas_explicit_sites ctx shadow_ctx)
     ctx func t [] (OK packed)` by
    (qpat_assum `packed = _` SUBST1_TAC >>
     irule create_admin_sequence_scope >>
     fs[create_operand_at_def,EVERY_MEM]) >>
  `!H. valid_horizon cx st0 H ee.storage_trace ==>
       Q H res (ee with gas_obs := []) Gp tnp packed` by metis_tac[] >>
  qexistsl_tac [`p`,`q`,`packed`,`Gp`,`tnp`] >> asm_rewrite_tac[] >>
  qpat_assum `abi_word_pack_witness _ _ _ _ _ _ _ _ _ _ _`
    (strip_assume_tac o REWRITE_RULE [abi_word_pack_witness_def]) >>
  rewrite_tac[scoped_operand_outcome_def] >> qexists_tac `[]` >>
  disj2_tac >> disj1_tac >> qexistsl_tac [`res`,`ee`,`OK packed`,`Gp`,`tnp`] >>
  qpat_x_assum `packed = _` kall_tac >>
  qpat_x_assum `sb.cs_current_insts = _` kall_tac >>
  simp[]
QED
