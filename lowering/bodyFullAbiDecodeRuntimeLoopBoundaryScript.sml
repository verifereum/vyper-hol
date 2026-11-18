Theory bodyFullAbiDecodeRuntimeLoopBoundary
Ancestors
  bodyFullAbiDecodeRuntimeLoopSyntax freshWrites list pair arithmetic
Libs
  bodyFullAbiDecodeRuntimeLoopSyntaxLib

Theorem abi_decode_loop_exit_post:
  (!H. V H ==> gas_origin_ptr_path
    (DF H,lo,explicit,ctx,fn,PG) (sin,Gin,tnin) [] (OK t,Gf,tnf)) /\
  (^loop_resource) start n t Gf tnf /\
  (^frame) start sin Gin tnin t Gf tnf /\
  ~t.vs_halted /\ t.vs_current_bb = final_st.cs_current_bb /\
  t.vs_inst_idx = 0 /\ final_st.cs_current_insts = [] /\
  start.cs_next_var <= final_st.cs_next_var /\
  start.cs_next_id <= final_st.cs_next_id ==>
  (^owned_decoder_post) live protected start final_st sin Gin tnin
Proof
  CONV_TAC (REDEPTH_CONV BETA_CONV) >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  qexistsl_tac [`OK t`,`Gf`,`tnf`] >>
  conj_tac >- first_assum ACCEPT_TAC >>
  disj1_tac >> qexists_tac `t` >>
  asm_rewrite_tac[listTheory.LENGTH] >>
  conj_tac
  >- (qpat_assum `EVERY (\(aid,p,b,k,bytes). aid < start.cs_next_id /\ FLOOKUP t.vs_allocas aid = SOME (b,k) /\ _) live`
        (mp_tac o REWRITE_RULE [listTheory.EVERY_MEM,pairTheory.FORALL_PROD]) >>
      simp[listTheory.EVERY_MEM,pairTheory.FORALL_PROD] >>
      disch_then (fn th => rpt gen_tac >> disch_then (mp_tac o MATCH_MP (SPEC_ALL th))) >>
      simp[] >> decide_tac) >>
  `output_id < final_st.cs_next_id /\ origin.cs_next_var <= final_st.cs_next_var` by decide_tac >>
  `not_fresh_at final_st output` by
    (irule freshWritesTheory.not_fresh_at_mono >> goal_assum drule >> simp[]) >>
  asm_rewrite_tac[] >>
  qpat_assum `EVERY (\(aid,p,b,k,bytes). not_fresh_at start p) live`
    (mp_tac o REWRITE_RULE [listTheory.EVERY_MEM,pairTheory.FORALL_PROD]) >>
  simp[listTheory.EVERY_MEM,pairTheory.FORALL_PROD] >>
  disch_then (fn th => rpt gen_tac >> disch_then (assume_tac o MATCH_MP (SPEC_ALL th))) >>
  irule freshWritesTheory.not_fresh_at_mono >> goal_assum drule >> simp[]
QED
