Theory bodyFullAbiDecodeRuntimeLoopBoundary
Ancestors
  bodyFullAbiDecodeRuntimeLoopSyntax bodyFullAbiDecodeLoopHeaderExact
  decoderNavigationPtr abiDecoderComposition loweringStateRelDefs
  typedMemoryCopy bodyPtrDefs ptrDiscipline venomInst venomState
  freshWrites list pair arithmetic rich_list
Libs
  bodyFullAbiDecodeRuntimeLoopSyntaxLib

Theorem abi_decode_loop_resource_jump[local]:
  (^loop_resource) start j s G tn ==>
  (^loop_resource) start j (jump_to hdr s) G tn
Proof
  CONV_TAC (REDEPTH_CONV BETA_CONV) >>
  disch_then (fn th => assume_tac (CONJUNCT1 th) >>
                       map_every assume_tac (CONJUNCTS (CONJUNCT2 th))) >>
  conj_tac
  >- (MATCH_MP_TAC (BETA_RULE abi_decode_loop_owned_jump_exact) >> first_assum ACCEPT_TAC) >>
  `!name b k. local_region ce es.scopes (jump_to hdr s) name b k <=>
              local_region ce es.scopes s name b k` by
    (rpt gen_tac >> irule local_region_lookup_cong >> simp[typed_copy_lookup_var_jump]) >>
  `!p k. ptr_covers G tn p (jump_to hdr s) k <=> ptr_covers G tn p s k` by
    simp[NoAsms,ptr_covers_def,typed_copy_lookup_var_jump] >>
  `allocas_from lo (jump_to hdr s)` by
    (qpat_assum `allocas_from lo s` mp_tac >> simp[NoAsms,allocas_from_def,jump_to_def]) >>
  asm_rewrite_tac[CONJUNCT1 abi_decode_jump_observations,typed_copy_lookup_var_jump] >>
  simp_tac (srw_ss()) [jump_to_def] >>
  asm_rewrite_tac[]
QED

Theorem abi_decode_loop_entry_jump_joint:
  (^repaired_loop_entry) (Var dst) src opc base_op hi ei asz msz ip cnt
    env sf ty tv live protected start final_st sin Gin tnin d aid counter cell n j srcbase srcoff h /\
  lookup_block start.cs_current_bb fn.fn_blocks = SOME
    <|bb_label := start.cs_current_bb; bb_instructions := start.cs_current_insts ++
      [mk_inst start.cs_next_id JMP [Label hdr] []]|> ==>
  (!H. V H ==> gas_origin_ptr_path (DF H,lo,explicit,ctx,fn,PG)
    (sin,Gin,tnin) [] (OK (jump_to hdr sin),Gin,tnin)) /\
  (^loop_inv) start hdr sin Gin tnin j (jump_to hdr sin) Gin tnin
Proof
  CONV_TAC (REDEPTH_CONV BETA_CONV) >>
  rewrite_tac[arithmeticTheory.SUB_EQUAL_0,arithmeticTheory.ADD_CLAUSES,
    arithmeticTheory.ADD_ASSOC] >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  qpat_x_assum `srcbase = w2n input_word` SUBST_ALL_TAC >>
  qpat_x_assum `ip = Var counter` SUBST_ALL_TAC >>
  `allocas_from lo sin` by
    (qpat_assum `?H. V H` (qx_choose_then `hh` assume_tac) >>
     qpat_assum `!H. V H ==> stmt_state_rel _ _ _ _ _ _ _ /\ _`
       (qspec_then `hh` (drule_then strip_assume_tac)) >>
     qpat_assum `ghost_inv_at _ lo _ _ _ _ _ _ sin`
       (map_every assume_tac o CONJUNCTS o REWRITE_RULE [ghost_inv_at_def]) >>
     first_assum ACCEPT_TAC) >>
  conj_tac
  >- (rpt strip_tac >> irule decoderNavigationPtrTheory.jump_origin_ptr_path >>
      asm_rewrite_tac[] >>
      qexistsl_tac [`<|bb_label := start.cs_current_bb;
        bb_instructions := start.cs_current_insts ++ [mk_inst start.cs_next_id JMP [Label hdr] []]|>`,
        `start.cs_next_id`] >>
      simp[get_instruction_def,EL_LENGTH_APPEND_0]) >>
  conj_tac
  >- (irule (BETA_RULE abi_decode_loop_resource_jump) >>
      qpat_x_assum `?p. Var dst = Var p /\ _` (strip_assume_tac o SRULE []) >>
      asm_rewrite_tac[]) >>
  simp[jump_to_def,typed_copy_lookup_var_jump]
QED

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
    (irule freshWritesTheory.not_fresh_at_mono >> qexists_tac `start` >> asm_rewrite_tac[]) >>
  asm_rewrite_tac[] >>
  qpat_assum `EVERY (\(aid,p,b,k,bytes). not_fresh_at start p) live`
    (mp_tac o REWRITE_RULE [listTheory.EVERY_MEM,pairTheory.FORALL_PROD]) >>
  simp[listTheory.EVERY_MEM,pairTheory.FORALL_PROD] >>
  disch_then (fn th => rpt gen_tac >> disch_then (assume_tac o MATCH_MP (SPEC_ALL th))) >>
  irule freshWritesTheory.not_fresh_at_mono >> qexists_tac `start` >> asm_rewrite_tac[]
QED
