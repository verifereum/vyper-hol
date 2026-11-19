Theory bodyFullAbiDecodeRuntimeLoopHeaderFrame
Ancestors
  abiDecoderReentry compileEnv decoderGhostFramePtr list
  loweringStateRelDefs pred_set ptrDiscipline venomState
Libs
  bodyFullAbiDecodeRuntimeLoopSyntaxLib

Theorem abi_decode_loop_header_anchor_owned_lift:
  anchor.cs_next_var = sa.cs_next_var /\ anchor.cs_next_id <= sa.cs_next_id /\
  (^owned_decoder_state) live protected anchor s G tn ==>
  (^owned_decoder_state) live protected sa s G tn
Proof
  BETA_TAC >> disch_then (map_every assume_tac o CONJUNCTS) >>
  `!p. not_fresh_at sa p = not_fresh_at anchor p` by simp[not_fresh_at_def] >>
  `output_id < sa.cs_next_id /\ origin.cs_next_var <= sa.cs_next_var` by decide_tac >>
  asm_rewrite_tac[] >> simp[EVERY_MEM, pairTheory.FORALL_PROD] >>
  rpt gen_tac >> strip_tac >>
  qpat_assum `EVERY (\(id,p,b,k,bytes). id < anchor.cs_next_id /\ _) live`
    (drule_then (strip_assume_tac o SRULE []) o REWRITE_RULE[EVERY_MEM, pairTheory.FORALL_PROD]) >>
  asm_rewrite_tac[] >> decide_tac
QED

Theorem abi_decode_loop_header_anchor_resource_frame:
  (^loop_resource) anchor k s G tn /\
  (^owned_decoder_state) live protected sg t Gf tnf /\
  (^frame) anchor s G tn t Gf tnf /\
  local_ptrs_reserved ce anchor /\ not_fresh_at anchor dst /\ not_fresh_at anchor counter /\
  abi_decoder_operand_live anchor.cs_next_var src /\
  abi_decoder_operand_live anchor.cs_next_var hi /\
  t.vs_memory = s.vs_memory /\ t.vs_allocas = s.vs_allocas /\
  t.vs_alloca_next = s.vs_alloca_next /\ t.vs_labels = s.vs_labels /\
  tnf.t_mem = tn.t_mem ==>
  (^loop_resource) anchor k t Gf tnf
Proof
  BETA_TAC >> disch_then (map_every assume_tac o CONJUNCTS) >>
  `!p sz. not_fresh_at anchor p /\ ptr_covers G tn p s sz ==>
     ptr_covers Gf tnf p t sz` by
    (rpt strip_tac >> irule ptr_covers_frame >>
     qexistsl_tac [`G`,`s`,`tn`] >> metis_tac[]) >>
  `!op. abi_decoder_operand_live anchor.cs_next_var op ==>
     eval_operand op t = eval_operand op s /\
     op_prov Gf op = op_prov G op /\ op_taint tnf op = op_taint tn op` by
    (Cases >> simp[abi_decoder_operand_live_def, abi_decoder_older_vars_def,
      GSYM not_fresh_at_def, eval_operand_def, op_prov_def, op_taint_def] >>
     metis_tac[op_taint_def]) >>
  `!name b sz. local_region ce es.scopes t name b sz <=>
                local_region ce es.scopes s name b sz` by
    (rpt gen_tac >> irule local_region_lookup_cong >>
     fs[local_ptrs_reserved_def] >> metis_tac[]) >>
  `allocas_from lo t` by
    (qpat_x_assum `allocas_from lo s` mp_tac >> asm_rewrite_tac[allocas_from_def]) >>
  `EVERY (\(id,p,b,sz,bytes). id < anchor.cs_next_id /\
      FLOOKUP t.vs_allocas id = SOME (b,sz) /\ lookup_var p t = SOME (n2w b) /\
      ptr_covers Gf tnf p t sz /\ op_taint tnf (Var p) = {} /\
      sz = LENGTH bytes /\ mem_bytes_at b sz t.vs_memory = bytes /\
      b+sz <= t.vs_alloca_next) live` by
    (simp[EVERY_MEM, pairTheory.FORALL_PROD] >> rpt gen_tac >> strip_tac >>
     qpat_assum `EVERY (\(id,p,b,k,bytes). id < anchor.cs_next_id /\
         FLOOKUP s.vs_allocas id = SOME (b,k) /\ _) live`
       (drule_then (strip_assume_tac o SRULE []) o
        REWRITE_RULE[EVERY_MEM, pairTheory.FORALL_PROD]) >>
     qpat_assum `EVERY (\(id,p,b,k,bytes). id < sg.cs_next_id /\ _) live`
       (drule_then (strip_assume_tac o SRULE []) o
        REWRITE_RULE[EVERY_MEM, pairTheory.FORALL_PROD]) >>
     asm_rewrite_tac[]) >>
  asm_rewrite_tac[] >> gns[eval_operand_def] >> rpt conj_tac >> metis_tac[]
QED
