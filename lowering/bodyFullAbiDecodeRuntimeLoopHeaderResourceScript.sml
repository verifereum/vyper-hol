Theory bodyFullAbiDecodeRuntimeLoopHeaderResource
Ancestors
  bodyFullAbiDecodeRuntimeLoopSyntax bodyFullAbiDecodeLoopHeader
  decoderGhostFramePtr stateRelProj exprLoweringProps loweringStateRelDefs
  compileEnv abiDecoderReentry venomState ptrDiscipline list pred_set
Libs
  bodyFullAbiDecodeRuntimeLoopSyntaxLib

Theorem header_owned_lift[local]:
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

Theorem header_resource_frame[local]:
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

(* The checked header supplies the endpoint once. Reattach the ages from
   the incoming resource, not the compiler indices after the branch. *)
Theorem abi_decode_loop_header_resource_joint:
  emit_op MLOAD [Var counter] sa = (Var idx,sb) /\
  compile_abi_dec_addr (Var input) src sb = (addr,sc) /\
  emit_op MLOAD [addr] sc = (count_op,sd) /\
  emit_op LT [Var idx;count_op] sd = (lt,se) /\
  emit_op ISZERO [lt] se = (done,sf) /\
  emit_inst JNZ [done;Label exit_lbl;Label body_lbl] [] sf = ((),sg) /\
  fn_has_code sa sb fn /\ fn_has_code sb sd fn /\ fn_has_code sd sg fn /\
  ~ctx_has_dalloca ctx /\ local_ptrs_reserved ce sa /\
  (!x sz. ce.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!x sz. ce.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  anchor.cs_next_var = sa.cs_next_var /\ anchor.cs_next_id <= sa.cs_next_id /\
  abi_decoder_operand_live anchor.cs_next_var (Var input) /\
  abi_decoder_operand_live anchor.cs_next_var (Var dst) /\
  abi_decoder_operand_live anchor.cs_next_var (Var counter) /\
  abi_decoder_operand_live anchor.cs_next_var src /\
  abi_decoder_operand_live anchor.cs_next_var hi /\
  n < dimword (:256) /\ hi <> Lit 0w /\ (?H. V H) /\
  w2n input_word + LENGTH input_bytes < dimword (:256) /\
  (^loop_resource) anchor k s G tn /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\ sa.cs_current_insts = [] /\
  s.vs_inst_idx = 0 ==>
  ?t Gf tnf.
    (!H. V H ==> gas_origin_ptr_path (DF H,lo,explicit,ctx,fn,PG)
       (s,G,tn) [] (OK t,Gf,tnf)) /\
    (^loop_resource) anchor k t Gf tnf /\ ~t.vs_halted /\ t.vs_inst_idx = 0 /\
    t.vs_current_bb = (if k = n then exit_lbl else body_lbl) /\
    (^frame) anchor s G tn t Gf tnf
Proof
  BETA_TAC >> disch_then (map_every assume_tac o CONJUNCTS) >>
  `!p. not_fresh_at sa p = not_fresh_at anchor p` by simp[not_fresh_at_def] >>
  `local_ptrs_reserved ce anchor` by
    (irule local_ptrs_reserved_next_var >> qexists_tac `sa` >> simp[]) >>
  `not_fresh_at sa input /\ not_fresh_at sa counter /\ not_fresh_at anchor dst /\
   (!x. src = Var x ==> not_fresh_at sa x) /\
   (!x. hi = Var x ==> not_fresh_at sa x)` by
    (asm_rewrite_tac[] >>
     conj_tac >- fs[abi_decoder_operand_live_def, abi_decoder_older_vars_def,
                   GSYM not_fresh_at_def] >>
     conj_tac >- fs[abi_decoder_operand_live_def, abi_decoder_older_vars_def,
                   GSYM not_fresh_at_def] >>
     conj_tac >- fs[abi_decoder_operand_live_def, abi_decoder_older_vars_def,
                   GSYM not_fresh_at_def] >>
     conj_tac >> rpt gen_tac >> disch_then SUBST_ALL_TAC >>
     fs[abi_decoder_operand_live_def, abi_decoder_older_vars_def,
        GSYM not_fresh_at_def]) >>
  `cell < dimword (:256)` by
    (qsuff_tac `s.vs_alloca_next < dimword (:256)` >- decide_tac >>
     qpat_x_assum `?H. V H` strip_assume_tac >>
     qpat_assum `!H. V H ==> stmt_state_rel H ctx fn ce cx es s /\ _`
       (drule_then (assume_tac o CONJUNCT1)) >>
     drule_then assume_tac stmt_state_rel_alloca_room >>
     drule_then ACCEPT_TAC alloca_room_next_lt) >>
  `(^owned_decoder_state) live protected sa s G tn` by
    (BETA_TAC >> MATCH_MP_TAC (BETA_RULE header_owned_lift) >> asm_rewrite_tac[]) >>
  pop_assum (map_every assume_tac o CONJUNCTS o BETA_RULE) >>
  mp_tac (abi_decode_loop_header_joint |> SPEC_ALL |>
          Q.INST [`j` |-> `k`] |> BETA_RULE) >>
  impl_tac >- asm_rewrite_tac[] >>
  disch_then (qx_choose_then `t` (qx_choose_then `Gf` (qx_choose_then `tnf`
    (map_every assume_tac o CONJUNCTS)))) >>
  `(^frame) anchor s G tn t Gf tnf` by
    (BETA_TAC >> gen_tac >> disch_tac >>
     qpat_assum `!p. not_fresh_at sa p ==> _` MATCH_MP_TAC >> asm_rewrite_tac[]) >>
  pop_assum (assume_tac o BETA_RULE) >>
  `not_fresh_at anchor counter` by
    (qpat_assum `abi_decoder_operand_live anchor.cs_next_var (Var counter)` mp_tac >>
     simp[NoAsms, abi_decoder_operand_live_def, abi_decoder_older_vars_def,
          GSYM not_fresh_at_def]) >>
  `(^loop_resource) anchor k t Gf tnf` by
    (BETA_TAC >> MATCH_MP_TAC (BETA_RULE header_resource_frame) >> asm_rewrite_tac[]) >>
  pop_assum (assume_tac o BETA_RULE) >>
  qexistsl_tac [`t`,`Gf`,`tnf`] >> asm_rewrite_tac[]
QED
