(* Compiler-code adapter for the shared checked encoder tail. *)
Theory revertReasonTailCodePtr
Ancestors
  revertReasonTailPtr revertReasonLayout fragExec exprLoweringProps
  context compileEnv bodyPtrDefs reasonCopySourcePtr venomInst venomState
  words arithmetic list rich_list finite_map

Theorem revert_reason_tail_code:
  fn_has_code sn sb fn /\ sb.cs_current_bb = sn.cs_current_bb /\
  sb.cs_current_insts = sn.cs_current_insts ++
    (revert_reason_copy id v q op ++ revert_reason_suffix id v b p q) ==>
  ?bb.
    lookup_block sn.cs_current_bb fn.fn_blocks = SOME bb /\
    isPREFIX (revert_reason_copy id v q op)
      (DROP (LENGTH sn.cs_current_insts) bb.bb_instructions) /\
    isPREFIX (revert_reason_suffix id v b p q)
      (DROP (LENGTH sn.cs_current_insts+5) bb.bb_instructions) /\
    MEM (mk_inst (id+5) ALLOCA [Lit 32w]
      [STRING #"%" (toString (v+4))]) (fn_insts fn)
Proof
  simp[fn_has_code_def] >> strip_tac >>
  gvs[IS_PREFIX_APPEND] >>
  pure_rewrite_tac[GSYM APPEND_ASSOC] >>
  simp[NoAsms, DROP_APPEND1] >>
  conj_tac >- (qexists_tac `l` >> simp[NoAsms, DROP_APPEND2]) >>
  irule lookup_block_fn_insts >> goal_assum (drule_at Any) >>
  simp[revert_reason_suffix_def]
QED

Theorem revert_reason_tail_at_compile_endpoint_ptr:
  fn_has_code sn sb fn /\ sb.cs_current_bb = sn.cs_current_bb /\
  sb.cs_current_insts = sn.cs_current_insts ++
    (revert_reason_copy sn.cs_next_id sn.cs_next_var (Var q) (Var src) ++
     revert_reason_suffix sn.cs_next_id sn.cs_next_var (Var b) (Var p) (Var q)) /\
  s.vs_current_bb = sn.cs_current_bb /\
  s.vs_inst_idx = LENGTH sn.cs_current_insts /\ ~s.vs_halted /\
  not_fresh_at sn b /\ not_fresh_at sn p /\
  not_fresh_at sn q /\ not_fresh_at sn src /\
  lookup_var b s = SOME B /\ lookup_var p s = SOME P /\
  lookup_var q s = SOME Q /\ lookup_var src s = SOME A /\
  ptr_covers G tn b s (64+ms) /\ ptr_covers G tn p s (32+ms) /\
  ptr_covers G tn q s ms /\
  ptr_covers G tn src s (32+contractABI$ceil32 L) /\
  mload (w2n A) s = n2w L /\
  (!j. w2n A <= j /\ j < w2n A+32 ==> j NOTIN tn.t_mem) /\
  32+contractABI$ceil32 L <= ms /\ L+63 < dimword(:256) /\
  64+ms < dimword(:256) /\ w2n B+64+ms < dimword(:256) /\
  w2n P+32+ms < dimword(:256) /\
  ~ctx_has_dalloca ctx /\ alloca_inv s /\ alloca_room ctx fn s /\
  (!a sz. FLOOKUP s.vs_allocas (sn.cs_next_id+5) = SOME (a,sz) ==> sz = 32) /\
  FLOOKUP s.vs_allocas parent = SOME (w2n Q,ms) /\ parent <> sn.cs_next_id+5 ==>
  ?z Gf tnf. gas_path_ptr D 0 ctx fn PG G tn s 0 Gf tnf (Abort Revert_abort z)
Proof
  strip_tac >> drule_all revert_reason_tail_code >> strip_tac >>
  `!k. k <= 20 ==>
    b <> STRING #"%" (toString (sn.cs_next_var+k)) /\
    p <> STRING #"%" (toString (sn.cs_next_var+k)) /\
    q <> STRING #"%" (toString (sn.cs_next_var+k)) /\
    src <> STRING #"%" (toString (sn.cs_next_var+k))` by
    (rpt strip_tac >> rename1 `x = STRING #"%" (toString (sn.cs_next_var+k))` >>
     qpat_x_assum `not_fresh_at sn x`
       (qspec_then `sn.cs_next_var+k` mp_tac o REWRITE_RULE [not_fresh_at_def]) >>
     asm_rewrite_tac[] >> decide_tac) >>
  `?t z Gf tnf j.
    run_inst_seq (revert_reason_copy sn.cs_next_id sn.cs_next_var (Var q) (Var src)) s = OK t /\
    run_inst_seq (revert_reason_suffix sn.cs_next_id sn.cs_next_var (Var b) (Var p) (Var q))
      (t with vs_inst_idx := s.vs_inst_idx+5) = Abort Revert_abort z /\
    gas_path_ptr D 0 ctx fn PG G tn s 0 Gf tnf
      (Abort Revert_abort (z with vs_inst_idx := j))` by
    (irule revert_reason_tail_resources_path_ptr >>
     asm_rewrite_tac[] >>
     conj_tac >- (qexists_tac `bb` >> asm_rewrite_tac[]) >>
     qexistsl_tac [`A`,`B`,`L`,`P`,`Q`,`ms`,`parent`] >> asm_rewrite_tac[]) >>
  metis_tac[]
QED
