(* Code and control boundary for the encoder's allocation prefix. *)
Theory revertReasonPrefixCodePtr
Ancestors
  revertReasonPrefixBoundaryPtr revertReasonPrefixPtr revertReasonPrefixFramePtr
  revertReasonRuns revertReasonLayout fragExec context compileEnv
  bodyPtrDefs ghostPcTransportPtr entrySinkExtraction exprLoweringProps allocationPtr
  venomInst venomState words arithmetic list rich_list finite_map

Theorem revert_reason_prefix_code:
  fn_has_code sa sm fn /\ sm.cs_current_bb = sa.cs_current_bb /\
  sm.cs_current_insts = sa.cs_current_insts ++
    revert_reason_prefix sa.cs_next_id sa.cs_next_var ms ==>
  ?bb. lookup_block sa.cs_current_bb fn.fn_blocks = SOME bb /\
    isPREFIX (revert_reason_prefix sa.cs_next_id sa.cs_next_var ms)
      (DROP (LENGTH sa.cs_current_insts) bb.bb_instructions) /\
    MEM (mk_inst sa.cs_next_id ALLOCA [Lit (n2w (64+ms))]
      [STRING #"%" (toString sa.cs_next_var)]) (fn_insts fn) /\
    MEM (mk_inst (sa.cs_next_id+3) ALLOCA [Lit (n2w ms)]
      [STRING #"%" (toString (sa.cs_next_var+2))]) (fn_insts fn)
Proof
  simp[fn_has_code_def] >> strip_tac >> gvs[IS_PREFIX_APPEND] >>
  simp[NoAsms, DROP_APPEND1] >> conj_tac >>
  irule lookup_block_fn_insts >> goal_assum (drule_at Any) >>
  simp[revert_reason_prefix_def]
QED

Theorem compile_revert_reason_prefix_code:
  compile_revert_with_reason cenv vv mt ms sa = ((),sb) /\ fn_has_code sa sb fn ==>
  ?sm sn op.
    unwrap_value cenv vv sm = (op,sn) /\
    fn_has_code sa sm fn /\ fn_has_code sm sn fn /\ fn_has_code sn sb fn /\
    same_blocks sa sm /\ same_blocks sn sb /\
    cs_extends sa sm /\ cs_extends sm sn /\ cs_extends sn sb /\
    sm.cs_next_var = sa.cs_next_var+3 /\ sm.cs_next_id = sa.cs_next_id+4 /\
    sm.cs_current_insts = sa.cs_current_insts ++
      revert_reason_prefix sa.cs_next_id sa.cs_next_var ms /\
    sm.cs_next_var <= sn.cs_next_var /\ sm.cs_next_id <= sn.cs_next_id /\
    sb.cs_current_insts = sn.cs_current_insts ++
      (revert_reason_copy sn.cs_next_id sn.cs_next_var
        (Var (STRING #"%" (toString (sa.cs_next_var+2)))) op ++
       revert_reason_suffix sn.cs_next_id sn.cs_next_var
        (Var (STRING #"%" (toString sa.cs_next_var)))
        (Var (STRING #"%" (toString (sa.cs_next_var+1))))
        (Var (STRING #"%" (toString (sa.cs_next_var+2)))))
Proof
  strip_tac >> drule compile_revert_reason_chunks >> strip_tac >>
  `cs_extends sm sb` by metis_tac[cs_extends_trans] >>
  `fn_has_code sa sm fn /\ fn_has_code sm sb fn` by
    metis_tac[fn_has_code_split] >>
  `fn_has_code sm sn fn /\ fn_has_code sn sb fn` by
    metis_tac[fn_has_code_split] >>
  qexistsl_tac [`sm`,`sn`,`op`] >> asm_rewrite_tac[]
QED

Theorem revert_reason_prefix_at_compile_endpoint_core_ptr[local]:
  fn_has_code sa sm fn /\ sm.cs_current_bb = sa.cs_current_bb /\
  sm.cs_current_insts = sa.cs_current_insts ++
    revert_reason_prefix sa.cs_next_id sa.cs_next_var ms /\
  stmt_state_rel ctx fn cenv cx es s /\ fn_inst_ids_distinct fn /\
  (!k. k < 3 ==> not_local_ptr cenv es.scopes
    (STRING #"%" (toString (sa.cs_next_var+k)))) /\
  64+ms < dimword(:256) /\ ~ctx_has_dalloca ctx /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?t Gf tnf.
    run_inst_seq (revert_reason_prefix sa.cs_next_id sa.cs_next_var ms) s = OK t /\
    inst_seq_ptr D 0 ctx fn PG G tn
      (revert_reason_prefix sa.cs_next_id sa.cs_next_var ms) s Gf tnf /\
    gas_path_ptr D 0 ctx fn PG G tn s 0 Gf tnf
      (OK (t with vs_inst_idx := s.vs_inst_idx+4)) /\
    ~(t with vs_inst_idx := s.vs_inst_idx+4).vs_halted /\
    (t with vs_inst_idx := s.vs_inst_idx+4).vs_current_bb = sm.cs_current_bb /\
    (t with vs_inst_idx := s.vs_inst_idx+4).vs_inst_idx = LENGTH sm.cs_current_insts /\
    stmt_state_rel ctx fn cenv cx es (t with vs_inst_idx := s.vs_inst_idx+4) /\
    ptr_covers Gf tnf (STRING #"%" (toString sa.cs_next_var))
      (t with vs_inst_idx := s.vs_inst_idx+4) (64+ms) /\
    ptr_covers Gf tnf (STRING #"%" (toString (sa.cs_next_var+1)))
      (t with vs_inst_idx := s.vs_inst_idx+4) (32+ms) /\
    ptr_covers Gf tnf (STRING #"%" (toString (sa.cs_next_var+2)))
      (t with vs_inst_idx := s.vs_inst_idx+4) ms
Proof
  strip_tac >> drule_all revert_reason_prefix_code >> strip_tac >>
  `?t. run_inst_seq (revert_reason_prefix sa.cs_next_id sa.cs_next_var ms) s = OK t`
    by metis_tac[revert_reason_prefix_run] >>
  `lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
   isPREFIX (revert_reason_prefix sa.cs_next_id sa.cs_next_var ms)
     (DROP s.vs_inst_idx bb.bb_instructions)` by asm_rewrite_tac[] >>
  drule_all revert_reason_prefix_checked_path >>
  disch_then (qspecl_then [`tn`,`PG`,`G`,`D`] strip_assume_tac) >>
  `!k. k < 2 ==> not_local_ptr cenv es.scopes
    (STRING #"%" (toString (sa.cs_next_var+k)))` by simp[] >>
  drule_all revert_reason_prefix_covers >> strip_tac >>
  drule_all revert_reason_prefix_state_rel >> strip_tac >>
  `EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
    (revert_reason_prefix sa.cs_next_id sa.cs_next_var ms)` by
    simp[NoAsms, revert_reason_prefix_def, mk_inst_def, is_terminator_def] >>
  drule_all run_inst_seq_preserves_entry_control >> strip_tac >>
  qexistsl_tac [`t`,`Gf`,`tnf`] >>
  simp[stmt_state_rel_inst_idx]
QED

Theorem revert_reason_prefix_pointer_values[local]:
  stmt_state_rel ctx fn cenv cx es s /\ fn_inst_ids_distinct fn /\
  MEM (mk_inst id ALLOCA [Lit (n2w (64+ms))]
    [STRING #"%" (toString v)]) (fn_insts fn) /\
  MEM (mk_inst (id+3) ALLOCA [Lit (n2w ms)]
    [STRING #"%" (toString (v+2))]) (fn_insts fn) /\
  (!k. k < 2 ==> not_local_ptr cenv es.scopes (STRING #"%" (toString (v+k)))) /\
  64+ms < dimword(:256) /\
  run_inst_seq (revert_reason_prefix id v ms) s = OK t ==>
  ?b c. b+(64+ms) < dimword(:256) /\ c+ms < dimword(:256) /\
    lookup_var (STRING #"%" (toString v)) t = SOME (n2w b) /\
    lookup_var (STRING #"%" (toString (v+1))) t = SOME (n2w b + 32w) /\
    lookup_var (STRING #"%" (toString (v+2))) t = SOME (n2w c) /\
    FLOOKUP t.vs_allocas (id+3) = SOME (c,ms)
Proof
  strip_tac >>
  `not_local_ptr cenv es.scopes (STRING #"%" (toString v)) /\
   not_local_ptr cenv es.scopes (STRING #"%" (toString (v+1)))` by
    (qpat_x_assum `!k. _` mp_tac >>
     disch_then (fn th => map_every (fn k => qspec_then k assume_tac th) [`0`,`1`]) >>
     gvs[arithmeticTheory.ADD_COMM]) >>
  `ms < dimword(:256) /\ 32 <= 64+ms` by decide_tac >>
  fs[revert_reason_prefix_def] >>
  drule run_inst_seq_four_endpoint >> strip_tac >>
  drule_all alloca_step_site >> strip_tac >>
  `lookup_var (STRING #"%" (toString v)) s1 = SOME (n2w b)` by
    gvs[eval_operand_def] >>
  `stmt_state_rel ctx fn cenv cx es s3` by
    (irule alloca_store_offset_state_rel >>
     simp[] >> qexistsl_tac [`id`,`ms+64`] >> simp[] >> metis_tac[]) >>
  `?c. FLOOKUP t.vs_allocas (id+3) = SOME (c,ms) /\
    c+ms < dimword(:256) /\
    eval_operand (Var (STRING #"%" (toString (v+2)))) t = SOME (n2w c)` by
    (irule alloca_step_site >> metis_tac[]) >>
  drule_all store_offset_endpoint >> strip_tac >>
  `STRING #"%" (toString v) <> STRING #"%" (toString (v+2)) /\
   STRING #"%" (toString (v+1)) <> STRING #"%" (toString (v+2))` by simp[] >>
  `lookup_var (STRING #"%" (toString v)) t =
   lookup_var (STRING #"%" (toString v)) s3 /\
   lookup_var (STRING #"%" (toString (v+1))) t =
   lookup_var (STRING #"%" (toString (v+1))) s3` by
    (conj_tac >> irule alloca_store_add_lookup_frame >> metis_tac[]) >>
  qexistsl_tac [`b`,`c`] >>
  gvs[eval_operand_def, lookup_var_def, update_var_def, mstore_def, FLOOKUP_UPDATE]
QED

Theorem revert_reason_prefix_pointer_resources:
  stmt_state_rel ctx fn cenv cx es s /\ fn_inst_ids_distinct fn /\
  MEM (mk_inst id ALLOCA [Lit (n2w (64+ms))]
    [STRING #"%" (toString v)]) (fn_insts fn) /\
  MEM (mk_inst (id+3) ALLOCA [Lit (n2w ms)]
    [STRING #"%" (toString (v+2))]) (fn_insts fn) /\
  (!k. k < 2 ==> not_local_ptr cenv es.scopes (STRING #"%" (toString (v+k)))) /\
  64+ms < dimword(:256) /\
  run_inst_seq (revert_reason_prefix id v ms) s = OK t ==>
  ?B P Q.
    lookup_var (STRING #"%" (toString v)) t = SOME B /\
    lookup_var (STRING #"%" (toString (v+1))) t = SOME P /\
    lookup_var (STRING #"%" (toString (v+2))) t = SOME Q /\
    w2n B+(64+ms) < dimword(:256) /\
    w2n P+(32+ms) < dimword(:256) /\
    w2n Q+ms < dimword(:256) /\
    FLOOKUP t.vs_allocas (id+3) = SOME (w2n Q,ms)
Proof
  strip_tac >> drule_all revert_reason_prefix_pointer_values >> strip_tac >>
  qexistsl_tac [`n2w b`,`n2w b+32w`,`n2w c`] >>
  `b < dimword(:256) /\ c < dimword(:256) /\ b+32 < dimword(:256)` by decide_tac >>
  asm_rewrite_tac[] >> simp[word_add_n2w, w2n_n2w, LESS_MOD] >> decide_tac
QED

Theorem revert_reason_prefix_old_observations:
  run_inst_seq (revert_reason_prefix id v ms) s = OK t /\
  inst_seq_ptr D lo ctx fn PG G tn (revert_reason_prefix id v ms) s Gf tnf ==>
  (!x. (!k. k < 3 ==> x <> STRING #"%" (toString (v+k))) ==>
    lookup_var x t = lookup_var x s /\
    FLOOKUP Gf x = FLOOKUP G x /\ op_taint tnf (Var x) = op_taint tn (Var x) /\
    (!n. ptr_covers G tn x s n ==> ptr_covers Gf tnf x t n)) /\
  tnf.t_stor = tn.t_stor /\ tnf.t_trans = tn.t_trans /\ tnf.t_imm = tn.t_imm
Proof
  strip_tac >> drule revert_reason_prefix_ghost_observations >> strip_tac >>
  asm_rewrite_tac[] >> gen_tac >> disch_tac >>
  `lookup_var x t = lookup_var x s` by
    metis_tac[revert_reason_prefix_lookup_frame] >>
  `FLOOKUP Gf x = FLOOKUP G x /\ op_taint tnf (Var x) = op_taint tn (Var x)` by
    metis_tac[] >>
  asm_rewrite_tac[] >> metis_tac[revert_reason_prefix_old_ptr_covers]
QED

Theorem revert_reason_prefix_at_compile_endpoint_ptr:
  fn_has_code sa sm fn /\ sm.cs_current_bb = sa.cs_current_bb /\
  sm.cs_current_insts = sa.cs_current_insts ++
    revert_reason_prefix sa.cs_next_id sa.cs_next_var ms /\
  stmt_state_rel ctx fn cenv cx es s /\ fn_inst_ids_distinct fn /\
  (!k. k < 3 ==> not_local_ptr cenv es.scopes
    (STRING #"%" (toString (sa.cs_next_var+k)))) /\
  64+ms < dimword(:256) /\ ~ctx_has_dalloca ctx /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?t Gf tnf B P Q.
    run_inst_seq (revert_reason_prefix sa.cs_next_id sa.cs_next_var ms) s = OK t /\
    inst_seq_ptr D 0 ctx fn PG G tn
      (revert_reason_prefix sa.cs_next_id sa.cs_next_var ms) s Gf tnf /\
    gas_path_ptr D 0 ctx fn PG G tn s 0 Gf tnf
      (OK (t with vs_inst_idx := s.vs_inst_idx+4)) /\
    ~(t with vs_inst_idx := s.vs_inst_idx+4).vs_halted /\
    (t with vs_inst_idx := s.vs_inst_idx+4).vs_current_bb = sm.cs_current_bb /\
    (t with vs_inst_idx := s.vs_inst_idx+4).vs_inst_idx = LENGTH sm.cs_current_insts /\
    stmt_state_rel ctx fn cenv cx es (t with vs_inst_idx := s.vs_inst_idx+4) /\
    ptr_covers Gf tnf (STRING #"%" (toString sa.cs_next_var))
      (t with vs_inst_idx := s.vs_inst_idx+4) (64+ms) /\
    ptr_covers Gf tnf (STRING #"%" (toString (sa.cs_next_var+1)))
      (t with vs_inst_idx := s.vs_inst_idx+4) (32+ms) /\
    ptr_covers Gf tnf (STRING #"%" (toString (sa.cs_next_var+2)))
      (t with vs_inst_idx := s.vs_inst_idx+4) ms /\
    lookup_var (STRING #"%" (toString sa.cs_next_var))
      (t with vs_inst_idx := s.vs_inst_idx+4) = SOME B /\
    lookup_var (STRING #"%" (toString (sa.cs_next_var+1)))
      (t with vs_inst_idx := s.vs_inst_idx+4) = SOME P /\
    lookup_var (STRING #"%" (toString (sa.cs_next_var+2)))
      (t with vs_inst_idx := s.vs_inst_idx+4) = SOME Q /\
    w2n B+(64+ms) < dimword(:256) /\ w2n P+(32+ms) < dimword(:256) /\
    w2n Q+ms < dimword(:256) /\
    FLOOKUP (t with vs_inst_idx := s.vs_inst_idx+4).vs_allocas
      (sa.cs_next_id+3) = SOME (w2n Q,ms) /\
    alloca_inv (t with vs_inst_idx := s.vs_inst_idx+4) /\
    alloca_room ctx fn (t with vs_inst_idx := s.vs_inst_idx+4) /\
    (!i n a sz. MEM i (fn_insts fn) /\ i.inst_opcode = ALLOCA /\
      i.inst_operands = [Lit n] /\
      FLOOKUP (t with vs_inst_idx := s.vs_inst_idx+4).vs_allocas i.inst_id = SOME (a,sz)
      ==> sz = w2n n)
Proof
  strip_tac >> drule_all revert_reason_prefix_at_compile_endpoint_core_ptr >>
  disch_then (qspecl_then [`tn`,`PG`,`G`,`D`] strip_assume_tac) >>
  drule_all revert_reason_prefix_code >> strip_tac >>
  `!k. k < 2 ==> not_local_ptr cenv es.scopes
    (STRING #"%" (toString (sa.cs_next_var+k)))` by simp[] >>
  drule_all revert_reason_prefix_pointer_resources >> strip_tac >>
  qexistsl_tac [`t`,`Gf`,`tnf`,`B`,`P`,`Q`] >>
  asm_rewrite_tac[] >>
  fs[lookup_var_def, stmt_state_rel_def] >> metis_tac[]
QED

(* This corollary intentionally retains the return-register freshness premise
   of the source ghost frame; the prefix resource boundary does not imply it. *)
Theorem revert_reason_prefix_ghost_inv_at_index:
  stmt_state_rel ctx fn cenv cx es s /\ fn_inst_ids_distinct fn /\
  MEM (mk_inst id ALLOCA [Lit (n2w (64+ms))]
    [STRING #"%" (toString v)]) (fn_insts fn) /\
  MEM (mk_inst (id+3) ALLOCA [Lit (n2w ms)]
    [STRING #"%" (toString (v+2))]) (fn_insts fn) /\
  (!k. k < 3 ==> not_local_ptr cenv es.scopes (STRING #"%" (toString (v+k)))) /\
  (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) \/
     cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==>
     !k. k < 3 ==> x <> STRING #"%" (toString (v+k))) /\
  64+ms < dimword(:256) /\ ghost_inv d cenv cx es G tn s /\
  run_inst_seq (revert_reason_prefix id v ms) s = OK t /\
  inst_seq_ptr D lo ctx fn PG G tn (revert_reason_prefix id v ms) s Gf tnf ==>
  ghost_inv d cenv cx es Gf tnf (t with vs_inst_idx := ix)
Proof
  strip_tac >> drule_all revert_reason_prefix_ghost_inv >> strip_tac >>
  Cases_on `d` >-
    (fs[ghost_inv_def, ptr_covers_def, return_buf_ptr_def, stor_taint_ok_def,
        lookup_var_def] >> metis_tac[]) >>
  rename1 `ghost_inv (SOME bc)` >> PairCases_on `bc` >>
  gvs[ghost_inv_def, return_buf_ptr_def, ptr_covers_def, stor_taint_ok_def,
      lookup_var_def] >> first_assum MATCH_ACCEPT_TAC
QED

Theorem revert_reason_prefix_memory_effects_at_index:
  stmt_state_rel ctx fn cenv cx es s /\ fn_inst_ids_distinct fn /\
  MEM (mk_inst id ALLOCA [Lit (n2w (64+ms))]
    [STRING #"%" (toString v)]) (fn_insts fn) /\
  MEM (mk_inst (id+3) ALLOCA [Lit (n2w ms)]
    [STRING #"%" (toString (v+2))]) (fn_insts fn) /\
  (!k. k < 2 ==> not_local_ptr cenv es.scopes (STRING #"%" (toString (v+k)))) /\
  64+ms < dimword(:256) /\
  run_inst_seq (revert_reason_prefix id v ms) s = OK t /\
  inst_seq_ptr D lo ctx fn PG G tn (revert_reason_prefix id v ms) s Gf tnf ==>
  ?b c. b+(64+ms) < dimword(:256) /\ c+ms < dimword(:256) /\
    FLOOKUP (t with vs_inst_idx := ix).vs_allocas id = SOME (b,64+ms) /\
    FLOOKUP (t with vs_inst_idx := ix).vs_allocas (id+3) = SOME (c,ms) /\
    (!i. i NOTIN ({i | b <= i /\ i < b+(64+ms)} UNION {i | c <= i /\ i < c+ms}) ==>
      mem_bytes_at i 1 (t with vs_inst_idx := ix).vs_memory = mem_bytes_at i 1 s.vs_memory) /\
    (!i. i NOTIN ({i | b <= i /\ i < b+(64+ms)} UNION {i | c <= i /\ i < c+ms}) /\
      i IN tnf.t_mem ==> i IN tn.t_mem)
Proof
  strip_tac >> drule_all revert_reason_prefix_memory_effects >> strip_tac >>
  qexistsl_tac [`b`,`c`] >>
  fs[venom_state_accfupds, combinTheory.K_THM] >>
  conj_tac >> first_assum MATCH_ACCEPT_TAC
QED
