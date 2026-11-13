(* Static encoder execution indexed by the deterministic source conversion. *)
Theory extRetAbiSourceStaticCountedPtr
Ancestors
  extRetAbiStaticCountedPtr valueEncodingProps robustCopyTransportPtr
  valueTypingMemoryProps abiEncoderInput bodyPtrDefs loweringPosts
  words finite_map pred_set arithmetic

Theorem compile_abi_encode_source_static_counted_ptr:
  ((ei = AbiPrimWord /\ n = 32) \/ ei = AbiCopy n) /\
  compile_abi_encode_to_buf (Var dst) (Var src) ei sa = (out,sb) /\
  fn_has_code sa sb fn /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\ ~s.vs_halted /\
  ~ctx_has_dalloca ctx /\ not_fresh_at sa src /\ not_fresh_at sa dst /\
  lookup_var src s = SOME a /\ lookup_var dst s = SOME b /\
  ptr_covers G tn src s cap /\ ptr_covers G tn dst s n /\ n <= cap /\
  n < dimword(:256) /\ w2n a+cap < dimword(:256) /\
  w2n b+n < dimword(:256) /\
  (w2n a+cap <= w2n b \/ w2n b+n <= w2n a) /\
  evaluate_type env ty = SOME tv /\ value_has_type tv v /\
  vyper_to_abi env ty v = SOME av /\ at = vyper_to_abi_type env ty /\
  ~is_dynamic at /\ has_type at av /\ static_length at = n /\
  type_memory_size tv = n /\ val_footprint tv v <= cap /\
  (!mem'. mem_agree_outside tn.t_mem s.vs_memory mem' ==>
    val_in_memory tv v (w2n a) mem') ==>
  ?Gf tnf sf.
    gas_path_ptr D 0 ctx fn PG G tn s 0 Gf tnf (OK sf) /\
    sf.vs_current_bb = sb.cs_current_bb /\
    sf.vs_inst_idx = LENGTH sb.cs_current_insts /\ ~sf.vs_halted /\
    eval_operand out sf = SOME (n2w n) /\ op_taint tnf out = {} /\
    mem_bytes_at (w2n b) n sf.vs_memory = enc at av /\
    tnf.t_mem = tn.t_mem DIFF {i | w2n b <= i /\ i < w2n b+n} /\
    (!i. w2n b <= i /\ i < w2n b+n ==> i NOTIN tnf.t_mem) /\
    mem_agree_outside {i | w2n b <= i /\ i < w2n b+n} sf.vs_memory s.vs_memory /\
    tnf.t_stor = tn.t_stor /\ tnf.t_trans = tn.t_trans /\
    (!p. not_fresh_at sa p ==>
      lookup_var p sf = lookup_var p s /\ FLOOKUP Gf p = FLOOKUP G p /\
      op_taint tnf (Var p) = op_taint tn (Var p)) /\
    ptr_covers Gf tnf dst sf n /\
    (!mem'. mem_agree_outside tnf.t_mem sf.vs_memory mem' ==>
      abi_encoder_input ei at av (w2n a) cap mem') /\
    (!mem'. mem_agree_outside tnf.t_mem sf.vs_memory mem' ==>
      val_in_memory tv v (w2n a) mem')
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `!mem'. mem_agree_outside tn.t_mem s.vs_memory mem' ==>
    mem_bytes_at (w2n a) n mem' = enc at av` by
    (rpt strip_tac >> first_x_assum drule >> strip_tac >>
     `~is_dynamic (vyper_to_abi_type env ty)` by metis_tac[] >>
     drule_all val_in_memory_static_abi >> simp[]) >>
  `!mem'. mem_agree_outside tn.t_mem s.vs_memory mem' ==>
    abi_encoder_input ei at av (w2n a) cap mem'` by
    (qpat_x_assum `(_ /\ _) \/ _` strip_assume_tac >>
     simp[abi_encoder_input_word_iff, abi_encoder_input_copy_iff] >> metis_tac[]) >>
  drule_all compile_abi_encode_static_counted_ptr >>
  disch_then (qspecl_then [`PG`, `D`] strip_assume_tac) >>
  qexistsl_tac [`Gf`, `tnf`, `sf`] >> asm_rewrite_tac[] >>
  rpt strip_tac >> irule robust_val_in_memory_exterior_frame >>
  conj_tac >- (drule value_has_type_memory_wf >> simp[]) >>
  qexistsl_tac [`s.vs_memory`, `sf.vs_memory`, `tn.t_mem`, `tnf.t_mem`,
    `{i | w2n b <= i /\ i < w2n b+n}`] >>
  simp[] >> conj_tac
  >- (qpat_x_assum `mem_agree_outside _ sf.vs_memory s.vs_memory` mp_tac >>
      simp[mem_agree_outside_def] >> metis_tac[]) >>
  fs[]
QED
