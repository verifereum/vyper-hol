Theory abiEncodeValuesLayout
Ancestors
  abiEncoderOpenInput abiCanonicalWindows abiEncoderSharedMembersCorrect
  abiEncoderTuple abiDecodeRanges valueEncodingDefs contractABI ptrDiscipline venomState
  arithmetic list rich_list pred_set

Theorem abi_encode_values_member_bounds:
  LIST_REL abi_encoder_layout_valid (pre ++ ty::post) (pvs ++ v::rest) /\
  LENGTH pre = LENGTH pvs /\
  hl = head_lengths (pre ++ ty::post) 0 /\
  ho = SUM (MAP abi_member_head_size pre) /\
  off = hl + SUM (MAP2 abi_member_tail_size pre pvs) /\
  n = LENGTH (enc (Tuple (pre ++ ty::post)) (ListV (pvs ++ v::rest))) ==>
  ho = LENGTH (FLAT (abi_tuple_heads hl 0 pre pvs)) /\
  off = hl + LENGTH (FLAT (abi_tuple_tails pre pvs)) /\
  hl <= off /\ off <= n /\
  ho + abi_member_head_size ty <= hl /\
  (is_dynamic ty ==> off + LENGTH (enc ty v) <= n) /\
  (~is_dynamic ty ==> LENGTH (enc ty v) = abi_member_head_size ty)
Proof
  strip_tac >>
  `LIST_REL abi_encoder_layout_valid pre pvs /\ abi_encoder_layout_valid ty v /\
   LIST_REL abi_encoder_layout_valid post rest` by
    gvs[LIST_REL_APPEND_EQ] >>
  `LENGTH post = LENGTH rest` by metis_tac[LIST_REL_LENGTH] >>
  `ho + abi_member_head_size ty <= hl` by
    simp[head_lengths_acc, MAP_APPEND, SUM_APPEND] >>
  `n = off + abi_member_tail_size ty v + SUM (MAP2 abi_member_tail_size post rest)` by
    (asm_simp_tac bool_ss [abi_encoder_open_tuple_length, head_lengths_acc,
      MAP_APPEND, MAP2_APPEND, SUM_APPEND, MAP, MAP2, SUM, ADD_CLAUSES,
      AC ADD_COMM ADD_ASSOC]) >>
  simp[abi_encoder_open_heads_length, abi_tuple_tails_length] >>
  Cases_on `is_dynamic ty` >>
  gvs[abi_encoder_layout_valid_def, abi_member_head_size_def,
      abi_member_tail_size_def] >> decide_tac
QED

(* Heads and tails are written to separate contiguous intervals. At the last
   row these intervals cover the bytes a caller can read. *)
Theorem abi_encode_values_output_ready:
  LIST_REL abi_encoder_layout_valid tys vs /\
  hl = head_lengths tys 0 /\ tl = LENGTH (FLAT (abi_tuple_tails tys vs)) /\
  abi_encoder_tuple_prefix hl tys vs d s.vs_memory /\
  (!i. d <= i /\ i < d + hl ==> i NOTIN tn.t_mem) /\
  (!i. d + hl <= i /\ i < d + hl + tl ==> i NOTIN tn.t_mem) ==>
  LENGTH (enc (Tuple tys) (ListV vs)) = hl + tl /\
  mem_bytes_at d (hl + tl) s.vs_memory = enc (Tuple tys) (ListV vs) /\
  (!i. d <= i /\ i < d + hl + tl ==> i NOTIN tn.t_mem)
Proof
  strip_tac >>
  `LENGTH tys = LENGTH vs` by metis_tac[LIST_REL_LENGTH] >>
  `LENGTH (enc (Tuple tys) (ListV vs)) = hl + tl` by
    fs[abi_encoder_open_tuple_length, abi_tuple_tails_length,
       head_lengths_acc] >>
  `mem_bytes_at d (hl + tl) s.vs_memory = enc (Tuple tys) (ListV vs)` by
    metis_tac[abi_encoder_open_tuple_prefix_complete] >>
  `!i. d <= i /\ i < d + hl + tl ==> i NOTIN tn.t_mem` by
    (rpt strip_tac >> Cases_on `i < d + hl` >- metis_tac[] >>
     `d + hl <= i` by decide_tac >> metis_tac[]) >>
  asm_rewrite_tac[]
QED

(* A row writes at the ends of the two prefixes. Scratch writes are
   disjoint from both prefixes, so the old bytes stay untainted. *)
Theorem abi_encode_values_clean_step:
  heads + hs <= hl /\ hl <= off /\
  (!i. d <= i /\ i < d + heads ==> i NOTIN tn.t_mem) /\
  (!i. d + hl <= i /\ i < d + off ==> i NOTIN tn.t_mem) /\
  (!i. d + heads <= i /\ i < d + heads + hs ==> i NOTIN tn'.t_mem) /\
  (!i. d + off <= i /\ i < d + off + ts ==> i NOTIN tn'.t_mem) /\
  (!i. (d <= i /\ i < d + heads) \/ (d + hl <= i /\ i < d + off) ==>
    i IN tn'.t_mem ==> i IN tn.t_mem) ==>
  (!i. d <= i /\ i < d + heads + hs ==> i NOTIN tn'.t_mem) /\
  (!i. d + hl <= i /\ i < d + off + ts ==> i NOTIN tn'.t_mem)
Proof
  strip_tac >> conj_tac >> gen_tac >> strip_tac
  >- (Cases_on `i < d + heads` >> fs[NOT_LESS] >> metis_tac[]) >>
  Cases_on `i < d + off` >> fs[NOT_LESS] >> metis_tac[]
QED

Theorem abi_encode_values_prefix_step:
  LENGTH pre = LENGTH pvs /\
  heads = LENGTH (FLAT (abi_tuple_heads hl 0 pre pvs)) /\
  tails = LENGTH (FLAT (abi_tuple_tails pre pvs)) /\
  off = hl + tails /\
  abi_encoder_layout_valid ty v /\
  abi_encoder_tuple_prefix hl pre pvs d s.vs_memory /\
  mem_bytes_at d heads t.vs_memory = mem_bytes_at d heads s.vs_memory /\
  mem_bytes_at (d + hl) tails t.vs_memory = mem_bytes_at (d + hl) tails s.vs_memory /\
  (is_dynamic ty ==>
    mem_word_at (d + heads) t.vs_memory = n2w off /\
    mem_bytes_at (d + off) (LENGTH (enc ty v)) t.vs_memory = enc ty v) /\
  (~is_dynamic ty ==>
    mem_bytes_at (d + heads) (abi_member_head_size ty) t.vs_memory = enc ty v) ==>
  abi_encoder_tuple_prefix hl (pre ++ [ty]) (pvs ++ [v]) d t.vs_memory
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  irule abi_encoder_tuple_prefix_append >>
  qpat_assum `abi_encoder_tuple_prefix hl pre pvs d s.vs_memory`
    (MAP_EVERY assume_tac o CONJUNCTS o PURE_REWRITE_RULE [abi_encoder_tuple_prefix_def]) >>
  simp[abi_encoder_tuple_prefix_def] >>
  Cases_on `is_dynamic ty` >> fs[abi_encoder_layout_valid_def, abi_member_head_size_def]
  >- (map_every (fn pat => qpat_assum pat (fn th => PURE_REWRITE_TAC [GSYM th]))
          [`heads = _`, `tails = _`, `off = _`] >>
      asm_simp_tac bool_ss [abiEncoderMemoryTheory.abi_encoder_word_window, GSYM ADD_ASSOC] >>
      metis_tac[]) >>
  map_every (fn pat => qpat_assum pat (fn th => PURE_REWRITE_TAC [GSYM th]))
    [`heads = _`, `tails = _`] >>
  `!q m. mem_bytes_at q 0 m = []` by simp[mem_bytes_at_def] >>
  asm_simp_tac bool_ss [] >> metis_tac[]
QED

(* The old prefixes can cross both materialization and encoding. The proof
   of the row only needs to supply their frame, the new cell, and any tail. *)
Theorem abi_encode_values_advance_prefix:
  LENGTH pre = LENGTH pvs /\
  heads = LENGTH (FLAT (abi_tuple_heads hl 0 pre pvs)) /\
  tails = LENGTH (FLAT (abi_tuple_tails pre pvs)) /\ off = hl + tails /\
  hs = abi_member_head_size ty /\ ts = abi_member_tail_size ty v /\
  heads + hs <= hl /\
  abi_encoder_layout_valid ty v /\
  abi_encoder_tuple_prefix hl pre pvs d s.vs_memory /\
  mem_bytes_at d heads t.vs_memory = mem_bytes_at d heads s.vs_memory /\
  mem_bytes_at (d + hl) tails t.vs_memory = mem_bytes_at (d + hl) tails s.vs_memory /\
  (!i. d <= i /\ i < d + heads ==> i NOTIN tn.t_mem) /\
  (!i. d + hl <= i /\ i < d + off ==> i NOTIN tn.t_mem) /\
  (!i. (d <= i /\ i < d + heads) \/ (d + hl <= i /\ i < d + off) ==>
    i IN tn'.t_mem ==> i IN tn.t_mem) /\
  (!i. d + heads <= i /\ i < d + heads + hs ==> i NOTIN tn'.t_mem) /\
  (!i. d + off <= i /\ i < d + off + ts ==> i NOTIN tn'.t_mem) /\
  (is_dynamic ty ==>
    mem_word_at (d + heads) t.vs_memory = n2w off /\
    mem_bytes_at (d + off) ts t.vs_memory = enc ty v) /\
  (~is_dynamic ty ==>
    mem_bytes_at (d + heads) hs t.vs_memory = enc ty v) ==>
  abi_encoder_tuple_prefix hl (pre ++ [ty]) (pvs ++ [v]) d t.vs_memory /\
  (!i. d <= i /\ i < d + heads + hs ==> i NOTIN tn'.t_mem) /\
  (!i. d + hl <= i /\ i < d + off + ts ==> i NOTIN tn'.t_mem)
Proof
  strip_tac >> conj_tac
  >- (`is_dynamic ty ==> ts = LENGTH (enc ty v)` by simp[abi_member_tail_size_def] >>
      `is_dynamic ty ==> mem_bytes_at (d + off) (LENGTH (enc ty v)) t.vs_memory = enc ty v` by metis_tac[] >>
      `~is_dynamic ty ==> mem_bytes_at (d + heads) (abi_member_head_size ty) t.vs_memory = enc ty v` by metis_tac[] >>
      irule abi_encode_values_prefix_step >> asm_rewrite_tac[] >>
      qexistsl_tac [`heads`,`off`,`s`,`tails`] >> simp[]) >>
  `hl <= off` by decide_tac >>
  mp_tac (Q.INST [`heads` |-> `heads`, `off` |-> `off`, `hs` |-> `hs`,
      `ts` |-> `ts`, `hl` |-> `hl`, `d` |-> `d`,
      `tn` |-> `tn`, `tn'` |-> `tn'`] abi_encode_values_clean_step) >>
  asm_rewrite_tac[]
QED

Theorem abi_encode_values_prefix_lengths:
  LENGTH pre = LENGTH avs /\
  LIST_REL abi_encoder_layout_valid pre avs /\
  abi_encoder_layout_valid at av ==>
  LENGTH (FLAT (abi_tuple_heads hl 0 (pre ++ [at]) (avs ++ [av]))) =
    LENGTH (FLAT (abi_tuple_heads hl 0 pre avs)) + abi_member_head_size at /\
  LENGTH (FLAT (abi_tuple_tails (pre ++ [at]) (avs ++ [av]))) =
    LENGTH (FLAT (abi_tuple_tails pre avs)) + abi_member_tail_size at av
Proof
  strip_tac >>
  `LIST_REL abi_encoder_layout_valid (pre ++ [at]) (avs ++ [av])` by
    simp[LIST_REL_APPEND_EQ] >>
  simp[abi_encoder_open_heads_length, abi_tuple_tails_length, MAP_APPEND,
       MAP2_APPEND, SUM_APPEND]
QED
