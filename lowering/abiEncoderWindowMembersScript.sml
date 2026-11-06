(* Indexed prefixes retain the original source window, not a declared residual. *)
Theory abiEncoderWindowMembers
Ancestors
  abiEncoderWindowChild abiEncoderWindowPhase freshWrites
  abiEncoderWindow abiEncoderWindowContract
  abiEncoderOpenPrefix abiEncoderMembersDefs abiEncoderTuple abiCanonicalWindows
  valueEncodingProps contractABI venomMemDefs compileEnv venomState finite_map
  list rich_list pred_set arithmetic

Definition window_member_head_size_def:
  window_member_head_size (infos : (abi_enc_info # num # num # bool) list) =
    SUM (MAP (\(_,az,_,_). az) infos)
End

Definition window_member_tail_def:
  window_member_tail infos ats avs k = window_member_head_size infos +
    LENGTH (FLAT (abi_tuple_tails (TAKE k ats) (TAKE k avs)))
End

Definition window_member_prefix_def:
  window_member_prefix infos ats avs k d mem <=>
    k <= LENGTH infos /\ LENGTH infos = LENGTH ats /\ LENGTH ats = LENGTH avs /\
    mem_bytes_at d
      (LENGTH (FLAT (abi_tuple_heads (window_member_head_size infos) 0
        (TAKE k ats) (TAKE k avs)))) mem =
      FLAT (abi_tuple_heads (window_member_head_size infos) 0 (TAKE k ats) (TAKE k avs)) /\
    mem_bytes_at (d+window_member_head_size infos)
      (LENGTH (FLAT (abi_tuple_tails (TAKE k ats) (TAKE k avs)))) mem =
      FLAT (abi_tuple_tails (TAKE k ats) (TAKE k avs))
End

Definition window_member_cursor_def:
  window_member_cursor infos dp site slot sb cap d n st s <=>
    (EXISTS (\(_,_,_,dyn). dyn) infos ==>
      (?x. dp = Var x /\ not_fresh_at st x) /\
      eval_operand dp s = SOME (n2w slot) /\
      FLOOKUP s.vs_allocas site = SOME (slot,32) /\ site < st.cs_next_id /\
      slot < dimword (:256) /\
      venomMemDefs$regions_disjoint (sb,cap) (slot,32) /\
      venomMemDefs$regions_disjoint (d,n) (slot,32))
End

Definition window_members_inv_def:
  window_members_inv ctx func infos at ats avs k src dst dp site slot
      sb cap d st en s <=>
    abi_encoder_window_pre ctx func st en dst src (AbiComplex infos) at
      (ListV avs) sb cap d s /\
    abi_encoder_tuple_type at ats /\ has_types ats avs /\
    window_member_head_size infos = head_lengths ats 0 /\
    window_member_prefix infos ats avs k d s.vs_memory /\
    window_member_cursor infos dp site slot sb cap d
      (LENGTH (enc at (ListV avs))) st s /\
    (EXISTS (\(_,_,_,dyn). dyn) infos ==>
      mem_word_at slot s.vs_memory = n2w (window_member_tail infos ats avs k))
End

Theorem window_member_prefix_zero:
  LENGTH infos = LENGTH ats /\ LENGTH ats = LENGTH avs ==>
  window_member_prefix infos ats avs 0 d mem
Proof
  simp[window_member_prefix_def, abi_tuple_heads_def, abi_tuple_tails_def,
    valueEncodingTheory.mem_bytes_at_def]
QED

Theorem window_members_inv_entry:
  abi_encoder_window_pre ctx func st en dst src (AbiComplex infos) at
    (ListV avs) sb cap d s /\
  abi_encoder_tuple_type at ats /\ has_types ats avs /\
  LENGTH infos = LENGTH ats /\ LENGTH ats = LENGTH avs /\
  window_member_head_size infos = head_lengths ats 0 /\
  window_member_cursor infos dp site slot sb cap d
    (LENGTH (enc at (ListV avs))) st s /\
  (EXISTS (\(_,_,_,dyn). dyn) infos ==>
    mem_word_at slot s.vs_memory = n2w (window_member_head_size infos)) ==>
  window_members_inv ctx func infos at ats avs 0 src dst dp site slot
    sb cap d st en s
Proof
  simp[window_members_inv_def, window_member_prefix_zero,
    window_member_tail_def, abi_tuple_tails_def]
QED

Theorem window_member_prefix_nil:
  window_member_prefix [] [] [] 0 d mem
Proof
  simp[window_member_prefix_zero]
QED

Theorem window_member_prefix_complete:
  window_member_prefix infos ats avs (LENGTH infos) d mem /\
  has_types ats avs /\ window_member_head_size infos = head_lengths ats 0 ==>
  mem_bytes_at d (LENGTH (enc (Tuple ats) (ListV avs))) mem =
    enc (Tuple ats) (ListV avs)
Proof
  simp_tac bool_ss [window_member_prefix_def] >> strip_tac >>
  `LENGTH (FLAT (abi_tuple_heads (head_lengths ats 0) 0 ats avs)) = head_lengths ats 0` by
    (drule abi_tuple_heads_length >> simp[abiDecodeRangesTheory.head_lengths_acc]) >>
  `enc (Tuple ats) (ListV avs) =
    FLAT (abi_tuple_heads (head_lengths ats 0) 0 ats avs) ++
    FLAT (abi_tuple_tails ats avs)` by
    simp[Once enc_def, enc_tuple_parts, LET_THM] >>
  `TAKE (LENGTH infos) ats = ats /\ TAKE (LENGTH infos) avs = avs` by
    metis_tac[TAKE_LENGTH_ID] >>
  asm_rewrite_tac[] >> irule abi_encoder_memory_append >> metis_tac[]
QED

Theorem window_members_inv_source:
  window_members_inv ctx func infos at ats avs k src dst dp site slot
    sb cap d st en s /\ k < LENGTH infos /\
  EL k infos = (ei,az,ms,dyn) ==>
  ?child_cap. child_cap <= ms /\
    sb + abi_encoder_member_span (TAKE k infos) + child_cap <= sb+cap /\
    az = abi_member_head_size (EL k ats) /\ dyn = is_dynamic (EL k ats) /\
    abi_encoder_window_input ei (EL k ats) (EL k avs)
      (sb+abi_encoder_member_span (TAKE k infos)) child_cap s.vs_memory
Proof
  strip_tac >>
  `abi_encoder_window_input (AbiComplex infos) at (ListV avs) sb cap s.vs_memory /\
    abi_encoder_tuple_type at ats` by
    fs[window_members_inv_def, abi_encoder_window_pre_def] >>
  drule_all abi_encoder_window_complex_child >> strip_tac >>
  `ats' = ats` by metis_tac[abiEncoderBufferFrameTheory.abi_encoder_tuple_type_unique] >> gvs[] >>
  metis_tac[]
QED

Theorem window_members_inv_complete:
  window_members_inv ctx func infos at ats avs (LENGTH infos) src dst dp site slot
    sb cap d st en s ==>
  mem_bytes_at d (LENGTH (enc at (ListV avs))) s.vs_memory = enc at (ListV avs)
Proof
  strip_tac >>
  `enc at (ListV avs) = enc (Tuple ats) (ListV avs)` by
    (`has_types ats avs` by fs[window_members_inv_def] >>
     `LENGTH ats = LENGTH avs` by fs[window_members_inv_def, window_member_prefix_def] >>
     fs[window_members_inv_def, abiEncoderInputTheory.abi_encoder_tuple_type_def] >>
     gvs[Once enc_def, LET_THM]) >>
  asm_rewrite_tac[] >> irule window_member_prefix_complete >>
  asm_rewrite_tac[] >>
  (conj_tac >- fs[window_members_inv_def]) >>
  qexists_tac `infos` >> fs[window_members_inv_def]
QED

(* No containment of the final declared end pointer is needed. *)
Theorem window_member_singleton_actual_source:
  (ct = Bytes NONE \/ ct = String) /\ has_type ct (BytesV bs) /\
  LENGTH bs <= maxlen /\ 32+LENGTH bs < ms /\
  mem_word_at sb mem = n2w (LENGTH bs) /\
  mem_bytes_at (sb+32) (LENGTH bs) mem = bs ==>
  abi_encoder_window_input (AbiComplex [(AbiBytestring maxlen,32,ms,T)])
    (Tuple [ct]) (ListV [BytesV bs]) sb (32+LENGTH bs) mem /\
  ~(abi_encoder_member_span (TAKE 1 [(AbiBytestring maxlen,32,ms,T)]) <=
      32+LENGTH bs)
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >> conj_tac
  >- (irule abi_encoder_window_singleton_bytes >> asm_rewrite_tac[] >> decide_tac) >>
  simp[abiEncoderInputTheory.abi_encoder_member_span_def] >> decide_tac
QED

Theorem window_members_inv_resources:
  window_members_inv ctx func infos at ats avs k src dst dp site slot
    sb cap d st en s ==>
  alloca_inv s /\ alloca_room ctx func s /\
  sb+cap <= s.vs_alloca_next /\
  d+LENGTH (enc at (ListV avs)) <= s.vs_alloca_next /\
  venomMemDefs$regions_disjoint (sb,cap) (d,LENGTH (enc at (ListV avs))) /\
  ~s.vs_halted /\ s.vs_current_bb = st.cs_current_bb /\
  s.vs_inst_idx = LENGTH st.cs_current_insts
Proof
  simp[window_members_inv_def, abi_encoder_window_pre_def]
QED

Theorem window_members_inv_child_source_bound:
  window_members_inv ctx func infos at ats avs k src dst dp site slot
    sb cap d st en s /\ k < LENGTH infos /\
  EL k infos = (ei,az,ms,dyn) ==>
  ?child_cap. child_cap <= ms /\
    sb + abi_encoder_member_span (TAKE k infos) + child_cap <= s.vs_alloca_next /\
    az = abi_member_head_size (EL k ats) /\ dyn = is_dynamic (EL k ats) /\
    abi_encoder_window_input ei (EL k ats) (EL k avs)
      (sb+abi_encoder_member_span (TAKE k infos)) child_cap s.vs_memory /\
    venomMemDefs$regions_disjoint
      (sb+abi_encoder_member_span (TAKE k infos),child_cap)
      (d,LENGTH (enc at (ListV avs)))
Proof
  strip_tac >> drule_all window_members_inv_source >> strip_tac >>
  drule window_members_inv_resources >> strip_tac >>
  qexists_tac `child_cap` >> asm_rewrite_tac[] >>
  (conj_tac >- decide_tac) >>
  qpat_x_assum `venomMemDefs$regions_disjoint (sb,cap) _` mp_tac >>
  simp_tac bool_ss [venomMemDefsTheory.regions_disjoint_def] >> decide_tac
QED

Theorem window_member_tail_bound:
  !ats avs k. LENGTH ats = LENGTH avs /\ k < LENGTH ats ==>
  LENGTH (FLAT (abi_tuple_tails (TAKE k ats) (TAKE k avs))) +
    (if is_dynamic (EL k ats) then LENGTH (enc (EL k ats) (EL k avs)) else 0) <=
  LENGTH (FLAT (abi_tuple_tails ats avs))
Proof
  Induct_on `ats` >- simp[] >> Cases_on `avs` >- simp[] >>
  Cases_on `k`
  >- (simp[abi_tuple_tails_def] >> Cases_on `is_dynamic h'` >> simp[]) >>
  simp[abi_tuple_tails_def] >> rpt strip_tac >>
  first_x_assum drule_all >>
  Cases_on `is_dynamic h'` >> simp[] >> decide_tac
QED

Theorem window_member_head_bound:
  !ats k. k < LENGTH ats ==>
  SUM (MAP abi_member_head_size (TAKE k ats)) + abi_member_head_size (EL k ats) <=
  head_lengths ats 0
Proof
  simp[abiDecodeRangesTheory.head_lengths_acc] >>
  metis_tac[abiEncoderInputTheory.abi_encoder_prefix_sum_bound]
QED

Theorem window_member_tuple_length:
  has_types ats avs ==>
  LENGTH (enc (Tuple ats) (ListV avs)) = head_lengths ats 0 +
    LENGTH (FLAT (abi_tuple_tails ats avs))
Proof
  strip_tac >>
  `enc (Tuple ats) (ListV avs) =
    FLAT (abi_tuple_heads (head_lengths ats 0) 0 ats avs) ++
    FLAT (abi_tuple_tails ats avs)` by
    simp[Once enc_def, enc_tuple_parts, LET_THM] >>
  asm_rewrite_tac[LENGTH_APPEND] >>
  simp[abi_tuple_heads_length, abiDecodeRangesTheory.head_lengths_acc]
QED

Theorem window_member_dynamic_bounds:
  has_types ats avs /\ LENGTH ats = LENGTH avs /\ k < LENGTH ats /\
  is_dynamic (EL k ats) ==>
  SUM (MAP abi_member_head_size (TAKE k ats)) + 32 <= head_lengths ats 0 /\
  head_lengths ats 0 +
    LENGTH (FLAT (abi_tuple_tails (TAKE k ats) (TAKE k avs))) +
    LENGTH (enc (EL k ats) (EL k avs)) <= LENGTH (enc (Tuple ats) (ListV avs))
Proof
  strip_tac >>
  drule_all window_member_tail_bound >>
  drule window_member_head_bound >>
  drule window_member_tuple_length >>
  simp[abiDecodeRangesTheory.abi_member_head_size_def] >> decide_tac
QED

(* Restrict both protected root intervals without changing declared member strides. *)
Theorem window_member_subwindow_pre:
  abi_encoder_window_pre ctx func st en dst src (AbiComplex infos) at
    (ListV avs) sb cap d s /\
  abi_encoder_admissible ei /\
  abi_encoder_window_input ei ct cv (sb+so) child_cap s.vs_memory /\
  so+child_cap <= cap /\ off+LENGTH (enc ct cv) <= LENGTH (enc at (ListV avs)) /\
  eval_operand child_src s = SOME (n2w (sb+so)) /\
  (!x. child_src = Var x ==> not_fresh_at st x) ==>
  abi_encoder_window_pre ctx func st en (Lit (n2w (d+off))) child_src
    ei ct cv (sb+so) child_cap (d+off) s
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  qpat_x_assum `abi_encoder_window_pre _ _ _ _ _ _ _ _ _ _ _ _ _` mp_tac >>
  pure_rewrite_tac [abi_encoder_window_pre_def] >> strip_tac >>
  pure_rewrite_tac [abi_encoder_window_pre_def] >>
  asm_rewrite_tac[] >> simp_tac (srw_ss()) [venomStateTheory.eval_operand_def] >>
  (conj_tac >- metis_tac[]) >>
  (conj_tac >- decide_tac) >>
  (conj_tac >- decide_tac) >>
  (conj_tac >-
    (qpat_x_assum `venomMemDefs$regions_disjoint (sb,cap) _` mp_tac >>
     simp_tac bool_ss [venomMemDefsTheory.regions_disjoint_def] >> decide_tac)) >>
  rpt gen_tac >> strip_tac >>
  `sz = 32 /\ venomMemDefs$regions_disjoint (sb,cap) (b,sz) /\
    venomMemDefs$regions_disjoint (d,LENGTH (enc at (ListV avs))) (b,sz)` by metis_tac[] >>
  asm_rewrite_tac[] >>
  qpat_x_assum `venomMemDefs$regions_disjoint (sb,cap) (b,sz)` mp_tac >>
  qpat_x_assum `venomMemDefs$regions_disjoint (d,_) (b,sz)` mp_tac >>
  simp_tac bool_ss [venomMemDefsTheory.regions_disjoint_def] >> decide_tac
QED

Theorem window_member_static_bounds:
  has_types ats avs /\ LENGTH ats = LENGTH avs /\ k < LENGTH ats /\
  ~is_dynamic (EL k ats) ==>
  SUM (MAP abi_member_head_size (TAKE k ats)) +
    LENGTH (enc (EL k ats) (EL k avs)) <= head_lengths ats 0
Proof
  strip_tac >>
  `has_type (EL k ats) (EL k avs)` by
    metis_tac[has_types_LIST_REL, LIST_REL_EL_EQN] >>
  `LENGTH (enc (EL k ats) (EL k avs)) = static_length (EL k ats)` by
    (drule_all (cj 1 enc_has_static_length) >> simp[]) >>
  drule window_member_head_bound >>
  simp[abiDecodeRangesTheory.abi_member_head_size_def]
QED

(* A live member supplies the complete recursive precondition, not a residual layout. *)
Theorem window_members_inv_child_pre:
  window_members_inv ctx func infos at ats avs k src dst dp site slot
    sb cap d st en s /\ k < LENGTH infos /\
  EL k infos = (ei,az,ms,dyn) /\ abi_encoder_admissible ei /\
  off + LENGTH (enc (EL k ats) (EL k avs)) <= LENGTH (enc at (ListV avs)) /\
  eval_operand child_src s = SOME (n2w (sb+abi_encoder_member_span (TAKE k infos))) /\
  (!x. child_src = Var x ==> not_fresh_at st x) ==>
  ?child_cap. child_cap <= ms /\
    abi_encoder_window_pre ctx func st en (Lit (n2w (d+off))) child_src
      ei (EL k ats) (EL k avs)
      (sb+abi_encoder_member_span (TAKE k infos)) child_cap (d+off) s
Proof
  strip_tac >> drule_all window_members_inv_source >> strip_tac >>
  qexists_tac `child_cap` >> asm_rewrite_tac[] >>
  irule window_member_subwindow_pre >> asm_rewrite_tac[] >>
  qexistsl_tac [`at`, `avs`, `cap`, `dst`, `infos`, `src`] >>
  asm_rewrite_tac[] >>
  (conj_tac >- decide_tac) >> fs[window_members_inv_def]
QED

Theorem window_members_inv_output_bounds:
  window_members_inv ctx func infos at ats avs k src dst dp site slot
    sb cap d st en s /\ k < LENGTH infos ==>
  (is_dynamic (EL k ats) ==>
    SUM (MAP abi_member_head_size (TAKE k ats)) + 32 <= window_member_head_size infos /\
    window_member_tail infos ats avs k + LENGTH (enc (EL k ats) (EL k avs)) <=
      LENGTH (enc at (ListV avs))) /\
  (~is_dynamic (EL k ats) ==>
    SUM (MAP abi_member_head_size (TAKE k ats)) + LENGTH (enc (EL k ats) (EL k avs)) <=
      window_member_head_size infos)
Proof
  strip_tac >>
  `has_types ats avs /\ LENGTH ats = LENGTH avs /\ k < LENGTH ats /\
    window_member_head_size infos = head_lengths ats 0 /\ abi_encoder_tuple_type at ats` by
    fs[window_members_inv_def, window_member_prefix_def] >>
  `enc at (ListV avs) = enc (Tuple ats) (ListV avs)` by
    (fs[abiEncoderInputTheory.abi_encoder_tuple_type_def] >>
     gvs[Once enc_def, LET_THM]) >>
  asm_rewrite_tac[window_member_tail_def] >>
  conj_tac >- metis_tac[window_member_dynamic_bounds] >>
  metis_tac[window_member_static_bounds]
QED

Theorem window_members_inv_dynamic_cursor:
  window_members_inv ctx func infos at ats avs k src dst dp site slot
    sb cap d st en s /\ k < LENGTH infos /\ EL k infos = (ei,az,ms,T) ==>
  (?x. dp = Var x /\ not_fresh_at st x) /\
  eval_operand dp s = SOME (n2w slot) /\
  FLOOKUP s.vs_allocas site = SOME (slot,32) /\
  site NOTIN window_alloca_sites func (frag_ids st en) /\
  slot < dimword (:256) /\
  mem_word_at slot s.vs_memory = n2w (window_member_tail infos ats avs k) /\
  d + SUM (MAP abi_member_head_size (TAKE k ats)) < dimword (:256) /\
  (d + SUM (MAP abi_member_head_size (TAKE k ats)) + 32 <= slot \/
   slot+32 <= d + SUM (MAP abi_member_head_size (TAKE k ats))) /\
  venomMemDefs$regions_disjoint
    (d+window_member_tail infos ats avs k,LENGTH (enc (EL k ats) (EL k avs)))
    (d+SUM (MAP abi_member_head_size (TAKE k ats)),32) /\
  venomMemDefs$regions_disjoint
    (d+window_member_tail infos ats avs k,LENGTH (enc (EL k ats) (EL k avs))) (slot,32)
Proof
  strip_tac >>
  `EXISTS (\(_,_,_,dyn). dyn) infos` by
    (simp[EXISTS_MEM] >> qexists_tac `(ei,az,ms,T)` >>
     simp[] >> metis_tac[MEM_EL]) >>
  `is_dynamic (EL k ats)` by
    metis_tac[window_members_inv_source] >>
  drule_all window_members_inv_output_bounds >> strip_tac >>
  drule window_members_inv_resources >> strip_tac >>
  `d+LENGTH (enc at (ListV avs)) < dimword (:256)` by
    metis_tac[exprLoweringPropsTheory.alloca_room_next_lt, LESS_EQ_LESS_TRANS] >>
  `head_lengths ats 0 <= LENGTH (enc at (ListV avs))` by
    (`has_types ats avs /\ abi_encoder_tuple_type at ats /\ LENGTH ats = LENGTH avs` by
       fs[window_members_inv_def, window_member_prefix_def] >>
     `enc at (ListV avs) = enc (Tuple ats) (ListV avs)` by
       (fs[abiEncoderInputTheory.abi_encoder_tuple_type_def] >> gvs[Once enc_def, LET_THM]) >>
     drule window_member_tuple_length >> simp[]) >>
  qpat_x_assum `window_members_inv _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _` mp_tac >>
  simp_tac bool_ss [window_members_inv_def, window_member_cursor_def] >> strip_tac >>
  `site < st.cs_next_id /\
   venomMemDefs$regions_disjoint (d,LENGTH (enc at (ListV avs))) (slot,32)` by
    metis_tac[] >>
  `site NOTIN window_alloca_sites func (frag_ids st en)` by
    (simp[window_alloca_sites_def, abiEncoderPropsTheory.frag_ids_def] >> decide_tac) >>
  `SUM (MAP abi_member_head_size (TAKE k ats)) + 32 <= head_lengths ats 0 /\
   window_member_tail infos ats avs k + LENGTH (enc (EL k ats) (EL k avs)) <=
     LENGTH (enc at (ListV avs))` by metis_tac[] >>
  asm_rewrite_tac[] >>
  fs[window_member_tail_def] >>
  qpat_x_assum `venomMemDefs$regions_disjoint (d,_) (slot,32)` mp_tac >>
  simp_tac bool_ss [venomMemDefsTheory.regions_disjoint_def] >> decide_tac
QED

(* Prefix transport is independent of the child's execution structure. *)
Theorem window_member_prefix_tuple:
  window_member_prefix infos ats avs k d mem <=>
  k <= LENGTH infos /\ LENGTH infos = LENGTH ats /\ LENGTH ats = LENGTH avs /\
  abi_encoder_tuple_prefix (window_member_head_size infos)
    (TAKE k ats) (TAKE k avs) d mem
Proof
  simp[window_member_prefix_def, abi_encoder_tuple_prefix_def]
QED

Theorem window_member_prefix_frame:
  window_member_prefix infos ats avs k d s.vs_memory /\
  abi_encoder_registered_effect ids outs s t /\ window_alloca_growth s t /\
  d + LENGTH (FLAT (abi_tuple_heads (window_member_head_size infos) 0
      (TAKE k ats) (TAKE k avs))) <= s.vs_alloca_next /\
  d + window_member_tail infos ats avs k <= s.vs_alloca_next /\
  EVERY (\r. venomMemDefs$regions_disjoint
    (d,LENGTH (FLAT (abi_tuple_heads (window_member_head_size infos) 0
      (TAKE k ats) (TAKE k avs)))) r) outs /\
  EVERY (\r. venomMemDefs$regions_disjoint
    (d+window_member_head_size infos,
      LENGTH (FLAT (abi_tuple_tails (TAKE k ats) (TAKE k avs)))) r) outs /\
  (!i b sz. i IN ids /\ FLOOKUP s.vs_allocas i = SOME (b,sz) ==>
    venomMemDefs$regions_disjoint
      (d,LENGTH (FLAT (abi_tuple_heads (window_member_head_size infos) 0
        (TAKE k ats) (TAKE k avs)))) (b,sz) /\
    venomMemDefs$regions_disjoint
      (d+window_member_head_size infos,
        LENGTH (FLAT (abi_tuple_tails (TAKE k ats) (TAKE k avs)))) (b,sz)) ==>
  window_member_prefix infos ats avs k d t.vs_memory
Proof
  strip_tac >>
  `mem_bytes_at d (LENGTH (FLAT (abi_tuple_heads (window_member_head_size infos) 0
      (TAKE k ats) (TAKE k avs)))) t.vs_memory =
   mem_bytes_at d (LENGTH (FLAT (abi_tuple_heads (window_member_head_size infos) 0
      (TAKE k ats) (TAKE k avs)))) s.vs_memory` by
    (irule window_alloca_growth_frame >> metis_tac[]) >>
  `mem_bytes_at (d+window_member_head_size infos)
      (LENGTH (FLAT (abi_tuple_tails (TAKE k ats) (TAKE k avs)))) t.vs_memory =
   mem_bytes_at (d+window_member_head_size infos)
      (LENGTH (FLAT (abi_tuple_tails (TAKE k ats) (TAKE k avs)))) s.vs_memory` by
    (irule window_alloca_growth_frame >> fs[window_member_tail_def] >> metis_tac[]) >>
  fs[window_member_prefix_def]
QED

Theorem window_member_prefix_advance:
  window_member_prefix infos ats avs k d old_mem /\ k < LENGTH infos /\
  abi_encoder_tuple_prefix (window_member_head_size infos)
    (TAKE k ats ++ [EL k ats]) (TAKE k avs ++ [EL k avs]) d mem ==>
  window_member_prefix infos ats avs (SUC k) d mem
Proof
  simp_tac bool_ss [window_member_prefix_tuple] >> strip_tac >>
  `k < LENGTH ats /\ k < LENGTH avs` by decide_tac >>
  simp[TAKE_SUC, TAKE1_DROP]
QED

Theorem window_member_prefix_step:
  window_member_prefix infos ats avs k d mem /\ k < LENGTH infos /\
  mem_bytes_at
    (d+LENGTH (FLAT (abi_tuple_heads (window_member_head_size infos) 0
      (TAKE k ats) (TAKE k avs))))
    (LENGTH (if is_dynamic (EL k ats) then
      enc_number (Uint 256) (NumV (window_member_tail infos ats avs k))
      else enc (EL k ats) (EL k avs))) mem =
    (if is_dynamic (EL k ats) then
      enc_number (Uint 256) (NumV (window_member_tail infos ats avs k))
      else enc (EL k ats) (EL k avs)) /\
  mem_bytes_at (d+window_member_tail infos ats avs k)
    (LENGTH (if is_dynamic (EL k ats) then enc (EL k ats) (EL k avs) else [])) mem =
    (if is_dynamic (EL k ats) then enc (EL k ats) (EL k avs) else []) ==>
  window_member_prefix infos ats avs (SUC k) d mem
Proof
  strip_tac >> irule window_member_prefix_advance >>
  asm_rewrite_tac[] >> reverse conj_tac
  >- (qexists_tac `mem` >> asm_rewrite_tac[]) >>
  irule abi_encoder_tuple_prefix_append >>
  `k <= LENGTH ats /\ k <= LENGTH avs /\ LENGTH ats = LENGTH avs` by
    fs[window_member_prefix_def] >>
  asm_rewrite_tac[] >>
  simp_tac bool_ss [GSYM window_member_tail_def, GSYM ADD_ASSOC] >>
  asm_rewrite_tac[] >> conj_tac
  >- simp[] >> fs[window_member_prefix_tuple]
QED

(* Remaining sites cannot have been newly registered by the completed prefix. *)
Theorem window_member_remaining_pre:
  abi_encoder_window_pre ctx func st en dst src ei at av sb cap d s /\
  window_phase ctx func st mid ids outs s t /\
  st.cs_next_var <= mid.cs_next_var /\ st.cs_next_id <= mid.cs_next_id /\
  fn_has_code mid en func /\
  DISJOINT ids (window_alloca_sites func (frag_ids mid en)) /\
  abi_encoder_window_input ei at av sb cap t.vs_memory /\
  eval_operand src t = SOME (n2w sb) /\ eval_operand dst t = SOME (n2w d) ==>
  abi_encoder_window_pre ctx func mid en dst src ei at av sb cap d t
Proof
  strip_tac >>
  drule window_phase_resources >> strip_tac >>
  drule window_phase_control >> strip_tac >>
  drule window_phase_effect >> strip_tac >>
  `s.vs_alloca_next <= t.vs_alloca_next` by fs[window_alloca_growth_def] >>
  qpat_x_assum `abi_encoder_window_pre _ _ _ _ _ _ _ _ _ _ _ _ _` mp_tac >>
  pure_rewrite_tac [abi_encoder_window_pre_def] >> strip_tac >>
  pure_rewrite_tac [abi_encoder_window_pre_def] >> asm_rewrite_tac[] >>
  (conj_tac >- metis_tac[not_fresh_at_mono]) >>
  (conj_tac >- decide_tac) >> (conj_tac >- decide_tac) >>
  rpt gen_tac >> strip_tac >>
  `inst.inst_id IN frag_ids st en` by
    (qpat_x_assum `_ IN frag_ids mid en` mp_tac >>
     simp_tac (srw_ss()) [abiEncoderPropsTheory.frag_ids_def] >> decide_tac) >>
  `inst.inst_id NOTIN ids` by
    (fs[DISJOINT_DEF, EXTENSION, window_alloca_sites_def] >> metis_tac[]) >>
  `FLOOKUP s.vs_allocas inst.inst_id = SOME (b,sz)` by
    (qpat_x_assum `abi_encoder_registered_effect _ _ _ _` mp_tac >>
     pure_rewrite_tac [abiEncoderRegisteredEffectTheory.abi_encoder_registered_effect_def] >>
     metis_tac[]) >>
  metis_tac[]
QED

Theorem window_member_prefix_layout:
  has_types ats avs /\ k <= LENGTH ats ==>
  has_types (TAKE k ats) (TAKE k avs) /\
  LENGTH (FLAT (abi_tuple_heads hl 0 (TAKE k ats) (TAKE k avs))) =
    SUM (MAP abi_member_head_size (TAKE k ats))
Proof
  strip_tac >>
  `has_types (TAKE k ats) (TAKE k avs)` by
    metis_tac[has_types_LIST_REL, LIST_REL_TAKE] >>
  simp[abi_tuple_heads_length, abiDecodeRangesTheory.head_lengths_acc]
QED

Theorem window_member_prefix_static_step:
  window_member_prefix infos ats avs k d mem /\ k < LENGTH infos /\
  has_types ats avs /\ ~is_dynamic (EL k ats) /\
  mem_bytes_at (d+SUM (MAP abi_member_head_size (TAKE k ats)))
    (LENGTH (enc (EL k ats) (EL k avs))) mem = enc (EL k ats) (EL k avs) ==>
  window_member_prefix infos ats avs (SUC k) d mem
Proof
  strip_tac >>
  `k <= LENGTH ats` by fs[window_member_prefix_def] >>
  drule_all window_member_prefix_layout >> strip_tac >>
  irule window_member_prefix_step >>
  asm_rewrite_tac[] >>
  simp[abi_tuple_heads_length, abiDecodeRangesTheory.head_lengths_acc,
    valueEncodingTheory.mem_bytes_at_def]
QED

Theorem window_member_prefix_dynamic_step:
  window_member_prefix infos ats avs k d mem /\ k < LENGTH infos /\
  has_types ats avs /\ is_dynamic (EL k ats) /\
  mem_word_at (d+SUM (MAP abi_member_head_size (TAKE k ats))) mem =
    n2w (window_member_tail infos ats avs k) /\
  mem_bytes_at (d+window_member_tail infos ats avs k)
    (LENGTH (enc (EL k ats) (EL k avs))) mem = enc (EL k ats) (EL k avs) ==>
  window_member_prefix infos ats avs (SUC k) d mem
Proof
  strip_tac >>
  `k <= LENGTH ats` by fs[window_member_prefix_def] >>
  drule_all window_member_prefix_layout >> strip_tac >>
  irule window_member_prefix_step >>
  asm_rewrite_tac[] >>
  simp_tac bool_ss [LENGTH_enc_number] >>
  asm_simp_tac (srw_ss()) [abiEncoderMemoryTheory.abi_encoder_word_window, enc_number_def]
QED

(* Static member writes start at the end of the completed head prefix. *)
Theorem window_member_static_prefix_frame:
  window_members_inv ctx func infos at ats avs k src dst dp site slot
    sb cap d st en s /\ k < LENGTH infos /\ ~is_dynamic (EL k ats) /\
  window_phase ctx func st en (window_alloca_sites func (frag_ids st en))
    [(d+SUM (MAP abi_member_head_size (TAKE k ats)),
      LENGTH (enc (EL k ats) (EL k avs)))] s t ==>
  window_member_prefix infos ats avs k d t.vs_memory
Proof
  strip_tac >>
  `has_types ats avs /\ k < LENGTH ats /\ k <= LENGTH ats /\ LENGTH ats = LENGTH avs /\
    window_member_prefix infos ats avs k d s.vs_memory` by
    fs[window_members_inv_def, window_member_prefix_def] >>
  drule_all window_member_prefix_layout >> strip_tac >>
  drule_all window_members_inv_output_bounds >> strip_tac >>
  drule window_members_inv_resources >> strip_tac >>
  `head_lengths ats 0 <= LENGTH (enc at (ListV avs)) /\
    window_member_tail infos ats avs k <= LENGTH (enc at (ListV avs))` by
    (drule window_member_tuple_length >>
     `enc at (ListV avs) = enc (Tuple ats) (ListV avs)` by
       (fs[window_members_inv_def, abiEncoderInputTheory.abi_encoder_tuple_type_def] >>
        gvs[Once enc_def, LET_THM]) >>
     drule_all window_member_tail_bound >> simp[window_member_tail_def] >>
     fs[window_members_inv_def]) >>
  irule window_member_prefix_frame >>
  qexistsl_tac [`window_alloca_sites func (frag_ids st en)`,
    `[(d+SUM (MAP abi_member_head_size (TAKE k ats)),
       LENGTH (enc (EL k ats) (EL k avs)))]`, `s`] >>
  asm_rewrite_tac[] >>
  `abi_encoder_registered_effect (window_alloca_sites func (frag_ids st en))
    [(d+SUM (MAP abi_member_head_size (TAKE k ats)),
       LENGTH (enc (EL k ats) (EL k avs)))] s t /\ window_alloca_growth s t` by
    metis_tac[window_phase_effect, window_phase_resources] >>
  asm_rewrite_tac[] >>
  (conj_tac >- simp[venomMemDefsTheory.regions_disjoint_def]) >>
  (conj_tac >- (fs[venomMemDefsTheory.regions_disjoint_def] >> decide_tac)) >>
  reverse conj_tac
  >- (gvs[window_members_inv_def] >> decide_tac) >>
  rpt gen_tac >> strip_tac >>
  `venomMemDefs$regions_disjoint (d,LENGTH (enc at (ListV avs))) (b,sz)` by
    (irule (cj 3 window_pre_sites) >>
     fs[window_members_inv_def] >> metis_tac[]) >>
  `SUM (MAP abi_member_head_size (TAKE k ats)) +
     LENGTH (enc (EL k ats) (EL k avs)) <= window_member_head_size infos` by metis_tac[] >>
  `window_member_head_size infos = head_lengths ats 0` by fs[window_members_inv_def] >>
  qpat_x_assum `window_member_tail infos ats avs k <= _` mp_tac >>
  qpat_x_assum `venomMemDefs$regions_disjoint (d,_) (b,sz)` mp_tac >>
  pure_rewrite_tac[window_member_tail_def, venomMemDefsTheory.regions_disjoint_def] >>
  decide_tac
QED

Theorem window_members_inv_total_bounds:
  window_members_inv ctx func infos at ats avs k src dst dp site slot
    sb cap d st en s /\ k < LENGTH infos ==>
  window_member_head_size infos <= LENGTH (enc at (ListV avs)) /\
  window_member_tail infos ats avs k <= LENGTH (enc at (ListV avs))
Proof
  strip_tac >>
  `has_types ats avs /\ LENGTH ats = LENGTH avs /\ k < LENGTH ats /\
    window_member_head_size infos = head_lengths ats 0 /\ abi_encoder_tuple_type at ats` by
    fs[window_members_inv_def, window_member_prefix_def] >>
  `enc at (ListV avs) = enc (Tuple ats) (ListV avs)` by
    (fs[abiEncoderInputTheory.abi_encoder_tuple_type_def] >> gvs[Once enc_def, LET_THM]) >>
  drule window_member_tuple_length >>
  drule_all window_member_tail_bound >>
  simp[window_member_tail_def] >> decide_tac
QED

Theorem window_member_static_run:
  window_members_inv ctx func infos at ats avs k src dst dp site slot
    sb cap d st en s /\ k < LENGTH infos /\
  EL k infos = (ei,az,ms,F) /\ abi_encoder_admissible ei /\ window_strong_contract ei /\
  compile_abi_encode_child dst child_src ei F
    (SUM (MAP abi_member_head_size (TAKE k ats))) dp st = (out,en) /\
  eval_operand child_src s = SOME (n2w (sb+abi_encoder_member_span (TAKE k infos))) /\
  (!x. child_src = Var x ==> not_fresh_at st x) ==>
  ?t. window_phase ctx func st en (window_alloca_sites func (frag_ids st en))
        [(d+SUM (MAP abi_member_head_size (TAKE k ats)),
          LENGTH (enc (EL k ats) (EL k avs)))] s t /\
      window_member_prefix infos ats avs (SUC k) d t.vs_memory /\
      eval_operand out t = SOME (n2w (LENGTH (enc (EL k ats) (EL k avs)))) /\
      (!i b sz. i IN window_alloca_sites func (frag_ids st en) /\
        FLOOKUP t.vs_allocas i = SOME (b,sz) ==> sz = 32)
Proof
  strip_tac >>
  `~is_dynamic (EL k ats)` by metis_tac[window_members_inv_source] >>
  drule_all window_members_inv_output_bounds >> strip_tac >>
  drule_all window_members_inv_total_bounds >> strip_tac >>
  `SUM (MAP abi_member_head_size (TAKE k ats)) +
    LENGTH (enc (EL k ats) (EL k avs)) <= LENGTH (enc at (ListV avs))` by
    (gvs[] >> decide_tac) >>
  drule_all window_members_inv_child_pre >> strip_tac >>
  `eval_operand dst s = SOME (n2w d)` by
    (qpat_assum `window_members_inv _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _` mp_tac >>
     simp_tac bool_ss [window_members_inv_def, abi_encoder_window_pre_def] >>
     metis_tac[]) >>
  drule_all window_static_child_run >> strip_tac >>
  qexists_tac `t` >> asm_rewrite_tac[] >>
  irule window_member_prefix_static_step >> asm_rewrite_tac[] >>
  `window_member_prefix infos ats avs k d t.vs_memory` by
    (irule window_member_static_prefix_frame >> metis_tac[]) >>
  asm_rewrite_tac[] >>
  qpat_assum `window_members_inv _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _` mp_tac >>
  simp_tac bool_ss [window_members_inv_def] >> metis_tac[]
QED

Theorem window_member_dynamic_prefix_frame:
  window_members_inv ctx func infos at ats avs k src dst dp site slot
    sb cap d st en s /\ k < LENGTH infos /\ EL k infos = (ei,az,ms,T) /\
  window_phase ctx func st en (window_alloca_sites func (frag_ids st en) UNION {site})
    [(d+SUM (MAP abi_member_head_size (TAKE k ats)),32);
     (d+window_member_tail infos ats avs k,LENGTH (enc (EL k ats) (EL k avs)))] s t ==>
  window_member_prefix infos ats avs k d t.vs_memory
Proof
  strip_tac >>
  `has_types ats avs /\ k <= LENGTH ats /\
    window_member_prefix infos ats avs k d s.vs_memory` by
    fs[window_members_inv_def, window_member_prefix_def] >>
  `is_dynamic (EL k ats)` by metis_tac[window_members_inv_source] >>
  `EXISTS (\(_,_,_,dyn). dyn) infos` by
    (simp[EXISTS_MEM] >> qexists_tac `(ei,az,ms,T)` >> simp[] >> metis_tac[MEM_EL]) >>
  `venomMemDefs$regions_disjoint (d,LENGTH (enc at (ListV avs))) (slot,32) /\
    FLOOKUP s.vs_allocas site = SOME (slot,32)` by
    fs[window_members_inv_def, window_member_cursor_def] >>
  drule_all window_member_prefix_layout >> strip_tac >>
  drule_all window_members_inv_output_bounds >> strip_tac >>
  drule_all window_members_inv_total_bounds >> strip_tac >>
  drule window_members_inv_resources >> strip_tac >>
  `SUM (MAP abi_member_head_size (TAKE k ats)) + 32 <= window_member_head_size infos` by
    metis_tac[] >>
  irule window_member_prefix_frame >>
  qexistsl_tac [`window_alloca_sites func (frag_ids st en) UNION {site}`,
    `[(d+SUM (MAP abi_member_head_size (TAKE k ats)),32);
      (d+window_member_tail infos ats avs k,LENGTH (enc (EL k ats) (EL k avs)))]`, `s`] >>
  asm_rewrite_tac[] >>
  `abi_encoder_registered_effect (window_alloca_sites func (frag_ids st en) UNION {site})
    [(d+SUM (MAP abi_member_head_size (TAKE k ats)),32);
      (d+window_member_tail infos ats avs k,LENGTH (enc (EL k ats) (EL k avs)))] s t /\
    window_alloca_growth s t` by metis_tac[window_phase_effect, window_phase_resources] >>
  asm_rewrite_tac[] >>
  (conj_tac >- (simp[venomMemDefsTheory.regions_disjoint_def, window_member_tail_def] >>
    decide_tac)) >>
  (conj_tac >- (simp[venomMemDefsTheory.regions_disjoint_def, window_member_tail_def] >>
    decide_tac)) >>
  reverse conj_tac >- decide_tac >>
  rpt gen_tac >> strip_tac >>
  `venomMemDefs$regions_disjoint (d,LENGTH (enc at (ListV avs))) (b,sz)` by
    (Cases_on `i = site`
     >- (gvs[] >> metis_tac[optionTheory.SOME_11, pairTheory.PAIR_EQ]) >>
     `i IN window_alloca_sites func (frag_ids st en)` by fs[] >>
     irule (cj 3 window_pre_sites) >> fs[window_members_inv_def] >> metis_tac[]) >>
  qpat_x_assum `window_member_tail infos ats avs k <= _` mp_tac >>
  qpat_x_assum `venomMemDefs$regions_disjoint (d,_) (b,sz)` mp_tac >>
  pure_rewrite_tac[window_member_tail_def, venomMemDefsTheory.regions_disjoint_def] >>
  decide_tac
QED

Theorem window_member_dynamic_run:
  window_members_inv ctx func infos at ats avs k src dst dp site slot
    sb cap d st en s /\ k < LENGTH infos /\
  EL k infos = (ei,az,ms,T) /\ abi_encoder_admissible ei /\ window_strong_contract ei /\
  compile_abi_encode_child dst child_src ei T
    (SUM (MAP abi_member_head_size (TAKE k ats))) dp st = (out,en) /\
  eval_operand child_src s = SOME (n2w (sb+abi_encoder_member_span (TAKE k infos))) /\
  (!x. child_src = Var x ==> not_fresh_at st x) ==>
  ?t. window_phase ctx func st en (window_alloca_sites func (frag_ids st en) UNION {site})
        [(d+SUM (MAP abi_member_head_size (TAKE k ats)),32);
         (d+window_member_tail infos ats avs k,LENGTH (enc (EL k ats) (EL k avs)))] s t /\
      window_member_prefix infos ats avs (SUC k) d t.vs_memory /\
      mem_word_at slot t.vs_memory = n2w (window_member_tail infos ats avs k +
        LENGTH (enc (EL k ats) (EL k avs))) /\
      FLOOKUP t.vs_allocas site = SOME (slot,32) /\
      eval_operand out t = SOME (n2w (LENGTH (enc (EL k ats) (EL k avs)))) /\
      (!i b sz. i IN (window_alloca_sites func (frag_ids st en) UNION {site}) /\
        FLOOKUP t.vs_allocas i = SOME (b,sz) ==> sz = 32)
Proof
  strip_tac >>
  drule_all window_members_inv_dynamic_cursor >>
  disch_then (CONJUNCTS_THEN2 STRIP_ASSUME_TAC
    (REPEAT_TCL CONJUNCTS_THEN assume_tac)) >>
  qpat_x_assum `dp = Var _` SUBST_ALL_TAC >>
  `is_dynamic (EL k ats)` by metis_tac[window_members_inv_source] >>
  drule_all window_members_inv_output_bounds >> strip_tac >>
  `window_member_tail infos ats avs k + LENGTH (enc (EL k ats) (EL k avs)) <=
    LENGTH (enc at (ListV avs))` by metis_tac[] >>
  drule_all window_members_inv_child_pre >> strip_tac >>
  `eval_operand dst s = SOME (n2w d) /\
    (!x. dst = Var x ==> not_fresh_at st x)` by
    (qpat_assum `window_members_inv _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _` mp_tac >>
     simp_tac bool_ss [window_members_inv_def, abi_encoder_window_pre_def] >> metis_tac[]) >>
  drule_all window_dynamic_child_run >> strip_tac >>
  qexists_tac `t` >> asm_rewrite_tac[] >>
  irule window_member_prefix_dynamic_step >> asm_rewrite_tac[] >>
  `window_member_prefix infos ats avs k d t.vs_memory` by
    (irule window_member_dynamic_prefix_frame >> metis_tac[]) >>
  asm_rewrite_tac[] >>
  qpat_assum `window_members_inv _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _` mp_tac >>
  simp_tac bool_ss [window_members_inv_def] >> metis_tac[]
QED

(* A member phase may write only output subwindows and its owned parent cursor. *)
Theorem window_member_source_frame:
  window_members_inv ctx func infos at ats avs k src dst dp site slot
    sb cap d st en s /\
  window_phase ctx func st mid ids outs s t /\
  ids SUBSET (window_alloca_sites func (frag_ids st en) UNION
    (if EXISTS (\(_,_,_,dyn). dyn) infos then {site} else {})) /\
  EVERY (\(b,n). d <= b /\ b+n <= d+LENGTH (enc at (ListV avs))) outs ==>
  abi_encoder_window_input (AbiComplex infos) at (ListV avs) sb cap t.vs_memory
Proof
  strip_tac >>
  `abi_encoder_window_pre ctx func st en dst src (AbiComplex infos) at
    (ListV avs) sb cap d s` by fs[window_members_inv_def] >>
  `abi_encoder_window_input (AbiComplex infos) at (ListV avs) sb cap s.vs_memory` by
    (qpat_assum `abi_encoder_window_pre _ _ _ _ _ _ _ _ _ _ _ _ _` mp_tac >>
     simp_tac bool_ss [abi_encoder_window_pre_def] >> metis_tac[]) >>
  drule window_members_inv_resources >> strip_tac >>
  irule window_alloca_growth_source >>
  qexistsl_tac [`ids`, `outs`, `s`] >> asm_rewrite_tac[] >>
  `abi_encoder_registered_effect ids outs s t /\ window_alloca_growth s t` by
    metis_tac[window_phase_effect, window_phase_resources] >>
  asm_rewrite_tac[] >> conj_tac
  >- (fs[EVERY_MEM] >> rpt strip_tac >> PairCases_on `r` >>
      `d <= r0 /\ r0+r1 <= d+LENGTH (enc at (ListV avs))` by
        (first_x_assum drule >> simp[]) >>
      qpat_x_assum `venomMemDefs$regions_disjoint (sb,cap) _` mp_tac >>
      pure_rewrite_tac[venomMemDefsTheory.regions_disjoint_def] >> decide_tac) >>
  rpt gen_tac >> strip_tac >>
  Cases_on `i IN window_alloca_sites func (frag_ids st en)`
  >- (irule (cj 2 window_pre_sites) >> metis_tac[]) >>
  `EXISTS (\(_,_,_,dyn). dyn) infos /\ i = site` by
    (qpat_x_assum `ids SUBSET _` mp_tac >> simp[SUBSET_DEF] >>
     Cases_on `EXISTS (\(_,_,_,dyn). dyn) infos` >> simp[] >> metis_tac[]) >>
  `FLOOKUP s.vs_allocas site = SOME (slot,32) /\
    venomMemDefs$regions_disjoint (sb,cap) (slot,32)` by
    fs[window_members_inv_def, window_member_cursor_def] >>
  gvs[]
QED

Theorem window_member_phase_pre:
  window_members_inv ctx func infos at ats avs k src dst dp site slot
    sb cap d st en s /\
  window_phase ctx func st mid ids outs s t /\
  ids SUBSET (window_alloca_sites func (frag_ids st en) UNION
    (if EXISTS (\(_,_,_,dyn). dyn) infos then {site} else {})) /\
  EVERY (\(b,n). d <= b /\ b+n <= d+LENGTH (enc at (ListV avs))) outs /\
  st.cs_next_var <= mid.cs_next_var /\ st.cs_next_id <= mid.cs_next_id /\
  fn_has_code mid en func /\
  DISJOINT ids (window_alloca_sites func (frag_ids mid en)) ==>
  abi_encoder_window_pre ctx func mid en dst src (AbiComplex infos) at
    (ListV avs) sb cap d t
Proof
  strip_tac >>
  `abi_encoder_window_pre ctx func st en dst src (AbiComplex infos) at
    (ListV avs) sb cap d s` by fs[window_members_inv_def] >>
  `eval_operand src s = SOME (n2w sb) /\ eval_operand dst s = SOME (n2w d) /\
    (!x. src = Var x ==> not_fresh_at st x) /\
    (!x. dst = Var x ==> not_fresh_at st x)` by
    (qpat_assum `abi_encoder_window_pre _ _ _ _ _ _ _ _ _ _ _ _ _` mp_tac >>
     simp_tac bool_ss [abi_encoder_window_pre_def] >> metis_tac[]) >>
  `eval_operand src t = SOME (n2w sb) /\ eval_operand dst t = SOME (n2w d)` by
    metis_tac[window_phase_operand] >>
  `abi_encoder_window_input (AbiComplex infos) at (ListV avs) sb cap t.vs_memory` by
    (irule window_member_source_frame >> metis_tac[]) >>
  irule window_member_remaining_pre >> metis_tac[]
QED

Theorem window_member_cursor_phase:
  window_member_cursor infos dp site slot sb cap d n st s /\
  window_phase ctx func st mid ids outs s t /\
  st.cs_next_var <= mid.cs_next_var /\ st.cs_next_id <= mid.cs_next_id ==>
  window_member_cursor infos dp site slot sb cap d n mid t
Proof
  simp_tac bool_ss [window_member_cursor_def] >> strip_tac >> strip_tac >>
  `(?x. dp = Var x /\ not_fresh_at st x) /\
    eval_operand dp s = SOME (n2w slot) /\
    FLOOKUP s.vs_allocas site = SOME (slot,32) /\ site < st.cs_next_id /\
    slot < dimword (:256) /\
    venomMemDefs$regions_disjoint (sb,cap) (slot,32) /\
    venomMemDefs$regions_disjoint (d,n) (slot,32)` by metis_tac[] >>
  `eval_operand dp t = SOME (n2w slot)` by
    (gvs[] >> irule window_phase_operand >> simp[] >> metis_tac[]) >>
  `FLOOKUP t.vs_allocas site = SOME (slot,32)` by
    metis_tac[window_phase_effect,
      abiEncoderRegisteredEffectTheory.abi_encoder_registered_effect_allocated] >>
  asm_rewrite_tac[] >> conj_tac
  >- metis_tac[not_fresh_at_mono] >> decide_tac
QED

Theorem window_member_tail_step:
  LENGTH ats = LENGTH avs /\ k < LENGTH ats ==>
  window_member_tail infos ats avs (SUC k) = window_member_tail infos ats avs k +
    (if is_dynamic (EL k ats) then LENGTH (enc (EL k ats) (EL k avs)) else 0)
Proof
  strip_tac >>
  `k < LENGTH avs` by decide_tac >>
  simp[window_member_tail_def, TAKE_SUC, TAKE1_DROP,
    abi_tuple_tails_append, abi_tuple_tails_def] >>
  Cases_on `is_dynamic (EL k ats)` >> simp[] >> decide_tac
QED

Theorem window_members_inv_phase_advance:
  window_members_inv ctx func infos at ats avs k src dst dp site slot
    sb cap d st en s /\
  window_phase ctx func st mid ids outs s t /\
  ids SUBSET (window_alloca_sites func (frag_ids st en) UNION
    (if EXISTS (\(_,_,_,dyn). dyn) infos then {site} else {})) /\
  EVERY (\(b,n). d <= b /\ b+n <= d+LENGTH (enc at (ListV avs))) outs /\
  st.cs_next_var <= mid.cs_next_var /\ st.cs_next_id <= mid.cs_next_id /\
  fn_has_code mid en func /\
  DISJOINT ids (window_alloca_sites func (frag_ids mid en)) /\
  window_member_prefix infos ats avs j d t.vs_memory /\
  (EXISTS (\(_,_,_,dyn). dyn) infos ==>
    mem_word_at slot t.vs_memory = n2w (window_member_tail infos ats avs j)) ==>
  window_members_inv ctx func infos at ats avs j src dst dp site slot
    sb cap d mid en t
Proof
  strip_tac >>
  `abi_encoder_window_pre ctx func mid en dst src (AbiComplex infos) at
    (ListV avs) sb cap d t` by
    (irule window_member_phase_pre >> metis_tac[]) >>
  `window_member_cursor infos dp site slot sb cap d (LENGTH (enc at (ListV avs))) st s /\
    abi_encoder_tuple_type at ats /\ has_types ats avs /\
    window_member_head_size infos = head_lengths ats 0` by
    fs[window_members_inv_def] >>
  `window_member_cursor infos dp site slot sb cap d (LENGTH (enc at (ListV avs))) mid t` by
    metis_tac[window_member_cursor_phase] >>
  simp_tac bool_ss [window_members_inv_def] >> asm_rewrite_tac[]
QED

Theorem window_members_inv_restrict_end:
  window_members_inv ctx func infos at ats avs k src dst dp site slot
    sb cap d st en s /\ fn_has_code st mid func /\ mid.cs_next_id <= en.cs_next_id ==>
  window_members_inv ctx func infos at ats avs k src dst dp site slot
    sb cap d st mid s
Proof
  pure_rewrite_tac [window_members_inv_def, abi_encoder_window_pre_def] >> strip_tac >>
  asm_rewrite_tac[] >> rpt gen_tac >> strip_tac >>
  `inst.inst_id IN frag_ids st en` by
    (qpat_x_assum `_ IN frag_ids st mid` mp_tac >>
     simp_tac (srw_ss()) [abiEncoderPropsTheory.frag_ids_def] >> decide_tac) >>
  metis_tac[]
QED

Theorem window_members_inv_pure_phase:
  window_members_inv ctx func infos at ats avs k src dst dp site slot
    sb cap d st en s /\ window_phase ctx func st mid {} [] s t /\
  st.cs_next_var <= mid.cs_next_var /\ st.cs_next_id <= mid.cs_next_id /\
  fn_has_code mid en func ==>
  window_members_inv ctx func infos at ats avs k src dst dp site slot
    sb cap d mid en t
Proof
  strip_tac >>
  `!q n. mem_bytes_at q n t.vs_memory = mem_bytes_at q n s.vs_memory` by
    (rpt gen_tac >> irule abi_encoder_window_effect_bytes >>
     qexistsl_tac [`{}`, `[]`] >> simp[] >> metis_tac[window_phase_effect]) >>
  `mem_word_at slot t.vs_memory = mem_word_at slot s.vs_memory` by
    (simp_tac bool_ss [abiStaticAggregatePropsTheory.mem_word_at_bytes] >> asm_rewrite_tac[]) >>
  `window_member_prefix infos ats avs k d t.vs_memory` by
    (asm_rewrite_tac[window_member_prefix_def] >>
     fs[window_members_inv_def, window_member_prefix_def]) >>
  `EXISTS (\(_,_,_,dyn). dyn) infos ==>
    mem_word_at slot t.vs_memory = n2w (window_member_tail infos ats avs k)` by
    (asm_rewrite_tac[] >> fs[window_members_inv_def]) >>
  irule window_members_inv_phase_advance >> asm_rewrite_tac[] >>
  qexistsl_tac [`{}`, `k`, `[]`, `s`, `st`] >> simp[]
QED


Theorem window_members_cons_context:
  compile_abi_encode_complex_elems dst src ((ei,az,ms,dyn)::rest) so ho dp st = (out,en) /\
  fn_has_code st en func ==>
  ?child_src ready len mid.
    emit_op ADD [src;Lit (n2w so)] st = (child_src,ready) /\
    compile_abi_encode_child dst child_src ei dyn ho dp ready = (len,mid) /\
    compile_abi_encode_complex_elems dst src rest (so+ms) (ho+az) dp mid = (out,en) /\
    fn_has_code st ready func /\ fn_has_code ready mid func /\ fn_has_code mid en func /\
    st.cs_next_var <= ready.cs_next_var /\ ready.cs_next_var <= mid.cs_next_var /\
    mid.cs_next_var <= en.cs_next_var /\ st.cs_next_id <= ready.cs_next_id /\
    ready.cs_next_id <= mid.cs_next_id /\ mid.cs_next_id <= en.cs_next_id
Proof
  simp_tac bool_ss [Once abiEncoderTheory.compile_abi_encode_child_def,
    comp_bind_def, comp_ignore_bind_def, LET_THM] >>
  rpt (pairarg_tac >> gvs[]) >> strip_tac >>
  rename1 `emit_op ADD [src;Lit (n2w so)] st = (child_src,ready)` >>
  rename1 `compile_abi_encode_child dst child_src ei dyn ho dp ready = (len,mid)` >>
  `cs_extends st ready` by metis_tac[abiEncoderAddressReachTheory.abi_encoder_emit_address_shape] >>
  `cs_extends ready mid /\ cs_extends mid en` by
    metis_tac[abiEncoderAppendTheory.cs_extends_abi_encode_child,
      cj 3 abiEncoderAppendTheory.cs_appends_abi_encode_mutual,
      fragExecTheory.cs_appends_def] >>
  `fn_has_code st ready func /\ fn_has_code ready mid func /\ fn_has_code mid en func` by
    metis_tac[fragExecTheory.fn_has_code_split, cs_extends_trans] >>
  `ready.cs_next_var <= mid.cs_next_var /\ ready.cs_next_id <= mid.cs_next_id /\
   mid.cs_next_var <= en.cs_next_var /\ mid.cs_next_id <= en.cs_next_id` by
    metis_tac[cj 1 abiEncoderCountersTheory.abi_encoder_counters_mono_mutual,
      cj 3 abiEncoderCountersTheory.abi_encoder_counters_mono_mutual,
      abiEncoderCountersTheory.abi_encoder_counters_mono_def, pairTheory.SND] >>
  asm_rewrite_tac[] >>
  qpat_x_assum `emit_op _ _ _ = _` mp_tac >>
  simp[emitHelperTheory.emit_op_def, comp_bind_def, comp_ignore_bind_def,
    comp_return_def, fresh_var_def, fresh_id_def, emit_def] >>
  rpt (pairarg_tac >> gvs[]) >> strip_tac >> gvs[]
QED

Theorem window_member_static_cursor_frame:
  window_members_inv ctx func infos at ats avs k src dst dp site slot
    sb cap d st en s /\
  window_phase ctx func st mid ids [(q,n)] s t /\
  site NOTIN ids /\ d <= q /\ q+n <= d+LENGTH (enc at (ListV avs)) ==>
  (EXISTS (\(_,_,_,dyn). dyn) infos ==>
    mem_word_at slot t.vs_memory = mem_word_at slot s.vs_memory)
Proof
  strip_tac >> strip_tac >>
  `FLOOKUP s.vs_allocas site = SOME (slot,32) /\
   venomMemDefs$regions_disjoint (d,LENGTH (enc at (ListV avs))) (slot,32)` by
    fs[window_members_inv_def, window_member_cursor_def] >>
  `venomMemDefs$regions_disjoint (slot,32) (q,n)` by
    (qpat_x_assum `venomMemDefs$regions_disjoint _ _` mp_tac >>
     pure_rewrite_tac[venomMemDefsTheory.regions_disjoint_def] >> decide_tac) >>
  `mem_bytes_at slot 32 t.vs_memory = mem_bytes_at slot 32 s.vs_memory` by
    (irule abi_encoder_window_effect_parent >>
     (conj_tac >- metis_tac[window_phase_resources]) >>
     qexistsl_tac [`ids`, `[(q,n)]`, `site`] >> simp[] >>
     metis_tac[window_phase_effect, window_phase_resources]) >>
  simp_tac bool_ss [abiStaticAggregatePropsTheory.mem_word_at_bytes] >> asm_rewrite_tac[]
QED

Theorem window_member_source_prepare:
  window_members_inv ctx func infos at ats avs k src dst dp site slot
    sb cap d st en s /\
  emit_op ADD [src;Lit (n2w so)] st = (child_src,ready) /\
  fn_has_code st ready func /\ fn_has_code ready en func /\
  st.cs_next_var <= ready.cs_next_var /\ st.cs_next_id <= ready.cs_next_id ==>
  ?t. window_phase ctx func st ready {} [] s t /\
    window_members_inv ctx func infos at ats avs k src dst dp site slot
      sb cap d ready en t /\
    eval_operand child_src t = SOME (n2w (sb+so)) /\
    (!x. child_src = Var x ==> not_fresh_at ready x)
Proof
  strip_tac >>
  `eval_operand src s = SOME (n2w sb) /\ alloca_inv s /\ alloca_room ctx func s /\
   ~s.vs_halted /\ s.vs_current_bb = st.cs_current_bb /\
   s.vs_inst_idx = LENGTH st.cs_current_insts` by
    (qpat_assum `window_members_inv _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _` mp_tac >>
     simp_tac bool_ss [window_members_inv_def, abi_encoder_window_pre_def] >> metis_tac[]) >>
  `eval_operand (Lit (n2w so)) s = SOME (n2w so)` by simp[eval_operand_def] >>
  drule_all window_emit_add_phase >> strip_tac >>
  qexists_tac `t` >> asm_rewrite_tac[] >>
  (conj_tac >- metis_tac[window_members_inv_pure_phase]) >>
  fs[wordsTheory.word_add_n2w]
QED

Theorem window_member_static_step_run:
  window_members_inv ctx func infos at ats avs k src dst dp site slot
    sb cap d st en s /\ k < LENGTH infos /\
  EL k infos = (ei,az,ms,F) /\ abi_encoder_admissible ei /\ window_strong_contract ei /\
  compile_abi_encode_child dst child_src ei F
    (SUM (MAP abi_member_head_size (TAKE k ats))) dp st = (out,mid) /\
  eval_operand child_src s = SOME (n2w (sb+abi_encoder_member_span (TAKE k infos))) /\
  (!x. child_src = Var x ==> not_fresh_at st x) /\
  fn_has_code st mid func /\ fn_has_code mid en func /\
  st.cs_next_var <= mid.cs_next_var /\ st.cs_next_id <= mid.cs_next_id /\
  mid.cs_next_id <= en.cs_next_id /\
  (EXISTS (\(_,_,_,dyn). dyn) infos ==>
    site NOTIN window_alloca_sites func (frag_ids st mid)) /\
  window_alloca_sites func (frag_ids st mid) SUBSET window_alloca_sites func (frag_ids st en) /\
  DISJOINT (window_alloca_sites func (frag_ids st mid))
    (window_alloca_sites func (frag_ids mid en)) ==>
  ?t. window_phase ctx func st mid (window_alloca_sites func (frag_ids st mid))
        [(d+SUM (MAP abi_member_head_size (TAKE k ats)),
          LENGTH (enc (EL k ats) (EL k avs)))] s t /\
      window_members_inv ctx func infos at ats avs (SUC k) src dst dp site slot
        sb cap d mid en t
Proof
  strip_tac >>
  `window_members_inv ctx func infos at ats avs k src dst dp site slot
    sb cap d st mid s` by metis_tac[window_members_inv_restrict_end] >>
  drule_all window_member_static_run >> strip_tac >>
  drule_all window_members_inv_total_bounds >> strip_tac >>
  `SUM (MAP abi_member_head_size (TAKE k ats)) +
   LENGTH (enc (EL k ats) (EL k avs)) <= LENGTH (enc at (ListV avs))` by
    (drule_all window_members_inv_output_bounds >> strip_tac >>
     `~is_dynamic (EL k ats)` by metis_tac[window_members_inv_source] >> gvs[] >> decide_tac) >>
  `EXISTS (\(_,_,_,dyn). dyn) infos ==>
    mem_word_at slot t.vs_memory = n2w (window_member_tail infos ats avs (SUC k))` by
    (strip_tac >>
     `site NOTIN window_alloca_sites func (frag_ids st mid)` by metis_tac[] >>
     `d <= d+SUM (MAP abi_member_head_size (TAKE k ats)) /\
      (d+SUM (MAP abi_member_head_size (TAKE k ats))) +
        LENGTH (enc (EL k ats) (EL k avs)) <= d+LENGTH (enc at (ListV avs))` by decide_tac >>
     `mem_word_at slot t.vs_memory = mem_word_at slot s.vs_memory` by
       (drule_all window_member_static_cursor_frame >> simp[]) >>
     `~is_dynamic (EL k ats)` by metis_tac[window_members_inv_source] >>
     `LENGTH ats = LENGTH avs /\ k < LENGTH ats` by
       fs[window_members_inv_def, window_member_prefix_def] >>
     drule_all window_member_tail_step >>
     fs[window_members_inv_def]) >>
  qexists_tac `t` >> asm_rewrite_tac[] >>
  irule window_members_inv_phase_advance >> asm_rewrite_tac[] >>
  qexistsl_tac [`window_alloca_sites func (frag_ids st mid)`, `k`,
    `[(d+SUM (MAP abi_member_head_size (TAKE k ats)),
       LENGTH (enc (EL k ats) (EL k avs)))]`, `s`, `st`] >>
  simp[] >> metis_tac[SUBSET_UNION, SUBSET_TRANS]
QED

Theorem window_member_dynamic_step_run:
  window_members_inv ctx func infos at ats avs k src dst dp site slot
    sb cap d st en s /\ k < LENGTH infos /\
  EL k infos = (ei,az,ms,T) /\ abi_encoder_admissible ei /\ window_strong_contract ei /\
  compile_abi_encode_child dst child_src ei T
    (SUM (MAP abi_member_head_size (TAKE k ats))) dp st = (out,mid) /\
  eval_operand child_src s = SOME (n2w (sb+abi_encoder_member_span (TAKE k infos))) /\
  (!x. child_src = Var x ==> not_fresh_at st x) /\
  fn_has_code st mid func /\ fn_has_code mid en func /\
  st.cs_next_var <= mid.cs_next_var /\ st.cs_next_id <= mid.cs_next_id /\
  mid.cs_next_id <= en.cs_next_id /\
  (window_alloca_sites func (frag_ids st mid) UNION {site}) SUBSET
    (window_alloca_sites func (frag_ids st en) UNION {site}) /\
  DISJOINT (window_alloca_sites func (frag_ids st mid) UNION {site})
    (window_alloca_sites func (frag_ids mid en)) ==>
  ?t. window_phase ctx func st mid (window_alloca_sites func (frag_ids st mid) UNION {site})
        [(d+SUM (MAP abi_member_head_size (TAKE k ats)),32);
         (d+window_member_tail infos ats avs k,LENGTH (enc (EL k ats) (EL k avs)))] s t /\
      window_members_inv ctx func infos at ats avs (SUC k) src dst dp site slot
        sb cap d mid en t
Proof
  strip_tac >>
  `window_members_inv ctx func infos at ats avs k src dst dp site slot
    sb cap d st mid s` by metis_tac[window_members_inv_restrict_end] >>
  drule_all window_member_dynamic_run >> strip_tac >>
  drule_all window_members_inv_output_bounds >> strip_tac >>
  drule_all window_members_inv_total_bounds >> strip_tac >>
  `is_dynamic (EL k ats)` by metis_tac[window_members_inv_source] >>
  `EXISTS (\(_,_,_,dyn). dyn) infos` by
    (simp[EXISTS_MEM] >> qexists_tac `(ei,az,ms,T)` >> simp[] >> metis_tac[MEM_EL]) >>
  `LENGTH ats = LENGTH avs /\ k < LENGTH ats` by
    (qpat_assum `window_member_prefix _ _ _ (SUC k) _ _` mp_tac >>
     simp_tac bool_ss [window_member_prefix_def] >> strip_tac >> decide_tac) >>
  `mem_word_at slot t.vs_memory = n2w (window_member_tail infos ats avs (SUC k))` by
    (drule_all window_member_tail_step >> disch_then (qspec_then `infos` mp_tac) >>
     asm_rewrite_tac[] >> disch_then SUBST1_TAC >> asm_rewrite_tac[]) >>
  qexists_tac `t` >> asm_rewrite_tac[] >>
  irule window_members_inv_phase_advance >> asm_rewrite_tac[] >>
  qexistsl_tac [`window_alloca_sites func (frag_ids st mid) UNION {site}`, `k`,
    `[(d+SUM (MAP abi_member_head_size (TAKE k ats)),32);
      (d+window_member_tail infos ats avs k,LENGTH (enc (EL k ats) (EL k avs)))]`, `s`, `st`] >>
  asm_rewrite_tac[] >>
  simp_tac (srw_ss()) [NoAsms, listTheory.EVERY_DEF] >>
  qpat_x_assum `is_dynamic _ ==> _` drule >> strip_tac >> decide_tac
QED

Theorem window_member_site_split:
  st.cs_next_id <= mid.cs_next_id /\ mid.cs_next_id <= en.cs_next_id ==>
  window_alloca_sites func (frag_ids st mid) SUBSET window_alloca_sites func (frag_ids st en) /\
  DISJOINT (window_alloca_sites func (frag_ids st mid))
    (window_alloca_sites func (frag_ids mid en)) /\
  (site < st.cs_next_id ==>
    site NOTIN window_alloca_sites func (frag_ids st mid) /\
    DISJOINT (window_alloca_sites func (frag_ids st mid) UNION {site})
      (window_alloca_sites func (frag_ids mid en)))
Proof
  simp_tac (srw_ss()) [window_alloca_sites_def, abiEncoderPropsTheory.frag_ids_def,
    SUBSET_DEF, DISJOINT_DEF, EXTENSION] >> rpt strip_tac >>
  spose_not_then strip_assume_tac >> decide_tac
QED

Theorem window_member_drop_cons[local]:
  !l n h rest. DROP n l = h::rest ==>
    n < LENGTH l /\ EL n l = h /\ DROP (SUC n) l = rest
Proof
  Induct >> rw[] >> Cases_on `n` >> gvs[] >>
  first_x_assum drule >> simp[]
QED

Theorem window_member_envelope_frame:
  EVERY (\(b,n). d <= b /\ b+n <= d+len) outs ==>
  !a. EVERY (\(b,n). a < b \/ b+n <= a) [(d,len)] ==>
      EVERY (\(b,n). a < b \/ b+n <= a) outs
Proof
  simp_tac (srw_ss()) [EVERY_MEM] >> strip_tac >>
  rpt gen_tac >> strip_tac >> qx_gen_tac `r` >> strip_tac >>
  Cases_on `r` >> first_x_assum drule >> simp[] >> decide_tac
QED

Theorem window_members_cons_run:
  window_members_inv ctx func infos at ats avs k src dst dp site slot
    sb cap d st en s /\ DROP k infos = (h0,h1,h2,h3)::rest /\
  window_strong_contract h0 /\
  compile_abi_encode_complex_elems dst src ((h0,h1,h2,h3)::rest)
    (abi_encoder_member_span (TAKE k infos))
    (SUM (MAP abi_member_head_size (TAKE k ats))) dp st = (out,en) ==>
  ?mid u. window_members_inv ctx func infos at ats avs (SUC k) src dst dp site slot
      sb cap d mid en u /\ DROP (SUC k) infos = rest /\
    compile_abi_encode_complex_elems dst src rest
      (abi_encoder_member_span (TAKE (SUC k) infos))
      (SUM (MAP abi_member_head_size (TAKE (SUC k) ats))) dp mid = (out,en) /\
    window_phase ctx func st mid
      (window_alloca_sites func (frag_ids st en) UNION
        (if EXISTS (\(_,_,_,dyn). dyn) infos then {site} else {}))
      [(d,LENGTH (enc at (ListV avs)))] s u /\
    st.cs_next_var <= mid.cs_next_var /\
    window_alloca_sites func (frag_ids mid en) SUBSET window_alloca_sites func (frag_ids st en)
Proof
  strip_tac >>
  `fn_has_code st en func` by
    (qpat_assum `window_members_inv _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _` mp_tac >>
     simp_tac bool_ss [window_members_inv_def, abi_encoder_window_pre_def] >> metis_tac[]) >>
  drule_all window_members_cons_context >> strip_tac >>
  `cs_extends ready mid /\ cs_extends mid en` by
    metis_tac[abiEncoderAppendTheory.cs_extends_abi_encode_child,
      cj 3 abiEncoderAppendTheory.cs_appends_abi_encode_mutual, fragExecTheory.cs_appends_def] >>
  `cs_extends st ready` by metis_tac[abiEncoderAddressReachTheory.abi_encoder_emit_address_shape] >>
  `fn_has_code ready en func` by metis_tac[fragExecTheory.fn_has_code_split, cs_extends_trans] >>
  drule_all window_member_source_prepare >> strip_tac >>
  `k < LENGTH infos /\ EL k infos = (h0,h1,h2,h3) /\ DROP (SUC k) infos = rest` by
    metis_tac[window_member_drop_cons] >>
  qpat_x_assum `compile_abi_encode_complex_elems _ _ (_::_) _ _ _ _ = _` kall_tac >>
  `abi_encoder_admissible h0` by
    (`abi_encoder_admissible (AbiComplex infos)` by
       (qpat_assum `window_members_inv _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _` mp_tac >>
        simp_tac bool_ss [window_members_inv_def, abi_encoder_window_pre_def] >> metis_tac[]) >>
     qpat_x_assum `abi_encoder_admissible (AbiComplex infos)` mp_tac >>
     simp_tac bool_ss [abiEncoderAdmissibleTheory.abi_encoder_admissible_def,
       abiEncoderAdmissibleTheory.abi_encoder_members_admissible_every] >>
     simp_tac (srw_ss()) [EVERY_MEM] >>
     disch_then (qspec_then `(h0,h1,h2,h3)` mp_tac) >> simp[] >> metis_tac[MEM_EL]) >>
  `EXISTS (\(_,_,_,dyn). dyn) infos ==> site < ready.cs_next_id` by
    (qpat_assum `window_members_inv _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _` mp_tac >>
     simp_tac bool_ss [window_members_inv_def, window_member_cursor_def] >> metis_tac[]) >>
  `window_alloca_sites func (frag_ids ready mid) SUBSET window_alloca_sites func (frag_ids ready en) /\
   DISJOINT (window_alloca_sites func (frag_ids ready mid)) (window_alloca_sites func (frag_ids mid en)) /\
   (EXISTS (\(_,_,_,dyn). dyn) infos ==>
     site NOTIN window_alloca_sites func (frag_ids ready mid) /\
     DISJOINT (window_alloca_sites func (frag_ids ready mid) UNION {site})
       (window_alloca_sites func (frag_ids mid en)))` by
    metis_tac[window_member_site_split] >>
  qpat_x_assum `window_members_inv _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ st en s` kall_tac >>
  qpat_x_assum `cs_extends ready mid` kall_tac >>
  qpat_x_assum `cs_extends mid en` kall_tac >>
  qpat_x_assum `cs_extends st ready` kall_tac >>
  `?u ids outs. window_members_inv ctx func infos at ats avs (SUC k) src dst dp site slot
      sb cap d mid en u /\ window_phase ctx func ready mid ids outs t u /\
    ids SUBSET (window_alloca_sites func (frag_ids ready en) UNION
      (if EXISTS (\(_,_,_,dyn). dyn) infos then {site} else {})) /\
    EVERY (\(b,n). d <= b /\ b+n <= d+LENGTH (enc at (ListV avs))) outs` by
    (reverse (Cases_on `h3`)
     >- ( `EXISTS (\(_,_,_,dyn). dyn) infos ==> site NOTIN window_alloca_sites func (frag_ids ready mid)` by metis_tac[] >>
          drule_all window_member_static_step_run >> strip_tac >>
          qexistsl_tac [`t'`, `window_alloca_sites func (frag_ids ready mid)`,
            `[(d+SUM (MAP abi_member_head_size (TAKE k ats)),LENGTH (enc (EL k ats) (EL k avs)))]`] >>
          asm_rewrite_tac[] >>
          (conj_tac >- metis_tac[SUBSET_UNION, SUBSET_TRANS]) >>
          drule_all window_members_inv_output_bounds >> strip_tac >>
          drule_all window_members_inv_total_bounds >> strip_tac >>
          `~is_dynamic (EL k ats)` by metis_tac[window_members_inv_source] >>
          simp_tac (srw_ss()) [NoAsms, EVERY_DEF] >>
          qpat_x_assum `~is_dynamic _ ==> _` drule >> decide_tac) >>
     `EXISTS (\(_,_,_,dyn). dyn) infos` by
       (simp[EXISTS_MEM] >> qexists_tac `(h0,h1,h2,T)` >> simp[] >> metis_tac[MEM_EL]) >>
     `(window_alloca_sites func (frag_ids ready mid) UNION {site}) SUBSET
        (window_alloca_sites func (frag_ids ready en) UNION {site}) /\
      DISJOINT (window_alloca_sites func (frag_ids ready mid) UNION {site})
        (window_alloca_sites func (frag_ids mid en))` by
       metis_tac[SUBSET_UNION, SUBSET_TRANS, pred_setTheory.UNION_SUBSET] >>
     drule_all window_member_dynamic_step_run >> strip_tac >>
     qexistsl_tac [`t'`, `window_alloca_sites func (frag_ids ready mid) UNION {site}`,
       `[(d+SUM (MAP abi_member_head_size (TAKE k ats)),32);
         (d+window_member_tail infos ats avs k,LENGTH (enc (EL k ats) (EL k avs)))]`] >>
     asm_rewrite_tac[] >>
     drule_all window_members_inv_output_bounds >> strip_tac >>
     drule_all window_members_inv_total_bounds >> strip_tac >>
     `is_dynamic (EL k ats)` by metis_tac[window_members_inv_source] >>
     simp_tac (srw_ss()) [NoAsms, EVERY_DEF] >>
     qpat_x_assum `is_dynamic _ ==> _` drule >> strip_tac >> decide_tac) >>
  `h1 = abi_member_head_size (EL k ats) /\ k < LENGTH ats` by
    (drule_all window_members_inv_source >> strip_tac >>
     qpat_assum `window_members_inv _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _` mp_tac >>
     simp_tac bool_ss [window_members_inv_def, window_member_prefix_def] >> metis_tac[]) >>
  `abi_encoder_member_span (TAKE (SUC k) infos) = abi_encoder_member_span (TAKE k infos) + h2 /\
   SUM (MAP abi_member_head_size (TAKE (SUC k) ats)) =
     SUM (MAP abi_member_head_size (TAKE k ats)) + h1` by
    simp[TAKE_SUC, TAKE1_DROP, abiEncoderInputTheory.abi_encoder_member_span_def,
      MAP_APPEND, SUM_APPEND] >>
  `window_alloca_sites func (frag_ids ready en) SUBSET window_alloca_sites func (frag_ids st en) /\
   window_alloca_sites func (frag_ids mid en) SUBSET window_alloca_sites func (frag_ids st en)` by
    (simp_tac (srw_ss()) [window_alloca_sites_def, abiEncoderPropsTheory.frag_ids_def,
       SUBSET_DEF] >> rpt strip_tac >> decide_tac) >>
  qexistsl_tac [`mid`, `u`] >> asm_rewrite_tac[] >>
  (conj_tac >- metis_tac[]) >>
  reverse conj_tac >- decide_tac >>
  irule window_phase_chain >>
  qexistsl_tac [`{}`, `[]`, `ready`, `ids`, `outs`, `t`] >>
  simp_tac (srw_ss()) [NoAsms, EMPTY_SUBSET, EVERY_DEF] >>
  asm_rewrite_tac[] >>
  (conj_tac >-
    (drule window_member_envelope_frame >>
     simp_tac (srw_ss()) [NoAsms, EVERY_DEF])) >>
  qpat_x_assum `ids SUBSET _` mp_tac >>
  qpat_x_assum `window_alloca_sites func (frag_ids ready en) SUBSET _` mp_tac >>
  simp_tac (srw_ss()) [SUBSET_DEF] >> metis_tac[]
QED

Theorem window_members_remaining_run:
  !rest ctx func infos at ats avs k src dst dp site slot sb cap d st en s out.
  window_members_inv ctx func infos at ats avs k src dst dp site slot
    sb cap d st en s /\ DROP k infos = rest /\
  (!ei az ms dyn. MEM (ei,az,ms,dyn) rest ==> window_strong_contract ei) /\
  compile_abi_encode_complex_elems dst src rest
    (abi_encoder_member_span (TAKE k infos))
    (SUM (MAP abi_member_head_size (TAKE k ats))) dp st = (out,en) ==>
  ?t. window_phase ctx func st en
        (window_alloca_sites func (frag_ids st en) UNION
          (if EXISTS (\(_,_,_,dyn). dyn) infos then {site} else {}))
        [(d,LENGTH (enc at (ListV avs)))] s t /\
      window_members_inv ctx func infos at ats avs (LENGTH infos) src dst dp site slot
        sb cap d en en t
Proof
  Induct_on `rest`
  >- (rpt gen_tac >>
      simp_tac bool_ss [Once abiEncoderTheory.compile_abi_encode_child_def,
        comp_return_def, pairTheory.PAIR_EQ] >> strip_tac >>
      `k = LENGTH infos` by
        (qpat_assum `window_members_inv _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _` mp_tac >>
         simp_tac bool_ss [window_members_inv_def, window_member_prefix_def] >>
         strip_tac >> fs[DROP_EQ_NIL] >> decide_tac) >>
      gvs[] >> qexists_tac `s` >> asm_rewrite_tac[] >>
      irule window_phase_refl >>
      qpat_assum `window_members_inv _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _` mp_tac >>
      simp_tac bool_ss [window_members_inv_def, abi_encoder_window_pre_def] >> metis_tac[]) >>
  rpt gen_tac >> strip_tac >> PairCases_on `h` >>
  `window_strong_contract h0` by metis_tac[MEM] >>
  drule_all window_members_cons_run >> strip_tac >>
  `!ei az ms dyn. MEM (ei,az,ms,dyn) rest ==> window_strong_contract ei` by metis_tac[MEM] >>
  first_x_assum drule_all >> strip_tac >>
  qexists_tac `t` >> asm_rewrite_tac[] >>
  irule window_phase_chain >>
  qexistsl_tac [`window_alloca_sites func (frag_ids st en) UNION
      (if EXISTS (\(_,_,_,dyn). dyn) infos then {site} else {})`,
    `[(d,LENGTH (enc at (ListV avs)))]`, `mid`,
    `window_alloca_sites func (frag_ids mid en) UNION
      (if EXISTS (\(_,_,_,dyn). dyn) infos then {site} else {})`,
    `[(d,LENGTH (enc at (ListV avs)))]`, `u`] >>
  asm_rewrite_tac[] >>
  qpat_x_assum `window_alloca_sites func (frag_ids mid en) SUBSET _` mp_tac >>
  simp_tac (srw_ss()) [SUBSET_DEF] >> metis_tac[]
QED
