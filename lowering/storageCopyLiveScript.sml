(*
 * Storing a value from memory into storage by copying its words.
 *
 * The lowering stores a non-word value held in memory by copying its
 * memory words, one per slot, over the whole of its storage region
 * (compile_memory_to_storage).  The source writes only the slots of its
 * encoding (encode_value): a bytestring's length and used data slots, a
 * DynArray's length and present elements.  The words differ only where
 * the stored value leaves bytes dead (dead_bytes), so the storages agree up
 * to the dead bytes afterwards.
 *
 * Main theorems:
 *   encode_value_memory_live    — a byte of the stored value's region that
 *                                 is not dead holds the matching byte of its
 *                                 memory words
 *   storage_agree_copy_region   — copying a declared region's memory words
 *                                 keeps the storages agreeing
 *)

Theory storageCopyLive
Ancestors
  valueEncodingProps
  list rich_list arithmetic words byte vfmTypes vfmState valueEncodingProofs
  compileEnv loweringStateRelDefs valueEncoding valueEncodingDefs accountsRelProps exprSimAttributeFields
  vyperStorageLayoutSafety vyperStorageFrame
  vyperEncodeDecode vyperTyping vyperStorage vyperValue storageDecodeMemory

(* ===== Memory and primitive encoding boundaries ===== *)

Theorem copy_mem_payload_byte[local]:
  !p len mem bs q r b.
    mem_bytes_at p len mem = bs /\ q = r + b /\
    q < len /\ b < 32 ==>
    EL b (word_to_bytes (mem_word_at (p + r) mem) T) = EL q bs
Proof
  rpt strip_tac >>
  pure_rewrite_tac[GSYM mem_bytes_at_word] >>
  qpat_x_assum `_ = bs` (SUBST1_TAC o SYM) >>
  asm_simp_tac bool_ss [EL_mem_bytes_at] >>
  qpat_x_assum `q = _` SUBST_ALL_TAC >>
  rewrite_tac[ADD_ASSOC]
QED

Theorem copy_primitive_memory_word[local]:
  !tv v off mem w.
    ( (?bt. tv = BaseTV bt) \/ (?n. tv = FlagTV n)) /\
    encode_base_to_slot v tv = SOME w /\ val_in_memory tv v off mem ==>
    mem_word_at off mem = w
Proof
  rpt gen_tac >> strip_tac
  >- (gvs[] >> Cases_on `bt` >> Cases_on `v` >>
      gvs[encode_base_to_slot_def, val_in_memory_def,
          typed_val_to_w256_def, val_to_w256_def, bool_to_slot_def,
          word_of_bytes_be_pad_right, AllCaseEqs()] >>
      rename1 `BytesT bd` >> Cases_on `bd` >>
      gvs[encode_base_to_slot_def, val_in_memory_def,
          typed_val_to_w256_def, word_of_bytes_be_pad_right, AllCaseEqs()])
  >> gvs[] >> Cases_on `v` >>
  gvs[encode_base_to_slot_def, val_in_memory_def, val_to_w256_def]
QED

(* ===== Storage interval boundaries ===== *)

Theorem copy_writes_frame[local]:
  !writes k st a s x.
    a <= x /\ x < a + s /\ a + s <= dimword (:256) /\
    (!i. MEM i (MAP FST writes) ==>
         w2n k + i < dimword (:256) /\
         ~(a <= w2n k + i /\ w2n k + i < a + s)) ==>
    lookup_storage (n2w x) (apply_writes k writes st) =
    lookup_storage (n2w x) st
Proof
  Induct >> simp[apply_writes_def] >>
  Cases >> simp[apply_writes_def] >> rpt strip_tac >>
  rename1 `update_storage (n2w (h + w2n k)) w st` >>
  `lookup_storage (n2w x)
     (apply_writes k writes (update_storage (n2w (h + w2n k)) w st)) =
   lookup_storage (n2w x) (update_storage (n2w (h + w2n k)) w st)` by
    (first_x_assum irule >> qexistsl_tac [`a`, `s`] >>
     simp[] >> metis_tac[ADD_COMM]) >>
  pop_assum SUBST1_TAC >>
  first_x_assum (qspec_then `h` mp_tac) >> simp[] >> strip_tac >>
  `x < dimword (:256)` by decide_tac >>
  `x <> h + w2n k` by decide_tac >>
  simp[lookup_storage_def, update_storage_def, combinTheory.APPLY_UPDATE_THM,
       n2w_11, LESS_MOD]
QED

Theorem copy_zero_writes_lookup[local]:
  !is k st x.
    lookup_storage x (apply_writes k (MAP (\i. (i, 0w)) is) st) =
    if MEM x (MAP (\i. n2w (w2n k + i)) is) then 0w
    else lookup_storage x st
Proof
  Induct >> simp[apply_writes_def] >>
  rpt gen_tac >>
  simp[lookup_storage_def, update_storage_def, combinTheory.APPLY_UPDATE_THM] >>
  metis_tac[]
QED

Theorem copy_zero_interval[local]:
  !k n st j.
    j < n ==>
    lookup_storage (n2w (w2n k + j))
      (apply_writes k (GENLIST (\i. (i, 0w)) n) st) = 0w
Proof
  rpt strip_tac >>
  `GENLIST (\i. (i, 0w : bytes32)) n =
   MAP (\i. (i, 0w)) (COUNT_LIST n)` by
    simp[COUNT_LIST_GENLIST, MAP_GENLIST, combinTheory.o_DEF] >>
  pop_assum SUBST1_TAC >> simp[copy_zero_writes_lookup] >>
  `MEM (n2w (w2n k + j) : bytes32)
       (MAP (\i. n2w (w2n k + i)) (COUNT_LIST n))` by
    (simp[MEM_MAP] >> qexists_tac `j` >> simp[MEM_COUNT_LIST]) >>
  fs[ADD_COMM]
QED

Theorem copy_selected_writes[local]:
  !pre child post k st d s x.
    w2n k + d <= x /\ x < w2n k + d + s /\
    w2n k + d + s <= dimword (:256) /\
    (!i. MEM i (MAP FST post) ==>
         w2n k + i < dimword (:256) /\
         ~(w2n k + d <= w2n k + i /\
           w2n k + i < w2n k + d + s)) ==>
    lookup_storage (n2w x)
      (apply_writes k
        (pre ++ MAP (\(i,w). (i + d,w)) child ++ post) st) =
    lookup_storage (n2w x)
      (apply_writes (n2w (w2n k + d)) child (apply_writes k pre st))
Proof
  rpt strip_tac >>
  rewrite_tac[apply_writes_append] >>
  `lookup_storage (n2w x)
    (apply_writes k post
      (apply_writes k (MAP (\(i,w). (i + d,w)) child)
        (apply_writes k pre st))) =
   lookup_storage (n2w x)
      (apply_writes k (MAP (\(i,w). (i + d,w)) child)
        (apply_writes k pre st))` by
    (irule copy_writes_frame >> qexistsl_tac [`w2n k + d`, `s`] >>
     asm_simp_tac bool_ss [] >> metis_tac[]) >>
  pop_assum SUBST1_TAC >>
  qspec_then `child` (qspec_then `d` mp_tac) apply_writes_shift >>
  disch_then (qspec_then `w2n k` mp_tac) >> simp[]
QED

(* ===== Dynamic byte chunks ===== *)

Theorem copy_slots_acc_prefix[local]:
  !acc bs. !prefix.
    bytes_to_slots_aux (acc ++ prefix) bs =
    REVERSE prefix ++ bytes_to_slots_aux acc bs
Proof
  ho_match_mp_tac bytes_to_slots_aux_ind >> conj_tac
  >- simp[bytes_to_slots_aux_def, REVERSE_APPEND] >>
  rpt strip_tac >>
  once_rewrite_tac [bytes_to_slots_aux_def] >>
  simp_tac bool_ss [LET_THM, GSYM APPEND] >>
  first_x_assum irule >> simp[]
QED

Theorem copy_slots_cons[local]:
  !h t.
    bytes_to_slots (h::t) =
    word_of_bytes_be
      (TAKE 32 (h::t) ++ REPLICATE (32 - LENGTH (TAKE 32 (h::t))) 0w) ::
    bytes_to_slots (DROP 32 (h::t))
Proof
  rpt gen_tac >> rewrite_tac[bytes_to_slots_def] >>
  once_rewrite_tac [bytes_to_slots_aux_def] >>
  simp_tac bool_ss [LET_THM] >>
  qmatch_goalsub_abbrev_tac `bytes_to_slots_aux [w] rest` >>
  qspecl_then [`[]`, `rest`, `[w]`] mp_tac copy_slots_acc_prefix >> simp[]
QED

Theorem copy_chunk_word[local]:
  !bs. word_of_bytes_be
    (TAKE 32 bs ++ REPLICATE (32 - LENGTH (TAKE 32 bs)) 0w) =
    mem_word_at 0 bs
Proof
  gen_tac >> simp[mem_word_at_def, word_of_bytes_be_def] >>
  AP_TERM_TAC >>
  Cases_on `32 <= LENGTH bs`
  >- simp[TAKE_APPEND1] >>
  `LENGTH bs < 32` by decide_tac >>
  simp[TAKE_LENGTH_TOO_LONG, TAKE_APPEND] >>
  irule LIST_EQ >> simp[LENGTH_TAKE_EQ] >>
  rpt strip_tac >> simp[EL_TAKE, EL_REPLICATE]
QED

Theorem copy_slots_index[local]:
  !bs i. 32 * i < LENGTH bs ==>
    i < LENGTH (bytes_to_slots bs) /\
    EL i (bytes_to_slots bs) = mem_word_at (32 * i) bs
Proof
  measureInduct_on `LENGTH bs` >> rpt gen_tac >> strip_tac >>
  Cases_on `bs` >- gvs[] >>
  rewrite_tac[copy_slots_cons, copy_chunk_word] >>
  Cases_on `i`
  >- simp[] >>
  rename1 `32 * SUC n < LENGTH (h::t)` >>
  `32 * n < LENGTH (DROP 32 (h::t))` by
    (fs[LENGTH_DROP, MULT_SUC] >> decide_tac) >>
  `LENGTH (DROP 32 (h::t)) < LENGTH (h::t)` by simp[] >>
  first_x_assum drule >> disch_then (qspec_then `n` mp_tac) >>
  asm_simp_tac bool_ss [] >> strip_tac >>
  asm_simp_tac bool_ss [LENGTH, EL, TL, prim_recTheory.LESS_MONO_EQ] >>
  pure_rewrite_tac[mem_word_at_def, DROP_DROP_T, MULT_SUC] >>
  simp_tac bool_ss [ADD_COMM]
QED

Theorem copy_lookup_update[local]:
  !a c x st.
    lookup_storage a (update_storage c x st) =
    if a = c then x else lookup_storage a st
Proof
  simp[lookup_storage_def, update_storage_def, combinTheory.APPLY_UPDATE_THM,
       EQ_SYM_EQ]
QED

Theorem copy_writes_preserve_word[local]:
  !writes k st addr w.
    lookup_storage addr st = w /\
    (!i v. MEM (i,v) writes /\ n2w (w2n k + i) = addr ==> v = w) ==>
    lookup_storage addr (apply_writes k writes st) = w
Proof
  Induct >- simp[apply_writes_def] >>
  Cases >> rename1 `(j,wj)::writes` >> rpt gen_tac >> strip_tac >>
  simp_tac bool_ss [apply_writes_def, LET_THM] >>
  qpat_x_assum `!k st addr w. _` irule >> conj_tac
  >- metis_tac[MEM] >>
  pure_rewrite_tac[copy_lookup_update] >>
  Cases_on `addr = n2w (w2n k + j)` >>
  asm_rewrite_tac[] >> metis_tac[MEM]
QED

Theorem copy_writes_hit[local]:
  !writes k st addr w.
    (?i. MEM (i,w) writes /\ n2w (w2n k + i) = addr) /\
    (!i v. MEM (i,v) writes /\ n2w (w2n k + i) = addr ==> v = w) ==>
    lookup_storage addr (apply_writes k writes st) = w
Proof
  rpt gen_tac >> strip_tac >>
  drule (iffLR MEM_SPLIT) >> strip_tac >>
  qpat_x_assum `writes = _` SUBST_ALL_TAC >>
  qpat_x_assum `_ = addr` (SUBST_ALL_TAC o SYM) >>
  simp_tac bool_ss [apply_writes_append, apply_writes_def, LET_THM] >>
  irule copy_writes_preserve_word >> conj_tac
  >- metis_tac[MEM_APPEND, MEM] >>
  pure_rewrite_tac[copy_lookup_update] >> metis_tac[]
QED

Theorem copy_dyn_lookup[local]:
  !ws k st j hd.
    w2n k + (LENGTH ws + 1) <= dimword (:256) /\
    j < LENGTH ws + 1 ==>
    lookup_storage (n2w (w2n k + j))
      (apply_writes k ((0, hd) ::
        MAPi (\i w. (i + 1,w)) ws) st) =
    if j = 0 then hd else EL (j - 1) ws
Proof
  rpt strip_tac >> match_mp_tac copy_writes_hit >> conj_tac
  >- (Cases_on `j = 0`
      >- (qexists_tac `0` >> asm_simp_tac bool_ss [MEM]) >>
      qexists_tac `j` >> simp_tac bool_ss [MEM, indexedListsTheory.MEM_MAPi] >>
      disj2_tac >> qexists_tac `j - 1` >> simp[]) >>
  rpt gen_tac >> simp_tac bool_ss [MEM, indexedListsTheory.MEM_MAPi] >>
  strip_tac
  >- (gvs[] >>
      `w2n k + j < dimword (:256)` by decide_tac >>
      fs[n2w_11, LESS_MOD] >> gvs[]) >>
  rename1 `ix < LENGTH ws` >>
  gvs[pairTheory.PAIR_EQ] >>
  `w2n k + (ix + 1) < dimword (:256) /\
   w2n k + j < dimword (:256)` by decide_tac >>
  fs[n2w_11, LESS_MOD] >>
  `ix = j - 1` by decide_tac >> simp[]
QED

Theorem copy_dyn_length_bound[local]:
  !ws hd sz.
    (!i. MEM i (MAP FST ((0,hd)::MAPi (\i w. (i+1,w)) ws)) ==> i < sz) ==>
    LENGTH ws + 1 <= sz
Proof
  rpt strip_tac >>
  `MEM (LENGTH ws)
     (MAP FST ((0,hd)::MAPi (\i w. (i+1,w)) ws))` by
    (Cases_on `ws = []` >- simp[] >>
     simp_tac bool_ss [MAP, MEM, MEM_MAP] >>
     qexists_tac `(LENGTH ws, EL (LENGTH ws - 1) ws)` >>
     simp_tac bool_ss [pairTheory.FST, indexedListsTheory.MEM_MAPi] >>
     disj2_tac >>
     qexists_tac `LENGTH ws - 1` >>
     `0 < LENGTH ws` by (Cases_on `ws` >> fs[]) >> simp[]) >>
  first_x_assum drule >> decide_tac
QED

Theorem copy_mem_payload_byte_at[local]:
  !mem bs addr b p r.
    mem_bytes_at p (LENGTH bs) mem = bs /\ addr = p + r /\
    r + b < LENGTH bs /\ b < 32 ==>
    EL b (word_to_bytes (mem_word_at addr mem) T) = EL (r+b) bs
Proof
  rpt strip_tac >> qpat_x_assum `addr = _` SUBST1_TAC >>
  irule copy_mem_payload_byte >> simp[] >> qexists_tac `LENGTH bs` >> simp[]
QED

Theorem copy_dyn_live[local]:
  !bs max off mem k st j b.
    LENGTH bs < dimword (:256) /\
    w2n k + (LENGTH (bytes_to_slots bs) + 1) <= dimword (:256) /\
    mem_word_at off mem = n2w (LENGTH bs) /\
    mem_bytes_at (off + 32) (LENGTH bs) mem = bs /\
    j < 1 + vfmConstants$word_size max /\ b < 32 /\
    ~dyn_bytes_dead
      (apply_writes k ((0,n2w (LENGTH bs)) ::
        MAPi (\i w. (i+1,w)) (bytes_to_slots bs)) st)
      (w2n k) max (w2n k + j) b ==>
    EL b (word_to_bytes
      (lookup_storage (n2w (w2n k + j))
        (apply_writes k ((0,n2w (LENGTH bs)) ::
          MAPi (\i w. (i+1,w)) (bytes_to_slots bs)) st)) T) =
    EL b (word_to_bytes (mem_word_at (off + 32*j) mem) T)
Proof
  rpt strip_tac >>
  `lookup_storage (n2w (w2n k))
    (apply_writes k ((0,n2w (LENGTH bs)) ::
      MAPi (\i w. (i+1,w)) (bytes_to_slots bs)) st) = n2w (LENGTH bs)` by
    (qspec_then `bytes_to_slots bs` (qspec_then `k` mp_tac) copy_dyn_lookup >>
     disch_then (qspecl_then [`st`, `0`, `n2w (LENGTH bs)`] mp_tac) >> simp[]) >>
  Cases_on `j = 0` >- (gvs[] >> simp[]) >>
  `32 * (j - 1) + b < LENGTH bs` by
    (gvs[dyn_bytes_dead_def, w2n_n2w, LESS_MOD] >> decide_tac) >>
  `32 * (j - 1) < LENGTH bs` by decide_tac >>
  drule copy_slots_index >> strip_tac >>
  `j < LENGTH (bytes_to_slots bs) + 1` by decide_tac >>
  simp[copy_dyn_lookup] >>
  `off + 32*j = (off + 32) + 32*(j-1)` by decide_tac >>
  pop_assum SUBST1_TAC >>
  `mem_bytes_at 0 (LENGTH bs) bs = bs` by simp[mem_bytes_at_def, TAKE_APPEND1] >>
  `EL b (word_to_bytes (mem_word_at (32*(j-1)) bs) T) =
   EL (32*(j-1)+b) bs` by
    (irule copy_mem_payload_byte_at >> simp[] >> qexists_tac `0` >> simp[]) >>
  pure_asm_rewrite_tac[] >> sym_tac >>
  irule copy_mem_payload_byte_at >> simp[] >> qexists_tac `off+32` >>
  simp[] >> decide_tac
QED

Theorem copy_dynamic_memory_live[local]:
  !tv max v off mem k writes st j b.
    (tv = BaseTV (BytesT (Dynamic max)) \/ tv = BaseTV (StringT max)) /\
    well_formed_type_value tv /\ value_has_type tv v /\
    val_in_memory tv v off mem /\ encode_value tv v = SOME writes /\
    w2n k + type_slot_size tv <= dimword (:256) /\
    j < type_slot_size tv /\ b < 32 /\
    ~dead_bytes (apply_writes k writes st) (w2n k) tv (w2n k+j) b ==>
    EL b (word_to_bytes
      (lookup_storage (n2w (w2n k+j)) (apply_writes k writes st)) T) =
    EL b (word_to_bytes (mem_word_at (off+32*j) mem) T)
Proof
  rpt gen_tac >> strip_tac >>
  drule (CONJUNCT1 encode_writes_bounded) >>
  asm_rewrite_tac[] >> disch_tac >>
  gvs[] >> Cases_on `v` >>
  gvs[well_formed_type_value_def, value_has_type_def, encode_value_def,
      encode_dyn_bytes_slots_def, val_in_memory_def, type_slot_size_def,
      dead_bytes_def, AllCaseEqs()] >>
  qmatch_goalsub_abbrev_tac `bytes_to_slots bs` >>
  TRY (rename1 `n2w (STRLEN s)` >>
    `LENGTH bs = STRLEN s` by simp[Abbr `bs`] >>
    pop_assum (SUBST_ALL_TAC o SYM)) >>
  `LENGTH (bytes_to_slots bs) + 1 <= vfmConstants$word_size max + 1` by
    (irule copy_dyn_length_bound >> qexists_tac `n2w (LENGTH bs) : bytes32` >>
     simp[] >> first_assum ACCEPT_TAC) >>
  once_rewrite_tac [Q.SPECL [`j`, `w2n k`] ADD_COMM,
                    Q.SPECL [`32*j`, `off`] ADD_COMM] >>
  irule copy_dyn_live >> simp[] >> qexists_tac `max` >> simp[] >> decide_tac
QED

(* Default values have zero words wherever a byte remains live. *)
Theorem copy_default_zero_word[local]:
  (!tv off mem base st j b.
    val_in_memory tv (default_value tv) off mem /\
    (!i. i < type_slot_size tv ==> lookup_storage (n2w (base+i)) st = 0w) /\
    j < type_slot_size tv /\ b < 32 /\
    ~dead_bytes st base tv (base+j) b ==>
    mem_word_at (off+32*j) mem = 0w) /\
  (!tvs off mem base st j b.
    tuple_in_memory (MAP default_value tvs) tvs off mem /\
    (!i. i < type_slot_size_list tvs ==> lookup_storage (n2w (base+i)) st = 0w) /\
    j < type_slot_size_list tvs /\ b < 32 /\
    ~dead_bytes_list st base tvs (base+j) b ==>
    mem_word_at (off+32*j) mem = 0w) /\
  (!fields off mem base st j b.
    fields_in_memory (MAP (\(id,t). (id,default_value t)) fields) fields off mem /\
    (!i. i < type_slot_size_fields fields ==> lookup_storage (n2w (base+i)) st = 0w) /\
    j < type_slot_size_fields fields /\ b < 32 /\
    ~dead_bytes_fields st base fields (base+j) b ==>
    mem_word_at (off+32*j) mem = 0w)
Proof
  ho_match_mp_tac type_slot_size_ind >>
  simp[default_value_def, default_value_tuple_MAP, default_value_struct_MAP,
       type_slot_size_def, val_in_memory_def, dead_bytes_def,
       val_to_w256_def, typed_val_to_w256_def, integer_wordTheory.i2w_def,
       word_of_bytes_be_pad_right, byteTheory.word_of_bytes_be_def,
       word_of_bytes_replicate_zero] >>
  rpt conj_tac
  >- (rpt strip_tac >>
      first_x_assum (qspec_then `0` mp_tac) >> simp[] >> strip_tac >>
      gvs[dyn_bytes_dead_def] >> `j = 0` by decide_tac >> gvs[])
  >- (rpt strip_tac >>
      first_x_assum (qspec_then `0` mp_tac) >> simp[] >> strip_tac >>
      gvs[dyn_bytes_dead_def] >> `j = 0` by decide_tac >> gvs[])
  >- suspend "address"
  >- suspend "fixed"
  >- suspend "dynamic"
  >- suspend "tuple"
  >> suspend "fields"
QED

Resume copy_default_zero_word[address]:
  rewrite_tac[GSYM word_to_bytes_w2w_address] >>
  simp[word_to_bytes_word_of_bytes_256, w2w_0]
QED
Resume copy_default_zero_word[fixed]:
  rpt strip_tac >>
  `0 < type_slot_size tv` by (Cases_on `type_slot_size tv` >> gvs[]) >>
  qabbrev_tac `sz = type_slot_size tv` >>
  rename1 `!i. i < n * sz ==> lookup_storage (n2w (a+i)) st = 0w` >>
  `j DIV sz < n` by simp[DIV_LT_X, Abbr `sz`] >>
  `j MOD sz < sz` by simp[] >>
  `j = j DIV sz * sz + j MOD sz` by metis_tac[DIVISION] >>
  `mem_word_at (32*(j MOD sz) + (off + (j DIV sz)*type_memory_size tv)) mem = 0w`
    suffices_by (pure_rewrite_tac[type_memory_size_slots] >>
      `32 * (j MOD sz) + (off + j DIV sz * (32 * type_slot_size tv)) =
       32*j + off` by (simp[Abbr `sz`] >> decide_tac) >>
      pop_assum SUBST1_TAC >> simp[]) >>
  qpat_x_assum `!off mem base st j b. _`
    (qspecl_then [`off + (j DIV sz)*type_memory_size tv`, `mem`,
                  `a + (j DIV sz)*sz`] mp_tac) >>
  disch_then irule >> simp[] >> qexistsl_tac [`b`, `st`] >>
  simp[] >> conj_tac
  >- (rpt strip_tac >> first_x_assum irule >>
      `sz * (j DIV sz + 1) <= sz * n` by simp[LE_MULT_LCANCEL] >>
      pop_assum (mp_tac o PURE_REWRITE_RULE [LEFT_ADD_DISTRIB, MULT_CLAUSES]) >>
      `sz * n = n * sz` by simp[MULT_COMM] >> decide_tac) >>
  `sz * (j DIV sz) + j MOD sz = j` by decide_tac >>
  pop_assum SUBST1_TAC >>
  qpat_x_assum `!i. ~(i < n) \/ _` (qspec_then `j DIV sz` mp_tac) >>
  simp[MULT_COMM]
QED
Resume copy_default_zero_word[dynamic]:
  rpt gen_tac >> disch_then kall_tac >> rpt strip_tac >>
  Cases_on `j = 0` >- gvs[] >>
  rename1 `!i. i < n * type_slot_size tv + 1 ==>
    lookup_storage (n2w (a+i)) st = 0w` >>
  qpat_x_assum `!i. i < n * type_slot_size tv + 1 ==> _`
    (qspec_then `0` mp_tac) >> simp[] >> strip_tac >>
  gvs[] >>
  `0 < type_slot_size tv` by (Cases_on `type_slot_size tv` >> gvs[]) >>
  qabbrev_tac `sz = type_slot_size tv` >>
  `0 < n` by (Cases_on `n` >> gvs[]) >>
  `(j-1) DIV sz < n` by (simp[DIV_LT_X] >> decide_tac) >>
  `(j-1) MOD sz < sz` by simp[] >>
  `j-1 = (j-1) DIV sz * sz + (j-1) MOD sz` by metis_tac[DIVISION] >>
  qpat_x_assum `!i. ~(i < n) \/ _` (qspec_then `(j-1) DIV sz` mp_tac) >>
  simp[LEFT_ADD_DISTRIB, MULT_COMM] >> decide_tac
QED
Resume copy_default_zero_word[tuple]:
  rpt strip_tac >>
  rename1 `!i. i < type_slot_size tv + type_slot_size_list tvs ==>
    lookup_storage (n2w (a+i)) st = 0w` >>
  Cases_on `j < type_slot_size tv`
  >- (qpat_x_assum `!off mem base st j b. val_in_memory _ _ _ _ /\ _ ==> _`
        (qspecl_then [`off`, `mem`, `a`] mp_tac) >>
      disch_then irule >> simp[] >> qexistsl_tac [`b`, `st`] >> simp[] >>
      rpt strip_tac >> first_x_assum irule >> decide_tac) >>
  `32*j+off = 32*(j-type_slot_size tv)+(off+type_memory_size tv)` by
    (simp[type_memory_size_slots] >> decide_tac) >>
  pop_assum SUBST1_TAC >>
  qpat_x_assum `!off mem base st j b. tuple_in_memory _ _ _ _ /\ _ ==> _`
    (qspecl_then [`off+type_memory_size tv`, `mem`, `a+type_slot_size tv`] mp_tac) >>
  disch_then irule >> simp[] >> qexistsl_tac [`b`, `st`] >> simp[] >>
  rpt strip_tac >> first_x_assum irule >> decide_tac
QED
Resume copy_default_zero_word[fields]:
  rpt strip_tac >>
  rename1 `!i. i < type_slot_size tv + type_slot_size_fields fields ==>
    lookup_storage (n2w (a+i)) st = 0w` >>
  Cases_on `j < type_slot_size tv`
  >- (qpat_x_assum `!off mem base st j b. val_in_memory _ _ _ _ /\ _ ==> _`
        (qspecl_then [`off`, `mem`, `a`] mp_tac) >>
      disch_then irule >> simp[] >> qexistsl_tac [`b`, `st`] >> simp[] >>
      rpt strip_tac >> first_x_assum irule >> decide_tac) >>
  `32*j+off = 32*(j-type_slot_size tv)+(off+type_memory_size tv)` by
    (simp[type_memory_size_slots] >> decide_tac) >>
  pop_assum SUBST1_TAC >>
  qpat_x_assum `!off mem base st j b. fields_in_memory _ _ _ _ /\ _ ==> _`
    (qspecl_then [`off+type_memory_size tv`, `mem`, `a+type_slot_size tv`] mp_tac) >>
  disch_then irule >> simp[] >> qexistsl_tac [`b`, `st`] >> simp[] >>
  rpt strip_tac >> first_x_assum irule >> decide_tac
QED
Finalise copy_default_zero_word

(* Select a nonempty child interval, retaining the surrounding writes. *)
Theorem copy_tuple_select[local]:
  !tvs vs offset off mem base st writes j b.
    values_have_types tvs vs /\ tuple_in_memory vs tvs off mem /\
    encode_tuple offset tvs vs = SOME writes /\
    j < type_slot_size_list tvs /\
    ~dead_bytes_list st (base+offset) tvs (base+offset+j) b ==>
    ?tv v d child pre post.
      MEM tv tvs /\ value_has_type tv v /\
      d <= j /\ j < d+type_slot_size tv /\
      d+type_slot_size tv <= type_slot_size_list tvs /\
      val_in_memory tv v (off+32*d) mem /\ encode_value tv v = SOME child /\
      writes = pre ++ MAP (\(i,w). (i+(offset+d),w)) child ++ post /\
      (!i. MEM i (MAP FST post) ==>
        offset+d+type_slot_size tv <= i /\ i < offset+type_slot_size_list tvs) /\
      ~dead_bytes st (base+offset+d) tv (base+offset+j) b
Proof
  Induct >> simp[type_slot_size_def] >>
  rpt gen_tac >> Cases_on `vs` >>
  simp[value_has_type_def, val_in_memory_def] >>
  rpt strip_tac >>
  qpat_x_assum `encode_tuple _ _ _ = _` mp_tac >>
  simp[Once encode_value_def, AllCaseEqs()] >> strip_tac >>
  rename1 `encode_value hd vhd = SOME hdws` >>
  rename1 `encode_tuple (offset+type_slot_size hd) tvs tail = SOME tailws` >>
  rename1 `~dead_bytes_list st (a+offset) (hd::tvs) _ b` >>
  gvs[Once dead_bytes_def] >>
  Cases_on `j < type_slot_size hd`
  >- suspend "head"
  >> suspend "tail"
QED

Resume copy_tuple_select[head]:
  qexistsl_tac [`hd`, `vhd`, `0`, `hdws`, `[]`, `tailws`] >> simp[] >>
  drule (cj 2 encode_writes_bounded) >> asm_rewrite_tac[] >>
  pure_rewrite_tac[ADD_ASSOC] >> simp_tac bool_ss []
QED
Resume copy_tuple_select[tail]:
  `j-type_slot_size hd < type_slot_size_list tvs` by decide_tac >>
  `~dead_bytes_list st (a+(offset+type_slot_size hd)) tvs
     (a+((j-type_slot_size hd)+(offset+type_slot_size hd))) b` by
    (`a+((j-type_slot_size hd)+(offset+type_slot_size hd)) = a+(j+offset)`
       by decide_tac >> simp[]) >>
  first_x_assum drule_all >> strip_tac >>
  qexistsl_tac [`tv`, `v`, `type_slot_size hd+d`, `child`,
    `MAP (\(i,w). (i+offset,w)) hdws ++ pre`, `post`] >>
  simp[APPEND_ASSOC] >> conj_tac
  >- (`off+32*(d+type_slot_size hd) = 32*d+(off+type_memory_size hd)` by
        (simp[type_memory_size_slots] >> decide_tac) >> simp[]) >>
  conj_tac
  >- (qpat_x_assum `!i. MEM i (MAP FST post) ==> _` mp_tac >>
      pure_rewrite_tac[ADD_ASSOC] >> simp_tac bool_ss []) >>
  `a+(j-type_slot_size hd+(offset+type_slot_size hd)) = a+(j+offset)`
    by decide_tac >> gvs[]
QED
Finalise copy_tuple_select

Theorem copy_struct_select[local]:
  !ftypes vs offset off mem base st writes j b.
    struct_has_type ftypes vs /\ fields_in_memory vs ftypes off mem /\
    encode_struct offset ftypes vs = SOME writes /\
    j < type_slot_size_fields ftypes /\
    ~dead_bytes_fields st (base+offset) ftypes (base+offset+j) b ==>
    ?tv v d child pre post.
      MEM tv (MAP SND ftypes) /\ value_has_type tv v /\
      d <= j /\ j < d+type_slot_size tv /\
      d+type_slot_size tv <= type_slot_size_fields ftypes /\
      val_in_memory tv v (off+32*d) mem /\ encode_value tv v = SOME child /\
      writes = pre ++ MAP (\(i,w). (i+(offset+d),w)) child ++ post /\
      (!i. MEM i (MAP FST post) ==>
        offset+d+type_slot_size tv <= i /\ i < offset+type_slot_size_fields ftypes) /\
      ~dead_bytes st (base+offset+d) tv (base+offset+j) b
Proof
  Induct >> simp[type_slot_size_def] >> rpt gen_tac >> PairCases_on `h` >>
  Cases_on `vs` >>
  simp[value_has_type_def, val_in_memory_def] >>
  PairCases_on `h` >> simp[value_has_type_def, val_in_memory_def] >>
  rpt strip_tac >>
  qpat_x_assum `encode_struct _ _ _ = _` mp_tac >>
  simp[Once encode_value_def, AllCaseEqs()] >> strip_tac >>
  rename1 `encode_value hd vhd = SOME hdws` >>
  rename1 `encode_struct (offset+type_slot_size hd) ftypes tail = SOME tailws` >>
  rename1 `~dead_bytes_fields st (a+offset) ((_ ,hd)::ftypes) _ b` >>
  gvs[Once dead_bytes_def, type_slot_size_def] >>
  Cases_on `j < type_slot_size hd`
  >- suspend "head"
  >> suspend "tail"
QED

Resume copy_struct_select[head]:
  qexistsl_tac [`hd`, `vhd`, `0`, `hdws`, `[]`, `tailws`] >> simp[] >>
  drule (cj 5 encode_writes_bounded) >> asm_rewrite_tac[] >>
  pure_rewrite_tac[ADD_ASSOC] >> simp_tac bool_ss []
QED
Resume copy_struct_select[tail]:
  `j-type_slot_size hd < type_slot_size_fields ftypes` by decide_tac >>
  `~dead_bytes_fields st (a+(offset+type_slot_size hd)) ftypes
     (a+((j-type_slot_size hd)+(offset+type_slot_size hd))) b` by
    (`a+((j-type_slot_size hd)+(offset+type_slot_size hd)) = a+(j+offset)`
       by decide_tac >> simp[]) >>
  first_x_assum drule_all >> strip_tac >>
  qexistsl_tac [`tv`, `v`, `type_slot_size hd+d`, `child`,
    `MAP (\(i,w). (i+offset,w)) hdws ++ pre`, `post`] >>
  simp[APPEND_ASSOC] >> conj_tac
  >- (`off+32*(d+type_slot_size hd) = 32*d+(off+type_memory_size hd)` by
        (simp[type_memory_size_slots] >> decide_tac) >> simp[]) >>
  conj_tac
  >- (qpat_x_assum `!i. MEM i (MAP FST post) ==> _` mp_tac >>
      pure_rewrite_tac[ADD_ASSOC] >> simp_tac bool_ss []) >>
  `a+(j-type_slot_size hd+(offset+type_slot_size hd)) = a+(j+offset)`
    by decide_tac >> gvs[]
QED
Finalise copy_struct_select

(* Every sparse write lies in the interval of a key actually present. *)
Theorem copy_sparse_write_key[local]:
  !sparse tv offset writes n x.
    sparse_has_type tv n sparse /\
    encode_static_array tv offset sparse = SOME writes /\
    MEM x (MAP FST writes) ==>
    ?i r. MEM i (MAP FST sparse) /\ r < type_slot_size tv /\
          x = offset+i*type_slot_size tv+r
Proof
  Induct >> simp[Once encode_value_def] >> Cases >> rename1 `(i0,hv)::sparse` >>
  rpt gen_tac >>
  simp[value_has_type_def] >> rpt strip_tac >>
  qpat_x_assum `encode_static_array _ _ _ = _` mp_tac >>
  simp[Once encode_value_def, AllCaseEqs()] >> strip_tac >>
  rename1 `encode_value tv hv = SOME hdws` >>
  rename1 `encode_static_array tv offset sparse = SOME tailws` >>
  gvs[MAP_APPEND, MEM_APPEND, MEM_MAP, pairTheory.EXISTS_PROD]
  >- (rename1 `MEM (r,w) hdws` >>
      `MEM r (MAP FST hdws)` by (simp[MEM_MAP, pairTheory.EXISTS_PROD] >> metis_tac[]) >>
      drule_all (cj 1 encode_writes_bounded) >> strip_tac >>
      qexistsl_tac [`i0`, `r`] >> simp[]) >>
  first_x_assum drule >> disch_then drule >>
  disch_then (qspec_then `x` mp_tac) >>
  (impl_tac >- metis_tac[]) >> strip_tac >>
  qexistsl_tac [`i`, `r`] >> simp[] >> metis_tac[]
QED

Theorem copy_sparse_select[local]:
  !sparse tv n offset off mem writes i v.
    sparse_has_type tv n sparse /\ SORTED $< (MAP FST sparse) /\
    kvs_in_memory sparse off tv mem /\
    encode_static_array tv offset sparse = SOME writes /\ MEM (i,v) sparse ==>
    ?child pre post.
      value_has_type tv v /\
      val_in_memory tv v (off+32*(i*type_slot_size tv)) mem /\
      encode_value tv v = SOME child /\
      writes = pre ++ MAP (\(j,w). (j+(offset+i*type_slot_size tv),w)) child ++ post /\
      (!j. MEM j (MAP FST post) ==>
        offset+(i+1)*type_slot_size tv <= j /\ j < offset+n*type_slot_size tv)
Proof
  Induct >> simp[] >> Cases >> rename1 `(i0,hv)::sparse` >> rpt gen_tac >>
  simp[value_has_type_def, val_in_memory_def] >> rpt strip_tac >>
  qpat_x_assum `encode_static_array _ _ _ = _` mp_tac >>
  simp[Once encode_value_def, AllCaseEqs()] >> strip_tac >>
  rename1 `encode_value tv hv = SOME hdws` >>
  rename1 `encode_static_array tv offset sparse = SOME tailws` >>
  gvs[]
  >- suspend "head"
  >> suspend "tail"
QED

Resume copy_sparse_select[head]:
  qexistsl_tac [`[]`, `tailws`] >>
  `off+32*(i*type_slot_size tv) = off+i*type_memory_size tv` by
    simp_tac std_ss [type_memory_size_slots, MULT_ASSOC, MULT_COMM] >>
  asm_rewrite_tac[APPEND] >> rpt strip_tac
  >- suspend "head_lower"
  >> (drule_all (cj 3 encode_writes_bounded) >> simp[])
QED
Resume copy_sparse_select[head_lower]:
  drule_all copy_sparse_write_key >>
  disch_then (qx_choosel_then [`i2`, `r2`] strip_assume_tac) >>
  `i < i2` by gvs[sortingTheory.SORTED_EQ] >>
  `(i+1)*type_slot_size tv <= i2*type_slot_size tv` by simp[LE_MULT_RCANCEL] >>
  decide_tac
QED
Resume copy_sparse_select[tail]:
  `SORTED $< (MAP FST sparse)` by gvs[sortingTheory.SORTED_EQ] >>
  first_x_assum drule_all >> strip_tac >>
  qexistsl_tac [`child`, `MAP (\(j,w). (j+offset+i0*type_slot_size tv,w)) hdws ++ pre`, `post`] >>
  simp[APPEND_ASSOC]
QED
Finalise copy_sparse_select

(* Dynamic payload selection retains the suffix's lower bound. *)
Theorem copy_dyn_select[local]:
  !vs tv offset off mem writes i.
    all_have_type tv vs /\ elems_in_memory vs off tv mem /\
    encode_dyn_array tv offset vs = SOME writes /\ i < LENGTH vs ==>
    ?v child pre post.
      value_has_type tv v /\
      val_in_memory tv v (off+32*(i*type_slot_size tv)) mem /\
      encode_value tv v = SOME child /\
      writes = pre ++ MAP (\(j,w). (j+(offset+i*type_slot_size tv),w)) child ++ post /\
      (!j. MEM j (MAP FST post) ==>
        offset+(i+1)*type_slot_size tv <= j /\
        j < offset+LENGTH vs*type_slot_size tv)
Proof
  Induct >> simp[] >> rpt gen_tac >>
  simp[value_has_type_def, val_in_memory_def] >> rpt strip_tac >>
  qpat_x_assum `encode_dyn_array _ _ _ = _` mp_tac >>
  simp[Once encode_value_def, AllCaseEqs()] >> strip_tac >>
  rename1 `encode_value tv h = SOME hdws` >>
  rename1 `encode_dyn_array tv (offset+type_slot_size tv) vs = SOME tailws` >>
  Cases_on `i`
  >- (qexistsl_tac [`h`, `hdws`, `[]`, `tailws`] >> simp[] >>
      drule (cj 4 encode_writes_bounded) >> asm_rewrite_tac[] >>
      rpt strip_tac >> first_x_assum drule >> strip_tac >>
      simp[MULT_CLAUSES] >> decide_tac) >>
  rename1 `SUC ix < SUC (LENGTH vs)` >>
  `ix < LENGTH vs` by decide_tac >>
  first_x_assum drule_all >> strip_tac >>
  qexistsl_tac [`v`, `child`, `MAP (\(j,w). (j+offset,w)) hdws ++ pre`, `post`] >>
  simp[APPEND_ASSOC, MULT_CLAUSES] >> conj_tac
  >- (`off+32*(type_slot_size tv+ix*type_slot_size tv) =
       off+type_memory_size tv+32*(ix*type_slot_size tv)` by
       (simp[type_memory_size_slots] >> decide_tac) >> asm_rewrite_tac[]) >>
  conj_tac
  >- (qpat_x_assum `_ = writes` (SUBST1_TAC o SYM) >>
      qpat_x_assum `tailws = _` SUBST1_TAC >>
      pure_rewrite_tac[APPEND_ASSOC, ADD_ASSOC] >> REFL_TAC) >>
  rpt strip_tac >> first_x_assum drule >> strip_tac >>
  pure_rewrite_tac[RIGHT_ADD_DISTRIB, MULT_CLAUSES] >>
  rule_assum_tac (PURE_REWRITE_RULE [LEFT_ADD_DISTRIB, MULT_CLAUSES]) >>
  once_rewrite_tac[MULT_COMM] >>
  pure_rewrite_tac[LEFT_ADD_DISTRIB, RIGHT_ADD_DISTRIB, MULT_CLAUSES] >>
  rule_assum_tac (PURE_REWRITE_RULE
    [LEFT_ADD_DISTRIB, RIGHT_ADD_DISTRIB, MULT_CLAUSES]) >> decide_tac
QED

Theorem copy_sparse_absent_storage[local]:
  !sparse tv n writes i k st x.
    sparse_has_type tv n sparse /\ encode_static_array tv 0 sparse = SOME writes /\
    ALOOKUP sparse i = NONE /\ i < n /\
    w2n k+n*type_slot_size tv <= dimword (:256) /\
    w2n k+i*type_slot_size tv <= x /\
    x < w2n k+i*type_slot_size tv+type_slot_size tv ==>
    lookup_storage (n2w x)
      (apply_writes k (GENLIST (\j. (j,0w)) (n*type_slot_size tv) ++ writes) st) = 0w
Proof
  rpt strip_tac >> qabbrev_tac `s = type_slot_size tv` >>
  `0 < s` by decide_tac >>
  `(i+1)*s <= n*s` by simp[LE_MULT_RCANCEL] >>
  `x-w2n k < n*s /\ x = w2n k+(x-w2n k)` by
    (pop_assum (mp_tac o PURE_REWRITE_RULE [LEFT_ADD_DISTRIB, RIGHT_ADD_DISTRIB, MULT_CLAUSES]) >>
     decide_tac) >>
  rewrite_tac[apply_writes_append] >>
  `lookup_storage (n2w x)
    (apply_writes k writes
      (apply_writes k (GENLIST (\j. (j,0w)) (n*s)) st)) =
   lookup_storage (n2w x)
      (apply_writes k (GENLIST (\j. (j,0w)) (n*s)) st)` by
    (irule copy_writes_frame >> qexistsl_tac [`w2n k+i*s`, `s`] >>
     simp[] >> rpt strip_tac >> rename1 `MEM j (MAP FST writes)` >>
     drule_all (cj 3 encode_writes_bounded) >> strip_tac
     >- (gvs[Abbr `s`] >> decide_tac) >>
     drule_all copy_sparse_write_key >> strip_tac >>
     rename1 `MEM h (MAP FST sparse)` >>
     spose_not_then strip_assume_tac >>
     `j DIV s = h` by
       (irule DIV_UNIQUE >> qexists_tac `r` >> simp[Abbr `s`]) >>
     `j DIV s = i` by
       (irule DIV_UNIQUE >> qexists_tac `j-i*s` >> decide_tac) >>
     gvs[alistTheory.ALOOKUP_NONE]) >>
  pop_assum SUBST1_TAC >>
  qpat_x_assum `x = _` SUBST1_TAC >> irule copy_zero_interval >> simp[]
QED

Theorem copy_static_live_index[local]:
  !st base tv n j b.
    j < n*type_slot_size tv /\
    ~dead_bytes st base (ArrayTV tv (Fixed n)) (base+j) b ==>
    ?i r. i < n /\ r < type_slot_size tv /\ j = i*type_slot_size tv+r /\
      ~dead_bytes st (base+i*type_slot_size tv) tv (base+j) b
Proof
  rpt strip_tac >>
  `0 < type_slot_size tv` by (Cases_on `type_slot_size tv` >> gvs[]) >>
  qabbrev_tac `s = type_slot_size tv` >>
  `j DIV s < n` by simp[DIV_LT_X] >>
  `j MOD s < s` by simp[] >>
  `j = j DIV s*s+j MOD s` by metis_tac[DIVISION] >>
  qabbrev_tac `ix = j DIV s` >> qabbrev_tac `r = j MOD s` >>
  qexistsl_tac [`ix`, `r`] >> simp[] >>
  qpat_x_assum `~dead_bytes _ _ _ _ _` mp_tac >>
  simp[Once dead_bytes_def] >>
  disch_then (qspec_then `ix` mp_tac) >> simp[Abbr `s`]
QED

Theorem copy_dyn_live_index[local]:
  !st base tv n j b.
    0 < j /\ j < 1+n*type_slot_size tv /\ b < 32 /\
    ~dead_bytes st base (ArrayTV tv (Dynamic n)) (base+j) b ==>
    ?i r. i < n /\ i < w2n (lookup_storage (n2w base) st) /\
      r < type_slot_size tv /\ j = 1+i*type_slot_size tv+r /\
      ~dead_bytes st (base+1+i*type_slot_size tv) tv (base+j) b
Proof
  rpt strip_tac >>
  `0 < type_slot_size tv` by (Cases_on `type_slot_size tv` >> gvs[]) >>
  qabbrev_tac `s = type_slot_size tv` >>
  `j-1 < n*s` by decide_tac >>
  `(j-1) DIV s < n` by simp[DIV_LT_X] >>
  `(j-1) MOD s < s` by simp[] >>
  `j-1 = (j-1) DIV s*s+(j-1) MOD s` by metis_tac[DIVISION] >>
  qabbrev_tac `ix = (j-1) DIV s` >> qabbrev_tac `r = (j-1) MOD s` >>
  `j = 1+ix*s+r` by decide_tac >>
  qpat_x_assum `j-1 = _` kall_tac >>
  qexistsl_tac [`ix`, `r`] >> simp[] >>
  qpat_x_assum `~dead_bytes _ _ _ _ _` mp_tac >>
  simp[Once dead_bytes_def] >>
  disch_then (qspec_then `ix` mp_tac) >>
  simp[Abbr `s`] >> rpt IF_CASES_TAC >> gvs[] >> decide_tac
QED

Theorem copy_dyn_head[local]:
  !tv vs slots k st.
    all_have_type tv vs /\ encode_dyn_array tv 1 vs = SOME slots /\
    w2n k+1+LENGTH vs*type_slot_size tv <= dimword (:256) ==>
    lookup_storage k (apply_writes k ((0,n2w (LENGTH vs))::slots) st) =
      n2w (LENGTH vs)
Proof
  rpt strip_tac >>
  drule (cj 4 encode_writes_bounded) >> asm_rewrite_tac[] >> strip_tac >>
  rewrite_tac[apply_writes_def] >>
  `lookup_storage (n2w (w2n k))
     (apply_writes k slots (update_storage (n2w (w2n k)) (n2w (LENGTH vs)) st)) =
   lookup_storage (n2w (w2n k))
     (update_storage (n2w (w2n k)) (n2w (LENGTH vs)) st)` by
    (irule copy_writes_frame >> qexistsl_tac [`w2n k`, `1`] >>
     simp[] >> rpt strip_tac >> first_x_assum drule >> strip_tac >> decide_tac) >>
  gvs[lookup_storage_def, update_storage_def, combinTheory.APPLY_UPDATE_THM]
QED

(* Turn a selector's write decomposition into its child storage interface. *)
Theorem copy_selected_storage[local]:
  !writes pre child post k st d tv total j b.
    writes = pre ++ MAP (\(i,w). (i+d,w)) child ++ post /\
    d <= j /\ j < d+type_slot_size tv /\
    d+type_slot_size tv <= total /\ w2n k+total <= dimword (:256) /\
    (!i. MEM i (MAP FST post) ==> d+type_slot_size tv <= i /\ i < total) /\
    ~dead_bytes (apply_writes k writes st) (w2n k+d) tv (w2n k+j) b ==>
    ?st0.
      (!x. w2n k+d <= x /\ x < w2n k+d+type_slot_size tv ==>
        lookup_storage (n2w x) (apply_writes k writes st) =
        lookup_storage (n2w x) (apply_writes (n2w (w2n k+d)) child st0)) /\
      ~dead_bytes (apply_writes (n2w (w2n k+d)) child st0)
        (w2n k+d) tv (w2n k+j) b
Proof
  rpt strip_tac >> qexists_tac `apply_writes k pre st` >>
  conj_asm1_tac
  >- (rpt strip_tac >> asm_rewrite_tac[] >>
      irule copy_selected_writes >> asm_rewrite_tac[] >>
      qexists_tac `type_slot_size tv` >>
      simp[] >> rpt strip_tac >>
      first_x_assum drule >> strip_tac >> decide_tac) >>
  drule (cj 1 dead_bytes_frame) >>
  disch_then (qspecl_then [`w2n k+j`, `b`] mp_tac) >> simp[]
QED

Theorem copy_tuple_member[local]:
  !tvs tv.
    well_formed_type_value (TupleTV tvs) /\ MEM tv tvs ==>
    well_formed_type_value tv /\
    type_value_size tv < type_value_size (TupleTV tvs)
Proof
  rpt strip_tac
  >- (gvs[well_formed_type_value_def, EVERY_MEM] >>
      first_x_assum drule >> simp[]) >>
  irule MEM_type_value_size_TupleTV >> asm_rewrite_tac[]
QED

Theorem copy_struct_member[local]:
  !fields tv.
    well_formed_type_value (StructTV fields) /\ MEM tv (MAP SND fields) ==>
    well_formed_type_value tv /\
    type_value_size tv < type_value_size (StructTV fields)
Proof
  rpt strip_tac
  >- (gvs[well_formed_type_value_def, EVERY_MEM, MEM_MAP] >>
      first_x_assum drule >> simp[]) >>
  irule MEM_type_value_size_StructTV >>
  gvs[MEM_MAP] >> PairCases_on `y` >> gvs[] >> metis_tac[]
QED

(* Storing v of type tv at slot k as the source does (encode_value), every
   byte of slot k + j that v does not leave dead equals that byte of v's
   j-th memory word.  The slots past a bytestring's used words and a
   DynArray's present elements keep their old words in storage while
   memory holds anything there; those are v's dead bytes. *)
Theorem encode_value_memory_live:
  !tv v off mem k writes st j b.
    well_formed_type_value tv /\ value_has_type tv v /\
    val_in_memory tv v off mem /\
    encode_value tv v = SOME writes /\
    w2n k + type_slot_size tv <= dimword (:256) /\
    j < type_slot_size tv /\ b < 32 /\
    ~dead_bytes (apply_writes k writes st) (w2n k) tv (w2n k + j) b ==>
    EL b (word_to_bytes
            (lookup_storage (n2w (w2n k + j)) (apply_writes k writes st)) T) =
    EL b (word_to_bytes (mem_word_at (off + 32 * j) mem) T)
Proof
  measureInduct_on `type_value_size tv` >> Cases_on `tv`
  >- suspend "base"
  >- suspend "tuple"
  >- suspend "array"
  >- suspend "struct"
  >- suspend "flag"
  >> simp[type_slot_size_def]
QED

Resume encode_value_memory_live[base]:
  pop_assum kall_tac >>
  Cases_on `?max. b = BytesT (Dynamic max) \/ b = StringT max`
  >- (pop_assum strip_assume_tac >> rpt strip_tac >>
      irule copy_dynamic_memory_live >>
      (conj_tac >- asm_rewrite_tac[]) >>
      qexists_tac `max` >> qexists_tac `BaseTV b` >> qexists_tac `v` >>
      asm_rewrite_tac[]) >>
  Cases_on `b` >> gvs[] >>
  TRY (rename1 `BytesT bd` >> Cases_on `bd` >> gvs[]) >>
  rpt strip_tac >>
  qpat_x_assum `encode_value _ _ = _` mp_tac >>
  simp[Once encode_value_def, AllCaseEqs()] >> strip_tac >>
  gvs[type_slot_size_def] >>
  `mem_word_at off mem = slot` by
    (metis_tac[copy_primitive_memory_word]) >>
  simp[apply_writes_def, lookup_storage_def, update_storage_def,
       combinTheory.APPLY_UPDATE_THM]
QED
Resume encode_value_memory_live[tuple]:
  rpt strip_tac >> Cases_on `v` >>
  TRY (rename1 `ArrayV av` >> Cases_on `av`) >>
  qpat_x_assum `value_has_type _ _` mp_tac >>
  simp[Once value_has_type_def] >> strip_tac >>
  qpat_x_assum `val_in_memory _ _ _ _` mp_tac >>
  simp[Once val_in_memory_def] >> strip_tac >>
  qpat_x_assum `encode_value _ _ = _` mp_tac >>
  simp[Once encode_value_def] >> strip_tac >>
  qpat_x_assum `~dead_bytes _ _ _ _ _` mp_tac >>
  simp[Once dead_bytes_def] >> strip_tac >>
  drule copy_tuple_select >> disch_then drule >> disch_then drule >>
  disch_then (qspecl_then [`w2n k`, `apply_writes k writes st`, `j`, `b`] mp_tac) >>
  (impl_tac >- (fs[type_slot_size_def] >> metis_tac[ADD_COMM])) >>
  simp_tac bool_ss [ADD_CLAUSES] >> strip_tac >>
  drule_all copy_tuple_member >> strip_tac >>
  `w2n k + type_slot_size_list l <= dimword (:256)` by
    fs[type_slot_size_def] >>
  drule_all copy_selected_storage >> strip_tac >>
  qpat_x_assum `!y. _` drule >>
  disch_then (qspecl_then [`v`, `off+32*d`, `mem`, `n2w (w2n k+d)`,
                         `child`, `st0`, `j-d`, `b`] mp_tac) >>
  `w2n k+d < dimword (:256)` by decide_tac >>
  `w2n k+d+(j-d) = w2n k+j` by decide_tac >>
  `off+32*d+32*(j-d) = 32*j+off` by decide_tac >>
  asm_simp_tac std_ss [w2n_n2w, LESS_MOD] >>
  asm_rewrite_tac[] >>
  (impl_tac >- (asm_rewrite_tac[] >> decide_tac)) >>
  strip_tac >>
  qpat_x_assum `!x. _` (qspec_then `w2n k+j` mp_tac) >>
  (impl_tac >- decide_tac) >>
  metis_tac[ADD_COMM]
QED
Resume encode_value_memory_live[struct]:
  rpt strip_tac >> Cases_on `v` >>
  qpat_x_assum `value_has_type _ _` mp_tac >>
  simp[Once value_has_type_def] >> strip_tac >>
  qpat_x_assum `val_in_memory _ _ _ _` mp_tac >>
  simp[Once val_in_memory_def] >> strip_tac >>
  qpat_x_assum `encode_value _ _ = _` mp_tac >>
  simp[Once encode_value_def] >> strip_tac >>
  qpat_x_assum `~dead_bytes _ _ _ _ _` mp_tac >>
  simp[Once dead_bytes_def] >> strip_tac >>
  drule copy_struct_select >> disch_then drule >> disch_then drule >>
  disch_then (qspecl_then [`w2n k`, `apply_writes k writes st`, `j`, `b`] mp_tac) >>
  (impl_tac >- (fs[type_slot_size_def] >> metis_tac[ADD_COMM])) >>
  simp_tac bool_ss [ADD_CLAUSES] >> strip_tac >>
  drule_all copy_struct_member >> strip_tac >>
  `w2n k + type_slot_size_fields l <= dimword (:256)` by
    fs[type_slot_size_def] >>
  drule_all copy_selected_storage >> strip_tac >>
  qpat_x_assum `!y. _` drule >>
  disch_then (qspecl_then [`v`, `off+32*d`, `mem`, `n2w (w2n k+d)`,
                         `child`, `st0`, `j-d`, `b`] mp_tac) >>
  `w2n k+d < dimword (:256)` by decide_tac >>
  `w2n k+d+(j-d) = w2n k+j` by decide_tac >>
  `off+32*d+32*(j-d) = 32*j+off` by decide_tac >>
  asm_simp_tac std_ss [w2n_n2w, LESS_MOD] >> asm_rewrite_tac[] >>
  (impl_tac >- (asm_rewrite_tac[] >> decide_tac)) >> strip_tac >>
  qpat_x_assum `!x. _` (qspec_then `w2n k+j` mp_tac) >>
  (impl_tac >- decide_tac) >> metis_tac[ADD_COMM]
QED
Resume encode_value_memory_live[flag]:
  pop_assum kall_tac >> rpt strip_tac >>
  qpat_x_assum `encode_value _ _ = _` mp_tac >>
  simp[Once encode_value_def, AllCaseEqs()] >> strip_tac >>
  gvs[type_slot_size_def] >>
  `mem_word_at off mem = slot` by metis_tac[copy_primitive_memory_word] >>
  simp[apply_writes_def, lookup_storage_def, update_storage_def,
       combinTheory.APPLY_UPDATE_THM]
QED
Resume encode_value_memory_live[array]:
  Cases_on `b` >- suspend "fixed" >> suspend "dynamic"
QED
Resume encode_value_memory_live[fixed]:
  rpt strip_tac >> Cases_on `v` >>
  TRY (rename1 `ArrayV av` >> Cases_on `av`) >>
  qpat_x_assum `value_has_type _ _` mp_tac >>
  simp[Once value_has_type_def] >> strip_tac >>
  qpat_x_assum `val_in_memory _ _ _ _` mp_tac >>
  simp[Once val_in_memory_def] >> strip_tac >>
  qpat_x_assum `encode_value _ _ = _` mp_tac >>
  simp[Once encode_value_def, AllCaseEqs()] >> strip_tac >>
  `j < n*type_slot_size t` by fs[type_slot_size_def] >>
  drule_all copy_static_live_index >> strip_tac >>
  Cases_on `ALOOKUP l i` >- suspend "absent" >> suspend "present"
QED
Resume encode_value_memory_live[absent]:
  qpat_x_assum `!y. type_value_size y < _ ==> _` kall_tac >>
  `w2n k+n*type_slot_size t <= dimword (:256)` by fs[type_slot_size_def] >>
  `!x. w2n k+i*type_slot_size t <= x /\
        x < w2n k+i*type_slot_size t+type_slot_size t ==>
        lookup_storage (n2w x) (apply_writes k writes st) = 0w` by
    (rpt strip_tac >> qpat_x_assum `_ = writes` (SUBST1_TAC o SYM) >>
     irule copy_sparse_absent_storage >> asm_rewrite_tac[] >>
     qexistsl_tac [`i`, `l`] >> asm_rewrite_tac[]) >>
  `val_in_memory t (default_value t) (off+32*(i*type_slot_size t)) mem` by
    (`off+32*(i*type_slot_size t) = off+i*type_memory_size t` by
      simp_tac std_ss [type_memory_size_slots, MULT_ASSOC, MULT_COMM] >>
     asm_rewrite_tac[] >> first_x_assum irule >> asm_rewrite_tac[]) >>
  `mem_word_at (off+32*(i*type_slot_size t)+32*r) mem = 0w` by
    (irule (cj 1 copy_default_zero_word) >>
     qexistsl_tac [`b`, `w2n k+i*type_slot_size t`, `apply_writes k writes st`, `t`] >>
     asm_rewrite_tac[] >> conj_tac
     >- (rpt strip_tac >> first_x_assum irule >> decide_tac) >>
     `w2n k+i*type_slot_size t+r = w2n k+j` by decide_tac >>
     metis_tac[ADD_ASSOC]) >>
  `off+32*(i*type_slot_size t)+32*r = 32*j+off` by decide_tac >>
  `lookup_storage (n2w (j+w2n k)) (apply_writes k writes st) = 0w` by
    (first_x_assum irule >> decide_tac) >> metis_tac[]
QED
Resume encode_value_memory_live[present]:
  `MEM (i,x) l` by metis_tac[alistTheory.ALOOKUP_MEM] >>
  drule_all copy_sparse_select >> strip_tac >>
  `writes = (GENLIST (\j. (j,0w)) (n*type_slot_size t) ++ pre) ++
      MAP (\(j,w). (j+i*type_slot_size t,w)) child ++ post` by
    metis_tac[APPEND_ASSOC, ADD_CLAUSES] >>
  `w2n k+n*type_slot_size t <= dimword (:256)` by fs[type_slot_size_def] >>
  `i*type_slot_size t <= j /\ j < i*type_slot_size t+type_slot_size t` by decide_tac >>
  `i*type_slot_size t+type_slot_size t <= n*type_slot_size t` by
    (`(i+1)*type_slot_size t <= n*type_slot_size t` by simp[LE_MULT_RCANCEL] >>
     pop_assum (mp_tac o PURE_REWRITE_RULE [RIGHT_ADD_DISTRIB, MULT_CLAUSES]) >>
     decide_tac) >>
  `!h. MEM h (MAP FST post) ==>
       i*type_slot_size t+type_slot_size t <= h /\ h < n*type_slot_size t` by
    (rpt strip_tac >> first_x_assum drule >> simp[LEFT_ADD_DISTRIB]) >>
  drule_all copy_selected_storage >> strip_tac >>
  `well_formed_type_value t` by fs[well_formed_type_value_def] >>
  `type_value_size t < type_value_size (ArrayTV t (Fixed n))` by simp[] >>
  qpat_x_assum `!y. type_value_size y < _ ==> _` drule >>
  disch_then (qspecl_then [`x`, `off+32*(i*type_slot_size t)`, `mem`,
    `n2w (w2n k+i*type_slot_size t)`, `child`, `st0`, `r`, `b`] mp_tac) >>
  `w2n k+i*type_slot_size t < dimword (:256)` by decide_tac >>
  `w2n k+i*type_slot_size t+r = w2n k+j` by decide_tac >>
  `off+32*(i*type_slot_size t)+32*r = 32*j+off` by decide_tac >>
  asm_simp_tac std_ss [w2n_n2w, LESS_MOD] >>
  (impl_tac >- (conj_tac >- decide_tac >>
     qpat_x_assum `~dead_bytes (apply_writes _ child _) _ _ _ _` mp_tac >>
     qpat_x_assum `j = _` (fn th => pure_rewrite_tac[th]) >>
     simp_tac bool_ss [ADD_ASSOC])) >> strip_tac >>
  qpat_x_assum `!x. _ <= x /\ _ ==> _` (qspec_then `w2n k+j` mp_tac) >>
  (impl_tac >- decide_tac) >> metis_tac[ADD_COMM]
QED
Resume encode_value_memory_live[dynamic]:
  rpt strip_tac >> Cases_on `v` >>
  TRY (rename1 `ArrayV av` >> Cases_on `av`) >>
  qpat_x_assum `value_has_type _ _` mp_tac >>
  simp[Once value_has_type_def] >> strip_tac >>
  qpat_x_assum `val_in_memory _ _ _ _` mp_tac >>
  simp[Once val_in_memory_def] >> strip_tac >>
  qpat_x_assum `encode_value _ _ = _` mp_tac >>
  simp[Once encode_value_def, AllCaseEqs()] >> strip_tac >>
  `1+LENGTH l*type_slot_size t <= 1+n*type_slot_size t` by
    simp[LE_MULT_RCANCEL] >>
  `w2n k+1+LENGTH l*type_slot_size t <= dimword (:256)` by
    (qpat_x_assum `w2n k + type_slot_size _ <= _` mp_tac >>
     pure_rewrite_tac[type_slot_size_def] >> decide_tac) >>
  `lookup_storage k (apply_writes k writes st) = n2w (LENGTH l)` by
    (qpat_x_assum `_::slots = writes` (SUBST1_TAC o SYM) >>
     irule copy_dyn_head >> asm_rewrite_tac[] >> metis_tac[]) >>
  Cases_on `j = 0` >- gvs[] >>
  `0 < j /\ j < 1+n*type_slot_size t` by
    (qpat_x_assum `j < type_slot_size _` mp_tac >>
     pure_rewrite_tac[type_slot_size_def] >> decide_tac) >>
  drule_all copy_dyn_live_index >> strip_tac >>
  `i < LENGTH l` by
    (qpat_x_assum `i < w2n _` mp_tac >>
     asm_rewrite_tac[n2w_w2n, w2n_n2w] >>
     `LENGTH l MOD dimword (:256) <= LENGTH l` by
       (irule MOD_LESS_EQ >> simp[]) >> decide_tac) >>
  drule_all copy_dyn_select >> strip_tac >>
  suspend "dynamic_child"
QED
Resume encode_value_memory_live[dynamic_child]:
  qabbrev_tac `d = 1+i*type_slot_size t` >>
  `writes = ((0,n2w (LENGTH l))::pre) ++
      MAP (\(j,w). (j+d,w)) child ++ post` by
    (simp_tac bool_ss [Abbr `d`, APPEND] >> metis_tac[]) >>
  `d <= j /\ j < d+type_slot_size t` by (simp[Abbr `d`] >> decide_tac) >>
  `d+type_slot_size t <= 1+LENGTH l*type_slot_size t` by
    (`(i+1)*type_slot_size t <= LENGTH l*type_slot_size t` by simp[LE_MULT_RCANCEL] >>
     pop_assum (mp_tac o PURE_REWRITE_RULE [RIGHT_ADD_DISTRIB, MULT_CLAUSES]) >>
     simp_tac bool_ss [Abbr `d`] >> decide_tac) >>
  `!h. MEM h (MAP FST post) ==>
       d+type_slot_size t <= h /\ h < 1+LENGTH l*type_slot_size t` by
    (rpt strip_tac >> first_x_assum drule >>
     simp_tac std_ss [Abbr `d`, RIGHT_ADD_DISTRIB] >> decide_tac) >>
  `w2n k+(1+LENGTH l*type_slot_size t) <= dimword (:256)` by decide_tac >>
  `~dead_bytes (apply_writes k writes st) (w2n k+d) t (w2n k+j) b` by
    (qpat_x_assum `~dead_bytes _ (_+1+_) _ _ _` mp_tac >>
     simp_tac bool_ss [Abbr `d`, ADD_ASSOC]) >>
  drule_all copy_selected_storage >> strip_tac >>
  `well_formed_type_value t` by fs[well_formed_type_value_def] >>
  `type_value_size t < type_value_size (ArrayTV t (Dynamic n))` by simp[] >>
  qpat_x_assum `!y. type_value_size y < _ ==> _` drule >>
  disch_then (qspecl_then [`v`, `off+32+32*(i*type_slot_size t)`, `mem`,
    `n2w (w2n k+d)`, `child`, `st0`, `r`, `b`] mp_tac) >>
  `w2n k+d < dimword (:256)` by decide_tac >>
  `w2n k+d+r = w2n k+j` by (simp[Abbr `d`] >> decide_tac) >>
  `off+32+32*(i*type_slot_size t)+32*r = 32*j+off` by
    (qpat_x_assum `j = _` mp_tac >> simp_tac bool_ss [Abbr `d`] >> decide_tac) >>
  asm_simp_tac std_ss [w2n_n2w, LESS_MOD] >>
  (impl_tac >- (conj_tac >- decide_tac >>
     qpat_x_assum `~dead_bytes (apply_writes _ child _) _ _ _ _` mp_tac >>
     qpat_x_assum `j = _` (fn th => pure_rewrite_tac[th]) >>
     simp_tac bool_ss [ADD_ASSOC])) >> strip_tac >>
  qpat_x_assum `!x. _ <= x /\ _ ==> _` (qspec_then `w2n k+j` mp_tac) >>
  (impl_tac >- decide_tac) >> metis_tac[ADD_COMM]
QED
Finalise encode_value_memory_live

Theorem copy_fold_lookup[local]:
  !is addr f q w st.
    (!i. MEM i is /\ addr i = q ==> f i = w) ==>
    lookup_storage q (FOLDL (\t i. update_storage (addr i) (f i) t) st is) =
    if MEM q (MAP addr is) then w else lookup_storage q st
Proof
  Induct >> simp[] >> rpt strip_tac >>
  first_x_assum (qspecl_then [`addr`, `f`, `q`, `w`,
    `update_storage (addr h) (f h) st`] mp_tac) >>
  (impl_tac >- metis_tac[]) >> simp[] >> strip_tac >>
  asm_rewrite_tac[] >>
  Cases_on `MEM q (MAP addr is)` >> asm_rewrite_tac[] >>
  Cases_on `addr h = q` >>
  gvs[lookup_storage_def, update_storage_def, combinTheory.APPLY_UPDATE_THM]
QED

Theorem copy_fold_region[local]:
  !k n q ws st.
    w2n k+n <= dimword (:256) ==>
    lookup_storage q
      (FOLDL (\t i. update_storage (k+n2w i) (ws i) t)
        st (COUNT_LIST n)) =
    if w2n k <= w2n q /\ w2n q < w2n k+n then
      ws (w2n q-w2n k)
    else lookup_storage q st
Proof
  rpt strip_tac >>
  `!i. i < n ==> w2n (k+n2w i) = w2n k+i` by
    (rpt strip_tac >>
     `i < dimword (:256) /\ w2n k+i < dimword (:256)` by decide_tac >>
     simp[w2n_add_2, w2n_n2w, LESS_MOD]) >>
  `!i. i < n /\ k+n2w i = q ==> i = w2n q-w2n k` by
    (rpt strip_tac >> first_x_assum drule >> simp[] >> decide_tac) >>
  `MEM q (MAP (\i. k+n2w i) (COUNT_LIST n)) <=>
     w2n k <= w2n q /\ w2n q < w2n k+n` by
    (simp[MEM_MAP, MEM_COUNT_LIST] >> eq_tac
     >- (rpt strip_tac >> first_x_assum drule >> simp[] >> decide_tac) >>
     strip_tac >> qexists_tac `w2n q-w2n k` >>
     `w2n q-w2n k < n` by decide_tac >> asm_rewrite_tac[] >>
     once_rewrite_tac[GSYM w2n_11] >>
     qpat_x_assum `!i. i < n ==> w2n _ = _` drule >> simp[] >> decide_tac) >>
  irule EQ_TRANS >>
  qexists_tac `if MEM q (MAP (\i. k+n2w i) (COUNT_LIST n)) then
     ws (w2n q-w2n k) else lookup_storage q st` >>
  conj_tac >- (ho_match_mp_tac copy_fold_lookup >> simp[MEM_COUNT_LIST] >> metis_tac[]) >>
  asm_rewrite_tac[]
QED

Theorem copy_encoded_outside[local]:
  !tv v writes k st x.
    encode_value tv v = SOME writes /\ value_has_type tv v /\
    w2n k + type_slot_size tv <= dimword (:256) /\
    x < dimword (:256) /\
    ~(w2n k <= x /\ x < w2n k + type_slot_size tv) ==>
    lookup_storage (n2w x) (apply_writes k writes st) =
    lookup_storage (n2w x) st
Proof
  rpt strip_tac >>
  drule (cj 1 encode_writes_bounded) >> asm_rewrite_tac[] >> strip_tac >>
  irule copy_writes_frame >> qexistsl_tac [`x`, `1`] >> simp[] >>
  rpt strip_tac >>
  qpat_x_assum `!off. MEM off _ ==> _` drule >> strip_tac >> decide_tac
QED

Theorem copy_storage_dead_outside[local]:
  !cx tr mid n subs k tv v writes st x b.
    declared_storage_region cx mid n subs = SOME (tr,k,tv) /\
    w2n k + type_slot_size tv <= dimword (:256) /\
    encode_value tv v = SOME writes /\ value_has_type tv v /\
    ~(w2n k <= x /\ x < w2n k + type_slot_size tv) /\
    storage_dead cx tr st x b ==>
    storage_dead cx tr (apply_writes k writes st) x b
Proof
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `storage_dead _ _ _ _ _` mp_tac >>
  simp_tac bool_ss [storage_dead_def] >> strip_tac >>
  rename1 `dead_bytes st (w2n slot) t x b` >>
  Cases_on `(slot,t) = (k,tv)`
  >- (gvs[] >> drule (cj 1 dead_bytes_range) >> strip_tac >>
      `F` by decide_tac) >>
  `ranges_disjoint (w2n slot) (type_slot_size t)
      (w2n k) (type_slot_size tv)` by
    (qpat_x_assum `!mid' n' subs' slot' tv'. _` irule >>
     conj_tac >- metis_tac[] >>
     qexistsl_tac [`mid`, `n`, `subs`] >> simp[]) >>
  `dead_bytes (apply_writes k writes st) (w2n slot) t x b <=>
   dead_bytes st (w2n slot) t x b` by
    (irule (cj 1 dead_bytes_frame) >> rpt strip_tac >>
     irule copy_encoded_outside >> conj_tac >- decide_tac >>
     qexistsl_tac [`tv`, `v`] >> fs[ranges_disjoint_def] >> decide_tac) >>
  simp_tac bool_ss [storage_dead_def] >>
  qexistsl_tac [`mid'`, `n'`, `subs'`, `slot`, `t`] >> asm_rewrite_tac[]
QED

(* The source stores v at the declared region (k, tv) on backend tr; the
   Venom side copies v's memory words over the whole region.  If the
   storages agreed up to the dead bytes before, they agree after: inside the
   region by encode_value_memory_live, and outside it nothing changed and no
   byte changed whether it is dead, since every region with dead bytes is
   apart from (k, tv). *)
Theorem storage_agree_copy_region:
  !cx tr mid n subs k tv v writes off mem ws st1 st2.
    declared_storage_region cx mid n subs = SOME (tr, k, tv) /\
    w2n k + type_slot_size tv <= dimword (:256) /\
    (!mid' n' subs' k' tv'.
       declared_storage_region cx mid' n' subs' = SOME (tr, k', tv') /\
       (k', tv') <> (k, tv) ==>
       ranges_disjoint (w2n k) (type_slot_size tv)
                       (w2n k') (type_slot_size tv')) /\
    well_formed_type_value tv /\ value_has_type tv v /\
    val_in_memory tv v off mem /\
    encode_value tv v = SOME writes /\
    (!i. i < type_slot_size tv /\
         (?b. b < 32 /\
              ~dead_bytes (apply_writes k writes st1) (w2n k) tv (w2n k + i) b) ==>
         ws i = mem_word_at (off + 32 * i) mem) /\
    storage_agree (storage_dead cx tr st1) st1 st2 ==>
    storage_agree (storage_dead cx tr (apply_writes k writes st1))
      (apply_writes k writes st1)
      (FOLDL (\t i. update_storage (k + n2w i) (ws i) t)
             st2 (COUNT_LIST (type_slot_size tv)))
Proof
  rpt gen_tac >> strip_tac >>
  simp_tac bool_ss [storage_agree_def] >> rpt gen_tac >> strip_tac >>
  rename1 `~storage_dead cx tr (apply_writes k writes st1) (w2n q) b` >>
  `lookup_storage q
    (FOLDL (\t i. update_storage (k+n2w i) (ws i) t)
      st2 (COUNT_LIST (type_slot_size tv))) =
    if w2n k <= w2n q /\ w2n q < w2n k+type_slot_size tv then
      ws (w2n q-w2n k) else lookup_storage q st2` by
    (irule copy_fold_region >> simp[]) >>
  pop_assum SUBST1_TAC >>
  Cases_on `w2n k <= w2n q /\ w2n q < w2n k+type_slot_size tv` >>
  asm_rewrite_tac[]
  >- (`~dead_bytes (apply_writes k writes st1) (w2n k) tv (w2n q) b` by
        (strip_tac >> qpat_x_assum `~storage_dead _ _ _ _ _` mp_tac >>
         simp_tac bool_ss [storage_dead_def] >>
         qexistsl_tac [`mid`, `n`, `subs`, `k`, `tv`] >> asm_rewrite_tac[]) >>
      `w2n k+(w2n q-w2n k) = w2n q` by decide_tac >>
      `w2n q-w2n k < type_slot_size tv` by decide_tac >>
      `ws (w2n q-w2n k) = mem_word_at (off+32*(w2n q-w2n k)) mem` by
        (qpat_x_assum `!i. _ ==> ws i = _` irule >>
         reverse conj_tac >- asm_rewrite_tac[] >> qexists_tac `b` >> simp[]) >>
      asm_rewrite_tac[] >>
      drule encode_value_memory_live >>
      disch_then drule >> disch_then drule >> disch_then drule >>
      disch_then (qspecl_then [`k`, `st1`, `w2n q-w2n k`, `b`] mp_tac) >>
      simp[] ) >>
  `~storage_dead cx tr st1 (w2n q) b` by
    (strip_tac >> qpat_x_assum `~storage_dead _ _ (apply_writes _ _ _) _ _`
       (fn th => mp_tac th) >> simp[] >>
     irule copy_storage_dead_outside >> reverse conj_tac >- asm_rewrite_tac[] >>
     qexistsl_tac [`mid`, `n`, `subs`, `tv`, `v`] >> asm_rewrite_tac[]) >>
  `lookup_storage q (apply_writes k writes st1) = lookup_storage q st1` by
    (`lookup_storage (n2w (w2n q)) (apply_writes k writes st1) =
      lookup_storage (n2w (w2n q)) st1` suffices_by simp[] >>
     irule copy_encoded_outside >> conj_tac >- simp[w2n_lt] >>
     qexistsl_tac [`tv`, `v`] >> simp[]) >>
  asm_rewrite_tac[] >>
  qpat_x_assum `storage_agree _ _ _` mp_tac >>
  simp[storage_agree_def]
QED
