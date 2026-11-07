(*
 * Relating source encoding to memory words used by a storage copy.
 *
 * The source encoder writes sparse slots. Written slots agree with memory
 * at bytes observed by dead_bytes; unwritten slots retain their old storage
 * contents. Dynamic-array capacity slots remain observable even beyond the
 * current length, while bytestring padding can be masked.
 *
 * Main theorems:
 *   encode_value_memory_live  — observed bytes of an encoded slot agree
 *                               with the corresponding memory word
 *   storage_agree_copy_region — a bulk copy preserves storage agreement
 *                               when encoding covers every observed slot
 *)

Theory storageCopyLive
Ancestors
  valueEncodingProps vyperStorageCoverage
  list rich_list arithmetic words byte vfmTypes vfmState valueEncodingProofs
  compileEnv valueEncoding accountsRelProps exprSimAttributeFields
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

(* Select a nonempty child interval, retaining the surrounding writes. *)
Theorem copy_tuple_select[local]:
  !tvs vs offset off mem base st writes j b.
    values_have_types tvs vs /\ tuple_in_memory vs tvs off mem /\
    encode_tuple offset tvs vs = SOME writes /\
    j < type_slot_size_list tvs /\ MEM (offset+j) (MAP FST writes) /\
    ~dead_bytes_list st (base+offset) tvs (base+offset+j) b ==>
    ?tv v d child pre post.
      MEM tv tvs /\ value_has_type tv v /\
      d <= j /\ j < d+type_slot_size tv /\
      d+type_slot_size tv <= type_slot_size_list tvs /\
      val_in_memory tv v (off+32*d) mem /\ encode_value tv v = SOME child /\
      writes = pre ++ MAP (\(i,w). (i+(offset+d),w)) child ++ post /\
      (!i. MEM i (MAP FST post) ==>
        offset+d+type_slot_size tv <= i /\ i < offset+type_slot_size_list tvs) /\
      ~dead_bytes st (base+offset+d) tv (base+offset+j) b /\
      MEM (j-d) (MAP FST child)
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
  gnvs[Once dead_bytes_def] >>
  Cases_on `j < type_slot_size hd`
  >- suspend "head"
  >> suspend "tail"
QED

Resume copy_tuple_select[head]:
  `MEM j (MAP FST hdws)` by
    (gvs[MEM_MAP, pairTheory.EXISTS_PROD]
     >- metis_tac[ADD_COMM, EQ_ADD_RCANCEL] >>
     drule (cj 2 encode_writes_bounded) >> asm_rewrite_tac[] >>
     disch_then (qspec_then `j+offset` mp_tac) >>
     (impl_tac >- (simp[MEM_MAP, pairTheory.EXISTS_PROD] >> metis_tac[])) >>
     strip_tac >> `F` by decide_tac) >>
  qexistsl_tac [`hd`, `vhd`, `0`, `hdws`, `[]`, `tailws`] >> simp[] >>
  drule (cj 2 encode_writes_bounded) >> asm_rewrite_tac[] >>
  pure_rewrite_tac[ADD_ASSOC] >> simp_tac bool_ss []
QED
Resume copy_tuple_select[tail]:
  `MEM (j+offset) (MAP FST tailws)` by
    (qpat_x_assum `_ \/ MEM _ _` strip_assume_tac >- (
       `MEM j (MAP FST hdws)` by
         (gvs[MEM_MAP, pairTheory.EXISTS_PROD] >>
          metis_tac[ADD_COMM, EQ_ADD_RCANCEL]) >>
       drule (cj 1 encode_writes_bounded) >> asm_rewrite_tac[] >>
       disch_then (qspec_then `j` mp_tac) >> simp[]) >> simp[]) >>
  `MEM (j-type_slot_size hd+(offset+type_slot_size hd)) (MAP FST tailws)` by
    (`j-type_slot_size hd+(offset+type_slot_size hd) = j+offset` by decide_tac >> simp[]) >>
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
    j < type_slot_size_fields ftypes /\ MEM (offset+j) (MAP FST writes) /\
    ~dead_bytes_fields st (base+offset) ftypes (base+offset+j) b ==>
    ?tv v d child pre post.
      MEM tv (MAP SND ftypes) /\ value_has_type tv v /\
      d <= j /\ j < d+type_slot_size tv /\
      d+type_slot_size tv <= type_slot_size_fields ftypes /\
      val_in_memory tv v (off+32*d) mem /\ encode_value tv v = SOME child /\
      writes = pre ++ MAP (\(i,w). (i+(offset+d),w)) child ++ post /\
      (!i. MEM i (MAP FST post) ==>
        offset+d+type_slot_size tv <= i /\ i < offset+type_slot_size_fields ftypes) /\
      ~dead_bytes st (base+offset+d) tv (base+offset+j) b /\
      MEM (j-d) (MAP FST child)
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
  gnvs[Once dead_bytes_def, type_slot_size_def] >>
  Cases_on `j < type_slot_size hd`
  >- suspend "head"
  >> suspend "tail"
QED

Resume copy_struct_select[head]:
  `MEM j (MAP FST hdws)` by
    (gvs[MEM_MAP, pairTheory.EXISTS_PROD]
     >- metis_tac[ADD_COMM, EQ_ADD_RCANCEL] >>
     drule (cj 5 encode_writes_bounded) >> asm_rewrite_tac[] >>
     disch_then (qspec_then `j+offset` mp_tac) >>
     (impl_tac >- (simp[MEM_MAP, pairTheory.EXISTS_PROD] >> metis_tac[])) >>
     strip_tac >> `F` by decide_tac) >>
  qexistsl_tac [`hd`, `vhd`, `0`, `hdws`, `[]`, `tailws`] >> simp[] >>
  drule (cj 5 encode_writes_bounded) >> asm_rewrite_tac[] >>
  pure_rewrite_tac[ADD_ASSOC] >> simp_tac bool_ss []
QED
Resume copy_struct_select[tail]:
  `MEM (j+offset) (MAP FST tailws)` by
    (qpat_x_assum `_ \/ MEM _ _` strip_assume_tac >- (
       `MEM j (MAP FST hdws)` by
         (gvs[MEM_MAP, pairTheory.EXISTS_PROD] >>
          metis_tac[ADD_COMM, EQ_ADD_RCANCEL]) >>
       drule (cj 1 encode_writes_bounded) >> asm_rewrite_tac[] >>
       disch_then (qspec_then `j` mp_tac) >> simp[]) >> simp[]) >>
  `MEM (j-type_slot_size hd+(offset+type_slot_size hd)) (MAP FST tailws)` by
    (`j-type_slot_size hd+(offset+type_slot_size hd) = j+offset` by decide_tac >> simp[]) >>
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

Theorem copy_sparse_write_owner[local]:
  !sparse tv offset writes n x.
    sparse_has_type tv n sparse /\
    encode_static_array tv offset sparse = SOME writes /\
    MEM x (MAP FST writes) ==>
    ?i r v child. MEM (i,v) sparse /\ MEM i (MAP FST sparse) /\
      encode_value tv v = SOME child /\ MEM r (MAP FST child) /\
      r < type_slot_size tv /\ x = offset+i*type_slot_size tv+r
Proof
  Induct >> simp[Once encode_value_def] >> Cases >> rename1 `(i0,hv)::sparse` >>
  rpt gen_tac >> simp[value_has_type_def] >> rpt strip_tac >>
  qpat_x_assum `encode_static_array _ _ _ = _` mp_tac >>
  simp[Once encode_value_def, AllCaseEqs()] >> strip_tac >>
  rename1 `encode_value tv hv = SOME hdws` >>
  rename1 `encode_static_array tv offset sparse = SOME tailws` >>
  gvs[MAP_APPEND, MEM_APPEND, MEM_MAP, pairTheory.EXISTS_PROD]
  >- (rename1 `MEM (r,w) hdws` >>
      `MEM r (MAP FST hdws)` by (simp[MEM_MAP, pairTheory.EXISTS_PROD] >> metis_tac[]) >>
      drule_all (cj 1 encode_writes_bounded) >> strip_tac >>
      qexistsl_tac [`i0`, `r`, `hv`, `hdws`] >> simp[] >> metis_tac[]) >>
  first_x_assum drule >> disch_then drule >>
  disch_then (qspec_then `x` mp_tac) >>
  (impl_tac >- metis_tac[]) >> strip_tac >>
  qexistsl_tac [`i`, `r`, `v`, `child`] >> simp[] >> metis_tac[]
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
  drule_all copy_sparse_write_owner >>
  disch_then (qx_choosel_then [`i2`, `r2`, `v2`, `child2`] strip_assume_tac) >>
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

(* A payload hit supplies activity independently of the dead-byte mask. *)
Theorem copy_dyn_written_index[local]:
  !tv vs offset writes i r.
    all_have_type tv vs /\ encode_dyn_array tv offset vs = SOME writes /\
    MEM (offset+i*type_slot_size tv+r) (MAP FST writes) ==>
    i < LENGTH vs
Proof
  rpt strip_tac >>
  drule (cj 4 encode_writes_bounded) >> asm_rewrite_tac[] >>
  disch_then (qspec_then `offset+i*type_slot_size tv+r` mp_tac) >>
  simp[] >> strip_tac >>
  `i*type_slot_size tv < LENGTH vs*type_slot_size tv` by decide_tac >>
  fs[LT_MULT_RCANCEL]
QED

(* Dynamic payload selection retains the suffix's lower bound. *)
Theorem copy_dyn_select[local]:
  !vs tv offset off mem writes i r.
    all_have_type tv vs /\ elems_in_memory vs off tv mem /\
    encode_dyn_array tv offset vs = SOME writes /\ i < LENGTH vs /\
    r < type_slot_size tv /\
    MEM (offset+i*type_slot_size tv+r) (MAP FST writes) ==>
    ?v child pre post.
      value_has_type tv v /\
      val_in_memory tv v (off+32*(i*type_slot_size tv)) mem /\
      encode_value tv v = SOME child /\
      writes = pre ++ MAP (\(j,w). (j+(offset+i*type_slot_size tv),w)) child ++ post /\
      (!j. MEM j (MAP FST post) ==>
        offset+(i+1)*type_slot_size tv <= j /\
        j < offset+LENGTH vs*type_slot_size tv) /\
      MEM r (MAP FST child)
Proof
  Induct >> simp[] >> rpt gen_tac >>
  simp[value_has_type_def, val_in_memory_def] >> rpt strip_tac >>
  qpat_x_assum `encode_dyn_array _ _ _ = _` mp_tac >>
  simp[Once encode_value_def, AllCaseEqs()] >> strip_tac >>
  rename1 `encode_value tv h = SOME hdws` >>
  rename1 `encode_dyn_array tv (offset+type_slot_size tv) vs = SOME tailws` >>
  Cases_on `i`
  >- (`MEM r (MAP FST hdws)` by
        (gvs[MEM_MAP, pairTheory.EXISTS_PROD]
         >- metis_tac[ADD_COMM, EQ_ADD_RCANCEL] >>
         drule (cj 4 encode_writes_bounded) >> asm_rewrite_tac[] >>
         disch_then (qspec_then `offset+r` mp_tac) >>
         (impl_tac >- (simp[MEM_MAP, pairTheory.EXISTS_PROD] >> metis_tac[])) >>
         strip_tac >> `F` by decide_tac) >>
      qexistsl_tac [`h`, `hdws`, `[]`, `tailws`] >> simp[] >>
      drule (cj 4 encode_writes_bounded) >> asm_rewrite_tac[] >>
      rpt strip_tac >> first_x_assum drule >> strip_tac >>
      simp[MULT_CLAUSES] >> decide_tac) >>
  rename1 `SUC ix < SUC (LENGTH vs)` >>
  `ix < LENGTH vs` by decide_tac >>
  `MEM (offset+type_slot_size tv+ix*type_slot_size tv+r) (MAP FST tailws)` by
    (gvs[MEM_MAP, pairTheory.EXISTS_PROD]
     >- (`MEM (r+SUC ix*type_slot_size tv) (MAP FST hdws)` by
           (simp[MEM_MAP, pairTheory.EXISTS_PROD] >> metis_tac[]) >>
         drule (cj 1 encode_writes_bounded) >> asm_rewrite_tac[] >>
         disch_then (qspec_then `r+SUC ix*type_slot_size tv` mp_tac) >>
         simp[MULT_CLAUSES] >> strip_tac >> `F` by decide_tac) >>
     fs[MULT_CLAUSES] >> metis_tac[]) >>
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

(* Structural default blocks retain the identity of their array element. *)
Theorem copy_default_block_key[local]:
  !n start tv defaults sparse x.
    (!r. MEM r (MAP FST defaults) ==> r < type_slot_size tv) /\
    MEM x (MAP FST (FLAT (GENLIST (\h.
      if MEM (start+h) (MAP FST sparse) then []
      else MAP (\(r,w). (r+(start+h)*type_slot_size tv,w)) defaults) n))) ==>
    ?h r. h < n /\ ~MEM (start+h) (MAP FST sparse) /\
      MEM r (MAP FST defaults) /\ r < type_slot_size tv /\
      x = (start+h)*type_slot_size tv+r
Proof
  rpt gen_tac >> strip_tac >>
  gvs[MEM_MAP, pairTheory.EXISTS_PROD, MEM_FLAT, MEM_GENLIST] >>
  qpat_x_assum `MEM _ (if _ then _ else _)` mp_tac >>
  IF_CASES_TAC >> simp[MEM_MAP, pairTheory.EXISTS_PROD] >>
  strip_tac >> metis_tac[ADD_COMM]
QED

Theorem copy_default_block_select[local]:
  !tv defaults sparse n i.
    (!r. MEM r (MAP FST defaults) ==> r < type_slot_size tv) /\
    i < n /\ ~MEM i (MAP FST sparse) ==>
    ?pre post.
      FLAT (GENLIST (\h. if MEM h (MAP FST sparse) then []
        else MAP (\(r,w). (r+h*type_slot_size tv,w)) defaults) n) =
        pre ++ MAP (\(r,w). (r+i*type_slot_size tv,w)) defaults ++ post /\
      (!x. MEM x (MAP FST pre) ==> x < i*type_slot_size tv) /\
      (!x. MEM x (MAP FST post) ==>
        (i+1)*type_slot_size tv <= x /\ x < n*type_slot_size tv)
Proof
  rpt gen_tac >> strip_tac >>
  qabbrev_tac `f = \h. if MEM h (MAP FST sparse) then []
        else MAP (\(r,w). (r+h*type_slot_size tv,w)) defaults` >>
  qexistsl_tac [`FLAT (TAKE i (GENLIST f n))`,
                `FLAT (DROP (SUC i) (GENLIST f n))`] >>
  conj_tac
  >- (qspec_then `GENLIST f n` mp_tac (Q.SPEC `i` rich_listTheory.TAKE_DROP_SUC) >>
      simp[] >> strip_tac >>
      `f i = MAP (\(r,w). (r+i*type_slot_size tv,w)) defaults` by simp[Abbr `f`] >>
      qpat_x_assum `_ = GENLIST f n`
        (fn th => simp[Once (GSYM th), SimpLHS, FLAT_APPEND]) >>
      simp[]) >>
  conj_tac
  >- suspend "prefix"
  >> suspend "suffix"
QED
Resume copy_default_block_select[prefix]:
  simp[TAKE_GENLIST, MIN_DEF] >> rpt strip_tac >>
  gvs[MEM_MAP, pairTheory.EXISTS_PROD, MEM_FLAT, MEM_GENLIST] >>
  qpat_x_assum `MEM _ (f _)` mp_tac >>
  simp[Abbr `f`] >> IF_CASES_TAC >>
  simp[MEM_MAP, pairTheory.EXISTS_PROD] >> strip_tac >>
  `p_1 < type_slot_size tv` by metis_tac[] >>
  `(m+1)*type_slot_size tv <= i*type_slot_size tv` by simp[LE_MULT_RCANCEL] >>
  qpat_x_assum `(m+1)*_ <= _` mp_tac >>
  pure_rewrite_tac[RIGHT_ADD_DISTRIB, MULT_CLAUSES] >> decide_tac
QED
Resume copy_default_block_select[suffix]:
  simp[DROP_GENLIST] >> gen_tac >> disch_tac >>
  gvs[MEM_MAP, pairTheory.EXISTS_PROD, MEM_FLAT, MEM_GENLIST] >>
  qpat_x_assum `MEM _ (f _)` mp_tac >>
  simp[Abbr `f`] >> IF_CASES_TAC >>
  simp[MEM_MAP, pairTheory.EXISTS_PROD] >> strip_tac >>
  `p_1 < type_slot_size tv` by metis_tac[] >>
  `type_slot_size tv*(i+1) <= type_slot_size tv*(m+SUC i)` by simp[LE_MULT_LCANCEL] >>
  `type_slot_size tv*(m+SUC i+1) <= type_slot_size tv*n` by simp[LE_MULT_LCANCEL] >>
  rule_assum_tac (PURE_REWRITE_RULE [LEFT_ADD_DISTRIB, MULT_CLAUSES]) >>
  pure_rewrite_tac[LEFT_ADD_DISTRIB, MULT_CLAUSES] >>
  once_rewrite_tac[MULT_COMM] >>
  rule_assum_tac (ONCE_REWRITE_RULE [MULT_COMM]) >> decide_tac
QED
Finalise copy_default_block_select

Theorem copy_default_block_member[local]:
  !tv defaults sparse n i r.
    (!q. MEM q (MAP FST defaults) ==> q < type_slot_size tv) /\
    i < n /\ r < type_slot_size tv /\
    MEM (i*type_slot_size tv+r)
      (MAP FST (FLAT (GENLIST (\h. if MEM h (MAP FST sparse) then []
        else MAP (\(q,w). (q+h*type_slot_size tv,w)) defaults) n))) ==>
    ~MEM i (MAP FST sparse) /\ MEM r (MAP FST defaults)
Proof
  rpt gen_tac >> strip_tac >>
  drule_all (SRULE [ADD_CLAUSES] (Q.SPECL [`n`, `0`] copy_default_block_key)) >>
  strip_tac >>
  `(i*type_slot_size tv+r) DIV type_slot_size tv = i` by
    (irule DIV_UNIQUE >> qexists_tac `r` >> simp[]) >>
  `(i*type_slot_size tv+r) DIV type_slot_size tv = h` by
    (irule DIV_UNIQUE >> qexists_tac `r''` >> simp[]) >>
  gvs[]
QED

Theorem copy_fixed_written_select[local]:
  !tv defaults sparse n off mem explicit writes i r.
    well_formed_type_value tv /\ sparse_has_type tv n sparse /\
    SORTED $< (MAP FST sparse) /\ kvs_in_memory sparse off tv mem /\
    (!h. h<n /\ ALOOKUP sparse h=NONE ==>
      val_in_memory tv (default_value tv) (off+h*type_memory_size tv) mem) /\
    encode_value tv (default_value tv)=SOME defaults /\
    encode_static_array tv 0 sparse=SOME explicit /\
    writes=FLAT (GENLIST (\h. if MEM h (MAP FST sparse) then []
        else MAP (\(q,w). (q+h*type_slot_size tv,w)) defaults) n) ++ explicit /\
    i<n /\ r<type_slot_size tv /\ MEM (i*type_slot_size tv+r) (MAP FST writes) ==>
    ?v child pre post.
      value_has_type tv v /\
      val_in_memory tv v (off+32*(i*type_slot_size tv)) mem /\
      encode_value tv v=SOME child /\ MEM r (MAP FST child) /\
      writes=pre++MAP (\(q,w). (q+i*type_slot_size tv,w)) child++post /\
      (!q. MEM q (MAP FST post) ==> q<n*type_slot_size tv /\
        (q<i*type_slot_size tv \/ (i+1)*type_slot_size tv<=q))
Proof
  rpt gen_tac >> strip_tac >>
  `!q. MEM q (MAP FST defaults) ==> q < type_slot_size tv` by
    (qspec_then `tv` assume_tac default_value_well_typed >>
     drule (cj 1 encode_writes_bounded) >> asm_rewrite_tac[]) >>
  Cases_on `ALOOKUP sparse i`
  >- suspend "absent"
  >> suspend "present"
QED
Resume copy_fixed_written_select[absent]:
  `~MEM i (MAP FST sparse)` by gvs[alistTheory.ALOOKUP_NONE] >>
  drule_all copy_default_block_select >> strip_tac >>
  qexistsl_tac [`default_value tv`, `defaults`, `pre`, `post++explicit`] >>
  simp[default_value_well_typed, APPEND_ASSOC] >>
  conj_tac
  >- (`off+32*(i*type_slot_size tv) = off+i*type_memory_size tv` by
        simp_tac std_ss [type_memory_size_slots, MULT_ASSOC, MULT_COMM] >> metis_tac[]) >>
  conj_tac
  >- (qpat_x_assum `MEM _ (MAP FST writes)` mp_tac >>
      qpat_x_assum `writes = _` (fn th => pure_rewrite_tac[th, MAP_APPEND, MEM_APPEND]) >>
      strip_tac
      >- (drule_all copy_default_block_member >> simp[]) >>
      drule_all copy_sparse_write_owner >> strip_tac >>
      rename1 `MEM h (MAP FST sparse)` >>
      rename1 `i*type_slot_size tv+r = 0+h*type_slot_size tv+rr` >>
      `(i*type_slot_size tv+r) DIV type_slot_size tv = i` by
        (irule DIV_UNIQUE >> qexists_tac `r` >> simp[]) >>
      `(i*type_slot_size tv+r) DIV type_slot_size tv = h` by
        (irule DIV_UNIQUE >> qexists_tac `rr` >> simp[]) >> gvs[]) >>
  rpt gen_tac >> strip_tac
  >- (first_x_assum drule >> simp[MULT_COMM]) >>
  drule_all copy_sparse_write_owner >> strip_tac >>
  conj_tac
  >- (drule_all (cj 3 encode_writes_bounded) >> simp[]) >>
  `i' <> i` by metis_tac[] >>
  Cases_on `i' < i`
  >- (disj1_tac >>
      `(i'+1)*type_slot_size tv <= i*type_slot_size tv` by simp[LE_MULT_RCANCEL] >>
      qpat_x_assum `(i'+1)*_ <= _` mp_tac >>
      pure_rewrite_tac[RIGHT_ADD_DISTRIB, MULT_CLAUSES] >> decide_tac) >>
  disj2_tac >>
  `type_slot_size tv*(i+1) <= type_slot_size tv*i'` by simp[LE_MULT_LCANCEL] >>
  pop_assum mp_tac >> once_rewrite_tac[MULT_COMM] >> decide_tac
QED
Resume copy_fixed_written_select[present]:
  `MEM i (MAP FST sparse)` by
    (drule alistTheory.ALOOKUP_MEM >> simp[MEM_MAP, pairTheory.EXISTS_PROD] >> metis_tac[]) >>
  `MEM (i*type_slot_size tv+r) (MAP FST explicit)` by
    (qpat_x_assum `MEM _ (MAP FST writes)` mp_tac >>
     qpat_x_assum `writes = _` (fn th => pure_rewrite_tac[th, MAP_APPEND, MEM_APPEND]) >>
     strip_tac >> simp[] >> drule_all copy_default_block_member >> simp[]) >>
  drule_all copy_sparse_write_owner >> strip_tac >>
  rename1 `MEM (h,v) sparse` >>
  rename1 `i*type_slot_size tv+r = 0+h*type_slot_size tv+rr` >>
  `(i*type_slot_size tv+r) DIV type_slot_size tv = i` by
    (irule DIV_UNIQUE >> qexists_tac `r` >> simp[]) >>
  `(i*type_slot_size tv+r) DIV type_slot_size tv = h` by
    (irule DIV_UNIQUE >> qexists_tac `rr` >> simp[]) >>
  `h=i` by decide_tac >>
  qpat_x_assum `MEM _ (MAP FST writes)` kall_tac >> gvs[] >>
  drule_all copy_sparse_select >> strip_tac >>
  `child'=child` by metis_tac[optionTheory.SOME_11] >>
  qmatch_goalsub_abbrev_tac `defs ++ explicit` >>
  qexistsl_tac [`v`, `child`, `defs++pre`, `post`] >>
  simp[APPEND_ASSOC] >> rpt strip_tac >> first_x_assum drule >> simp[MULT_COMM]
QED
Finalise copy_fixed_written_select

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
    ?i r. i < n /\
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
Theorem copy_selected_storage_outside[local]:
  !writes pre child post k st d tv total j b.
    writes = pre ++ MAP (\(i,w). (i+d,w)) child ++ post /\
    d <= j /\ j < d+type_slot_size tv /\
    d+type_slot_size tv <= total /\ w2n k+total <= dimword (:256) /\
    (!i. MEM i (MAP FST post) ==>
      i < total /\ (i < d \/ d+type_slot_size tv <= i)) /\
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

(* An observed byte agrees with memory when its slot occurs in the source
   encoding. No claim is made about retained, unwritten storage slots. *)
Theorem encode_value_memory_live:
  !tv v off mem k writes st j b.
    well_formed_type_value tv /\ value_has_type tv v /\
    val_in_memory tv v off mem /\
    encode_value tv v = SOME writes /\
    w2n k + type_slot_size tv <= dimword (:256) /\
    j < type_slot_size tv /\ b < 32 /\
    MEM j (MAP FST writes) /\
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
  Cases_on `b` >> gvs[]
  >>~- ([`BytesT bd`], Cases_on `bd` >> gvs[] >>
    rpt strip_tac >>
    qpat_x_assum `encode_value _ _ = _` mp_tac >>
    simp[Once encode_value_def, AllCaseEqs()] >> strip_tac >>
    gvs[type_slot_size_def] >>
    `mem_word_at off mem = slot` by metis_tac[copy_primitive_memory_word] >>
    simp[apply_writes_def, lookup_storage_def, update_storage_def,
         combinTheory.APPLY_UPDATE_THM]) >>
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
  qpat_x_assum `value_has_type _ _` mp_tac >>
  simp[Once value_has_type_def] >> strip_tac >>
  rename1 `ArrayV av` >> Cases_on `av` >>
  qpat_x_assum `value_has_type _ _` mp_tac >>
  simp[Once value_has_type_def, AllCaseEqs()] >> strip_tac >>
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
  `!h. MEM h (MAP FST post) ==>
    h < type_slot_size_list l /\ (h < d \/ d+type_slot_size tv <= h)` by metis_tac[] >>
  drule_all copy_selected_storage_outside >> strip_tac >>
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
  simp[Once value_has_type_def, AllCaseEqs()] >> strip_tac >>
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
  `!h. MEM h (MAP FST post) ==>
    h < type_slot_size_fields l /\ (h < d \/ d+type_slot_size tv <= h)` by metis_tac[] >>
  drule_all copy_selected_storage_outside >> strip_tac >>
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
  qpat_x_assum `value_has_type _ _` mp_tac >>
  simp[Once value_has_type_def] >> strip_tac >>
  rename1 `ArrayV av` >> Cases_on `av` >>
  qpat_x_assum `value_has_type _ _` mp_tac >>
  simp[Once value_has_type_def, AllCaseEqs()] >> strip_tac >>
  qpat_x_assum `val_in_memory _ _ _ _` mp_tac >>
  simp[Once val_in_memory_def] >> strip_tac >>
  qpat_x_assum `encode_value _ _ = _` mp_tac >>
  simp[Once encode_value_def, AllCaseEqs()] >> strip_tac >>
  `j < n*type_slot_size t` by fs[type_slot_size_def] >>
  drule_all copy_static_live_index >> strip_tac >>
  `well_formed_type_value t` by fs[well_formed_type_value_def] >>
  `MEM (i*type_slot_size t+r) (MAP FST writes)` by metis_tac[] >>
  qpat_x_assum `_ ++ nonzeros = writes` (assume_tac o SYM) >>
  drule_all copy_fixed_written_select >> strip_tac >>
  `w2n k+n*type_slot_size t <= dimword (:256)` by fs[type_slot_size_def] >>
  `i*type_slot_size t <= j /\ j < i*type_slot_size t+type_slot_size t` by decide_tac >>
  `i*type_slot_size t+type_slot_size t <= n*type_slot_size t` by
    (`(i+1)*type_slot_size t <= n*type_slot_size t` by simp[LE_MULT_RCANCEL] >>
     pop_assum (mp_tac o PURE_REWRITE_RULE [RIGHT_ADD_DISTRIB, MULT_CLAUSES]) >>
     decide_tac) >>
  `!h. MEM h (MAP FST post) ==>
       h < n*type_slot_size t /\
       (h < i*type_slot_size t \/ i*type_slot_size t+type_slot_size t <= h)` by
    (rpt strip_tac >> first_x_assum drule >> simp[LEFT_ADD_DISTRIB]) >>
  drule_all copy_selected_storage_outside >> strip_tac >>
  `type_value_size t < type_value_size (ArrayTV t (Fixed n))` by simp[] >>
  qpat_x_assum `!y. type_value_size y < _ ==> _` drule >>
  disch_then (qspecl_then [`v`, `off+32*(i*type_slot_size t)`, `mem`,
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
  qpat_x_assum `value_has_type _ _` mp_tac >>
  simp[Once value_has_type_def] >> strip_tac >>
  rename1 `ArrayV av` >> Cases_on `av` >>
  qpat_x_assum `value_has_type _ _` mp_tac >>
  simp[Once value_has_type_def, AllCaseEqs()] >> strip_tac >>
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
  `MEM (1+i*type_slot_size t+r) (MAP FST slots)` by
    (qpat_x_assum `MEM j (MAP FST writes)` mp_tac >>
     qpat_x_assum `_::slots = writes` (SUBST1_TAC o SYM) >>
     simp[MAP, MEM]) >>
  `i < LENGTH l` by (drule_all copy_dyn_written_index >> simp[]) >>
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
  `!h. MEM h (MAP FST post) ==>
    h < 1+LENGTH l*type_slot_size t /\ (h < d \/ d+type_slot_size t <= h)` by metis_tac[] >>
  drule_all copy_selected_storage_outside >> strip_tac >>
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
    (!i b. i < type_slot_size tv /\ b < 32 /\
       ~dead_bytes (apply_writes k writes st1) (w2n k) tv (w2n k + i) b ==>
       MEM i (MAP FST writes)) /\
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
      `MEM (w2n q-w2n k) (MAP FST writes)` by
        (qpat_x_assum `!i b. _ ==> MEM i _` irule >>
         reverse conj_tac >- simp[] >> qexists_tac `b` >> simp[]) >>
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
