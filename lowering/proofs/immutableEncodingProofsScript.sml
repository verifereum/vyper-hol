Theory immutableEncodingProofs
Ancestors
  immutableEncoding valueEncoding

Theorem immutable_fit_exact:
  LENGTH bs = n ==> immutable_fit n bs = bs
Proof
  simp[immutable_fit_def, listTheory.TAKE_APPEND1]
QED

Theorem immutable_word_bytes_length[simp]:
  LENGTH (immutable_word_bytes w) = 32
Proof
  simp[immutable_word_bytes_def, byteTheory.LENGTH_word_to_bytes,
       fcpLib.INDEX_CONV ``dimindex(:256)``]
QED

Theorem immutable_word_bytes_decode[simp]:
  word_of_bytes T (0w:bytes32) (immutable_word_bytes w) = w
Proof
  simp[immutable_word_bytes_def, byteTheory.word_of_bytes_word_to_bytes,
       fcpLib.INDEX_CONV ``dimindex(:256)``, dividesTheory.compute_divides]
QED

Theorem immutable_bytes_context:
  n <= LENGTH bs ==>
  mem_bytes_at (LENGTH pre) n (pre ++ bs ++ post) = TAKE n bs
Proof
  simp[mem_bytes_at_def, listTheory.DROP_APPEND, listTheory.TAKE_APPEND1]
QED

Theorem immutable_word_context:
  mem_word_at (LENGTH pre) (pre ++ immutable_word_bytes w ++ post) = w
Proof
  simp[mem_word_at_def, listTheory.DROP_APPEND, listTheory.TAKE_APPEND1] >>
  `TAKE 32 (immutable_word_bytes w) = immutable_word_bytes w` by
    metis_tac[listTheory.TAKE_LENGTH_ID_rwt, immutable_word_bytes_length] >>
  simp[]
QED

Theorem immutable_fit_padding:
  LENGTH bs <= n ==>
  immutable_fit n bs = bs ++ REPLICATE (n - LENGTH bs) 0w
Proof
  strip_tac >>
  simp[immutable_fit_def, rich_listTheory.TAKE_APPEND,
       listTheory.TAKE_LENGTH_TOO_LONG, rich_listTheory.REPLICATE_GENLIST,
       listTheory.TAKE_GENLIST] >> AP_TERM_TAC >>
  simp[arithmeticTheory.MIN_DEF] >> decide_tac
QED

Theorem immutable_word_fit:
  immutable_fit 32 (immutable_word_bytes w) = immutable_word_bytes w
Proof
  irule immutable_fit_exact >> simp[]
QED

Theorem immutable_bytes_payload_context:
  mem_bytes_at (LENGTH pre + 32) (LENGTH bs)
    (pre ++ immutable_word_bytes w ++ bs ++ post) = bs
Proof
  `LENGTH pre + 32 = LENGTH (pre ++ immutable_word_bytes w)` by simp[] >>
  pop_assum SUBST1_TAC >>
  metis_tac[immutable_bytes_context, listTheory.APPEND_ASSOC,
            listTheory.TAKE_LENGTH_ID, arithmeticTheory.LESS_EQ_REFL]
QED

Theorem immutable_capacity_roundup:
  n <= 32 * word_size n
Proof
  simp[vfmConstantsTheory.word_size_def] >>
  qspec_then `n + 31` mp_tac (SRULE [] (Q.SPEC `32` arithmeticTheory.DIVISION)) >>
  ` (n + 31) MOD 32 < 32` by simp[] >> decide_tac
QED

Theorem immutable_payload_decodes:
  LENGTH bs <= 32 * word_size n ==>
  mem_word_at (LENGTH pre)
    (pre ++ immutable_fit (32 + 32 * word_size n)
      (immutable_word_bytes w ++ bs) ++ post) = w /\
  mem_bytes_at (LENGTH pre + 32) (LENGTH bs)
    (pre ++ immutable_fit (32 + 32 * word_size n)
      (immutable_word_bytes w ++ bs) ++ post) = bs
Proof
  strip_tac >>
  simp[immutable_fit_padding] >>
  conj_tac
  >- (simp[mem_word_at_def, listTheory.DROP_APPEND, listTheory.TAKE_APPEND1,
           listTheory.TAKE_LENGTH_ID_rwt]) >>
  simp[mem_bytes_at_def, listTheory.DROP_APPEND, listTheory.TAKE_APPEND1,
       listTheory.DROP_LENGTH_TOO_LONG] >>
  `DROP 32 (immutable_word_bytes w) = []` by
    metis_tac[listTheory.DROP_LENGTH_NIL, immutable_word_bytes_length] >> simp[]
QED

Theorem immutable_base_decodes:
  immutable_value_admissible (BaseTV bt) v ==>
  val_in_memory (BaseTV bt) v (LENGTH pre)
    (pre ++ encode_immutable_value (BaseTV bt) v ++ post)
Proof
  Cases_on `bt` >> Cases_on `v` >>
  simp[immutable_value_admissible_def, encode_immutable_value_def,
       type_memory_size_def, immutable_word_fit, val_in_memory_def,
       typed_val_to_w256_def, immutable_word_context]
  >- (strip_tac >>
      `LENGTH (MAP (n2w o ORD) s : word8 list) <= 32 * word_size n` by
        (simp[] >> metis_tac[immutable_capacity_roundup, arithmeticTheory.LESS_EQ_TRANS]) >>
      drule immutable_payload_decodes >>
      disch_then (qspecl_then [`n2w (LENGTH s)`, `pre`, `post`] mp_tac) >>
      simp[]) >>
  Cases_on `b` >>
  simp[type_memory_size_def, immutable_word_fit, immutable_word_context] >>
  strip_tac >>
  `LENGTH l <= 32 * word_size n` by
    metis_tac[immutable_capacity_roundup, arithmeticTheory.LESS_EQ_TRANS] >>
  drule immutable_payload_decodes >>
  disch_then (qspecl_then [`n2w (LENGTH l)`, `pre`, `post`] mp_tac) >> simp[]
QED

Theorem immutable_tuple_length[simp]:
  !tvs vs. LENGTH (encode_immutable_tuple tvs vs) = type_memory_size_list tvs
Proof
  Induct >> Cases_on `vs` >> simp[encode_immutable_value_def, type_memory_size_def]
QED

Theorem immutable_fields_length[simp]:
  !fts vs. LENGTH (encode_immutable_fields fts vs) = type_memory_size_fields fts
Proof
  Induct >- simp[encode_immutable_value_def, type_memory_size_def] >>
  Cases_on `h` >> Cases_on `vs` >>
  simp[encode_immutable_value_def, type_memory_size_def] >>
  Cases_on `h` >> simp[encode_immutable_value_def, type_memory_size_def]
QED

Theorem immutable_elems_context:
  !vs. (!v. MEM v vs ==> !pre post.
     val_in_memory tv v (LENGTH pre) (pre ++ encode_immutable_value tv v ++ post)) ==>
  !pre post. elems_in_memory vs (LENGTH pre) tv
    (pre ++ FLAT (MAP (encode_immutable_value tv) vs) ++ post)
Proof
  Induct >> simp[val_in_memory_def] >> rpt strip_tac >>
  metis_tac[listTheory.APPEND_ASSOC, listTheory.LENGTH_APPEND,
            encode_immutable_value_length]
QED

Theorem immutable_flat_slot:
  !bss i. EVERY (\bs. LENGTH bs = sz) bss /\ i < LENGTH bss ==>
    ?pre post. FLAT bss = pre ++ EL i bss ++ post /\ LENGTH pre = i * sz
Proof
  Induct >- simp[] >> Cases_on `i`
  >- (simp[] >> rpt strip_tac >> qexistsl [`[]`, `FLAT bss`] >> simp[]) >>
  simp[] >> rpt strip_tac >> first_x_assum drule >>
  disch_then (qspec_then `n` mp_tac) >> simp[] >> strip_tac >>
  qexistsl [`h ++ pre`, `post`] >>
  simp[listTheory.APPEND_ASSOC, arithmeticTheory.MULT_CLAUSES]
QED

Theorem immutable_flat_map_length:
  !vs. LENGTH (FLAT (MAP (encode_immutable_value tv) vs)) =
       LENGTH vs * type_memory_size tv
Proof
  Induct >> simp[arithmeticTheory.MULT_CLAUSES]
QED

Theorem immutable_dynamic_padding:
  LENGTH vs <= n ==>
  immutable_fit (n * type_memory_size tv + 32)
    (immutable_word_bytes w ++ FLAT (MAP (encode_immutable_value tv) vs)) =
  immutable_word_bytes w ++ FLAT (MAP (encode_immutable_value tv) vs) ++
    REPLICATE (n * type_memory_size tv - LENGTH vs * type_memory_size tv) 0w
Proof
  strip_tac >>
  `LENGTH (immutable_word_bytes w ++ FLAT (MAP (encode_immutable_value tv) vs)) <=
   n * type_memory_size tv + 32` by
    (simp[immutable_flat_map_length, arithmeticTheory.LE_MULT_RCANCEL]) >>
  drule immutable_fit_padding >> simp[immutable_flat_map_length]
QED

Theorem immutable_flat_uniform_length:
  !bss. EVERY (\bs. LENGTH bs = sz) bss ==>
    LENGTH (FLAT bss) = LENGTH bss * sz
Proof
  Induct >> simp[arithmeticTheory.MULT_CLAUSES]
QED

Theorem immutable_slot_context:
  EVERY (\bs. LENGTH bs = type_memory_size tv) bss /\
  i < LENGTH bss /\ EL i bss = encode_immutable_value tv v /\
  (!pre post. val_in_memory tv v (LENGTH pre)
      (pre ++ encode_immutable_value tv v ++ post)) ==>
  val_in_memory tv v (LENGTH pre + i * type_memory_size tv)
    (pre ++ FLAT bss ++ post)
Proof
  strip_tac >> drule_all immutable_flat_slot >> strip_tac >>
  metis_tac[listTheory.APPEND_ASSOC, listTheory.LENGTH_APPEND]
QED

Theorem immutable_kvs_context:
  !kvs. (!i v. MEM (i,v) kvs ==>
    i < LENGTH bss /\ EL i bss = encode_immutable_value tv v /\
    (!pre post. val_in_memory tv v (LENGTH pre)
      (pre ++ encode_immutable_value tv v ++ post))) ==>
  EVERY (\bs. LENGTH bs = type_memory_size tv) bss ==>
  !pre post. kvs_in_memory kvs (LENGTH pre) tv (pre ++ FLAT bss ++ post)
Proof
  Induct >- simp[val_in_memory_def] >> Cases_on `h` >>
  simp[val_in_memory_def] >> rpt strip_tac >>
  metis_tac[immutable_slot_context]
QED

Theorem immutable_encoding_decodes_mutual:
  (!tv v. immutable_value_admissible tv v ==>
    !pre post. val_in_memory tv v (LENGTH pre)
      (pre ++ encode_immutable_value tv v ++ post)) /\
  (!tvs vs. immutable_tuple_admissible tvs vs ==>
    !pre post. tuple_in_memory vs tvs (LENGTH pre)
      (pre ++ encode_immutable_tuple tvs vs ++ post)) /\
  (!fts vs. immutable_fields_admissible fts vs ==>
    !pre post. fields_in_memory vs fts (LENGTH pre)
      (pre ++ encode_immutable_fields fts vs ++ post))
Proof
  ho_match_mp_tac encode_immutable_value_ind >> rpt conj_tac
  >- metis_tac[immutable_base_decodes]
  >- (rpt gen_tac >> Cases_on `v` >>
      simp[immutable_value_admissible_def, encode_immutable_value_def,
           immutable_word_fit, val_in_memory_def, typed_val_to_w256_def,
           immutable_word_context])
  >- simp[immutable_value_admissible_def, val_in_memory_def]
  >- suspend "tuple_value"
  >- suspend "struct_value"
  >- suspend "arrays"
  >- simp[immutable_value_admissible_def, val_in_memory_def]
  >- suspend "tuple_cons"
  >- simp[immutable_value_admissible_def, val_in_memory_def]
  >> suspend "fields_cons"
QED

Resume immutable_encoding_decodes_mutual[tuple_value]:
  rpt gen_tac >> Cases_on `v` >>
  simp[immutable_value_admissible_def] >> Cases_on `a` >>
  simp[immutable_value_admissible_def, encode_immutable_value_def,
       type_memory_size_def, immutable_fit_exact, immutable_tuple_length,
       immutable_fields_length, val_in_memory_def]
QED

Resume immutable_encoding_decodes_mutual[struct_value]:
  rpt gen_tac >> Cases_on `v` >>
  simp[immutable_value_admissible_def, encode_immutable_value_def,
       type_memory_size_def, immutable_fit_exact, immutable_tuple_length,
       immutable_fields_length, val_in_memory_def]
QED

Resume immutable_encoding_decodes_mutual[tuple_cons]:
  rpt gen_tac >> Cases_on `vs` >>
  simp[immutable_value_admissible_def, encode_immutable_value_def,
       val_in_memory_def] >> rpt strip_tac >>
  metis_tac[listTheory.APPEND_ASSOC, listTheory.LENGTH_APPEND,
            encode_immutable_value_length]
QED
Resume immutable_encoding_decodes_mutual[fields_cons]:
  rpt gen_tac >> Cases_on `vs` >> simp[immutable_value_admissible_def] >>
  Cases_on `h` >>
  simp[immutable_value_admissible_def, encode_immutable_value_def,
       val_in_memory_def] >> rpt strip_tac >>
  metis_tac[listTheory.APPEND_ASSOC, listTheory.LENGTH_APPEND,
            encode_immutable_value_length]
QED
Resume immutable_encoding_decodes_mutual[arrays]:
  rpt gen_tac >> Cases_on `bound` >> Cases_on `v` >>
  simp[immutable_value_admissible_def] >> Cases_on `a` >>
  simp[immutable_value_admissible_def, encode_immutable_value_def,
       val_in_memory_def, type_memory_size_def] >>
  rpt strip_tac
  >- suspend "sparse"
  >- (pure_rewrite_tac[ETA_THM] >> simp[immutable_dynamic_padding] >>
      simp[mem_word_at_def, listTheory.DROP_APPEND, listTheory.TAKE_APPEND1,
           listTheory.TAKE_LENGTH_ID_rwt])
  >> suspend "dynamic_elems"
QED

Resume immutable_encoding_decodes_mutual[sparse]:
  qmatch_goalsub_abbrev_tac `FLAT bss` >>
  `EVERY (\bs. LENGTH bs = type_memory_size tv) bss` by
    (simp[Abbr `bss`, listTheory.EVERY_GENLIST] >> gen_tac >>
     Cases_on `ALOOKUP l i` >> simp[]) >>
  `LENGTH (FLAT bss) = n * type_memory_size tv` by
    (drule immutable_flat_uniform_length >> simp[Abbr `bss`]) >>
  simp[immutable_fit_exact] >> irule immutable_kvs_context >> simp[] >>
  rpt gen_tac >> strip_tac >>
  `i < n /\ immutable_value_admissible tv v` by
    (gvs[listTheory.EVERY_MEM] >> first_x_assum drule >> simp[]) >>
  `ALOOKUP l i = SOME v` by metis_tac[alistTheory.ALOOKUP_ALL_DISTINCT_MEM] >>
  simp[Abbr `bss`, listTheory.EL_GENLIST] >> metis_tac[]
QED

Resume immutable_encoding_decodes_mutual[dynamic_elems]:
  pure_rewrite_tac[ETA_THM] >> simp[immutable_dynamic_padding] >>
  `!v. MEM v l ==> !pre post. val_in_memory tv v (LENGTH pre)
     (pre ++ encode_immutable_value tv v ++ post)` by
    (gvs[listTheory.EVERY_MEM] >> metis_tac[]) >>
  drule immutable_elems_context >>
  disch_then (qspecl_then [`pre ++ immutable_word_bytes (n2w (LENGTH l))`,
    `REPLICATE (n * type_memory_size tv - LENGTH l * type_memory_size tv) 0w ++ post`]
    mp_tac) >> simp[listTheory.APPEND_ASSOC]
QED
Finalise immutable_encoding_decodes_mutual

Theorem immutable_encoding_decodes:
  immutable_value_admissible tv v ==>
  val_in_memory tv v (LENGTH pre) (pre ++ encode_immutable_value tv v ++ post)
Proof
  metis_tac[immutable_encoding_decodes_mutual]
QED

Theorem immutable_encoding_slice_decodes:
  immutable_value_admissible tv v /\ off <= LENGTH mem /\
  TAKE (type_memory_size tv) (DROP off mem) = encode_immutable_value tv v ==>
  val_in_memory tv v off mem
Proof
  strip_tac >>
  `mem = TAKE off mem ++ encode_immutable_value tv v ++
         DROP (type_memory_size tv) (DROP off mem)` by
    metis_tac[listTheory.TAKE_DROP, listTheory.APPEND_ASSOC] >>
  `LENGTH (TAKE off mem) = off` by simp[] >>
  metis_tac[immutable_encoding_decodes]
QED

Theorem immutable_encoding_slice_preserved:
  immutable_value_admissible tv v /\ off <= LENGTH mem' /\
  TAKE (type_memory_size tv) (DROP off mem) = encode_immutable_value tv v /\
  TAKE (type_memory_size tv) (DROP off mem') =
    TAKE (type_memory_size tv) (DROP off mem) ==>
  val_in_memory tv v off mem'
Proof
  metis_tac[immutable_encoding_slice_decodes]
QED

(* Updating a disjoint byte interval preserves a canonical capacity slice. *)
Theorem immutable_slice_splice_disjoint:
  off + n <= LENGTH mem /\ at <= LENGTH mem /\
  (off + n <= at \/ at + LENGTH bs <= off) ==>
  TAKE n (DROP off (TAKE at mem ++ bs ++ DROP (at + LENGTH bs) mem)) =
    TAKE n (DROP off mem)
Proof
  rpt strip_tac >> irule listTheory.LIST_EQ >>
  simp[listTheory.LENGTH_TAKE_EQ, listTheory.EL_TAKE,
       listTheory.EL_APPEND_EQN, listTheory.EL_DROP,
       listTheory.LENGTH_DROP]
QED

Theorem immutable_encoding_disjoint_splice:
  immutable_value_admissible tv v /\
  off + type_memory_size tv <= LENGTH mem /\ at <= LENGTH mem /\
  TAKE (type_memory_size tv) (DROP off mem) = encode_immutable_value tv v /\
  (off + type_memory_size tv <= at \/ at + LENGTH bs <= off) ==>
  val_in_memory tv v off
    (TAKE at mem ++ bs ++ DROP (at + LENGTH bs) mem)
Proof
  strip_tac >> irule immutable_encoding_slice_decodes >> simp[] >>
  metis_tac[immutable_slice_splice_disjoint]
QED

val _ = List.app (fn (name, th) => let
  val (oracles, axioms) = Tag.dest_tag (Thm.tag th)
  in if null axioms andalso null (Thm.hyp th) andalso
        List.all (fn s => s = "DISK_THM") oracles then
       print ("IMMUTABLE_DECODING_KERNEL_CLOSED " ^ name ^ "\n")
     else raise Fail ("Unclosed immutable decoding theorem: " ^ name)
  end) (DB.thms "immutableEncodingProofs");
