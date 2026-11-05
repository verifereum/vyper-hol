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
  cheat
QED

Theorem copy_primitive_memory_word[local]:
  !tv v off mem w.
    ( (?bt. tv = BaseTV bt) \/ (?n. tv = FlagTV n)) /\
    encode_base_to_slot v tv = SOME w /\ val_in_memory tv v off mem ==>
    mem_word_at off mem = w
Proof
  cheat
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
  cheat
QED

Theorem copy_zero_writes_lookup[local]:
  !is k st x.
    lookup_storage x (apply_writes k (MAP (\i. (i, 0w)) is) st) =
    if MEM x (MAP (\i. n2w (w2n k + i)) is) then 0w
    else lookup_storage x st
Proof
  cheat
QED

Theorem copy_zero_interval[local]:
  !k n st j.
    j < n ==>
    lookup_storage (n2w (w2n k + j))
      (apply_writes k (GENLIST (\i. (i, 0w)) n) st) = 0w
Proof
  cheat
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
  cheat
QED

(* ===== Dynamic byte chunks ===== *)

Theorem copy_slots_acc_prefix[local]:
  !acc bs. !prefix.
    bytes_to_slots_aux (acc ++ prefix) bs =
    REVERSE prefix ++ bytes_to_slots_aux acc bs
Proof
  cheat
QED

Theorem copy_slots_cons[local]:
  !h t.
    bytes_to_slots (h::t) =
    word_of_bytes_be
      (TAKE 32 (h::t) ++ REPLICATE (32 - LENGTH (TAKE 32 (h::t))) 0w) ::
    bytes_to_slots (DROP 32 (h::t))
Proof
  cheat
QED

Theorem copy_chunk_word[local]:
  !bs. word_of_bytes_be
    (TAKE 32 bs ++ REPLICATE (32 - LENGTH (TAKE 32 bs)) 0w) =
    mem_word_at 0 bs
Proof
  cheat
QED

Theorem copy_slots_index[local]:
  !bs i. 32 * i < LENGTH bs ==>
    i < LENGTH (bytes_to_slots bs) /\
    EL i (bytes_to_slots bs) = mem_word_at (32 * i) bs
Proof
  cheat
QED

Theorem copy_lookup_update[local]:
  !a c x st.
    lookup_storage a (update_storage c x st) =
    if a = c then x else lookup_storage a st
Proof
  cheat
QED

Theorem copy_writes_preserve_word[local]:
  !writes k st addr w.
    lookup_storage addr st = w /\
    (!i v. MEM (i,v) writes /\ n2w (w2n k + i) = addr ==> v = w) ==>
    lookup_storage addr (apply_writes k writes st) = w
Proof
  cheat
QED

Theorem copy_writes_hit[local]:
  !writes k st addr w.
    (?i. MEM (i,w) writes /\ n2w (w2n k + i) = addr) /\
    (!i v. MEM (i,v) writes /\ n2w (w2n k + i) = addr ==> v = w) ==>
    lookup_storage addr (apply_writes k writes st) = w
Proof
  cheat
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
  cheat
QED

Theorem copy_dyn_length_bound[local]:
  !ws hd sz.
    (!i. MEM i (MAP FST ((0,hd)::MAPi (\i w. (i+1,w)) ws)) ==> i < sz) ==>
    LENGTH ws + 1 <= sz
Proof
  cheat
QED

Theorem copy_mem_payload_byte_at[local]:
  !mem bs addr b p r.
    mem_bytes_at p (LENGTH bs) mem = bs /\ addr = p + r /\
    r + b < LENGTH bs /\ b < 32 ==>
    EL b (word_to_bytes (mem_word_at addr mem) T) = EL (r+b) bs
Proof
  cheat
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
  cheat
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
  cheat
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
  cheat
QED


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
  cheat
QED


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
  cheat
QED


(* Every sparse write lies in the interval of a key actually present. *)
Theorem copy_sparse_write_key[local]:
  !sparse tv offset writes n x.
    sparse_has_type tv n sparse /\
    encode_static_array tv offset sparse = SOME writes /\
    MEM x (MAP FST writes) ==>
    ?i r. MEM i (MAP FST sparse) /\ r < type_slot_size tv /\
          x = offset+i*type_slot_size tv+r
Proof
  cheat
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
  cheat
QED


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
  cheat
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
  cheat
QED

Theorem copy_static_live_index[local]:
  !st base tv n j b.
    j < n*type_slot_size tv /\
    ~dead_bytes st base (ArrayTV tv (Fixed n)) (base+j) b ==>
    ?i r. i < n /\ r < type_slot_size tv /\ j = i*type_slot_size tv+r /\
      ~dead_bytes st (base+i*type_slot_size tv) tv (base+j) b
Proof
  cheat
QED

Theorem copy_dyn_live_index[local]:
  !st base tv n j b.
    0 < j /\ j < 1+n*type_slot_size tv /\ b < 32 /\
    ~dead_bytes st base (ArrayTV tv (Dynamic n)) (base+j) b ==>
    ?i r. i < n /\ i < w2n (lookup_storage (n2w base) st) /\
      r < type_slot_size tv /\ j = 1+i*type_slot_size tv+r /\
      ~dead_bytes st (base+1+i*type_slot_size tv) tv (base+j) b
Proof
  cheat
QED

Theorem copy_dyn_head[local]:
  !tv vs slots k st.
    all_have_type tv vs /\ encode_dyn_array tv 1 vs = SOME slots /\
    w2n k+1+LENGTH vs*type_slot_size tv <= dimword (:256) ==>
    lookup_storage k (apply_writes k ((0,n2w (LENGTH vs))::slots) st) =
      n2w (LENGTH vs)
Proof
  cheat
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
  cheat
QED

Theorem copy_tuple_member[local]:
  !tvs tv.
    well_formed_type_value (TupleTV tvs) /\ MEM tv tvs ==>
    well_formed_type_value tv /\
    type_value_size tv < type_value_size (TupleTV tvs)
Proof
  cheat
QED

Theorem copy_struct_member[local]:
  !fields tv.
    well_formed_type_value (StructTV fields) /\ MEM tv (MAP SND fields) ==>
    well_formed_type_value tv /\
    type_value_size tv < type_value_size (StructTV fields)
Proof
  cheat
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
  cheat
QED


Theorem copy_fold_lookup[local]:
  !is addr f q w st.
    (!i. MEM i is /\ addr i = q ==> f i = w) ==>
    lookup_storage q (FOLDL (\t i. update_storage (addr i) (f i) t) st is) =
    if MEM q (MAP addr is) then w else lookup_storage q st
Proof
  cheat
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
  cheat
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
  cheat
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
  cheat
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
  cheat
QED
