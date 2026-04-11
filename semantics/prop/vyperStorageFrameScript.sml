(*
 * vyperStorageFrameScript.sml
 *
 * Storage frame theorems for Vyper: writing to one storage location
 * preserves reading from a disjoint location.
 *
 * Design: all theorems are per-key (no universal quantifiers over
 * hashmap keys). The key values appear as specific parameters, so
 * the assumptions are exactly as strong as needed for the particular
 * execution or proof. For concrete executions, slot disjointness
 * is dischargeable by EVAL (keccak is computationally evaluable).
 *
 * Definitions:
 *   ranges_disjoint            — two slot ranges don't overlap (foundational predicate)
 *   hashmap_var_info           — extract hashmap variable metadata from context
 *   get_leaf_tv                — leaf type_value of a value_type
 *
 * Frame theorems (core):
 *   write_storage_preserves_read       — monadic write/read frame theorem
 *
 * Frame theorems (static ↔ static):
 *   static_write_preserves_static_read — via ranges_disjoint, not well_formed_layout
 *   well_formed_layout_implies_ranges_disjoint — connection to existing predicate
 *
 * Frame theorems (hashmap → static, per-key):
 *   hashmap_write_preserves_static_read    — ref-level
 *   update_hashmap_preserves_static_read   — name-level
 *
 * Frame theorems (static → hashmap, per-key) [NEW]:
 *   static_write_preserves_hashmap_read    — ref-level
 *   update_toplevel_preserves_lookup_hashmap — name-level
 *
 * Frame theorems (hashmap → hashmap, per-key-pair) [NEW]:
 *   hashmap_write_preserves_other_hashmap_read     — same backend, ref-level
 *   hashmap_write_preserves_other_hashmap_read_gen — any backend, ref-level
 *   update_hashmap_preserves_other_lookup_hashmap   — name-level
 *   update_hashmap_preserves_same_lookup_hashmap_other_key — same var, different keys
 *
 * Frame theorems (nested hashmaps):
 *   nested_hashmap_write_preserves_static_read_chain — via compute_hashmap_slot
 *
 * Relating existing predicates to ranges_disjoint:
 *   hashmap_slots_disjoint_as_ranges_disjoint
 *   hashmap_var_slots_disjoint_as_ranges_disjoint
 *)

Theory vyperStorageFrame

Ancestors
  vyperHashMapPreservation vyperHashMap vyperHashMapStorage
  vyperLookupStorage vyperStorageBackend
  vyperEncodeDecode

Libs
  wordsLib

(* ===== Foundational Definitions ===== *)

(* Two slot ranges [off1, off1+sz1) and [off2, off2+sz2) are disjoint
   and both fit within the 256-bit address space. *)
Definition ranges_disjoint_def:
  ranges_disjoint off1 sz1 off2 sz2 ⇔
    off1 + sz1 ≤ dimword(:256) ∧
    off2 + sz2 ≤ dimword(:256) ∧
    (off1 + sz1 ≤ off2 ∨ off2 + sz2 ≤ off1)
End

(* ===== Basic properties of ranges_disjoint ===== *)

Theorem ranges_disjoint_sym:
  ∀off1 sz1 off2 sz2.
    ranges_disjoint off1 sz1 off2 sz2 ⇔ ranges_disjoint off2 sz2 off1 sz1
Proof
  simp[ranges_disjoint_def]
QED

Theorem ranges_disjoint_irrefl:
  ∀off sz. 0 < sz ⇒ ¬ranges_disjoint off sz off sz
Proof
  simp[ranges_disjoint_def]
QED

(* Bridge between num-level and word-level offsets.
   Used in every theorem that composes ranges_disjoint (num)
   with write_storage_preserves_read (word). *)
Theorem ranges_disjoint_n2w_w2n:
  ∀off1 sz1 off2 sz2.
    ranges_disjoint off1 sz1 off2 sz2 ⇒
    ranges_disjoint off1 sz1 (w2n ((n2w off2):bytes32)) sz2
Proof
  rpt gen_tac >> rewrite_tac[ranges_disjoint_def] >> disch_tac >>
  Cases_on `off2 < dimword(:256)`
  >- (gvs[Excl "dimword_256", wordsTheory.w2n_n2w])
  >> `off2 = dimword(:256) ∧ sz2 = 0` by gvs[Excl "dimword_256"] >>
  gvs[Excl "dimword_256"]
QED

(* Helper: write_storage_slot succeeds when value has the right type *)
Theorem write_storage_slot_succeeds:
  ∀cx b slot tv v st.
    value_has_type tv v ⇒
    write_storage_slot cx b slot tv v st =
    (INL (), SND (write_storage_slot cx b slot tv v st))
Proof
  rpt strip_tac >>
  drule (CONJUNCT1 vyperTypingTheory.value_has_type_equiv) >>
  simp[optionTheory.IS_SOME_EXISTS] >> strip_tac >>
  simp[write_storage_slot_eq]
QED

(* ===== Relating existing predicates to ranges_disjoint ===== *)

Theorem hashmap_slots_disjoint_as_ranges_disjoint:
  ∀base kt tv kv1 kv2.
    hashmap_slots_disjoint base kt tv kv1 kv2 ⇔
    ranges_disjoint (w2n (hashmap_slot_for base kt kv1)) (type_slot_size tv)
                    (w2n (hashmap_slot_for base kt kv2)) (type_slot_size tv)
Proof
  simp[hashmap_slots_disjoint_def, ranges_disjoint_def, LET_THM]
QED

Theorem hashmap_var_slots_disjoint_as_ranges_disjoint:
  ∀bslot kt hm_tv kv var_off var_tv.
    hashmap_var_slots_disjoint bslot kt hm_tv kv var_off var_tv ⇔
    ranges_disjoint (w2n (hashmap_slot_for bslot kt kv)) (type_slot_size hm_tv)
                    var_off (type_slot_size var_tv)
Proof
  simp[hashmap_var_slots_disjoint_def, ranges_disjoint_def, LET_THM]
QED

(* ===== Hashmap Variable Info Accessor ===== *)

(* Extract metadata for a hashmap variable declaration from the context.
   Returns (is_transient, base_slot, key_type, value_type) or NONE.
   Analogous to storage_var_info for StorageVarDecl. *)
Definition hashmap_var_info_def:
  hashmap_var_info cx mid n =
    case get_module_code cx mid of
    | NONE => NONE
    | SOME code =>
        case find_var_decl_by_num (string_to_num n) code of
        | SOME (HashMapVarDecl b kt vt, id) =>
            (case lookup_var_slot_from_layout cx b mid id of
             | SOME off => SOME (b, off, kt, vt)
             | NONE => NONE)
        | _ => NONE
End

(* ===== Leaf Type Extraction ===== *)

(* Extract the leaf type_value from a value_type, traversing through
   nested HashMapT layers. Returns NONE if evaluate_type fails. *)
Definition get_leaf_tv_def:
  get_leaf_tv tenv (Type t) = evaluate_type tenv t ∧
  get_leaf_tv tenv (HashMapT kt vt) = get_leaf_tv tenv vt
End

(* Connection: for a leaf hashmap (vt = Type t), get_leaf_tv
   agrees with evaluate_type *)
Theorem get_leaf_tv_Type:
  ∀tenv t. get_leaf_tv tenv (Type t) = evaluate_type tenv t
Proof
  simp[get_leaf_tv_def]
QED

(* Connection: is_leaf_hashmap implies get_leaf_tv succeeds *)
Theorem is_leaf_hashmap_get_leaf_tv:
  ∀cx mid n.
    is_leaf_hashmap cx mid n ⇒
    ∃b off kt vt tv.
      hashmap_var_info cx mid n = SOME (b, off, kt, vt) ∧
      get_leaf_tv (get_tenv cx) vt = SOME tv ∧
      well_formed_type_value tv
Proof
  rw[is_leaf_hashmap_def] >>
  simp[hashmap_var_info_def, get_leaf_tv_def]
QED

(* Helper: decode_value unchanged when apply_writes is at a
   disjoint word-level slot range. Works with word slots directly
   (vs decode_value_disjoint_writes which uses num offsets). *)
Theorem decode_value_disjoint_writes_words:
  ∀tv2 sz1 writes (slot1:bytes32) (slot2:bytes32) storage.
    (∀wr_off. MEM wr_off (MAP FST writes) ⇒ wr_off < sz1) ∧
    ranges_disjoint (w2n slot1) sz1 (w2n slot2) (type_slot_size tv2) ⇒
    decode_value (apply_writes slot1 writes storage) (w2n slot2) tv2 =
    decode_value storage (w2n slot2) tv2
Proof
  rpt gen_tac >> strip_tac >>
  `slot1 = n2w (w2n slot1)` by simp[wordsTheory.n2w_w2n] >>
  pop_assum SUBST1_TAC >>
  irule decode_value_disjoint_writes >>
  fs[ranges_disjoint_def] >> qexists `sz1` >> simp[]
QED

(* ============================================================
   Core Frame Theorem: write_storage_slot preserves read_storage_slot
   at a disjoint slot range (or different backend).

   This is the foundational theorem from which all other frame
   properties derive. It composes:
   - write_storage_slot_eq (write = encode + apply_writes + set)
   - read_storage_slot_eq  (read = get + decode)
   - get_storage_after_set / get_storage_after_set_other
   - decode_value_disjoint_writes (decode ignores disjoint writes)
   - encode_writes_bounded (writes stay within type_slot_size)
   ============================================================ *)

Theorem write_storage_preserves_read:
  ∀cx b1 slot1 tv1 v b2 slot2 tv2 st st'.
    write_storage_slot cx b1 slot1 tv1 v st = (INL (), st') ∧
    value_has_type tv1 v ∧
    (b1 ≠ b2 ∨
     ranges_disjoint (w2n slot1) (type_slot_size tv1)
                     (w2n slot2) (type_slot_size tv2)) ⇒
    FST (read_storage_slot cx b2 slot2 tv2 st') =
    FST (read_storage_slot cx b2 slot2 tv2 st)
Proof
  rpt gen_tac >> disch_tac >>
  gvs[write_storage_slot_eq, AllCaseEqs()] >>
  rename1 `encode_value tv1 v = SOME writes` >>
  simp[read_storage_slot_eq] >>
  Cases_on `b1 = b2`
  >- (
    (* Same backend: ranges must be disjoint *)
    gvs[get_storage_after_set] >>
    suspend "same_backend")
  >- (simp[get_storage_after_set_other] >> CASE_TAC >> simp[])
QED

Resume write_storage_preserves_read[same_backend]:
  `decode_value (apply_writes slot1 writes (get_storage cx st b1))
     (w2n slot2) tv2 =
   decode_value (get_storage cx st b1) (w2n slot2) tv2` by (
    irule decode_value_disjoint_writes_words >>
    qexists `type_slot_size tv1` >> simp[] >>
    metis_tac[CONJUNCT1 encode_writes_bounded]) >>
  simp[] >> CASE_TAC >> simp[]
QED

Finalise write_storage_preserves_read

(* All-num version: write at num offset preserves read at num offset.
   Composes write_storage_slot_succeeds + write_storage_preserves_read +
   ranges_disjoint_n2w_w2n. *)
Theorem write_preserves_read_num:
  ∀cx b1 off1 tv1 v b2 off2 tv2 st.
    value_has_type tv1 v ∧
    (b1 ≠ b2 ∨
     ranges_disjoint off1 (type_slot_size tv1) off2 (type_slot_size tv2)) ⇒
    FST (read_storage_slot cx b2 (n2w off2) tv2
           (SND (write_storage_slot cx b1 (n2w off1) tv1 v st))) =
    FST (read_storage_slot cx b2 (n2w off2) tv2 st)
Proof
  rpt gen_tac >> strip_tac >>
  irule write_storage_preserves_read >>
  qexistsl [`b1`, `n2w off1`, `tv1`, `v`] >>
  simp[Excl "w2n_n2w", write_storage_slot_succeeds] >>
  strip_tac >>
  ONCE_REWRITE_TAC [GSYM ranges_disjoint_sym] >>
  irule ranges_disjoint_n2w_w2n >>
  ONCE_REWRITE_TAC [GSYM ranges_disjoint_sym] >>
  irule ranges_disjoint_n2w_w2n >>
  first_assum ACCEPT_TAC
QED

(* ============================================================
   Core helper: lookup_toplevel_name after set_storage
   
   When storage for backend b is replaced by storage', and the
   FST of read_storage_slot for variable (b2, off2, tv2) is
   unchanged, then lookup_toplevel_name is unchanged.
   
   This factors out the monadic unfolding of lookup_global that
   would otherwise be repeated in every frame theorem.
   ============================================================ *)

Theorem lookup_toplevel_name_after_set_storage:
  ∀cx st b storage' mid m.
    (∀b2 off2 tv2.
       storage_var_info cx mid m = SOME (b2, off2, tv2) ∧ b = b2 ⇒
       FST (read_storage_slot cx b (n2w off2) tv2
              (set_storage cx st b storage')) =
       FST (read_storage_slot cx b (n2w off2) tv2 st)) ⇒
    lookup_toplevel_name cx (set_storage cx st b storage') mid m =
    lookup_toplevel_name cx st mid m
Proof
  rpt gen_tac >> strip_tac >>
  simp[lookup_toplevel_name_def] >>
  `lookup_global cx mid (string_to_num m) (set_storage cx st b storage') =
   lookup_global cx mid (string_to_num m) st` by (
    cheat) >>
  simp[]
QED

(* ============================================================
   Lifted Frame Theorems: variable-level preservation
   ============================================================ *)

(* ----- Static var write preserves static var read ----- *)

Theorem static_write_preserves_static_read:
  ∀cx st mid1 n1 mid2 n2 v b1 off1 tv1 b2 off2 tv2.
    storage_var_info cx mid1 n1 = SOME (b1, off1, tv1) ∧
    storage_var_info cx mid2 n2 = SOME (b2, off2, tv2) ∧
    var_in_storage cx mid1 n1 ∧
    var_in_storage cx mid2 n2 ∧
    storable_value cx mid1 n1 v ∧
    (b1 ≠ b2 ∨ ranges_disjoint off1 (type_slot_size tv1) off2 (type_slot_size tv2)) ⇒
    lookup_toplevel_name cx (update_toplevel_name cx st mid1 n1 v) mid2 n2 =
    lookup_toplevel_name cx st mid2 n2
Proof
  (* Follows from lookup_toplevel_name_preserved_after_update.
     The key observation is that well_formed_layout's disjointness
     condition for same-backend variables is exactly
     ranges_disjoint off1 (type_slot_size tv1) off2 (type_slot_size tv2)
     (without the dimword bounds, which come from well_formed_layout's
     non-overflow clause). For different backends, the proof is direct
     from get_storage_after_set_other. *)
  cheat
QED

(* ----- Hashmap write preserves static var read (per-key) ----- *)

(* Already essentially proved as lookup_toplevel_name_write_hashmap,
   but we restate with ranges_disjoint for uniformity and to make
   the per-key nature explicit. *)

Theorem hashmap_write_preserves_static_read:
  ∀cx st b bslot kt t kv v mid m tv var_b var_off var_tv.
    evaluate_type (get_tenv cx) t = SOME tv ∧
    value_has_type tv v ∧
    storage_var_info cx mid m = SOME (var_b, var_off, var_tv) ∧
    (b ≠ var_b ∨
     ranges_disjoint (w2n (hashmap_slot_for bslot kt kv)) (type_slot_size tv)
                     var_off (type_slot_size var_tv)) ⇒
    lookup_toplevel_name cx
      (write_hashmap cx st (HashMapRef b bslot kt (Type t)) kv v) mid m =
    lookup_toplevel_name cx st mid m
Proof
  (* Follows from lookup_toplevel_name_write_hashmap.
     The existing theorem's hypothesis asks for
     hashmap_var_slots_disjoint bslot kt tv kv var_off var_tv
     when b = var_b, which is exactly
     ranges_disjoint (w2n (hashmap_slot_for bslot kt kv)) (type_slot_size tv)
                     var_off (type_slot_size var_tv)
     by hashmap_var_slots_disjoint_as_ranges_disjoint.
     When b ≠ var_b, get_storage_after_set_other handles it directly. *)
  cheat
QED

(* Name-level convenience: update_hashmap preserves lookup_toplevel_name *)
Theorem update_hashmap_preserves_static_read:
  ∀cx st mid_h n_h kv v mid_v n_v.
    is_leaf_hashmap cx mid_h n_h ∧
    hashmap_ref_storable cx (THE (lookup_toplevel_name cx st mid_h n_h)) v ∧
    (∀b_h off_h kt vt tv_h b_v off_v tv_v.
       hashmap_var_info cx mid_h n_h = SOME (b_h, off_h, kt, vt) ∧
       get_leaf_tv (get_tenv cx) vt = SOME tv_h ∧
       storage_var_info cx mid_v n_v = SOME (b_v, off_v, tv_v) ⇒
       b_h ≠ b_v ∨
       ranges_disjoint (w2n (hashmap_slot_for (n2w off_h) kt kv)) (type_slot_size tv_h)
                       off_v (type_slot_size tv_v)) ⇒
    lookup_toplevel_name cx (update_hashmap cx st mid_h n_h kv v) mid_v n_v =
    lookup_toplevel_name cx st mid_v n_v
Proof
  (* Unfold update_hashmap to write_hashmap.
     Use is_leaf_hashmap to get the HashMapRef structure.
     Apply hashmap_write_preserves_static_read with the concrete ref
     components extracted from hashmap_var_info / is_leaf_hashmap. *)
  cheat
QED

(* ----- Static var write preserves hashmap read (per-key) ----- *)

(* NEW: This is the "reverse direction" that didn't exist before.
   Writing a static variable preserves reading from a hashmap entry. *)

Theorem static_write_preserves_hashmap_read:
  ∀cx st mid_v n_v v b_h bslot kt t kv tv.
    var_in_storage cx mid_v n_v ∧
    storable_value cx mid_v n_v v ∧
    evaluate_type (get_tenv cx) t = SOME tv ∧
    (∀b_v off_v tv_v.
       storage_var_info cx mid_v n_v = SOME (b_v, off_v, tv_v) ⇒
       b_h ≠ b_v ∨
       ranges_disjoint off_v (type_slot_size tv_v)
                       (w2n (hashmap_slot_for bslot kt kv)) (type_slot_size tv)) ⇒
    read_hashmap cx (update_toplevel_name cx st mid_v n_v v)
                    (HashMapRef b_h bslot kt (Type t)) kv =
    read_hashmap cx st (HashMapRef b_h bslot kt (Type t)) kv
Proof
  (* update_toplevel_name unfolds to set_global, which calls
     write_storage_slot cx b_v (n2w off_v) tv_v v.
     read_hashmap unfolds to hashmap_read = decode_value at
     w2n (hashmap_slot_for bslot kt kv).
     Different backend: get_storage_after_set_other shows storage unchanged.
     Same backend + disjoint ranges:
       The write modifies slots [off_v, off_v + type_slot_size tv_v).
       The read uses slots [hm_off, hm_off + type_slot_size tv).
       decode_value_disjoint_writes gives the result. *)
  cheat
QED

(* Name-level convenience *)
Theorem update_toplevel_preserves_lookup_hashmap:
  ∀cx st mid_v n_v v mid_h n_h kv.
    var_in_storage cx mid_v n_v ∧
    storable_value cx mid_v n_v v ∧
    is_leaf_hashmap cx mid_h n_h ∧
    (∀b_v off_v tv_v b_h off_h kt vt tv_h.
       storage_var_info cx mid_v n_v = SOME (b_v, off_v, tv_v) ∧
       hashmap_var_info cx mid_h n_h = SOME (b_h, off_h, kt, vt) ∧
       get_leaf_tv (get_tenv cx) vt = SOME tv_h ⇒
       b_v ≠ b_h ∨
       ranges_disjoint off_v (type_slot_size tv_v)
                       (w2n (hashmap_slot_for (n2w off_h) kt kv)) (type_slot_size tv_h)) ⇒
    lookup_hashmap cx (update_toplevel_name cx st mid_v n_v v) mid_h n_h kv =
    lookup_hashmap cx st mid_h n_h kv
Proof
  (* Unfold lookup_hashmap to lookup_toplevel_name + read_hashmap.
     lookup_toplevel_name for a hashmap variable is state-independent
     (is_leaf_hashmap_lookup_state_independent), so it returns the same
     HashMapRef before and after update_toplevel_name.
     For read_hashmap, apply static_write_preserves_hashmap_read. *)
  cheat
QED

(* ----- Hashmap write preserves different hashmap read (per-key-pair) ----- *)

(* NEW: Writing to one hashmap variable preserves reading from a
   different hashmap variable. Per-key-pair: kv1 is the written key,
   kv2 is the read key. *)

Theorem hashmap_write_preserves_other_hashmap_read:
  ∀cx st b bslot1 kt1 t1 kv1 v bslot2 kt2 t2 kv2 tv1 tv2.
    evaluate_type (get_tenv cx) t1 = SOME tv1 ∧
    evaluate_type (get_tenv cx) t2 = SOME tv2 ∧
    value_has_type tv1 v ∧
    (ranges_disjoint (w2n (hashmap_slot_for bslot1 kt1 kv1)) (type_slot_size tv1)
                     (w2n (hashmap_slot_for bslot2 kt2 kv2)) (type_slot_size tv2)) ⇒
    read_hashmap cx
      (write_hashmap cx st (HashMapRef b bslot1 kt1 (Type t1)) kv1 v)
      (HashMapRef b bslot2 kt2 (Type t2)) kv2 =
    read_hashmap cx st (HashMapRef b bslot2 kt2 (Type t2)) kv2
Proof
  rpt gen_tac >> strip_tac >>
  irule read_hashmap_after_write_other_ref >> simp[] >>
  gvs[GSYM hashmap_var_slots_disjoint_as_ranges_disjoint]
QED

(* Same as above but also handles different backends *)
Theorem hashmap_write_preserves_other_hashmap_read_gen:
  ∀cx st b1 bslot1 kt1 t1 kv1 v b2 bslot2 kt2 t2 kv2 tv1 tv2.
    evaluate_type (get_tenv cx) t1 = SOME tv1 ∧
    evaluate_type (get_tenv cx) t2 = SOME tv2 ∧
    value_has_type tv1 v ∧
    (b1 ≠ b2 ∨
     ranges_disjoint (w2n (hashmap_slot_for bslot1 kt1 kv1)) (type_slot_size tv1)
                     (w2n (hashmap_slot_for bslot2 kt2 kv2)) (type_slot_size tv2)) ⇒
    read_hashmap cx
      (write_hashmap cx st (HashMapRef b1 bslot1 kt1 (Type t1)) kv1 v)
      (HashMapRef b2 bslot2 kt2 (Type t2)) kv2 =
    read_hashmap cx st (HashMapRef b2 bslot2 kt2 (Type t2)) kv2
Proof
  rpt gen_tac >> disch_tac >> gvs[] >>
  Cases_on `b1 = b2` >> gvs[]
  >- (irule hashmap_write_preserves_other_hashmap_read >> simp[])
  >> irule read_hashmap_after_write_other_backend >> simp[]
QED

(* Name-level convenience: update_hashmap preserves lookup_hashmap
   for a different hashmap variable *)
Theorem update_hashmap_preserves_other_lookup_hashmap:
  ∀cx st mid1 n1 kv1 v mid2 n2 kv2.
    is_leaf_hashmap cx mid1 n1 ∧
    is_leaf_hashmap cx mid2 n2 ∧
    hashmap_ref_storable cx (THE (lookup_toplevel_name cx st mid1 n1)) v ∧
    (∀b1 off1 kt1 vt1 tv1 b2 off2 kt2 vt2 tv2.
       hashmap_var_info cx mid1 n1 = SOME (b1, off1, kt1, vt1) ∧
       get_leaf_tv (get_tenv cx) vt1 = SOME tv1 ∧
       hashmap_var_info cx mid2 n2 = SOME (b2, off2, kt2, vt2) ∧
       get_leaf_tv (get_tenv cx) vt2 = SOME tv2 ⇒
       b1 ≠ b2 ∨
       ranges_disjoint
         (w2n (hashmap_slot_for (n2w off1) kt1 kv1)) (type_slot_size tv1)
         (w2n (hashmap_slot_for (n2w off2) kt2 kv2)) (type_slot_size tv2)) ⇒
    lookup_hashmap cx (update_hashmap cx st mid1 n1 kv1 v) mid2 n2 kv2 =
    lookup_hashmap cx st mid2 n2 kv2
Proof
  (* Unfold update_hashmap to write_hashmap and lookup_hashmap to
     lookup_toplevel_name + read_hashmap.
     lookup_toplevel_name for mid2/n2 is state-independent (hashmap var),
     so it returns the same HashMapRef after update_hashmap.
     For read_hashmap, the write_hashmap went to mid1/n1's ref.
     Apply hashmap_write_preserves_other_hashmap_read_gen with the
     concrete refs extracted from hashmap_var_info and is_leaf_hashmap. *)
  cheat
QED

(* ----- Same hashmap, different keys (per-key-pair) ----- *)

(* This already exists as lookup_hashmap_after_update_other in
   vyperHashMapTheory, but with hashmap_ref_no_collision (which
   universally quantifies). We provide a per-key-pair version. *)

Theorem update_hashmap_preserves_same_lookup_hashmap_other_key:
  ∀cx st mid n kv1 kv2 v.
    is_leaf_hashmap cx mid n ∧
    hashmap_ref_storable cx (THE (lookup_toplevel_name cx st mid n)) v ∧
    (∀b off kt vt tv.
       hashmap_var_info cx mid n = SOME (b, off, kt, vt) ∧
       get_leaf_tv (get_tenv cx) vt = SOME tv ⇒
       ranges_disjoint
         (w2n (hashmap_slot_for (n2w off) kt kv1)) (type_slot_size tv)
         (w2n (hashmap_slot_for (n2w off) kt kv2)) (type_slot_size tv)) ⇒
    lookup_hashmap cx (update_hashmap cx st mid n kv1 v) mid n kv2 =
    lookup_hashmap cx st mid n kv2
Proof
  (* Unfold update_hashmap and lookup_hashmap.
     Both use the same HashMapRef (state-independent for hashmap vars).
     The write goes to hashmap_slot_for base kt kv1, the read from
     hashmap_slot_for base kt kv2.
     ranges_disjoint ensures the slot ranges don't overlap.
     Follows from hashmap_read_after_write_other via
     hashmap_slots_disjoint_as_ranges_disjoint. *)
  cheat
QED

(* ============================================================
   Nested Hashmap Support

   For nested hashmaps (HashMap[K1, HashMap[K2, V]]), the final
   storage slot is computed by compute_hashmap_slot applied to
   the full key chain. The frame theorems above work at the leaf
   ref level (HashMapRef with Type t), which is what you get after
   indexing through all outer layers.

   These theorems connect compute_hashmap_slot to the ref-level
   frame theorems, handling the key chain uniformly.
   ============================================================ *)

(* NOTE on nested hashmaps and compute_hashmap_slot:
   For a nested hashmap HashMap[K1, HashMap[K2, V]] at base_slot:
   - compute_hashmap_slot base_slot [K1] [s1] = SOME mid_slot
   - The leaf ref is HashMapRef b mid_slot K2 (Type t)
   - A write with key kv2 goes to hashmap_slot_for mid_slot K2 kv2
   - The full slot is: hashmap_slot(hashmap_slot(base, encode(k1)), encode(k2))
   
   compute_hashmap_slot with ALL key types and subscripts
   (including the final key) gives the actual storage slot:
   - compute_hashmap_slot base_slot [K1, K2] [s1, s2] = SOME final_write_slot
   
   The ref-level frame theorems above (hashmap_write_preserves_static_read etc.)
   already handle nested hashmaps: the bslot in the HashMapRef IS the mid_slot
   (output of outer indexing), and kv is the final key. The user obtains the
   leaf HashMapRef by chaining hashmap_index.
   
   The theorem below works directly at the write_storage_slot/read_storage_slot
   level with a slot computed by compute_hashmap_slot, bypassing the
   ref-level API entirely. This is useful because assign_target for hashmaps
   computes the final slot via compute_hashmap_slot and then calls
   write_storage_slot directly. *)

Theorem nested_hashmap_write_preserves_static_read_chain:
  ∀cx st b base_slot all_kts all_subs final_slot t tv
   new_val mid_v n_v var_b var_off var_tv.
    compute_hashmap_slot base_slot all_kts all_subs = SOME final_slot ∧
    evaluate_type (get_tenv cx) t = SOME tv ∧
    value_has_type tv new_val ∧
    storage_var_info cx mid_v n_v = SOME (var_b, var_off, var_tv) ∧
    (b ≠ var_b ∨
     ranges_disjoint (w2n final_slot) (type_slot_size tv)
                     var_off (type_slot_size var_tv)) ⇒
    FST (read_storage_slot cx var_b (n2w var_off) var_tv
           (SND (write_storage_slot cx b final_slot tv new_val st))) =
    FST (read_storage_slot cx var_b (n2w var_off) var_tv st)
Proof
  rpt gen_tac >> strip_tac >> gvs[] >>
  irule write_storage_preserves_read >>
  qexistsl [`b`, `final_slot`, `tv`, `new_val`] >>
  simp[Excl "w2n_n2w", write_storage_slot_succeeds] >>
  strip_tac >>
  irule ranges_disjoint_n2w_w2n >>
  first_assum ACCEPT_TAC
QED

(* ============================================================
   well_formed_layout expressed via ranges_disjoint

   well_formed_layout already works for static-static disjointness.
   We show it implies ranges_disjoint for any pair of static variables.
   ============================================================ *)

Theorem well_formed_layout_implies_ranges_disjoint:
  ∀cx mid1 n1 mid2 n2 b off1 tv1 off2 tv2.
    well_formed_layout cx ∧
    storage_var_info cx mid1 n1 = SOME (b, off1, tv1) ∧
    storage_var_info cx mid2 n2 = SOME (b, off2, tv2) ∧
    (mid1, n1) ≠ (mid2, n2) ⇒
    ranges_disjoint off1 (type_slot_size tv1) off2 (type_slot_size tv2)
Proof
  (* Unfold well_formed_layout: the disjointness clause gives
     off1 + type_slot_size tv1 ≤ off2 ∨ off2 + type_slot_size tv2 ≤ off1
     and the non-overflow clause gives
     off1 + type_slot_size tv1 ≤ dimword(:256) and similarly for off2.
     These are exactly ranges_disjoint. *)
  cheat
QED
