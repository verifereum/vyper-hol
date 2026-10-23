Theory abiDecodeRanges
Ancestors
  contractABI arithmetic list rich_list words byte
Libs
  wordsLib

(* Head and tail lengths are separate: static children occupy the head,
   dynamic children occupy the tail and have a single offset head word. *)
Definition abi_member_head_size_def:
  abi_member_head_size t = if is_dynamic t then 32 else static_length t
End

Definition abi_member_tail_size_def:
  abi_member_tail_size t v = if is_dynamic t then LENGTH (enc t v) else 0
End

Theorem head_lengths_acc:
  !ts a. head_lengths ts a = a + SUM (MAP abi_member_head_size ts)
Proof
  Induct >> simp[head_lengths_def, abi_member_head_size_def] >>
  rpt gen_tac >> Cases_on `is_dynamic h` >> simp[]
QED

Theorem enc_tuple_length_exact:
  !ts vs hl tl hds tls.
    has_types ts vs ==>
    LENGTH (enc_tuple hl tl ts vs hds tls) =
      SUM (MAP LENGTH hds) + SUM (MAP LENGTH tls) +
      SUM (MAP abi_member_head_size ts) +
      SUM (MAP2 abi_member_tail_size ts vs)
Proof
  Induct_on `ts` >> Cases_on `vs` >>
  simp[has_type_def, Once enc_def, LENGTH_FLAT, REV_REVERSE_LEM,
       MAP_REVERSE, SUM_REVERSE, SUM_APPEND] >>
  rpt strip_tac >>
  rename1 `has_type ty v` >>
  Cases_on `is_dynamic ty`
  >- simp[abi_member_head_size_def, abi_member_tail_size_def,
          LENGTH_word_to_bytes] >>
  `LENGTH (enc ty v) = static_length ty` by
    (irule (cj 1 enc_has_static_length) >> simp[]) >>
  simp[abi_member_head_size_def, abi_member_tail_size_def]
QED

Theorem has_types_length:
  !ts vs. has_types ts vs ==> LENGTH ts = LENGTH vs
Proof
  Induct >> Cases_on `vs` >> simp[has_type_def]
QED

Theorem has_types_append:
  !ts vs us ws.
    LENGTH ts = LENGTH vs ==>
    (has_types (ts ++ us) (vs ++ ws) <=>
     has_types ts vs /\ has_types us ws)
Proof
  Induct >> Cases_on `vs` >> simp[has_type_def] >> metis_tac[]
QED

Theorem canonical_tuple_length:
  has_types ts vs ==>
  LENGTH (enc (Tuple ts) (ListV vs)) =
    SUM (MAP abi_member_head_size ts) +
    SUM (MAP2 abi_member_tail_size ts vs)
Proof
  simp[has_type_def, Once enc_def] >> strip_tac >>
  drule enc_tuple_length_exact >> simp[]
QED

(* A prefix identifies an arbitrary member, not only member zero.  The
   tail offset is relative to the containing tuple/array data base. *)
Theorem canonical_member_ranges:
  has_types (pre ++ ty::post) (pvs ++ v::rest) /\
  LENGTH pre = LENGTH pvs ==>
  let totlen = LENGTH (enc (Tuple (pre ++ ty::post))
                            (ListV (pvs ++ v::rest))) in
  let head = SUM (MAP abi_member_head_size pre) in
  let tail = SUM (MAP abi_member_head_size (pre ++ ty::post)) +
             SUM (MAP2 abi_member_tail_size pre pvs) in
    head + abi_member_head_size ty <= totlen /\
    (is_dynamic ty ==> tail + LENGTH (enc ty v) <= totlen) /\
    (~is_dynamic ty ==> head + LENGTH (enc ty v) <= totlen)
Proof
  strip_tac >>
  drule canonical_tuple_length >>
  gvs[has_type_def, has_types_append, MAP_APPEND, SUM_APPEND, MAP2_APPEND] >>
  strip_tac >>
  Cases_on `is_dynamic ty`
  >- simp[abi_member_head_size_def, abi_member_tail_size_def] >>
  `LENGTH (enc ty v) = static_length ty` by
    (irule (cj 1 enc_has_static_length) >> simp[]) >>
  simp[abi_member_head_size_def, abi_member_tail_size_def]
QED

Theorem have_type_replicate:
  !vs. have_type ty vs ==>
    has_types (REPLICATE (LENGTH vs) ty) vs
Proof
  Induct >> simp[has_type_def]
QED

Theorem uniform_member_sizes[local]:
  !vs. SUM (MAP abi_member_head_size (REPLICATE (LENGTH vs) ty)) =
         LENGTH vs * abi_member_head_size ty /\
       MAP2 abi_member_tail_size (REPLICATE (LENGTH vs) ty) vs =
         MAP (abi_member_tail_size ty) vs
Proof
  Induct >> simp[REPLICATE, MULT_CLAUSES]
QED

Theorem canonical_array_length:
  has_type (Array bound ty) (ListV vs) ==>
  LENGTH (enc (Array bound ty) (ListV vs)) =
    (if bound = NONE then 32 else 0) +
    LENGTH vs * abi_member_head_size ty +
    SUM (MAP (abi_member_tail_size ty) vs)
Proof
  strip_tac >>
  `has_types (REPLICATE (LENGTH vs) ty) vs` by
    (irule have_type_replicate >> gvs[has_type_def]) >>
  Cases_on `bound` >>
  simp[Once enc_def] >>
  drule enc_tuple_length_exact >>
  simp[enc_number_def, LENGTH_word_to_bytes, uniform_member_sizes] >>
  metis_tac[]
QED


Theorem have_type_append[local]:
  !xs ys. have_type ty (xs ++ ys) <=> have_type ty xs /\ have_type ty ys
Proof
  Induct >> pure_rewrite_tac[APPEND, has_type_def] >> metis_tac[]
QED

Theorem canonical_array_member_ranges:
  has_type (Array bound ty) (ListV (pre ++ v::post)) ==>
  let totlen = LENGTH (enc (Array bound ty) (ListV (pre ++ v::post))) in
  let data = if bound = NONE then 32 else 0 in
  let head = LENGTH pre * abi_member_head_size ty in
  let tail = LENGTH (pre ++ v::post) * abi_member_head_size ty +
             SUM (MAP (abi_member_tail_size ty) pre) in
    data + head + abi_member_head_size ty <= totlen /\
    (is_dynamic ty ==> data + tail + LENGTH (enc ty v) <= totlen) /\
    (~is_dynamic ty ==> data + head + LENGTH (enc ty v) <= totlen)
Proof
  strip_tac >> drule canonical_array_length >>
  Cases_on `bound` >>
  gvs[has_type_def, have_type_append, MAP_APPEND, SUM_APPEND,
      LEFT_ADD_DISTRIB, MULT_CLAUSES] >>
  strip_tac >> Cases_on `is_dynamic ty` >>
  gvs[abi_member_head_size_def, abi_member_tail_size_def] >>
  TRY (decide_tac >> NO_TAC) >>
  `LENGTH (enc ty v) = static_length ty` by
    (irule (cj 1 enc_has_static_length) >> simp[]) >>
  gvs[] >> decide_tac
QED

(* The interval transport is intentionally separate from canonicality.  The
   STRICT endpoint bound excludes 2^256, which would encode hi as zero. *)
Theorem abi_interval_word_guards:
  off + sz <= len /\ base + len < dimword (:'a) ==>
    w2n ((n2w base : 'a word) + n2w off) = base + off /\
    w2n ((n2w base : 'a word) + n2w off + n2w sz) = base + off + sz /\
    ~((n2w base + n2w off : 'a word) <+ n2w base) /\
    ~((n2w base + n2w off + n2w sz : 'a word) >+ n2w (base + len))
Proof
  strip_tac >>
  `base < dimword (:'a) /\ off < dimword (:'a) /\ sz < dimword (:'a) /\
   base + off < dimword (:'a) /\ base + (off + sz) < dimword (:'a)` by decide_tac >>
  simp[word_add_n2w, w2n_n2w, WORD_LO, WORD_HI, GSYM ADD_ASSOC]
QED

Theorem compile_getelemptr_abi_canonical_guard:
  has_types (pre ++ ty::post) (pvs ++ v::rest) /\
  LENGTH pre = LENGTH pvs /\ is_dynamic ty /\
  base + LENGTH (enc (Tuple (pre ++ ty::post))
                    (ListV (pvs ++ v::rest))) < dimword (:'a) ==>
  let off = SUM (MAP abi_member_head_size (pre ++ ty::post)) +
            SUM (MAP2 abi_member_tail_size pre pvs) in
  ~((n2w base + n2w off : 'a word) <+ n2w base)
Proof
  strip_tac >> drule_all canonical_member_ranges >> simp[] >> strip_tac >>
  irule (cj 3 abi_interval_word_guards) >>
  qexistsl [`LENGTH (enc (Tuple (pre ++ ty::post)) (ListV (pvs ++ v::rest)))`,
    `LENGTH (enc ty v)`] >>
  simp[]
QED

Theorem compile_abi_decode_dyn_elem_ptr_canonical_guards:
  has_type (Array bound ty) (ListV (pre ++ v::post)) /\
  is_dynamic ty /\ elem_abi_sz <= LENGTH (enc ty v) /\
  base + LENGTH (enc (Array bound ty) (ListV (pre ++ v::post))) <
    dimword (:'a) ==>
  let data = if bound = NONE then 32 else 0 in
  let off = LENGTH (pre ++ v::post) * abi_member_head_size ty +
            SUM (MAP (abi_member_tail_size ty) pre) in
    ~((n2w (base + data) + n2w off : 'a word) <+ n2w (base + data)) /\
    ~((n2w (base + data) + n2w off + n2w elem_abi_sz : 'a word) >+
       n2w (base + LENGTH (enc (Array bound ty) (ListV (pre ++ v::post)))))
Proof
  strip_tac >> drule canonical_array_member_ranges >> simp[] >> strip_tac >>
  qabbrev_tac `data = if bound = NONE then 32 else 0` >>
  qabbrev_tac `off = LENGTH (pre ++ v::post) * abi_member_head_size ty +
                    SUM (MAP (abi_member_tail_size ty) pre)` >>
  qabbrev_tac `totlen = LENGTH (enc (Array bound ty) (ListV (pre ++ v::post)))` >>
  `data + off + elem_abi_sz <= totlen` by
    (Cases_on `bound` >> gvs[Abbr `data`, Abbr `off`, Abbr `totlen`] >> decide_tac) >>
  `base + data + (totlen - data) < dimword (:'a)` by decide_tac >>
  `off + elem_abi_sz <= totlen - data` by decide_tac >>
  drule_all abi_interval_word_guards >>
  simp[Abbr `off`]
QED

(* Integrity check for this boundary theory.  These are arithmetic/layout
   results, not decoder execution or a theorem about loading the offset word.
   Consumers still establish loaded-offset agreement and metadata size bounds. *)
val _ = List.app (fn (_, th) =>
  if List.all (fn s => s = "DISK_THM") (#1 (Tag.dest_tag (Thm.tag th)))
  then () else raise Fail "abiDecodeRanges: oracle dependency")
  (DB.thms "abiDecodeRanges");
