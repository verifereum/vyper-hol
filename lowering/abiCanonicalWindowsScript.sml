(* Canonical ABI child windows, including the actual encoded offset words. *)
Theory abiCanonicalWindows
Ancestors
  abiDecodeRanges contractABI arithmetic list rich_list byte

Theorem abi_window_dimindex[simp,local]: dimindex (:256) = 256
Proof
  CONV_TAC fcpLib.INDEX_CONV
QED

Definition abi_tuple_heads_def:
  abi_tuple_heads hl tl (ty::tys) (v::vs) =
    (if is_dynamic ty then enc_number (Uint 256) (NumV (hl + tl))
     else enc ty v) ::
    abi_tuple_heads hl (tl + abi_member_tail_size ty v) tys vs /\
  abi_tuple_heads _ _ _ _ = []
End

Definition abi_tuple_tails_def:
  abi_tuple_tails (ty::tys) (v::vs) =
    (if is_dynamic ty then enc ty v else []) :: abi_tuple_tails tys vs /\
  abi_tuple_tails _ _ = []
End

Theorem enc_tuple_parts:
  !tys vs hl tl hds tls.
  enc_tuple hl tl tys vs hds tls =
    FLAT (REVERSE hds) ++ FLAT (abi_tuple_heads hl tl tys vs) ++
    FLAT (REVERSE tls) ++ FLAT (abi_tuple_tails tys vs)
Proof
  Induct >> Cases_on `vs` >>
  simp[Once enc_def, abi_tuple_heads_def, abi_tuple_tails_def,
       REV_REVERSE_LEM, REVERSE_APPEND, FLAT_APPEND, abi_member_tail_size_def] >>
  rpt gen_tac >> rename1 `is_dynamic ty` >>
  Cases_on `is_dynamic ty` >> simp[abi_member_tail_size_def]
QED

Theorem abi_tuple_head_length:
  has_type ty v ==>
  LENGTH (if is_dynamic ty then word_to_bytes (n2w off : 256 word) T
          else enc ty v) = abi_member_head_size ty
Proof
  strip_tac >> Cases_on `is_dynamic ty` >>
  simp[abi_member_head_size_def] >>
  irule (cj 1 enc_has_static_length) >> simp[]
QED

Theorem abi_tuple_heads_length:
  !tys vs hl tl. has_types tys vs ==>
  LENGTH (FLAT (abi_tuple_heads hl tl tys vs)) =
    SUM (MAP abi_member_head_size tys)
Proof
  Induct >> Cases_on `vs` >>
  simp[has_type_def, abi_tuple_heads_def] >>
  rpt strip_tac >> rename1 `enc ty av` >>
  `LENGTH (if is_dynamic ty then word_to_bytes (n2w (hl + tl) : 256 word) T
           else enc ty av) = abi_member_head_size ty` by
    (irule abi_tuple_head_length >> simp[]) >>
  simp[]
QED

Theorem abi_tuple_tails_length:
  !tys vs. LENGTH tys = LENGTH vs ==>
  LENGTH (FLAT (abi_tuple_tails tys vs)) =
    SUM (MAP2 abi_member_tail_size tys vs)
Proof
  Induct >> Cases_on `vs` >> simp[abi_tuple_tails_def] >>
  rpt gen_tac >> rename1 `is_dynamic ty` >>
  Cases_on `is_dynamic ty` >> simp[abi_member_tail_size_def]
QED

Theorem abi_tuple_heads_append:
  !pre pvs hl tl tys vs. LENGTH pre = LENGTH pvs ==>
  abi_tuple_heads hl tl (pre ++ tys) (pvs ++ vs) =
    abi_tuple_heads hl tl pre pvs ++
    abi_tuple_heads hl (tl + SUM (MAP2 abi_member_tail_size pre pvs)) tys vs
Proof
  Induct
  >- (Cases_on `pvs` >> simp[abi_tuple_heads_def]) >>
  Cases_on `pvs` >> simp[abi_tuple_heads_def] >>
  rpt strip_tac >> first_x_assum irule >> simp[]
QED

Theorem abi_tuple_tails_append:
  !pre pvs tys vs. LENGTH pre = LENGTH pvs ==>
  abi_tuple_tails (pre ++ tys) (pvs ++ vs) =
    abi_tuple_tails pre pvs ++ abi_tuple_tails tys vs
Proof
  Induct >> Cases_on `pvs` >> simp[abi_tuple_tails_def]
QED

Theorem canonical_member_parts:
  LENGTH pre = LENGTH pvs ==>
  let hl = head_lengths (pre ++ ty::post) 0 in
  let tl = SUM (MAP2 abi_member_tail_size pre pvs) in
  enc (Tuple (pre ++ ty::post)) (ListV (pvs ++ v::rest)) =
    FLAT (abi_tuple_heads hl 0 pre pvs) ++
    (if is_dynamic ty then enc_number (Uint 256) (NumV (hl + tl))
     else enc ty v) ++
    FLAT (abi_tuple_heads hl (tl + abi_member_tail_size ty v) post rest) ++
    FLAT (abi_tuple_tails pre pvs) ++
    (if is_dynamic ty then enc ty v else []) ++
    FLAT (abi_tuple_tails post rest)
Proof
  strip_tac >>
  simp[Once enc_def, enc_tuple_parts, abi_tuple_heads_append,
       abi_tuple_tails_append, abi_tuple_heads_def, abi_tuple_tails_def,
       FLAT_APPEND, APPEND_ASSOC, MAP2_APPEND, SUM_APPEND]
QED

Theorem abi_window_from_parts:
  bs = prefix ++ (chunk ++ suffix) /\ off = LENGTH prefix /\ n = LENGTH chunk ==>
  TAKE n (DROP off bs) = chunk
Proof
  strip_tac >> gvs[] >>
  pure_rewrite_tac[GSYM APPEND_ASSOC, DROP_LENGTH_APPEND, TAKE_LENGTH_APPEND] >>
  REFL_TAC
QED

Theorem canonical_member_head_window:
  has_types (pre ++ ty::post) (pvs ++ v::rest) /\
  LENGTH pre = LENGTH pvs ==>
  let hl = head_lengths (pre ++ ty::post) 0 in
  let tl = SUM (MAP2 abi_member_tail_size pre pvs) in
  TAKE (abi_member_head_size ty)
    (DROP (SUM (MAP abi_member_head_size pre))
      (enc (Tuple (pre ++ ty::post)) (ListV (pvs ++ v::rest)))) =
    (if is_dynamic ty then enc_number (Uint 256) (NumV (hl + tl))
     else enc ty v)
Proof
  strip_tac >>
  `has_types pre pvs /\ has_type ty v /\ has_types post rest` by
    gvs[has_types_append, has_type_def] >>
  simp_tac bool_ss [LET_THM] >> irule abi_window_from_parts >>
  conj_tac >- simp[abi_tuple_head_length] >>
  qexistsl_tac
    [`FLAT (abi_tuple_heads (head_lengths (pre ++ ty::post) 0) 0 pre pvs)`,
     `FLAT (abi_tuple_heads (head_lengths (pre ++ ty::post) 0)
       (SUM (MAP2 abi_member_tail_size pre pvs) + abi_member_tail_size ty v)
       post rest) ++ FLAT (abi_tuple_tails pre pvs) ++
       (if is_dynamic ty then enc ty v else []) ++
       FLAT (abi_tuple_tails post rest)`] >>
  conj_tac
  >- (pure_rewrite_tac[APPEND_ASSOC] >>
      match_mp_tac (SIMP_RULE pureSimps.pure_ss [LET_THM] canonical_member_parts) >>
      first_assum ACCEPT_TAC) >>
  simp[abi_tuple_heads_length]
QED

Theorem canonical_member_tail_window:
  has_types (pre ++ ty::post) (pvs ++ v::rest) /\
  LENGTH pre = LENGTH pvs /\ is_dynamic ty ==>
  TAKE (LENGTH (enc ty v))
    (DROP (head_lengths (pre ++ ty::post) 0 +
           SUM (MAP2 abi_member_tail_size pre pvs))
      (enc (Tuple (pre ++ ty::post)) (ListV (pvs ++ v::rest)))) = enc ty v
Proof
  strip_tac >>
  `has_types pre pvs /\ has_type ty v /\ has_types post rest` by
    gvs[has_types_append, has_type_def] >>
  irule abi_window_from_parts >>
  conj_tac >- REFL_TAC >>
  qexistsl_tac
    [`FLAT (abi_tuple_heads (head_lengths (pre ++ ty::post) 0) 0 pre pvs) ++
      enc_number (Uint 256)
        (NumV (head_lengths (pre ++ ty::post) 0 +
               SUM (MAP2 abi_member_tail_size pre pvs))) ++
      FLAT (abi_tuple_heads (head_lengths (pre ++ ty::post) 0)
        (SUM (MAP2 abi_member_tail_size pre pvs) + abi_member_tail_size ty v)
        post rest) ++ FLAT (abi_tuple_tails pre pvs)`,
     `FLAT (abi_tuple_tails post rest)`] >>
  conj_tac
  >- (pure_rewrite_tac[APPEND_ASSOC] >>
      qpat_x_assum `is_dynamic ty` (fn dyn =>
        match_mp_tac (SIMP_RULE bool_ss [LET_THM,dyn]
          canonical_member_parts)) >>
      first_assum ACCEPT_TAC) >>
  simp[abi_tuple_heads_length, abi_tuple_tails_length,
       head_lengths_acc, MAP_APPEND, SUM_APPEND, abi_member_head_size_def] >>
  decide_tac
QED

val () = List.app (fn (n,th) =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th) in
    if null (Thm.hyp th) andalso null axioms andalso
       List.all (fn s => s = "DISK_THM") oracles then
      print ("ABI_CANONICAL_WINDOWS_KERNEL_CLOSED " ^ n ^ "\n")
    else raise Fail ("ABI canonical window not kernel closed: " ^ n)
  end) (DB.thms "abiCanonicalWindows");
