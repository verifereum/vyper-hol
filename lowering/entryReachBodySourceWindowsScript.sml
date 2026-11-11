Theory entryReachBodySourceWindows
Ancestors
  entryReachBodySourceLayout entryReachBodyLayoutWindows
  abiCanonicalWindows abiDecodeRanges vyperABI vyperValue list rich_list

(* Keep whole-list conversion evidence intact; the slice witnesses identify
   a member of its output, not independently converted prefix/suffix lists. *)
Theorem entry_source_member_head_window:
  EVERY (entry_abi_support env) tys /\
  LIST_REL (\ty v. ?tv. evaluate_type env ty = SOME tv /\ value_has_type tv v) tys vs /\
  vyper_to_abi_list env tys vs = SOME (pvs ++ v::rest) /\
  MAP (vyper_to_abi_type env) tys = pre ++ ty::post /\
  LENGTH pre = LENGTH pvs ==>
  let hl = head_lengths (pre ++ ty::post) 0 in
  let tl = SUM (MAP2 abi_member_tail_size pre pvs) in
  TAKE (abi_member_head_size ty)
    (DROP (SUM (MAP abi_member_head_size pre))
      (enc (Tuple (pre ++ ty::post)) (ListV (pvs ++ v::rest)))) =
    (if is_dynamic ty then enc_number (Uint 256) (NumV (hl + tl))
     else enc ty v)
Proof
  strip_tac >> drule_all entry_source_list_conversion_layout >>
  strip_tac >> irule entry_layout_member_head_window >> metis_tac[]
QED

Theorem entry_source_member_tail_window:
  EVERY (entry_abi_support env) tys /\
  LIST_REL (\ty v. ?tv. evaluate_type env ty = SOME tv /\ value_has_type tv v) tys vs /\
  vyper_to_abi_list env tys vs = SOME (pvs ++ v::rest) /\
  MAP (vyper_to_abi_type env) tys = pre ++ ty::post /\
  LENGTH pre = LENGTH pvs /\ is_dynamic ty ==>
  TAKE (LENGTH (enc ty v))
    (DROP (head_lengths (pre ++ ty::post) 0 +
           SUM (MAP2 abi_member_tail_size pre pvs))
      (enc (Tuple (pre ++ ty::post)) (ListV (pvs ++ v::rest)))) = enc ty v
Proof
  strip_tac >> drule_all entry_source_list_conversion_layout >>
  strip_tac >> irule entry_layout_member_tail_window >> metis_tac[]
QED
