(* TOP-LEVEL: separate ABI field heads from their accumulated tail bytes.
   Payloads are complete child encodings; dynamic offsets remain relative
   to the containing aggregate, including during suffix traversal. *)
Theory abiFieldLayoutDefs
Ancestors
  contractABI list pair rich_list words arithmetic
Libs wordsLib

Definition abi_field_head_def:
  abi_field_head tail_offset is_dyn (payload:word8 list) =
    if is_dyn then word_to_bytes (n2w tail_offset : bytes32) T else payload
End

Definition abi_field_tail_def:
  abi_field_tail is_dyn (payload:word8 list) = if is_dyn then payload else []
End

Definition abi_field_heads_def:
  abi_field_heads tail_offset [] = [] /\
  abi_field_heads tail_offset ((is_dyn,payload)::fields) =
    abi_field_head tail_offset is_dyn payload ++
    abi_field_heads (tail_offset + LENGTH (abi_field_tail is_dyn payload)) fields
End

Definition abi_field_tails_def:
  abi_field_tails [] = [] /\
  abi_field_tails ((is_dyn,payload)::fields) =
    abi_field_tail is_dyn payload ++ abi_field_tails fields
End

Definition abi_field_head_size_def:
  abi_field_head_size ([]:(bool # word8 list) list) = 0 /\
  abi_field_head_size ((is_dyn,payload)::fields) =
    (if is_dyn then 32 else LENGTH payload) + abi_field_head_size fields
End

Definition abi_field_tail_size_def:
  abi_field_tail_size fields = LENGTH (abi_field_tails fields)
End

Definition abi_field_bytes_def:
  abi_field_bytes tail_offset fields = abi_field_heads tail_offset fields ++ abi_field_tails fields
End

Theorem abi_field_head_length[simp]:
  !tail_offset is_dyn payload.
    LENGTH (abi_field_head tail_offset is_dyn payload) = if is_dyn then 32 else LENGTH payload
Proof
  rpt gen_tac >> Cases_on `is_dyn` >> simp[abi_field_head_def]
QED

Theorem abi_field_heads_length[simp]:
  !fields tail_offset. LENGTH (abi_field_heads tail_offset fields) = abi_field_head_size fields
Proof
  Induct_on `fields` >- simp[abi_field_heads_def, abi_field_head_size_def] >>
  Cases >> simp[abi_field_heads_def, abi_field_head_size_def]
QED

Theorem abi_field_tail_size_nil[simp]:
  abi_field_tail_size [] = 0
Proof
  simp[abi_field_tail_size_def, abi_field_tails_def]
QED

Theorem abi_field_tail_size_cons[simp]:
  !is_dyn payload fields.
    abi_field_tail_size ((is_dyn,payload)::fields) =
      LENGTH (abi_field_tail is_dyn payload) + abi_field_tail_size fields
Proof
  simp[abi_field_tail_size_def, abi_field_tails_def]
QED

Theorem abi_field_bytes_length[simp]:
  !fields tail_offset.
    LENGTH (abi_field_bytes tail_offset fields) = abi_field_head_size fields + abi_field_tail_size fields
Proof
  simp[abi_field_bytes_def, abi_field_tail_size_def]
QED

Theorem abi_field_head_size_append:
  !left right.
    abi_field_head_size (left ++ right) = abi_field_head_size left + abi_field_head_size right
Proof
  Induct_on `left` >- simp[abi_field_head_size_def] >>
  Cases >> gen_tac >> simp_tac list_ss [abi_field_head_size_def] >>
  first_x_assum (qspec_then `right` SUBST1_TAC) >> decide_tac
QED

Theorem abi_field_tails_append:
  !left right. abi_field_tails (left ++ right) = abi_field_tails left ++ abi_field_tails right
Proof
  Induct_on `left` >- simp[abi_field_tails_def] >>
  Cases >> gen_tac >> simp_tac list_ss [abi_field_tails_def] >>
  first_x_assum (qspec_then `right` SUBST1_TAC) >> simp_tac bool_ss [APPEND_ASSOC]
QED

Theorem abi_field_tail_size_append:
  !left right.
    abi_field_tail_size (left ++ right) = abi_field_tail_size left + abi_field_tail_size right
Proof
  simp[abi_field_tail_size_def, abi_field_tails_append]
QED

Theorem abi_field_heads_append:
  !left right tail_offset.
    abi_field_heads tail_offset (left ++ right) =
      abi_field_heads tail_offset left ++
      abi_field_heads (tail_offset + abi_field_tail_size left) right
Proof
  Induct_on `left` >- simp[abi_field_heads_def] >>
  Cases >> rpt gen_tac >> rename1 `abi_field_heads _ ((is_dyn,payload)::left ++ right) = _` >>
  simp_tac list_ss [abi_field_heads_def] >>
  simp_tac bool_ss [abi_field_tail_size_cons, APPEND_ASSOC, ADD_ASSOC] >>
  first_x_assum (qspecl_then [`right`, `tail_offset + LENGTH (abi_field_tail is_dyn payload)`] SUBST1_TAC) >>
  simp_tac bool_ss [APPEND_ASSOC, ADD_ASSOC]
QED

val () = List.app (fn (name,th) =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th)
  in if null axioms andalso null (Thm.hyp th) andalso
      List.all (fn s => s = "DISK_THM") oracles
    then () else raise Fail ("unclosed ABI field head/tail layout: " ^ name)
  end) (DB.thms "abiFieldLayoutDefs")
