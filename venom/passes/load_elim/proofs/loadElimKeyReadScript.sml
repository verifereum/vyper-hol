Theory loadElimKeyRead
Ancestors
  loadElimDefs memLocDefs venomState venomEffects words list

(* Address resolution is partial: a fixed location must describe exactly one
   word of the selected address space, at a representable address. *)
Definition le_key_address_def:
  (le_key_address space (LK_Op op) s =
     OPTION_MAP w2n (eval_operand op s)) /\
  (le_key_address space (LK_Loc ml) s =
     case memloc_runtime_region ml s of
       NONE => NONE
     | SOME (a,n) =>
         if n = addr_space_word_scale space /\ a < dimword (:256)
         then SOME a else NONE)
End

(* No arbitrary read value is assigned to an unsupported address space. *)
Definition le_read_address_def:
  le_read_address space a (s:venom_state) =
    case space of
      AddrSp_Memory => SOME (mload a s)
    | AddrSp_Storage => SOME (sload (n2w a) s)
    | AddrSp_Transient => SOME (tload (n2w a) s)
    | AddrSp_Calldata => SOME (word_of_bytes T (0w:bytes32)
        (TAKE 32 (DROP a s.vs_call_ctx.cc_calldata ++ REPLICATE 32 0w)))
    | AddrSp_Data => SOME (word_of_bytes T (0w:bytes32)
        (TAKE 32 (DROP a s.vs_data_section ++ REPLICATE 32 0w)))
    | _ => NONE
End

Definition le_key_read_def:
  le_key_read space k s =
    case le_key_address space k s of
      NONE => NONE
    | SOME a => le_read_address space a s
End

Theorem le_key_address_operand[simp]:
  le_key_address space (LK_Op op) s =
    OPTION_MAP w2n (eval_operand op s)
Proof
  simp[le_key_address_def]
QED

Theorem le_key_address_location:
  memloc_runtime_region ml s = SOME (a,n) ==>
  le_key_address space (LK_Loc ml) s =
    if n = addr_space_word_scale space /\ a < dimword (:256)
    then SOME a else NONE
Proof
  simp[le_key_address_def]
QED

Theorem le_key_address_location_undefined:
  memloc_runtime_region ml s = NONE ==>
  le_key_address space (LK_Loc ml) s = NONE
Proof
  simp[le_key_address_def]
QED

Theorem le_key_read_undefined:
  le_key_address space k s = NONE ==> le_key_read space k s = NONE
Proof
  simp[le_key_read_def]
QED

Theorem le_key_read_operand:
  eval_operand op s = SOME a ==>
  le_key_read space (LK_Op op) s = le_read_address space (w2n a) s
Proof
  simp[le_key_read_def, le_key_address_def]
QED

Theorem le_key_read_location:
  memloc_runtime_region ml s = SOME (a,addr_space_word_scale space) /\
  a < dimword (:256) ==>
  le_key_read space (LK_Loc ml) s = le_read_address space a s
Proof
  simp[le_key_read_def, le_key_address_def]
QED

Theorem le_key_read_location_invalid:
  memloc_runtime_region ml s = SOME (a,n) /\
  (n <> addr_space_word_scale space \/ dimword (:256) <= a) ==>
  le_key_read space (LK_Loc ml) s = NONE
Proof rpt strip_tac >> simp[le_key_read_def, le_key_address_def]
QED

Theorem le_read_address_spaces[simp]:
  le_read_address AddrSp_Memory a s = SOME (mload a s) /\
  le_read_address AddrSp_Storage a s = SOME (sload (n2w a) s) /\
  le_read_address AddrSp_Transient a s = SOME (tload (n2w a) s) /\
  le_read_address AddrSp_Calldata a s = SOME (word_of_bytes T (0w:bytes32)
    (TAKE 32 (DROP a s.vs_call_ctx.cc_calldata ++ REPLICATE 32 0w))) /\
  le_read_address AddrSp_Data a s = SOME (word_of_bytes T (0w:bytes32)
    (TAKE 32 (DROP a s.vs_data_section ++ REPLICATE 32 0w)))
Proof
  simp[le_read_address_def]
QED

(* Transport deliberately requires both address and contents preservation.
   Neither follows merely from the absence of a memory write. *)
Theorem le_key_read_transport:
  le_key_address space k t = le_key_address space k s /\
  (!a. le_key_address space k s = SOME a ==>
       le_read_address space a t = le_read_address space a s) ==>
  le_key_read space k t = le_key_read space k s
Proof
  strip_tac >> simp[le_key_read_def] >>
  Cases_on `le_key_address space k s` >> simp[]
QED

Theorem le_key_address_operand_transport:
  eval_operand op t = eval_operand op s ==>
  le_key_address space (LK_Op op) t = le_key_address space (LK_Op op) s
Proof
  simp[]
QED

Theorem le_key_address_location_transport:
  memloc_runtime_region ml t = memloc_runtime_region ml s ==>
  le_key_address space (LK_Loc ml) t = le_key_address space (LK_Loc ml) s
Proof
  simp[le_key_address_def]
QED
