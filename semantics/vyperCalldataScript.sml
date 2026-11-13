(* How a deployed Vyper contract reads its raw calldata: the selector
   dispatch, the fallback, and the argument decoding of an external entry.
   Mirrors pinned Vyper's codegen_venom/module.py and abi/abi_decoder.py with
   no upper bound (`hi = None`), which is how every bounded calldata argument
   is decoded: reads past the end are zero, nested offsets wrap modulo 2^256,
   padding and trailing bytes are not checked.

   Accepted here (as by the compiled contract) but rejected by a strict ABI
   decoder:
   - any calldata: bytes after the encoding (trailing data) are ignored;
     reads past the end are zeros, so a truncated encoding decodes as if
     zero-padded.  Only the static head must be present (calldatasize check).
   - selector: fewer than 4 bytes, or an unknown selector, runs __default__
     (if declared) with no arguments instead of failing.
   - uint256, int256, bytes32, a flag with 256 members: any word.
   - Bytes[m], String[m]: the padding after the payload is not checked to be
     zero; the payload may run past the end (zeros); String bytes need not be
     valid UTF-8.
   - DynArray[t, m]: the count is checked against m only; elements may run
     past the end (zeros).
   - every dynamic value: its offset is not checked to point after the head,
     to be 32-byte aligned, or to be unshared; offsets may overlap, alias the
     head or the selector, and nested offsets wrap modulo 2^256 (only a
     top-level argument's `4 + offset` is checked not to wrap below 4).
   Rejected (NONE), as the pin asserts: a clamp failure on uintN/intN (N <
   256), address, bool, decimal, bytesM (M < 32) or a flag of fewer than 256
   members; a length or count over its bound; a short static head; a
   top-level offset wrapping below 4. *)
Theory vyperCalldata
Ancestors
  vyperABIEntries vyperValue vyperContext vyperMisc list rich_list arithmetic words byte
Libs
  wordsLib

(* ===== Raw reads (CALLDATACOPY / CALLDATALOAD) ===== *)

Definition cd_bytes_def:
  cd_bytes (cd:word8 list) (a:num) (n:num) =
    TAKE n (DROP a cd ++ REPLICATE n 0w)
End

Definition cd_word_def:
  cd_word cd (a:num) : bytes32 = word_of_bytes T 0w (cd_bytes cd a 32)
End

(* The selector as a number: the first four bytes, big-endian. *)
Definition cd_selector_def:
  cd_selector (cd:word8 list) = FOLDL (\n b. 256 * n + w2n b) 0 (TAKE 4 cd)
End

(* Address arithmetic: 256-bit words (ADD), except inside a bulk copy, which
   reads a contiguous byte range from a natural offset. *)
Definition cd_at_def:
  cd_at nat (p:num) (k:num) = if nat then p + k else (p + k) MOD dimword(:256)
End

(* ===== ABI shape of a type value ===== *)

Definition tv_abi_dynamic_def:
  tv_abi_dynamic (BaseTV (BytesT (Dynamic _))) = T /\
  tv_abi_dynamic (BaseTV (StringT _)) = T /\
  tv_abi_dynamic (ArrayTV _ (Dynamic _)) = T /\
  tv_abi_dynamic (ArrayTV t (Fixed _)) = tv_abi_dynamic t /\
  tv_abi_dynamic (TupleTV ts) = tv_abi_dynamic_list ts /\
  tv_abi_dynamic (StructTV fs) = tv_abi_dynamic_fields fs /\
  tv_abi_dynamic _ = F /\
  tv_abi_dynamic_list [] = F /\
  tv_abi_dynamic_list (t::ts) = (tv_abi_dynamic t \/ tv_abi_dynamic_list ts) /\
  tv_abi_dynamic_fields [] = F /\
  tv_abi_dynamic_fields ((_,t)::fs) =
    (tv_abi_dynamic t \/ tv_abi_dynamic_fields fs)
End

(* Static (head) size; a dynamic member takes one offset word. *)
Definition tv_abi_static_size_def:
  tv_abi_static_size (ArrayTV t (Fixed n)) =
    n * (if tv_abi_dynamic t then 32 else tv_abi_static_size t) /\
  tv_abi_static_size (TupleTV ts) = tv_abi_static_size_list ts /\
  tv_abi_static_size (StructTV fs) = tv_abi_static_size_fields fs /\
  tv_abi_static_size NoneTV = 0 /\
  tv_abi_static_size _ = 32 /\
  tv_abi_static_size_list [] = 0 /\
  tv_abi_static_size_list (t::ts) =
    (if tv_abi_dynamic t then 32 else tv_abi_static_size t) +
    tv_abi_static_size_list ts /\
  tv_abi_static_size_fields [] = 0 /\
  tv_abi_static_size_fields ((_,t)::fs) =
    (if tv_abi_dynamic t then 32 else tv_abi_static_size t) +
    tv_abi_static_size_fields fs
End

(* Embedded static size: abi_type.embedded_static_size() *)
Definition tv_abi_size_def:
  tv_abi_size t = if tv_abi_dynamic t then 32 else tv_abi_static_size t
End

(* abi_decoder.py needs_clamp *)
Definition tv_needs_clamp_def:
  tv_needs_clamp (BaseTV (UintT n)) = (n < 256) /\
  tv_needs_clamp (BaseTV (IntT n)) = (n < 256) /\
  tv_needs_clamp (BaseTV (BytesT (Fixed n))) = (n < 32) /\
  tv_needs_clamp (BaseTV _) = T /\
  tv_needs_clamp (FlagTV m) = (m < 256) /\
  tv_needs_clamp NoneTV = F /\
  tv_needs_clamp (ArrayTV _ (Dynamic _)) = T /\
  tv_needs_clamp (ArrayTV t (Fixed _)) = tv_needs_clamp t /\
  tv_needs_clamp (TupleTV ts) = tv_needs_clamp_list ts /\
  tv_needs_clamp (StructTV fs) = tv_needs_clamp_fields fs /\
  tv_needs_clamp_list [] = F /\
  tv_needs_clamp_list (t::ts) = (tv_needs_clamp t \/ tv_needs_clamp_list ts) /\
  tv_needs_clamp_fields [] = F /\
  tv_needs_clamp_fields ((_,t)::fs) =
    (tv_needs_clamp t \/ tv_needs_clamp_fields fs)
End

(* ===== Decoding ===== *)

(* One word, clamped where needs_clamp says so; NONE where the pin asserts. *)
Definition cd_word_value_def:
  cd_word_value (BaseTV (UintT n)) (w:bytes32) =
    (if w2n w < 2 ** n then SOME (IntV (&w2n w)) else NONE) /\
  cd_word_value (BaseTV (IntT n)) w =
    (if within_int_bound (Signed n) (w2i w) then SOME (IntV (w2i w))
     else NONE) /\
  cd_word_value (BaseTV AddressT) w =
    (if w2n w < 2 ** 160 then SOME (AddressV (w2w w)) else NONE) /\
  cd_word_value (BaseTV BoolT) w =
    (if w2n w <= 1 then SOME (BoolV (w = 1w)) else NONE) /\
  cd_word_value (BaseTV DecimalT) w =
    (if within_int_bound decimal_bound (w2i w) then SOME (DecimalV (w2i w))
     else NONE) /\
  cd_word_value (BaseTV (BytesT (Fixed n))) w =
    (let bs = word_to_bytes w T in
     if EVERY ($= 0w) (DROP n bs) then SOME (BytesV (TAKE n bs)) else NONE) /\
  cd_word_value (FlagTV m) w =
    (if w2n w < 2 ** m then SOME (FlagV (w2n w)) else NONE) /\
  cd_word_value _ _ = NONE
End

(* Where a member whose head is at `base + ofs` lives: a dynamic member's
   head holds an offset relative to `base` (the enclosing tuple, or a dynamic
   array's data start). *)
Definition cd_member_ptr_def:
  cd_member_ptr nat cd t base ofs =
    let head = cd_at nat base ofs in
    if tv_abi_dynamic t then cd_at nat base (w2n (cd_word cd head)) else head
End

(* `cd_decode nat cd t p`: the value of type t encoded at calldata offset p.
   A bytestring's payload is copied from the natural offset p + 32; a dynamic
   array whose element is static and unclamped is bulk-copied from its data
   start, so its elements are read at natural offsets (nat = T); otherwise
   elements are decoded one by one at word-arithmetic addresses. *)
Definition cd_decode_def:
  cd_decode nat cd (BaseTV (BytesT (Dynamic m))) p =
    (let len = w2n (cd_word cd p) in
     if m < len then NONE else SOME (BytesV (cd_bytes cd (p + 32) len))) /\
  cd_decode nat cd (BaseTV (StringT m)) p =
    (let len = w2n (cd_word cd p) in
     if m < len then NONE
     else SOME (StringV (MAP (CHR o w2n) (cd_bytes cd (p + 32) len)))) /\
  cd_decode nat cd (ArrayTV t (Dynamic m)) p =
    (let cnt = w2n (cd_word cd p) in
     if m < cnt then NONE
     else
       let bulk = (~tv_abi_dynamic t /\ ~tv_needs_clamp t) in
       case cd_decode_elems (nat \/ bulk) cd t (cd_at nat p 32) 0 cnt of
         NONE => NONE
       | SOME vs => SOME (ArrayV (DynArrayV vs))) /\
  cd_decode nat cd (ArrayTV t (Fixed n)) p =
    (case cd_decode_elems nat cd t p 0 n of
       NONE => NONE
     | SOME vs => SOME (ArrayV (make_array_value t (Fixed n) vs))) /\
  cd_decode nat cd (TupleTV ts) p =
    (case cd_decode_list nat cd ts p 0 of
       NONE => NONE
     | SOME vs => SOME (ArrayV (TupleV vs))) /\
  cd_decode nat cd (StructTV fs) p =
    (case cd_decode_list nat cd (MAP SND fs) p 0 of
       NONE => NONE
     | SOME vs => SOME (StructV (ZIP (MAP FST fs, vs)))) /\
  cd_decode nat cd NoneTV p = SOME NoneV /\
  cd_decode nat cd t p = cd_word_value t (cd_word cd p) /\

  cd_decode_elems nat cd t base i 0 = SOME [] /\
  cd_decode_elems nat cd t base i (SUC k) =
    (case cd_decode nat cd t
            (cd_member_ptr nat cd t base (i * tv_abi_size t)) of
       NONE => NONE
     | SOME v =>
       case cd_decode_elems nat cd t base (i + 1) k of
         NONE => NONE
       | SOME vs => SOME (v::vs)) /\

  cd_decode_list nat cd [] p ofs = SOME [] /\
  cd_decode_list nat cd (t::ts) p ofs =
    (case cd_decode nat cd t (cd_member_ptr nat cd t p ofs) of
       NONE => NONE
     | SOME v =>
       case cd_decode_list nat cd ts p (ofs + tv_abi_size t) of
         NONE => NONE
       | SOME vs => SOME (v::vs))
Termination
  WF_REL_TAC `inv_image ($< LEX $<) (\x. case x of
      INL (_,_,t,_) => (type_value_size t, 0)
    | INR (INL (_,_,t,_,_,k)) => (type_value_size t, k + 1)
    | INR (INR (_,_,ts,_,_)) => (list_size type_value_size ts, 0))`
  \\ rw[list_size_pair_size_map]
  \\ simp[type_value_size_def]
End

(* The argument tuple at offset 4.  A dynamic argument's offset is relative to
   4, and the pin asserts the sum does not wrap below 4
   (module.py _get_abi_arg_ptr). *)
Definition calldata_decode_args_def:
  calldata_decode_args cd [] ofs = SOME [] /\
  calldata_decode_args cd (t::ts) ofs =
    (let head = 4 + ofs in
     let p = if tv_abi_dynamic t
             then (4 + w2n (cd_word cd head)) MOD dimword(:256) else head in
     if p < 4 then NONE
     else
       case cd_decode F cd t p of
         NONE => NONE
       | SOME v =>
         case calldata_decode_args cd ts (ofs + tv_abi_size t) of
           NONE => NONE
         | SOME vs => SOME (v::vs))
End

(* ===== Dispatch ===== *)

Definition is_default_decl_def:
  is_default_decl (FunctionDecl External _ _ _ name _ _ _ _) =
    (name = "__default__") /\
  is_default_decl _ = F
End

(* The external entry a calldata reaches: SOME (name, args) when the contract
   runs `name` with `args`, NONE when it reverts with empty returndata before
   any function body.  Fewer than 4 bytes, or a selector matching no
   signature, takes the fallback: `__default__` with no arguments if declared,
   else `revert(0, 0)`.  A hit shorter than its static head reverts
   (calldatasize check), and so does a failed decode. *)
Definition calldata_dispatch_def:
  calldata_dispatch tops cd =
    let tenv = type_env tops in
    let hit = if LENGTH cd < 4 then NONE
              else FIND (\(name,tys). abi_method_id tenv name tys = cd_selector cd)
                        (abi_external_signatures tops) in
    case hit of
      NONE => if EXISTS is_default_decl tops then SOME ("__default__", [])
              else NONE
    | SOME (name, tys) =>
      case OPT_MMAP (evaluate_type tenv) tys of
        NONE => NONE
      | SOME tvs =>
        if LENGTH cd < 4 + SUM (MAP tv_abi_size tvs) then NONE
        else case calldata_decode_args cd tvs 0 of
               NONE => NONE
             | SOME vs => SOME (name, vs)
End

(* ===== Examples ===== *)

Definition cd_example_word_def:
  cd_example_word (n:num) : word8 list = word_to_bytes (n2w n : bytes32) T
End

Theorem calldata_decode_args_examples:
  (* a clamped word: in range, out of range *)
  calldata_decode_args ([1w;2w;3w;4w] ++ cd_example_word 5)
    [BaseTV (UintT 8)] 0 = SOME [IntV 5] /\
  calldata_decode_args ([1w;2w;3w;4w] ++ cd_example_word 256)
    [BaseTV (UintT 8)] 0 = NONE /\
  (* trailing bytes ignored *)
  calldata_decode_args ([1w;2w;3w;4w] ++ cd_example_word 5 ++ [7w])
    [BaseTV (UintT 256)] 0 = SOME [IntV 5] /\
  (* a payload past the end reads as zeros *)
  calldata_decode_args
    ([1w;2w;3w;4w] ++ cd_example_word 32 ++ cd_example_word 2)
    [BaseTV (BytesT (Dynamic 4))] 0 = SOME [BytesV [0w;0w]] /\
  (* a length over the bound *)
  calldata_decode_args
    ([1w;2w;3w;4w] ++ cd_example_word 32 ++ cd_example_word 5)
    [BaseTV (BytesT (Dynamic 4))] 0 = NONE /\
  (* a top-level offset wrapping below 4 *)
  calldata_decode_args
    ([1w;2w;3w;4w] ++ cd_example_word (dimword(:256) - 4))
    [BaseTV (BytesT (Dynamic 4))] 0 = NONE /\
  (* an offset aliasing the head: the length is the offset word itself *)
  calldata_decode_args
    ([1w;2w;3w;4w] ++ cd_example_word 0)
    [ArrayTV (BaseTV (UintT 256)) (Dynamic 3)] 0 =
      SOME [ArrayV (DynArrayV [])] /\
  (* a count with elements past the end *)
  calldata_decode_args
    ([1w;2w;3w;4w] ++ cd_example_word 32 ++ cd_example_word 2)
    [ArrayTV (BaseTV (UintT 256)) (Dynamic 3)] 0 =
      SOME [ArrayV (DynArrayV [IntV 0; IntV 0])]
Proof
  rpt conj_tac >> EVAL_TAC
QED

(* Short calldata goes to __default__ when there is one, else nowhere. *)
Theorem calldata_dispatch_fallback_examples:
  calldata_dispatch
    [FunctionDecl External Payable F F "__default__" [] [] NoneT []] [] =
    SOME ("__default__", []) /\
  calldata_dispatch
    [FunctionDecl External Nonpayable F F "f" [] [] NoneT []] [1w; 2w] = NONE
Proof
  EVAL_TAC
QED
