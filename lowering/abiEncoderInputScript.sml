(* Pure source representation for all encoder descriptors.
   Static slices cover every byte, including omitted sparse-array defaults.
   Bytestring padding is deliberately not an input requirement. *)
Theory abiEncoderInput
Ancestors
  abiDecodeRanges compileEnv valueEncoding contractABI words list rich_list arithmetic

Definition abi_encoder_member_span_def:
  abi_encoder_member_span (infos:(abi_enc_info # num # num # bool) list) =
    SUM (MAP (\(_,_,n,_). n) infos)
End

Definition abi_encoder_tuple_type_def:
  abi_encoder_tuple_type at ats <=>
    at = Tuple ats \/ ?n ct. at = Array (SOME n) ct /\ ats = REPLICATE n ct
End

Inductive abi_encoder_input:
[word:]
  (!at av sb cap mem.
    has_type at av /\ ~is_dynamic at /\ static_length at = 32 /\ 32 <= cap /\
    mem_bytes_at sb 32 mem = enc at av ==>
    abi_encoder_input AbiPrimWord at av sb cap mem)
[copy:]
  (!sz at av sb cap mem.
    has_type at av /\ ~is_dynamic at /\ static_length at = sz /\ sz <= cap /\
    mem_bytes_at sb sz mem = enc at av ==>
    abi_encoder_input (AbiCopy sz) at av sb cap mem)
[bytes:]
  (!maxlen at bs sb cap mem.
    (at = Bytes NONE \/ at = String) /\ has_type at (BytesV bs) /\
    LENGTH bs <= maxlen /\ 32 + LENGTH bs <= cap /\
    mem_word_at sb mem = n2w (LENGTH bs) /\
    mem_bytes_at (sb + 32) (LENGTH bs) mem = bs ==>
    abi_encoder_input (AbiBytestring maxlen) at (BytesV bs) sb cap mem)
[array:]
  (!ei abi_sz mem_sz dyn ct avs sb cap mem.
    has_type (Array NONE ct) (ListV avs) /\
    abi_sz = abi_member_head_size ct /\ dyn = is_dynamic ct /\
    32 + LENGTH avs * mem_sz <= cap /\
    mem_word_at sb mem = n2w (LENGTH avs) /\
    (!i. i < LENGTH avs ==>
      abi_encoder_input ei ct (EL i avs) (sb + 32 + i * mem_sz) mem_sz mem) ==>
    abi_encoder_input (AbiDynArray ei abi_sz mem_sz dyn) (Array NONE ct) (ListV avs) sb cap mem)
[complex:]
  (!infos at ats avs sb cap mem.
    abi_encoder_tuple_type at ats /\ has_type at (ListV avs) /\
    LENGTH infos = LENGTH ats /\ LENGTH ats = LENGTH avs /\
    abi_encoder_member_span infos <= cap /\
    (!i ei abi_sz mem_sz dyn. i < LENGTH infos /\ EL i infos = (ei,abi_sz,mem_sz,dyn) ==>
      abi_sz = abi_member_head_size (EL i ats) /\ dyn = is_dynamic (EL i ats) /\
      abi_encoder_input ei (EL i ats) (EL i avs)
        (sb + abi_encoder_member_span (TAKE i infos)) mem_sz mem) ==>
    abi_encoder_input (AbiComplex infos) at (ListV avs) sb cap mem)
End

Theorem abi_encoder_input_typed:
  abi_encoder_input ei at av sb cap mem ==> has_type at av
Proof
  simp_tac bool_ss [Once abi_encoder_input_cases] >> rpt strip_tac >> gvs[]
QED

Theorem abi_encoder_input_word_iff:
  abi_encoder_input AbiPrimWord at av sb cap mem <=>
  has_type at av /\ ~is_dynamic at /\ static_length at = 32 /\ 32 <= cap /\
  mem_bytes_at sb 32 mem = enc at av
Proof
  simp[Once abi_encoder_input_cases]
QED

Theorem abi_encoder_input_copy_iff:
  abi_encoder_input (AbiCopy sz) at av sb cap mem <=>
  has_type at av /\ ~is_dynamic at /\ static_length at = sz /\ sz <= cap /\
  mem_bytes_at sb sz mem = enc at av
Proof
  simp[Once abi_encoder_input_cases] >> eq_tac >> rpt strip_tac >> gvs[]
QED

Theorem abi_encoder_input_bytes_iff:
  abi_encoder_input (AbiBytestring maxlen) at av sb cap mem <=>
  ?bs. av = BytesV bs /\ (at = Bytes NONE \/ at = String) /\ has_type at (BytesV bs) /\
    LENGTH bs <= maxlen /\ 32 + LENGTH bs <= cap /\
    mem_word_at sb mem = n2w (LENGTH bs) /\ mem_bytes_at (sb + 32) (LENGTH bs) mem = bs
Proof
  simp[Once abi_encoder_input_cases] >> metis_tac[]
QED

Theorem abi_encoder_input_capacity:
  abi_encoder_input ei at av sb cap mem /\ cap <= larger ==>
  abi_encoder_input ei at av sb larger mem
Proof
  strip_tac >>
  qpat_x_assum `abi_encoder_input _ _ _ _ _ _`
    (strip_assume_tac o ONCE_REWRITE_RULE [abi_encoder_input_cases]) >>
  gvs[] >> ONCE_REWRITE_TAC [abi_encoder_input_cases] >> asm_simp_tac (srw_ss()) [LET_THM] >>
  gvs[AC ADD_COMM ADD_ASSOC, MULT_COMM] >>
  FIRST [decide_tac,
    rename1 `abi_encoder_tuple_type at ats` >> qexists_tac `ats` >> gvs[] >> decide_tac]
QED

val () = List.app (fn (n,th) =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th) in
    if null (Thm.hyp th) andalso null axioms andalso
       List.all (fn s => s = "DISK_THM") oracles then
      print ("ABI_ENCODER_INPUT_KERNEL_CLOSED " ^ n ^ "\n")
    else raise Fail ("ABI encoder input not kernel closed: " ^ n)
  end) (DB.thms "abiEncoderInput");
