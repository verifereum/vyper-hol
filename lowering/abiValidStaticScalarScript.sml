(* Valid static scalar encodings agree with their canonical readable prefix. *)
Theory abiValidStaticScalar
Ancestors
  contractABI venomMemProofs vfmTypes byte words integer_word list rich_list arithmetic

Definition abi_static_prefix_def:
  abi_static_prefix at <=>
    !bs. valid_enc at bs /\ static_length at <= LENGTH bs ==>
      enc at (dec at bs) = TAKE (static_length at) bs
End

Theorem abi_static_prefix_numbers:
  (!n. abi_static_prefix (Uint n)) /\ (!n. abi_static_prefix (Int n)) /\
  abi_static_prefix Address /\ abi_static_prefix Bool /\
  (!n m. abi_static_prefix (Fixed n m)) /\ (!n m. abi_static_prefix (Ufixed n m))
Proof
  rpt conj_tac >> rpt gen_tac >>
  simp[abi_static_prefix_def] >> rpt strip_tac >>
  irule word_bytes_roundtrip_proof >>
  CONV_TAC (DEPTH_CONV fcpLib.INDEX_CONV) >>
  simp[LENGTH_TAKE_EQ, dividesTheory.divides_def]
QED

Theorem abi_zero_bytes_replicate:
  !bs:word8 list. EVERY ((=) 0w) bs ==> bs = REPLICATE (LENGTH bs) 0w
Proof
  Induct >> simp[] >> rpt strip_tac >> gvs[]
QED

Theorem abi_valid_fixed_bytes_prefix:
  valid_enc (Bytes (SOME n)) bs /\ 32 <= LENGTH bs ==>
  enc (Bytes (SOME n)) (dec (Bytes (SOME n)) bs) = TAKE 32 bs
Proof
  simp_tac bool_ss [valid_enc_def, valid_bytes_bound_def] >> strip_tac >>
  drule abi_zero_bytes_replicate >>
  simp[LENGTH_DROP, LENGTH_TAKE_EQ] >> strip_tac >>
  `TAKE n bs ++ DROP n (TAKE 32 bs) = TAKE 32 bs` by
    (qspecl_then [`n`, `TAKE 32 bs`] mp_tac TAKE_DROP >>
     asm_simp_tac bool_ss [TAKE_TAKE, MIN_DEF]) >>
  gvs[Once enc_def, Once dec_def, TAKE_TAKE_MIN, MIN_DEF]
QED

Theorem abi_static_prefix_fixed_bytes:
  !n. abi_static_prefix (Bytes (SOME n))
Proof
  simp[abi_static_prefix_def, abi_valid_fixed_bytes_prefix]
QED

val () = List.app (fn (n,th) =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th) in
    if null (Thm.hyp th) andalso null axioms andalso
       List.all (fn s => s = "DISK_THM") oracles then
      print ("ABI_VALID_STATIC_SCALAR_KERNEL_CLOSED " ^ n ^ "\n")
    else raise Fail ("ABI valid static scalar not kernel closed: " ^ n)
  end) (DB.thms "abiValidStaticScalar");
