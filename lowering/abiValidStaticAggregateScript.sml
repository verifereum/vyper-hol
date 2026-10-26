(* Static ABI arrays and tuples reconstruct canonical prefixes recursively. *)
Theory abiValidStaticAggregate
Ancestors
  abiValidStaticMembers abiValidStaticScalar contractABI list rich_list arithmetic

Theorem abi_static_array_decode_tuple:
  !n at base hds acc. ~is_dynamic at ==>
  dec_array n (SOME (static_length at)) at base hds acc =
    dec_tuple (REPLICATE n at) base hds acc
Proof
  Induct >> simp[dec_def]
QED

Theorem abi_static_prefix_tuple:
  EVERY (\at. ~is_dynamic at /\ abi_static_prefix at) ts ==>
  abi_static_prefix (Tuple ts)
Proof
  strip_tac >> simp_tac bool_ss [abi_static_prefix_def] >> rpt strip_tac >>
  `~any_dynamic ts` by
    (fs[EVERY_MEM, any_dynamic_EXISTS, EXISTS_MEM] >> metis_tac[]) >>
  `valid_enc_tuple ts bs bs` by fs[Once valid_enc_def] >>
  drule_all abi_valid_static_members >> disch_then (qspec_then `[]` strip_assume_tac) >>
  drule_all enc_tuple_static >> strip_tac >>
  `dec (Tuple ts) bs = ListV vs` by asm_simp_tac (srw_ss()) [Once dec_def] >>
  asm_simp_tac bool_ss []
QED

Theorem abi_static_prefix_array:
  ~is_dynamic at /\ abi_static_prefix at ==>
  abi_static_prefix (Array (SOME n) at)
Proof
  strip_tac >> simp_tac bool_ss [abi_static_prefix_def] >> rpt strip_tac >>
  `EVERY (\ty. ~is_dynamic ty /\ abi_static_prefix ty) (REPLICATE n at)` by simp[] >>
  `valid_enc_tuple (REPLICATE n at) bs bs` by
    fs[valid_enc_tuple_REPLICATE, Once valid_enc_def] >>
  drule_all abi_valid_static_members >> disch_then (qspec_then `[]` strip_assume_tac) >>
  `~any_dynamic (REPLICATE n at)` by simp[any_dynamic_EXISTS] >>
  drule_all enc_tuple_static >> strip_tac >>
  `dec (Array (SOME n) at) bs = ListV vs` by
    asm_simp_tac (srw_ss()) [Once dec_def, LET_THM, abi_static_array_decode_tuple] >>
  `enc (Array (SOME n) at) (ListV vs) = enc (Tuple (REPLICATE n at)) (ListV vs)` by
    (CONV_TAC (LAND_CONV (ONCE_REWRITE_CONV [enc_def])) >>
     CONV_TAC (RAND_CONV (ONCE_REWRITE_CONV [enc_def])) >>
     asm_simp_tac bool_ss [LET_THM, LENGTH_REPLICATE]) >>
  asm_simp_tac bool_ss [static_length_def, static_length_Tuple_SUM, map_replicate,
    SUM_REPLICATE]
QED

Theorem abi_static_prefix_bytes_bound:
  !bound. ~is_dynamic (Bytes bound) ==> abi_static_prefix (Bytes bound)
Proof
  Cases >> simp[is_dynamic_def, abi_static_prefix_fixed_bytes]
QED

Theorem abi_static_prefix_array_bound:
  !bound at. (~is_dynamic at ==> abi_static_prefix at) ==>
    ~is_dynamic (Array bound at) ==> abi_static_prefix (Array bound at)
Proof
  Cases >> simp[is_dynamic_def, abi_static_prefix_array]
QED

Theorem abi_static_prefix_tuple_members:
  (!at. MEM at ts ==> ~is_dynamic at ==> abi_static_prefix at) ==>
  ~is_dynamic (Tuple ts) ==> abi_static_prefix (Tuple ts)
Proof
  rpt strip_tac >> irule abi_static_prefix_tuple >>
  fs[is_dynamic_def, any_dynamic_EXISTS, EVERY_MEM, EXISTS_MEM] >> metis_tac[]
QED

Theorem abi_static_prefix_static_mutual:
  (!at. ~is_dynamic at ==> abi_static_prefix at) /\
  (!ts. EVERY (\at. ~is_dynamic at ==> abi_static_prefix at) ts)
Proof
  ho_match_mp_tac abi_type_induction >>
  simp[is_dynamic_def, abi_static_prefix_numbers, abi_static_prefix_bytes_bound,
    abi_static_prefix_array_bound, abi_static_prefix_tuple_members, EVERY_MEM]
QED

Theorem abi_static_prefix_static = CONJUNCT1 abi_static_prefix_static_mutual;

val () = List.app (fn (n,th) =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th) in
    if null (Thm.hyp th) andalso null axioms andalso
       List.all (fn s => s = "DISK_THM") oracles then
      print ("ABI_VALID_STATIC_AGGREGATE_KERNEL_CLOSED " ^ n ^ "\n")
    else raise Fail ("ABI valid static aggregate not kernel closed: " ^ n)
  end) (DB.thms "abiValidStaticAggregate");
