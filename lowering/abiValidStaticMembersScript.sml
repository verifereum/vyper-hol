(* Static member-list decoding reconstructs the canonical readable head prefix. *)
Theory abiValidStaticMembers
Ancestors
  abiValidStaticScalar contractABI list rich_list arithmetic

Theorem abi_valid_static_members:
  !ts. EVERY (\at. ~is_dynamic at /\ abi_static_prefix at) ts ==>
  !base hds acc. valid_enc_tuple ts base hds ==>
  ?vs. dec_tuple ts base hds acc = ListV (REVERSE acc ++ vs) /\
    LENGTH vs = LENGTH ts /\ has_types ts vs /\
    FLAT (MAP2 enc ts vs) = TAKE (static_length (Tuple ts)) hds /\
    static_length (Tuple ts) <= LENGTH hds
Proof
  Induct
  >- simp[dec_def, valid_enc_def] >>
  qx_gen_tac `at` >> simp_tac bool_ss [EVERY_DEF] >> strip_tac >>
  MAP_EVERY qx_gen_tac [`input`, `hds`, `acc`] >> strip_tac >>
  qpat_x_assum `valid_enc_tuple _ _ _` mp_tac >>
  asm_simp_tac bool_ss [Once valid_enc_def, LET_THM] >> strip_tac >>
  `has_type at (dec at (TAKE (static_length at) hds))` by
    (irule (cj 1 dec_has_type) >> first_assum ACCEPT_TAC) >>
  `enc at (dec at (TAKE (static_length at) hds)) = TAKE (static_length at) hds` by
    (qpat_x_assum `abi_static_prefix at` mp_tac >>
     simp_tac bool_ss [abi_static_prefix_def] >>
     disch_then (qspec_then `TAKE (static_length at) hds` mp_tac) >>
     asm_simp_tac (srw_ss()) [LENGTH_TAKE_EQ, TAKE_TAKE, MIN_DEF]) >>
  qpat_x_assum `EVERY _ ts ==> _` drule >>
  disch_then (qspecl_then [`input`, `DROP (static_length at) hds`,
    `dec at (TAKE (static_length at) hds)::acc`] mp_tac) >>
  impl_tac >- first_assum ACCEPT_TAC >> strip_tac >>
  qexists_tac `dec at (TAKE (static_length at) hds)::vs` >>
  asm_simp_tac (srw_ss()) [Once dec_def, has_type_def, TAKE_SUM, APPEND_ASSOC] >>
  fs[LENGTH_DROP] >> decide_tac
QED

val () = List.app (fn (n,th) =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th) in
    if null (Thm.hyp th) andalso null axioms andalso
       List.all (fn s => s = "DISK_THM") oracles then
      print ("ABI_VALID_STATIC_MEMBERS_KERNEL_CLOSED " ^ n ^ "\n")
    else raise Fail ("ABI valid static members not kernel closed: " ^ n)
  end) (DB.thms "abiValidStaticMembers");
