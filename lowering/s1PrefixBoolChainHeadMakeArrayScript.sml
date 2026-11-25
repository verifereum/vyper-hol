(* The MakeArray head inherits prefix facts from its strictly smaller elements. *)
Theory s1PrefixBoolChainHeadMakeArray
Ancestors
  s1PrefixPreds s1PrefixMakeArray s1PrefixCheckedContextFull
  bodyFullPreds vyperAST list

Theorem prefix_list_from_members:
  !cx ys. (!a. MEM a ys ==> body_expr_prefix_ok cx a) ==>
    body_exprs_prefix_ok cx ys
Proof
  rpt gen_tac >> strip_tac >>
  Induct_on `ys` >- simp[body_exprs_prefix_ok_def] >>
  rpt gen_tac >> strip_tac >>
  simp[body_exprs_prefix_ok_def]
QED

Theorem expr_size_lt_make_array_member:
  !ann t n xs a. MEM a xs ==>
    expr_size a < expr_size (Builtin ann (MakeArray t n) xs)
Proof
  rpt gen_tac >> strip_tac >>
  Induct_on `xs` >- simp[] >>
  rpt gen_tac >> strip_tac >> gvs[expr_size_def] >>
  Cases_on `a = h` >> gvs[] >> first_x_assum irule >> metis_tac[]
QED

Theorem bool_chain_head_make_array_prefix_ok:
  !cx ann t n xs.
    (!a. expr_size a < expr_size (Builtin ann (MakeArray t n) xs) ==>
       body_expr_prefix_ok cx a) ==>
    body_expr_prefix_ok cx (Builtin ann (MakeArray t n) xs)
Proof
  rpt gen_tac >> strip_tac >>
  simp[Once body_expr_prefix_ok_def] >> conj_tac
  >- (rpt gen_tac >> strip_tac >>
      `body_exprs_full_ok cx xs` by
        (drule checked_context_full_exprs >> metis_tac[]) >>
      `body_exprs_prefix_ok cx xs` by
        ((irule prefix_list_from_members >>
         rpt gen_tac >> strip_tac >>
         `expr_size a < expr_size (Builtin ann (MakeArray t n) xs)` by
           metis_tac[expr_size_lt_make_array_member] >>
         first_x_assum irule >> (fn g => if length (fst g) = 7 andalso String.translate (fn c => if Char.isSpace c then "" else String.str c) (PP.pp_to_string 100 Parse.pp_term (snd g)) = "expr_sizea<expr_size(Builtinann(MakeArraytn)xs)" then (simp[prefix_list_from_members, expr_size_lt_make_array_member]) g else (ALL_TAC) g))) >>
      irule make_array_builtin_sim_prefix >> metis_tac[]) >>
  rpt gen_tac >> strip_tac >>
  irule prefix_list_from_members >>
  rpt gen_tac >> strip_tac >>
  `expr_size a < expr_size (Builtin ann (MakeArray t n) xs)` by
    metis_tac[expr_size_lt_make_array_member] >>
  qpat_assum `!a. expr_size a < expr_size (Builtin ann (MakeArray t n) xs) ==> body_expr_prefix_ok cx a` irule >>
  qpat_assum `expr_size a < expr_size (Builtin ann (MakeArray t n) xs)` ACCEPT_TAC
QED
