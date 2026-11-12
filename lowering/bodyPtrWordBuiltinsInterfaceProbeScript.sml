Theory bodyPtrWordBuiltinsInterfaceProbe
Ancestors bodyPtrWordBuiltinsModularCompose bodyPtrPreds vyperAST

val _ = (show_types := true; show_assums := true);
fun inspect (name,th) =
  (print ("\nINTERFACE " ^ name ^ "\n"); print (thm_to_string th ^ "\n");
   print ("HYPS " ^ Int.toString (length (hyp th)) ^ "\n");
   app (fn t => print (term_to_string t ^ "\n")) (hyp th);
   app (fn t => print ("FREE " ^ term_to_string t ^ " : " ^ type_to_string (type_of t) ^ "\n"))
     (free_vars (concl th));
   app (fn t => print ("TYVAR " ^ type_to_string t ^ "\n")) (type_vars_in_term (concl th)));
val _ = inspect ("pow",body_word_pow_ptr_ok);
val _ = inspect ("mod",body_word_modular_ptr_ok);
val _ = inspect ("mod-spec",SPEC_ALL body_word_modular_ptr_ok);
val _ = inspect ("mod-inst",Q.INST [`is_mul` |-> `T`] body_word_modular_ptr_ok);
val _ = inspect ("mod-simp",SIMP_RULE (srw_ss()) [] (Q.INST [`is_mul` |-> `T`] body_word_modular_ptr_ok));
val _ = inspect ("mod-gen",GEN_ALL (SIMP_RULE (srw_ss()) [] (Q.INST [`is_mul` |-> `T`] body_word_modular_ptr_ok)));

Theorem word_pow_interface_probe:
  !cx ty a b. body_exprs_ptr_ok cx [a;b] ==>
    body_expr_ptr_ok cx (Builtin ty PowMod256 [a;b])
Proof
  rpt strip_tac >> irule body_word_pow_ptr_ok >> simp[]
QED

val _ = let
  val producer = body_word_modular_ptr_ok |> Q.INST [`is_mul` |-> `T`] |> SIMP_RULE (srw_ss()) []
  val target = ``body_expr_ptr_ok cx (Builtin ty MulMod [head;h;hh])``
  val pc = snd (dest_imp (concl producer))
  fun constants label tm = app (fn c => let val {Thy,Name,Ty} = dest_thy_const c in
    print (label ^ " CONST " ^ Thy ^ "$" ^ Name ^ " : " ^ type_to_string Ty ^ "\n") end)
    (find_terms is_const tm)
  val _ = constants "producer" pc
  val _ = constants "target" target
  val (ts,tys) = match_term pc target
in print ("MATCH OK terms=" ^ Int.toString (length ts) ^ " types=" ^ Int.toString (length tys) ^ "\n") end;

Theorem word_mul_interface_probe:
  !cx ty a b m. body_exprs_ptr_ok cx [a;b;m] ==>
    body_expr_ptr_ok cx (Builtin ty MulMod [a;b;m])
Proof
  rpt strip_tac >>
  irule (body_word_modular_ptr_ok |> Q.INST [`is_mul` |-> `T`] |> SIMP_RULE (srw_ss()) []) >> simp[]
QED
