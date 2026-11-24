(* The singleton instance of the linked exemption certificate. *)
Theory gasExemptCert
Ancestors
  gasExemptCertMods gasExemptOrigin sourceExemptMods
  gasSummary fragGasFocus e2eDefs vyperAST vyperInterpreter vyperState

Definition gas_exempt_cert_singleton_def:
  gas_exempt_cert memory tops p source start marks out endpoint <=>
    gas_exempt_cert_mods memory [(NONE,tops)] p source start marks out endpoint
End

(* Preserve the singleton introduction rules at their original arities. *)
fun singleton_cert th =
  let
    val (vars, _) = strip_forall (concl th)
    val tops = ``tops : toplevel list``
    val modules = ``[(NONE:num option,^tops)]``
    val mods = valOf (List.find (fn v => type_of v = type_of modules) vars)
  in
    th |> SPECL vars |> INST [mods |-> modules]
       |> REWRITE_RULE [GSYM gas_exempt_cert_singleton_def,
                        GSYM gas_exempt_origin_singleton_def]
       |> GENL (map (fn v => if aconv v mods then tops else v) vars)
  end

val gas_exempt_cert_rules = save_thm
  ("gas_exempt_cert_rules", LIST_CONJ (map singleton_cert (CONJUNCTS gas_exempt_cert_mods_rules)))

val gas_exempt_cert_cases = save_thm
  ("gas_exempt_cert_cases", singleton_cert gas_exempt_cert_mods_cases)

(* Lift the induction motive by restricting it to singleton module lists.
   Its closure rules then reduce to the closure rules for tops. *)
local
  val (_, body) = dest_forall (concl gas_exempt_cert_mods_ind)
  val (arguments, _) = strip_forall (snd (dest_imp body))
  val modules = List.nth (arguments, 1)
  val tops = ``tops : toplevel list``
  val singleton = ``[(NONE:num option,^tops)]``
  val singleton_arguments = hd arguments :: tops :: List.drop (arguments, 2)
  val property = mk_var ("gas_exempt_cert'",
    List.foldr (op -->) bool (map type_of singleton_arguments))
  val property_body = list_mk_comb (property, singleton_arguments)
  val direct = list_mk_abs (arguments, subst
    [tops |-> ``SND (HD ^modules)``] property_body)
  val restricted = list_mk_abs (arguments, mk_forall (tops,
    mk_imp (mk_eq (modules, singleton), property_body)))
  fun motive_instance predicate =
    CONV_RULE (DEPTH_CONV BETA_CONV) (SPEC predicate gas_exempt_cert_mods_ind)
  val clauses = motive_instance direct |> concl |> dest_imp |> fst |> strip_conj
  (* The closure rule is assumed after specialization, not before it. *)
  fun specialize_clause clause =
    let
      val (vars, rest) = strip_forall clause
      val mod_var = valOf (List.find (fn v => type_of v = type_of singleton) vars)
    in
      list_mk_forall (map (fn v => if aconv v mod_var then tops else v) vars,
        subst [mod_var |-> singleton] rest)
      |> rhs o concl o REWRITE_CONV
        [listTheory.HD, pairTheory.SND, GSYM gas_exempt_origin_singleton_def]
    end
  val legacy_clauses = list_mk_conj (map specialize_clause clauses)
  val lifted_ind = motive_instance restricted
  val lifted_clauses = strip_conj (fst (dest_imp (concl lifted_ind)))
  fun prove_lifted (legacy, linked) = prove (linked,
    assume_tac legacy >> rpt strip_tac >>
    gvs[GSYM gas_exempt_origin_singleton_def] >> metis_tac[])
  val lifted_closed = LIST_CONJ
    (ListPair.map prove_lifted (CONJUNCTS (ASSUME legacy_clauses), lifted_clauses))
  val singleton_induction = MATCH_MP lifted_ind lifted_closed
    |> singleton_cert
    |> SIMP_RULE bool_ss [listTheory.CONS_11, pairTheory.PAIR_EQ]
in
  val gas_exempt_cert_ind = save_thm ("gas_exempt_cert_ind",
    GEN property (DISCH legacy_clauses singleton_induction))
end

val gas_exempt_cert_strongind = save_thm ("gas_exempt_cert_strongind",
  IndDefLib.derive_strong_induction (gas_exempt_cert_rules, gas_exempt_cert_ind))
val () = IndDefLib.export_rule_induction "gas_exempt_cert_strongind"

val gas_exempt_cert_origin = save_thm ("gas_exempt_cert_origin", singleton_cert gas_exempt_cert_mods_origin)
val gas_exempt_cert_bind_unit = save_thm ("gas_exempt_cert_bind_unit", singleton_cert gas_exempt_cert_mods_bind_unit)
val gas_exempt_cert_error_unit = save_thm ("gas_exempt_cert_error_unit", singleton_cert gas_exempt_cert_mods_error_unit)
val gas_exempt_cert_bind_bool = save_thm ("gas_exempt_cert_bind_bool", singleton_cert gas_exempt_cert_mods_bind_bool)
val gas_exempt_cert_error_bool = save_thm ("gas_exempt_cert_error_bool", singleton_cert gas_exempt_cert_mods_error_bool)
val gas_exempt_cert_bind_result = save_thm ("gas_exempt_cert_bind_result", singleton_cert gas_exempt_cert_mods_bind_result)
val gas_exempt_cert_error_result = save_thm ("gas_exempt_cert_error_result", singleton_cert gas_exempt_cert_mods_error_result)
val gas_exempt_cert_bind_value = save_thm ("gas_exempt_cert_bind_value", singleton_cert gas_exempt_cert_mods_bind_value)
val gas_exempt_cert_error_value = save_thm ("gas_exempt_cert_error_value", singleton_cert gas_exempt_cert_mods_error_value)
val gas_exempt_cert_bind_place = save_thm ("gas_exempt_cert_bind_place", singleton_cert gas_exempt_cert_mods_bind_place)
val gas_exempt_cert_error_place = save_thm ("gas_exempt_cert_error_place", singleton_cert gas_exempt_cert_mods_error_place)
val gas_exempt_cert_bind_values = save_thm ("gas_exempt_cert_bind_values", singleton_cert gas_exempt_cert_mods_bind_values)
val gas_exempt_cert_error_values = save_thm ("gas_exempt_cert_error_values", singleton_cert gas_exempt_cert_mods_error_values)
val gas_exempt_cert_bind_results = save_thm ("gas_exempt_cert_bind_results", singleton_cert gas_exempt_cert_mods_bind_results)
val gas_exempt_cert_error_results = save_thm ("gas_exempt_cert_error_results", singleton_cert gas_exempt_cert_mods_error_results)
val gas_exempt_cert_cleanup = save_thm ("gas_exempt_cert_cleanup", singleton_cert gas_exempt_cert_mods_cleanup)
val gas_exempt_cert_handler = save_thm ("gas_exempt_cert_handler", singleton_cert gas_exempt_cert_mods_handler)
val gas_exempt_cert_get_scopes = save_thm ("gas_exempt_cert_get_scopes", singleton_cert gas_exempt_cert_mods_get_scopes)
val gas_exempt_cert_invoke = save_thm ("gas_exempt_cert_invoke", singleton_cert gas_exempt_cert_mods_invoke)
val gas_exempt_cert_unforce_result = save_thm ("gas_exempt_cert_unforce_result", singleton_cert gas_exempt_cert_mods_unforce_result)
val gas_exempt_cert_source_cong = save_thm ("gas_exempt_cert_source_cong", singleton_cert gas_exempt_cert_mods_source_cong)

Theorem gas_exempt_cert_forget_memory:
  !checked tops p source start marks out endpoint.
    gas_exempt_cert checked tops p source start marks out endpoint ==>
    !memory. (memory ==> checked) ==>
      gas_exempt_cert memory tops p source start marks out endpoint
Proof
  metis_tac[gas_exempt_cert_forget_memory_mods, gas_exempt_cert_singleton_def]
QED

Theorem gas_exempt_cert_execution:
  !memory tops ctx func source es s0 marks err ee leaf finish.
    gas_exempt_cert memory tops (ctx, func) source (es, s0)
      marks (err, ee) (leaf, finish) ==>
    (!tail. source
       (es with gas_obs := gas_explicit marks s0.vs_gas_readings ++ tail) =
       (INR (Error err), ee with gas_obs := tail)) /\
    gas_focus_path memory (ctx, func) s0 (LENGTH marks) (leaf, finish) /\
    unspecified_behaviour_exempt tops err
Proof
  metis_tac[gas_exempt_cert_execution_mods, gas_exempt_cert_singleton_def,
            unspecified_behaviour_exempt_mods_singleton]
QED

Theorem gas_exempt_cert_function_cleanup:
  !memory tops ctx func a es s0 marks err ee leaf finish saved k.
  gas_exempt_cert memory tops (ctx,func)
    (ignore_bind (a : evaluation_state -> unit evaluation_result) (return ()))
    (es,s0) marks (err,ee) (leaf,finish) ==>
  gas_exempt_cert memory tops (ctx,func)
    (bind (finally (try (ignore_bind a (return NoneV)) handle_function)
       (set_scopes saved)) k)
    (es,s0) marks (err,ee with scopes := saved) (leaf,finish)
Proof
  metis_tac[gas_exempt_cert_function_cleanup_mods, gas_exempt_cert_singleton_def]
QED

Theorem gas_exempt_cert_start_gas_obs:
  !memory tops env source start marks out endpoint.
    gas_exempt_cert memory tops env source start marks out endpoint ==>
    !gs. gas_exempt_cert memory tops env source
      (FST start with gas_obs := gs, SND start) marks out endpoint
Proof
  metis_tac[gas_exempt_cert_start_gas_obs_mods, gas_exempt_cert_singleton_def]
QED

Theorem read_result_no_exempt_error:
  !tops cx r st err st'.
    read_result cx r st = (INR (Error err), st') ==>
    ~unspecified_behaviour_exempt tops err
Proof
  metis_tac[read_result_no_exempt_error_mods, gas_exempt_cert_singleton_def,
            unspecified_behaviour_exempt_mods_singleton]
QED

Theorem gas_source_unforce_result:
  !tops cx e st err ee.
    unspecified_behaviour_exempt tops err /\
    ignore_bind (bind (eval_expr cx e) (read_result cx)) (return ()) st =
      (INR (Error err), ee) ==>
    ignore_bind (eval_expr cx e) (return ()) st =
      (INR (Error err), ee)
Proof
  metis_tac[gas_source_unforce_result_mods, gas_exempt_cert_singleton_def,
            unspecified_behaviour_exempt_mods_singleton]
QED
