(* Shared term construction for the linked guarded decoder.  The Lib is also
   loaded by the defining theory, so look up the effect only on invocation. *)
structure bodyAbiDecodeGuardedEffectSyntaxLib =
struct
open HolKernel boolLib bossLib
open abiEncoderTheory compileEnvTheory venomStateTheory venomExecSemanticsTheory
     fragExecTheory fragGasPathTheory exprSimAbiGasBridgeTheory
     bodyFullAbiDecodeLoopObservedSyntaxLib
     bodyFullAbiDecodeRuntimeLoopLengthObservedLib
     bodyFullAbiDecodeCutArraySyntaxLib bodyFullAbiDecodeCutPathLib
open bodyFullAbiDecodeArrayBulkRobustTheory

fun effect_const () = prim_mk_const
  {Thy = "bodyAbiDecodeGuardedEffectBaseMods", Name = "abi_decode_guarded_effect"};
fun effect s tn t tf = list_mk_comb (effect_const (), [s,tn,t,tf]);
val beta_conv = QCONV (REDEPTH_CONV BETA_CONV);
val normalize_guarded_effect = QCONV (beta_conv THENC REWRITE_CONV [GSYM CONJ_ASSOC]);
fun beta tm = rhs (concl (beta_conv tm));
fun normalized tm = rhs (concl (normalize_guarded_effect tm));
fun param vs name = valOf (List.find (fn v => fst (dest_var v) = name) vs);
fun triple what [x,y,z] = (x,y,z)
  | triple what _ = raise Fail ("guarded effect: expected " ^ what ^ " triple");

(* Mechanically compare a strengthened term with the old one, deleting only
   full effect conjuncts.  No rewrites of the entry, abort, or witness scopes. *)
fun erase_effect tm =
  let
    val e = effect_const ()
    fun is_effect x = same_const e (fst (strip_comb x))
    fun erase x =
      if is_conj x then
        let val (p,q) = dest_conj x in
          if is_effect q then erase p
          else mk_conj (erase p,erase q)
        end
      else if is_comb x then let val (f,a) = dest_comb x in mk_comb (erase f,erase a) end
      else if is_abs x then let val (v,b) = dest_abs x in mk_abs (v,erase b) end
      else x
  in erase tm end;

fun checked name old new =
  if aconv (normalized old) (normalized (erase_effect (beta new))) then new
  else raise Fail ("guarded effect changed " ^ name);

(* Strengthen only the normal disjunct, at its already bound state and taint.
   In particular, never choose another physical run under the H quantifier. *)
fun decorate_result s tn is_success result =
  let
    val (normal, abort) = dest_disj result
    val (vs, core) = strip_exists normal
    val (t,tf) = is_success vs core
    val normal' = list_mk_exists (vs, mk_conj (core, effect s tn t tf))
  in mk_disj (normal', abort) end;

fun decorate_observed_post s tn post =
  let
    val (vs, core) = strip_exists (beta post)
    val (r,_,tf) = triple "observed witnesses" vs
    val fields = strip_conj core
    val result = List.last fields
    val _ = case strip_exists (snd (dest_disj result)) of
      ([a], abort) => if aconv abort ``^r = Abort Revert_abort ^a`` then ()
                     else raise Fail "guarded effect: unexpected abort branch"
    | _ => raise Fail "guarded effect: unexpected abort binders"
    fun success [t] body =
          if aconv (hd (strip_conj body)) ``^r = OK ^t`` then (t,tf)
          else raise Fail "guarded effect: unexpected normal branch"
      | success _ _ = raise Fail "guarded effect: unexpected normal binders"
    val core' = list_mk_conj (List.take (fields, length fields - 1) @
      [decorate_result s tn success result])
  in checked "observed packet" post (list_mk_exists (vs, core')) end;

fun decorate_motive old =
  let
    val (args, body) = strip_abs old
    val (params, imp) = strip_forall body
    val (entry, post) = dest_imp imp
    val post' = decorate_observed_post (param params "s") (param params "tn") post
  in checked "motive" old (list_mk_abs (args, list_mk_forall (params, mk_imp (entry,post')))) end;

fun effect_ind motives = ISPECL motives abiEncoderTheory.compile_abi_decode_to_buf_ind;
fun ind_schema ind = dest_imp (concl (BETA_RULE ind));
fun effect_clauses ind = strip_conj (fst (ind_schema ind));
fun effect_mutual ind = snd (ind_schema ind);
fun guarded_effect_compiler_cases ind =
  case effect_clauses ind of [word,bytes,array,complex,nil_case,cons,loop] =>
    {word=word, bytes=bytes, array=array, complex=complex,
     nil_case=nil_case, cons=cons, loop=loop}
  | _ => raise Fail "guarded effect: unexpected compiler clauses";
val old_typed = [guarded_plus_typed, bounded_complex_plus_typed, repaired_loop_plus_typed];
val old_typed_length = [guarded_plus_typed, bounded_complex_plus_typed,
  repaired_loop_length_plus_typed];
val old_untyped = [guarded_plus, bounded_complex_plus, repaired_loop_plus];
fun guarded_effect_motive () = decorate_motive guarded_plus;
fun guarded_effect_motive_typed () = decorate_motive guarded_plus_typed;
fun guarded_effect_ind () = effect_ind (map decorate_motive old_untyped);
fun guarded_effect_ind_typed () = effect_ind (map decorate_motive old_typed);
fun guarded_effect_length_ind_typed () = effect_ind (map decorate_motive old_typed_length);

(* Fixed-observer inputs of bodyFullAbiDecodeGuardedCut; decoration does
   not change these or the separate observer certificate for the same r. *)
val cut_fn = ``frag_relabel_observer cut_start cut_finish L ids fn id``;
val cut_pos = ``frag_observer_cut cut_finish``;
val outer_layout = ``
  cs_extends cut_start cut_ready /\
  cut_start.cs_blocks <> cut_finish.cs_blocks /\
  LENGTH ids = LENGTH cut_start.cs_current_insts /\
  fn_has_code cut_start cut_finish fn /\
  fn_has_code (start_relabel L ids cut_start) (start_swap cut_start L ids cut_finish) ^cut_fn /\
  frag_ops_free cut_start cut_finish /\ L <> cut_finish.cs_current_bb /\
  ~MEM L (MAP (\bb. bb.bb_label) (emitted_blocks cut_start cut_finish)) /\
  EVERY (\i. ~MEM (Label L) i.inst_operands) (frag_code cut_start cut_finish)``;
val span = ``\a b. cs_extends cut_ready a /\ cs_extends a b /\ cs_extends b cut_finish``;
val crosses = ``\a b. a.cs_blocks = cut_start.cs_blocks /\ b.cs_blocks <> cut_start.cs_blocks``;
val related = ``\a s u. ~u.vs_halted /\
  (u.vs_current_bb,u.vs_inst_idx) = (^shadow_cursor) L cut_start a /\
  frag_relabel_state L cut_start.cs_current_bb u s``;
val replay = ``\u b r. (^shadow_result) ctx ^cut_fn ^cut_pos L cut_start.cs_current_bb u
  ((^shadow_cursor) L cut_start b) r``;

fun crossing_motive old =
  let
    val (args, body) = strip_abs (beta old)
    val (params, imp) = strip_forall body
    val (entry, post) = dest_imp imp
    val a = param params "start" and b = param params "finish" and s = param params "s"
    val u = variant (params @ free_vars body) ``shadow_in:venom_state``
  in
    list_mk_abs (args, list_mk_forall (params @ [u],
      mk_imp (``^entry /\ (^span) ^a ^b /\ (^crosses) ^a ^b /\ (^related) ^a ^s ^u``,
        extend_post post ``\r. (^replay) ^u ^b r``)))
  end;
fun fix_guarded_observer tm =
  let val vs = free_vars tm
  in subst [param vs "cut_observer" |-> cut_fn, param vs "cut" |-> cut_pos] tm end;
fun crossing_motives [guarded, members, loop] =
      [crossing_motive guarded, crossing_motive members,
       fix_guarded_observer (specialize_array_cut (decorate_array_motive loop))]
  | crossing_motives _ = raise Fail "guarded effect: expected three compiler motives";
fun guarded_effect_cut_ind () = effect_ind (crossing_motives (map decorate_motive old_typed_length));
fun guarded_effect_cut_ind_untyped () = effect_ind (crossing_motives (map decorate_motive old_untyped));

(* Array preparation uses its parameterized observer, with the same effect in
   the length-loop IH and in the parent's successful endpoint packet. *)
fun effect_array_clause motives =
  case motives of [guarded, members, loop] =>
    List.nth (effect_clauses (effect_ind
      [decorate_array_motive guarded, members, decorate_array_motive loop]), 2)
  | _ => raise Fail "guarded effect: expected three compiler motives";
fun guarded_effect_array_clause () = effect_array_clause (map decorate_motive old_typed_length);
fun guarded_effect_array_cut_clause () = specialize_array_cut (guarded_effect_array_clause ());

fun guarded_effect_body_for guarded completed =
  let
    val old = mk_body_observed_statement guarded completed
    val (entry, result) = dest_imp old
    val vs = free_vars old
    val (s,tn) = (param vs "s", param vs "tn")
    fun success [t,Gf,tf] _ = (t,tf)
      | success _ _ = raise Fail "guarded effect: unexpected body witnesses"
    (* In this API the revert branch comes first. *)
    val (abort, normal) = dest_disj (beta result)
    val (normal', _) = dest_disj (decorate_result s tn success (mk_disj (normal,abort)))
  in mk_imp (entry, checked "body result" result (mk_disj (abort,normal'))) end;

fun guarded_effect_body () =
  close_statement (guarded_effect_body_for (guarded_effect_motive ()) completed_robust);
fun guarded_effect_body_typed () =
  close_statement (guarded_effect_body_for (guarded_effect_motive_typed ()) completed_robust_typed);
fun guarded_effect_length_body_typed () = close_statement
  (guarded_effect_body_for (guarded_effect_motive_typed ())
    ``\j0 k s tn. (^completed_robust_typed) j0 k s tn /\
      mem_word_at d s.vs_memory = (w:256 word)``);
fun guarded_effect_length_loop_clause () = List.last (effect_clauses (guarded_effect_length_ind_typed ()));
fun guarded_effect_length_split_entry () = split_entry_clause (guarded_effect_length_loop_clause ());

(* A standalone all-success packet, e.g. the bulk suffix, uses a triple
   (state, provenance, taint) rather than the outcome/ghost disjunction. *)
fun guarded_effect_success_clause s tn old =
  let
    val (vs, imp) = strip_forall (beta old)
    val (entry, post) = dest_imp imp
    val (ws, body) = strip_exists post
    val (t,_,tf) = triple "successful suffix witnesses" ws
  in checked "successful suffix" old
    (list_mk_forall (vs, mk_imp (entry, list_mk_exists (ws, mk_conj (body,effect s tn t tf))))) end;

val old_bulk_clause = concl abi_decode_array_bulk_robust_conditional;
fun guarded_effect_bulk_clause () =
  let val vs = free_vars old_bulk_clause
  in guarded_effect_success_clause (param vs "s") (param vs "tn") old_bulk_clause end;

fun check_guarded_effect_syntax () =
  let
    fun check_ind old new =
      (ignore (guarded_effect_compiler_cases new);
       ignore (checked "compiler induction" (concl (effect_ind old)) (concl new)))
    fun check name old new = ignore (checked name old new)
  in
    check_ind old_untyped (guarded_effect_ind ());
    check_ind old_typed (guarded_effect_ind_typed ());
    check_ind old_typed_length (guarded_effect_length_ind_typed ());
    check_ind (crossing_motives old_untyped) (guarded_effect_cut_ind_untyped ());
    check_ind (crossing_motives old_typed_length) (guarded_effect_cut_ind ());
    check "body" closed_body_observed_statement (guarded_effect_body ());
    check "typed body" closed_body_observed_statement_typed (guarded_effect_body_typed ());
    check "length body" closed_body_length_observed_statement (guarded_effect_length_body_typed ());
    check "split-entry loop" observed_loop_length_split_entry_clause_typed (guarded_effect_length_split_entry ());
    check "array" array_decorated_clause (guarded_effect_array_clause ());
    check "selected array" array_cut_clause (guarded_effect_array_cut_clause ());
    ignore (guarded_effect_bulk_clause ())
  end;
end
