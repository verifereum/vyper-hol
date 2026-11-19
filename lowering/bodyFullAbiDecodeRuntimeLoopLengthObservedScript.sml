(* Same-execution length frame for the observed dynamic array loop. *)
Theory bodyFullAbiDecodeRuntimeLoopLengthObserved
Ancestors bodyFullAbiDecodeRuntimeLoopObserved
Libs bodyFullAbiDecodeRuntimeLoopLengthObservedLib

(* Check the nonbulk IH in the generated DecDynArray clause.  Its
   compiler operands are bound by the clause, and d and s by the invocation. *)
val _ =
  let
    val ind = abiEncoderTheory.compile_abi_decode_to_buf_ind
    val motives = [bodyFullAbiDecodeLoopObservedSyntaxLib.guarded_plus_typed,
      bodyFullAbiDecodeLoopObservedSyntaxLib.bounded_complex_plus_typed,
      repaired_loop_length_plus_typed]
    fun clauses xs = strip_conj (fst (dest_imp (concl (ISPECL xs ind))))
    val (outer, schema) = strip_forall (List.nth (clauses (fst (strip_forall (concl ind))), 2))
    val [dst, src, opc, base, hi, elem, asz, msz, dyn, max_count] = outer
    val (inner, _) = strip_forall (fst (dest_imp schema))
    val [bulk, ip, alloc, cnt] = inner
    val guard = ``(^bulk <=> ~^dyn /\ ~dec_info_needs_clamp ^elem) /\
      ~^bulk /\ ^ip = (^alloc).buf_operand``
    val invoke = list_mk_comb (repaired_loop_length_plus_typed,
      [dst,src,opc,base,hi,elem,asz,msz,ip,cnt])
    val beta = rhs o concl o REDEPTH_CONV BETA_CONV
    val expected = beta (list_mk_forall (outer @ inner, mk_imp (guard, invoke)))
    val actual = List.nth (clauses motives, 2)
    val (bound, array_step) = strip_forall (beta actual)
    val ih = list_mk_forall (bound, fst (dest_imp array_step))
    val (params, invocation) = strip_forall (snd (dest_imp (snd (strip_forall ih))))
    fun param name = valOf (List.find (fn v => fst (dest_var v) = name) params)
    val d = param "d"
    val s = param "s"
    val (_, post) = strip_exists (snd (dest_imp invocation))
    val (normal, _) = dest_disj (List.last (strip_conj post))
    val ([t], success) = strip_exists normal
  in
    if aconv (rand (snd (dest_imp schema))) ``DecDynArray ^elem ^asz ^msz ^dyn ^max_count`` andalso
       aconv ih expected andalso
       aconv (List.last (strip_conj success))
         ``mem_word_at ^d (^t).vs_memory = mem_word_at ^d (^s).vs_memory``
    then () else raise Fail "unexpected generated DecDynArray nonbulk length IH"
  end;

Theorem abi_decode_dyn_loop_length_from_body:
  (^closed_body_length_observed_statement) ==> (^observed_loop_length_clause_typed)
Proof
  let val norm = REDEPTH_CONV BETA_CONV THENC simpLib.SIMP_CONV bool_ss [] in
    CONV_TAC norm >>
    ACCEPT_TAC (CONV_RULE norm (Q.SPEC `T` abi_decode_dyn_loop_word_frame_from_body))
  end
QED
