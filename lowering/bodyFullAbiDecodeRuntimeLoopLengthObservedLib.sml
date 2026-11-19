(* Word-frame specializations of the observed loop: HOL quotations only. *)
structure bodyFullAbiDecodeRuntimeLoopLengthObservedLib =
struct
open HolKernel boolLib bossLib
open bodyFullAbiDecodeLoopObservedSyntaxLib
     bodyFullAbiDecodeRuntimeLoopSyntaxLib
open venomStateTheory wordsTheory

fun body_with keep_word = mk_body_observed_statement guarded_plus_typed
  ``\j0 k s tn. (^completed_robust_typed) j0 k s tn /\
    (^keep_word ==> mem_word_at d s.vs_memory = (w:256 word))``;

val closed_body_length_observed_statement =
  close_statement (mk_body_observed_statement guarded_plus_typed
    ``\j0 k s tn. (^completed_robust_typed) j0 k s tn /\
      mem_word_at d s.vs_memory = (w:256 word)``);

(* Preserve the exact old entry and reuse its original d and s binders. *)
fun loop_with word_frame =
  let
    val (args, clause) = strip_abs repaired_loop_plus_typed
    val (params, implication) = strip_forall clause
    val (entry, post) = dest_imp implication
    val (head, robust :: rest) = strip_comb post
    fun param name = List.find (fn v => fst (dest_var v) = name) params |> valOf
    val dest = param "d"
    val initial = param "s"
    val word_eq = ``mem_word_at ^dest (t:venom_state).vs_memory =
                     mem_word_at ^dest (^initial).vs_memory``
    val extra = word_frame word_eq
    val robust_framed = ``\t tn'. ^robust t tn' /\ ^extra``
  in
    list_mk_abs (args, list_mk_forall (params,
      mk_imp (entry, list_mk_comb (head, robust_framed :: rest))))
  end;

val repaired_loop_length_plus_typed = loop_with I;
fun loop_clause_with loop = generated_loop_clause
  [guarded_plus_typed, bounded_complex_plus_typed, loop];
val observed_loop_length_clause_typed = loop_clause_with repaired_loop_length_plus_typed;

val runtime_loop_word_frame_statement =
  let
    val flag = ``keep_word:bool``
    val body_params = fst (strip_forall closed_body_length_observed_statement)
    val body = list_mk_forall (body_params, body_with flag)
    val loop = loop_clause_with (loop_with (fn eq => mk_imp (flag, eq)))
  in
    mk_forall (flag, mk_imp (body, loop))
  end;

(* Expose the actual first closed block and keep the header observation
   with the result witnesses of the original invocation. *)
fun split_entry_clause clause =
  let
    val normalized = rhs (concl (REDEPTH_CONV BETA_CONV clause))
    val (ops, step) = strip_forall normalized
    val (ih, invoke) = dest_imp step
    val (params, implication) = strip_forall invoke
    val (entry, post) = dest_imp implication
    fun param name = valOf (List.find (fn v => fst (dest_var v) = name) params)
    val start = param "start"
    val finish = param "finish"
    val initial = param "s"
    val ([r,Gf,tnf], body) = strip_exists post
    val [physical, observer, result] = strip_conj body
    val hdr = ``header_start:compileEnv$compile_state``
    val tail = ``!obs. fragExec$fn_has_code ^hdr ^finish obs ==>
      fragGasPath$gas_path ctx obs (jump_to (^hdr).cs_current_bb ^initial) 0 ^r``
    val witnesses = list_mk_exists ([r,Gf,tnf], list_mk_conj [physical,observer,tail,result])
    val extended = ``?^hdr.
      compileEnv$cs_extends ^start ^hdr /\ compileEnv$cs_extends ^hdr ^finish /\
      (^hdr).cs_current_insts = [] /\
      (^hdr).cs_current_bb = FST (compileEnv$fresh_label "dec_dyn_hdr" ^start) /\
      (^hdr).cs_blocks = <|bb_label := (^start).cs_current_bb;
        bb_instructions := (^start).cs_current_insts ++
          [venomInst$mk_inst (^start).cs_next_id JMP [Label (^hdr).cs_current_bb] []]|> :: (^start).cs_blocks /\
      ^witnesses``
  in
    list_mk_forall (ops, mk_imp (ih, list_mk_forall (params, mk_imp (entry, extended))))
  end;

val observed_loop_length_split_entry_clause_typed =
  split_entry_clause observed_loop_length_clause_typed;

val runtime_loop_word_frame_split_entry_statement =
  let
    val (flags, conditional) = strip_forall runtime_loop_word_frame_statement
    val (body, clause) = dest_imp conditional
  in
    list_mk_forall (flags, mk_imp (body, split_entry_clause clause))
  end;

val _ =
  let
    val ih = mk_observed_loop_ih observed_loop_length_clause_typed
      repaired_loop_length_plus_typed
    val beta = REDEPTH_CONV BETA_CONV
    val normalize = rhs o concl o (beta THENC simpLib.SIMP_CONV bool_ss [])
    val inst = rhs o concl o beta o curry mk_comb (rand runtime_loop_word_frame_statement)
    val old = mk_imp (closed_body_observed_statement_typed, observed_loop_clause_typed)
    val len = mk_imp (closed_body_length_observed_statement, observed_loop_length_clause_typed)
  in
    if aconv (normalize ih) (normalize observed_loop_ih_typed) andalso
       aconv (normalize (inst F)) (normalize old) andalso
       aconv (normalize (inst T)) (normalize len)
    then () else raise Fail "unexpected word-frame specialization or child IH"
  end;
end
