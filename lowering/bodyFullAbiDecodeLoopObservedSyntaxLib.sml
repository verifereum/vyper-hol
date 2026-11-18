(* Shared observed motives and the conditional Body interface. These are
   HOL terms only: neither consumer needs the Body proof to load them. *)
structure bodyFullAbiDecodeLoopObservedSyntaxLib =
struct
open HolKernel boolLib bossLib
open bodyFullAbiDecodeRuntimeLoopSyntaxLib
open bodyFullAbiDecodeInterfaceTheory abiDecoderLoopSetupTheory abiEncoderTheory
     compileEnvTheory venomInstTheory venomExecSemanticsTheory venomStateTheory
     loweringStateRelDefsTheory wordsTheory listTheory rich_listTheory
     finite_mapTheory arithmeticTheory valueEncodingPropsTheory ptrDisciplineTheory
     abiDecoderCoherenceTheory abiDecoderMemberInfosTheory abiDecoderExecutionTheory
     pred_setTheory fragGasPathTheory bodyPtrDefsTheory vyperTypingTheory

val contained = ``\protected.
  EVERY (\(a,bytes:word8 list). output_base <= a /\
    a + LENGTH bytes <= output_base + output_cap) protected``;

val input_origin = ``\s.
  (?aid ib isz. aid < output_id /\ FLOOKUP s.vs_allocas aid = SOME (ib,isz) /\
     ib <= w2n (input_word:256 word) /\
     w2n input_word + LENGTH (input_bytes:word8 list) <= ib + isz) \/
  (?name ib isz. local_region ce es.scopes s name ib isz /\
     ib <= w2n input_word /\ w2n input_word + LENGTH input_bytes <= ib + isz)``;

val taint_decreases = ``\tn tnf.
  !i. output_base <= i /\ i < output_base + output_cap /\
      i IN tnf.t_mem ==> i IN tn.t_mem``;

val robust_at = ``\tv a s tn.
  !v. val_wf tv v /\ val_in_memory tv v a s.vs_memory ==>
    !mem. mem_agree_outside tn.t_mem s.vs_memory mem ==>
      val_in_memory tv v a mem``;

(* The typed instance restricts just the values quantified in robustness. *)
val robust_at_typed = ``\tv a s tn.
  !v. value_has_type tv v /\ val_wf tv v /\ val_in_memory tv v a s.vs_memory ==>
    !mem. mem_agree_outside tn.t_mem s.vs_memory mem ==>
      val_in_memory tv v a mem``;

fun mk_completed_robust robust_at = ``\j0 k s tn.
  !i. j0 <= i /\ i < k ==> (^robust_at) tv (d+32+i*msz) s tn``;

val completed_robust = mk_completed_robust robust_at;
val completed_robust_typed = mk_completed_robust robust_at_typed;

(* Preserve all of owned_decoder_post, adding an observer of the same
   outcome and normal-return facts at that outcome's state and taint. *)
val observed_decoder_post = ``\robust live protected start finish s G tn.
  ?r G' tn'.
    (!H. V H ==> gas_origin_ptr_path
      (DF H,lo,explicit,ctx,fn,PG) (s,G,tn) [] (r,G',tn')) /\
    (!obs. fn_has_code start finish obs ==> gas_path ctx obs s 0 r) /\
    ((?t. r = OK t /\ ~t.vs_halted /\
       t.vs_current_bb = finish.cs_current_bb /\
       t.vs_inst_idx = LENGTH finish.cs_current_insts /\
       (^owned_decoder_state) live protected finish t G' tn' /\
       (^frame) start s G tn t G' tn' /\
       (^input_origin) t /\ (^taint_decreases) tn tn' /\ robust t tn') \/
     (?t. r = Abort Revert_abort t))``;

local
  (* Keep the argument order and entire old entry verbatim. The new term
     uses those same parameters, including the bound state and taint. *)
  fun enhance_motive old_motive robust =
    let
      val (args, clause) = strip_abs old_motive
      val (params, implication) = strip_forall clause
      val (entry, _) = dest_imp implication
      fun param name = List.find (fn v => fst (dest_var v) = name) params |> valOf
      val protected = param "protected"
      val s = param "s"
      val new_entry = ``^entry /\ (^contained) ^protected /\ (^input_origin) ^s``
      val post = list_mk_comb (observed_decoder_post,
        robust :: map param ["live","protected","start","finish","s","G","tn"])
    in
      list_mk_abs (args, list_mk_forall (params, mk_imp (new_entry, post)))
    end
in
  fun mk_observed_motives robust_at =
    let
      val guarded = enhance_motive guarded_to_buf_motive ``(^robust_at) tv d``
      val complex = enhance_motive bounded_complex_elems_motive ``\t tn'.
        !i. i < LENGTH tvs ==>
          (^robust_at) (EL i tvs) (d+vo+SUM (TAKE i (MAP type_memory_size tvs))) t tn'``
      val completed = mk_completed_robust robust_at
      val loop = enhance_motive repaired_loop_motive ``(^completed) j n``
    in
      (guarded, complex, loop)
    end;
end;

fun mk_observed_loop_clause (guarded, complex, loop) =
  generated_loop_clause [guarded, complex, loop];

fun mk_observed_loop_ih clause loop =
  let
    val (formals, implication) = strip_forall clause
    val (args, _) = strip_abs loop
  in
    subst (ListPair.mapEq (fn (v,a) => v |-> a) (formals,args))
      (fst (dest_imp implication))
  end;

val (guarded_plus, bounded_complex_plus, repaired_loop_plus) =
  mk_observed_motives robust_at;
val observed_loop_clause =
  mk_observed_loop_clause (guarded_plus, bounded_complex_plus, repaired_loop_plus);
val observed_loop_ih = mk_observed_loop_ih observed_loop_clause repaired_loop_plus;

val (guarded_plus_typed, bounded_complex_plus_typed, repaired_loop_plus_typed) =
  mk_observed_motives robust_at_typed;
val observed_loop_clause_typed = mk_observed_loop_clause
  (guarded_plus_typed, bounded_complex_plus_typed, repaired_loop_plus_typed);
val observed_loop_ih_typed =
  mk_observed_loop_ih observed_loop_clause_typed repaired_loop_plus_typed;

(* Projection of the child IH does not use any property of robustness. *)
val observed_recursive_call_schema =
  let
    val robustness = mk_var ("robustness", type_of robust_at)
    val motives as (guarded, _, loop) = mk_observed_motives robustness
    val ih = mk_observed_loop_ih (mk_observed_loop_clause motives) loop
  in
    mk_forall (robustness, ``^ih /\
      abi_decode_array_element_setup ip src dst opc base_op hi ei asz msz body_st =
        ((idx,child_src,child_dst),child) ==>
      (^guarded) child_dst child_src opc base_op hi ei``)
  end;

fun mk_body_observed_statement guarded_plus completed_robust =
  snd (strip_abs ``\(s:venom_state) (finish:compile_state).
  abi_decoder_coherent ce env sf ty tv /\
  ei = type_to_abi_dec_info sf ce ty /\
  asz = abi_embedded_static_size ce.ce_struct_fields ty /\
  msz = type_memory_size tv /\ n < dimword (:256) /\ hi <> Lit 0w /\
  w2n input_word+LENGTH input_bytes < dimword (:256) /\
  (?H. V H) /\ ~ctx_has_dalloca ctx /\ fn_inst_ids_distinct fn /\
  local_ptrs_reserved ce anchor /\
  (!x sz. ce.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at origin x) /\
  (!x sz. ce.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at origin x) /\
  abi_decoder_operand_live anchor.cs_next_var src /\
  abi_decoder_operand_live anchor.cs_next_var hi /\
  abi_decoder_operand_live anchor.cs_next_var (Var dst) /\
  abi_decoder_operand_live anchor.cs_next_var (Var counter) /\
  abi_decoder_operand_live anchor.cs_next_var (Var input) /\
  anchor.cs_next_var <= loop_body.cs_next_var /\ anchor.cs_next_id <= loop_body.cs_next_id /\
  abi_decode_array_element_setup (Var counter) src (Var dst) MLOAD
    (Var input) hi ei asz msz loop_body = ((idx,child_src,child_dst),child) /\
  compile_abi_decode_to_buf child_dst child_src MLOAD (Var input) hi ei child =
    ((),returned) /\
  fn_has_code loop_body child fn /\ fn_has_code child returned fn /\
  idx = Var iv /\ loop_body.cs_next_var <= child.cs_next_var /\
  child.cs_next_var <= returned.cs_next_var /\ ~not_fresh_at returned nv /\
  lookup_block returned.cs_current_bb fn.fn_blocks = SOME
    <|bb_label := returned.cs_current_bb; bb_instructions :=
      returned.cs_current_insts ++
        abi_decode_backedge_insts returned.cs_next_id iv nv (Var counter) hdr|> /\
  lookup_block hdr fn.fn_blocks = SOME hdr_bb /\
  phi_prefix_length hdr_bb.bb_instructions = 0 /\
  (^guarded_plus) child_dst child_src MLOAD (Var input) hi ei /\
  (^loop_resource) anchor k s G tn /\ k<n /\ ~s.vs_halted /\
  s.vs_current_bb = loop_body.cs_current_bb /\
  s.vs_inst_idx = LENGTH loop_body.cs_current_insts /\
  (^contained) protected /\ (^input_origin) s /\ j0 <= k /\
  (^completed_robust) j0 k s tn /\
  (!obs. fn_has_code anchor finish obs ==>
    fn_has_code loop_body child obs /\ fn_has_code child returned obs /\
    lookup_block returned.cs_current_bb obs.fn_blocks = SOME
      <|bb_label := returned.cs_current_bb; bb_instructions :=
        returned.cs_current_insts ++
          abi_decode_backedge_insts returned.cs_next_id iv nv (Var counter) hdr|>) ==>
  (?t Gf tnf.
    (!H. V H ==> gas_origin_ptr_path (DF H,lo,explicit,ctx,fn,PG)
      (s,G,tn) [] (Abort Revert_abort t,Gf,tnf)) /\
    (!obs. fn_has_code anchor finish obs ==> gas_path ctx obs s 0 (Abort Revert_abort t))) \/
  (?t Gf tnf.
    (!H. V H ==> gas_origin_ptr_path (DF H,lo,explicit,ctx,fn,PG)
      (s,G,tn) [] (OK t,Gf,tnf)) /\
    (!obs. fn_has_code anchor finish obs ==> gas_path ctx obs s 0 (OK t)) /\
    ~t.vs_halted /\ t.vs_current_bb = hdr /\ t.vs_inst_idx = 0 /\
    (^loop_resource) anchor (SUC k) t Gf tnf /\
    (^frame) anchor s G tn t Gf tnf /\ (^input_origin) t /\
    (^taint_decreases) tn tnf /\ (^completed_robust) j0 (SUC k) t tnf)``);

val body_observed_statement =
  mk_body_observed_statement guarded_plus completed_robust;
val body_observed_statement_typed =
  mk_body_observed_statement guarded_plus_typed completed_robust_typed;

fun close_statement tm = list_mk_forall (free_vars tm, tm);
val closed_body_observed_statement = close_statement body_observed_statement;
val closed_body_observed_statement_typed = close_statement body_observed_statement_typed;

val _ =
  let
    fun minus xs ys = List.filter (fn x => not (List.exists (aconv x) ys)) xs
    fun same xs ys = null (minus xs ys) andalso null (minus ys xs)
    fun args tm = let val (a, c) = strip_abs tm in a @ fst (strip_forall c) end
    fun check (old, observed) =
      ListPair.allEq (uncurry aconv) (args old, args observed) andalso
      same (free_vars old) (free_vars observed)
    val old = subst [mk_var ("j", numSyntax.num) |-> mk_var ("k", numSyntax.num)] body_statement
    fun pre tm = strip_conj (fst (dest_imp tm))
    val dropped = minus (pre old) (pre body_observed_statement)
    val unchanged =
      case dropped of [child] => aconv (fst (strip_comb child)) guarded_to_buf_motive
                    | _ => false
    val extra = map (fst o dest_var) (minus (free_vars body_observed_statement) (free_vars old))
  in
    if List.all check [(guarded_to_buf_motive, guarded_plus),
                       (bounded_complex_elems_motive, bounded_complex_plus),
                       (repaired_loop_motive, repaired_loop_plus),
                       (guarded_plus, guarded_plus_typed),
                       (bounded_complex_plus, bounded_complex_plus_typed),
                       (repaired_loop_plus, repaired_loop_plus_typed)] andalso
       unchanged andalso null (minus (free_vars old) (free_vars body_observed_statement)) andalso
       length extra = 2 andalso List.exists (fn n => n = "j0") extra andalso
       List.exists (fn n => n = "finish") extra andalso
       ListPair.allEq (uncurry aconv)
         (fst (strip_forall closed_body_observed_statement),
          fst (strip_forall closed_body_observed_statement_typed)) andalso
       null (free_vars closed_body_observed_statement) andalso
       null (free_vars closed_body_observed_statement_typed)
    then () else raise Fail "unexpected observed syntax delta"
  end;
end
