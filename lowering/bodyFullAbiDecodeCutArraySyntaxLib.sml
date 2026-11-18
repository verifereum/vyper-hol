(* Parameterized observation for the array constructor. The ordinary
   constructor uses the same phase bind with the observation disabled. *)
structure bodyFullAbiDecodeCutArraySyntaxLib =
struct
open HolKernel boolLib bossLib
open abiEncoderTheory compileEnvTheory venomStateTheory venomExecSemanticsTheory
     venomInstTheory fragExecTheory fragGasPathTheory emitHelperPropsTheory
     exprSimAbiGasBridgeTheory
     bodyFullAbiDecodeLoopObservedSyntaxLib
     bodyFullAbiDecodeRuntimeLoopLengthObservedLib
     bodyFullAbiDecodeCutPathLib

val array_mode = ``observe_array:bool``;
val array_relation = ``observe_phase:compile_state -> compile_state ->
  venom_state -> exec_result -> bool``;

val array_crossing = ``\a b.
  cs_extends cut_ready a /\ cs_extends b cut_finish /\
  a.cs_blocks = cut_start.cs_blocks /\ b.cs_blocks <> cut_start.cs_blocks``;

val array_cert = ``\a b s r. ^array_mode ==> ^array_relation a b s r``;

val array_straight_rule = ``!a b s r.
  cs_extends cut_ready a /\ cs_extends a b /\ cs_extends b cut_finish /\
  a.cs_blocks = cut_start.cs_blocks /\ b.cs_blocks = a.cs_blocks /\
  EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
    (emitted_insts a b) /\
  ~s.vs_halted /\ s.vs_current_bb = a.cs_current_bb /\
  s.vs_inst_idx = LENGTH a.cs_current_insts /\
  (!obs. fn_has_code a b obs ==> gas_path ctx obs s 0 r) /\
  ((?t. r = OK t /\ ~t.vs_halted /\ t.vs_current_bb = b.cs_current_bb /\
        t.vs_inst_idx = LENGTH b.cs_current_insts) \/
   (?t. r = Abort Revert_abort t)) ==>
  ^array_relation a b s r``;

val array_bind_rule = ``!a b c s t r.
  ^array_relation a b s (OK t) /\ ^array_relation b c t r ==>
  ^array_relation a c s r``;

val array_revert_rule = ``!a b c s t.
  ^array_relation a b s (Abort Revert_abort t) ==>
  ^array_relation a c s (Abort Revert_abort t)``;

val array_cut_layout = ``
  cs_extends cut_start cut_ready /\ cut_start.cs_blocks <> cut_finish.cs_blocks /\
  frag_ops_free cut_start cut_finish /\ FST (cut:string # num) <> L /\
  (?ids fn id. LENGTH ids = LENGTH cut_start.cs_current_insts /\
     fn_has_code cut_start cut_finish fn /\
     cut_observer = frag_relabel_observer cut_start cut_finish L ids fn id /\
     fn_has_code (start_relabel L ids cut_start) (start_swap cut_start L ids cut_finish)
       cut_observer)``;

(* Preserve all descent arguments and old entry/post binders. *)
fun decorate_array_motive old =
  let
    val (args, clause) = strip_abs old
    val (params, implication) = strip_forall clause
    val (entry, post) = dest_imp implication
    fun param name = List.find (fn v => fst (dest_var v) = name) params |> valOf
    val a = param "start"
    val b = param "finish"
    val s = param "s"
    val entry' = mk_conj (entry, ``^array_mode ==> ^array_crossing ^a ^b``)
    val post' = extend_post post ``\r. ^array_cert ^a ^b ^s r``
  in
    list_mk_abs (args, list_mk_forall (params, mk_imp (entry', post')))
  end;

fun clause_of guarded loop =
  abiEncoderTheory.compile_abi_decode_to_buf_ind
  |> ISPECL [guarded, bounded_complex_plus_typed, loop]
  |> BETA_RULE |> concl |> dest_imp |> fst |> strip_conj
  |> (fn clauses => List.nth (clauses, 2));

val array_decorated_clause =
  clause_of (decorate_array_motive guarded_plus_typed)
    (decorate_array_motive repaired_loop_length_plus_typed);

(* Fix the observer and outer cut before any of the phase witnesses are
   selected.  Each phase certificate accepts the shadow of its actual input. *)
val array_shadow = ``\a b s r.
  !u. ~u.vs_halted /\
      (u.vs_current_bb,u.vs_inst_idx) = (^shadow_cursor) L cut_start a /\
      frag_relabel_state L cut_start.cs_current_bb u s ==>
      (^shadow_result) ctx cut_observer cut L cut_start.cs_current_bb u
        ((^shadow_cursor) L cut_start b) r``;

fun specialize_array_cut tm =
  subst [array_mode |-> T, array_relation |-> array_shadow] tm;

val array_cut_straight_rule = specialize_array_cut array_straight_rule;
val array_cut_clause = specialize_array_cut array_decorated_clause;
end
