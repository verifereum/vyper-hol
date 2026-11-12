(* Opt-in regression check: each fixture lowers to a unit satisfying
   o1_source_unit_ok, the raw O1-source shape that S2
   (lower_vyper_runtime_unit_source_unit_ok) promises. Each lowering is
   evaluated once at top level and the shape is decided by
   o1_source_unit_check, whose soundness is proved.
   TOP-LEVEL: <fixture>_source_unit_ok for six fixtures covering external
   dispatch, an internal call, a loop, a dynamic internal argument, dynamic
   ABI encoding and a storage dynamic array. *)

Theory evalCompilerSourceShape
Ancestors
  evalCompiler evalCompilerSubsetAbiInternalCalls evalCompilerSubsetAbiBuiltins
  evalCompilerSubsetState o1SourceUnitCheck compileVyper concretizeMemLocDefs
  alist byte integer_word option
Libs finite_mapLib computeLib wordsLib

val () = computeLib.upd_compset add_finite_map_compset
val () = computeLib.upd_compset (computeLib.add_thms [fmap_to_alist_FEMPTY])
val () = computeLib.upd_compset (computeLib.add_thms [i2w_pos])

Theorem lowered_source_unit_ok_intro[local]:
  resolve_o1_policy p = SOME r /\ lower_vyper_runtime_unit prog r = SOME u /\
  o1_source_unit_ok u ==>
  !rpolicy.
    resolve_o1_policy p = SOME rpolicy ==>
    ?unit.
      lower_vyper_runtime_unit prog rpolicy = SOME unit /\
      o1_source_unit_ok unit
Proof
  rw[] >> gvs[] >> qexists_tac `u` >> simp[]
QED

val policy_eval = EVAL ``resolve_o1_policy (o1_policy all_capabilities)``
val rpolicy = optionSyntax.dest_some (rhs (concl policy_eval))

(* Names the o1_source_unit_check_def conjuncts that don't evaluate to T. *)
fun failing_conjuncts prog unit =
  let
    val conjs = strip_conj (rhs (concl
      (SPEC unit (GEN_ALL (SPEC_ALL o1_source_unit_check_def)))))
    fun ok c = aconv (rhs (concl (EVAL c))) T
    val numbered =
      ListPair.zip (List.tabulate (length conjs, fn i => i + 1), conjs)
    val bad = List.filter (not o ok o snd) numbered
  in
    "o1_source_unit_check fails for " ^ term_to_string prog ^
    "; conjuncts of o1_source_unit_check_def not T: " ^
    String.concatWith ", " (map (Int.toString o fst) bad)
  end

(* |- resolve ... = SOME r /\ lower prog r = SOME u /\ o1_source_unit_ok u,
   with the evaluation kept out of the theorem proofs below. *)
fun source_shape_facts prog =
  let
    val lower_eval = EVAL ``lower_vyper_runtime_unit ^prog ^rpolicy``
    val unit = optionSyntax.dest_some (rhs (concl lower_eval))
    val check = EQT_ELIM (EVAL ``o1_source_unit_check ^unit``)
      handle HOL_ERR _ => raise Fail (failing_conjuncts prog unit)
  in
    LIST_CONJ [policy_eval, lower_eval,
               MATCH_MP o1_source_unit_check_sound check]
  end

val two_external_facts = source_shape_facts ``two_external_program``
val internal_call_arg_facts = source_shape_facts ``internal_call_arg_program``
val for_accum_facts = source_shape_facts ``for_accum_program``
val internal_bytes_call_facts =
  source_shape_facts ``task090_internal_bytes_call_program``
val abi_dynamic_facts = source_shape_facts ``task090_abi_dynamic_program``
val storage_dynarray_facts = source_shape_facts ``storage_dynarray_program``

Theorem two_external_source_unit_ok:
  !rpolicy.
    resolve_o1_policy (o1_policy all_capabilities) = SOME rpolicy ==>
    ?unit.
      lower_vyper_runtime_unit two_external_program rpolicy = SOME unit /\
      o1_source_unit_ok unit
Proof
  ACCEPT_TAC (MATCH_MP lowered_source_unit_ok_intro two_external_facts)
QED

Theorem internal_call_arg_source_unit_ok:
  !rpolicy.
    resolve_o1_policy (o1_policy all_capabilities) = SOME rpolicy ==>
    ?unit.
      lower_vyper_runtime_unit internal_call_arg_program rpolicy = SOME unit /\
      o1_source_unit_ok unit
Proof
  ACCEPT_TAC (MATCH_MP lowered_source_unit_ok_intro internal_call_arg_facts)
QED

Theorem for_accum_source_unit_ok:
  !rpolicy.
    resolve_o1_policy (o1_policy all_capabilities) = SOME rpolicy ==>
    ?unit.
      lower_vyper_runtime_unit for_accum_program rpolicy = SOME unit /\
      o1_source_unit_ok unit
Proof
  ACCEPT_TAC (MATCH_MP lowered_source_unit_ok_intro for_accum_facts)
QED

Theorem internal_bytes_call_source_unit_ok:
  !rpolicy.
    resolve_o1_policy (o1_policy all_capabilities) = SOME rpolicy ==>
    ?unit.
      lower_vyper_runtime_unit task090_internal_bytes_call_program rpolicy =
        SOME unit /\ o1_source_unit_ok unit
Proof
  ACCEPT_TAC (MATCH_MP lowered_source_unit_ok_intro internal_bytes_call_facts)
QED

Theorem abi_dynamic_source_unit_ok:
  !rpolicy.
    resolve_o1_policy (o1_policy all_capabilities) = SOME rpolicy ==>
    ?unit.
      lower_vyper_runtime_unit task090_abi_dynamic_program rpolicy =
        SOME unit /\ o1_source_unit_ok unit
Proof
  ACCEPT_TAC (MATCH_MP lowered_source_unit_ok_intro abi_dynamic_facts)
QED

Theorem storage_dynarray_source_unit_ok:
  !rpolicy.
    resolve_o1_policy (o1_policy all_capabilities) = SOME rpolicy ==>
    ?unit.
      lower_vyper_runtime_unit storage_dynarray_program rpolicy = SOME unit /\
      o1_source_unit_ok unit
Proof
  ACCEPT_TAC (MATCH_MP lowered_source_unit_ok_intro storage_dynarray_facts)
QED
