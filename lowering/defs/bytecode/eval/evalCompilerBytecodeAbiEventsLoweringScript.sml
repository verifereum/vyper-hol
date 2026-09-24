(* Checked source-lowering staging for the mixed-event-types fixture. *)

Theory evalCompilerBytecodeAbiEventsLowering
Ancestors evalCompilerSubsetAbiEvents compileVyper concretizeMemLocDefs alist byte integer_word option cv_std
Libs evalCompilerBytecodeLib finite_mapLib computeLib wordsLib

fun holbuild_extra_deps (_ : string list) = ()
val () = holbuild_extra_deps [".."]
val () = computeLib.upd_compset add_finite_map_compset
val () = computeLib.upd_compset (computeLib.add_thms [fmap_to_alist_FEMPTY])
val () = computeLib.upd_compset (computeLib.add_thms [i2w_pos])
val () = Globals.max_print_depth := 20

Definition mixed_event_types_n2w_def[nocompute]:
  mixed_event_types_n2w n : bytes32 = n2w n
End

Theorem word_of_bytes_be_bytes32_mixed_event_types:
  (word_of_bytes_be bs : bytes32) =
    mixed_event_types_n2w
      (num_of_bytes (be_bytes (dimindex (:256) DIV 8) [] bs))
Proof
  PURE_REWRITE_TAC[mixed_event_types_n2w_def] >>
  irule word_of_bytes_be_eq_num_of_bytes >> EVAL_TAC
QED

Theorem word_of_bytes_bytes32_mixed_event_types:
  (word_of_bytes T 0w bs : bytes32) =
    mixed_event_types_n2w
      (num_of_bytes (be_bytes (dimindex (:256) DIV 8) [] bs))
Proof
  simp[GSYM byteTheory.word_of_bytes_be_def,
       word_of_bytes_be_bytes32_mixed_event_types]
QED

Theorem w2n_mixed_event_types_n2w[compute]:
  w2n (mixed_event_types_n2w n) = n MOD dimword (:256)
Proof
  simp[mixed_event_types_n2w_def]
QED

Theorem get_byte_set_byte_bytes32_mixed_event_types:
  get_byte a (set_byte a b (w : bytes32) be) be = b
Proof
  simp[byteTheory.get_byte_set_byte]
QED

Theorem get_byte_set_byte_irrelevant_bytes32_mixed_event_types:
  w2n (a : bytes32) MOD 32 <> w2n a' MOD 32 ==>
  get_byte a' (set_byte a b (w : bytes32) be) be = get_byte a' w be
Proof
  simp[byteTheory.get_byte_set_byte_irrelevant]
QED

Theorem word_to_bytes_be_bytes32_genlist_mixed_event_types:
  word_to_bytes_be (w : bytes32) =
    GENLIST (λi. get_byte (n2w i) w T) 32
Proof
  simp[listTheory.LIST_EQ_REWRITE, byteTheory.word_to_bytes_be_def,
       byteTheory.word_to_bytes_def, byteTheory.EL_word_to_bytes_aux]
QED

Theorem word_of_bytes_be_word_to_bytes_be_mixed_event_types:
  word_of_bytes_be (word_to_bytes_be (w : bytes32)) = w
Proof
  simp[byteTheory.word_to_bytes_be_def, byteTheory.word_of_bytes_be_def,
       byteTheory.word_of_bytes_word_to_bytes]
QED

val () = computeLib.upd_compset
  (computeLib.add_thms
    [word_of_bytes_be_bytes32_mixed_event_types,
     word_of_bytes_bytes32_mixed_event_types,
     w2n_mixed_event_types_n2w,
     contextTheory.compile_copy_memory_def])

val mixed_event_types_policy_eval = save_thm
  ("mixed_event_types_policy_eval",
   EVAL ``resolve_o1_policy (o1_policy prague_capabilities)``)
val mixed_event_types_rpolicy = optionSyntax.dest_some
  (rhs (concl mixed_event_types_policy_eval))
val mixed_event_types_runtime_unit_eval = save_thm
  ("mixed_event_types_runtime_unit_eval",
   EVAL ``lower_vyper_runtime_unit task090_mixed_event_types_program
           ^mixed_event_types_rpolicy``)
