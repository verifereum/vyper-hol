(* Checked runtime-pipeline staging for the external-dynamic fixture. *)

Theory evalCompilerBytecodeAbiExternalDynamicPipeline
Ancestors evalCompilerSubsetAbiExternal compileVyper concretizeMemLocDefs alist byte integer_word option cv_std
Libs evalCompilerBytecodeLib finite_mapLib computeLib wordsLib

fun holbuild_extra_deps (_ : string list) = ()
val () = holbuild_extra_deps [".."]
val () = computeLib.upd_compset add_finite_map_compset
val () = computeLib.upd_compset (computeLib.add_thms [fmap_to_alist_FEMPTY])
val () = computeLib.upd_compset (computeLib.add_thms [i2w_pos])
val () = Globals.max_print_depth := 20

(* Keep concrete words in numeral form while evaluating the checked pipeline.
   The opaque wrapper is definitionally n2w, but avoids eagerly expanding a
   256-bit numeral into nested set_byte terms. *)
Definition external_dynamic_n2w_def[nocompute]:
  external_dynamic_n2w n : bytes32 = n2w n
End

Theorem word_of_bytes_be_bytes32_external_dynamic:
  (word_of_bytes_be bs : bytes32) =
    external_dynamic_n2w
      (num_of_bytes (be_bytes (dimindex (:256) DIV 8) [] bs))
Proof
  PURE_REWRITE_TAC[external_dynamic_n2w_def] >>
  irule word_of_bytes_be_eq_num_of_bytes >> EVAL_TAC
QED

Theorem word_of_bytes_bytes32_external_dynamic:
  (word_of_bytes T 0w bs : bytes32) =
    external_dynamic_n2w
      (num_of_bytes (be_bytes (dimindex (:256) DIV 8) [] bs))
Proof
  simp[GSYM byteTheory.word_of_bytes_be_def,
       word_of_bytes_be_bytes32_external_dynamic]
QED

Theorem w2n_external_dynamic_n2w[compute]:
  w2n (external_dynamic_n2w n) = n MOD dimword (:256)
Proof
  simp[external_dynamic_n2w_def]
QED

Theorem get_byte_set_byte_bytes32_external_dynamic:
  get_byte a (set_byte a b (w : bytes32) be) be = b
Proof
  simp[byteTheory.get_byte_set_byte]
QED

Theorem get_byte_set_byte_irrelevant_bytes32_external_dynamic:
  w2n (a : bytes32) MOD 32 <> w2n a' MOD 32 ==>
  get_byte a' (set_byte a b (w : bytes32) be) be = get_byte a' w be
Proof
  simp[byteTheory.get_byte_set_byte_irrelevant]
QED

Theorem word_to_bytes_be_bytes32_genlist_external_dynamic:
  word_to_bytes_be (w : bytes32) =
    GENLIST (λi. get_byte (n2w i) w T) 32
Proof
  simp[listTheory.LIST_EQ_REWRITE, byteTheory.word_to_bytes_be_def,
       byteTheory.word_to_bytes_def, byteTheory.EL_word_to_bytes_aux]
QED

Theorem word_of_bytes_be_word_to_bytes_be_external_dynamic:
  word_of_bytes_be (word_to_bytes_be (w : bytes32)) = w
Proof
  simp[byteTheory.word_to_bytes_be_def, byteTheory.word_of_bytes_be_def,
       byteTheory.word_of_bytes_word_to_bytes]
QED

val () = computeLib.upd_compset
  (computeLib.add_thms
    [word_of_bytes_be_bytes32_external_dynamic,
     word_of_bytes_bytes32_external_dynamic,
     w2n_external_dynamic_n2w,
     contextTheory.compile_copy_memory_def])

Definition external_dynamic_runtime_pipeline_def:
  external_dynamic_runtime_pipeline tops =
    case resolve_o1_policy (o1_policy all_capabilities) of
      NONE => NONE
    | SOME rpolicy =>
        case lower_vyper_runtime_unit tops rpolicy of
          NONE => NONE
        | SOME unit =>
            OPTION_MAP (λout. (rpolicy,out))
              (run_venom_pipeline (K T) (K T) (K T)
                 rpolicy o1_pipeline_spec unit)
End

Definition external_dynamic_runtime_compile_def:
  external_dynamic_runtime_compile tops =
    case external_dynamic_runtime_pipeline tops of
      NONE => NONE
    | SOME (rpolicy,out) =>
        if out.po_final_assembly <> rpolicy.rpol_final_assembly then NONE
        else finalize_codegen (K SOME) rpolicy out.po_unit
End

Definition external_dynamic_deploy_compile_def:
  external_dynamic_deploy_compile tops runtime =
    case resolve_o1_policy (o1_policy all_capabilities) of
      NONE => NONE
    | SOME rpolicy =>
        case lower_vyper_deploy_unit tops rpolicy runtime of
          NONE => NONE
        | SOME unit =>
            checked_unit_pipeline
              (λrp u. run_venom_pipeline (K T) (K T) (K T)
                 rp o1_pipeline_spec u)
              (K SOME) rpolicy unit
End

val external_dynamic_runtime_pipeline_eval =
  save_thm ("external_dynamic_runtime_pipeline_eval",
    EVAL ``external_dynamic_runtime_pipeline task090_external_dynamic_program``)
