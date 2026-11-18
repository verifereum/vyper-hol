(* A read of a storage array after a later pop sees the shortened array; a
   constructor argument is read before such a later argument runs. *)
Theory vyperCtorStorageAliasTest
Ancestors
  vyperCreate vyperStoragePopTest
Libs
  wordsLib cv_transLib

Definition ctor_storage_old_value_def:
  ctor_storage_old_value = ArrayV (DynArrayV [IntV 11; IntV 37])
End
val () = cv_auto_trans ctor_storage_old_value_def;

Definition ctor_storage_post_pop_def:
  ctor_storage_post_pop =
    SND (pop_place (pop_test_context F)
      (StoragePlace F 4w (ArrayTV (BaseTV (UintT 8)) (Dynamic 4)))
      (pop_test_state F 2))
End
val () = cv_auto_trans ctor_storage_post_pop_def;

Theorem ctor_storage_arg_reads_after_pop:
  FST (read_result (pop_test_context F)
    (PlaceR (StoragePlace F 4w (ArrayTV (BaseTV (UintT 8)) (Dynamic 4))))
    ctor_storage_post_pop) = INL (ArrayV (DynArrayV [IntV 11]))
Proof
  CONV_TAC cv_eval
QED
