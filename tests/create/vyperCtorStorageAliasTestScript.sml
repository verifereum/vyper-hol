(* A storage array passed as a constructor argument keeps its location until
   the constructor tuple is copied, after a later pop has changed its length. *)
Theory vyperCtorStorageAliasTest
Ancestors
  vyperCreate vyperStoragePopTest
Libs
  cv_transLib

Definition ctor_storage_old_value_def:
  ctor_storage_old_value = ArrayV (DynArrayV [IntV 11; IntV 37])
End
val () = cv_auto_trans ctor_storage_old_value_def;

Definition ctor_storage_post_pop_def:
  ctor_storage_post_pop =
    SND (assign_target (pop_test_context F)
      (BaseTargetV (TopLevelVar NONE "items") []) PopOp
      (pop_test_state F 2))
End
val () = cv_auto_trans ctor_storage_post_pop_def;

Theorem ctor_storage_arg_reads_after_pop:
  refresh_create_arg (pop_test_context F)
    (TopLevelName (ArrayT (BaseT (UintT 8)) (Dynamic 4))
      (NONE,"items"))
    ctor_storage_old_value ctor_storage_post_pop =
    ArrayV (DynArrayV [IntV 11])
Proof
  CONV_TAC cv_eval
QED

val _ = app (fn (name, th) =>
  if null (List.filter (fn s => s <> "DISK_THM")
             (#1 (Tag.dest_tag (Thm.tag th)))) then ()
  else raise Fail ("Oracle dependency in " ^ name))
  (DB.thms "vyperCtorStorageAliasTest");
