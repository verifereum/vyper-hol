(* TOP-LEVEL: the last two actions of nonempty Log lowering, with actual
   ABI encoder and LOG instruction cuts in the containing function. *)
Theory abiLogCode
Ancestors
  abiEncoderStructure abiEncoder compileEnv context fragExec emitHelper
  emitHelperProps list rich_list

Definition compile_log_abi_emit_def:
  compile_log_abi_emit dst src info topic_ops =
    comp_bind (compile_abi_encode_to_buf dst src info)
      (\size_op. emit_inst LOG
        (Lit (n2w (LENGTH topic_ops)) :: REVERSE topic_ops ++ [size_op;dst]) [])
End

Theorem compile_log_abi_emit_split:
  !dst src info topic_ops cs cs'.
    compile_log_abi_emit dst src info topic_ops cs = ((),cs') <=>
    ?size_op mid. compile_abi_encode_to_buf dst src info cs = (size_op,mid) /\
      emit_inst LOG (Lit (n2w (LENGTH topic_ops)) :: REVERSE topic_ops ++ [size_op;dst]) [] mid = ((),cs')
Proof
  rpt gen_tac >> simp[compile_log_abi_emit_def, comp_bind_def] >>
  Cases_on `compile_abi_encode_to_buf dst src info cs` >> simp[]
QED

Theorem compile_log_abi_emit_code:
  !dst src info topic_ops cs size_op mid cs' func.
    compile_abi_encode_to_buf dst src info cs = (size_op,mid) /\
    emit_inst LOG (Lit (n2w (LENGTH topic_ops)) :: REVERSE topic_ops ++ [size_op;dst]) [] mid = ((),cs') /\
    fn_has_code cs cs' func ==>
    fn_has_code cs mid func /\ fn_has_code mid cs' func
Proof
  rpt gen_tac >> strip_tac >>
  `cs_extends mid cs'` by
    (irule cs_extends_same_block >> drule emit_inst_extends >> simp[IS_PREFIX_APPEND]) >>
  drule_all compile_abi_encode_code_split >> simp[]
QED

val () = List.app (fn (name,th) =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th)
  in if null axioms andalso null (Thm.hyp th) andalso
      List.all (fn s => s = "DISK_THM") oracles
    then () else raise Fail ("unclosed actual Log encoding/emission cuts: " ^ name)
  end) (DB.thms "abiLogCode")
