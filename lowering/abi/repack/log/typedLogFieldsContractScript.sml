(* TOP-LEVEL: aligned declared/source field types provide the physical
   strides and individual field contracts used by full data packing. *)
Theory typedLogFieldsContract
Ancestors
  typedLogFieldContract valueEncoding context compileEnv venomInst list

Definition log_field_list_contract_def:
  log_field_list_contract ctx func cenv [] ([]:(operand # type) list) [] [] = T /\
  log_field_list_contract ctx func cenv (fty::fts) ((src,aty)::ops) (ftv::ftvs) (atv::atvs) =
    (type_memory_bytes cenv fty = type_memory_size ftv /\
      log_field_type_contract ctx func cenv fty aty ftv atv /\
      log_field_list_contract ctx func cenv fts ops ftvs atvs) /\
  log_field_list_contract ctx func cenv _ _ _ _ = F
End

val () = List.app (fn (name,th) =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th)
  in if null axioms andalso null (Thm.hyp th) andalso
      List.all (fn s => s = "DISK_THM") oracles
    then () else raise Fail ("unclosed aligned Log field list contracts: " ^ name)
  end) (DB.thms "typedLogFieldsContract")
