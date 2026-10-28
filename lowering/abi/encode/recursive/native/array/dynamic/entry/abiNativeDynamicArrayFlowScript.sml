(* TOP-LEVEL: actual dynamic-array compilation extends code and preserves
   fresh instruction history while monotonically reserving SSA names. *)
Theory abiNativeDynamicArrayFlow
Ancestors
  abiIdFlow abiEncodeVarFlow abiEncoderStructure compileIdFlow compileVarFlow compileEnv fragExec venomState

Theorem abi_native_dynamic_array_flow:
  !dst src info width stride len_op cs ret after.
    compile_abi_encode_dyn_loop dst src info width stride len_op cs = (ret,after) /\ compiler_id_history cs ==>
    cs_extends cs after /\ cs.cs_next_var <= after.cs_next_var /\ compiler_id_history after
Proof
  rpt gen_tac >> strip_tac >> drule compile_abi_loop_id_flow >> strip_tac >>
  `compiler_id_history after` by (first_x_assum irule >> first_assum MATCH_ACCEPT_TAC) >>
  qspecl_then [`dst`, `src`, `info`, `width`, `stride`, `len_op`] mp_tac (cj 4 compiler_vars_mono_abi_encode) >>
  DISCH_TAC >> drule_all compiler_vars_mono_result >> DISCH_TAC >>
  qspecl_then [`dst`, `src`, `info`, `width`, `stride`, `len_op`] mp_tac (cj 4 cs_appends_compile_abi_encode) >>
  simp_tac bool_ss [cs_appends_def] >> DISCH_TAC >>
  `cs_extends cs after` by (first_x_assum drule >> simp[]) >> simp[]
QED

val () = List.app (fn (name,th) =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th)
  in if null axioms andalso null (Thm.hyp th) andalso List.all (fn s => s = "DISK_THM") oracles
    then () else raise Fail ("unclosed actual dynamic array compiler history and name flow: " ^ name)
  end) (DB.thms "abiNativeDynamicArrayFlow")
