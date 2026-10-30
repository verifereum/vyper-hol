(* TOP-LEVEL: shared generative recursion for the actual member compiler.
   The callback executes a whole member, returning the runtime state and
   invariant for the recursive suffix, plus its certificate continuation.
   This is not a fold over an assumed execution: only compiler code is given. *)
Theory abiEncoderMembersGenerate
Ancestors
  abiFieldsStructure abiFieldsCons abiComplexStructure compileEnv fragExec list pair

Theorem abi_encoder_members_generate:
  (!ei az mz dyn rest st so ho out en x s len ce.
    compile_abi_encode_complex_elems dst src ((ei,az,mz,dyn)::rest) so ho dp st = (out,en) /\
    fn_has_code st en func /\ Inv ((ei,az,mz,dyn)::rest) (st,so,ho) (out,en) x s /\
    compile_abi_encode_child dst (Var (compiler_var_name st.cs_next_var 0)) ei dyn ho dp
      (abi_complex_field_cut src so st) = (len,ce) /\
    compile_abi_encode_complex_elems dst src rest (so+mz) (ho+az) dp ce = (out,en) /\
    fn_has_code st ce func /\ fn_has_code ce en func /\ cs_extends ce en ==>
    ?x' u. Inv rest (ce,so+mz,ho+az) (out,en) x' u /\
      (!t. Run rest (ce,so+mz,ho+az) (out,en) u t ==>
        Run ((ei,az,mz,dyn)::rest) (st,so,ho) (out,en) s t)) /\
  (!st so ho out en x s.
    compile_abi_encode_complex_elems dst src [] so ho dp st = (out,en) /\
    fn_has_code st en func /\ Inv [] (st,so,ho) (out,en) x s ==>
    Run [] (st,so,ho) (out,en) s s /\ Post (out,en) s) ==>
  !infos st so ho out en x s.
    compile_abi_encode_complex_elems dst src infos so ho dp st = (out,en) /\
    fn_has_code st en func /\ Inv infos (st,so,ho) (out,en) x s ==>
    ?t. Run infos (st,so,ho) (out,en) s t /\ Post (out,en) t
Proof
  disch_then (CONJUNCTS_THEN2 ASSUME_TAC ASSUME_TAC) >> Induct
  >- (rpt strip_tac >> qexists_tac `s` >> metis_tac[]) >>
  simp_tac bool_ss [FORALL_PROD] >>
  MAP_EVERY qx_gen_tac [`ei`, `az`, `mz`, `dyn`] >> rpt gen_tac >> strip_tac >>
  qpat_x_assum `compile_abi_encode_complex_elems _ _ (_::_) _ _ _ _ = _`
    (fn th => ASSUME_TAC th >> mp_tac (PURE_REWRITE_RULE [compile_abi_fields_cons_cuts] th)) >>
  disch_then (qx_choose_then `len` (qx_choose_then `ce` strip_assume_tac)) >>
  drule_all abi_fields_step_contains >> strip_tac >>
  `cs_extends ce en` by (drule_all compile_abi_fields_extends >> simp[]) >>
  qpat_x_assum `!ei az mz dyn rest st so ho out en x s len ce. _`
    (drule_all_then strip_assume_tac) >>
  first_x_assum (drule_all_then strip_assume_tac) >>
  qexists_tac `t` >> asm_simp_tac bool_ss []
QED

val () = List.app (fn (name,th) =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th)
  in if null axioms andalso null (Thm.hyp th) andalso
      List.all (fn s => s = "DISK_THM") oracles
    then () else raise Fail ("unclosed member execution generator: " ^ name)
  end) (DB.thms "abiEncoderMembersGenerate")
