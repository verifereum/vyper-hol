(* Actual staged bytes, including unused padding, flow through the generated
   deployment epilogue. Canonical encoding is not a premise. *)
Theory immutableDeployRelation
Ancestors
  immutableSectionRel immutableDeployExecution compileVyper compileEnv context
  moduleLowering emitHelperProps list

Definition immutable_staging_rel_def:
  immutable_staging_rel tops imms s <=>
    let cap = compute_immutables_len
      (get_struct_fields (make_struct_fields_map tops)) tops in
    immutables_section_rel tops imms
      (TAKE cap (s.vs_memory ++ REPLICATE cap 0w))
End

Theorem immutable_staging_section:
  immutable_staging_rel tops imms s ==>
  ?section. immutables_section_rel tops imms section /\
    TAKE (LENGTH section)
      (s.vs_memory ++ REPLICATE (LENGTH section) 0w) = section
Proof
  rw[immutable_staging_rel_def] >> goal_assum (drule_at Any) >>
  drule immutables_section_rel_length >> simp[]
QED

Theorem compile_constructor_epilogue_section_execution:
  immutables_section_rel tops imms section /\
  compile_constructor_epilogue (LENGTH runtime) (LENGTH section) imm st = ((),st') /\
  FLOOKUP s.vs_allocas st.cs_next_id = SOME (pos,sz) /\
  eval_operand imm
    (update_var ("%" ++ toString (st.cs_next_var + 1))
      (n2w (pos + LENGTH runtime))
      (update_var ("%" ++ toString st.cs_next_var) (n2w pos) s)) = SOME 0w /\
  FLOOKUP s.vs_labels "runtime_begin" = SOME (n2w codepos) /\
  TAKE (LENGTH runtime)
    (DROP codepos s.vs_code ++ REPLICATE (LENGTH runtime) 0w) = runtime /\
  TAKE (LENGTH section)
    (s.vs_memory ++ REPLICATE (LENGTH section) 0w) = section /\
  pos + LENGTH runtime + LENGTH section < dimword (:256) /\
  codepos < dimword (:256) ==>
  ?final. run_inst_seq (emitted_insts st st') s = Halt final /\
    final.vs_returndata = runtime ++ section /\ final.vs_halted /\
    installed_code_rel tops runtime imms final.vs_returndata
Proof
  strip_tac >>
  `?final. run_inst_seq (emitted_insts st st') s = Halt final /\
     final.vs_returndata = runtime ++ section /\ final.vs_halted` by
    (Cases_on `section = []`
     >- (gvs[] >>
         `pos < dimword (:256) /\ LENGTH runtime < dimword (:256)` by decide_tac >>
         drule_all compile_constructor_epilogue_zero_allocated_execution >> simp[]) >>
     `0 < LENGTH section` by
       metis_tac[LENGTH_NIL, arithmeticTheory.NOT_ZERO_LT_ZERO] >>
     drule_all compile_constructor_epilogue_allocated_execution >> simp[]) >>
  qexists_tac `final` >> asm_rewrite_tac[] >>
  simp[installed_code_rel_def] >> qexists_tac `section` >> simp[]
QED

Theorem compile_constructor_epilogue_section_block:
  immutables_section_rel tops imms section /\
  compile_constructor_epilogue (LENGTH runtime) (LENGTH section) imm st = ((),st') /\
  isPREFIX (emitted_insts st st') (DROP s.vs_inst_idx bb.bb_instructions) /\
  run_inst_seq (emitted_insts st st') s = Halt final /\
  final.vs_returndata = runtime ++ section ==>
  ?final'. exec_block fuel ctx bb s = Halt final' /\
    final'.vs_returndata = runtime ++ section /\
    installed_code_rel tops runtime imms final'.vs_returndata
Proof
  strip_tac >>
  drule_all_then (qspecl_then [`fuel`, `ctx`] strip_assume_tac)
    compile_constructor_epilogue_block_bridge >>
  rename1 `exec_block fuel ctx bb s = Halt block_final` >>
  qexists_tac `block_final` >> asm_rewrite_tac[] >>
  simp[installed_code_rel_def] >>
  qexists_tac `section` >> simp[]
QED

val _ = List.app (fn (name, th) => let
  val (oracles, axioms) = Tag.dest_tag (Thm.tag th)
  in if null axioms andalso null (Thm.hyp th) andalso
        List.all (fn s => s = "DISK_THM") oracles then ()
     else raise Fail ("Unclosed immutable deployment relation: " ^ name)
  end) (DB.thms "immutableDeployRelation");
