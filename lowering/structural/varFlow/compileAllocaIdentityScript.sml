(* TOP-LEVEL: a function instruction already present at a compiler cut has
   an identity outside that cut's new allocation profile. Instruction-ID
   uniqueness replaces assumptions about numerical allocation-ID ranges. *)
Theory compileAllocaIdentity
Ancestors
  compileAllocaProvenance localPtrsProps compileEnv fragExec venomInst list

Theorem compiler_old_instruction_outside_alloca_profile:
  !before after func old_inst.
    cs_extends before after /\ fn_has_code before after func /\ fn_inst_ids_distinct func /\
    MEM old_inst (fn_insts func) /\ compiler_instruction_member before old_inst ==>
    ~MEM old_inst.inst_id (compiler_alloca_ids before after)
Proof
  rpt gen_tac >> strip_tac >> DISCH_TAC >>
  qpat_x_assum `MEM _ (compiler_alloca_ids _ _)`
    (mp_tac o REWRITE_RULE [compiler_alloca_ids_member]) >>
  disch_then (qx_choose_then `new_inst` strip_assume_tac) >>
  `MEM new_inst (fn_insts func)` by
    (qspecl_then [`before`, `after`, `func`, `new_inst`] mp_tac compiler_new_instruction_member >> simp[]) >>
  `new_inst = old_inst` by
    (qspecl_then [`func`, `new_inst`, `old_inst`] mp_tac fn_inst_ids_distinct_inj >> simp[]) >> fs[]
QED

val () = List.app (fn (name,th) =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th)
  in if null axioms andalso null (Thm.hyp th) andalso
      List.all (fn s => s = "DISK_THM") oracles
    then () else raise Fail ("unclosed old instruction allocation identity: " ^ name)
  end) (DB.thms "compileAllocaIdentity")
