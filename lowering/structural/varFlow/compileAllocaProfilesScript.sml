(* TOP-LEVEL: compiler allocation profiles split and nest through actual
   compiler extensions, including current instructions moved into blocks.
   These are instruction-membership facts; allocation IDs need no ordering. *)
Theory compileAllocaProfiles
Ancestors
  compileAllocaProvenance compileEnv fragExec venomInst list rich_list pred_set

Theorem compiler_current_instruction_extends:
  !before after inst.
    cs_extends before after /\ MEM inst before.cs_current_insts ==>
    compiler_instruction_member after inst
Proof
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `cs_extends _ _` (mp_tac o REWRITE_RULE [cs_extends_def]) >>
  disch_then (qx_choose_then `added` strip_assume_tac) >> Cases_on `added = []`
  >- (gvs[compiler_instruction_member_def, IS_PREFIX_APPEND] >> simp[MEM_APPEND]) >>
  gvs[] >>
  `MEM inst (LAST added).bb_instructions` by
    (qpat_x_assum `isPREFIX _ _` (mp_tac o REWRITE_RULE [IS_PREFIX_APPEND]) >>
     strip_tac >> simp[MEM_APPEND]) >>
  simp_tac bool_ss [compiler_instruction_member_def] >> disj2_tac >> qexists_tac `LAST added` >>
  simp[MEM_APPEND, LAST_MEM]
QED

Theorem compiler_instruction_member_extends:
  !before after inst.
    cs_extends before after /\ compiler_instruction_member before inst ==>
    compiler_instruction_member after inst
Proof
  rpt gen_tac >> strip_tac >> Cases_on `MEM inst before.cs_current_insts`
  >- (drule_all compiler_current_instruction_extends >> simp[]) >>
  qpat_x_assum `compiler_instruction_member before inst`
    (mp_tac o REWRITE_RULE [compiler_instruction_member_def]) >> asm_simp_tac bool_ss [] >>
  disch_then (qx_choose_then `bb` strip_assume_tac) >>
  `MEM bb after.cs_blocks` by (fs[cs_extends_def] >> simp[MEM_APPEND]) >>
  simp_tac bool_ss [compiler_instruction_member_def] >> disj2_tac >> qexists_tac `bb` >> simp[]
QED

Theorem compiler_alloca_profile_subprofile:
  !before child_before child_after after.
    cs_extends before child_before /\ cs_extends child_after after ==>
    set (compiler_alloca_ids child_before child_after) SUBSET set (compiler_alloca_ids before after)
Proof
  rpt gen_tac >> strip_tac >> simp_tac (srw_ss()) [SUBSET_DEF] >> qx_gen_tac `id` >>
  simp_tac bool_ss [compiler_alloca_ids_member] >>
  disch_then (qx_choose_then `inst` strip_assume_tac) >>
  `compiler_instruction_member after inst` by
    (drule_all compiler_instruction_member_extends >> simp[]) >>
  `~compiler_instruction_member before inst` by
    (DISCH_TAC >> qspecl_then [`before`, `child_before`, `inst`]
       mp_tac compiler_instruction_member_extends >> impl_tac >- simp[] >> simp[]) >>
  qexists_tac `inst` >> simp[]
QED

Theorem compiler_alloca_profile_split:
  !before middle after.
    cs_extends before middle /\ cs_extends middle after ==>
    set (compiler_alloca_ids before after) =
      set (compiler_alloca_ids before middle) UNION set (compiler_alloca_ids middle after)
Proof
  rpt gen_tac >> strip_tac >>
  `!inst. compiler_instruction_member before inst ==> compiler_instruction_member middle inst` by
    (rpt strip_tac >> drule_all compiler_instruction_member_extends >> simp[]) >>
  `!inst. compiler_instruction_member middle inst ==> compiler_instruction_member after inst` by
    (rpt strip_tac >> drule_all compiler_instruction_member_extends >> simp[]) >>
  simp[EXTENSION, compiler_alloca_ids_member] >> metis_tac[]
QED

val () = List.app (fn (name,th) =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th)
  in if null axioms andalso null (Thm.hyp th) andalso
      List.all (fn s => s = "DISK_THM") oracles
    then () else raise Fail ("unclosed nested compiler allocation profiles: " ^ name)
  end) (DB.thms "compileAllocaProfiles")
