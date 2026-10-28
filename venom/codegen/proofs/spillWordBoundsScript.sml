(* Spill addresses fit machine words when the emitted PUSH bytes fit.
   TOP-LEVEL: codegen_assembly_push_sizes, plan_restore_offset_word_bound. *)
Theory spillWordBounds
Ancestors
  asmIR asmSem asmTargetSafety codegen stackPlanTypes stackPlanGen planExec
  venomMemProps words list rich_list arithmetic

Theorem encode_num_bytes_length_bound:
  !fuel n. LENGTH (encode_num_bytes n) <= fuel ==> n < 256 ** fuel
Proof
  Induct_on `fuel` >> gen_tac >> Cases_on `n = 0` >>
  simp[Once encode_num_bytes_def, LENGTH_SNOC] >> strip_tac >>
  first_x_assum drule >> simp[EXP, DIV_LT_X, MULT_COMM]
QED

Theorem asm_block_at_member:
  !prog pc code inst.
    asm_block_at prog pc code /\ MEM inst code ==> MEM inst prog
Proof
  rpt gen_tac >> strip_tac >> fs[MEM_EL, asm_block_at_def] >>
  rename1 `inst = EL idx code` >> qexists_tac `pc + idx` >>
  conj_tac >- decide_tac >>
  first_x_assum (qspec_then `idx` mp_tac) >> simp[]
QED

Theorem assembly_target_safe_push_sizes:
  !caps prog.
    assembly_target_safe caps prog ==>
    !bytes. MEM (AsmPush bytes) prog ==> LENGTH bytes <= 32
Proof
  rpt gen_tac >> simp[assembly_target_safe_def, EVERY_MEM] >> strip_tac >>
  rpt gen_tac >> strip_tac >> first_x_assum drule >>
  simp[asm_inst_target_safe_def] >> Cases_on `bytes` >> simp[]
QED

Theorem codegen_assembly_push_sizes:
  !rpolicy unit prog.
    codegen_assembly rpolicy unit = SOME prog ==>
    !bytes. MEM (AsmPush bytes) prog ==> LENGTH bytes <= 32
Proof
  rpt gen_tac >> strip_tac >>
  `assembly_target_safe rpolicy.rpol_target prog` by
    gvs[codegen_assembly_def, LET_THM, AllCaseEqs()] >>
  drule assembly_target_safe_push_sizes >> simp_tac bool_ss []
QED

Theorem plan_restore_offset_word_bound:
  !initial_fmp ops prog pc off.
    (!bytes. MEM (AsmPush bytes) prog ==> LENGTH bytes <= 32) /\
    asm_block_at prog pc (execute_plan initial_fmp ops) /\
    MEM (SORestore off) ops ==> off < dimword(:256)
Proof
  rpt gen_tac >> strip_tac >>
  `MEM (AsmPush (encode_num_bytes off)) (execute_plan initial_fmp ops)` by
    (simp[execute_plan_def, MEM_FLAT, MEM_MAP, PULL_EXISTS] >>
     qexists_tac `SORestore off` >> asm_simp_tac (srw_ss()) [exec_stack_op_def]) >>
  `MEM (AsmPush (encode_num_bytes off)) prog` by
    (irule asm_block_at_member >>
     qexistsl_tac [`execute_plan initial_fmp ops`,`pc`] >> asm_rewrite_tac []) >>
  `LENGTH (encode_num_bytes off) <= 32` by
    (first_x_assum irule >> first_assum ACCEPT_TAC) >>
  mp_tac (Q.SPECL [`32`,`off`] encode_num_bytes_length_bound) >>
  asm_simp_tac (srw_ss()) [dimword_def, dimindex_256]
QED

Theorem plan_spill_offset_word_bound:
  !initial_fmp ops prog pc off.
    (!bytes. MEM (AsmPush bytes) prog ==> LENGTH bytes <= 32) /\
    asm_block_at prog pc (execute_plan initial_fmp ops) /\
    MEM (SOSpill off) ops ==> off < dimword(:256)
Proof
  rpt gen_tac >> strip_tac >>
  `MEM (AsmPush (encode_num_bytes off)) (execute_plan initial_fmp ops)` by
    (simp[execute_plan_def, MEM_FLAT, MEM_MAP, PULL_EXISTS] >>
     qexists_tac `SOSpill off` >> asm_simp_tac (srw_ss()) [exec_stack_op_def]) >>
  `MEM (AsmPush (encode_num_bytes off)) prog` by
    (irule asm_block_at_member >>
     qexistsl_tac [`execute_plan initial_fmp ops`,`pc`] >> asm_rewrite_tac []) >>
  `LENGTH (encode_num_bytes off) <= 32` by
    (first_x_assum irule >> first_assum ACCEPT_TAC) >>
  mp_tac (Q.SPECL [`32`,`off`] encode_num_bytes_length_bound) >>
  asm_simp_tac (srw_ss()) [dimword_def, dimindex_256]
QED

val () = List.app (fn (name,th) =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th)
  in if null axioms andalso null (Thm.hyp th) andalso
      List.all (fn s => s = "DISK_THM") oracles
    then () else raise Fail ("unclosed spill word-bound proof: " ^ name)
  end) (DB.thms "spillWordBounds")
