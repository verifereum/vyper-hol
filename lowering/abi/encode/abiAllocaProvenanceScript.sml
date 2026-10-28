(* TOP-LEVEL: every new allocation in arbitrary recursive ABI code has a
   generated output and belongs to the containing function. Live source
   pointers precede these outputs, so the actual compiler allocation-ID
   profile supplies writer privacy without a caller-provided instruction table. *)
Theory abiAllocaProvenance
Ancestors
  abiAllocaFlow compileAllocaFlow compileAllocaProvenance abiEncoderStructure
  sourceMemorySeparation abiStaticLoopCode abiFieldOperands
  compileEnv fragExec localPtrsProps venomState venomInst list arithmetic

Theorem compile_abi_encode_alloca_provenance:
  !dst src info cs op cs' func inst.
    compile_abi_encode_to_buf dst src info cs = (op,cs') /\ fn_has_code cs cs' func /\
    compiler_instruction_member cs' inst /\ ~compiler_instruction_member cs inst /\ inst.inst_opcode = ALLOCA ==>
    MEM inst (fn_insts func) /\
    ?n. cs.cs_next_var <= n /\ inst.inst_outputs = [compiler_var_name n 0]
Proof
  rpt gen_tac >> strip_tac >>
  `!P. compiler_alloca_pred P (compile_abi_encode_to_buf dst src info)` by
    (qx_gen_tac `P` >> MATCH_ACCEPT_TAC
      (Q.SPECL [`dst`, `src`, `info`] (cj 2 (Q.SPEC `P` compiler_alloca_pred_abi_encode)))) >>
  drule_all compiler_alloca_fresh_output >> disch_then (qx_choose_then `n` strip_assume_tac) >>
  `cs_extends cs cs'` by (drule_all compile_abi_encode_extends >> simp[]) >>
  `MEM inst (fn_insts func)` by (drule_all compiler_new_instruction_member >> simp[]) >>
  conj_tac >- first_assum MATCH_ACCEPT_TAC >> qexists_tac `n` >> simp[compiler_var_name_def]
QED

Theorem compile_abi_child_alloca_provenance:
  !dst src info is_dyn head_offset dyn_ptr cs op cs' func inst.
    compile_abi_encode_child dst src info is_dyn head_offset dyn_ptr cs = (op,cs') /\ fn_has_code cs cs' func /\
    compiler_instruction_member cs' inst /\ ~compiler_instruction_member cs inst /\ inst.inst_opcode = ALLOCA ==>
    MEM inst (fn_insts func) /\
    ?n. cs.cs_next_var <= n /\ inst.inst_outputs = [compiler_var_name n 0]
Proof
  rpt gen_tac >> strip_tac >>
  `!P. compiler_alloca_pred P (compile_abi_encode_child dst src info is_dyn head_offset dyn_ptr)` by
    (qx_gen_tac `P` >> MATCH_ACCEPT_TAC
      (Q.SPECL [`dst`, `src`, `info`, `is_dyn`, `head_offset`, `dyn_ptr`]
        (cj 1 (Q.SPEC `P` compiler_alloca_pred_abi_encode)))) >>
  drule_all compiler_alloca_fresh_output >> disch_then (qx_choose_then `n` strip_assume_tac) >>
  `cs_extends cs cs'` by
    (mp_tac (Q.SPECL [`dst`, `src`, `info`, `is_dyn`, `head_offset`, `dyn_ptr`] (cj 1 cs_appends_compile_abi_encode)) >>
     simp_tac bool_ss [cs_appends_def] >> disch_then (qspecl_then [`cs`, `op`, `cs'`] mp_tac) >> simp[]) >>
  `MEM inst (fn_insts func)` by (drule_all compiler_new_instruction_member >> simp[]) >>
  conj_tac >- first_assum MATCH_ACCEPT_TAC >> qexists_tac `n` >> simp[compiler_var_name_def]
QED

Theorem compile_abi_encode_alloca_private:
  !dst src info cs op cs' func inst cenv scopes.
    compile_abi_encode_to_buf dst src info cs = (op,cs') /\ fn_has_code cs cs' func /\
    compiler_instruction_member cs' inst /\ ~compiler_instruction_member cs inst /\ inst.inst_opcode = ALLOCA /\
    (!name entry p capacity. lookup_scopes name scopes = SOME entry /\
      FLOOKUP cenv.ce_vars name = SOME (PtrVar (Var p) capacity) ==> abi_operand_before cs.cs_next_var (Var p)) ==>
    MEM inst (fn_insts func) /\ ?q. inst.inst_outputs = [q] /\ not_local_ptr cenv scopes q
Proof
  rpt gen_tac >> strip_tac >> drule_all compile_abi_encode_alloca_provenance >>
  disch_then (CONJUNCTS_THEN2 ASSUME_TAC (qx_choose_then `n` strip_assume_tac)) >>
  `not_local_ptr cenv scopes (compiler_var_name n 0)` by
    (mp_tac (Q.SPECL [`cenv`, `scopes`, `cs.cs_next_var`, `n`] source_pointer_operands_not_local) >>
     impl_tac >- (rpt conj_tac >> first_assum MATCH_ACCEPT_TAC) >> simp[]) >>
  conj_tac >- first_assum MATCH_ACCEPT_TAC >> qexists_tac `compiler_var_name n 0` >> simp[]
QED

Theorem compile_abi_encode_writer_instructions:
  !dst src info cs op cs' func cenv scopes.
    compile_abi_encode_to_buf dst src info cs = (op,cs') /\ fn_has_code cs cs' func /\
    (!name entry p capacity. lookup_scopes name scopes = SOME entry /\
      FLOOKUP cenv.ce_vars name = SOME (PtrVar (Var p) capacity) ==> abi_operand_before cs.cs_next_var (Var p)) ==>
    !id. MEM id (compiler_alloca_ids cs cs') ==> ?inst q.
      MEM inst (fn_insts func) /\ inst.inst_id = id /\ inst.inst_outputs = [q] /\ not_local_ptr cenv scopes q
Proof
  rpt gen_tac >> strip_tac >> qx_gen_tac `id` >> DISCH_TAC >>
  qpat_x_assum `MEM id (compiler_alloca_ids cs cs')`
    (mp_tac o REWRITE_RULE [compiler_alloca_ids_member]) >>
  disch_then (qx_choose_then `inst` strip_assume_tac) >>
  drule_all compile_abi_encode_alloca_private >>
  disch_then (CONJUNCTS_THEN2 ASSUME_TAC (qx_choose_then `q` strip_assume_tac)) >>
  qexistsl_tac [`inst`, `q`] >> simp[]
QED

val () = List.app (fn (name,th) =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th)
  in if null axioms andalso null (Thm.hyp th) andalso
      List.all (fn s => s = "DISK_THM") oracles
    then () else raise Fail ("unclosed recursive ABI writer ownership: " ^ name)
  end) (DB.thms "abiAllocaProvenance")
