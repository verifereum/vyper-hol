(* TOP-LEVEL: future writer identities belong to the reserved profile and
   their actual instructions do not define live source pointers. This is
   compiler provenance, independent of the next expression's semantics. *)
Theory logArgumentWriters
Ancestors
  logArgumentSourceTypes sourceAllocationPrivacy sourceMemorySeparation sourceMemoryFrames
  compileAllocaProvenance compileAllocaFlow compileEnv fragExec
  allocationGrowth localPtrsProps venomInst venomMemDefs venomState list
  abiStaticLoopCode

Definition log_argument_writers_def:
  log_argument_writers func cenv scopes ids writers <=>
    !id. MEM id writers ==> MEM id ids /\
      ?inst q. MEM inst (fn_insts func) /\ inst.inst_id = id /\ inst.inst_outputs = [q] /\
        not_local_ptr cenv scopes q
End

Theorem not_local_ptr_consistent_scopes:
  !env cx es es1 cenv q.
    env_scopes_consistent env cx es /\ env_scopes_consistent env cx es1 /\
    not_local_ptr cenv es.scopes q ==> not_local_ptr cenv es1.scopes q
Proof
  rpt gen_tac >> strip_tac >> simp_tac bool_ss [not_local_ptr_def] >>
  MAP_EVERY qx_gen_tac [`name`, `entry`, `region_size`] >> DISCH_TAC >>
  qspecl_then [`env`, `cx`, `es`, `es1`, `name`, `entry`] mp_tac consistent_scopes_lookup_type >>
  impl_tac >- (rpt conj_tac >> first_assum MATCH_ACCEPT_TAC) >>
  disch_then (qx_choose_then `old` strip_assume_tac) >>
  qpat_x_assum `not_local_ptr _ _ _` (mp_tac o REWRITE_RULE [not_local_ptr_def]) >>
  disch_then (qspecl_then [`name`, `old`, `region_size`] mp_tac) >> simp[]
QED

Theorem log_argument_writers_transport:
  !env cx es es1 func cenv ids writers next_writers.
    env_scopes_consistent env cx es /\ env_scopes_consistent env cx es1 /\
    log_argument_writers func cenv es.scopes ids writers /\
    (!id. MEM id next_writers ==> MEM id writers) ==>
    log_argument_writers func cenv es1.scopes ids next_writers
Proof
  rpt gen_tac >> strip_tac >> simp_tac bool_ss [log_argument_writers_def] >>
  qx_gen_tac `id` >> DISCH_TAC >> `MEM id writers` by
    (qpat_x_assum `!id. MEM id next_writers ==> _` irule >> first_assum MATCH_ACCEPT_TAC) >>
  qpat_x_assum `log_argument_writers _ _ _ _ _` (mp_tac o REWRITE_RULE [log_argument_writers_def]) >>
  disch_then (qspec_then `id` mp_tac) >>
  impl_tac >- first_assum MATCH_ACCEPT_TAC >>
  disch_then (CONJUNCTS_THEN2 ASSUME_TAC
    (qx_choose_then `inst` (qx_choose_then `q` strip_assume_tac))) >>
  `not_local_ptr cenv es1.scopes q` by (drule_all not_local_ptr_consistent_scopes >> simp[]) >>
  conj_tac >- first_assum MATCH_ACCEPT_TAC >> qexistsl_tac [`inst`, `q`] >> simp[]
QED

Theorem log_argument_writers_private:
  !func cenv scopes ids writers before after.
    log_argument_writers func cenv scopes ids writers /\ source_alloca_floor cenv scopes ids before /\
    allocation_growth before after /\ alloca_inv after /\ fn_inst_ids_distinct func /\
    local_ptrs_rel func cenv scopes before ==>
    source_writes_separated cenv scopes before (abi_allocation_windows writers after)
Proof
  rpt gen_tac >> strip_tac >>
  `!id. MEM id writers ==> MEM id ids` by
    (fs[log_argument_writers_def] >> rpt strip_tac >> first_x_assum drule >> simp[]) >>
  `source_alloca_floor cenv scopes writers before` by
    (qspecl_then [`cenv`, `scopes`, `writers`, `ids`, `before`] mp_tac source_alloca_floor_subprofile >>
     impl_tac >- (rpt conj_tac >> first_assum MATCH_ACCEPT_TAC) >> simp[]) >>
  qspecl_then [`func`, `cenv`, `scopes`, `writers`, `before`, `after`] mp_tac source_profile_writes_private >>
  impl_tac >- (rpt conj_tac >> FIRST [first_assum MATCH_ACCEPT_TAC,
    qpat_x_assum `log_argument_writers _ _ _ _ _` (mp_tac o REWRITE_RULE [log_argument_writers_def]) >>
    simp_tac bool_ss [] >> metis_tac[]]) >> simp[]
QED

Theorem log_argument_writers_code:
  !action cs value final_cut func cenv scopes ids.
    (!P. compiler_alloca_pred P action) /\ action cs = (value,final_cut) /\
    cs_extends cs final_cut /\ fn_has_code cs final_cut func /\
    (!id. MEM id (compiler_alloca_ids cs final_cut) ==> MEM id ids) /\
    (!name entry p region_size. lookup_scopes name scopes = SOME entry /\
      FLOOKUP cenv.ce_vars name = SOME (PtrVar (Var p) region_size) ==> abi_operand_before cs.cs_next_var (Var p)) ==>
    log_argument_writers func cenv scopes ids (compiler_alloca_ids cs final_cut)
Proof
  rpt gen_tac >> strip_tac >> simp_tac bool_ss [log_argument_writers_def] >> qx_gen_tac `id` >> DISCH_TAC >>
  `MEM id ids` by (qpat_x_assum `!id. MEM id _ ==> MEM id ids` irule >> first_assum MATCH_ACCEPT_TAC) >>
  qpat_x_assum `MEM id (compiler_alloca_ids _ _)` (mp_tac o REWRITE_RULE [compiler_alloca_ids_member]) >>
  disch_then (qx_choose_then `inst` strip_assume_tac) >>
  `MEM inst (fn_insts func)` by
    (qspecl_then [`cs`, `final_cut`, `func`, `inst`] mp_tac compiler_new_instruction_member >> simp[]) >>
  qspecl_then [`action`, `cs`, `value`, `final_cut`, `inst`] mp_tac compiler_alloca_fresh_output >>
  impl_tac >- (rpt conj_tac >> first_assum MATCH_ACCEPT_TAC) >>
  disch_then (qx_choose_then `n` strip_assume_tac) >>
  `not_local_ptr cenv scopes (compiler_var_name n 0)` by
    (qspecl_then [`cenv`, `scopes`, `cs.cs_next_var`, `n`] mp_tac source_pointer_operands_not_local >>
     impl_tac >- (rpt conj_tac >> first_assum MATCH_ACCEPT_TAC) >> simp[]) >>
  conj_tac >- first_assum MATCH_ACCEPT_TAC >>
  qexistsl_tac [`inst`, `compiler_var_name n 0`] >> simp[compiler_var_name_def]
QED

val () = List.app (fn (name,th) =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th)
  in if null axioms andalso null (Thm.hyp th) andalso
      List.all (fn s => s = "DISK_THM") oracles
    then () else raise Fail ("unclosed static Log argument writer provenance: " ^ name)
  end) (DB.thms "logArgumentWriters")
