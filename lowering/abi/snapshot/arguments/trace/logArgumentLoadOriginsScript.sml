(* TOP-LEVEL: transport the saved prefix through expression execution.
   Values follow from write geometry, including fresh callee scratch;
   origins, local lifetimes and the source allocation floor follow from
   scope consistency, allocation growth and preserved old operands. *)
Theory logArgumentLoadOrigins
Ancestors
  logArgumentFreshFrame logArgumentOrigins logArgumentSourceTypes logArgumentBackingFrames
  logArgumentLoadFrame
  sourceAllocationPrivacy sourceMemoryFrames abiAllocationWindows abiMemoryFrame
  allocationGrowth typedLogArgs abiFieldOperands compileEnv vyperTypeInvariants
  venomMemDefs venomState list pair words

Theorem log_argument_load_origins_state:
  !env cx es es1 cenv func ids args tvs values before after writers next_writers
    source_ok next_source bound next_var semantic_writes.
    env_scopes_consistent env cx es /\ env_scopes_consistent env cx es1 /\
    local_ptrs_rel func cenv es.scopes before /\ source_alloca_floor cenv es.scopes ids before /\
    (!name entry p region_size. lookup_scopes name es.scopes = SOME entry /\
      FLOOKUP cenv.ce_vars name = SOME (PtrVar (Var p) region_size) ==> abi_operand_before bound (Var p)) /\
    alloca_inv before /\ allocas_non_overlapping after /\ allocation_growth before after /\ bound <= next_var /\
    (!id. MEM id next_writers ==> MEM id writers) /\ (source_ok ==> next_source) /\
    (!arg_op. abi_operand_before bound arg_op ==> eval_operand arg_op after = eval_operand arg_op before) /\
    log_args_rel args tvs values before /\ EVERY (\arg. abi_operand_before bound (FST arg)) args /\
    log_args_origins cenv es.scopes before writers source_ok args tvs /\
    source_writes_contained cenv es.scopes before semantic_writes /\ (source_ok ==> semantic_writes = []) /\
    source_writes_separated cenv es.scopes before (abi_allocation_windows writers after) /\
    abi_memory_frame (semantic_writes ++ abi_allocation_windows writers after ++
      [(before.vs_alloca_next,after.vs_alloca_next - before.vs_alloca_next)]) before after ==>
    log_args_rel args tvs values after /\
    log_args_origins cenv es1.scopes after next_writers next_source args tvs /\
    source_alloca_floor cenv es1.scopes ids after /\
    (!name entry p region_size. lookup_scopes name es1.scopes = SOME entry /\
      FLOOKUP cenv.ce_vars name = SOME (PtrVar (Var p) region_size) ==> abi_operand_before next_var (Var p)) /\
    EVERY (\arg. abi_operand_before next_var (FST arg)) args
Proof
  rpt gen_tac >> disch_then (REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) >>
  `EVERY (\arg. eval_operand (FST arg) after = eval_operand (FST arg) before) args` by
    (simp_tac bool_ss [EVERY_MEM] >> qx_gen_tac `arg` >> DISCH_TAC >>
     qpat_x_assum `!arg_op. _` irule >> fs[EVERY_MEM]) >>
  `source_memory_separated cenv es.scopes before before.vs_alloca_next
    (after.vs_alloca_next - before.vs_alloca_next)` by
    (qspecl_then [`func`, `cenv`, `es.scopes`, `ids`, `before`, `before.vs_alloca_next`,
       `after.vs_alloca_next - before.vs_alloca_next`] mp_tac source_floor_fresh_window >> simp[]) >>
  `log_args_rel args tvs values after` by
    (qspecl_then [`args`, `tvs`, `values`, `cenv`, `es.scopes`, `before`, `after`, `writers`, `source_ok`, `semantic_writes`]
      mp_tac log_args_origins_fresh_execution_frame >> simp[]) >>
  `!name entry p region_size. lookup_scopes name es.scopes = SOME entry /\
    FLOOKUP cenv.ce_vars name = SOME (PtrVar (Var p) region_size) ==> lookup_var p after = lookup_var p before` by
    (MAP_EVERY qx_gen_tac [`name`, `entry`, `p`, `region_size`] >> strip_tac >>
     `abi_operand_before bound (Var p)` by
       (qpat_x_assum `!name entry p region_size. _ ==> abi_operand_before _ _`
         (qspecl_then [`name`, `entry`, `p`, `region_size`] mp_tac) >> simp[]) >>
     qpat_x_assum `!arg_op. _` (qspec_then `Var p` mp_tac) >> simp[eval_operand_def]) >>
  `log_args_origins cenv es1.scopes after next_writers next_source args tvs` by
    (qspecl_then [`args`, `tvs`, `env`, `cx`, `es`, `es1`, `cenv`, `before`, `after`, `writers`, `next_writers`,
       `source_ok`, `next_source`] mp_tac log_args_origins_consistent_growth >>
     impl_tac >- (rpt conj_tac >> first_assum MATCH_ACCEPT_TAC) >> simp[]) >>
  `source_alloca_floor cenv es1.scopes ids after` by
    (qspecl_then [`env`, `cx`, `es`, `es1`, `cenv`, `ids`, `before`, `after`]
      mp_tac source_alloca_floor_consistent_growth >>
     impl_tac >- (rpt conj_tac >> first_assum MATCH_ACCEPT_TAC) >> simp[]) >>
  `!name entry p region_size. lookup_scopes name es1.scopes = SOME entry /\
    FLOOKUP cenv.ce_vars name = SOME (PtrVar (Var p) region_size) ==> abi_operand_before next_var (Var p)` by
    (qspecl_then [`env`, `cx`, `es`, `es1`, `cenv`, `bound`, `next_var`]
      mp_tac source_pointer_lifetimes_consistent_scopes >>
     impl_tac >- (rpt conj_tac >> first_assum MATCH_ACCEPT_TAC) >> simp[]) >>
  `EVERY (\arg. abi_operand_before next_var (FST arg)) args` by
    (qspecl_then [`args`, `bound`, `next_var`] mp_tac log_args_before_mono >> simp[]) >>
  rpt conj_tac >> first_assum MATCH_ACCEPT_TAC
QED

val () = List.app (fn (name,th) =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th)
  in if null axioms andalso null (Thm.hyp th) andalso
      List.all (fn s => s = "DISK_THM") oracles
    then () else raise Fail ("unclosed expression frame for Log argument origins: " ^ name)
  end) (DB.thms "logArgumentLoadOrigins")
