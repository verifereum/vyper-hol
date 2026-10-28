(* TOP-LEVEL: source environment consistency transports allocation floors
   and local pointer lifetimes across argument evaluation. Values may
   change; each visible variable retains its checked runtime type. *)
Theory logArgumentSourceTypes
Ancestors
  sourceAllocationPrivacy sourceMemoryFrames allocationGrowth abiFieldOperands
  vyperTypeInvariants vyperValue vyperState vyperContext compileEnv
  finite_map list option

Theorem consistent_scopes_lookup_type:
  !env cx before after name entry.
    env_scopes_consistent env cx before /\ env_scopes_consistent env cx after /\
    lookup_scopes name after.scopes = SOME entry ==>
    ?old. lookup_scopes name before.scopes = SOME old /\ old.type = entry.type
Proof
  rpt gen_tac >> strip_tac >> fs[env_scopes_consistent_def] >>
  qpat_x_assum `!id entry. lookup_scopes id after.scopes = SOME entry ==> _`
    (qspecl_then [`name`, `entry`] mp_tac) >> simp[IS_SOME_EXISTS] >>
  disch_then (qx_choose_then `ty` ASSUME_TAC) >>
  qpat_x_assum `!id ty. FLOOKUP _ _ = SOME _ ==> IS_SOME (lookup_scopes id before.scopes)`
    (qspecl_then [`name`, `ty`] mp_tac) >> simp[IS_SOME_EXISTS] >>
  disch_then (qx_choose_then `old` ASSUME_TAC) >>
  qpat_x_assum `!id ty entry. _ /\ lookup_scopes id before.scopes = SOME entry ==> _`
    (qspecl_then [`name`, `ty`, `old`] mp_tac) >> simp[] >> DISCH_TAC >>
  qpat_x_assum `!id ty entry. _ /\ lookup_scopes id after.scopes = SOME entry ==> _`
    (qspecl_then [`name`, `ty`, `entry`] mp_tac) >> simp[] >> DISCH_TAC >>
  qexists_tac `old` >> fs[]
QED

Theorem source_alloca_floor_consistent_scopes:
  !env cx before after cenv ids ss.
    env_scopes_consistent env cx before /\ env_scopes_consistent env cx after /\
    source_alloca_floor cenv before.scopes ids ss ==>
    source_alloca_floor cenv after.scopes ids ss
Proof
  rpt gen_tac >> strip_tac >> simp_tac bool_ss [source_alloca_floor_def] >>
  MAP_EVERY qx_gen_tac [`name`, `entry`, `offset`, `region_size`] >> strip_tac >>
  qspecl_then [`env`, `cx`, `before`, `after`, `name`, `entry`] mp_tac consistent_scopes_lookup_type >>
  impl_tac >- (rpt conj_tac >> first_assum MATCH_ACCEPT_TAC) >>
  disch_then (qx_choose_then `old` strip_assume_tac) >>
  qpat_x_assum `source_alloca_floor _ _ _ _` (mp_tac o REWRITE_RULE [source_alloca_floor_def]) >>
  disch_then (qspecl_then [`name`, `old`, `offset`, `region_size`] mp_tac) >>
  simp[] >> strip_tac >> first_assum MATCH_ACCEPT_TAC
QED

Theorem source_alloca_floor_consistent_growth:
  !env cx before after cenv ids ss out.
    env_scopes_consistent env cx before /\ env_scopes_consistent env cx after /\
    source_alloca_floor cenv before.scopes ids ss /\ allocation_growth ss out ==>
    source_alloca_floor cenv after.scopes ids out
Proof
  rpt gen_tac >> strip_tac >>
  `source_alloca_floor cenv after.scopes ids ss` by
    (drule_all source_alloca_floor_consistent_scopes >> simp[]) >>
  drule_all source_alloca_floor_growth >> simp[]
QED

Theorem source_pointer_lifetimes_consistent_scopes:
  !env cx before after cenv bound next_var.
    env_scopes_consistent env cx before /\ env_scopes_consistent env cx after /\
    (!name entry p region_size. lookup_scopes name before.scopes = SOME entry /\
      FLOOKUP cenv.ce_vars name = SOME (PtrVar (Var p) region_size) ==> abi_operand_before bound (Var p)) /\
    bound <= next_var ==>
    !name entry p region_size. lookup_scopes name after.scopes = SOME entry /\
      FLOOKUP cenv.ce_vars name = SOME (PtrVar (Var p) region_size) ==> abi_operand_before next_var (Var p)
Proof
  rpt gen_tac >> strip_tac >> MAP_EVERY qx_gen_tac [`name`, `entry`, `p`, `region_size`] >> strip_tac >>
  qspecl_then [`env`, `cx`, `before`, `after`, `name`, `entry`] mp_tac consistent_scopes_lookup_type >>
  impl_tac >- (rpt conj_tac >> first_assum MATCH_ACCEPT_TAC) >>
  disch_then (qx_choose_then `old` strip_assume_tac) >>
  `abi_operand_before bound (Var p)` by
    (qpat_x_assum `!name entry p region_size. _` (qspecl_then [`name`, `old`, `p`, `region_size`] mp_tac) >> simp[]) >>
  irule abi_operand_before_mono >> qexists_tac `bound` >> simp[]
QED

Theorem source_memory_separated_consistent_scopes:
  !env cx es es1 cenv before after offset byte_count.
    env_scopes_consistent env cx es /\ env_scopes_consistent env cx es1 /\
    source_memory_separated cenv es.scopes before offset byte_count /\
    (!name entry p region_size. lookup_scopes name es.scopes = SOME entry /\
      FLOOKUP cenv.ce_vars name = SOME (PtrVar (Var p) region_size) ==> lookup_var p after = lookup_var p before) ==>
    source_memory_separated cenv es1.scopes after offset byte_count
Proof
  rpt gen_tac >> strip_tac >> simp_tac bool_ss [source_memory_separated_def] >> conj_tac
  >- (MAP_EVERY qx_gen_tac [`name`, `entry`, `local_offset`, `region_size`] >> strip_tac >>
      qspecl_then [`env`, `cx`, `es`, `es1`, `name`, `entry`] mp_tac consistent_scopes_lookup_type >>
      impl_tac >- (rpt conj_tac >> first_assum MATCH_ACCEPT_TAC) >>
      disch_then (qx_choose_then `old` strip_assume_tac) >>
      qpat_x_assum `source_memory_separated _ _ _ _ _`
        (mp_tac o CONJUNCT1 o REWRITE_RULE [source_memory_separated_def]) >>
      disch_then (qspecl_then [`name`, `old`, `local_offset`, `region_size`] mp_tac) >> simp[]) >>
  MAP_EVERY qx_gen_tac [`name`, `entry`, `p`, `region_size`, `ptr_addr`] >> strip_tac >>
  qspecl_then [`env`, `cx`, `es`, `es1`, `name`, `entry`] mp_tac consistent_scopes_lookup_type >>
  impl_tac >- (rpt conj_tac >> first_assum MATCH_ACCEPT_TAC) >>
  disch_then (qx_choose_then `old` strip_assume_tac) >>
  `lookup_var p after = lookup_var p before` by
    (qpat_x_assum `!name entry p region_size. _ ==> lookup_var p after = lookup_var p before`
      (qspecl_then [`name`, `old`, `p`, `region_size`] mp_tac) >> simp[]) >>
  qpat_x_assum `source_memory_separated _ _ _ _ _`
    (mp_tac o CONJUNCT2 o REWRITE_RULE [source_memory_separated_def]) >>
  disch_then (qspecl_then [`name`, `old`, `p`, `region_size`, `ptr_addr`] mp_tac) >> fs[]
QED

val () = List.app (fn (name,th) =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th)
  in if null axioms andalso null (Thm.hyp th) andalso
      List.all (fn s => s = "DISK_THM") oracles
    then () else raise Fail ("unclosed source scope type transport for Log arguments: " ^ name)
  end) (DB.thms "logArgumentSourceTypes")
