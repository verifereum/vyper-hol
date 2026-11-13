(* TOP-LEVEL: source-backed argument footprints may occupy any subwindow
   of a live local, including computed element and field pointers.
   Writes private from source locals preserve all such windows. *)
Theory logArgumentSourceWindows
Ancestors
  loweringStateRelDefs sourceMemoryFrames sourceAbiFrames abiMemoryFrame logArgumentSourceTypes vyperTypeInvariants
  compileEnv venomState vyperState list pair words arithmetic

Definition source_value_window_def:
  source_value_window cenv scopes ss offset byte_count <=>
    ?name entry region_base region_size.
      lookup_scopes name scopes = SOME entry /\
      (FLOOKUP cenv.ce_vars name = SOME (MemLoc region_base region_size) \/
       ?p ptr_addr. FLOOKUP cenv.ce_vars name = SOME (PtrVar (Var p) region_size) /\
         lookup_var p ss = SOME ptr_addr /\ region_base = w2n ptr_addr) /\
      region_base <= offset /\ offset + byte_count <= region_base + type_memory_size entry.type
End

Theorem source_value_window_memloc:
  !cenv scopes ss name entry region_base region_size offset byte_count.
    lookup_scopes name scopes = SOME entry /\
    FLOOKUP cenv.ce_vars name = SOME (MemLoc region_base region_size) /\
    region_base <= offset /\ offset + byte_count <= region_base + type_memory_size entry.type ==>
    source_value_window cenv scopes ss offset byte_count
Proof
  rpt gen_tac >> strip_tac >> simp_tac bool_ss [source_value_window_def] >>
  qexistsl_tac [`name`, `entry`, `region_base`, `region_size`] >> simp[]
QED

Theorem source_value_window_ptrvar:
  !cenv scopes ss name entry p region_size ptr_addr offset byte_count.
    lookup_scopes name scopes = SOME entry /\
    FLOOKUP cenv.ce_vars name = SOME (PtrVar (Var p) region_size) /\ lookup_var p ss = SOME ptr_addr /\
    w2n ptr_addr <= offset /\ offset + byte_count <= w2n ptr_addr + type_memory_size entry.type ==>
    source_value_window cenv scopes ss offset byte_count
Proof
  rpt gen_tac >> strip_tac >> simp_tac bool_ss [source_value_window_def] >>
  qexistsl_tac [`name`, `entry`, `w2n ptr_addr`, `region_size`] >> rpt conj_tac >>
  FIRST [first_assum MATCH_ACCEPT_TAC, disj2_tac >> qexistsl_tac [`p`, `ptr_addr`] >> simp[]]
QED

Theorem source_value_window_subwindow:
  !cenv scopes ss outer_base byte_count offset read_len.
    source_value_window cenv scopes ss outer_base byte_count /\
    outer_base <= offset /\ offset + read_len <= outer_base + byte_count ==>
    source_value_window cenv scopes ss offset read_len
Proof
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `source_value_window _ _ _ _ _`
    (mp_tac o REWRITE_RULE [source_value_window_def]) >>
  disch_then (qx_choose_then `name` (qx_choose_then `entry`
    (qx_choose_then `region_base` (qx_choose_then `region_size`
      (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC strip_assume_tac)))))) >>
  simp_tac bool_ss [source_value_window_def] >>
  qexistsl_tac [`name`, `entry`, `region_base`, `region_size`] >>
  rpt conj_tac >> FIRST [first_assum MATCH_ACCEPT_TAC, decide_tac]
QED

Theorem source_value_window_separated:
  !cenv scopes ss offset read_len dst write_len.
    source_value_window cenv scopes ss offset read_len /\
    source_memory_separated cenv scopes ss dst write_len ==>
    abi_window_separated offset read_len dst write_len
Proof
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `source_value_window _ _ _ _ _`
    (mp_tac o REWRITE_RULE [source_value_window_def]) >>
  disch_then (qx_choose_then `name` (qx_choose_then `entry`
    (qx_choose_then `region_base` (qx_choose_then `region_size` strip_assume_tac)))) >|
   [qpat_x_assum `source_memory_separated _ _ _ _ _`
      (mp_tac o CONJUNCT1 o REWRITE_RULE [source_memory_separated_def]) >>
    disch_then (qspecl_then [`name`, `entry`, `region_base`, `region_size`] mp_tac) >>
    asm_simp_tac (srw_ss()) [abi_window_separated_def, regions_disjoint_def] >> strip_tac >> decide_tac,
    qpat_x_assum `source_memory_separated _ _ _ _ _`
      (mp_tac o CONJUNCT2 o REWRITE_RULE [source_memory_separated_def]) >>
    disch_then (qspecl_then [`name`, `entry`, `p`, `region_size`, `ptr_addr`] mp_tac) >>
    asm_simp_tac (srw_ss()) [abi_window_separated_def, regions_disjoint_def] >> strip_tac >> gvs[] >> decide_tac]
QED

Theorem source_value_window_writes:
  !cenv scopes ss offset read_len writes.
    source_value_window cenv scopes ss offset read_len /\ source_writes_separated cenv scopes ss writes ==>
    EVERY (\(dst,write_len). abi_window_separated offset read_len dst write_len) writes
Proof
  rpt gen_tac >> strip_tac >> simp_tac (srw_ss()) [EVERY_MEM, FORALL_PROD] >>
  MAP_EVERY qx_gen_tac [`dst`, `write_len`] >> DISCH_TAC >>
  qpat_x_assum `source_writes_separated _ _ _ _` (mp_tac o REWRITE_RULE [source_writes_separated_def, EVERY_MEM]) >>
  disch_then (qspec_then `(dst,write_len)` mp_tac) >> simp[] >> strip_tac
  >- simp[abi_window_separated_def] >>
  drule_all source_value_window_separated >> simp[]
QED

Theorem source_value_window_consistent_frame:
  !env cx es es1 cenv before after offset byte_count.
    env_scopes_consistent env cx es /\ env_scopes_consistent env cx es1 /\
    source_value_window cenv es.scopes before offset byte_count /\
    (!name entry p region_size. lookup_scopes name es.scopes = SOME entry /\
      FLOOKUP cenv.ce_vars name = SOME (PtrVar (Var p) region_size) ==> lookup_var p after = lookup_var p before) ==>
    source_value_window cenv es1.scopes after offset byte_count
Proof
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `source_value_window _ _ _ _ _` (mp_tac o REWRITE_RULE [source_value_window_def]) >>
  disch_then (qx_choose_then `name` (qx_choose_then `entry`
    (qx_choose_then `region_base` (qx_choose_then `region_size`
      (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC strip_assume_tac)))))) >>
  qspecl_then [`env`, `cx`, `es1`, `es`, `name`, `entry`] mp_tac consistent_scopes_lookup_type >>
  impl_tac >- (rpt conj_tac >> first_assum MATCH_ACCEPT_TAC) >>
  disch_then (qx_choose_then `new` strip_assume_tac) >>
  simp_tac bool_ss [source_value_window_def] >>
  qexistsl_tac [`name`, `new`, `region_base`, `region_size`] >> asm_simp_tac bool_ss [] >>
  qpat_x_assum `FLOOKUP _ _ = SOME (MemLoc _ _) \/ _` strip_assume_tac
  >- (disj1_tac >> first_assum MATCH_ACCEPT_TAC) >>
  `lookup_var p after = lookup_var p before` by
    (qpat_x_assum `!name entry p region_size. _ ==> lookup_var p after = lookup_var p before`
      (qspecl_then [`name`, `entry`, `p`, `region_size`] mp_tac) >> simp[]) >>
  disj2_tac >> qexistsl_tac [`p`, `ptr_addr`] >> simp[]
QED
