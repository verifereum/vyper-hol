(* Suspended translations cannot overlap an allocation of the current owner. *)
Theory readonlyInvokeCopyFwdMapCopyGuards
Ancestors
  readonlyInvokeCopyFwdOperationalMapOrigins readonlyInvokeCopyFwdGlobalSupport
  occurrenceGeometry o1LowerDloadOccurrence readonlyInvokeCopyFwdRel
  readonlyInvokeCopyFwdOperationalSupport
  readonlyInvokeCopyFwdHistoryAvailability pair
  finite_map list rich_list pred_set

Theorem ricf_translation_origin_current_copy_exclusion[local]:
  occ_frame_reachable vs C stk PG G tn fn inst s n a U B HP H /\
  occurrence_natural_geometry lo a U B stk s /\
  FLOOKUP B id = SOME (db,len) /\ FST id = a /\
  ricf_translation_origin vs C ctx0 log stk' PG' G' tn' fn' inst' s' V B
    key (b,c,z) /\ (!u. MEM u V ==> MEM u U) /\ k < z ==>
  ~(db <= b+k /\ b+k < db+len) /\
  ~(db <= c+k /\ c+k < db+len)
Proof
  strip_tac >> drule ricf_translation_origin_endpoints >> strip_tac >> gvs[] >>
  drule occ_frame_reachable_owner_fresh >> simp[] >> strip_tac >>
  `MEM (EL (LENGTH pre) V) U` by metis_tac[EL_MEM] >>
  `id <> p.rpe_dst /\ id <> p.rpe_src` by
    (gvs[MEM_MAP] >> metis_tac[]) >>
  Cases_on `len = 0` >- simp[] >>
  `0 < p.rpe_size /\ 0 < len` by decide_tac >>
  `db+len <= p.rpe_db \/ p.rpe_db+p.rpe_size <= db` by
    metis_tac[occurrence_geometry_sites_disjoint] >>
  `db+len <= p.rpe_sb \/ p.rpe_sb+p.rpe_size <= db` by
    metis_tac[occurrence_geometry_sites_disjoint] >>
  decide_tac
QED

Theorem ricf_map_origins_current_copy_exclusion:
  occ_frame_reachable vs C stk PG G tn fn inst s n a U B HP H /\
  occurrence_natural_geometry lo a U B stk s /\
  FLOOKUP B id = SOME (db,len) /\ FST id = a /\
  ricf_map_origins vs C ctx0 log stk PG G tn fn inst s U B sites ==>
  !b c z k. (b,c,z) IN ricf_site_triples sites /\ k < z ==>
    ~(db <= b+k /\ b+k < db+len) /\
    ~(db <= c+k /\ c+k < db+len)
Proof
  rw[ricf_site_triples_def] >>
  fs[ricf_map_origins_def] >>
  metis_tac[ricf_translation_origin_current_copy_exclusion]
QED

Theorem ricf_saved_map_origins_current_copy_exclusion:
  occ_frame_reachable vs C stk PG G tn fn inst s n a U B HP H /\
  occurrence_natural_geometry lo a U B stk s /\
  FLOOKUP B id = SOME (db,len) /\ FST id = a /\
  ricf_saved_map_origins vs C ctx0 log stk U B maps ==>
  !j b c z k. j < LENGTH stk /\
    (b,c,z) IN ricf_site_triples (EL j maps) /\ k < z ==>
    ~(db <= b+k /\ b+k < db+len) /\
    ~(db <= c+k /\ c+k < db+len)
Proof
  rw[ricf_site_triples_def] >>
  drule_all ricf_saved_map_origins_lookup >> strip_tac >>
  metis_tac[ricf_translation_origin_current_copy_exclusion, MEM_DROP_IMP]
QED

(* Availability chooses the actual current destination occurrence; map guards
   then follow from ownership, without any assumed endpoint inequalities. *)
Theorem ricf_located_copy_map_exclusion:
  EVERY wf_ssa C.ctx_functions /\ EVERY wf_function C.ctx_functions /\
  EVERY fn_inst_wf C.ctx_functions /\ vs.vs_allocas = FEMPTY /\
  ~ctx_has_dalloca C /\ ricf_full_alloca_copies fn /\ ricf_src_alloca fn /\
  ALL_DISTINCT (MAP (\inst. inst.inst_id) (fn_insts fn)) /\
  ricf_located_event ctx0 fn log round b es prefix e current /\
  occ_frame_reachable vs C stk PG G tn fn
    (ricf_event_copy e (EL b fn.fn_blocks)) s n a U B HP H /\
  lookup_block s.vs_current_bb fn.fn_blocks = SOME (EL b fn.fn_blocks) /\
  s.vs_inst_idx = e.rfe_index /\
  occurrence_natural_geometry lo a U B stk s /\
  ricf_map_origins vs C ctx0 log stk PG G tn fn
    (ricf_event_copy e (EL b fn.fn_blocks)) s U B sites /\
  ricf_saved_map_origins vs C ctx0 log stk U B maps ==>
  ?dst sv z da db sb.
    (ricf_event_copy e (EL b fn.fn_blocks)).inst_operands =
      [Var dst;Var sv;Lit z] /\
    eval_operands (ricf_event_copy e (EL b fn.fn_blocks)).inst_operands s =
      SOME [n2w db;n2w sb;z] /\
    MEM da (fn_insts fn) /\ da.inst_opcode = ALLOCA /\
    FLOOKUP B (a,da.inst_id) = SOME (db,w2n z) /\
    (!x y w k. (x,y,w) IN ricf_site_triples sites /\ k < w ==>
      ~(db <= x+k /\ x+k < db+w2n z) /\
      ~(db <= y+k /\ y+k < db+w2n z)) /\
    (!j x y w k. j < LENGTH stk /\
      (x,y,w) IN ricf_site_triples (EL j maps) /\ k < w ==>
      ~(db <= x+k /\ x+k < db+w2n z) /\
      ~(db <= y+k /\ y+k < db+w2n z))
Proof
  strip_tac >> drule_all ricf_located_event_operands_available >> strip_tac >>
  qexistsl_tac [`dst`, `sv`, `z`, `da`, `db`, `sb`] >>
  asm_rewrite_tac [] >>
  `FST (a,da.inst_id) = a` by simp[] >>
  conj_tac
  >- metis_tac[ricf_map_origins_current_copy_exclusion] >>
  metis_tac[ricf_saved_map_origins_current_copy_exclusion]
QED
