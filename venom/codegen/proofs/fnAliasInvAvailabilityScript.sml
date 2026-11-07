Theory fnAliasInvAvailability
Ancestors
  fnAliasInvLiveness venomWf rich_list list livenessDefs finite_map
  pair indexedLists passSharedDefs o1ContractSimplifyCfg cfgNormBase
  venomExecProps cfgAnalysisProps cfgHelpers cfgNormSupplySim
Libs
  venomInstTheory

(* All entry paths have encountered a definition, counting only the strict
   instruction prefix in the final block. Unreachable labels are vacuous. *)
Definition alias_path_available_def:
  alias_path_available fn l i v <=>
    !path. is_fn_path fn path /\ path <> [] /\
      (?entry. fn_entry_label fn = SOME entry /\ HD path = entry) /\
      LAST path = l ==>
      (?k bb inst. k < LENGTH path - 1 /\
        lookup_block (EL k path) fn.fn_blocks = SOME bb /\
        MEM inst bb.bb_instructions /\ MEM v (inst_defs inst)) \/
      (?bb j. lookup_block l fn.fn_blocks = SOME bb /\
        j < i /\ j < LENGTH bb.bb_instructions /\
        MEM v (inst_defs (EL j bb.bb_instructions)))
End

Definition alias_pending_phi_def:
  alias_pending_phi fn l i v <=>
    ?bb inst. lookup_block l fn.fn_blocks = SOME bb /\
      MEM inst (DROP i (collect_phis bb.bb_instructions)) /\
      MEM v (inst_uses inst)
End

Theorem alias_pending_phi_past_prefix:
  LENGTH (collect_phis bb.bb_instructions) <= i /\
  lookup_block l fn.fn_blocks = SOME bb ==>
  ~alias_pending_phi fn l i v
Proof
  strip_tac >>
  `DROP i (collect_phis bb.bb_instructions) = []` by
    (simp[GSYM LENGTH_NIL, LENGTH_DROP]) >>
  simp[alias_pending_phi_def]
QED

Definition alias_phi_loop_fn_def:
  alias_phi_loop_fn = mk_raw_function "phi_loop"
    [<| bb_label := "entry"; bb_instructions :=
       [mk_inst 0 PARAM [] ["seed"];
        mk_inst 1 JMP [Label "header"] []] |>;
     <| bb_label := "header"; bb_instructions :=
       [mk_inst 2 PHI [Label "entry"; Var "seed";
                       Label "body"; Var "next"] ["p"];
        mk_inst 3 ISZERO [Var "p"] ["z"];
        mk_inst 4 JMP [Label "body"] []] |>;
     <| bb_label := "body"; bb_instructions :=
       [mk_inst 5 ADD [Var "p"; Lit 1w] ["next"];
        mk_inst 6 JMP [Label "header"] []] |>]
End

Theorem alias_phi_loop_liveness:
  MEM "next" (live_vars_at (liveness_analyze alias_phi_loop_fn) "header" 0) /\
  MEM "seed" (input_vars_from "entry"
    (EL 1 alias_phi_loop_fn.fn_blocks).bb_instructions
    (live_vars_at (liveness_analyze alias_phi_loop_fn) "header" 0)) /\
  ~MEM "next" (input_vars_from "entry"
    (EL 1 alias_phi_loop_fn.fn_blocks).bb_instructions
    (live_vars_at (liveness_analyze alias_phi_loop_fn) "header" 0)) /\
  alias_pending_phi alias_phi_loop_fn "header" 0 "next" /\
  (!v. ~alias_pending_phi alias_phi_loop_fn "header" 1 v)
Proof
  EVAL_TAC >> simp[livenessDefsTheory.collect_phis_def] >> EVAL_TAC
QED

Theorem alias_phi_loop_not_available:
  ~alias_path_available alias_phi_loop_fn "header" 0 "next"
Proof
  simp[alias_path_available_def] >>
  qexists_tac `["entry"; "header"]` >>
  EVAL_TAC >> simp[SF DNF_ss] >> EVAL_TAC >>
  rpt strip_tac >> CCONTR_TAC >> gvs[]
QED

(* Generic accumulator form retains the map-absence fact lost by the
   existing input_vars_from_phi_correct_proof boundary. *)
Theorem alias_input_fold_partition:
  !base acc placed op_map matching v.
    MEM v (FST (FOLDL (\(acc, placed) w.
      case FLOOKUP op_map w of
        NONE => (acc ++ [w], placed)
      | SOME phi_idx =>
          if MEM phi_idx placed then (acc, placed)
          else case FLOOKUP matching phi_idx of
                 SOME src_v => (acc ++ [src_v], phi_idx::placed)
               | NONE => (acc, placed))
      (acc, placed) base)) ==>
    MEM v acc \/ (MEM v base /\ FLOOKUP op_map v = NONE) \/
    ?i. FLOOKUP matching i = SOME v
Proof
  Induct >> simp[] >> rpt gen_tac >>
  Cases_on `FLOOKUP op_map h` >> simp[]
  >- (strip_tac >> first_x_assum drule >> strip_tac >>
      gvs[MEM_APPEND] >> metis_tac[]) >>
  rename1 `FLOOKUP op_map h = SOME phi_idx` >>
  Cases_on `MEM phi_idx placed` >> simp[]
  >- (strip_tac >> first_x_assum drule >> metis_tac[]) >>
  Cases_on `FLOOKUP matching phi_idx` >> simp[]
  >- (strip_tac >> first_x_assum drule >> metis_tac[]) >>
  strip_tac >> first_x_assum drule >> strip_tac >>
  gvs[MEM_APPEND] >> metis_tac[]
QED

Theorem alias_phi_matching_fold_origin:
  !indexed op_map matching src i v.
    FLOOKUP (SND (FOLDL
      (\(op_map,matching) (j,phi).
        (FOLDL (\m (l,w). m |+ (w,j)) op_map (phi_pairs phi.inst_operands),
         case FIND (\(l,w). l = src) (phi_pairs phi.inst_operands) of
           NONE => matching | SOME (_,w) => matching |+ (j,w)))
      (op_map,matching) indexed)) i = SOME v ==>
    FLOOKUP matching i = SOME v \/
    ?j phi. MEM (j,phi) indexed /\ MEM (src,v) (phi_pairs phi.inst_operands)
Proof
  Induct >> simp[] >> rpt gen_tac >> PairCases_on `h` >> simp[] >>
  strip_tac >> first_x_assum drule >> strip_tac
  >- (Cases_on `FIND (\(l,w). l = src) (phi_pairs h1.inst_operands)` >>
      gvs[] >> PairCases_on `x` >> gvs[FLOOKUP_UPDATE] >>
      Cases_on `h0 = i` >> gvs[] >>
      disj2_tac >> qexistsl_tac [`h0`,`h1`] >> simp[] >>
      qpat_x_assum `FIND _ _ = SOME _` mp_tac >>
      qid_spec_tac `x0` >> qid_spec_tac `v` >>
      SPEC_TAC (``phi_pairs h1.inst_operands``, ``pairs : (string # string) list``) >>
      Induct >> simp[FIND_thm] >> rpt gen_tac >> PairCases_on `h` >>
      simp[] >> IF_CASES_TAC >> gvs[]) >>
  metis_tac[]
QED

Theorem alias_build_phi_maps_matching_origin:
  FLOOKUP (SND (build_phi_maps src phis)) i = SOME v ==>
  ?phi. MEM phi phis /\ MEM (src,v) (phi_pairs phi.inst_operands)
Proof
  simp[build_phi_maps_def] >>
  strip_tac >> drule alias_phi_matching_fold_origin >>
  simp[MEM_MAPi] >> metis_tac[MEM_EL]
QED

Theorem alias_input_vars_from_partition:
  MEM v (input_vars_from pred instrs live) ==>
  (MEM v live /\
   FLOOKUP (FST (build_phi_maps pred (collect_phis instrs))) v = NONE) \/
  ?phi. MEM phi (collect_phis instrs) /\
    MEM (pred,v) (phi_pairs phi.inst_operands)
Proof
  simp[input_vars_from_def] >>
  Cases_on `NULL (collect_phis instrs)`
  >- (gvs[NULL_EQ, build_phi_maps_def]) >>
  Cases_on `build_phi_maps pred (collect_phis instrs)` >>
  simp[] >> simp[Once UNCURRY] >> strip_tac >>
  drule alias_input_fold_partition >> simp[] >> strip_tac >> gvs[] >>
  disj2_tac >> irule alias_build_phi_maps_matching_origin >>
  qexists_tac `i` >> simp[]
QED

Theorem alias_phi_operand_fold_absent:
  !pairs m j v.
    FLOOKUP (FOLDL (\m (l,w). m |+ (w,j)) m pairs) v = NONE <=>
    FLOOKUP m v = NONE /\ !l. ~MEM (l,v) pairs
Proof
  Induct >> simp[] >> rpt gen_tac >> PairCases_on `h` >>
  simp[FLOOKUP_UPDATE] >> Cases_on `h1 = v` >> simp[] >> metis_tac[]
QED

Theorem alias_phi_maps_fold_absent:
  !indexed op_map matching src v.
    FLOOKUP (FST (FOLDL
      (\(op_map,matching) (j,phi).
        (FOLDL (\m (l,w). m |+ (w,j)) op_map (phi_pairs phi.inst_operands),
         case FIND (\(l,w). l = src) (phi_pairs phi.inst_operands) of
           NONE => matching | SOME (_,w) => matching |+ (j,w)))
      (op_map,matching) indexed)) v = NONE <=>
    FLOOKUP op_map v = NONE /\
    !j phi l. MEM (j,phi) indexed ==> ~MEM (l,v) (phi_pairs phi.inst_operands)
Proof
  Induct >> simp[] >> rpt gen_tac >> PairCases_on `h` >> simp[] >>
  Cases_on `FIND (\(l,w). l = src) (phi_pairs h1.inst_operands)`
  >- (gvs[alias_phi_operand_fold_absent] >> metis_tac[]) >>
  PairCases_on `x` >> gvs[alias_phi_operand_fold_absent] >> metis_tac[]
QED

Theorem alias_build_phi_maps_absent:
  FLOOKUP (FST (build_phi_maps src phis)) v = NONE <=>
  !phi l. MEM phi phis ==> ~MEM (l,v) (phi_pairs phi.inst_operands)
Proof
  simp[build_phi_maps_def, alias_phi_maps_fold_absent, MEM_MAPi] >>
  metis_tac[MEM_EL]
QED

Theorem alias_build_phi_maps_absent_uses:
  FLOOKUP (FST (build_phi_maps src phis)) v = NONE /\
  (!phi. MEM phi phis ==> phi_well_formed phi.inst_operands) ==>
  !phi. MEM phi phis ==> ~MEM v (inst_uses phi)
Proof
  simp[alias_build_phi_maps_absent, inst_uses_def] >> rpt strip_tac >>
  `MEM (Var v) phi.inst_operands` by gvs[MEM_operand_vars_eq_Var] >>
  `phi_well_formed phi.inst_operands` by metis_tac[] >>
  drule_all phi_well_formed_var_pair >> metis_tac[]
QED

(* The corresponding local livenessTransferProofs adapter is not exported. *)
Theorem alias_phi_pairs_subset_uses:
  !ops v. MEM v (MAP SND (phi_pairs ops)) ==>
    MEM v (venomInst$operand_vars ops)
Proof
  ho_match_mp_tac phi_pairs_ind >>
  simp[phi_pairs_def, venomInstTheory.operand_vars_def,
       venomInstTheory.operand_var_def] >>
  rpt strip_tac >>
  gvs[venomInstTheory.operand_vars_def, venomInstTheory.operand_var_def] >>
  Cases_on `venomInst$operand_var v1` >> gvs[]
QED

Theorem alias_input_vars_ordinary_intro:
  MEM v live /\
  (!phi. MEM phi (collect_phis instrs) ==> ~MEM v (inst_uses phi)) ==>
  MEM v (input_vars_from pred instrs live)
Proof
  strip_tac >>
  `FLOOKUP (FST (build_phi_maps pred (collect_phis instrs))) v = NONE` by
    (simp[alias_build_phi_maps_absent] >> rpt strip_tac >>
     `MEM v (venomInst$operand_vars phi.inst_operands)` by
       (irule alias_phi_pairs_subset_uses >> simp[MEM_MAP] >>
        qexists_tac `(l,v)` >> simp[]) >>
     gvs[inst_uses_def] >> metis_tac[]) >>
  simp[input_vars_from_def] >>
  Cases_on `NULL (collect_phis instrs)` >- simp[] >>
  Cases_on `build_phi_maps pred (collect_phis instrs)` >> gvs[] >>
  simp[Once UNCURRY] >>
  irule livenessTransferProofsTheory.foldl_passthrough >> simp[]
QED

(* Representation adapter only: dominance-to-all-paths is imported from
   o1ContractSimplifyCfg, rather than reproved in this leaf. *)
Theorem alias_all_paths_indexed:
  lookup_block bb.bb_label fn.fn_blocks = SOME bb /\
  (!b. MEM b fn.fn_blocks ==>
    lookup_block b.bb_label fn.fn_blocks = SOME b) /\
  def_on_all_paths fn bb point v /\
  (case point of NONE => LENGTH bb.bb_instructions <= i
   | SOME use_inst => !j. j < LENGTH bb.bb_instructions /\
       EL j bb.bb_instructions = use_inst ==> j <= i) ==>
  alias_path_available fn bb.bb_label i v
Proof
  simp[def_on_all_paths_def, alias_path_available_def] >> rpt strip_tac >>
  first_x_assum drule_all >> strip_tac
  >- (disj1_tac >> qexistsl_tac [`k`,`def_bb`,`def_inst`] >>
      simp[inst_defs_def] >> metis_tac[]) >>
  disj2_tac >> qexists_tac `i'` >> simp[inst_defs_def] >>
  Cases_on `point` >> gvs[] >> metis_tac[arithmeticTheory.LESS_LESS_EQ_TRANS]
QED

Theorem alias_ordinary_use_available:
  wf_function fn /\ def_dominates_uses fn /\
  MEM bb fn.fn_blocks /\ i < LENGTH bb.bb_instructions /\
  (EL i bb.bb_instructions).inst_opcode <> PHI /\
  MEM v (inst_uses (EL i bb.bb_instructions)) ==>
  alias_path_available fn bb.bb_label i v
Proof
  strip_tac >>
  `!b. MEM b fn.fn_blocks ==>
     lookup_block b.bb_label fn.fn_blocks = SOME b` by
    (rpt strip_tac >> irule MEM_lookup_block >>
     gvs[wf_function_def, fn_labels_def]) >>
  `def_available_at fn bb (SOME (EL i bb.bb_instructions)) v` by
    (qpat_x_assum `def_dominates_uses fn` mp_tac >>
     simp[def_dominates_uses_def] >>
     disch_then (qspecl_then [`bb`,`EL i bb.bb_instructions`] mp_tac) >>
     simp[EL_MEM] >> gvs[inst_uses_def, MEM_operand_vars_eq_Var]) >>
  irule alias_all_paths_indexed >>
  simp[] >> qexists_tac `SOME (EL i bb.bb_instructions)` >> simp[] >>
  reverse conj_tac
  >- (irule def_available_on_all_paths >> simp[]) >>
  rpt strip_tac >>
  `ALL_DISTINCT (MAP (\inst. inst.inst_id) bb.bb_instructions)` by
    metis_tac[wf_function_block_inst_ids_distinct] >>
  `j = i` by
    (drule ALL_DISTINCT_EL_IMP >>
     disch_then (qspecl_then [`j`,`i`] mp_tac) >> simp[EL_MAP]) >>
  simp[]
QED

Theorem alias_phi_edge_available:
  wf_function fn /\ def_dominates_uses fn /\
  MEM bb fn.fn_blocks /\ MEM phi bb.bb_instructions /\
  phi.inst_opcode = PHI /\
  MEM (pred,v) (phi_pairs phi.inst_operands) ==>
  ?pred_bb. lookup_block pred fn.fn_blocks = SOME pred_bb /\
    alias_path_available fn pred (LENGTH pred_bb.bb_instructions) v
Proof
  strip_tac >>
  `phi_edge_uses_wf fn bb phi` by
    metis_tac[def_dominates_uses_def] >>
  gvs[phi_edge_uses_wf_def] >>
  first_x_assum drule >> strip_tac >>
  `!b. MEM b fn.fn_blocks ==>
     lookup_block b.bb_label fn.fn_blocks = SOME b` by
    (rpt strip_tac >> irule MEM_lookup_block >>
     gvs[wf_function_def, fn_labels_def]) >>
  qpat_x_assum `pred_bb.bb_label = pred` (SUBST_ALL_TAC o SYM) >>
  qexists_tac `pred_bb` >> simp[] >>
  irule alias_all_paths_indexed >> simp[] >> qexists_tac `NONE` >> simp[] >>
  irule def_available_on_all_paths >> simp[]
QED

Theorem alias_available_nondef_backward:
  lookup_block l fn.fn_blocks = SOME bb /\
  i < LENGTH bb.bb_instructions /\
  ~MEM v (inst_defs (EL i bb.bb_instructions)) /\
  alias_path_available fn l (SUC i) v ==>
  alias_path_available fn l i v
Proof
  simp[alias_path_available_def] >> rpt strip_tac >>
  first_x_assum drule_all >> strip_tac
  >- metis_tac[] >>
  gvs[] >> disj2_tac >> qexists_tac `j` >> simp[] >>
  `j <> i` by metis_tac[] >> decide_tac
QED

Theorem alias_pending_phi_backward:
  alias_pending_phi fn l (SUC i) v ==> alias_pending_phi fn l i v
Proof
  simp[alias_pending_phi_def] >> rpt strip_tac >>
  qexistsl_tac [`bb`,`inst`] >> simp[] >>
  qpat_x_assum `MEM inst (DROP (SUC i) _)` mp_tac >>
  SPEC_TAC (``collect_phis bb.bb_instructions``, ``xs : instruction list``) >>
  qid_spec_tac `i` >> Induct >> Cases_on `xs` >> simp[]
QED

Theorem alias_cfg_successor_boundary:
  wf_function fn /\ MEM s (cfg_succs_of (cfg_analyze fn) l) ==>
  fn_cfg_edge fn l s /\ ?bb. lookup_block s fn.fn_blocks = SOME bb
Proof
  strip_tac >>
  `MEM l (fn_labels fn)` by
    (CCONTR_TAC >> gvs[fn_labels_def, cfg_analyze_succs] >>
     drule cfgHelpersTheory.cfg_succs_of_not_in_labels >>
     metis_tac[MEM]) >>
  conj_tac
  >- (gvs[fn_labels_def, MEM_MAP] >>
      rename1 `MEM b fn.fn_blocks` >>
      `cfg_succs_of (cfg_analyze fn) b.bb_label = bb_succs b` by
        metis_tac[cfg_analyze_preserves_bb_succs] >>
      gvs[fn_cfg_edge_def] >> metis_tac[]) >>
  `MEM s (fn_labels fn)` by metis_tac[cfg_analyze_succ_labels] >>
  gvs[fn_labels_def, MEM_MAP] >>
  metis_tac[MEM_lookup_block, wf_function_def, fn_labels_def]
QED

Theorem alias_available_edge_backward:
  fn_cfg_edge fn l s /\ alias_path_available fn s 0 v ==>
  alias_path_available fn l (LENGTH (liveness_instrs fn.fn_blocks l)) v
Proof
  simp[alias_path_available_def] >> rpt strip_tac >>
  `is_fn_path fn (SNOC s path)` by
    simp[supply_path_snoc] >>
  qpat_x_assum `!path. _` (qspec_then `SNOC s path` mp_tac) >>
  simp[SNOC_APPEND, LAST_APPEND_CONS] >>
  (impl_tac >- (Cases_on `path` >> gvs[])) >>
  strip_tac >>
  `k < LENGTH path` by decide_tac >>
  `EL k (path ++ [s]) = EL k path` by simp[EL_APPEND1] >>
  gvs[] >>
  Cases_on `k < LENGTH path - 1`
  >- (disj1_tac >> qexistsl_tac [`k`,`bb`,`inst`] >> simp[]) >>
  `k = LENGTH path - 1` by decide_tac >>
  `EL k path = LAST path` by
    metis_tac[LAST_EL, arithmeticTheory.PRE_SUB1] >>
  gvs[] >> disj2_tac >>
  simp[livenessBlockProofsTheory.liveness_instrs_def] >>
  gvs[MEM_EL] >> metis_tac[]
QED

Theorem alias_available_cfg_successor_backward:
  wf_function fn /\ MEM s (cfg_succs_of (cfg_analyze fn) l) /\
  alias_path_available fn s 0 v ==>
  alias_path_available fn l (LENGTH (liveness_instrs fn.fn_blocks l)) v
Proof
  metis_tac[alias_cfg_successor_boundary, alias_available_edge_backward]
QED

Theorem alias_phi_at_index_pending:
  !instrs i.
    (!j k. j < k /\ k < LENGTH instrs /\
      (EL k instrs).inst_opcode = PHI ==>
      (EL j instrs).inst_opcode = PHI) /\
    i < LENGTH instrs /\ (EL i instrs).inst_opcode = PHI ==>
    MEM (EL i instrs) (DROP i (collect_phis instrs))
Proof
  Induct >> simp[] >> Cases_on `i` >>
  simp[livenessDefsTheory.collect_phis_def] >> rpt strip_tac >>
  `h.inst_opcode = PHI` by
    (first_x_assum (qspecl_then [`0`,`SUC n`] mp_tac) >> simp[]) >>
  simp[livenessDefsTheory.collect_phis_def] >> first_x_assum irule >>
  simp[] >> rpt strip_tac >>
  first_x_assum (qspecl_then [`SUC j`,`SUC k`] mp_tac) >> simp[]
QED

Theorem alias_use_available_or_pending:
  wf_function fn /\ def_dominates_uses fn /\
  lookup_block l fn.fn_blocks = SOME bb /\
  i < LENGTH bb.bb_instructions /\
  MEM v (inst_uses (EL i bb.bb_instructions)) ==>
  alias_path_available fn l i v \/ alias_pending_phi fn l i v
Proof
  strip_tac >>
  `MEM bb fn.fn_blocks /\ bb.bb_label = l` by
    metis_tac[lookup_block_MEM, lookup_block_label] >>
  Cases_on `(EL i bb.bb_instructions).inst_opcode = PHI`
  >- (disj2_tac >> simp[alias_pending_phi_def] >>
      qexists_tac `EL i bb.bb_instructions` >> simp[] >>
      irule alias_phi_at_index_pending >>
      metis_tac[wf_function_def, bb_well_formed_def]) >>
  disj1_tac >> gvs[] >> irule alias_ordinary_use_available >> simp[]
QED

Theorem alias_availability_inst_closed:
  wf_function fn /\ def_dominates_uses fn /\
  lookup_block l fn.fn_blocks = SOME bb /\ i < LENGTH bb.bb_instructions /\
  (!v. MEM v live ==> alias_path_available fn l (SUC i) v \/
     alias_pending_phi fn l (SUC i) v) ==>
  !v. MEM v (liveness_transfer fn.fn_blocks (EL i bb.bb_instructions) live) ==>
    alias_path_available fn l i v \/ alias_pending_phi fn l i v
Proof
  strip_tac >> ho_match_mp_tac alias_liveness_transfer_rule >> conj_tac
  >- metis_tac[alias_use_available_or_pending] >>
  metis_tac[alias_available_nondef_backward, alias_pending_phi_backward]
QED

Theorem alias_availability_edge_closed:
  wf_function fn /\ def_dominates_uses fn /\
  MEM s (cfg_succs_of (cfg_analyze fn) l) /\
  (!v. MEM v live ==> alias_path_available fn s 0 v \/
    alias_pending_phi fn s 0 v) ==>
  !v. MEM v (liveness_edge_transfer fn.fn_blocks s l live) ==>
    alias_path_available fn l (LENGTH (liveness_instrs fn.fn_blocks l)) v \/
    alias_pending_phi fn l (LENGTH (liveness_instrs fn.fn_blocks l)) v
Proof
  strip_tac >>
  drule_all alias_cfg_successor_boundary >> strip_tac >>
  simp[liveness_edge_transfer_def] >> rpt strip_tac >>
  drule alias_input_vars_from_partition >> strip_tac
  >- (disj1_tac >> irule alias_available_cfg_successor_backward >>
      simp[] >> qexists_tac `s` >> simp[] >>
      `!phi. MEM phi (collect_phis bb.bb_instructions) ==>
          phi_well_formed phi.inst_operands` by
        (rpt strip_tac >>
         drule livenessTransferProofsTheory.collect_phis_mem >> strip_tac >>
         `MEM bb fn.fn_blocks` by metis_tac[lookup_block_MEM] >>
         metis_tac[def_dominates_uses_def, phi_edge_uses_wf_def]) >>
      `!phi. MEM phi (collect_phis bb.bb_instructions) ==>
         ~MEM v (inst_uses phi)` by
        (metis_tac[alias_build_phi_maps_absent_uses]) >>
      `~alias_pending_phi fn s 0 v` by
        (simp[alias_pending_phi_def] >> metis_tac[]) >>
      metis_tac[]) >>
  disj1_tac >>
  `MEM bb fn.fn_blocks /\ bb.bb_label = s` by
    metis_tac[lookup_block_MEM, lookup_block_label] >>
  drule livenessTransferProofsTheory.collect_phis_mem >> strip_tac >>
  drule_all alias_phi_edge_available >> strip_tac >>
  gvs[livenessBlockProofsTheory.liveness_instrs_def]
QED

Theorem alias_availability_live_closed:
  wf_function fn /\ def_dominates_uses fn ==>
  alias_live_closed fn (\l i v.
    alias_path_available fn l i v \/ alias_pending_phi fn l i v)
Proof
  simp[alias_live_closed_def] >> strip_tac >> conj_tac
  >- metis_tac[alias_availability_inst_closed] >>
  metis_tac[alias_availability_edge_closed]
QED

Theorem alias_live_available_or_pending:
  wf_function fn /\ def_dominates_uses fn /\
  MEM v (live_vars_at (liveness_analyze fn) l i) ==>
  alias_path_available fn l i v \/ alias_pending_phi fn l i v
Proof
  strip_tac >> drule_all alias_availability_live_closed >>
  disch_then (mp_tac o MATCH_MP alias_live_closed_analyze) >> simp[]
QED

Theorem alias_live_available_after_phis:
  wf_function fn /\ def_dominates_uses fn /\
  MEM v (live_vars_at (liveness_analyze fn) l i) /\
  lookup_block l fn.fn_blocks = SOME bb /\
  LENGTH (collect_phis bb.bb_instructions) <= i ==>
  alias_path_available fn l i v
Proof
  metis_tac[alias_live_available_or_pending, alias_pending_phi_past_prefix]
QED
