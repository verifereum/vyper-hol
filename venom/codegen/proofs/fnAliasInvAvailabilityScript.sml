Theory fnAliasInvAvailability
Ancestors
  fnAliasInvLiveness venomWf rich_list list livenessDefs finite_map
  pair indexedLists passSharedDefs
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
