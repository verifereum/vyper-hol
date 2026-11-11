Theory concretizePtrConflictContract
Ancestors concretizePtrReadCoverage concretizePtrStoreCoverage
  concretizePtrOrdering concretizeMemLocDefs enumeral indexedLists
  calleeMemoryWitness finite_map list pred_set words

(* This is a consumer contract, not a semantic demand theorem. *)
Theorem ptr_marked_protected_store_pair:
  MEM bb fn.fn_blocks /\ i < LENGTH bb.bb_instructions /\
  OL alloc_to (ml_lookup la (bb.bb_label,i)) /\
  OL alloc_to (ml_lookup us (bb.bb_label,i)) /\
  MEM a (ml_lookup la (bb.bb_label,i)) /\
  MEM a (ml_lookup us (bb.bb_label,i)) /\
  MEM b (find_base_allocas_opt bpr (inst_write_op (EL i bb.bb_instructions))) ==>
  ?xs ys.
    FLOOKUP (ml_mark_stores_live bpr fn (ml_compute_livesets la us fn)) a = SOME xs /\
    FLOOKUP (ml_mark_stores_live bpr fn (ml_compute_livesets la us fn)) b = SOME ys /\
    MEM (bb.bb_label,i) xs /\ MEM (bb.bb_label,i) ys
Proof
  strip_tac >>
  `MEM a (sinter alloc_to (ml_lookup la (bb.bb_label,i))
                         (ml_lookup us (bb.bb_label,i)))` by
    (qpat_x_assum `OL alloc_to (ml_lookup la _)` (mp_tac o MATCH_MP OL_INTER_IMP) >>
     disch_then (qspec_then `ml_lookup us (bb.bb_label,i)` mp_tac) >>
     simp[EXTENSION] >> metis_tac[]) >>
  drule_all ptr_marked_intersection >> strip_tac >>
  `MEM (i,EL i bb.bb_instructions)
    (MAPi (\j inst. (j,inst)) bb.bb_instructions)` by simp[MEM_MAPi] >>
  drule_all ptr_mark_stores_covers_write >> strip_tac >>
  metis_tac[]
QED

(* Reuse witness_one: initializes local Allocation 3, calls leaf, then reads 3.
   Unlike the metadata-only leaf fixture, this leaf actually writes its site. *)
Definition ptr_conflict_leaf_def:
  ptr_conflict_leaf = mk_raw_function "leaf"
    [<| bb_label := "entry"; bb_instructions :=
      [mk_inst 100 ALLOCA [Lit (32w:256 word)] ["b"];
       mk_inst 101 MSTORE [Var "b"; Lit 9w] [];
       mk_inst 102 RET [] []] |>]
End

Definition ptr_conflict_ctx_def:
  ptr_conflict_ctx = mk_venom_context
    [THE (concretize_function_fuel_in_context
      (concretize_memloc_fuel ptr_conflict_leaf)
      (mk_venom_context [] NONE) [] ptr_conflict_leaf)] (SOME "caller")
End

Definition ptr_conflict_ls_def:
  ptr_conflict_ls = context_mem_livesets (concretize_memloc_fuel witness_one)
    ptr_conflict_ctx witness_one
    (bp_analyze_fuel (concretize_memloc_fuel witness_one)
      (cfg_analyze witness_one) witness_one) (cfg_analyze witness_one)
End

Theorem ptr_conflict_imported_store_fixture:
  callee_mems_used ptr_conflict_ctx "leaf" = [(Allocation 100,0,32)] /\
  (?xs ys. FLOOKUP ptr_conflict_ls (Allocation 3) = SOME xs /\
           FLOOKUP ptr_conflict_ls (Allocation 100) = SOME ys /\
           MEM ("entry",2) xs /\ MEM ("entry",2) ys)
Proof
  CONV_TAC (DEPTH_CONV wordsLib.SIZES_CONV) >> EVAL_TAC >> simp[]
QED

Theorem ptr_conflict_layout_fixture:
  OPTION_MAP (\f. (f.fn_eom,f.fn_mems_used))
    (concretize_function_fuel_in_context
      (concretize_memloc_fuel ptr_conflict_leaf)
      (mk_venom_context [] NONE) [] ptr_conflict_leaf) =
    SOME (SOME 32,[(Allocation 100,0,32)]) /\
  OPTION_MAP (\layout. (FLOOKUP layout.cl_positions (Allocation 3),layout.cl_eom))
    (compute_function_layout_fuel_in_context (concretize_memloc_fuel witness_one)
      ptr_conflict_ctx [] witness_one) = SOME (SOME 32,64)
Proof
  CONV_TAC (DEPTH_CONV wordsLib.SIZES_CONV) >> EVAL_TAC
QED
