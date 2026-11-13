(* Constructor code offsets denote live immutable bytes in memory. *)
Theory bodyIntCallPostProvenanceArrayImmutableFrame
Ancestors
  loweringPosts loweringStateRelDefs exprLoweringProps words bodyIntCallPathLayout

Theorem immutables_rel_sub_layout:
  immutables_rel cenv addr src ctor es s /\
  FLOOKUP cenv.ce_module_vars (src,name) = SOME (ImmutableLoc off) /\
  FLOOKUP (case ALOOKUP es.immutables addr of
             NONE => FEMPTY
           | SOME imms => get_source_immutables src imms)
    name = SOME (itv,iv) /\
  sub_layout itv iv k tv v ==>
  val_in_memory tv v (off+k)
    (if ctor then s.vs_memory else s.vs_data_section)
Proof
  simp[immutables_rel_def, sub_layout_def] >> rpt strip_tac >>
  first_x_assum drule_all >> strip_tac >> metis_tac[arithmeticTheory.ADD_COMM]
QED

Theorem immutable_holds_ctor_memory:
  immutable_holds cenv cx ty raw w es s /\
  stmt_state_rel ctx func cenv cx es s /\ cenv.ce_is_ctor ==>
  ?tv v. evaluate_type (get_tenv cx) ty = SOME tv /\
    read_result cx raw es = (INL v,es) /\
    val_in_memory tv v (w2n w) s.vs_memory
Proof
  strip_tac >>
  gvs[immutable_holds_def] >>
  `off+k < dimword (:256)` by (gvs[sub_layout_def] >> decide_tac) >>
  simp[w2n_n2w] >>
  `immutables_rel cenv cx.txn.target cenv.ce_module cenv.ce_is_ctor es s` by
    gvs[stmt_state_rel_def, state_rel_def] >>
  drule_all immutables_rel_sub_layout >> simp[arithmeticTheory.ADD_COMM]
QED

(* Concrete live nested dynamic selection in constructor memory. *)
Theorem constructor_nested_dynamic_selection[local]:
  immutables_rel ce addr src T es s /\
  FLOOKUP ce.ce_module_vars (src,name) = SOME (ImmutableLoc off) /\
  FLOOKUP (case ALOOKUP es.immutables addr of
             NONE => FEMPTY
           | SOME imms => get_source_immutables src imms) name =
    SOME (ArrayTV (ArrayTV (BaseTV BoolT) (Dynamic 1)) (Dynamic 1),
          ArrayV (DynArrayV [ArrayV (DynArrayV [BoolV T])])) ==>
  val_in_memory (ArrayTV (BaseTV BoolT) (Dynamic 1))
    (ArrayV (DynArrayV [BoolV T])) (off+32) s.vs_memory
Proof
  strip_tac >>
  `sub_layout
     (ArrayTV (ArrayTV (BaseTV BoolT) (Dynamic 1)) (Dynamic 1))
     (ArrayV (DynArrayV [ArrayV (DynArrayV [BoolV T])])) 32
     (ArrayTV (BaseTV BoolT) (Dynamic 1)) (ArrayV (DynArrayV [BoolV T]))` by
    (irule bodyIntCallPathLayoutTheory.mem_path_selection_sub_layout >>
     reverse conj_tac >- EVAL_TAC >>
     qexists `[ValueSubscript (IntV 0)]` >> EVAL_TAC >> simp[]) >>
  drule_all immutables_rel_sub_layout >> simp[]
QED
