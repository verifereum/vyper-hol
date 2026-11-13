Theory concretizeAnalysisLivenessPaths
Ancestors
  concretizeAnalysisLivenessProduction concretizeAnalysisLivenessTransfer
  concretizePtrReadCoverage concretizePtrOrdering cfgAnalysisProps relation

(* A guard is tested only at the destination of an intra-block edge.
   CFG joins import recorded entry sets directly, without that test. *)
Definition ml_indexed_step_def:
  ml_indexed_step fn guard p q <=>
    (?bb i. MEM bb fn.fn_blocks /\ SUC i < LENGTH bb.bb_instructions /\
      p = (bb.bb_label,i) /\ q = (bb.bb_label,SUC i) /\
      guard (EL (SUC i) bb.bb_instructions)) \/
    (?bb dst. MEM bb fn.fn_blocks /\ MEM dst fn.fn_blocks /\
      bb.bb_instructions <> [] /\ dst.bb_instructions <> [] /\
      MEM dst.bb_label (cfg_succs_of (cfg_analyze fn) bb.bb_label) /\
      p = (bb.bb_label,PRE (LENGTH bb.bb_instructions)) /\ q = (dst.bb_label,0))
End

Definition ml_indexed_path_def:
  ml_indexed_path fn guard = RTC (ml_indexed_step fn guard)
End

Theorem ml_production_liveat_step:
  wf_function fn /\ all_reachable fn /\
  (!nm. OL alloc_to (mems nm)) /\ OL alloc_to pallocas /\
  ml_iterate_fuel (concretize_memloc_fuel fn) bpr mems sizes pallocas
    (cfg_analyze fn) fn FEMPTY FEMPTY = (la,us) /\
  ml_indexed_step fn (\inst. ~ptr_ml_can_kill a bpr sizes inst) p q /\
  MEM a (ml_lookup la q) ==>
  MEM a (ml_lookup la p)
Proof
  simp[ml_indexed_step_def] >> rpt strip_tac >> gvs[]
  >- metis_tac[ml_production_liveat_retention] >>
  metis_tac[ml_production_liveat_cfg_edge]
QED

Theorem ml_production_used_step:
  wf_function fn /\ all_reachable fn /\
  (!nm. OL alloc_to (mems nm)) /\ OL alloc_to pallocas /\
  ml_iterate_fuel (concretize_memloc_fuel fn) bpr mems sizes pallocas
    (cfg_analyze fn) fn FEMPTY FEMPTY = (la,us) /\
  ml_indexed_step fn (\inst. T) p q /\ MEM a (ml_lookup us p) ==>
  MEM a (ml_lookup us q)
Proof
  simp[ml_indexed_step_def] >> rpt strip_tac >> gvs[]
  >- metis_tac[ml_production_used_retention] >>
  metis_tac[ml_production_used_cfg_edge, cfg_edge_symmetry_uncond]
QED

Theorem ml_production_liveat_path:
  wf_function fn /\ all_reachable fn /\
  (!nm. OL alloc_to (mems nm)) /\ OL alloc_to pallocas /\
  ml_iterate_fuel (concretize_memloc_fuel fn) bpr mems sizes pallocas
    (cfg_analyze fn) fn FEMPTY FEMPTY = (la,us) ==>
  !p q. ml_indexed_path fn (\inst. ~ptr_ml_can_kill a bpr sizes inst) p q ==>
    MEM a (ml_lookup la q) ==> MEM a (ml_lookup la p)
Proof
  strip_tac >> rewrite_tac[ml_indexed_path_def] >>
  ho_match_mp_tac RTC_INDUCT >> simp[] >>
  metis_tac[ml_production_liveat_step]
QED

Theorem ml_production_used_path:
  wf_function fn /\ all_reachable fn /\
  (!nm. OL alloc_to (mems nm)) /\ OL alloc_to pallocas /\
  ml_iterate_fuel (concretize_memloc_fuel fn) bpr mems sizes pallocas
    (cfg_analyze fn) fn FEMPTY FEMPTY = (la,us) ==>
  !p q. ml_indexed_path fn (\inst. T) p q ==>
    MEM a (ml_lookup us p) ==> MEM a (ml_lookup us q)
Proof
  strip_tac >> rewrite_tac[ml_indexed_path_def] >>
  ho_match_mp_tac RTC_INDUCT >> simp[] >>
  metis_tac[ml_production_used_step]
QED

Theorem ml_production_liveat_future_generator:
  wf_function fn /\ all_reachable fn /\
  (!nm. OL alloc_to (mems nm)) /\ OL alloc_to pallocas /\
  ml_iterate_fuel (concretize_memloc_fuel fn) bpr mems sizes pallocas
    (cfg_analyze fn) fn FEMPTY FEMPTY = (la,us) /\
  MEM bb fn.fn_blocks /\ i < LENGTH bb.bb_instructions /\
  ml_read_gen a bpr mems (EL i bb.bb_instructions) /\
  ml_indexed_path fn (\inst. ~ptr_ml_can_kill a bpr sizes inst) p (bb.bb_label,i) ==>
  MEM a (ml_lookup la p)
Proof
  metis_tac[ml_production_liveat_generation, ml_production_liveat_path]
QED

Theorem ml_production_used_past_generator:
  wf_function fn /\ all_reachable fn /\
  (!nm. OL alloc_to (mems nm)) /\ OL alloc_to pallocas /\
  ml_iterate_fuel (concretize_memloc_fuel fn) bpr mems sizes pallocas
    (cfg_analyze fn) fn FEMPTY FEMPTY = (la,us) /\
  MEM bb fn.fn_blocks /\ i < LENGTH bb.bb_instructions /\
  ml_used_gen a bpr mems (EL i bb.bb_instructions) /\
  ml_indexed_path fn (\inst. T) (bb.bb_label,i) q ==>
  MEM a (ml_lookup us q)
Proof
  metis_tac[ml_production_used_generation, ml_production_used_path]
QED

Theorem ml_production_invoke_generators:
  wf_function fn /\ all_reachable fn /\
  (!nm. OL alloc_to (mems nm)) /\ OL alloc_to pallocas /\
  ml_iterate_fuel (concretize_memloc_fuel fn) bpr mems sizes pallocas
    (cfg_analyze fn) fn FEMPTY FEMPTY = (la,us) /\
  MEM bb fn.fn_blocks /\ i < LENGTH bb.bb_instructions /\
  inst = EL i bb.bb_instructions /\ inst.inst_opcode = INVOKE /\
  inst.inst_operands = Label nm :: ops /\
  (MEM a (mems nm) \/ ml_operand_gen a bpr inst) ==>
  MEM a (ml_lookup la (bb.bb_label,i)) /\ MEM a (ml_lookup us (bb.bb_label,i))
Proof
  strip_tac >>
  `ml_read_gen a bpr mems inst /\ ml_used_gen a bpr mems inst` by
    (simp[ml_read_gen_def, ml_used_gen_def, ml_callee_gen_def] >> metis_tac[]) >>
  metis_tac[ml_production_liveat_generation, ml_production_used_generation]
QED

(* INVOKE continuation retention uses ml_production_liveat_retention directly:
   its stronger opcode-independent statement also specifies the next-instruction kill. *)

Theorem ml_production_marked_membership:
  (!nm. OL alloc_to (mems nm)) /\ OL alloc_to pallocas /\
  ml_iterate_fuel (concretize_memloc_fuel fn) bpr mems sizes pallocas
    (cfg_analyze fn) fn FEMPTY FEMPTY = (la,us) /\
  MEM bb fn.fn_blocks /\ i < LENGTH bb.bb_instructions /\
  MEM a (ml_lookup la (bb.bb_label,i)) /\ MEM a (ml_lookup us (bb.bb_label,i)) ==>
  ?addrs. FLOOKUP (ml_mark_stores_live bpr fn (ml_compute_livesets la us fn)) a = SOME addrs /\
    MEM (bb.bb_label,i) addrs
Proof
  strip_tac >> drule_all ml_production_ordered >> strip_tac >>
  `OL alloc_to (ml_lookup la (bb.bb_label,i)) /\
   OL alloc_to (ml_lookup us (bb.bb_label,i))` by gvs[ptr_ml_ordered_def] >>
  `MEM a (sinter alloc_to (ml_lookup la (bb.bb_label,i))
    (ml_lookup us (bb.bb_label,i)))` by
    (qpat_x_assum `OL alloc_to (ml_lookup la _)`
       (mp_tac o MATCH_MP enumeralTheory.OL_INTER_IMP) >>
     disch_then (qspec_then `ml_lookup us (bb.bb_label,i)` mp_tac) >>
     simp[pred_setTheory.EXTENSION] >> metis_tac[]) >>
  metis_tac[ptr_marked_intersection]
QED
