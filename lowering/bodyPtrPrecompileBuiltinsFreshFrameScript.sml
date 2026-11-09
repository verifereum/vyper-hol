Theory bodyPtrPrecompileBuiltinsFreshFrame
Ancestors bodyPtrPrecompileBuiltinsSuffixGhost compileEnv exprSimProps
          localPtrsProps bodyPtrDefs valueEncoding loweringPosts finite_map
          pred_set

(* Spatial discharge of the semantic exterior-frame boundary. *)
Theorem scoped_value_footprint:
  local_ptrs_rel func cenv scopes s /\
  lookup_scopes name scopes = SOME entry /\
  FLOOKUP cenv.ce_vars name = SOME (PtrVar (Var p) sz) /\
  lookup_var p s = SOME w ==>
  val_wf entry.type entry.value /\
  val_footprint entry.type entry.value <= sz /\
  local_region cenv scopes s name (w2n w) sz
Proof
  strip_tac >>
  `val_wf entry.type entry.value /\ type_memory_size entry.type <= sz` by
    (gvs[local_ptrs_rel_def] >> metis_tac[]) >>
  drule val_footprint_le >> strip_tac >>
  simp[local_region_def] >> metis_tac[]
QED

Theorem scoped_footprint_exterior:
  local_ptrs_rel func cenv scopes s /\
  (!name b sz. local_region cenv scopes s name b sz ==>
     regions_disjoint off len b sz) /\
  lookup_scopes name scopes = SOME entry /\
  FLOOKUP cenv.ce_vars name = SOME (PtrVar (Var p) sz) /\
  lookup_var p s = SOME w ==>
  val_wf entry.type entry.value /\
  (!i. w2n w <= i /\ i < w2n w + val_footprint entry.type entry.value ==>
       i NOTIN {j | off <= j /\ j < off + len})
Proof
  strip_tac >> drule_all scoped_value_footprint >> strip_tac >>
  `regions_disjoint off len (w2n w) sz` by metis_tac[] >>
  gvs[regions_disjoint_def] >> simp[] >> rpt strip_tac >> decide_tac
QED

Theorem fresh_scratch_ghost_frame:
  ghost_inv d cenv cx es G tn s /\
  local_ptrs_rel func cenv es.scopes s /\
  (!name b sz. local_region cenv es.scopes s name b sz ==>
     regions_disjoint off len b sz) /\
  (!p sz. ((?name. FLOOKUP cenv.ce_vars name = SOME (PtrVar (Var p) sz)) \/
            cenv.ce_return_buf = SOME (PtrVar (Var p) sz) \/
            cenv.ce_return_pc = SOME (PtrVar (Var p) sz)) ==>
     FLOOKUP G' p = FLOOKUP G p /\
     op_taint tn' (Var p) = op_taint tn (Var p) /\
     lookup_var p t = lookup_var p s) /\
  (!i. ~(off <= i /\ i < off + len) ==>
     mem_bytes_at i 1 t.vs_memory = mem_bytes_at i 1 s.vs_memory) /\
  (!i. ~(off <= i /\ i < off + len) ==> (i IN tn'.t_mem <=> i IN tn.t_mem)) /\
  tn'.t_stor = tn.t_stor /\ tn'.t_trans = tn.t_trans /\ tn'.t_imm = tn.t_imm /\
  t.vs_call_ctx = s.vs_call_ctx /\ t.vs_accounts = s.vs_accounts /\
  t.vs_transient = s.vs_transient ==>
  ghost_inv d cenv cx es G' tn' t
Proof
  strip_tac >> irule ghost_inv_exterior_frame >>
  qexistsl_tac [`G`, `s`, `tn`, `{i | off <= i /\ i < off + len}`] >>
  pure_rewrite_tac[IN_GSPEC] >> conj_tac >- metis_tac[] >>
  conj_tac
  >- (rpt gen_tac >> strip_tac >>
      drule_all scoped_footprint_exterior >> simp[]) >>
  simp[]
QED

(* The input allocation's s1 and output allocation's t in
   allocated_payload_run both supply the local-region premise above.
   No disjointness from older allocations is needed for ghost_inv itself:
   that premise belongs to S1's wb_frame, not to scoped value transport.
   For ghost_kept use ghost_kept_memory_subset from SuffixGhost directly;
   its old-variable stability and decreasing memory taint interface is
   independent of which of the two scratch buffers is being written. *)
