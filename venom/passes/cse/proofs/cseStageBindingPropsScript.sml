Theory cseStageBindingProps
Ancestors cseRootReplayProps cseHistoryProps cseReplayProps cseCanonProps
  venomInstIdsProps venomWf

(* The stage is the input prefix of the canon fold, not the final map. *)
Definition cse_stage_canon_def:
 cse_stage_canon fn k =
   FOLDL (\c (ae,i). compute_canon_inst (dfg_build_function fn) c ae i)
     FEMPTY (TAKE k (cse_canon_inputs (avail_analyze fn) fn))
End

(* Quantify over all live singleton writers, including writers whose output
   is not a syntactic operand of the instruction at the current cut. *)
Definition cse_stage_binding_def:
 cse_stage_binding fn k <=>
 !ctx fuel0 s0 events n bb s use pre post m db d u t x.
   cse_prefix ctx fn fuel0 s0 events (CseExec n bb s) /\
   get_instruction bb s.vs_inst_idx = SOME use /\
   MEM d (fn_insts fn) /\ d.inst_outputs = [x] /\ d.inst_opcode <> PHI /\
   cse_path_preorder fn d.inst_id use.inst_id /\ d.inst_id <> use.inst_id /\
   events = pre ++ [CseStep m db d u t] ++ post /\
   cse_prefix ctx fn fuel0 s0 pre (CseExec m db u) /\
   EVERY (\ev. ~cse_event_writes ev x) post ==>
   ?r z. MEM r (fn_insts fn) /\ r.inst_outputs = [z] /\ r.inst_opcode <> PHI /\
     r.inst_id = canonical_id (cse_stage_canon fn k) d.inst_id /\
     cse_path_preorder fn r.inst_id d.inst_id /\ lookup_var x s = lookup_var z s
End

Theorem cse_stage_binding_zero:
 cse_stage_binding fn 0
Proof
 simp[cse_stage_binding_def, cse_stage_canon_def, cseDefsTheory.canonical_id_def] >>
 rpt strip_tac >> qexistsl [`d`, `x`] >> simp[] >>
 metis_tac[cseCanonPropsTheory.cse_path_preorder_reflexive, relationTheory.reflexive_def]
QED


Theorem cse_stage_ordinary_operand_binding:
 wf_function fn /\ fn_inst_wf fn /\ cse_reachable_wf_ssa fn /\
 cse_stage_binding fn k /\
 cse_prefix ctx fn fuel0 s0 events (CseExec n bb s) /\
 get_instruction bb s.vs_inst_idx = SOME use /\ use.inst_opcode <> PHI /\
 MEM op use.inst_operands /\
 operand_producer (dfg_build_function fn) {} op = SOME a /\
 (?opc args. mk_operand_expr (dfg_build_function fn) [] op = ExprOp opc args) ==>
 ?r z. MEM r (fn_insts fn) /\ r.inst_outputs = [z] /\ r.inst_opcode <> PHI /\
   r.inst_id = canonical_id (cse_stage_canon fn k) a /\
   cse_path_preorder fn r.inst_id use.inst_id /\ r.inst_id <> use.inst_id /\
   eval_operand op s = lookup_var z s
Proof
 strip_tac >>
 drule_all cse_prefix_some_operand_current_binding >> strip_tac >>
 drule_all fn_operand_producer_expression_shape >> strip_tac >>
 `inst = definer` by (irule fn_inst_ids_distinct_inj >> fs[wf_function_def] >> metis_tac[]) >>
 gvs[] >>
 `~is_pseudo definer.inst_opcode /\ LENGTH definer.inst_outputs <= 1` by
   metis_tac[availExprDefsTheory.avail_expr_distinct, arithmeticTheory.NOT_LESS] >>
 `definer.inst_outputs = [v]` by
   (Cases_on `definer.inst_outputs` >> gvs[] >>
    Cases_on `t` >> gvs[]) >>
 `definer.inst_opcode <> PHI` by
   (strip_tac >> gvs[venomInstTheory.is_pseudo_def]) >>
 drule_all cse_prefix_some_operand_live_writer >> strip_tac >>
 `?r z. MEM r (fn_insts fn) /\ r.inst_outputs = [z] /\ r.inst_opcode <> PHI /\
   r.inst_id = canonical_id (cse_stage_canon fn k) definer.inst_id /\
   cse_path_preorder fn r.inst_id definer.inst_id /\ lookup_var v s = lookup_var z s` by
   (qpat_x_assum `cse_stage_binding fn k` mp_tac >>
    simp[cse_stage_binding_def] >> metis_tac[]) >>
 qexistsl [`r`, `z`] >> simp[] >>
 `cse_point_has_id fn (bb.bb_label,s.vs_inst_idx) use.inst_id` by
   (qpat_assum `cse_prefix _ _ _ _ _ (CseExec n bb s)`
      (mp_then Any mp_tac cse_prefix_exec_control) >> simp[] >> strip_tac >>
    gvs[cseCanonPropsTheory.cse_point_has_id_def,
        venomInstTheory.get_instruction_def, AllCaseEqs()]) >>
 qpat_assum `cse_prefix _ _ _ _ _ (CseExec n bb s)`
   (mp_then Any mp_tac cse_prefix_project_exec) >> simp[] >> strip_tac >>
 irule cse_path_preorder_reachable_strict_chain >> metis_tac[]
QED

Theorem cse_stage_source_interval_ordinary_operands_equal:
 wf_function fn /\ fn_inst_wf fn /\ cse_reachable_wf_ssa fn /\
 cse_stage_binding fn k /\
 cse_prefix ctx fn fuel0 s0 events (CseExec n bb s) /\
 get_instruction bb s.vs_inst_idx = SOME inst /\ inst.inst_opcode <> PHI /\
 events = pre ++ [CseStep m sb src u v] ++ post /\
 cse_prefix ctx fn fuel0 s0 pre (CseExec m sb u) /\
 get_instruction sb u.vs_inst_idx = SOME src /\
 src.inst_opcode <> PHI /\ MEM src (fn_insts fn) /\
 (!j ph. LENGTH pre < j /\ j <= LENGTH events /\
   cse_prefix ctx fn fuel0 s0 (TAKE j events) ph ==>
   cse_phase_has_source fn ph e src) /\
 MEM op inst.inst_operands /\ MEM sop src.inst_operands /\
 operand_producer (dfg_build_function fn) {} op = SOME a /\
 operand_producer (dfg_build_function fn) {} sop = SOME b /\
 (?opc args. mk_operand_expr (dfg_build_function fn) [] op = ExprOp opc args) /\
 (?opc args. mk_operand_expr (dfg_build_function fn) [] sop = ExprOp opc args) /\
 canonical_id (cse_stage_canon fn k) a = canonical_id (cse_stage_canon fn k) b ==>
 eval_operand op s = eval_operand sop u
Proof
 strip_tac >>
 `?r z. MEM r (fn_insts fn) /\ r.inst_outputs = [z] /\ r.inst_opcode <> PHI /\
   r.inst_id = canonical_id (cse_stage_canon fn k) a /\
   cse_path_preorder fn r.inst_id inst.inst_id /\ r.inst_id <> inst.inst_id /\
   eval_operand op s = lookup_var z s` by
   (irule cse_stage_ordinary_operand_binding >> metis_tac[]) >>
 `?q y. MEM q (fn_insts fn) /\ q.inst_outputs = [y] /\ q.inst_opcode <> PHI /\
   q.inst_id = canonical_id (cse_stage_canon fn k) b /\
   cse_path_preorder fn q.inst_id src.inst_id /\ q.inst_id <> src.inst_id /\
   eval_operand sop u = lookup_var y u` by
   (irule cse_stage_ordinary_operand_binding >> metis_tac[]) >>
 `r = q` by (irule fn_inst_ids_distinct_inj >> fs[wf_function_def] >> metis_tac[]) >> gvs[] >>
 `lookup_var y s = lookup_var y u` by
   (irule cse_source_interval_predecessor_binding_all >>
    qexistsl [`bb`, `ctx`, `q`, `e`, `pre ++ [CseStep m sb src u v] ++ post`] >>
    simp[] >> metis_tac[]) >>
 metis_tac[]
QED

Theorem cse_stage_source_interval_operand_alignment:
 wf_function fn /\ fn_inst_wf fn /\ cse_reachable_wf_ssa fn /\
 cse_stage_binding fn k /\
 cse_prefix ctx fn fuel0 s0 events (CseExec n bb s) /\
 get_instruction bb s.vs_inst_idx = SOME inst /\ inst.inst_opcode <> PHI /\
 events = pre ++ [CseStep m sb src u v] ++ post /\
 cse_prefix ctx fn fuel0 s0 pre (CseExec m sb u) /\
 get_instruction sb u.vs_inst_idx = SOME src /\
 src.inst_opcode <> PHI /\ MEM src (fn_insts fn) /\
 ~is_pseudo src.inst_opcode /\ LENGTH src.inst_outputs <= 1 /\
 mk_expr (dfg_build_function fn) inst = mk_expr (dfg_build_function fn) src /\
 operand_ids_match (cse_stage_canon fn k) (dfg_build_function fn) inst src /\
 (!j ph. LENGTH pre < j /\ j <= LENGTH events /\
   cse_prefix ctx fn fuel0 s0 (TAKE j events) ph ==>
   cse_phase_has_source fn ph e src) ==>
 MAP (\op. eval_operand op u) src.inst_operands =
 MAP (\op. eval_operand op s) inst.inst_operands \/
 (is_commutative inst.inst_opcode /\ LENGTH src.inst_operands = 2 /\
  LENGTH inst.inst_operands = 2 /\
  MAP (\op. eval_operand op u) src.inst_operands =
  REVERSE (MAP (\op. eval_operand op s) inst.inst_operands))
Proof
 strip_tac >>
 `!op sop a b.
   MEM op inst.inst_operands /\ MEM sop src.inst_operands /\
   operand_producer (dfg_build_function fn) {} op = SOME a /\
   operand_producer (dfg_build_function fn) {} sop = SOME b /\
   (?opc args. mk_operand_expr (dfg_build_function fn) [] op = ExprOp opc args) /\
   (?opc args. mk_operand_expr (dfg_build_function fn) [] sop = ExprOp opc args) /\
   canonical_id (cse_stage_canon fn k) a = canonical_id (cse_stage_canon fn k) b ==>
   eval_operand op s = eval_operand sop u` by
   (rpt gen_tac >> strip_tac >>
    irule cse_stage_source_interval_ordinary_operands_equal >> metis_tac[]) >>
 gvs[] >> irule cse_source_interval_operand_alignment >>
 simp[GSYM cse_stage_canon_def] >> metis_tac[]
QED

(* Replay a successful singleton computation against its available source.
   The result is a binding at the current input, ready for B(k). *)
Theorem cse_stage_available_singleton_replay:
 wf_function fn /\ fn_inst_wf fn /\ cse_reachable_wf_ssa fn /\
 EVERY (\i. ~is_alloca_op i.inst_opcode) (fn_insts fn) /\
 cse_stage_binding fn k /\
 cse_prefix ctx fn fuel0 s0 events (CseExec n bb s) /\
 get_instruction bb s.vs_inst_idx = SOME inst /\
 inst_wf inst /\ inst_wf src /\ inst.inst_outputs = [x] /\ src.inst_outputs = [y] /\
 FLOOKUP (ae_lookup_inst fn bb.bb_label s.vs_inst_idx)
   (mk_expr (dfg_build_function fn) inst) = SOME xs /\ MEM src xs /\
 operand_ids_match (cse_stage_canon fn k) (dfg_build_function fn) inst src /\
 step_inst n ctx inst s = OK t ==>
 lookup_var x t = lookup_var y s
Proof
 strip_tac >>
 drule_all cse_prefix_exec_avail_output_persistence >> strip_tac >>
 `MEM (CseStep m sb src u v) events` by gvs[listTheory.MEM_APPEND] >>
 drule_all cse_prefix_event_provenance >> simp[] >> strip_tac >>
 `MEM src (fn_insts fn)` by
   (drule_all cse_prefix_exec_control >> strip_tac >>
    simp[venomInstTheory.fn_insts_def] >>
    irule venomInstTheory.fmp_fn_insts_blocks_intro >>
    gvs[venomInstTheory.get_instruction_def, AllCaseEqs()] >>
    metis_tac[venomExecPropsTheory.lookup_block_MEM, listTheory.EL_MEM]) >>
 `~is_pseudo src.inst_opcode /\ src.inst_opcode <> ASSIGN /\
  ~is_terminator src.inst_opcode /\ ~avail_nonidempotent src.inst_opcode /\
  ~has_conflicting_effects src.inst_opcode /\
  mk_expr (dfg_build_function fn) inst = mk_expr (dfg_build_function fn) src` by
   gvs[availExprProofsTheory.avail_source_birth_def] >>
 `inst.inst_opcode = src.inst_opcode` by metis_tac[mk_expr_root_inversion] >>
 `src.inst_opcode <> PHI` by
   (strip_tac >> gvs[venomInstTheory.is_pseudo_def]) >>
 `MAP (\op. eval_operand op u) src.inst_operands =
    MAP (\op. eval_operand op s) inst.inst_operands \/
  (is_commutative inst.inst_opcode /\ LENGTH src.inst_operands = 2 /\
   LENGTH inst.inst_operands = 2 /\
   MAP (\op. eval_operand op u) src.inst_operands =
   REVERSE (MAP (\op. eval_operand op s) inst.inst_operands))` by
   (`inst.inst_opcode <> PHI /\ LENGTH src.inst_outputs <= 1` by simp[] >>
    drule_all cse_stage_source_interval_operand_alignment >> simp[]) >>
 `lookup_var x t = lookup_var y v` by
   (irule cse_singleton_history_replay >> simp[] >> metis_tac[]) >>
 metis_tac[]
QED

Theorem cse_stage_available_live_binding:
 wf_function fn /\ fn_inst_wf fn /\ cse_reachable_wf_ssa fn /\
 EVERY (\i. ~is_alloca_op i.inst_opcode) (fn_insts fn) /\
 cse_stage_binding fn k /\
 cse_prefix ctx fn fuel0 s0 events (CseExec n bb s) /\
 get_instruction bb s.vs_inst_idx = SOME use /\
 events = pre ++ [CseStep m cb inst u t] ++ post /\
 cse_prefix ctx fn fuel0 s0 pre (CseExec m cb u) /\
 get_instruction cb u.vs_inst_idx = SOME inst /\
 MEM inst (fn_insts fn) /\ inst.inst_opcode <> PHI /\
 inst_wf inst /\ inst_wf src /\ inst.inst_outputs = [x] /\ src.inst_outputs = [y] /\
 EVERY (\ev. ~cse_event_writes ev x) post /\
 cse_path_preorder fn inst.inst_id use.inst_id /\ inst.inst_id <> use.inst_id /\
 cse_path_preorder fn src.inst_id inst.inst_id /\ src.inst_id <> inst.inst_id /\
 avail_get_source (ae_lookup_inst fn cb.bb_label u.vs_inst_idx)
   (mk_expr (dfg_build_function fn) inst) = SOME src /\
 operand_ids_match (cse_stage_canon fn k) (dfg_build_function fn) inst src /\
 step_inst m ctx inst u = OK t ==>
 ?r z. MEM r (fn_insts fn) /\ r.inst_outputs = [z] /\ r.inst_opcode <> PHI /\
   r.inst_id = canonical_id (cse_stage_canon fn k) src.inst_id /\
   cse_path_preorder fn r.inst_id inst.inst_id /\ lookup_var x s = lookup_var z s
Proof
 strip_tac >>
 `lookup_var x t = lookup_var y u` by
   (irule cse_stage_available_singleton_replay >>
    gvs[availExprDefsTheory.avail_get_source_def, AllCaseEqs()] >>
    goal_assum (drule_at Any) >> simp[] >> metis_tac[listTheory.MEM]) >>
 `?xs. FLOOKUP (ae_lookup_inst fn cb.bb_label u.vs_inst_idx)
    (mk_expr (dfg_build_function fn) inst) = SOME xs /\ MEM src xs` by
   (gvs[availExprDefsTheory.avail_get_source_def, AllCaseEqs()] >> simp[]) >>
 drule_all cse_prefix_exec_avail_output_persistence >> strip_tac >>
 `MEM src (fn_insts fn)` by
   (irule (cj 1 cseSourcePropsTheory.cse_avail_get_source_provenance) >>
    metis_tac[availExprDefsTheory.ae_lookup_inst_def]) >>
 `src.inst_opcode <> PHI` by
   (gvs[availExprProofsTheory.avail_source_birth_def] >>
    strip_tac >> gvs[venomInstTheory.is_pseudo_def]) >>
 `?r z. MEM r (fn_insts fn) /\ r.inst_outputs = [z] /\ r.inst_opcode <> PHI /\
   r.inst_id = canonical_id (cse_stage_canon fn k) src.inst_id /\
   cse_path_preorder fn r.inst_id src.inst_id /\ lookup_var y u = lookup_var z u` by
   (qpat_x_assum `cse_stage_binding fn k` mp_tac >>
    simp[cse_stage_binding_def] >> metis_tac[]) >>
 `cse_path_preorder fn r.inst_id inst.inst_id /\ r.inst_id <> inst.inst_id` by
   (`cse_point_has_id fn (cb.bb_label,u.vs_inst_idx) inst.inst_id` by
      (qpat_assum `cse_prefix _ _ _ _ _ (CseExec m cb u)`
         (mp_then Any mp_tac cse_prefix_exec_control) >> simp[] >> strip_tac >>
       gvs[cseCanonPropsTheory.cse_point_has_id_def,
           venomInstTheory.get_instruction_def, AllCaseEqs()]) >>
    qpat_assum `cse_prefix _ _ _ _ _ (CseExec m cb u)`
      (mp_then Any mp_tac cse_prefix_project_exec) >> simp[] >> strip_tac >>
    irule cse_path_preorder_reachable_strict_chain >> metis_tac[]) >>
 qexistsl [`r`, `z`] >> simp[] >>
 irule cse_canonical_edge_live_binding >> metis_tac[]
QED

Theorem cse_canon_input_at_exec:
 wf_function fn /\ fn_inst_wf fn /\ MEM (ae,inst) (cse_canon_inputs (avail_analyze fn) fn) /\
 cse_prefix ctx fn fuel0 s0 events (CseExec n bb s) /\
 get_instruction bb s.vs_inst_idx = SOME inst ==>
 ae = ae_lookup_inst fn bb.bb_label s.vs_inst_idx
Proof
 strip_tac >> drule_all cse_canon_input_location >> strip_tac >>
 `lookup_block bb.bb_label fn.fn_blocks = SOME bb` by
   (drule_all cse_prefix_exec_control >> simp[]) >>
 `cse_point_has_id fn (bb.bb_label,s.vs_inst_idx) inst.inst_id /\
  cse_point_has_id fn (bb'.bb_label,k) inst.inst_id` by
   gvs[cseCanonPropsTheory.cse_point_has_id_def,
       venomInstTheory.get_instruction_def, AllCaseEqs()] >>
 `(bb.bb_label,s.vs_inst_idx) = (bb'.bb_label,k)` by
   (irule cse_point_has_id_injective >> metis_tac[]) >>
 gvs[availExprDefsTheory.ae_lookup_inst_def]
QED

Theorem cse_stage_changed_live_binding:
 wf_function fn /\ fn_inst_wf fn /\ cse_reachable_wf_ssa fn /\
 EVERY (\i. ~is_alloca_op i.inst_opcode) (fn_insts fn) /\
 EVERY inst_wf (fn_insts fn) /\ cse_stage_binding fn k /\
 MEM (ae,inst) (cse_canon_inputs (avail_analyze fn) fn) /\
 compute_canon_inst (dfg_build_function fn) (cse_stage_canon fn k) ae inst <>
   cse_stage_canon fn k /\
 cse_prefix ctx fn fuel0 s0 events (CseExec n bb s) /\
 get_instruction bb s.vs_inst_idx = SOME use /\
 events = pre ++ [CseStep m cb inst u t] ++ post /\
 cse_prefix ctx fn fuel0 s0 pre (CseExec m cb u) /\
 get_instruction cb u.vs_inst_idx = SOME inst /\
 inst.inst_outputs = [x] /\ EVERY (\ev. ~cse_event_writes ev x) post /\
 cse_path_preorder fn inst.inst_id use.inst_id /\ inst.inst_id <> use.inst_id /\
 step_inst m ctx inst u = OK t ==>
 ?r z. MEM r (fn_insts fn) /\ r.inst_outputs = [z] /\ r.inst_opcode <> PHI /\
   r.inst_id = canonical_id
     (compute_canon_inst (dfg_build_function fn) (cse_stage_canon fn k) ae inst)
     inst.inst_id /\
   cse_path_preorder fn r.inst_id inst.inst_id /\ lookup_var x s = lookup_var z s
Proof
 strip_tac >> drule compute_canon_inst_changed >> strip_tac >>
 `MEM inst (fn_insts fn)` by metis_tac[cse_canon_input_member] >>
 `MEM src (fn_insts fn) /\
  avail_source_birth (dfg_build_function fn) (mk_expr (dfg_build_function fn) inst) src src` by
   (irule cse_canon_input_source_birth >> metis_tac[]) >>
 `inst.inst_opcode = src.inst_opcode` by
   metis_tac[availExprProofsTheory.avail_source_birth_def, mk_expr_root_inversion] >>
 `inst_wf inst /\ inst_wf src` by metis_tac[listTheory.EVERY_MEM] >>
 `src.inst_opcode <> INVOKE /\ inst.inst_opcode <> PHI` by
   (conj_tac
    >- (strip_tac >> gvs[availExprProofsTheory.avail_source_birth_def,
          availExprDefsTheory.avail_nonidempotent_def,
          venomEffectsTheory.is_nonidempotent_def]) >>
    strip_tac >> gvs[venomInstTheory.is_pseudo_def]) >>
 `LENGTH src.inst_outputs = LENGTH inst.inst_outputs` by
   (irule inst_wf_same_opcode_output_length >> metis_tac[]) >>
 `LENGTH src.inst_outputs = 1` by simp[] >>
 `?y. src.inst_outputs = [y]` by gvs[listTheory.LENGTH_EQ_NUM_compute] >>
 `ae = ae_lookup_inst fn cb.bb_label u.vs_inst_idx` by
   (irule cse_canon_input_at_exec >> metis_tac[]) >>
 `cse_path_preorder fn src.inst_id inst.inst_id` by
   (drule_all cse_canon_input_location >> strip_tac >>
    qpat_x_assum `EL k' _ = inst` (SUBST_ALL_TAC o SYM) >>
    irule cse_avail_source_path_preorder >>
    goal_assum (drule_at Any) >> simp[availExprDefsTheory.ae_lookup_inst_def] >> metis_tac[]) >>
 simp[canonical_id_update] >>
 irule cse_stage_available_live_binding >> metis_tac[]
QED

Theorem cse_stage_binding_suc:
 wf_function fn /\ fn_inst_wf fn /\ cse_reachable_wf_ssa fn /\
 EVERY (\i. ~is_alloca_op i.inst_opcode) (fn_insts fn) /\
 cse_stage_binding fn k ==> cse_stage_binding fn (SUC k)
Proof
 strip_tac >>
 Cases_on `k < LENGTH (cse_canon_inputs (avail_analyze fn) fn)`
 >- (Cases_on `EL k (cse_canon_inputs (avail_analyze fn) fn)` >>
     rename1 `EL k (cse_canon_inputs (avail_analyze fn) fn) = (ae,i)` >>
     `MEM (ae,i) (cse_canon_inputs (avail_analyze fn) fn)` by metis_tac[listTheory.EL_MEM] >>
     `cse_stage_canon fn (SUC k) =
       compute_canon_inst (dfg_build_function fn) (cse_stage_canon fn k) ae i` by
       simp[cse_stage_canon_def, rich_listTheory.TAKE_SUC_BY_TAKE, listTheory.FOLDL_SNOC] >>
     Cases_on `compute_canon_inst (dfg_build_function fn) (cse_stage_canon fn k) ae i =
       cse_stage_canon fn k`
     >- (gvs[cse_stage_binding_def] >> metis_tac[]) >>
     `EVERY inst_wf (fn_insts fn)` by
       (gvs[venomWfTheory.fn_inst_wf_def, venomInstTheory.fn_insts_def] >>
        qpat_x_assum `!bb inst. _` mp_tac >> POP_ASSUM_LIST (K ALL_TAC) >>
        qspec_tac (`fn.fn_blocks`, `bbs`) >> Induct >>
        simp[venomInstTheory.fn_insts_blocks_def, listTheory.EVERY_MEM] >>
        fs[listTheory.EVERY_MEM] >> metis_tac[]) >>
     simp[cse_stage_binding_def] >> rpt gen_tac >> strip_tac >>
     Cases_on `d.inst_id = i.inst_id`
     >- (`d = i` by metis_tac[fn_inst_ids_distinct_inj, wf_function_def, cse_canon_input_member] >>
         `MEM (CseStep m db d u t) (pre ++ [CseStep m db d u t] ++ post)` by
           simp[listTheory.MEM_APPEND] >>
         `get_instruction db u.vs_inst_idx = SOME d /\ step_inst m ctx d u = OK t` by
           (drule_all cse_prefix_event_provenance >> simp[]) >>
         metis_tac[cse_stage_changed_live_binding]) >>
     `canonical_id (cse_stage_canon fn (SUC k)) d.inst_id =
       canonical_id (cse_stage_canon fn k) d.inst_id` by
       (drule compute_canon_inst_changed >> strip_tac >> simp[canonical_id_update]) >>
     qpat_x_assum `cse_stage_binding fn k` mp_tac >>
     simp[cse_stage_binding_def] >> metis_tac[]) >>
 `cse_stage_canon fn (SUC k) = cse_stage_canon fn k` by
   simp[cse_stage_canon_def, listTheory.TAKE_LENGTH_TOO_LONG] >>
 gvs[cse_stage_binding_def] >> metis_tac[]
QED

Theorem cse_stage_binding_all:
 wf_function fn /\ fn_inst_wf fn /\ cse_reachable_wf_ssa fn /\
 EVERY (\i. ~is_alloca_op i.inst_opcode) (fn_insts fn) ==>
 !k. cse_stage_binding fn k
Proof
 strip_tac >> Induct >- simp[cse_stage_binding_zero] >>
 irule cse_stage_binding_suc >> simp[]
QED

Theorem cse_stage_canon_final:
 cse_stage_canon fn (LENGTH (cse_canon_inputs (avail_analyze fn) fn)) =
 compute_canon (dfg_build_function fn) (avail_analyze fn) fn
Proof
 simp[cse_stage_canon_def, GSYM cse_canon_record_projection,
      cse_canon_record_compute_canon]
QED

Theorem cse_final_source_interval_operand_alignment:
 wf_function fn /\ fn_inst_wf fn /\ cse_reachable_wf_ssa fn /\
 EVERY (\i. ~is_alloca_op i.inst_opcode) (fn_insts fn) /\
 cse_prefix ctx fn fuel0 s0 events (CseExec n bb s) /\
 get_instruction bb s.vs_inst_idx = SOME inst /\ inst.inst_opcode <> PHI /\
 events = pre ++ [CseStep m sb src u v] ++ post /\
 cse_prefix ctx fn fuel0 s0 pre (CseExec m sb u) /\
 get_instruction sb u.vs_inst_idx = SOME src /\
 src.inst_opcode <> PHI /\ MEM src (fn_insts fn) /\
 ~is_pseudo src.inst_opcode /\ LENGTH src.inst_outputs <= 1 /\
 mk_expr (dfg_build_function fn) inst = mk_expr (dfg_build_function fn) src /\
 operand_ids_match (compute_canon (dfg_build_function fn) (avail_analyze fn) fn)
   (dfg_build_function fn) inst src /\
 (!j ph. LENGTH pre < j /\ j <= LENGTH events /\
   cse_prefix ctx fn fuel0 s0 (TAKE j events) ph ==>
   cse_phase_has_source fn ph e src) ==>
 MAP (\op. eval_operand op u) src.inst_operands =
 MAP (\op. eval_operand op s) inst.inst_operands \/
 (is_commutative inst.inst_opcode /\ LENGTH src.inst_operands = 2 /\
  LENGTH inst.inst_operands = 2 /\
  MAP (\op. eval_operand op u) src.inst_operands =
  REVERSE (MAP (\op. eval_operand op s) inst.inst_operands))
Proof
 strip_tac >>
 `cse_stage_binding fn (LENGTH (cse_canon_inputs (avail_analyze fn) fn))` by
   metis_tac[cse_stage_binding_all] >>
 `operand_ids_match (cse_stage_canon fn (LENGTH (cse_canon_inputs (avail_analyze fn) fn)))
    (dfg_build_function fn) inst src` by simp[cse_stage_canon_final] >>
 drule_all cse_stage_source_interval_operand_alignment >> simp[]
QED
