(*
 * FmpLowering's step contract: the structural half of its O1 pass
 * contract.  Lowering any function of a well-shaped observed unit keeps
 * the O1 function shape, takes new instruction ids and labels from the
 * supply, maps no labels, and keeps the supply's instruction-id record.
 *
 * TOP-LEVEL:
 *   fmp_step_contract  - o1_step_contract for VP_FmpLowering
 *)

Theory fmpStepContract
Ancestors
  o1PassContract fmpLowerDefs venomPassDispatcher
  fmpStepBridge fmpStepShape fmpStepStructural fmpStepRestrictions fmpStepLayout
  fmpWfDefs callLayoutDefs fmpAnalysisDefs fcgDefs venomWf venomInst list
  rich_list

(* Why it holds (intuition, not a prescribed proof).

   A sealed input comes back unchanged.  An unsealed one either only gets
   its signature sealed, or is rewritten: DALLOCA becomes ADD/NOT/AND/BUMP
   on a runner variable, an INVOKE of a callee taking the FMP passes the
   runner as a hidden argument, reclaim points get an ASSIGN of the
   runner, and the entry block gets the root (INITIAL_FMP for the context
   entry, FMP_PARAM otherwise, placed after the user parameters) and, for
   a non-entry function, its RETPC_PARAM re-indexed.  Every new
   instruction id comes from fresh_inst_id on the supply and every new
   variable from fresh_ir_var; no block or label is added, so the label
   map is empty.  The first block has no PHI (first_block_no_phi), so the
   inserted root keeps the PHI prefix of bb_well_formed. *)

Theorem fmp_step_contract:
  o1_step_contract rpolicy (CFP_Simple VP_FmpLowering)
Proof
  simp[o1_step_contract_def] >> rpt strip_tac >>
  drule_all fmp_fn_pass_step_input >> strip_tac >>
  drule fmp_fn_pass_step_result >> strip_tac >>
  rpt conj_tac
  >- (simp[o1_fn_shape_def] >> rpt conj_tac
      >- metis_tac[fmp_lower_function_wf_function]
      >- metis_tac[fmp_lower_function_inst_wf, o1_fn_shape_def]
      >- metis_tac[fmp_lower_function_fn_shape_ok]
      >- metis_tac[fmp_lower_function_first_block_no_preds, o1_fn_shape_def]
      >- metis_tac[fmp_lower_function_first_block_no_phi, o1_fn_shape_def]
      >- metis_tac[fmp_lower_function_invoke_ok, o1_fn_shape_def]
      >- metis_tac[fmp_lower_function_label_refs_ok, o1_fn_shape_def]
      >- metis_tac[fmp_lower_function_no_dret]
      >- metis_tac[fmp_lower_function_dalloca_nonopaque]
      >- metis_tac[fmp_lower_function_entry_restrictions] >>
      metis_tac[SRULE[] fmp_lower_function_nonentry_restrictions])
  >- metis_tac[fmp_lower_function_fresh_names]
  >- simp[label_map_sources_ok_def] >>
  metis_tac[fmp_lower_function_inst_ok]
QED

(* The step contract of FmpLowering's walk run: it adds no ALLOCA, so the
   function row (no ALLOCA from row 3 on) carries over. *)
(* Every successful lowering is checked against its sealed signature, whose
   syntax demands the canonical parameter prefix. *)
Theorem fmp_lower_function_canonical_param_prefix:
  fmp_lower_function ctx s fn = SOME (fn',s') ==> canonical_param_prefix fn'
Proof
  simp[fmp_lower_function_def, fmp_lower_function_with_info_def,
       AllCaseEqs()] >> rpt strip_tac >>
  gvs[fmp_signature_matches_fn_def, fmp_signature_syntax_wf_def] >>
  drule fmp_checked_seal_some >> strip_tac >>
  gvs[fmp_signature_syntax_wf_def]
QED

Theorem is_pseudo_param_or_phi:
  is_pseudo op <=> op = PHI \/ is_param_opcode op
Proof
  Cases_on `op` >> simp[is_pseudo_def, is_param_opcode_def]
QED

Theorem pseudos_prefix_split:
  bb.bb_instructions = xs ++ ys /\
  EVERY (\i. is_pseudo i.inst_opcode) xs /\
  EVERY (\i. ~is_pseudo i.inst_opcode) ys ==> pseudos_prefix bb
Proof
  rw[pseudos_prefix_def] >> gvs[EVERY_EL] >>
  Cases_on `i < LENGTH xs` >> gvs[EL_APPEND1] >>
  `LENGTH xs <= j` by decide_tac >>
  `j - LENGTH xs < LENGTH ys` by decide_tac >>
  gvs[EL_APPEND2]
QED

Theorem canonical_after_fmp_split:
  !k insts. canonical_after_fmp k insts ==>
    ?xs ys. insts = xs ++ ys /\
      EVERY (\i. is_param_opcode i.inst_opcode) xs /\ no_param_insts ys
Proof
  Cases_on `insts`
  >- (rpt strip_tac >> qexistsl [`[]`, `[]`] >> simp[no_param_insts_def]) >>
  rpt gen_tac >> simp[canonical_after_fmp_def] >>
  Cases_on `h.inst_opcode = RETPC_PARAM` >> fs[] >> strip_tac
  >- (qexistsl [`[h]`, `t`] >> gvs[param_inst_at_def]) >>
  qexistsl [`[]`, `h::t`] >> gvs[]
QED

Theorem canonical_entry_params_split:
  !k insts. canonical_entry_params_from k insts ==>
    ?xs ys. insts = xs ++ ys /\
      EVERY (\i. is_param_opcode i.inst_opcode) xs /\ no_param_insts ys
Proof
  Induct_on `insts`
  >- (rpt strip_tac >> qexistsl [`[]`, `[]`] >> simp[no_param_insts_def]) >>
  rpt gen_tac >> simp[canonical_entry_params_from_def] >>
  Cases_on `h.inst_opcode = PARAM` >> fs[] >> strip_tac
  >- (first_x_assum drule >> strip_tac >>
      qexistsl [`h::xs`, `ys`] >> gvs[param_inst_at_def]) >>
  Cases_on `h.inst_opcode = FMP_PARAM` >> gvs[]
  >- (drule canonical_after_fmp_split >> strip_tac >>
      qexistsl [`h::xs`, `ys`] >> gvs[param_inst_at_def]) >>
  Cases_on `h.inst_opcode = RETPC_PARAM` >> gvs[]
  >- (qexistsl [`[h]`, `insts`] >> gvs[param_inst_at_def]) >>
  qexistsl [`[]`, `h::insts`] >> gvs[]
QED

(* The canonical parameter prefix, with no PHI in the first block and the
   PHI prefix of every block, makes the pseudo instructions a prefix. *)
Theorem canonical_param_prefix_pseudos:
  canonical_param_prefix fn /\ wf_function fn /\ first_block_no_phi fn ==>
  fn_pseudos_prefix fn /\
  EVERY (\bb. no_param_insts bb.bb_instructions) (TL fn.fn_blocks)
Proof
  strip_tac >>
  Cases_on `fn.fn_blocks` >> gvs[canonical_param_prefix_def] >>
  simp[fn_pseudos_prefix_def] >> rpt strip_tac >> gvs[]
  >- (drule canonical_entry_params_split >> strip_tac >>
      irule pseudos_prefix_split >> qexistsl [`xs`, `ys`] >>
      gvs[first_block_no_phi_def, no_param_insts_def, EVERY_MEM,
          is_pseudo_param_or_phi] >>
      rpt strip_tac >> res_tac >> gvs[is_param_opcode_def]) >>
  `bb_well_formed bb` by gvs[wf_function_def] >>
  gvs[EVERY_MEM, no_param_insts_def] >>
  `!i. MEM i bb.bb_instructions ==> ~is_param_opcode i.inst_opcode` by
    metis_tac[] >>
  gvs[pseudos_prefix_def, bb_well_formed_def, is_pseudo_param_or_phi] >>
  metis_tac[MEM_EL]
QED

(* ===== FmpLowering on a function that needs no FMP ===== *)

Theorem fmp_opcode_info_raw:
  (fmp_opcode_needs_fmp op ==> is_raw_fmp_opcode op) /\
  (fmp_opcode_publishes_fmp op ==> is_raw_fmp_opcode op)
Proof
  rw[fmp_opcode_needs_fmp_def, fmp_opcode_publishes_fmp_def] >>
  simp[is_raw_fmp_opcode_def]
QED

Theorem fmp_scan_insts_no_raw:
  !insts. EVERY (\i. ~is_raw_fmp_opcode i.inst_opcode) insts ==>
          fmp_scan_insts insts = fmp_info_bottom
Proof
  Induct >> rw[fmp_scan_insts_def] >>
  `~fmp_opcode_needs_fmp h.inst_opcode /\
   ~fmp_opcode_publishes_fmp h.inst_opcode` by metis_tac[fmp_opcode_info_raw] >>
  simp[fmp_info_join_def, fmp_info_bottom_def]
QED

Theorem fmp_direct_info_no_raw:
  no_raw_fmp_ops fn ==> fmp_direct_info fn = fmp_info_bottom
Proof
  rw[no_raw_fmp_ops_def, fmp_direct_info_def] >>
  irule fmp_scan_insts_no_raw >> simp[EVERY_MEM]
QED

Theorem fmp_collect_invokes_targets:
  !insts targets t.
    fmp_collect_invokes insts = SOME targets /\ MEM t targets ==>
    MEM t (MAP FST (get_invoke_targets insts))
Proof
  Induct >> simp[fmp_collect_invokes_def, get_invoke_targets_def] >>
  rw[fmp_invoke_target_def] >> gvs[AllCaseEqs()] >> metis_tac[]
QED

Theorem fmp_join_target_info_unneeded:
  !targets acc out.
    fmp_join_target_info infos targets acc = SOME out /\
    (!t. MEM t targets ==>
         ?i. FLOOKUP infos t = SOME i /\ ~i.fi_needs_fmp) ==>
    out.fi_needs_fmp = acc.fi_needs_fmp /\
    out.fi_publishes_fmp = acc.fi_publishes_fmp
Proof
  Induct >> simp[fmp_join_target_info_def] >> rpt gen_tac >> strip_tac >>
  gvs[AllCaseEqs()] >>
  `~info.fi_needs_fmp` by (first_x_assum (qspec_then `h` mp_tac) >> simp[]) >>
  first_x_assum drule >> simp[fmp_info_join_def]
QED

Theorem get_invoke_targets_mem:
  !insts name. MEM name (MAP FST (get_invoke_targets insts)) ==>
    ?inst rest. MEM inst insts /\ inst.inst_opcode = INVOKE /\
                inst.inst_operands = Label name :: rest
Proof
  Induct >> rw[get_invoke_targets_def] >> BasicProvers.EVERY_CASE_TAC >> gvs[] >>
  metis_tac[]
QED

(* An unsealed input with no raw FMP operation whose callees take no FMP
   parameter needs no FMP and publishes none: every analysed target is an
   INVOKE label, which the input boundary resolves to a sealed callee
   whose information is its signature's. *)
Theorem fmp_lower_input_no_param_info:
  fmp_info_valid ctx infos /\ fmp_lower_input infos ctx fn /\
  no_raw_fmp_ops fn /\ EVERY fmp_sig_no_param ctx.ctx_functions /\
  FLOOKUP infos fn.fn_name = SOME info ==>
  ~info.fi_needs_fmp /\ ~info.fi_publishes_fmp
Proof
  strip_tac >>
  `MEM fn ctx.ctx_functions` by
    (fs[fmp_lower_input_def] >> metis_tac[lookup_function_MEM]) >>
  `fn.fn_fmp_signature = NONE` by fs[fmp_lower_input_def] >>
  fs[fmp_info_valid_def] >>
  first_x_assum (qspec_then `fn` mp_tac) >> simp[] >> strip_tac >>
  drule fmp_join_target_info_unneeded >> impl_tac
  >- (rpt strip_tac >>
      gvs[fmp_function_targets_def, AllCaseEqs()] >>
      drule_all fmp_collect_invokes_targets >> strip_tac >>
      drule get_invoke_targets_mem >> strip_tac >>
      `fmp_lower_inst_shape infos ctx inst` by
        (gvs[fmp_lower_input_def, fmp_lower_blocks_shape_def,
             fmp_lower_insts_shape_def, EVERY_MEM, fn_insts_def,
             unitShapeDefsTheory.MEM_fn_insts_blocks_iff] >> metis_tac[]) >>
      gvs[fmp_lower_inst_shape_def, optionTheory.IS_SOME_EXISTS,
          fmp_resolve_invoke_def, AllCaseEqs()] >>
      drule lookup_function_MEM >> strip_tac >>
      gvs[EVERY_MEM, fmp_sig_no_param_def] >>
      res_tac >> simp[fmp_info_of_signature_def]) >>
  simp[fmp_direct_info_no_raw, fmp_info_bottom_def]
QED

(* On such a function the lowering leaves the blocks as they are: a
   sealed input comes back unchanged, and an unsealed one is only sealed,
   with no FMP parameter. *)
Theorem fmp_lower_function_no_param:
  fmp_lower_function ctx s fn = SOME (fn',s') /\ no_raw_fmp_ops fn /\
  EVERY fmp_sig_no_param ctx.ctx_functions ==>
  (?x. fn' = fn with fn_fmp_signature := x) /\ fmp_sig_no_param fn'
Proof
  strip_tac >> fs[fmp_lower_function_def, AllCaseEqs()] >>
  qpat_x_assum `fmp_lower_function_with_info _ _ _ _ = _` mp_tac >>
  simp[fmp_lower_function_with_info_def] >>
  Cases_on `fn.fn_fmp_signature` >> simp[]
  >- (strip_tac >>
      `?info. FLOOKUP infos fn.fn_name = SOME info` by
        (fs[fmp_lower_input_def] >>
         Cases_on `FLOOKUP infos fn.fn_name` >> fs[]) >>
      `~info.fi_needs_fmp /\ ~info.fi_publishes_fmp` by
        metis_tac[fmp_lower_input_no_param_info] >>
      gvs[AllCaseEqs(), fmp_checked_seal_def, fmp_seal_def,
          fmp_sig_no_param_def] >>
      simp[venomInstTheory.ir_function_component_equality]) >>
  rw[] >- (qexists `SOME x` >>
           simp[venomInstTheory.ir_function_component_equality]) >>
  `MEM fn ctx.ctx_functions` by metis_tac[lookup_function_MEM] >>
  fs[EVERY_MEM]
QED

Theorem fmp_step_contract_at:
  o1_step_contract_at 3 rpolicy (CFP_Simple VP_FmpLowering)
Proof
  irule o1_step_contract_at_preserve >> simp[fmp_step_contract] >>
  rpt strip_tac >> drule fmp_fn_pass_step_result >> strip_tac >>
  drule_all fmp_fn_pass_step_input >> strip_tac >>
  `wf_function out.fpo_function /\ first_block_no_phi out.fpo_function` by
    metis_tac[fmp_lower_function_wf_function,
              fmp_lower_function_first_block_no_phi, o1_fn_shape_def] >>
  drule fmp_lower_function_canonical_param_prefix >> strip_tac >>
  drule_all canonical_param_prefix_pseudos >> strip_tac >>
  `fmp_sig_no_param out.fpo_function /\ make_ssa_input_ok out.fpo_function` by
    (drule fmp_lower_function_no_param >> impl_tac >- fs[o1_fn_row_def] >>
     strip_tac >> fs[o1_fn_row_def]) >>
  fs[o1_fn_row_def] >> metis_tac[fmp_lower_function_no_alloca]
QED
