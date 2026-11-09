(* Parallel PHI evaluation across the caller continuation predecessor repair. *)
Theory functionInlinerPhiTransport
Ancestors
  functionInlinerDefs functionInlinerOrigin functionInlinerSiteLayout simplifyCfgBypassPhi venomExecSemantics venomWf
  cfgTransform venomState passSimulationProps list

Theorem inline_resolve_phi_repair:
  phi_well_formed ops /\ ~MEM (Label fresh) ops /\ prev <> fresh ==>
  resolve_phi (if prev = old then fresh else prev)
    (MAP (subst_label_op old fresh) ops) = resolve_phi prev ops
Proof
  strip_tac >> Cases_on `old = fresh`
  >- (gvs[] >> AP_TERM_TAC >>
      irule LIST_EQ >> simp[EL_MAP] >> rpt strip_tac >>
      Cases_on `EL x ops` >> simp[subst_label_op_def] >> metis_tac[]) >>
  metis_tac[scfg_resolve_phi_replace]
QED

Theorem inline_eval_one_phi_repair:
  phi_well_formed inst.inst_operands /\
  ~MEM (Label fresh) inst.inst_operands /\ prev <> fresh ==>
  eval_one_phi (s with vs_prev_bb := SOME (if prev = old then fresh else prev))
    (subst_label_inst old fresh inst) =
  eval_one_phi (s with vs_prev_bb := SOME prev) inst
Proof
  strip_tac >> drule_all inline_resolve_phi_repair >>
  disch_then (qspec_then `old` assume_tac) >>
  simp[eval_one_phi_def, subst_label_inst_def] >>
  Cases_on `inst.inst_outputs` >> simp[] >>
  Cases_on `t` >> simp[] >>
  Cases_on `resolve_phi prev inst.inst_operands` >> simp[] >>
  Cases_on `x` >> simp[eval_operand_def, lookup_var_def]
QED

Theorem inline_phi_prefix_repair:
  !insts. phi_prefix_length
    (MAP (\inst. if inst.inst_opcode <> PHI then inst
                else subst_label_inst old fresh inst) insts) =
    phi_prefix_length insts
Proof
  Induct >> simp[] >> Cases_on `h.inst_opcode = PHI` >>
  gvs[phi_prefix_length_def, subst_label_inst_def]
QED

Theorem inline_eval_phis_repair:
  !insts s prev old fresh.
  EVERY (\inst. inst.inst_opcode = PHI ==>
    phi_well_formed inst.inst_operands /\ ~MEM (Label fresh) inst.inst_operands) insts /\
  prev <> fresh ==>
  eval_phis (s with vs_prev_bb := SOME (if prev = old then fresh else prev))
    (MAP (\inst. if inst.inst_opcode <> PHI then inst
                else subst_label_inst old fresh inst) insts) =
  case eval_phis (s with vs_prev_bb := SOME prev) insts of
    OK u => OK (u with vs_prev_bb := SOME (if prev = old then fresh else prev))
  | err => err
Proof
  Induct >> simp[eval_phis_def] >> rpt gen_tac >> strip_tac >>
  Cases_on `h.inst_opcode = PHI`
  >- (gvs[] >>
      `eval_one_phi (s with vs_prev_bb := SOME (if prev = old then fresh else prev))
         (subst_label_inst old fresh h) =
       eval_one_phi (s with vs_prev_bb := SOME prev) h` by
        (irule inline_eval_one_phi_repair >> simp[]) >>
      first_x_assum (qspecl_then [`s`, `prev`, `old`, `fresh`] mp_tac) >>
      simp[] >> strip_tac >>
      simp[eval_phis_def, subst_label_inst_def] >>
      Cases_on `eval_one_phi (s with vs_prev_bb := SOME prev) h` >> simp[] >>
      PairCases_on `x` >> simp[] >>
      Cases_on `eval_phis (s with vs_prev_bb := SOME prev) insts` >>
      gvs[update_var_def]) >>
  simp[eval_phis_def]
QED

Theorem inline_fix_phis_lookup:
  lookup_block l (fix_inline_phis old fresh ret fn).fn_blocks =
  OPTION_MAP (\bb. if MEM bb.bb_label (bb_succs ret) then
    bb with bb_instructions := MAP (\inst.
      if inst.inst_opcode <> PHI then inst else subst_label_inst old fresh inst)
      bb.bb_instructions else bb) (lookup_block l fn.fn_blocks)
Proof
  simp[fix_inline_phis_def] >> irule lookup_block_map >>
  gen_tac >> BETA_TAC >> IF_CASES_TAC >> simp[]
QED

Theorem inline_fix_phis_lookup_some:
  lookup_block l fn.fn_blocks = SOME bb ==>
  lookup_block l (fix_inline_phis old fresh ret fn).fn_blocks =
  SOME (if MEM bb.bb_label (bb_succs ret) then
    bb with bb_instructions := MAP (\inst.
      if inst.inst_opcode <> PHI then inst else subst_label_inst old fresh inst)
      bb.bb_instructions else bb)
Proof
  simp[inline_fix_phis_lookup]
QED

Theorem inline_fix_phis_nonphi:
  inst.inst_opcode <> PHI ==>
  (if inst.inst_opcode <> PHI then inst else subst_label_inst old fresh inst) = inst
Proof
  simp[]
QED

(* Static closure discharges the operand freshness side condition. The
   runtime predecessor inequality remains explicit, even for closed PHIs. *)
Theorem inline_eval_phis_closed_repair:
  inliner_phi_labels_closed fn /\ fn_inst_wf fn /\
  MEM bb fn.fn_blocks /\ ~MEM fresh (fn_labels fn) /\ prev <> fresh ==>
  eval_phis (s with vs_prev_bb := SOME (if prev = old then fresh else prev))
    (MAP (\inst. if inst.inst_opcode <> PHI then inst
                else subst_label_inst old fresh inst) bb.bb_instructions) =
  case eval_phis (s with vs_prev_bb := SOME prev) bb.bb_instructions of
    OK u => OK (u with vs_prev_bb := SOME (if prev = old then fresh else prev))
  | err => err
Proof
  strip_tac >> irule inline_eval_phis_repair >> simp[EVERY_MEM] >>
  rpt strip_tac
  >- (gvs[fn_inst_wf_def, EVERY_MEM] >>
      `inst_wf inst` by metis_tac[] >> gvs[inst_wf_def]) >>
  `MEM inst (fn_insts fn)` by
    (simp[venomInstTheory.fn_insts_def,
       unitShapeDefsTheory.MEM_fn_insts_blocks_iff] >> metis_tac[]) >>
  metis_tac[inliner_phi_labels_fresh]
QED

Theorem inline_eval_phis_none_repair:
  eval_phis (s with vs_prev_bb := NONE)
    (MAP (\inst. if inst.inst_opcode <> PHI then inst
                else subst_label_inst old fresh inst) insts) =
  eval_phis (s with vs_prev_bb := NONE) insts
Proof
  Cases_on `insts` >> simp[eval_phis_def] >>
  Cases_on `h.inst_opcode = PHI` >>
  simp[eval_phis_def, subst_label_inst_def, eval_one_phi_def] >>
  Cases_on `h.inst_outputs` >> simp[] >> Cases_on `t` >> simp[]
QED

Theorem inline_eval_phis_optional_repair:
  inliner_phi_labels_closed fn /\ fn_inst_wf fn /\
  MEM bb fn.fn_blocks /\ ~MEM fresh (fn_labels fn) /\
  (!prev. p = SOME prev ==> MEM prev (fn_labels fn)) ==>
  eval_phis (s with vs_prev_bb := OPTION_MAP (\l. if l = old then fresh else l) p)
    (MAP (\inst. if inst.inst_opcode <> PHI then inst
                else subst_label_inst old fresh inst) bb.bb_instructions) =
  case eval_phis (s with vs_prev_bb := p) bb.bb_instructions of
    OK u => OK (u with vs_prev_bb := OPTION_MAP (\l. if l = old then fresh else l) p)
  | err => err
Proof
  strip_tac >> Cases_on `p`
  >- (simp[inline_eval_phis_none_repair] >> Cases_on `bb.bb_instructions` >>
      simp[eval_phis_def] >> Cases_on `h.inst_opcode = PHI` >>
      simp[eval_phis_def, eval_one_phi_def] >>
      Cases_on `h.inst_outputs` >> simp[] >> Cases_on `t` >> simp[]) >>
  simp[] >> irule inline_eval_phis_closed_repair >> simp[] >> metis_tac[]
QED

(* Final layout: PHI repair followed by instruction-ID renumbering. *)
Theorem inline_final_lookup_fields:
  lookup_block l fn.fn_blocks = SOME bb ==>
  ?tb. lookup_block l (renumber_fn_inst_ids (fix_inline_phis old fresh rb fn)).fn_blocks =
      SOME tb /\
    tb.bb_label = bb.bb_label /\
    MAP inline_inst_fields tb.bb_instructions =
      MAP inline_inst_fields
        (if MEM bb.bb_label (bb_succs rb) then
           MAP (\inst. if inst.inst_opcode <> PHI then inst
                      else subst_label_inst old fresh inst) bb.bb_instructions
         else bb.bb_instructions)
Proof
  strip_tac >> drule inline_fix_phis_lookup_some >>
  disch_then (qspecl_then [`rb`, `old`, `fresh`] assume_tac) >>
  drule inline_renumber_lookup_some >>
  disch_then strip_assume_tac >> qexists `bb'` >>
  Cases_on `MEM bb.bb_label (bb_succs rb)` >> gvs[]
QED

(* Raw lookup premise is supplied by the existing call/clone/return/other
   lookup cases. This theorem discharges the executable inline_one_site
   wrapper and both final transformations in one place. *)
Theorem inline_one_site_lookup_fields:
  find_invoke_site callee.fn_name caller.fn_blocks = SOME (lbl,i) /\
  p = inline_prefix ist.is_inline_count /\
  ret = return_block_label p ist.is_label_counter /\
  lookup_block lbl caller.fn_blocks = SOME source_bb /\
  ~MEM ret (fn_labels caller) /\
  lookup_block l (inline_call_site p ret caller callee lbl i).fn_blocks = SOME bb /\
  inline_one_site caller callee ist = SOME (fn',ist') ==>
  ?tb. lookup_block l fn'.fn_blocks = SOME tb /\ tb.bb_label = bb.bb_label /\
    MAP inline_inst_fields tb.bb_instructions =
      MAP inline_inst_fields
        (if MEM bb.bb_label
              (bb_succs <|bb_label := ret;
                bb_instructions := DROP (i+1) source_bb.bb_instructions|>) then
           MAP (\inst. if inst.inst_opcode <> PHI then inst
                      else subst_label_inst lbl ret inst) bb.bb_instructions
         else bb.bb_instructions)
Proof
  strip_tac >>
  drule_all inline_call_site_lookup_return >>
  disch_then (qspecl_then [`p`, `i`, `callee`] assume_tac) >>
  gvs[inline_one_site_def] >>
  irule inline_final_lookup_fields >> simp[]
QED
