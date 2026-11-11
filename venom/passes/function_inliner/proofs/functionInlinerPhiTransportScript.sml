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

Theorem inline_pure1_id[local]:
  exec_pure1 f (inst with inst_id := k) s = exec_pure1 f inst s
Proof simp[exec_pure1_def]
QED

Theorem inline_pure2_id[local]:
  exec_pure2 f (inst with inst_id := k) s = exec_pure2 f inst s
Proof simp[exec_pure2_def]
QED

Theorem inline_pure3_id[local]:
  exec_pure3 f (inst with inst_id := k) s = exec_pure3 f inst s
Proof simp[exec_pure3_def]
QED

Theorem inline_read0_id[local]:
  exec_read0 f (inst with inst_id := k) s = exec_read0 f inst s
Proof simp[exec_read0_def]
QED

Theorem inline_read1_id[local]:
  exec_read1 f (inst with inst_id := k) s = exec_read1 f inst s
Proof simp[exec_read1_def]
QED

Theorem inline_write2_id[local]:
  exec_write2 f (inst with inst_id := k) s = exec_write2 f inst s
Proof simp[exec_write2_def]
QED

Theorem inline_gas_id[local]:
  exec_gas (inst with inst_id := k) s = exec_gas inst s
Proof simp[exec_gas_def]
QED

Theorem inline_ext_call_id[local]:
  exec_ext_call (inst with inst_id := k) s g a v off sz ro rs st =
  exec_ext_call inst s g a v off sz ro rs st
Proof simp[exec_ext_call_def]
QED

Theorem inline_delegatecall_id[local]:
  exec_delegatecall (inst with inst_id := k) s g a off sz ro rs =
  exec_delegatecall inst s g a off sz ro rs
Proof simp[exec_delegatecall_def]
QED

Theorem inline_create_id[local]:
  exec_create (inst with inst_id := k) s v off sz salt =
  exec_create inst s v off sz salt
Proof simp[exec_create_def]
QED

Theorem inline_step_base_id:
  inst.inst_opcode <> ALLOCA ==>
  step_inst_base (inst with inst_id := k) s = step_inst_base inst s
Proof
  Cases_on `inst.inst_opcode` >>
  first_assum (fn eq =>
    let val opc = rhs (concl eq)
        val branch = valOf (List.find
          (fn th => aconv opc (rhs (#1 (dest_imp (#2 (strip_forall (concl th)))))))
          (CONJUNCTS step_inst_base_opcode_eqs))
    in simp[branch, inline_pure1_id, inline_pure2_id, inline_pure3_id,
            inline_read0_id, inline_read1_id, inline_write2_id, inline_gas_id,
            inline_ext_call_id, inline_delegatecall_id, inline_create_id]
    end) >>
  simp[dretShapeDefsTheory.parse_dret_shape_def]
QED

Theorem inline_step_id:
  inst.inst_opcode <> ALLOCA ==>
  step_inst fuel ctx (inst with inst_id := k) s = step_inst fuel ctx inst s
Proof
  strip_tac >> rewrite_tac[step_inst_def] >>
  Cases_on `inst.inst_opcode = INVOKE`
  >- simp[decode_invoke_def] >>
  simp[inline_step_base_id]
QED

Theorem inline_fields_step:
  inline_inst_fields inst' = inline_inst_fields inst /\ inst.inst_opcode <> ALLOCA ==>
  step_inst fuel ctx inst' s = step_inst fuel ctx inst s
Proof
  strip_tac >>
  `inst' = inst with inst_id := inst'.inst_id` by
    (Cases_on `inst` >> Cases_on `inst'` >> gvs[inline_inst_fields_def, venomInstTheory.instruction_component_equality]) >>
  qpat_x_assum `inst' = _` SUBST1_TAC >>
  irule inline_step_id >> simp[]
QED

Theorem inline_fields_length:
  MAP inline_inst_fields xs = MAP inline_inst_fields ys ==> LENGTH xs = LENGTH ys
Proof
  metis_tac[LENGTH_MAP]
QED

Theorem inline_fields_phi_prefix:
  !xs ys. MAP inline_inst_fields xs = MAP inline_inst_fields ys ==>
    phi_prefix_length xs = phi_prefix_length ys
Proof
  Induct >> Cases_on `ys` >> simp[] >>
  rpt strip_tac >> gvs[inline_inst_fields_def, phi_prefix_length_def] >> metis_tac[]
QED

Theorem inline_invoke_suffix_nonphi:
  bb_well_formed bb /\ i < LENGTH bb.bb_instructions /\
  (EL i bb.bb_instructions).inst_opcode = INVOKE ==>
  EVERY (\inst. inst.inst_opcode <> PHI) (DROP (i+1) bb.bb_instructions)
Proof
  simp[EVERY_MEM] >> rpt strip_tac >>
  fs[MEM_EL] >>
  `n + (i+1) < LENGTH bb.bb_instructions` by decide_tac >>
  `(EL n (DROP (i+1) bb.bb_instructions)) =
    EL (n + (i+1)) bb.bb_instructions` by (irule EL_DROP >> decide_tac) >>
  fs[bb_well_formed_def] >>
  first_x_assum (qspecl_then [`i`, `n + (i+1)`] mp_tac) >> simp[] >> gvs[]
QED

Theorem inline_invoke_suffix_phi_prefix:
  bb_well_formed bb /\ i < LENGTH bb.bb_instructions /\
  (EL i bb.bb_instructions).inst_opcode = INVOKE ==>
  phi_prefix_length (DROP (i+1) bb.bb_instructions) = 0
Proof
  strip_tac >> drule_all inline_invoke_suffix_nonphi >>
  Cases_on `DROP (i+1) bb.bb_instructions` >>
  simp[phi_prefix_length_def]
QED

Theorem inline_invoke_suffix_eval_phis:
  bb_well_formed bb /\ i < LENGTH bb.bb_instructions /\
  (EL i bb.bb_instructions).inst_opcode = INVOKE ==>
  eval_phis s (DROP (i+1) bb.bb_instructions) = OK s
Proof
  strip_tac >> irule venomExecProofsTheory.eval_phis_no_phis >>
  irule inline_invoke_suffix_nonphi >> simp[]
QED

Theorem inline_fields_phi_prefix_contents:
  !xs ys. MAP inline_inst_fields xs = MAP inline_inst_fields ys ==>
    MAP inline_inst_fields (TAKE (phi_prefix_length xs) xs) =
    MAP inline_inst_fields (TAKE (phi_prefix_length ys) ys)
Proof
  rpt strip_tac >> drule inline_fields_phi_prefix >> strip_tac >>
  simp[MAP_TAKE]
QED

Theorem inline_phi_prefix_split:
  !i insts next. i < LENGTH insts /\ (EL i insts).inst_opcode <> PHI /\
    next.inst_opcode <> PHI ==>
    TAKE (phi_prefix_length (TAKE i insts ++ [next])) (TAKE i insts ++ [next]) =
    TAKE (phi_prefix_length insts) insts
Proof
  Induct >- (Cases_on `insts` >> simp[phi_prefix_length_def]) >>
  Cases_on `insts` >> simp[] >> rpt strip_tac >>
  Cases_on `h.inst_opcode = PHI` >> simp[phi_prefix_length_def]
QED

Theorem inline_caller_raw_phi_prefix:
  lookup_block lbl caller.fn_blocks = SOME call_bb /\
  lookup_block b caller.fn_blocks = SOME bb /\
  i < LENGTH call_bb.bb_instructions /\
  (EL i call_bb.bb_instructions).inst_opcode = INVOKE ==>
  ?raw. lookup_block b (inline_call_site p ret caller callee lbl i).fn_blocks = SOME raw /\
    raw.bb_label = bb.bb_label /\
    TAKE (phi_prefix_length raw.bb_instructions) raw.bb_instructions =
    TAKE (phi_prefix_length bb.bb_instructions) bb.bb_instructions
Proof
  strip_tac >> Cases_on `b = lbl`
  >- (gvs[] >> drule inline_call_site_lookup_call >>
      disch_then (qspecl_then [`ret`, `p`, `i`, `callee`] assume_tac) >>
      simp[] >> irule inline_phi_prefix_split >> simp[]) >>
  drule_all inline_call_site_lookup_other >>
  disch_then (qspecl_then [`ret`, `p`, `i`, `callee`] assume_tac) >>
  metis_tac[]
QED

Theorem inline_phi_prefix_repair_contents:
  !insts. TAKE (phi_prefix_length
      (MAP (\inst. if inst.inst_opcode <> PHI then inst else subst_label_inst old fresh inst) insts))
      (MAP (\inst. if inst.inst_opcode <> PHI then inst else subst_label_inst old fresh inst) insts) =
    MAP (subst_label_inst old fresh) (TAKE (phi_prefix_length insts) insts)
Proof
  Induct >> simp[] >> gen_tac >> Cases_on `h.inst_opcode = PHI` >>
  gvs[phi_prefix_length_def, subst_label_inst_def]
QED

Theorem inline_caller_produced_phi_prefix_fields:
  lookup_block lbl caller.fn_blocks = SOME call_bb /\
  lookup_block b caller.fn_blocks = SOME bb /\
  i < LENGTH call_bb.bb_instructions /\
  (EL i call_bb.bb_instructions).inst_opcode = INVOKE ==>
  ?tb. lookup_block b
      (renumber_fn_inst_ids (fix_inline_phis lbl ret rb
        (inline_call_site p ret caller callee lbl i))).fn_blocks = SOME tb /\
    MAP inline_inst_fields (TAKE (phi_prefix_length tb.bb_instructions) tb.bb_instructions) =
    MAP inline_inst_fields
      (if MEM bb.bb_label (bb_succs rb) then
        MAP (subst_label_inst lbl ret)
          (TAKE (phi_prefix_length bb.bb_instructions) bb.bb_instructions)
       else TAKE (phi_prefix_length bb.bb_instructions) bb.bb_instructions)
Proof
  strip_tac >> drule_all inline_caller_raw_phi_prefix >>
  disch_then (qspecl_then [`ret`, `p`, `callee`] strip_assume_tac) >>
  drule inline_final_lookup_fields >>
  disch_then (qspecl_then [`rb`, `lbl`, `ret`] strip_assume_tac) >>
  qexists `tb` >> simp[] >>
  drule inline_fields_phi_prefix_contents >>
  Cases_on `MEM bb.bb_label (bb_succs rb)` >> gvs[] >>
  simp[inline_phi_prefix_repair_contents]
QED

(* Freshness is needed only on the supported source namespace, not globally. *)
Theorem inline_resolve_phi_supported_repair:
  phi_well_formed ops /\
  EVERY (\op. !l. op = Label l ==> MEM l labels) ops /\
  MEM prev labels /\ ~MEM fresh labels ==>
  resolve_phi (if repair /\ prev = old then fresh else prev)
    (if repair then MAP (subst_label_op old fresh) ops else ops) =
  resolve_phi prev ops
Proof
  strip_tac >> Cases_on `repair` >> simp[] >>
  irule inline_resolve_phi_repair >>
  gvs[EVERY_MEM] >> metis_tac[]
QED
