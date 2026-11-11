(*
 * Encoding well-formedness of generated assembly.
 *
 * TOP-LEVEL:
 *   codegen_assembly_asm_encoding_wf — codegen output of an OFFSET-free
 *     (unit_shape_ok) unit is asm_encoding_wf (codegen_assembly checks the
 *     program fits the 2-byte label pushes).
 *   generate_context_plan_no_push_ofst — without OFFSET instructions the
 *     stack plan contains no SOPushOfst.
 *)

Theory codegenEncodingWf
Ancestors
  codegen asmWf asmTargetSafety symbolResolve planExec asmIR stackPlanGen
  stackPlanTypes stackPlanOps unitShapeDefs venomInst list rich_list arithmetic finite_map

(* ===== Encoded sizes ===== *)

Theorem encode_num_bytes_length_le_symbol_size:
  n < 65536 ==> LENGTH (encode_num_bytes n) <= symbol_size
Proof
  rw[Once encode_num_bytes_def, symbol_size_def] >>
  rw[Once encode_num_bytes_def] >>
  `n DIV 256 < 256` by simp[DIV_LT_X] >>
  `n DIV 256 DIV 256 = 0` by simp[DIV_EQ_0] >>
  simp[Once encode_num_bytes_def]
QED

Theorem compute_label_offsets_snoc:
  compute_label_offsets (SNOC inst prog) =
    (FST (compute_label_offsets prog) + asm_inst_size inst,
     case inst of
       AsmLabel lbl =>
         SND (compute_label_offsets prog) |+
           (lbl, FST (compute_label_offsets prog))
     | AsmDataHeader lbl =>
         SND (compute_label_offsets prog) |+
           (lbl, FST (compute_label_offsets prog))
     | _ => SND (compute_label_offsets prog))
Proof
  simp[compute_label_offsets_def, FOLDL_SNOC] >>
  Cases_on `FOLDL (λ(pc,labels) inst.
              (pc + asm_inst_size inst,
               case inst of
                 AsmLabel lbl => labels |+ (lbl,pc)
               | AsmDataHeader lbl => labels |+ (lbl,pc)
               | _ => labels)) (0,FEMPTY) prog` >>
  simp[]
QED

(* Every label offset is at most the total instruction size. *)
Theorem compute_label_offsets_bound:
  !prog.
    FST (compute_label_offsets prog) = SUM (MAP asm_inst_size prog) /\
    !lbl off. FLOOKUP (SND (compute_label_offsets prog)) lbl = SOME off ==>
              off <= SUM (MAP asm_inst_size prog)
Proof
  ho_match_mp_tac SNOC_INDUCT >>
  conj_tac >- simp[compute_label_offsets_def] >>
  rpt gen_tac >> strip_tac >>
  simp[compute_label_offsets_snoc, MAP_SNOC, SUM_SNOC] >>
  Cases_on `x` >> simp[FLOOKUP_UPDATE] >> rw[] >> res_tac >> simp[]
QED

(* asm_inst_size_def alone names asmIR's datatype size function. *)
Theorem asm_inst_size_le_encode[local]:
  (!name. inst = AsmOp name ==> IS_SOME (evm_opcode_byte name)) ==>
  asm_inst_size inst <= LENGTH (encode_inst offsets inst)
Proof
  Cases_on `inst` >>
  simp[encode_inst_def, symbolResolveTheory.asm_inst_size_def]
  >- (strip_tac >> Cases_on `evm_opcode_byte s` >> gvs[])
  >- (Cases_on `l` >> simp[encode_inst_def]) >>
  rpt CASE_TAC >> rw[pad_bytes_def, symbol_size_def]
QED

(* ===== No SOPushOfst without OFFSET ===== *)

Theorem spill_fold_no_push_ofst[local]:
  !items acc_ops offsets al ops offsets' al'.
  FOLDL (\(ops, offs, al) item.
    (\(off, al'). (ops ++ [SOSpill off], SNOC off offs, al'))
      (alloc_spill_slot al))
    (acc_ops, offsets, al) items = (ops, offsets', al') /\
  ~MEM (SOPushOfst lbl d) acc_ops ==>
  ~MEM (SOPushOfst lbl d) ops
Proof
  Induct >> simp[] >> rpt gen_tac >>
  Cases_on `alloc_spill_slot al` >> simp[] >>
  strip_tac >>
  first_x_assum (qspec_then `acc_ops ++ [SOSpill q]` mp_tac) >>
  simp[] >> disch_then drule >> simp[]
QED

Theorem do_swap_no_push_ofst[local]:
  do_swap dist ps = (ops, ps') ==>
  !lbl d. ~MEM (SOPushOfst lbl d) ops
Proof
  simp[do_swap_def] >>
  Cases_on `dist = 0` >- simp[] >>
  Cases_on `dist <= 16` >- (rw[] >> simp[]) >>
  simp[] >> pairarg_tac >> simp[] >> strip_tac >> gvs[] >>
  simp[MEM_MAP, PULL_EXISTS] >>
  rpt gen_tac >> drule spill_fold_no_push_ofst >> simp[]
QED

Theorem popmany_fold_no_push_ofst[local]:
  !xs acc_ops ps ops ps'.
  FOLDL (\(ops, ps) v.
    case stack_get_depth v ps.ps_stack of
      NONE => (ops, ps)
    | SOME dist =>
        (\(swap_ops, ps').
          (ops ++ swap_ops ++ [SOPop 1],
           ps' with ps_stack := stack_pop 1 ps'.ps_stack))
        (if dist = 0 then ([], ps) else do_swap dist ps))
    (acc_ops, ps) xs = (ops, ps') /\
  ~MEM (SOPushOfst lbl d) acc_ops ==>
  ~MEM (SOPushOfst lbl d) ops
Proof
  Induct >> simp[] >> rpt gen_tac >>
  Cases_on `stack_get_depth h ps.ps_stack` >> simp[]
  >- metis_tac[] >>
  Cases_on `x = 0` >> simp[]
  >- (strip_tac >>
      first_x_assum (qspec_then `acc_ops ++ [SOPop 1]` mp_tac) >>
      simp[] >> disch_then drule >> simp[]) >>
  Cases_on `do_swap x ps` >> simp[] >> strip_tac >>
  first_x_assum (qspec_then `acc_ops ++ q ++ [SOPop 1]` mp_tac) >>
  simp[] >> disch_then drule >>
  drule do_swap_no_push_ofst >> simp[]
QED

Theorem popmany_individual_no_push_ofst[local]:
  popmany_individual to_pop ps = (ops, ps') ==>
  !lbl d. ~MEM (SOPushOfst lbl d) ops
Proof
  simp[popmany_individual_def] >> strip_tac >> rpt gen_tac >>
  drule popmany_fold_no_push_ofst >> simp[]
QED

Theorem popmany_plan_no_push_ofst[local]:
  popmany_plan to_pop ps = (ops, ps') ==>
  !lbl d. ~MEM (SOPushOfst lbl d) ops
Proof
  Cases_on `to_pop` >> simp[popmany_plan_def] >>
  rpt IF_CASES_TAC >> simp[]
  >- (pairarg_tac >> simp[] >> strip_tac >> gvs[] >>
      drule do_swap_no_push_ofst >> simp[])
  >> metis_tac[popmany_individual_no_push_ofst]
QED

Theorem optimistic_swap_plan_no_push_ofst[local]:
  optimistic_swap_plan dfg inst live term ps = (ops, ps') ==>
  !lbl d. ~MEM (SOPushOfst lbl d) ops
Proof
  simp[optimistic_swap_plan_def] >> rpt IF_CASES_TAC >> simp[] >>
  Cases_on `stack_get_depth (Var (LAST live)) ps.ps_stack` >> simp[] >>
  metis_tac[do_swap_no_push_ofst]
QED

Theorem do_spill_tos_no_push_ofst[local]:
  do_spill_tos ps = (ops, ps') ==>
  !lbl d. ~MEM (SOPushOfst lbl d) ops
Proof
  simp[do_spill_tos_def] >> pairarg_tac >> simp[] >> rw[] >> simp[]
QED

Theorem do_spill_at_no_push_ofst[local]:
  do_spill_at dist ps = (ops, ps') ==>
  !lbl d. ~MEM (SOPushOfst lbl d) ops
Proof
  simp[do_spill_at_def] >> IF_CASES_TAC >> simp[]
  >- metis_tac[do_spill_tos_no_push_ofst] >>
  pairarg_tac >> simp[] >> strip_tac >> gvs[] >>
  drule do_spill_tos_no_push_ofst >> simp[]
QED

Theorem do_restore_no_push_ofst[local]:
  do_restore op ps = (ops, ps') ==>
  !lbl d. ~MEM (SOPushOfst lbl d) ops
Proof
  simp[do_restore_def] >>
  Cases_on `FLOOKUP ps.ps_spilled op` >> simp[] >> rw[] >> simp[]
QED

Theorem restore_spilled_plan_no_push_ofst[local]:
  !ops0 ps ops ps'.
    restore_spilled_plan ops0 ps = (ops, ps') ==>
    !lbl d. ~MEM (SOPushOfst lbl d) ops
Proof
  Induct >> simp[restore_spilled_plan_def] >> rpt gen_tac >>
  rpt (pairarg_tac >> gvs[]) >> strip_tac >> gvs[] >>
  imp_res_tac do_restore_no_push_ofst >> metis_tac[]
QED

Theorem do_dup_no_push_ofst[local]:
  do_dup dist ps = (ops, ps') ==>
  !lbl d. ~MEM (SOPushOfst lbl d) ops
Proof
  simp[do_dup_def] >> IF_CASES_TAC >- (rw[] >> simp[]) >>
  pairarg_tac >> simp[] >> strip_tac >> gvs[] >>
  simp[MEM_FLAT, MEM_MAP, PULL_EXISTS] >>
  rpt IF_CASES_TAC >> simp[] >> rpt gen_tac >>
  drule spill_fold_no_push_ofst >> simp[]
QED

Theorem reduce_depth_plan_no_push_ofst[local]:
  !fuel target_ops target_op f n ps ops ps'.
  reduce_depth_plan fuel target_ops target_op f n ps = (ops, ps') ==>
  !lbl d. ~MEM (SOPushOfst lbl d) ops
Proof
  Induct >> simp[reduce_depth_plan_def] >> rpt gen_tac >>
  IF_CASES_TAC >> simp[] >>
  Cases_on `stack_get_unfixed_depth target_op f n ps.ps_stack` >> simp[] >>
  IF_CASES_TAC >> simp[] >>
  Cases_on `select_spill_candidate ps.ps_stack target_ops x n` >> simp[] >>
  pairarg_tac >> pairarg_tac >> simp[] >> strip_tac >> gvs[] >>
  pairarg_tac >> gvs[] >> metis_tac[do_spill_at_no_push_ofst]
QED

Theorem reorder_one_no_push_ofst[local]:
  reorder_one dfg target_ops idx op ps = (ops, ps') ==>
  !lbl d. ~MEM (SOPushOfst lbl d) ops
Proof
  simp[reorder_one_def] >> pairarg_tac >>
  `!lbl d. ~MEM (SOPushOfst lbl d) restore_ops` by
    (gvs[AllCaseEqs()] >> metis_tac[do_restore_no_push_ofst]) >>
  gvs[] >> qpat_x_assum `_ = (restore_ops, ps1)` kall_tac >>
  Cases_on `stack_get_unfixed_depth op (LENGTH target_ops - (idx + 1))
              (LENGTH target_ops) ps1.ps_stack` >> simp[]
  >- (rw[] >> gvs[]) >>
  pairarg_tac >>
  `!lbl d. ~MEM (SOPushOfst lbl d) reduce_ops` by
    (gvs[AllCaseEqs()] >> metis_tac[reduce_depth_plan_no_push_ofst]) >>
  gvs[] >> qpat_x_assum `_ = (reduce_ops, ps2)` kall_tac >>
  Cases_on `stack_get_unfixed_depth op (LENGTH target_ops - (idx + 1))
              (LENGTH target_ops) ps2.ps_stack` >> simp[]
  >- (rw[] >> gvs[]) >>
  rpt IF_CASES_TAC >> simp[] >> gvs[] >>
  rpt (pairarg_tac >> gvs[]) >>
  strip_tac >> gvs[] >>
  metis_tac[do_swap_no_push_ofst, MEM_APPEND]
QED

Theorem reorder_fold_no_push_ofst[local]:
  !xs acc_ops ps ops ps'.
  FOLDL (\(ops, ps) (idx, op).
    (\(step_ops, ps'). (ops ++ step_ops, ps'))
      (reorder_one dfg target_ops idx op ps)) (acc_ops, ps) xs =
    (ops, ps') /\ ~MEM (SOPushOfst lbl d) acc_ops ==>
  ~MEM (SOPushOfst lbl d) ops
Proof
  Induct >> simp[] >> rpt gen_tac >> PairCases_on `h` >> simp[] >>
  Cases_on `reorder_one dfg target_ops h0 h1 ps` >> simp[] >> strip_tac >>
  first_x_assum (qspec_then `acc_ops ++ q` mp_tac) >> simp[] >>
  disch_then drule >> drule reorder_one_no_push_ofst >> simp[]
QED

Theorem reorder_plan_no_push_ofst:
  reorder_plan dfg target_ops ps = (ops, ps') ==>
  !lbl d. ~MEM (SOPushOfst lbl d) ops
Proof
  simp[reorder_plan_def] >> strip_tac >> rpt gen_tac >>
  drule reorder_fold_no_push_ofst >> simp[]
QED

Theorem emit_one_input_no_push_ofst[local]:
  emit_one_input opc live op ps = (ops, ps') ==>
  !lbl d. ~MEM (SOPushOfst lbl d) ops
Proof
  simp[emit_one_input_def] >> pairarg_tac >>
  `!lbl d. ~MEM (SOPushOfst lbl d) restore_ops` by
    (gvs[AllCaseEqs()] >> metis_tac[do_restore_no_push_ofst]) >>
  gvs[] >> qpat_x_assum `_ = (restore_ops, ps1)` kall_tac >>
  Cases_on `op` >> simp[] >> rpt IF_CASES_TAC >> simp[] >>
  gvs[AllCaseEqs()] >> rpt strip_tac >> gvs[] >>
  pairarg_tac >> gvs[] >> metis_tac[do_dup_no_push_ofst]
QED

Theorem emit_input_plan_no_push_ofst:
  !operands ps ops ps'.
  emit_input_plan opc operands live ps = (ops, ps') ==>
  !lbl d. ~MEM (SOPushOfst lbl d) ops
Proof
  Induct >> simp[emit_input_plan_def] >> rpt gen_tac >>
  rpt (pairarg_tac >> gvs[]) >> strip_tac >> gvs[] >>
  metis_tac[emit_one_input_no_push_ofst, MEM_APPEND]
QED

Theorem generate_emit_ops_no_push_ofst[local]:
  generate_emit_ops inst topics ps = (ops, ps') ==>
  !lbl d. ~MEM (SOPushOfst lbl d) ops
Proof
  simp[generate_emit_ops_def] >> rpt IF_CASES_TAC >>
  gvs[AllCaseEqs(), bump_emit_ops_def] >>
  rpt strip_tac >> gvs[] >> pairarg_tac >> gvs[]
QED

Theorem generate_phi_plan_no_push_ofst[local]:
  generate_phi_plan inst live halting ps = (ops, ps') ==>
  !lbl d. ~MEM (SOPushOfst lbl d) ops
Proof
  simp[generate_phi_plan_def] >>
  Cases_on `stack_get_phi_depth (FILTER is_var_operand inst.inst_operands)
              ps.ps_stack` >> simp[] >>
  Cases_on `MEM (operand_to_string (stack_peek x ps.ps_stack)) live` >>
  simp[] >> rpt (pairarg_tac >> gvs[]) >>
  rw[] >> rpt (pairarg_tac >> gvs[]) >>
  imp_res_tac do_dup_no_push_ofst >> imp_res_tac popmany_plan_no_push_ofst >>
  gvs[]
QED

Theorem generate_regular_inst_plan_no_push_ofst[local]:
  generate_regular_inst_plan liveness dfg cfg fn inst live halting term cur ps =
    (ops, ps') ==> !lbl d. ~MEM (SOPushOfst lbl d) ops
Proof
  simp[generate_regular_inst_plan_def] >> pairarg_tac >>
  `!lbl d. ~MEM (SOPushOfst lbl d) input_ops` by
    metis_tac[emit_input_plan_no_push_ofst] >>
  gvs[] >> qpat_x_assum `_ = (input_ops, ps1)` kall_tac >>
  pairarg_tac >>
  `!lbl d. ~MEM (SOPushOfst lbl d) join_ops` by
    (gvs[AllCaseEqs()] >> rpt (pairarg_tac >> gvs[]) >>
     metis_tac[reorder_plan_no_push_ofst,
               restore_spilled_plan_no_push_ofst]) >>
  gvs[] >> qpat_x_assum `_ = (join_ops, ps2)` kall_tac >>
  pairarg_tac >>
  `!lbl d. ~MEM (SOPushOfst lbl d) reorder_ops` by
    (gvs[AllCaseEqs()] >> rpt (pairarg_tac >> gvs[]) >>
     gvs[AllCaseEqs()] >> metis_tac[reorder_plan_no_push_ofst]) >>
  gvs[] >> qpat_x_assum `_ = (reorder_ops, ps4)` kall_tac >>
  pairarg_tac >>
  `!lbl d. ~MEM (SOPushOfst lbl d) emit_ops` by
    metis_tac[generate_emit_ops_no_push_ofst] >>
  gvs[] >> qpat_x_assum `_ = (emit_ops, ps7)` kall_tac >>
  IF_CASES_TAC >> simp[] >- (rw[] >> gvs[]) >>
  pairarg_tac >>
  `!lbl d. ~MEM (SOPushOfst lbl d) pop_ops` by
    (gvs[AllCaseEqs()] >> metis_tac[popmany_plan_no_push_ofst]) >>
  gvs[] >> qpat_x_assum `_ = (pop_ops, ps8)` kall_tac >>
  pairarg_tac >>
  `!lbl d. ~MEM (SOPushOfst lbl d) opt_ops` by
    (gvs[AllCaseEqs()] >> metis_tac[optimistic_swap_plan_no_push_ofst]) >>
  gvs[] >> rw[] >> gvs[]
QED

Theorem generate_inst_plan_no_push_ofst[local]:
  generate_inst_plan liveness dfg cfg fn inst live halting term cur ps =
    SOME (ops, ps') /\ inst.inst_opcode <> OFFSET ==>
  !lbl d. ~MEM (SOPushOfst lbl d) ops
Proof
  simp[generate_inst_plan_def] >> rpt IF_CASES_TAC >> simp[] >>
  metis_tac[generate_phi_plan_no_push_ofst,
            generate_regular_inst_plan_no_push_ofst]
QED

Theorem prepare_params_plan_no_push_ofst[local]:
  prepare_params_plan liveness fn ps = (ops, ps') ==>
  !lbl d. ~MEM (SOPushOfst lbl d) ops
Proof
  simp[prepare_params_plan_def] >> IF_CASES_TAC >> simp[] >>
  rpt (pairarg_tac >> gvs[]) >> strip_tac >> gvs[] >>
  metis_tac[popmany_plan_no_push_ofst, optimistic_swap_plan_no_push_ofst,
            MEM_APPEND]
QED

Theorem clean_stack_plan_no_push_ofst[local]:
  clean_stack_plan liveness cfg fn bb ps = (ops, ps') ==>
  !lbl d. ~MEM (SOPushOfst lbl d) ops
Proof
  simp[clean_stack_plan_def] >> gvs[AllCaseEqs()] >>
  rpt IF_CASES_TAC >> simp[] >>
  rpt (pairarg_tac >> gvs[]) >> rpt strip_tac >> gvs[] >>
  rpt (pairarg_tac >> gvs[]) >>
  metis_tac[popmany_plan_no_push_ofst]
QED

Theorem generate_block_insts_plan_no_push_ofst[local]:
  !insts i ps ops ps'.
  generate_block_insts_plan liveness dfg cfg fn bb_label halting
    n_params block_len i insts ps = SOME (ops, ps') /\
  EVERY (\inst. inst.inst_opcode <> OFFSET) insts ==>
  !lbl d. ~MEM (SOPushOfst lbl d) ops
Proof
  Induct >> simp[generate_block_insts_plan_def] >> rpt gen_tac >>
  simp[AllCaseEqs()] >> strip_tac >> gvs[] >>
  metis_tac[generate_inst_plan_no_push_ofst, MEM_APPEND]
QED

Theorem generate_block_plan_no_push_ofst[local]:
  generate_block_plan liveness dfg cfg fn bb ps = SOME (ops, ps') /\
  EVERY (\inst. inst.inst_opcode <> OFFSET) bb.bb_instructions ==>
  !lbl d. ~MEM (SOPushOfst lbl d) ops
Proof
  simp[generate_block_plan_def] >> pairarg_tac >>
  `!lbl d. ~MEM (SOPushOfst lbl d) param_ops` by
    (gvs[AllCaseEqs()] >> metis_tac[prepare_params_plan_no_push_ofst]) >>
  gvs[] >> qpat_x_assum `_ = (param_ops, ps1)` kall_tac >>
  pairarg_tac >>
  `!lbl d. ~MEM (SOPushOfst lbl d) clean_ops` by
    (gvs[AllCaseEqs()] >> metis_tac[clean_stack_plan_no_push_ofst]) >>
  gvs[] >> qpat_x_assum `_ = (clean_ops, ps2)` kall_tac >>
  simp[AllCaseEqs()] >> strip_tac >> gvs[] >>
  `EVERY (\inst. inst.inst_opcode <> OFFSET) (non_param_insts bb)` by
    (gvs[non_param_insts_def, EVERY_MEM, MEM_FILTER] >> metis_tac[]) >>
  drule_all generate_block_insts_plan_no_push_ofst >> simp[]
QED

Theorem lookup_block_offset_free[local]:
  !bbs.
  EVERY (\inst. inst.inst_opcode <> OFFSET) (fn_insts_blocks bbs) /\
  lookup_block lbl bbs = SOME bb ==>
  EVERY (\inst. inst.inst_opcode <> OFFSET) bb.bb_instructions
Proof
  Induct >> simp[fn_insts_blocks_def, lookup_block_def, FIND_thm] >>
  rpt gen_tac >> IF_CASES_TAC >> simp[] >> strip_tac >> gvs[lookup_block_def]
QED

Theorem fn_plan_aux_no_push_ofst[local]:
  (!liveness dfg cfg fn worklist visited ps ops visited' ps'.
    generate_fn_plan_aux liveness dfg cfg fn worklist visited ps =
      SOME (ops, visited', ps') /\
    EVERY (\inst. inst.inst_opcode <> OFFSET) (fn_insts fn) ==>
    !lbl d. ~MEM (SOPushOfst lbl d) ops) /\
  (!liveness dfg cfg fn ss sp succs visited ps ops visited' ps'.
    generate_succs_plan liveness dfg cfg fn ss sp succs visited ps =
      SOME (ops, visited', ps') /\
    EVERY (\inst. inst.inst_opcode <> OFFSET) (fn_insts fn) ==>
    !lbl d. ~MEM (SOPushOfst lbl d) ops)
Proof
  ho_match_mp_tac generate_fn_plan_aux_ind >> rpt conj_tac
  >- (rpt gen_tac >> simp[Once generate_fn_plan_aux_def] >> rw[] >> simp[])
  >- (rpt gen_tac >> strip_tac >>
      simp[Once generate_fn_plan_aux_def] >>
      Cases_on `MEM lbl visited` >- (gvs[] >> metis_tac[]) >>
      gvs[] >> Cases_on `lookup_block lbl fn.fn_blocks`
      >- (gvs[] >> metis_tac[]) >>
      simp[AllCaseEqs()] >> rpt gen_tac >> strip_tac >> gvs[] >>
      `EVERY (\inst. inst.inst_opcode <> OFFSET) x.bb_instructions` by
        (irule lookup_block_offset_free >>
         gvs[fn_insts_def] >> metis_tac[]) >>
      drule_all generate_block_plan_no_push_ofst >> strip_tac >>
      metis_tac[MEM_APPEND])
  >- (rpt gen_tac >> simp[Once generate_fn_plan_aux_def] >> rw[] >> simp[])
  >> rpt gen_tac >> strip_tac >>
  simp[Once generate_fn_plan_aux_def, AllCaseEqs()] >>
  rpt gen_tac >> strip_tac >> gvs[] >>
  metis_tac[MEM_APPEND]
QED

(* SOPushOfst is emitted only by generate_offset_plan, for OFFSET. *)
Theorem generate_fn_plan_with_cleanup_no_push_ofst:
  generate_fn_plan_with_cleanup ch growth fn spill_base lbl_ctr =
    SOME (ops, ps) /\
  EVERY (\inst. inst.inst_opcode <> OFFSET) (fn_insts fn) ==>
  !lbl d. ~MEM (SOPushOfst lbl d) ops
Proof
  simp[generate_fn_plan_with_cleanup_def,
       generate_fn_plan_with_cleanup_analyzed_def, AllCaseEqs()] >>
  strip_tac >> gvs[] >>
  metis_tac[cj 1 fn_plan_aux_no_push_ofst]
QED

Theorem generate_context_regions_no_push_ofst[local]:
  !fns acc acc'.
    generate_context_regions gen fns acc = SOME acc' /\
    (!fn sb lc ops ps lbl d.
       MEM fn fns /\ gen fn sb lc = SOME (ops, ps) ==>
       ~MEM (SOPushOfst lbl d) ops) /\
    (!r lbl d. MEM r acc.cpa_regions ==> ~MEM (SOPushOfst lbl d) r.sr_plan) ==>
    !r lbl d. MEM r acc'.cpa_regions ==> ~MEM (SOPushOfst lbl d) r.sr_plan
Proof
  Induct >> simp[generate_context_regions_def] >>
  rpt gen_tac >> simp[AllCaseEqs()] >> rpt strip_tac >>
  first_x_assum (drule_then (qspecl_then [`r`, `lbl`, `d`] mp_tac)) >>
  impl_tac >- (rw[MEM_SNOC] >> gvs[] >> metis_tac[]) >>
  simp[]
QED

Theorem generate_context_plan_no_push_ofst:
  generate_context_plan ctx = SOME cp /\
  EVERY (\fn. EVERY (\inst. inst.inst_opcode <> OFFSET) (fn_insts fn))
        ctx.ctx_functions ==>
  !lbl d. ~MEM (SOPushOfst lbl d) (context_plan_ops cp)
Proof
  simp[generate_context_plan_def, generate_context_plan_with_def,
       AllCaseEqs()] >> strip_tac >>
  `!r lbl d. MEM r acc.cpa_regions ==> ~MEM (SOPushOfst lbl d) r.sr_plan` by
    (rpt strip_tac >> drule generate_context_regions_no_push_ofst >>
     disch_then (qspecl_then [`r`, `lbl`, `d`] mp_tac) >>
     impl_tac
     >- (simp[] >> rpt strip_tac >>
         drule generate_fn_plan_with_cleanup_no_push_ofst >>
         gvs[EVERY_MEM] >> metis_tac[]) >>
     gvs[]) >>
  gvs[context_plan_ops_def, finish_context_plan_def,
      revert_postamble_def, MEM_FLAT, MEM_MAP] >>
  metis_tac[]
QED

Theorem execute_plan_no_push_ofst[local]:
  (!lbl d. ~MEM (SOPushOfst lbl d) ops) ==>
  !lbl d. ~MEM (AsmPushOfst lbl d) (execute_plan fmp ops)
Proof
  simp[execute_plan_def, MEM_FLAT, MEM_MAP, PULL_EXISTS] >>
  rpt strip_tac >> rename1 `MEM op ops` >>
  Cases_on `op` >> gvs[exec_stack_op_def, MEM_REPLICATE] >>
  rename1 `SOPush opd` >> Cases_on `opd` >> gvs[exec_stack_op_def]
QED

Theorem data_segment_no_push_ofst[local]:
  !segs. ~MEM (AsmPushOfst lbl d) (data_segment_asm segs)
Proof
  Induct >> fs[data_segment_asm_def, data_section_asm_def, MEM_MAP] >>
  rpt gen_tac >> Cases_on `di` >> simp[]
QED

(* ===== Main theorem ===== *)

Theorem codegen_assembly_asm_encoding_wf:
  codegen_assembly rpolicy unit = SOME prog /\ unit_shape_ok unit ==>
  asm_encoding_wf prog
Proof
  strip_tac >>
  `?cp. generate_context_plan unit.cu_context = SOME cp /\
        assembly_target_safe rpolicy.rpol_target prog /\
        asm_symbols_ok prog /\
        prog = execute_plan cp.cp_initial_fmp (context_plan_ops cp) ++
               data_segment_asm unit.cu_data_segment ++
               [AsmDataHeader "code_end"]` by
    (qpat_x_assum `codegen_assembly _ _ = _` mp_tac >>
     simp[codegen_assembly_def, AllCaseEqs()] >> rw[] >> simp[]) >>
  `!lbl d. ~MEM (AsmPushOfst lbl d) prog` by
    (`EVERY (\fn. EVERY (\inst. inst.inst_opcode <> OFFSET) (fn_insts fn))
        unit.cu_context.ctx_functions` by
       (fs[unit_shape_ok_def, fn_shape_ok_def, inst_shape_ok_def, EVERY_MEM] >>
        rpt strip_tac >> res_tac >> fs[]) >>
     drule_all generate_context_plan_no_push_ofst >> strip_tac >>
     drule execute_plan_no_push_ofst >>
     disch_then (qspec_then `cp.cp_initial_fmp` assume_tac) >>
     qpat_x_assum `prog = _` SUBST1_TAC >>
     simp[data_segment_no_push_ofst]) >>
  qpat_x_assum `prog = _` kall_tac >>
  `EVERY (\inst. !name. inst = AsmOp name ==>
                        IS_SOME (evm_opcode_byte name)) prog /\
   EVERY (\inst. !bytes. inst = AsmPush bytes ==> LENGTH bytes <= 32) prog` by
    (gvs[assembly_target_safe_def, EVERY_MEM] >> rw[] >> res_tac >>
     gvs[asm_inst_target_safe_def, asm_opcode_target_supported_def] >>
     Cases_on `bytes = []` >> gvs[]) >>
  `SUM (MAP asm_inst_size prog) < 65536` by fs[asm_symbols_ok_def] >>
  qspec_then `prog` strip_assume_tac compute_label_offsets_bound >>
  Cases_on `compute_label_offsets prog` >> gvs[asm_encoding_wf_def] >>
  rpt conj_tac >> rpt strip_tac
  >- (fs[EVERY_EL] >> res_tac >> fs[])
  >- (irule encode_num_bytes_length_le_symbol_size >> res_tac >> simp[])
  >- metis_tac[MEM_EL]
  >- (fs[EVERY_EL] >> res_tac >> fs[])
QED
