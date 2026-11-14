(* Only foreign STOP/NOP ids are moved: allocation keys are untouched. *)
Theory extcallReturnObserverIds
Ancestors
  extcallReturnObserver extcallReturnObserverRun exprSimAbiGasBridge abiDecoderLoop fragExec venomExecSemantics
  venomExecProofs venomInst venomInstProps unitShapeDefs list rich_list arithmetic localPtrsProps venomWf compileEnv

Definition return_observer_inst_ids_def:
  return_observer_inst_ids func bound inst =
    if MEM inst (fn_insts func) then inst
    else inst with inst_id := bound + inst.inst_id
End

Definition return_observer_ids_def:
  return_observer_ids func bound obs =
    obs with fn_blocks := MAP
      (\bb. bb with bb_instructions :=
        MAP (return_observer_inst_ids func bound) bb.bb_instructions)
      obs.fn_blocks
End

Theorem return_observer_stop_nop_ids:
  (inst.inst_opcode = STOP \/ inst.inst_opcode = NOP) ==>
  step_inst_base (inst with inst_id := id) s = step_inst_base inst s
Proof
  strip_tac >> simp[step_inst_base_opcode_eqs]
QED

Theorem return_observer_inst_ids_step:
  (inst.inst_opcode <> STOP /\ inst.inst_opcode <> NOP ==>
     MEM inst (fn_insts func)) ==>
  step_inst fuel ctx (return_observer_inst_ids func bound inst) s =
  step_inst fuel ctx inst s
Proof
  strip_tac >> simp[return_observer_inst_ids_def] >>
  IF_CASES_TAC >> simp[] >>
  `inst.inst_opcode = STOP \/ inst.inst_opcode = NOP` by metis_tac[] >>
  simp[step_inst_non_invoke, return_observer_stop_nop_ids]
QED

Theorem return_observer_ids_bound:
  ?bound. !i. MEM i (fn_insts func ++ fn_insts obs) ==> i.inst_id < bound
Proof
  qexists_tac `SUC (MAX_LIST (MAP (\i. i.inst_id) (fn_insts func ++ fn_insts obs)))` >>
  rpt strip_tac >>
  `MEM i.inst_id (MAP (\i. i.inst_id) (fn_insts func ++ fn_insts obs))` by
    (simp[MEM_MAP] >> qexists_tac `i` >> fs[]) >>
  drule MAX_LIST_PROPERTY >> simp[]
QED

Theorem return_observer_ids_insts:
  fn_insts (return_observer_ids func bound obs) =
  MAP (return_observer_inst_ids func bound) (fn_insts obs)
Proof
  simp[return_observer_ids_def, fn_insts_def] >>
  qspec_tac (`obs.fn_blocks`, `bbs`) >> Induct >>
  simp[fn_insts_blocks_def, MAP_APPEND]
QED

Theorem return_observer_inst_ids_agree:
  fn_inst_ids_distinct func /\
  (!i. MEM i (fn_insts func) ==> i.inst_id < bound) /\
  MEM i (fn_insts func) /\
  i.inst_id = (return_observer_inst_ids func bound j).inst_id ==>
  i = return_observer_inst_ids func bound j
Proof
  simp[return_observer_inst_ids_def] >>
  IF_CASES_TAC >> simp[] >> rpt strip_tac
  >- metis_tac[fn_inst_ids_distinct_inj] >>
  `i.inst_id < bound` by metis_tac[] >> gvs[]
QED

Theorem return_observer_inst_ids_injective_id:
  (!i. MEM i (fn_insts func) ==> i.inst_id < bound) /\
  (return_observer_inst_ids func bound i).inst_id =
    (return_observer_inst_ids func bound j).inst_id ==>
  i.inst_id = j.inst_id
Proof
  strip_tac >>
  Cases_on `MEM i (fn_insts func)` >>
  Cases_on `MEM j (fn_insts func)` >>
  gvs[return_observer_inst_ids_def] >>
  res_tac >> decide_tac
QED

Theorem return_observer_ids_distinct:
  fn_inst_ids_distinct obs /\
  (!i. MEM i (fn_insts func) ==> i.inst_id < bound) ==>
  fn_inst_ids_distinct (return_observer_ids func bound obs)
Proof
  `!bbs. fn_insts_blocks bbs = FLAT (MAP (\bb. bb.bb_instructions) bbs)` by
    (Induct >> simp[fn_insts_blocks_def]) >>
  `!f. fn_inst_ids_distinct f <=>
       ALL_DISTINCT (MAP (\i. i.inst_id) (fn_insts f))` by
    simp[fn_inst_ids_distinct_def, fn_insts_def, MAP_FLAT,
         MAP_MAP_o, combinTheory.o_DEF] >>
  simp[return_observer_ids_insts, MAP_MAP_o, combinTheory.o_DEF] >>
  strip_tac >>
  qpat_x_assum `ALL_DISTINCT _` mp_tac >>
  qspec_tac (`fn_insts obs`, `is`) >>
  Induct >> simp[MEM_MAP] >> rpt strip_tac >>
  metis_tac[return_observer_inst_ids_injective_id]
QED

Theorem return_observer_inst_ids_fields[simp]:
  (return_observer_inst_ids func bound i).inst_opcode = i.inst_opcode /\
  (return_observer_inst_ids func bound i).inst_operands = i.inst_operands /\
  (return_observer_inst_ids func bound i).inst_outputs = i.inst_outputs
Proof
  simp[return_observer_inst_ids_def] >> IF_CASES_TAC >> simp[]
QED

Theorem return_observer_ids_phis:
  !is. eval_phis s (MAP (return_observer_inst_ids func bound) is) =
         eval_phis s is /\
       phi_prefix_length (MAP (return_observer_inst_ids func bound) is) =
         phi_prefix_length is
Proof
  Induct >> simp[eval_phis_def, phi_prefix_length_def] >>
  `!i. eval_one_phi s (return_observer_inst_ids func bound i) =
       eval_one_phi s i` by simp[eval_one_phi_def] >>
  simp[]
QED

Theorem return_observer_ids_get_instruction:
  get_instruction
    (bb with bb_instructions := MAP (return_observer_inst_ids func bound)
                                   bb.bb_instructions) idx =
  OPTION_MAP (return_observer_inst_ids func bound) (get_instruction bb idx)
Proof
  simp[get_instruction_def, EL_MAP] >> IF_CASES_TAC >> simp[]
QED

Theorem return_observer_ids_lookup:
  lookup_block lbl (return_observer_ids func bound obs).fn_blocks =
  OPTION_MAP (\bb. bb with bb_instructions :=
    MAP (return_observer_inst_ids func bound) bb.bb_instructions)
    (lookup_block lbl obs.fn_blocks)
Proof
  simp[return_observer_ids_def, lookup_block_def] >>
  qspec_tac (`obs.fn_blocks`, `bbs`) >> Induct >>
  simp[FIND_thm] >> gen_tac >> IF_CASES_TAC >> simp[]
QED

Theorem return_observer_ids_block:
  !n s bb fuel ctx.
    LENGTH bb.bb_instructions - s.vs_inst_idx = n /\
    EVERY (\i. i.inst_opcode <> STOP /\ i.inst_opcode <> NOP ==>
                   MEM i (fn_insts func)) bb.bb_instructions ==>
    exec_block fuel ctx
      (bb with bb_instructions := MAP (return_observer_inst_ids func bound)
                                     bb.bb_instructions) s =
    exec_block fuel ctx bb s
Proof
  completeInduct_on `n` >> rpt gen_tac >> strip_tac >>
  Cases_on `get_instruction bb s.vs_inst_idx`
  >- (once_rewrite_tac[exec_block_def] >>
      simp[return_observer_ids_get_instruction]) >>
  rename1 `get_instruction bb s.vs_inst_idx = SOME inst` >>
  `inst.inst_opcode <> STOP /\ inst.inst_opcode <> NOP ==>
       MEM inst (fn_insts func)` by
    (fs[EVERY_MEM, get_instruction_def, AllCaseEqs()] >> metis_tac[MEM_EL]) >>
  once_rewrite_tac[exec_block_def] >>
  simp[return_observer_ids_get_instruction, return_observer_inst_ids_step] >>
  Cases_on `step_inst fuel ctx inst s` >> simp[] >>
  IF_CASES_TAC >> simp[] >>
  first_x_assum irule >> gvs[get_instruction_def]
QED

Theorem return_observer_ids_run_blocks:
  !fuel s ctx obs.
    EVERY (\i. i.inst_opcode <> STOP /\ i.inst_opcode <> NOP ==>
                   MEM i (fn_insts func)) (fn_insts obs) ==>
    run_blocks fuel ctx (return_observer_ids func bound obs) s =
    run_blocks fuel ctx obs s
Proof
  Induct_on `fuel` >- (once_rewrite_tac[run_blocks_def] >> simp[]) >>
  rpt gen_tac >> strip_tac >> once_rewrite_tac[run_blocks_def] >>
  simp[return_observer_ids_lookup] >>
  Cases_on `lookup_block s.vs_current_bb obs.fn_blocks` >> simp[] >>
  rename1 `lookup_block s.vs_current_bb obs.fn_blocks = SOME bb` >>
  `EVERY (\i. i.inst_opcode <> STOP /\ i.inst_opcode <> NOP ==>
                   MEM i (fn_insts func)) bb.bb_instructions` by
    metis_tac[return_observer_block_properties] >>
  simp[return_observer_ids_phis, return_observer_ids_block] >>
  qspecl_then [`s`, `bb.bb_instructions`] strip_assume_tac eval_phis_ok_or_error_defs >>
  simp[] >>
  Cases_on `exec_block fuel ctx bb
    (s' with vs_inst_idx := phi_prefix_length bb.bb_instructions)` >> simp[]
QED

Theorem return_observer_ids_run_from:
  EVERY (\i. i.inst_opcode <> STOP /\ i.inst_opcode <> NOP ==>
                 MEM i (fn_insts func)) (fn_insts obs) ==>
  run_from fuel ctx (return_observer_ids func bound obs) s =
  run_from fuel ctx obs s
Proof
  strip_tac >> once_rewrite_tac[run_from_def] >>
  simp[return_observer_ids_lookup] >>
  Cases_on `lookup_block s.vs_current_bb obs.fn_blocks` >> simp[] >>
  rename1 `lookup_block s.vs_current_bb obs.fn_blocks = SOME bb` >>
  `EVERY (\i. i.inst_opcode <> STOP /\ i.inst_opcode <> NOP ==>
                 MEM i (fn_insts func)) bb.bb_instructions` by
    metis_tac[return_observer_block_properties] >>
  simp[return_observer_ids_block] >>
  Cases_on `exec_block fuel ctx bb s` >>
  simp[return_observer_ids_run_blocks]
QED

Theorem return_observer_ids_sim:
  EVERY (\i. i.inst_opcode <> STOP /\ i.inst_opcode <> NOP ==>
                 MEM i (fn_insts func)) (fn_insts obs) ==>
  (abi_decode_sim ctx (return_observer_ids func bound obs) s t <=>
   abi_decode_sim ctx obs s t)
Proof
  strip_tac >> simp[abi_decode_sim_def, return_observer_ids_run_from]
QED

Theorem return_observer_ids_original_list:
  EVERY (\i. MEM i (fn_insts func)) is ==>
  MAP (return_observer_inst_ids func bound) is = is
Proof
  Induct_on `is` >> simp[return_observer_inst_ids_def]
QED

Theorem return_observer_ids_original_block:
  MEM bb (emitted_blocks sa sb) /\ fn_has_code sa sb func ==>
  MAP (return_observer_inst_ids func bound) bb.bb_instructions = bb.bb_instructions
Proof
  strip_tac >> irule return_observer_ids_original_list >>
  fs[fn_has_code_def, EVERY_MEM] >> rpt strip_tac >>
  `lookup_block bb.bb_label func.fn_blocks = SOME bb` by metis_tac[] >>
  drule lookup_block_MEM >> strip_tac >>
  simp[fn_insts_def, MEM_fn_insts_blocks_iff] >> metis_tac[]
QED

Theorem return_observer_ids_original_current:
  fn_has_code sa sb func ==>
  MAP (return_observer_inst_ids func bound) sb.cs_current_insts = sb.cs_current_insts
Proof
  strip_tac >> irule return_observer_ids_original_list >>
  fs[fn_has_code_def, EVERY_MEM, IS_PREFIX_APPEND] >> rpt strip_tac >>
  drule lookup_block_MEM >> strip_tac >>
  simp[fn_insts_def, MEM_fn_insts_blocks_iff] >>
  metis_tac[MEM_APPEND]
QED

Theorem return_observer_ids_code:
  fn_has_code sa sb func /\ fn_has_code sa sb obs ==>
  fn_has_code sa sb (return_observer_ids func bound obs)
Proof
  strip_tac >> rewrite_tac[fn_has_code_def] >> conj_tac
  >- (qx_gen_tac `b` >> strip_tac >>
      `lookup_block b.bb_label obs.fn_blocks = SOME b` by
        metis_tac[fn_has_code_def] >>
      `MAP (return_observer_inst_ids func bound) b.bb_instructions =
       b.bb_instructions` by metis_tac[return_observer_ids_original_block] >>
      simp[return_observer_ids_lookup]) >>
  qpat_x_assum `fn_has_code sa sb obs` mp_tac >>
  rewrite_tac[fn_has_code_def] >> strip_tac >>
  qexists_tac `bb with bb_instructions :=
    MAP (return_observer_inst_ids func bound) bb.bb_instructions` >>
  simp[return_observer_ids_lookup] >>
  `MAP (return_observer_inst_ids func bound) sb.cs_current_insts =
   sb.cs_current_insts` by metis_tac[return_observer_ids_original_current] >>
  fs[IS_PREFIX_APPEND] >> gvs[] >> metis_tac[MAP_APPEND]
QED

Definition return_observer_prefix_ids_def:
  return_observer_prefix_ids func bound ids =
    MAP (\id. (return_observer_inst_ids func bound (mk_inst id NOP [] [])).inst_id) ids
End

Theorem return_observer_prefix_ids_length[simp]:
  LENGTH (return_observer_prefix_ids func bound ids) = LENGTH ids
Proof
  simp[return_observer_prefix_ids_def]
QED

Theorem return_observer_ids_prefix:
  MAP (\id. mk_inst id NOP [] []) (return_observer_prefix_ids func bound ids) =
  MAP (return_observer_inst_ids func bound) (MAP (\id. mk_inst id NOP [] []) ids)
Proof
  simp[return_observer_prefix_ids_def, MAP_MAP_o, combinTheory.o_DEF, MAP_EQ_f] >>
  rpt strip_tac >> simp[return_observer_inst_ids_def] >>
  IF_CASES_TAC >> simp[mk_inst_def]
QED

Theorem return_observer_ids_relabel_emitted:
  cs_extends sa sb /\ sa.cs_blocks <> sb.cs_blocks /\ fn_has_code sa sb func ==>
  emitted_blocks (start_relabel L (return_observer_prefix_ids func bound ids) sa)
    (start_swap sa L (return_observer_prefix_ids func bound ids) sb) =
  MAP (\bb. bb with bb_instructions :=
    MAP (return_observer_inst_ids func bound) bb.bb_instructions)
    (emitted_blocks (start_relabel L ids sa) (start_swap sa L ids sb))
Proof
  strip_tac >> simp[start_swap_emitted_blocks, MAP_APPEND, return_observer_ids_prefix] >>
  `!b. MEM b (emitted_blocks sa sb) ==>
       MAP (return_observer_inst_ids func bound) b.bb_instructions = b.bb_instructions` by
    metis_tac[return_observer_ids_original_block] >>
  `emitted_blocks sa sb <> []` by
    (fs[cs_extends_def] >>
     `emitted_blocks sa sb = new` by
       (irule emitted_blocks_append >> simp[]) >> gvs[] >>
     strip_tac >> gvs[]) >>
  `MAP (\bb. bb with bb_instructions :=
      MAP (return_observer_inst_ids func bound) bb.bb_instructions)
      (FRONT (emitted_blocks sa sb)) = FRONT (emitted_blocks sa sb)` by
    (CONV_TAC (RAND_CONV (REWR_CONV (GSYM (CONJUNCT1 MAP_ID)))) >>
     irule MAP_CONG >> simp[] >>
     qx_gen_tac `b` >> strip_tac >>
     `MEM b (emitted_blocks sa sb)` by metis_tac[MEM_FRONT_NOT_NIL] >> simp[]) >>
  `MAP (return_observer_inst_ids func bound)
       (LAST (emitted_blocks sa sb)).bb_instructions =
       (LAST (emitted_blocks sa sb)).bb_instructions` by metis_tac[MEM_LAST_NOT_NIL] >>
  simp[MAP_APPEND] >> metis_tac[MAP_DROP]
QED

Theorem return_observer_ids_relabel_code:
  cs_extends sa sb /\ sa.cs_blocks <> sb.cs_blocks /\
  fn_has_code sa sb func /\
  fn_has_code (start_relabel L ids sa) (start_swap sa L ids sb) obs ==>
  fn_has_code (start_relabel L (return_observer_prefix_ids func bound ids) sa)
    (start_swap sa L (return_observer_prefix_ids func bound ids) sb)
    (return_observer_ids func bound obs)
Proof
  strip_tac >> rewrite_tac[fn_has_code_def] >> conj_tac
  >- (qx_gen_tac `bnew` >>
      simp[return_observer_ids_relabel_emitted, MEM_MAP] >>
      strip_tac >> gvs[] >> rename1 `MEM b (emitted_blocks _ _)` >>
      `lookup_block b.bb_label obs.fn_blocks = SOME b` by metis_tac[fn_has_code_def] >>
      simp[return_observer_ids_lookup]) >>
  qpat_x_assum `fn_has_code _ _ obs` mp_tac >>
  rewrite_tac[fn_has_code_def] >> simp[start_swap_fields] >> strip_tac >>
  qexists_tac `bb with bb_instructions :=
    MAP (return_observer_inst_ids func bound) bb.bb_instructions` >>
  simp[start_swap_fields, return_observer_ids_lookup] >>
  `MAP (return_observer_inst_ids func bound) sb.cs_current_insts =
   sb.cs_current_insts` by metis_tac[return_observer_ids_original_current] >>
  fs[IS_PREFIX_APPEND] >> gvs[] >> metis_tac[MAP_APPEND]
QED

Theorem return_observer_ids_properties:
  (!i. MEM i (fn_insts obs) /\ i.inst_opcode <> STOP /\ i.inst_opcode <> NOP ==>
         MEM i (fn_insts func)) ==>
  ((!i. MEM i (fn_insts (return_observer_ids func bound obs)) /\
          i.inst_opcode <> STOP /\ i.inst_opcode <> NOP ==> MEM i (fn_insts func)) /\
   (!op. (!i. MEM i (fn_insts obs) ==> i.inst_opcode <> op) ==>
         !i. MEM i (fn_insts (return_observer_ids func bound obs)) ==> i.inst_opcode <> op) /\
   (return_observer_ids func bound obs).fn_name = obs.fn_name)
Proof
  simp[return_observer_ids_insts, MEM_MAP, return_observer_ids_def] >>
  rpt strip_tac >> gvs[] >>
  metis_tac[return_observer_inst_ids_def]
QED

Theorem return_observer_ids_complete_metadata:
  fn_inst_ids_distinct func /\ fn_inst_ids_distinct obs /\
  (!i. MEM i (fn_insts func) ==> i.inst_id < bound) /\
  (!i. MEM i (fn_insts obs) /\ i.inst_opcode <> STOP /\ i.inst_opcode <> NOP ==>
         MEM i (fn_insts func)) ==>
  fn_inst_ids_distinct
    (return_observer_complete func (return_observer_ids func bound obs) keep) /\
  (!i. i.inst_opcode = ALLOCA ==>
    (MEM i (fn_insts (return_observer_complete func
                      (return_observer_ids func bound obs) keep)) <=>
     MEM i (fn_insts func))) /\
  (return_observer_complete func (return_observer_ids func bound obs) keep).fn_name =
    obs.fn_name
Proof
  strip_tac >> conj_tac
  >- (irule return_observer_complete_ids >>
      simp[return_observer_ids_distinct] >>
      rpt strip_tac >>
      fs[return_observer_ids_insts, MEM_MAP] >> gvs[] >>
      metis_tac[return_observer_inst_ids_agree]) >>
  reverse conj_tac
  >- simp[return_observer_complete_def, return_observer_ids_def] >>
  rpt strip_tac >> irule return_observer_complete_allocas >> simp[] >>
  simp[return_observer_ids_insts, MEM_MAP] >> rpt strip_tac >> gvs[] >>
  rename1 `MEM original (fn_insts obs)` >>
  `MEM original (fn_insts func)` by (fs[] >> metis_tac[]) >>
  gvs[return_observer_inst_ids_def]
QED
