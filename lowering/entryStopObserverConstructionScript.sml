(* STOP insertion retains the unexecuted suffix and its allocation inventory. *)
Theory entryStopObserverConstruction
Ancestors
  compileEnv allocaFrontierBound allocaBudgetProps fcgDefs vyperCompiler abiEncoderObserver fragExec venomExecProps venomExecSemantics venomInst list rich_list
  arithmetic

Definition entry_stop_block_def:
  entry_stop_block k iid bb = bb with bb_instructions :=
    TAKE k bb.bb_instructions ++ [mk_inst iid STOP [] []] ++
    DROP k bb.bb_instructions
End

Definition entry_stop_function_def:
  entry_stop_function lbl k iid fn = fn with fn_blocks :=
    MAP (\bb. if bb.bb_label = lbl then entry_stop_block k iid bb else bb)
      fn.fn_blocks
End

Definition entry_stop_context_def:
  entry_stop_context name lbl k iid ctx = ctx with ctx_functions :=
    MAP (\fn. if fn.fn_name = name then entry_stop_function lbl k iid fn else fn)
      ctx.ctx_functions
End

Theorem entry_stop_block_label[simp]:
  (entry_stop_block k iid bb).bb_label = bb.bb_label
Proof
  simp[entry_stop_block_def]
QED

Theorem entry_stop_block_at_cut:
  k <= LENGTH bb.bb_instructions ==>
  get_instruction (entry_stop_block k iid bb) k = SOME (mk_inst iid STOP [] [])
Proof
  simp[entry_stop_block_def, get_instruction_def, EL_APPEND_EQN]
QED

Theorem entry_stop_block_before_cut:
  j < k /\ k <= LENGTH bb.bb_instructions ==>
  get_instruction (entry_stop_block k iid bb) j = get_instruction bb j
Proof
  simp[entry_stop_block_def, get_instruction_def, EL_APPEND_EQN, EL_TAKE]
QED

Theorem entry_stop_block_inventory:
  !P k iid bb. ~P (mk_inst iid STOP [] []) ==>
  FILTER P (entry_stop_block k iid bb).bb_instructions = FILTER P bb.bb_instructions
Proof
  rpt strip_tac >> simp[entry_stop_block_def, FILTER_APPEND] >>
  metis_tac[TAKE_DROP, FILTER_APPEND]
QED

Theorem entry_stop_lookup_block:
  !bbs lbl k iid.
  lookup_block lbl (MAP (\bb. if bb.bb_label = target then
      entry_stop_block k iid bb else bb) bbs) =
  OPTION_MAP (\bb. if bb.bb_label = target then entry_stop_block k iid bb else bb)
    (lookup_block lbl bbs)
Proof
  Induct >> simp[lookup_block_def, FIND_thm] >> rpt gen_tac >>
  Cases_on `h.bb_label = target` >> simp[] >>
  Cases_on `h.bb_label = lbl` >> gvs[lookup_block_def]
QED

Theorem entry_stop_function_name[simp]:
  (entry_stop_function lbl k iid fn).fn_name = fn.fn_name
Proof
  simp[entry_stop_function_def]
QED

Theorem entry_stop_function_inventory:
  !bbs. ~P (mk_inst iid STOP [] []) ==>
  FILTER P (fn_insts_blocks
    (MAP (\bb. if bb.bb_label = lbl then entry_stop_block k iid bb else bb) bbs)) =
  FILTER P (fn_insts_blocks bbs)
Proof
  Induct >> simp[fn_insts_blocks_def, FILTER_APPEND] >> rpt strip_tac >>
  Cases_on `h.bb_label = lbl` >> simp[entry_stop_block_inventory]
QED

Theorem entry_stop_fn_insts_inventory:
  ~P (mk_inst iid STOP [] []) ==>
  FILTER P (fn_insts (entry_stop_function lbl k iid fn)) = FILTER P (fn_insts fn)
Proof
  simp[fn_insts_def, entry_stop_function_def, entry_stop_function_inventory]
QED

Theorem entry_stop_context_inventory:
  !fns. ~P (mk_inst iid STOP [] []) ==>
  FILTER P (FLAT (MAP fn_insts
    (MAP (\fn. if fn.fn_name = name then entry_stop_function lbl k iid fn else fn) fns))) =
  FILTER P (FLAT (MAP fn_insts fns))
Proof
  Induct >> simp[FILTER_APPEND] >> rpt strip_tac >>
  Cases_on `h.fn_name = name` >> simp[entry_stop_fn_insts_inventory]
QED

Theorem entry_stop_unit_budget:
  unit_alloca_budget (entry_stop_context name lbl k iid ctx) = unit_alloca_budget ctx
Proof
  simp[unit_alloca_budget_def, entry_stop_context_def,
       entry_stop_context_inventory, mk_inst_def]
QED

Theorem entry_stop_lookup_function:
  !fns fname.
  lookup_function fname
    (MAP (\fn. if fn.fn_name = name then entry_stop_function lbl k iid fn else fn) fns) =
  OPTION_MAP (\fn. if fn.fn_name = name then entry_stop_function lbl k iid fn else fn)
    (lookup_function fname fns)
Proof
  Induct >> simp[lookup_function_def, FIND_thm] >> rpt gen_tac >>
  Cases_on `h.fn_name = name` >> simp[] >>
  Cases_on `h.fn_name = fname` >> gvs[lookup_function_def]
QED

Theorem entry_stop_remaining_budget:
  remaining_alloca_budget (fn_insts (entry_stop_function lbl k iid fn)) s =
  remaining_alloca_budget (fn_insts fn) s
Proof
  simp[remaining_alloca_budget_def, entry_stop_fn_insts_inventory, mk_inst_def]
QED

Theorem entry_stop_fn_opcode_member:
  ins.inst_opcode <> STOP ==>
  (MEM ins (fn_insts (entry_stop_function lbl k iid fn)) <=> MEM ins (fn_insts fn))
Proof
  strip_tac >>
  `FILTER (\i. i.inst_opcode = ins.inst_opcode)
     (fn_insts (entry_stop_function lbl k iid fn)) =
   FILTER (\i. i.inst_opcode = ins.inst_opcode) (fn_insts fn)` by
    (irule entry_stop_fn_insts_inventory >> simp[mk_inst_def]) >>
  pop_assum (mp_tac o Q.AP_TERM `MEM ins`) >> simp[MEM_FILTER]
QED

Theorem entry_stop_direct_calls:
  fn_directly_calls (entry_stop_context name lbl k iid ctx) a b <=>
  fn_directly_calls ctx a b
Proof
  simp[fn_directly_calls_def, entry_stop_context_def, entry_stop_lookup_function] >>
  Cases_on `lookup_function a ctx.ctx_functions` >> simp[] >>
  Cases_on `x.fn_name = name` >> simp[] >>
  `INVOKE <> STOP` by simp[] >>
  metis_tac[entry_stop_fn_opcode_member]
QED

Theorem entry_stop_call_relation:
  fn_directly_calls (entry_stop_context name lbl k iid ctx) = fn_directly_calls ctx
Proof
  simp[FUN_EQ_THM, entry_stop_direct_calls]
QED

Theorem entry_stop_frontier_inv:
  alloca_frontier_inv ctx fn site s ==>
  alloca_frontier_inv (entry_stop_context fn.fn_name lbl k iid ctx)
    (entry_stop_function lbl k iid fn) site s
Proof
  simp[alloca_frontier_inv_def, entry_stop_function_name,
       entry_stop_remaining_budget, entry_stop_call_relation, entry_stop_unit_budget] >>
  strip_tac >> conj_tac
  >- simp[entry_stop_context_def, entry_stop_lookup_function] >>
  simp[entry_stop_context_def, entry_stop_context_inventory, mk_inst_def]
QED

Theorem entry_stop_has_code:
  fn_has_code st final fn /\
  (!bb. MEM bb (emitted_blocks st final) ==> bb.bb_label <> final.cs_current_bb) ==>
  fn_has_code st final
    (entry_stop_function final.cs_current_bb (LENGTH final.cs_current_insts) iid fn)
Proof
  simp[fn_has_code_def, entry_stop_function_def, entry_stop_lookup_block] >>
  strip_tac >>
  `bb.bb_label = final.cs_current_bb` by metis_tac[lookup_block_label] >>
  qexists_tac `entry_stop_block (LENGTH final.cs_current_insts) iid bb` >>
  simp[entry_stop_block_def, IS_PREFIX_APPEND] >>
  qpat_x_assum `isPREFIX _ _` mp_tac >> simp[IS_PREFIX_APPEND] >> strip_tac >>
  qexists_tac `mk_inst iid STOP [] [] :: l` >> simp[TAKE_LENGTH_APPEND, DROP_LENGTH_APPEND]
QED

Theorem entry_stop_function_cut:
  lookup_block lbl fn.fn_blocks = SOME bb /\ k <= LENGTH bb.bb_instructions ==>
  lookup_block lbl (entry_stop_function lbl k iid fn).fn_blocks =
    SOME (entry_stop_block k iid bb) /\
  get_instruction (entry_stop_block k iid bb) k = SOME (mk_inst iid STOP [] [])
Proof
  strip_tac >> `bb.bb_label = lbl` by metis_tac[lookup_block_label] >>
  simp[entry_stop_function_def, entry_stop_lookup_block, entry_stop_block_at_cut]
QED

Theorem entry_stop_block_zero_phi:
  phi_prefix_length (entry_stop_block 0 iid bb).bb_instructions = 0
Proof
  simp[entry_stop_block_def, phi_prefix_length_def, mk_inst_def]
QED

Theorem entry_stop_block_ids:
  ALL_DISTINCT (MAP (\i. i.inst_id) bb.bb_instructions) /\
  ~MEM iid (MAP (\i. i.inst_id) bb.bb_instructions) ==>
  ALL_DISTINCT (MAP (\i. i.inst_id) (entry_stop_block k iid bb).bb_instructions)
Proof
  `bb.bb_instructions = TAKE k bb.bb_instructions ++ DROP k bb.bb_instructions` by
    simp[TAKE_DROP] >>
  strip_tac >>
  qpat_x_assum `ALL_DISTINCT _` mp_tac >>
  qpat_x_assum `~MEM _ _` mp_tac >>
  once_asm_rewrite_tac[] >>
  simp[entry_stop_block_def, MAP_APPEND, ALL_DISTINCT_APPEND, mk_inst_def] >>
  metis_tac[]
QED

Theorem entry_stop_blocks_absent[local]:
  !bbs. ~MEM lbl (MAP (\bb. bb.bb_label) bbs) ==>
  MAP (\bb. if bb.bb_label = lbl then entry_stop_block k iid bb else bb) bbs = bbs
Proof
  Induct >> simp[] >> rpt strip_tac >> simp[]
QED

Theorem entry_stop_block_id_member[local]:
  MEM id (MAP (\i. i.inst_id) (entry_stop_block k iid bb).bb_instructions) ==>
  id = iid \/ MEM id (MAP (\i. i.inst_id) bb.bb_instructions)
Proof
  `MAP (\i. i.inst_id) bb.bb_instructions =
   MAP (\i. i.inst_id) (TAKE k bb.bb_instructions) ++
   MAP (\i. i.inst_id) (DROP k bb.bb_instructions)` by
    metis_tac[TAKE_DROP, MAP_APPEND] >>
  simp[entry_stop_block_def, MAP_APPEND, mk_inst_def] >>
  metis_tac[MEM_APPEND]
QED

Theorem entry_stop_blocks_id_member[local]:
  !bbs. MEM id (FLAT (MAP (\bb. MAP (\i. i.inst_id) bb.bb_instructions)
    (MAP (\bb. if bb.bb_label = lbl then entry_stop_block k iid bb else bb) bbs))) ==>
  id = iid \/ MEM id (FLAT (MAP (\bb. MAP (\i. i.inst_id) bb.bb_instructions) bbs))
Proof
  Induct >> simp[] >> gen_tac >> Cases_on `h.bb_label = lbl` >>
  simp[] >> metis_tac[entry_stop_block_id_member]
QED

Theorem entry_stop_blocks_ids:
  !bbs. ALL_DISTINCT (MAP (\bb. bb.bb_label) bbs) /\
  ALL_DISTINCT (FLAT (MAP (\bb. MAP (\i. i.inst_id) bb.bb_instructions) bbs)) /\
  ~MEM iid (FLAT (MAP (\bb. MAP (\i. i.inst_id) bb.bb_instructions) bbs)) ==>
  ALL_DISTINCT (FLAT (MAP (\bb. MAP (\i. i.inst_id) bb.bb_instructions)
    (MAP (\bb. if bb.bb_label = lbl then entry_stop_block k iid bb else bb) bbs)))
Proof
  Induct >> simp[] >> rpt gen_tac >>
  simp[ALL_DISTINCT_APPEND] >> strip_tac >>
  Cases_on `h.bb_label = lbl`
  >- (gvs[] >> drule entry_stop_blocks_absent >> strip_tac >>
      simp[ALL_DISTINCT_APPEND, entry_stop_block_ids] >>
      metis_tac[entry_stop_block_id_member]) >>
  simp[ALL_DISTINCT_APPEND] >>
  metis_tac[entry_stop_blocks_id_member]
QED

Theorem entry_stop_insts_flat[local]:
  !bbs. fn_insts_blocks bbs = FLAT (MAP (\bb. bb.bb_instructions) bbs)
Proof
  Induct >> simp[fn_insts_blocks_def]
QED

Theorem entry_stop_function_ids:
  ALL_DISTINCT (MAP (\bb. bb.bb_label) fn.fn_blocks) /\
  ALL_DISTINCT (MAP (\i. i.inst_id) (fn_insts fn)) /\
  ~MEM iid (MAP (\i. i.inst_id) (fn_insts fn)) ==>
  ALL_DISTINCT (MAP (\i. i.inst_id)
    (fn_insts (entry_stop_function lbl k iid fn)))
Proof
  simp[fn_insts_def, entry_stop_insts_flat, MAP_FLAT, MAP_MAP_o, combinTheory.o_DEF,
       entry_stop_function_def] >>
  MATCH_ACCEPT_TAC (SRULE [MAP_MAP_o, combinTheory.o_DEF] entry_stop_blocks_ids)
QED

Theorem entry_stop_emitted_labels:
  compile_state_ok final ==>
  !bb. MEM bb (emitted_blocks st final) ==> bb.bb_label <> final.cs_current_bb
Proof
  simp[compile_state_ok_def, emitted_blocks_def, MEM_MAP] >>
  rpt strip_tac >> drule MEM_TAKE >> strip_tac >> metis_tac[]
QED

Theorem entry_stop_has_code_ok:
  fn_has_code st final fn /\ compile_state_ok final ==>
  fn_has_code st final
    (entry_stop_function final.cs_current_bb (LENGTH final.cs_current_insts) iid fn)
Proof
  strip_tac >> irule entry_stop_has_code >>
  metis_tac[entry_stop_emitted_labels]
QED

Theorem entry_stop_function_zero_phi:
  final.cs_current_insts = [] /\
  lookup_block final.cs_current_bb
    (entry_stop_function final.cs_current_bb (LENGTH final.cs_current_insts) iid fn).fn_blocks
    = SOME bb ==>
  phi_prefix_length bb.bb_instructions = 0
Proof
  simp[entry_stop_function_def, entry_stop_lookup_block] >>
  Cases_on `lookup_block final.cs_current_bb fn.fn_blocks` >> simp[] >>
  `x.bb_label = final.cs_current_bb` by metis_tac[lookup_block_label] >>
  simp[] >> strip_tac >> gvs[entry_stop_block_zero_phi]
QED
