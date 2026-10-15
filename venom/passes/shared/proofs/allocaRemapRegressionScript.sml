(* Kernel-checked regressions for the ORIGINAL (pre-FMP) contract.
   Keep this frozen relation independent of the production relation. *)
Theory allocaRemapRegression
Ancestors
  allocaRemapDefs pointerConfinedDefs memLocDefs venomExecSemantics venomState venomInst
  venomWf venomMemDefs venomMemProps finite_map pred_set list While words fcp byte
  dretShapeDefs stateEquiv rich_list

Definition original_alloca_remap_rel_def:
  original_alloca_remap_rel fn (roots : string set) (remap : alloca_remap) s1 s2 <=>
    let pv = pointer_derived_vars fn roots in
    (!v. v NOTIN pv ==> lookup_var v s1 = lookup_var v s2) /\
    (!v aid orig_off sz new_off.
       v IN roots /\ fn_alloca_id_of_var fn v = SOME aid /\
       FLOOKUP s1.vs_allocas aid = SOME (orig_off, sz) /\
       FLOOKUP remap aid = SOME new_off ==>
       lookup_var v s1 = SOME (n2w orig_off) /\
       lookup_var v s2 = SOME (n2w new_off)) /\
    (!v. v IN pv ==>
       lookup_var v s1 = NONE /\ lookup_var v s2 = NONE \/
       ?w1 w2 aid orig_off sz new_off.
         FLOOKUP s1.vs_allocas aid = SOME (orig_off, sz) /\
         FLOOKUP remap aid = SOME new_off /\
         lookup_var v s1 = SOME w1 /\ lookup_var v s2 = SOME w2 /\
         w1 - n2w orig_off = w2 - n2w new_off /\
         orig_off <= w2n w1 /\ w2n w1 < orig_off + sz /\
         new_off <= w2n w2 /\ w2n w2 < new_off + sz /\
         orig_off + sz < dimword (:256) /\
         new_off + sz < dimword (:256)) /\
    alloca_mem_agrees remap s1 s2 /\
    (!i. ~in_alloca_region s1 i /\ ~in_alloca_region s2 i ==>
         mem_byte_at s1.vs_memory i = mem_byte_at s2.vs_memory i) /\
    allocas_non_overlapping s1 /\ allocas_non_overlapping s2 /\
    FDOM s1.vs_allocas = FDOM s2.vs_allocas /\
    (!aid off1 sz new_off.
      FLOOKUP s1.vs_allocas aid = SOME (off1, sz) /\
      FLOOKUP remap aid = SOME new_off ==>
      FLOOKUP s2.vs_allocas aid = SOME (new_off, sz)) /\
    LENGTH s1.vs_memory = LENGTH s2.vs_memory /\
    s1.vs_halted = s2.vs_halted /\
    s1.vs_returndata = s2.vs_returndata /\
    s1.vs_accounts = s2.vs_accounts /\
    s1.vs_transient = s2.vs_transient /\
    s1.vs_call_ctx = s2.vs_call_ctx /\
    s1.vs_tx_ctx = s2.vs_tx_ctx /\
    s1.vs_block_ctx = s2.vs_block_ctx /\
    s1.vs_logs = s2.vs_logs /\
    s1.vs_immutables = s2.vs_immutables /\
    s1.vs_data_section = s2.vs_data_section /\
    s1.vs_labels = s2.vs_labels /\
    s1.vs_code = s2.vs_code /\
    s1.vs_params = s2.vs_params /\
    s1.vs_prev_bb = s2.vs_prev_bb /\
    s1.vs_current_bb = s2.vs_current_bb /\
    s1.vs_inst_idx = s2.vs_inst_idx /\
    s1.vs_prev_hashes = s2.vs_prev_hashes
End

Definition probe_inst_def:
  probe_inst = instruction 0 GETFMP [] ["x"]
End
Definition probe_bb_def:
  probe_bb = <| bb_label := "entry"; bb_instructions := [probe_inst] |>
End
Definition probe_fn_def:
  probe_fn = mk_raw_function "probe" [probe_bb]
End
Definition probe_s1_def:
  probe_s1 = init_venom_state "entry"
End
Definition probe_s2_def:
  probe_s2 = probe_s1 with vs_fmp := 1w
End

Theorem probe_no_pointers:
  pointer_derived_vars probe_fn {} = {}
Proof
  simp[pointer_derived_vars_def, SET_TO_LIST_EMPTY, pointer_use_vars_def] >>
  once_rewrite_tac[OWHILE_THM] >>
  simp[pointer_use_step_step_def, pointer_use_step_def, probe_fn_def,
       probe_bb_def, probe_inst_def, mk_raw_function_def,
       is_pointer_preserving_op_def] >>
  once_rewrite_tac[OWHILE_THM] >> simp[]
QED

(* Every old antecedent, including the actual OK result, is verified. *)
Theorem unequal_fmp_remap_inputs:
  original_alloca_remap_rel probe_fn {} FEMPTY probe_s1 probe_s2 /\
  FINITE ({} : string set) /\
  {} SUBSET alloca_roots probe_fn /\
  ssa_form probe_fn /\
  pointer_confined probe_fn {} /\
  all_mem_via_pointer probe_fn {} /\
  step_inst_base probe_inst probe_s1 = OK (update_var "x" 0w probe_s1) /\
  ~is_alloca_op probe_inst.inst_opcode /\
  ~is_terminator probe_inst.inst_opcode /\
  ~is_ext_call_op probe_inst.inst_opcode /\
  ~is_immutable_op probe_inst.inst_opcode /\
  MEM probe_bb probe_fn.fn_blocks /\
  MEM probe_inst probe_bb.bb_instructions /\
  (!op v. MEM op probe_inst.inst_operands /\ op = Var v ==>
          v NOTIN pointer_derived_vars probe_fn {})
Proof
  simp[pointer_confined_def, all_mem_via_pointer_def, probe_no_pointers,
       probe_fn_def, probe_bb_def, probe_inst_def, mk_raw_function_def] >>
  EVAL_TAC >> simp[]
QED

(* Negation of the full existential conclusion, not just output inequality. *)
Theorem unequal_fmp_remap_output:
  ~(?v2. step_inst_base probe_inst probe_s2 = OK v2 /\
    original_alloca_remap_rel probe_fn {} FEMPTY (update_var "x" 0w probe_s1) v2)
Proof
  simp[probe_inst_def, step_inst_base_def, exec_read0_def] >>
  simp[original_alloca_remap_rel_def, probe_no_pointers, lookup_var_def,
       update_var_def, probe_s1_def, probe_s2_def, init_venom_state_def] >>
  DISJ1_TAC >> qexists_tac `"x"` >> EVAL_TAC >> simp[]
QED

(* Before changing the production definition, this certifies that the frozen
   definition is exactly the old contract. After strengthening, it becomes
   the projection theorem below. *)
Theorem alloca_remap_rel_original:
  alloca_remap_rel fn roots remap s1 s2 ==>
  original_alloca_remap_rel fn roots remap s1 s2
Proof
  simp[alloca_remap_rel_def, original_alloca_remap_rel_def]
QED

(* ILOAD/ISTORE are ordinary memory operations in the current baseline.
   These refute the obsolete immutable-only helper contracts exactly. *)
Theorem istore_memory_counterexample:
  let inst = instruction 0 ISTORE [Lit 0w; Lit 1w] [] in
  let s = init_venom_state "entry" in
  let v = istore 0 1w s in
    is_immutable_op inst.inst_opcode /\ step_inst_base inst s = OK v /\
    v.vs_memory <> s.vs_memory
Proof
  EVAL_TAC >> simp[] >>
  CONV_TAC (DEPTH_CONV fcpLib.INDEX_CONV) >> EVAL_TAC
QED

Theorem iload_output_counterexample:
  let inst = instruction 0 ILOAD [Lit 0w] ["x"] in
  let s1 = mstore 0 0w (init_venom_state "entry") in
  let s2 = mstore 0 1w (init_venom_state "entry") in
  let v1 = update_var "x" 0w s1 in
  let v2 = update_var "x" 1w s2 in
    is_immutable_op inst.inst_opcode /\
    step_inst_base inst s1 = OK v1 /\ step_inst_base inst s2 = OK v2 /\
    s1.vs_immutables = s2.vs_immutables /\
    (!op. MEM op inst.inst_operands ==>
          eval_operand op s1 = eval_operand op s2) /\
    (!nm. MEM nm inst.inst_outputs ==> lookup_var nm s1 = lookup_var nm s2) /\
    ~(!v. MEM v inst.inst_outputs ==> lookup_var v v1 = lookup_var v v2)
Proof
  simp[LET_DEF, step_inst_base_def, exec_read1_def, eval_operand_def,
       mload_mstore_same] >>
  simp[lookup_var_def, update_var_def, FLOOKUP_UPDATE,
       mstore_def, write_memory_with_expansion_def, write_memory_def] >>
  simp[is_immutable_op_def]
QED

Definition iload_bb_def:
  iload_bb = <| bb_label := "entry";
                bb_instructions := [instruction 0 ILOAD [Var "p"] ["x"]] |>
End
Definition iload_fn_def:
  iload_fn = mk_raw_function "probe" [iload_bb]
End

Theorem iload_no_propagation:
  pointer_derived_vars iload_fn {"p"} = {"p"}
Proof
  simp[pointer_derived_vars_def, pointer_use_vars_def] >>
  once_rewrite_tac[OWHILE_THM] >>
  simp[pointer_use_step_step_def, pointer_use_step_def, iload_fn_def,
       iload_bb_def, mk_raw_function_def, is_pointer_preserving_op_def] >>
  once_rewrite_tac[OWHILE_THM] >> simp[]
QED

Theorem pointer_confined_elim_counterexample:
  pointer_confined iload_fn {"p"} /\
  ~(!bb inst v. MEM bb iload_fn.fn_blocks /\ MEM inst bb.bb_instructions /\
      MEM (Var v) inst.inst_operands /\ v IN pointer_derived_vars iload_fn {"p"} ==>
      (?ops. mem_write_ops inst = SOME ops /\
             ~is_immutable_op inst.inst_opcode /\ Var v = ops.iao_ofst) \/
      (?ops. mem_read_ops inst = SOME ops /\
             ~is_immutable_op inst.inst_opcode /\ Var v = ops.iao_ofst) \/
      (is_pointer_preserving_op inst.inst_opcode /\
       set inst.inst_outputs SUBSET pointer_derived_vars iload_fn {"p"}))
Proof
  simp[pointer_confined_def, iload_no_propagation, iload_fn_def,
       iload_bb_def, mk_raw_function_def] >> EVAL_TAC >> simp[]
QED

Definition store_inst_def:
  store_inst = instruction 1 ISTORE [Var "p"; Lit 1w] []
End
Definition store_bb_def:
  store_bb = <| bb_label := "entry"; bb_instructions :=
    [instruction 0 ALLOCA [Lit 32w] ["p"]; store_inst;
     instruction 2 STOP [] []] |>
End
Definition store_fn_def:
  store_fn = mk_raw_function "probe" [store_bb]
End
Definition store_s1_def:
  store_s1 = update_var "p" 0w
    (init_venom_state "entry" with vs_allocas := FEMPTY |+ (0,(0,32)))
End
Definition store_s2_def:
  store_s2 = update_var "p" 32w
    (init_venom_state "entry" with vs_allocas := FEMPTY |+ (0,(32,32)))
End
Definition store_remap_def:
  (store_remap : alloca_remap) = FEMPTY |+ (0,32)
End

Theorem store_no_propagation:
  pointer_derived_vars store_fn {"p"} = {"p"}
Proof
  simp[pointer_derived_vars_def, pointer_use_vars_def] >>
  once_rewrite_tac[OWHILE_THM] >>
  simp[pointer_use_step_step_def, pointer_use_step_def, store_fn_def,
       store_bb_def, store_inst_def, mk_raw_function_def,
       is_pointer_preserving_op_def] >>
  once_rewrite_tac[OWHILE_THM] >> simp[]
QED

(* Exact old step_inst_base_preserves_remap antecedents, with the FINAL
   strengthened relation too: ISTORE writes offset-keyed bookkeeping. *)
Theorem istore_remap_inputs:
  alloca_remap_rel store_fn {"p"} store_remap store_s1 store_s2 /\
  FINITE {"p"} /\ {"p"} SUBSET alloca_roots store_fn /\
  wf_function store_fn /\ ssa_form store_fn /\
  pointer_confined store_fn {"p"} /\ all_mem_via_pointer store_fn {"p"} /\
  affine_pointer_ops store_fn {"p"} /\
  pointer_arith_in_region store_fn {"p"} /\ phi_pv_all_var store_fn {"p"} /\
  alloca_safe_access store_fn {"p"} store_s1 /\
  alloca_safe_access store_fn {"p"} store_s2 /\
  step_inst_base store_inst store_s1 = OK (istore 0 1w store_s1) /\
  ~is_alloca_op store_inst.inst_opcode /\
  ~is_terminator store_inst.inst_opcode /\
  ~is_ext_call_op store_inst.inst_opcode /\
  (?bb. MEM bb store_fn.fn_blocks /\ MEM store_inst bb.bb_instructions) /\
  (!u. u IN pointer_derived_vars store_fn {"p"} ==>
       LENGTH (FILTER ($= (Var u)) store_inst.inst_operands) <= 1)
Proof
  simp[alloca_remap_rel_def, pointer_confined_def, all_mem_via_pointer_def,
       affine_pointer_ops_def, pointer_arith_in_region_def,
       phi_pv_all_var_def, alloca_safe_access_def, store_no_propagation,
       store_fn_def, store_bb_def, store_inst_def, mk_raw_function_def,
       store_s1_def, store_s2_def, store_remap_def,
       update_var_def, lookup_var_def, init_venom_state_def,
       FLOOKUP_UPDATE, alloca_mem_agrees_def, in_alloca_region_def,
       allocas_non_overlapping_def, mem_byte_at_def,
       fn_alloca_id_of_var_def] >>
  CONV_TAC (DEPTH_CONV fcpLib.INDEX_CONV) >> simp[dimword_def] >>
  rpt conj_tac >> rw[] >>
  gvs[mem_write_ops_def, mem_read_ops_def, is_pointer_preserving_op_def,
      step_inst_base_def, eval_operand_def, FLOOKUP_UPDATE,
      is_alloca_op_def, is_terminator_def, is_ext_call_op_def] >>
  EVAL_TAC >> simp[] >>
  TRY (wordsLib.WORD_DECIDE_TAC >> NO_TAC) >>
  TRY (simp[dimword_def] >> CONV_TAC (DEPTH_CONV fcpLib.INDEX_CONV) >>
       simp[] >> NO_TAC) >>
  qexists_tac `instruction 0 ALLOCA [Lit 32w] ["p"]` >> simp[]
QED

Theorem istore_remap_output:
  ~(?v2. step_inst_base store_inst store_s2 = OK v2 /\
    alloca_remap_rel store_fn {"p"} store_remap (istore 0 1w store_s1) v2)
Proof
  simp[store_inst_def, step_inst_base_def, store_s2_def,
       eval_operand_def, lookup_var_def, update_var_def, FLOOKUP_UPDATE] >>
  strip_tac >>
  fs[alloca_remap_rel_def, LET_DEF, istore_def, mstore_def,
     write_memory_with_expansion_def, write_memory_def, store_s1_def,
     update_var_def, init_venom_state_def] >>
  qpat_x_assum `FEMPTY |+ _ = FEMPTY |+ _`
    (mp_tac o AP_TERM ``\m:(num, bytes32) fmap. FLOOKUP m 0``) >>
  simp[FLOOKUP_UPDATE]
QED

Definition memory_inst_def:
  memory_inst = instruction 1 MSTORE [Var "p"; Lit 1w] []
End
Definition memory_bb_def:
  memory_bb = <| bb_label := "entry"; bb_instructions :=
    [instruction 0 ALLOCA [Lit 32w] ["p"]; memory_inst;
     instruction 2 STOP [] []] |>
End
Definition memory_fn_def:
  memory_fn = mk_raw_function "probe" [memory_bb]
End

Theorem memory_no_propagation:
  pointer_derived_vars memory_fn {"p"} = {"p"}
Proof
  simp[pointer_derived_vars_def, pointer_use_vars_def] >>
  once_rewrite_tac[OWHILE_THM] >>
  simp[pointer_use_step_step_def, pointer_use_step_def, memory_fn_def,
       memory_bb_def, memory_inst_def, mk_raw_function_def,
       is_pointer_preserving_op_def] >>
  once_rewrite_tac[OWHILE_THM] >> simp[]
QED

Theorem mstore_remap_inputs:
  alloca_remap_rel memory_fn {"p"} store_remap store_s1 store_s2 /\
  FINITE {"p"} /\ {"p"} SUBSET alloca_roots memory_fn /\
  wf_function memory_fn /\ ssa_form memory_fn /\
  pointer_confined memory_fn {"p"} /\ all_mem_via_pointer memory_fn {"p"} /\
  affine_pointer_ops memory_fn {"p"} /\
  pointer_arith_in_region memory_fn {"p"} /\ phi_pv_all_var memory_fn {"p"} /\
  alloca_safe_access memory_fn {"p"} store_s1 /\
  alloca_safe_access memory_fn {"p"} store_s2 /\
  step_inst_base memory_inst store_s1 = OK (mstore 0 1w store_s1) /\
  ~is_alloca_op memory_inst.inst_opcode /\
  ~is_terminator memory_inst.inst_opcode /\
  ~is_ext_call_op memory_inst.inst_opcode /\
  (?bb. MEM bb memory_fn.fn_blocks /\ MEM memory_inst bb.bb_instructions) /\
  (!u. u IN pointer_derived_vars memory_fn {"p"} ==>
       LENGTH (FILTER ($= (Var u)) memory_inst.inst_operands) <= 1)
Proof
  simp[alloca_remap_rel_def, pointer_confined_def, all_mem_via_pointer_def,
       affine_pointer_ops_def, pointer_arith_in_region_def,
       phi_pv_all_var_def, alloca_safe_access_def, memory_no_propagation,
       memory_fn_def, memory_bb_def, memory_inst_def, mk_raw_function_def,
       store_s1_def, store_s2_def, store_remap_def,
       update_var_def, lookup_var_def, init_venom_state_def,
       FLOOKUP_UPDATE, alloca_mem_agrees_def, in_alloca_region_def,
       allocas_non_overlapping_def, mem_byte_at_def,
       fn_alloca_id_of_var_def] >>
  CONV_TAC (DEPTH_CONV fcpLib.INDEX_CONV) >> simp[dimword_def] >>
  rpt conj_tac >> rw[] >>
  gvs[mem_write_ops_def, mem_read_ops_def, is_pointer_preserving_op_def,
      step_inst_base_def, eval_operand_def, FLOOKUP_UPDATE,
      is_alloca_op_def, is_terminator_def, is_ext_call_op_def] >>
  EVAL_TAC >> simp[] >>
  TRY (wordsLib.WORD_DECIDE_TAC >> NO_TAC) >>
  TRY (simp[dimword_def] >> CONV_TAC (DEPTH_CONV fcpLib.INDEX_CONV) >>
       simp[] >> NO_TAC) >>
  qexists_tac `instruction 0 ALLOCA [Lit 32w] ["p"]` >> simp[]
QED

Theorem mstore_remap_output:
  ~(?v2. step_inst_base memory_inst store_s2 = OK v2 /\
    alloca_remap_rel memory_fn {"p"} store_remap (mstore 0 1w store_s1) v2)
Proof
  simp[memory_inst_def, step_inst_base_def, exec_write2_def, store_s2_def,
       eval_operand_def, lookup_var_def, update_var_def, FLOOKUP_UPDATE] >>
  strip_tac >>
  `LENGTH (mstore 0 1w store_s1).vs_memory =
   LENGTH (mstore 32 1w store_s2).vs_memory` by
    fs[alloca_remap_rel_def, LET_DEF, store_s2_def, update_var_def] >>
  pop_assum mp_tac >>
  simp[mstore_def, write_memory_with_expansion_def, write_memory_def,
       expand_memory_def, store_s1_def, store_s2_def, update_var_def,
       init_venom_state_def, LENGTH_word_to_bytes] >>
  CONV_TAC (DEPTH_CONV fcpLib.INDEX_CONV) >> simp[]
QED

Definition literal_store_inst_def:
  literal_store_inst = instruction 0 ISTORE [Lit 32w; Lit 1w] []
End
Definition literal_store_bb_def:
  literal_store_bb = <| bb_label := "entry";
                       bb_instructions := [literal_store_inst] |>
End
Definition literal_store_fn_def:
  literal_store_fn = mk_raw_function "probe" [literal_store_bb]
End
Definition literal_s1_def:
  literal_s1 = store_s1 with vs_vars := FEMPTY
End
Definition literal_s2_def:
  literal_s2 = store_s2 with vs_vars := FEMPTY
End

Theorem literal_store_no_pointers:
  pointer_derived_vars literal_store_fn {} = {}
Proof
  simp[pointer_derived_vars_def, pointer_use_vars_def] >>
  once_rewrite_tac[OWHILE_THM] >>
  simp[pointer_use_step_step_def, pointer_use_step_def, literal_store_fn_def,
       literal_store_bb_def, literal_store_inst_def, mk_raw_function_def,
       is_pointer_preserving_op_def] >>
  once_rewrite_tac[OWHILE_THM] >> simp[]
QED

Theorem immutable_remap_inputs:
  alloca_remap_rel literal_store_fn {} store_remap literal_s1 literal_s2 /\
  is_immutable_op literal_store_inst.inst_opcode /\
  step_inst_base literal_store_inst literal_s1 = OK (istore 32 1w literal_s1) /\
  ~is_alloca_op literal_store_inst.inst_opcode /\
  ~is_terminator literal_store_inst.inst_opcode /\
  ~is_ext_call_op literal_store_inst.inst_opcode /\
  pointer_confined literal_store_fn {} /\
  FINITE ({} : string set) /\ {} SUBSET alloca_roots literal_store_fn /\
  ssa_form literal_store_fn /\
  (?bb. MEM bb literal_store_fn.fn_blocks /\ MEM literal_store_inst bb.bb_instructions) /\
  (!op v. MEM op literal_store_inst.inst_operands /\ op = Var v ==>
          v NOTIN pointer_derived_vars literal_store_fn {})
Proof
  simp[alloca_remap_rel_def, literal_store_no_pointers, pointer_confined_def,
       literal_store_fn_def, literal_store_bb_def, literal_store_inst_def,
       mk_raw_function_def, literal_s1_def, literal_s2_def,
       store_s1_def, store_s2_def, store_remap_def, update_var_def,
       lookup_var_def, init_venom_state_def, FLOOKUP_UPDATE,
       alloca_mem_agrees_def, mem_byte_at_def, in_alloca_region_def,
       allocas_non_overlapping_def] >> EVAL_TAC >> simp[]
QED

Theorem immutable_remap_output:
  ~(?v2. step_inst_base literal_store_inst literal_s2 = OK v2 /\
    alloca_remap_rel literal_store_fn {} store_remap
      (istore 32 1w literal_s1) v2)
Proof
  simp[literal_store_inst_def, step_inst_base_def, eval_operand_def] >>
  strip_tac >>
  `alloca_mem_agrees store_remap (istore 32 1w literal_s1)
     (istore 32 1w literal_s2)` by fs[alloca_remap_rel_def, LET_DEF] >>
  pop_assum (mp_tac o Q.SPECL [`0`,`0`,`32`,`32`] o
    REWRITE_RULE[alloca_mem_agrees_def]) >>
  simp[istore_def, mstore_def, write_memory_with_expansion_def,
       write_memory_def, literal_s1_def, literal_s2_def, store_s1_def,
       store_s2_def, store_remap_def, update_var_def, init_venom_state_def,
       FLOOKUP_UPDATE] >>
  qexists_tac `31` >> simp[mem_byte_at_def, expand_memory_def] >>
  CONV_TAC (DEPTH_CONV fcpLib.INDEX_CONV) >> EVAL_TAC >> simp[]
QED

Definition dret_inst_def:
  dret_inst = instruction 1 DRET [Lit 1w; Lit 31w; Lit 1w; Lit 0w] []
End
Definition dret_bb_def:
  dret_bb = <| bb_label := "entry"; bb_instructions := [dret_inst] |>
End
Definition dret_fn_def:
  dret_fn = mk_raw_function "probe" [dret_bb]
End
Definition dret_memory_def:
  dret_memory = REPLICATE 31 (0w : word8) ++ [1w] ++ REPLICATE 64 0w
End
Definition dret_s1_def:
  dret_s1 = init_venom_state "entry" with
    <| vs_allocas := FEMPTY |+ (0,(32,32)); vs_memory := dret_memory;
       vs_call_entry_fmp := 32w |>
End
Definition dret_s2_def:
  dret_s2 = dret_s1 with vs_allocas := FEMPTY |+ (0,(64,32))
End
Definition dret_remap_def:
  (dret_remap : alloca_remap) = FEMPTY |+ (0,64)
End

Theorem dret_no_pointers:
  pointer_derived_vars dret_fn {} = {}
Proof
  simp[pointer_derived_vars_def, pointer_use_vars_def] >>
  once_rewrite_tac[OWHILE_THM] >>
  simp[pointer_use_step_step_def, pointer_use_step_def, dret_fn_def,
       dret_bb_def, dret_inst_def, mk_raw_function_def,
       is_pointer_preserving_op_def] >>
  once_rewrite_tac[OWHILE_THM] >> simp[]
QED

Theorem dret_remap_inputs:
  alloca_remap_rel dret_fn {} dret_remap dret_s1 dret_s2 /\
  pointer_confined dret_fn {} /\ all_mem_via_pointer dret_fn {} /\
  alloca_safe_access dret_fn {} dret_s1 /\
  alloca_safe_access dret_fn {} dret_s2 /\
  ptrs_in_alloca_bounds dret_fn {} dret_s1 /\
  ptrs_in_alloca_bounds dret_fn {} dret_s2 /\
  (!u. u IN pointer_derived_vars dret_fn {} ==>
    LENGTH (FILTER ($= (Var u)) dret_inst.inst_operands) <= 1) /\
  is_terminator dret_inst.inst_opcode /\ dret_inst.inst_opcode <> INVOKE /\
  (?bb. MEM bb dret_fn.fn_blocks /\ MEM dret_inst bb.bb_instructions)
Proof
  simp[alloca_remap_rel_def, pointer_confined_def, all_mem_via_pointer_def,
       alloca_safe_access_def, ptrs_in_alloca_bounds_def, dret_no_pointers,
       dret_fn_def, dret_bb_def, dret_inst_def, mk_raw_function_def,
       dret_s1_def, dret_s2_def, dret_memory_def, dret_remap_def,
       init_venom_state_def, lookup_var_def, FLOOKUP_UPDATE,
       alloca_mem_agrees_def, in_alloca_region_def,
       allocas_non_overlapping_def] >>
  rpt conj_tac >> rw[] >>
  gvs[mem_write_ops_def, mem_read_ops_def, is_terminator_def] >>
  simp[mem_byte_at_def, EL_APPEND_EQN, EL_REPLICATE] >>
  rpt IF_CASES_TAC >> fs[] >> TRY decide_tac
QED

Theorem dret_remap_output:
  !remap. FLOOKUP remap 0 = SOME 64 ==>
  ~lift_result (alloca_remap_rel dret_fn {} remap)
    (alloca_remap_rel dret_fn {} remap)
    (alloca_remap_rel dret_fn {} remap)
    (case step_inst_base dret_inst dret_s1 of
       OK s => if s.vs_halted then Halt s else OK s
     | Halt s => Halt s | Abort a s => Abort a s
     | IntRet vs s => IntRet vs s | Error e => Error e)
    (case step_inst_base dret_inst dret_s2 of
       OK s => if s.vs_halted then Halt s else OK s
     | Halt s => Halt s | Abort a s => Abort a s
     | IntRet vs s => IntRet vs s | Error e => Error e)
Proof
  rpt gen_tac >> strip_tac >>
  simp[dret_inst_def, step_inst_base_def, parse_dret_shape_def,
       eval_operands_def, eval_operand_def, pair_dret_words_def,
       pack_dret_dynamic_def, dret_s1_def, dret_s2_def,
       init_venom_state_def, venomLayoutTheory.ceil32_def, lift_result_def] >> strip_tac >>
  `alloca_mem_agrees remap
    (mcopy 32 31 1 dret_s1 with vs_fmp := 64w)
    (mcopy 32 31 1 dret_s2 with vs_fmp := 64w)` by
    fs[alloca_remap_rel_def, LET_DEF, dret_s1_def, dret_s2_def,
       init_venom_state_def] >>
  pop_assum (mp_tac o Q.SPECL [`0`,`32`,`32`,`64`] o
    REWRITE_RULE[alloca_mem_agrees_def]) >>
  simp[dret_remap_def, dret_s1_def, dret_s2_def, init_venom_state_def,
       mcopy_def, write_memory_with_expansion_def, write_memory_def,
       FLOOKUP_UPDATE] >>
  qexists_tac `0` >>
  simp[mem_byte_at_def, dret_memory_def, expand_memory_def] >> EVAL_TAC
QED

(* Every exact old block-contract hypothesis, including freshness and
   instruction well-formedness. Materialization is also satisfied. *)
Theorem dret_block_inputs:
  FINITE ({} : string set) /\ {} SUBSET alloca_roots dret_fn /\
  wf_function dret_fn /\ ssa_form dret_fn /\
  pointer_confined dret_fn {} /\ all_mem_via_pointer dret_fn {} /\
  affine_pointer_ops dret_fn {} /\ pointer_arith_in_region dret_fn {} /\
  phi_pv_all_var dret_fn {} /\ step_preserves_safety dret_fn {} /\
  fn_inst_wf dret_fn /\
  alloca_remap_rel dret_fn {} dret_remap dret_s1 dret_s2 /\
  allocas_in_memory dret_s1 /\ allocas_in_memory dret_s2 /\
  alloca_safe_access dret_fn {} dret_s1 /\
  alloca_safe_access dret_fn {} dret_s2 /\
  ptrs_in_alloca_bounds dret_fn {} dret_s1 /\
  ptrs_in_alloca_bounds dret_fn {} dret_s2 /\
  FDOM dret_remap SUBSET FDOM dret_s1.vs_allocas /\
  (!inst. MEM inst dret_bb.bb_instructions ==>
    inst.inst_opcode <> INVOKE /\ ~is_ext_call_op inst.inst_opcode /\
    ~is_alloca_op inst.inst_opcode /\ inst.inst_opcode <> ISTORE /\
    (!u. u IN pointer_derived_vars dret_fn {} ==>
      LENGTH (FILTER ($= (Var u)) inst.inst_operands) <= 1)) /\
  (!inst. MEM inst dret_bb.bb_instructions /\ is_alloca_op inst.inst_opcode ==>
    inst.inst_outputs = [HD inst.inst_outputs] /\ HD inst.inst_outputs IN {} /\
    fn_alloca_id_of_var dret_fn (HD inst.inst_outputs) = SOME inst.inst_id /\
    ?sz. inst.inst_operands = [Lit sz] /\ 0 < w2n sz) /\
  (!inst s. MEM inst dret_bb.bb_instructions /\ is_alloca_op inst.inst_opcode ==>
    !sz. inst.inst_operands = [Lit sz] ==>
         s.vs_alloca_next + w2n sz < dimword (:256)) /\
  (!i. dret_s1.vs_inst_idx <= i /\ i < LENGTH dret_bb.bb_instructions ==>
    (EL i dret_bb.bb_instructions).inst_id NOTIN FDOM dret_s1.vs_allocas) /\
  MEM dret_bb dret_fn.fn_blocks
Proof
  strip_assume_tac dret_remap_inputs >>
  simp[dret_no_pointers, dret_fn_def, dret_bb_def, dret_inst_def,
       mk_raw_function_def, affine_pointer_ops_def,
       pointer_arith_in_region_def, phi_pv_all_var_def,
       step_preserves_safety_def, fn_inst_wf_def, allocas_in_memory_def,
       dret_s1_def, dret_s2_def, dret_memory_def, dret_remap_def,
       init_venom_state_def, FLOOKUP_UPDATE, wf_function_def, ssa_form_def] >>
  EVAL_TAC >> simp[]
QED

Theorem dret_block_output:
  !fuel ctx. ~(?remap'.
    FDOM dret_remap SUBSET FDOM remap' /\
    (!aid. aid IN FDOM dret_remap ==>
      FLOOKUP remap' aid = FLOOKUP dret_remap aid) /\
    lift_result (alloca_remap_rel dret_fn {} remap')
      (alloca_remap_rel dret_fn {} remap')
      (alloca_remap_rel dret_fn {} remap')
      (exec_block fuel ctx dret_bb dret_s1)
      (exec_block fuel ctx dret_bb dret_s2))
Proof
  rpt gen_tac >> strip_tac >>
  `FLOOKUP remap' 0 = SOME 64` by
    (qpat_x_assum `!aid. _` (qspec_then `0` mp_tac) >>
     simp[dret_remap_def, FLOOKUP_UPDATE]) >>
  drule dret_remap_output >>
  fs[Once exec_block_def, get_instruction_def, step_inst_def,
     dret_bb_def, dret_inst_def, dret_s1_def, dret_s2_def,
     init_venom_state_def, is_terminator_def] >>
  fs[Once exec_block_def, get_instruction_def, step_inst_def, is_terminator_def]
QED

(* Exact old ten-way terminator-enumeration hypotheses and negated conclusion. *)
Theorem frame_return_terminators_counterexample:
  !opc. (opc = DRET \/ opc = RETFMP) ==>
    is_terminator opc /\ opc <> INVOKE /\
    ~(opc = JMP \/ opc = JNZ \/ opc = DJMP \/ opc = RET \/
      opc = RETURN \/ opc = REVERT \/ opc = STOP \/ opc = SINK \/
      opc = SELFDESTRUCT \/ opc = INVALID)
Proof
  rpt strip_tac >> gvs[is_terminator_def]
QED
