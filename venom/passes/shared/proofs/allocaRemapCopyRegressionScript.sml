(* Permanent counterexample to the original MCOPY preservation helper:
   zero-padded copies materialize different memory lengths after relocation. *)
Theory allocaRemapCopyRegression
Ancestors
  allocaRemapDefs allocaRemapRegression pointerConfinedDefs memLocDefs
  venomExecSemantics venomState venomInst venomWf venomMemDefs
  finite_map pred_set list While words fcp
Libs
  wordsLib fcpLib

Definition copy_inst_def:
  copy_inst = instruction 2 MCOPY [Var "p"; Var "q"; Lit 32w] []
End
Definition copy_bb_def:
  copy_bb = <| bb_label := "entry"; bb_instructions :=
    [instruction 0 ALLOCA [Lit 32w] ["p"];
     instruction 1 ALLOCA [Lit 32w] ["q"];
     copy_inst; instruction 3 STOP [] []] |>
End
Definition copy_fn_def:
  copy_fn = mk_raw_function "probe" [copy_bb]
End
Definition copy_s1_def:
  copy_s1 = update_var "q" 64w (store_s1 with
    vs_allocas := store_s1.vs_allocas |+ (1,(64,32)))
End
Definition copy_s2_def:
  copy_s2 = update_var "q" 64w (store_s2 with
    vs_allocas := store_s2.vs_allocas |+ (1,(64,32)))
End
Definition copy_remap_def:
  copy_remap = store_remap |+ (1,64)
End

Theorem copy_no_propagation:
  pointer_derived_vars copy_fn {"p";"q"} = {"p";"q"}
Proof
  simp[pointer_derived_vars_def, pointer_use_vars_def] >>
  once_rewrite_tac[OWHILE_THM] >>
  simp[pointer_use_step_step_def, pointer_use_step_def, copy_fn_def,
       copy_bb_def, copy_inst_def, mk_raw_function_def,
       is_pointer_preserving_op_def] >>
  once_rewrite_tac[OWHILE_THM] >> simp[SET_TO_LIST_INV]
QED

(* Every original mcopy_preserves_remap antecedent, and the extra public
   step-contract hypotheses. The source and destination each occur once. *)
Theorem mcopy_remap_inputs:
  alloca_remap_rel copy_fn {"p";"q"} copy_remap copy_s1 copy_s2 /\
  FINITE {"p";"q"} /\ {"p";"q"} SUBSET alloca_roots copy_fn /\
  wf_function copy_fn /\ ssa_form copy_fn /\
  pointer_confined copy_fn {"p";"q"} /\
  all_mem_via_pointer copy_fn {"p";"q"} /\
  affine_pointer_ops copy_fn {"p";"q"} /\
  pointer_arith_in_region copy_fn {"p";"q"} /\
  phi_pv_all_var copy_fn {"p";"q"} /\
  alloca_safe_access copy_fn {"p";"q"} copy_s1 /\
  alloca_safe_access copy_fn {"p";"q"} copy_s2 /\
  copy_inst.inst_opcode = MCOPY /\
  step_inst_base copy_inst copy_s1 = OK (mcopy 0 64 32 copy_s1) /\
  MEM copy_bb copy_fn.fn_blocks /\ MEM copy_inst copy_bb.bb_instructions /\
  (!u. u IN pointer_derived_vars copy_fn {"p";"q"} ==>
    LENGTH (FILTER ($= (Var u)) copy_inst.inst_operands) <= 1) /\
  (?v. MEM (Var v) copy_inst.inst_operands /\
    v IN pointer_derived_vars copy_fn {"p";"q"} /\
    (?ops. (mem_write_ops copy_inst = SOME ops \/
            mem_read_ops copy_inst = SOME ops) /\ ops.iao_ofst = Var v))
Proof
  conj_tac >- suspend "relation" >>
  simp[alloca_remap_rel_def, pointer_confined_def, all_mem_via_pointer_def,
       affine_pointer_ops_def, pointer_arith_in_region_def,
       phi_pv_all_var_def, alloca_safe_access_def, copy_no_propagation,
       copy_fn_def, copy_bb_def, copy_inst_def, mk_raw_function_def,
       copy_s1_def, copy_s2_def, copy_remap_def,
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
  FIRST [qexists_tac `instruction 0 ALLOCA [Lit 32w] ["p"]` >> simp[] >> NO_TAC,
         qexists_tac `instruction 1 ALLOCA [Lit 32w] ["q"]` >> simp[] >> NO_TAC,
         qexists_tac `"p"` >> simp[] >>
         qexists_tac `<|iao_ofst := Var "p"; iao_size := SOME (Lit 32w);
                       iao_max_size := SOME (Lit 32w)|>` >> simp[]]
QED

Resume mcopy_remap_inputs[relation]:
  simp[alloca_remap_rel_def, copy_no_propagation,
       copy_fn_def, copy_bb_def, copy_inst_def, mk_raw_function_def,
       fn_alloca_id_of_var_def, copy_s1_def, copy_s2_def, copy_remap_def,
       store_s1_def, store_s2_def, store_remap_def,
       update_var_def, lookup_var_def, init_venom_state_def,
       FLOOKUP_UPDATE, alloca_mem_agrees_def, in_alloca_region_def,
       allocas_non_overlapping_def, mem_byte_at_def] >>
  CONV_TAC (DEPTH_CONV fcpLib.INDEX_CONV) >> simp[dimword_def] >>
  rpt conj_tac >> rw[] >> gvs[AllCaseEqs()] >>
  gvs[fn_insts_def, fn_insts_blocks_def, is_alloca_op_def,
      FIND_thm, instruction_accessors] >>
  EVAL_TAC >> simp[] >>
  qexistsl_tac [`1`,`64`,`32`,`64`] >> EVAL_TAC
QED
Finalise mcopy_remap_inputs

Theorem mcopy_remap_output:
  ~(?v2. step_inst_base copy_inst copy_s2 = OK v2 /\
    alloca_remap_rel copy_fn {"p";"q"} copy_remap
      (mcopy 0 64 32 copy_s1) v2)
Proof
  simp[copy_inst_def, step_inst_base_def, copy_s2_def, store_s2_def,
       eval_operand_def, lookup_var_def, update_var_def, FLOOKUP_UPDATE] >>
  strip_tac >>
  fs[alloca_remap_rel_def, LET_DEF, mcopy_def,
     write_memory_with_expansion_def, write_memory_def,
     copy_s1_def, store_s1_def, store_s2_def,
     update_var_def, init_venom_state_def] >>
  CONV_TAC (DEPTH_CONV fcpLib.INDEX_CONV) >> simp[expand_memory_def]
QED

(* MSTORE also satisfies the old memory-helper's extra pointer antecedent. *)
Theorem mstore_memory_helper_inputs:
  ~is_immutable_op memory_inst.inst_opcode /\
  MEM memory_bb memory_fn.fn_blocks /\ MEM memory_inst memory_bb.bb_instructions /\
  (?v. MEM (Var v) memory_inst.inst_operands /\
       v IN pointer_derived_vars memory_fn {"p"})
Proof
  simp[memory_inst_def, memory_bb_def, memory_fn_def, mk_raw_function_def,
       memory_no_propagation, is_immutable_op_def]
QED
