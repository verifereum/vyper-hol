Theory o1ContractCfgNormJointCursors
Ancestors
  o1ContractCfgNormCursors o1ContractCfgNormCursorBlocks
  o1ContractCfgNormCursorCalls o1ContractCfgNormCursorReturns
  o1ContractCfgNormCursorProjection o1ContractCfgNorm o1PassContract o1PassLift
  cfgNormSupplySim cfgNormDefs frameJointTransition frameOriginHistory
  venomExecSemantics venomExecProofs venomStepProps venomInst venomState
  venomWf venomWfProps unitShapeDefs unitTransformDefs stateFrame
  ptrDiscipline contextCodegenRel ctxLookupAgreeHelpers
  list rich_list finite_map arithmetic pair option

(* Fixed schedule data is selected before runtime entries. Saved cells
   belong to the actual paired call frames; histories remain independent.
   Head equality alone cannot classify a stutter: a real self-loop can
   also leave the head fixed. Administrative cases require their opcode
   classification from the cursor construction. *)

Definition cfg_norm_joint_cursors_def:
  cfg_norm_joint_cursors C8 C9 (schedules,(rounds,cells),saved)
    (JointConfig stk8 PG8 G8 tn8 fn8 inst8 s8 oms8 om8 hs8 h8)
    (JointConfig stk9 PG9 G9 tn9 fn9 inst9 s9 oms9 om9 hs9 h9) <=>
  C9.ctx_entry = C8.ctx_entry /\
  ALL_DISTINCT (MAP (\fn. fn.fn_name) C8.ctx_functions) /\
  MAP FST schedules = C8.ctx_functions /\
  MAP (FST o SND) schedules = C9.ctx_functions /\
  EVERY (\(sf,tf,rs).
    ?s t meta.
      supply_norm_inv s sf /\ EVERY label_positions_ok (fn_insts sf) /\
      cfg_norm_function_supply s sf = (tf,t) /\
      sf.fn_name = tf.fn_name /\ fn_entry_label sf = fn_entry_label tf /\
      rs <> [] /\ HD rs = (s,sf,meta) /\ LAST rs = (t,tf,NONE) /\
      LENGTH rs <= SUC (2 * LENGTH sf.fn_blocks) /\
      !C cs v inst.
        fn_entry_state sf cs /\ enters_block tf cs v /\ active_inst tf inst v ==>
        ?cur first a.
          cfg_norm_cursors C rs cur /\
          LAST cur = ((inst,v),NONE) /\ HD cur = ((first,a),NONE) /\
          enters_block sf cs a) schedules /\
  MEM (fn8,fn9,rounds) schedules /\
  cfg_norm_cursors C8 rounds cells /\
  (?pending. HD cells = ((inst8,s8),pending)) /\
  LAST cells = ((inst9,s9),NONE) /\
  LENGTH stk8 = LENGTH stk9 /\
  LENGTH oms8 = LENGTH stk8 /\ LENGTH hs8 = LENGTH stk8 /\
  LENGTH oms9 = LENGTH stk9 /\ LENGTH hs9 = LENGTH stk9 /\
  LIST_REL (\(rs,cur) (f8,f9).
    MEM (f8.cf_fn,f9.cf_fn,rs) schedules /\
    cfg_norm_cursors C8 rs cur /\
    (?pending. HD cur = ((f8.cf_inst,f8.cf_state),pending)) /\
    LAST cur = ((f9.cf_inst,f9.cf_state),NONE) /\
    f8.cf_inst.inst_opcode = INVOKE /\ f9.cf_inst.inst_opcode = INVOKE)
    saved (ZIP (stk8,stk9))
End

(* Initialization must prove the static certificate in the wrapper, rather
   than take it as a callback premise. The state fields are actual entry
   requirements: joint_initial alone allows arbitrary variables/halted. *)
Theorem cfg_norm_joint_cursors_initial:
  ctx_pass_stage rp (CFP_Simple VP_CFGNormalization) view C8 C9 /\
  o1_ctx_shape C8 /\ EVERY wf_ssa C8.ctx_functions ==>
  ?schedules.
    !vs0 q8 q9.
      vs0.vs_vars = FEMPTY /\ ~vs0.vs_halted /\
      joint_initial vs0 C8 q8 /\ joint_initial vs0 C9 q9 ==>
      ?current. cfg_norm_joint_cursors C8 C9 (schedules,current,[]) q8 q9
Proof
  rpt strip_tac >> drule cfg_norm_stage_functions >> strip_tac
QED

(* Stronger than the generic ML goal only in explicitly retaining the
   SAME schedules. Current/saved cells evolve through actual transitions. *)
Theorem cfg_norm_joint_cursors_step:
  !C8 C9 schedules current saved
    stk8 PG8 G8 tn8 fn8 inst8 s8 oms8 om8 hs8 h8
    stk9 PG9 G9 tn9 fn9 inst9 s9 oms9 om9 hs9 h9 ev q9'.
    cfg_norm_joint_cursors C8 C9 (schedules,current,saved)
      (JointConfig stk8 PG8 G8 tn8 fn8 inst8 s8 oms8 om8 hs8 h8)
      (JointConfig stk9 PG9 G9 tn9 fn9 inst9 s9 oms9 om9 hs9 h9) /\
    joint_transition C9
      (JointConfig stk9 PG9 G9 tn9 fn9 inst9 s9 oms9 om9 hs9 h9) ev q9' ==>
    mem_corr inst8 s8 inst9 s9 /\ call_corr inst8 s8 inst9 s9 /\
    (inst_mem_ranges inst9 s9 <> [] /\ ~in_revert_forward fn9 s9 ==>
      ~in_revert_forward fn8 s8) /\
    ?current' saved' q8'.
      ((q8' = JointConfig stk8 PG8 G8 tn8 fn8 inst8 s8 oms8 om8 hs8 h8 /\
        MEM inst9.inst_opcode [ASSIGN; JMP; JNZ] /\
        inst9.inst_opcode <> GAS /\ inst9.inst_opcode <> INVOKE /\
        inst_mem_ranges inst9 s9 = []) \/
       ?ev8. joint_transition C8
         (JointConfig stk8 PG8 G8 tn8 fn8 inst8 s8 oms8 om8 hs8 h8) ev8 q8') /\
      cfg_norm_joint_cursors C8 C9 (schedules,current',saved') q8' q9'
Proof
  rpt gen_tac >> strip_tac >> Cases_on `current` >>
  fs[cfg_norm_joint_cursors_def]
QED
