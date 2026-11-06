Theory bodyPtrPopCodeContainment
Ancestors
  bodyPtrPopConsumerCut bodyPtrPopFrameProbe fragExec context emitHelper
  venomInst compileEnv rich_list emitHelperProps loweringPosts

(* fn_has_code_current_inst in bodyPtrCallCalldata already handles an
   intermediate current block.  Here no append premise is needed: the
   final current block is part of fn_has_code even for an empty fragment. *)
Theorem pop_code_final_inst:
  fn_has_code sa sb func /\ MEM inst sb.cs_current_insts ==>
  MEM inst (fn_insts func)
Proof
  rw[fn_has_code_def] >>
  irule lookup_block_fn_insts >> goal_assum (drule_at Any) >>
  metis_tac[IS_PREFIX_MEM]
QED

Theorem pop_code_finished_inst:
  fn_has_code sa sb func /\ MEM bb (emitted_blocks sa sb) /\
  MEM inst bb.bb_instructions ==> MEM inst (fn_insts func)
Proof
  rw[fn_has_code_def] >>
  irule lookup_block_fn_insts >>
  first_x_assum drule >> strip_tac >> goal_assum (drule_at Any) >> simp[]
QED

(* The frame-to-function lookup projection already exists, uniquely, as
   pop_stmt_frame_function_lookup in bodyPtrPopFrameProbe.  Reuse it. *)

(* At compile_array_subscript's dynamic branch (exprLowering:1367),
   sj is the post-index state, sk the result of its first loader action.
   sf is the end of the WHOLE Pop fragment.  These append premises locate
   the loader in that fragment without assuming that it finishes a block.
   This is code containment only: it asserts no raw storage agreement. *)
Theorem pop_saved_header_load_in_function:
  compile_ptr_load is_ctor imm (slot_loc tr) base_op sj = (len_op,sk) /\
  cs_extends sa sj /\ cs_extends sj sk /\ cs_extends sk sf /\
  fn_has_code sa sf func ==>
  MEM (mk_inst sj.cs_next_id (if tr then TLOAD else SLOAD) [base_op]
         [STRING #"%" (toString sj.cs_next_var)]) (fn_insts func)
Proof
  strip_tac >>
  `fn_has_code sj sk func` by metis_tac[fn_has_code_mid] >>
  irule pop_code_final_inst >> goal_assum (drule_at Any) >>
  Cases_on `tr` >> gvs[slot_loc_def, compile_ptr_load_def] >>
  drule emitted_insts_emit_op >> simp[]
QED
