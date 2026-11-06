(* Contained field capacity for actual memory projections. *)
Theory bodyFieldMemory
Ancestors
  loweringPosts gasOutcome gasSummary
  bodyFieldMemoryProps bodyFieldValueMemory bodyFieldForceMemory
  exprSimAttributeProps exprSimFieldLayout exprSimProps exprSimVVFrame
  bodyNameValueMemory
  bodyNameMemoryFacts
  exprSimSource
  exprSimAttributeFields bodyAllocMemory
  valueEncoding compileEnv venomState words list rich_list finite_map
  exprSimAttribute exprSimHash exprSimLiteralBuffer exprOperandVar
  exprSimBuffer exprSimAggregateChildren exprSimDefs context
  exprLowering exprLoweringProps emitHelper emitHelperProps fragExec fragExecMem instMemFrontier
  allocaHistoryFragment venomInst vyperAST vyperTyping vyperInterpreter
  exprSimHyps vyperTypeSystem vyperTypeInvariants allocLimits
  bodyMemoryDefs exprSimUnwrap vyperState exprSimLen vyperTypeExprSoundness

(* The field pointer of a local struct's field, with room below the
   frontier for the field's whole type, under the counted contract: the
   capacity comes from bodyFieldValueMemory's counted prefix.  Restated
   from a fixed-run frag_exec_mem form whose post read the end state with
   the source's gas observations still attached. *)
Theorem compile_attribute_name_body_capacity_mem:
  expr_body_pre cenv cx env (Attribute ann (Name (StructT sid) id) fld) es /\
  compile_expr cenv ty (Attribute ann (Name (StructT sid) id) fld) sa = (vv,sb) /\
  fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
  local_ptrs_reserved cenv sa /\ stmt_state_rel ctx func cenv cx es s0 /\
  alloca_history func s0 /\ ~s0.vs_halted /\
  s0.vs_current_bb = sa.cs_current_bb /\
  s0.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  gas_outcome T (cx_tops cx) (ctx,func)
    (eval_expr cx (Attribute ann (Name (StructT sid) id) fld)) (es,s0)
    (\res ee t. (?tv. res = INL tv /\
               vv_post ctx func cenv cx (Attribute ann (Name (StructT sid) id) fld)
                 es sa sb s0 ee tv vv t) /\
         vv_loc vv = LocMemory /\
         (?ftv w. evaluate_type (get_tenv cx) ann = SOME ftv /\
                  eval_operand (vv_operand vv) t = SOME w /\
                  w2n w + type_memory_size ftv <= t.vs_alloca_next) /\
         s0.vs_alloca_next <= t.vs_alloca_next /\ alloca_history func t)
    (\res ee r. expr_exit res r)
Proof
  strip_tac >> drule_all body_attribute_name_counted_prefix >> strip_tac >>
  rewrite_tac[gas_outcome_def] >> qexists_tac `[]` >> disj1_tac >>
  rewrite_tac[gas_summary_at_def] >>
  qexistsl_tac [`INL tv`, `es`, `OK t`] >>
  gvs[vv_loc_def, vv_location_def, mk_ptr_def, vv_operand_def]
QED
