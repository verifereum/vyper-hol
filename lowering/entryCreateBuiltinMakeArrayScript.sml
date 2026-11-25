(* Selected MakeArray materialization at the compiler's element boundaries. *)
Theory entryCreateBuiltinMakeArray
Ancestors
  bodyFullMakeArray bodyFullMakeArrayLoop bodyFullMakeArrayStore
  entryCreateNativeFirstExit entryCreateIntervalLayout entryCreateAdminSequence
  createSizeCutCode createSizeCutOpens createSizeTypedCopyCode createSizeLocationCode
  exprSimAggregateLoops exprSimAggregateSource exprSimAggregateLayout
  abiBufferAllocationCode gasShadowCompileStmtHelpers gasShadowCompileConvert
  gasShadowCompileHelpers fragExec exprLoweringProps compileEnv
  emitHelperProps entryCreateFocusSpec bodyPtrMakeArrayPrimitiveInstall
  entryIntCallStageBuffer exprSimAbiEncodeObliviousCode createSizeCutRegion
  entryCreateStmtCases entryCreatePathScope list

(* The post-child element materialization is a closed interval, even when
   unwrap and typed store emit copy loops. *)
Theorem make_array_slot_suffix_code:
  emit_op ADD [buf; Lit (n2w off)] m = (dst,n) /\
  unwrap_value ce vv n = (op,u) /\
  compile_store_memory ce op dst mt (lowered_value_type ce e) u = ((),t) ==>
  create_cut_code {} m n /\ create_cut_code {} n u /\
  create_cut_code {} u t /\ create_cut_code {} m t
Proof
  strip_tac >>
  `create_cut_code {} m n` by
    (mp_tac (Q.INST [`opc` |-> `ADD`, `ops` |-> `[buf; Lit (n2w off)]`,
                     `a` |-> `m`, `exits` |-> `{}`] create_cut_code_emit_op) >>
     simp[create_cut_targets_def]) >>
  `create_cut_code {} n u` by
    metis_tac[create_unwrap_cut_code,pairTheory.SND] >>
  `create_cut_code {} u t` by
    metis_tac[create_store_memory_cut_code,pairTheory.SND] >>
  simp[] >> metis_tac[create_cut_code_join]
QED

Theorem make_array_header_cut:
  (if header then emit_void MSTORE [buf; Lit (n2w len)] else return ()) a =
    ((),b) /\ fn_has_code a b f /\ create_operand_at a s ==>
  create_cut_code {} a b /\
  create_operand_cut a b E C f tops cx st0 source (es,s)
Proof
  Cases_on `header` >> simp[comp_return_def]
  >- (strip_tac >> conj_tac
      >- (mp_tac (Q.INST [`opc` |-> `MSTORE`, `ops` |-> `[buf; Lit (n2w len)]`,
                          `exits` |-> `{}`] create_cut_code_emit_void) >>
          simp[create_cut_targets_def]) >>
      drule_all emit_void_fetch_boundary >> strip_tac >>
      irule create_admin_sequence_cut >> simp[] >>
      drule emitted_insts_emit_void >>
      simp[venomInstTheory.mk_inst_def,venomInstTheory.is_terminator_def]) >>
  strip_tac >> gvs[create_operand_cut_def, create_operand_empty_scope]
QED

Theorem make_array_alloc_cut:
  compile_alloc_buffer cap a = (ba,b) /\ fn_has_code a b f /\
  create_operand_at a s ==>
  create_cut_code {} a b /\
  create_operand_cut a b E C f tops cx st0 source (es,s)
Proof
  strip_tac >> conj_tac
  >- metis_tac[create_alloc_buffer_cut_code,pairTheory.SND] >>
  drule compile_alloc_buffer_code >> strip_tac >>
  irule create_admin_sequence_cut >>
  simp[venomInstTheory.mk_inst_def,venomInstTheory.is_terminator_def]
QED

Triviality make_array_slot_action:
  code_action (\opc. opc <> INVOKE /\ opc <> CREATE /\ opc <> CREATE2)
    (do dst <- emit_op ADD [buf; Lit (n2w off)];
        op <- unwrap_value ce vv;
        compile_store_memory ce op dst mt (lowered_value_type ce e)
     od)
Proof
  simp[code_action_bind, code_action_emit_op, buffer_unwrap_action,
       buffer_store_action]
QED

Theorem make_array_slot_suffix_visit:
  emit_op ADD [buf; Lit (n2w off)] m = (dst,n) /\
  unwrap_value ce vv n = (op,u) /\
  compile_store_memory ce op dst mt (lowered_value_type ce e) u = ((),t) /\
  body_inv tops C ce cx /\ MEM f C.ctx_functions /\ fn_has_code m t f /\
  create_interior_visit m t E C f (p,d,k) s (before,hit,after) ==>
  create_body_cut E tops cx st0 source (es,s0) (front,hit)
Proof
  strip_tac >>
  `create_cut_code {} m t` by metis_tac[make_array_slot_suffix_code] >>
  `EVERY (\i. ~MEM i.inst_opcode [INVOKE;CREATE;CREATE2]) (frag_code m t)` by
    (qspec_then `m` mp_tac (REWRITE_RULE [code_action_def] make_array_slot_action) >>
     simp[code_step_def, comp_bind_def]) >>
  drule_all create_cut_region_rules >> strip_tac >>
  `create_cut_region m t s` by fs[create_interior_visit_def,create_operand_at_def] >>
  drule create_interior_visit_cases >> strip_tac >>
  `create_cut_region m t u'` by metis_tac[create_expr_prefix_cut_region] >>
  fs[create_operand_fetch_def,create_operand_at_def,EVERY_MEM] >>
  `MEM inst (frag_code m t)` by metis_tac[] >>
  gvs[] >> irule create_cut_noncreate_visit >> metis_tac[]
QED
