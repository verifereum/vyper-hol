(* Static inputs at the concrete nonempty Array round cut. *)
Theory bodyForArrayConsCutsMods
Ancestors
  bodyForArrayCodeCutsMods bodyFullForArrayRound stmtSimProps
  bodyInvCodeProps bodySim compileEnv loweringPosts
Libs
  monadsyntax

Theorem for_array_cons_cut_inputs_mods:
  for_nonslot_layout (c,id,fty,e,sty,bd,ret_ty,loop_body) (func,shadow_func)
    (sa0,vv,sbExpr,shadow_sa0,shadow_sbExpr,loc,len_op,saL)
    (bc,saD,saA,xd,capacity,aidItem)
    (entry,cond,bod,incr,exit,idx,invalid,valid,done_var,next_var)
    (sa,stride,off_op,sm,sum_op,sn,addr,saCopy,sbCopy)
    (sbBody,sj,sb,shadow_sbCopy,shadow_sbBody) /\
  acyclic_struct_metadata c.ce_struct_fields /\
  (loc = LocMemory \/ loc = LocCode) /\
  ~block_is_terminated sbCopy /\
  evaluate_type (get_tenv cx) fty = SOME tyv /\
  capacity = type_memory_size tyv ==>
  ?inst bc_out.
    MEM inst (fn_insts func) /\
    inst.inst_id = aidItem /\
    inst.inst_opcode = ALLOCA /\
    inst.inst_outputs = [xd] /\
    ~block_is_terminated sbCopy /\
    stmts_env bc (InLoop exit incr) ret_ty loop_body sbCopy = (bc_out,sbBody) /\
    type_memory_size tyv <= capacity
Proof
  strip_tac >>
  qpat_x_assum `for_nonslot_layout _ _ _ _ _ _ _`
    (map_every assume_tac o CONJUNCTS o REWRITE_RULE [for_nonslot_layout_def]) >>
  `MEM (mk_inst saL.cs_next_id ALLOCA [Lit (n2w capacity)] [xd])
      (fn_insts func)` by
    (qpat_assum `compile_alloc_buffer _ saL = _`
       (fn th =>
         map_every assume_tac o CONJUNCTS o
         SIMP_RULE (srw_ss()) [] o
         MATCH_MP loweringHaltTheory.compile_alloc_buffer_insts $ th) >>
     irule compileAllocaProvenanceTheory.fn_has_code_current_member >>
     qexistsl [`saL`,`saA`] >> simp[]) >>
  `stmts_env bc (InLoop exit incr) ret_ty loop_body sbCopy =
      (FST (stmts_env bc (InLoop exit incr) ret_ty loop_body sbCopy),sbBody)` by
    (qpat_assum `compile_stmts bc _ ret_ty loop_body sbCopy = _`
       (mp_tac o REWRITE_RULE [compile_stmts_env]) >>
     simp[] >> metis_tac[pairTheory.PAIR]) >>
  qexistsl [`mk_inst saL.cs_next_id ALLOCA [Lit (n2w capacity)] [xd]`,
    `FST (stmts_env bc (InLoop exit incr) ret_ty loop_body sbCopy)`] >>
  rpt conj_tac >> simp[venomInstTheory.mk_inst_def]
QED
