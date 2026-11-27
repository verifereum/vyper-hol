(* The item allocation and body compiler cut shared by the Array routes. *)
Theory bodyForArrayLayoutItemCutMods
Ancestors
  bodyFullForArrayRound compileAllocaProvenance loweringHalt
  stmtSimProps venomInst

Theorem for_array_layout_item_cut_mods:
  for_nonslot_layout (c,id,fty,e,sty,bd,ret_ty,loop_body) (func,shadow_func)
    (sa0,vv,sbExpr,shadow_sa0,shadow_sbExpr,loc,len_op,saL)
    (bc,saD,saA,xd,capacity,aidItem)
    (entry,cond,bod,incr,exit,idx,invalid,valid,done_var,next_var)
    (sa,stride,off_op,sm,sum_op,sn,addr,saCopy,sbCopy)
    (sbBody,sj,sb,shadow_sbCopy,shadow_sbBody) ==>
  ?inst bc_out.
    MEM inst (fn_insts func) /\
    inst.inst_id = aidItem /\
    inst.inst_opcode = ALLOCA /\
    inst.inst_outputs = [xd] /\
    stmts_env bc (InLoop exit incr) ret_ty loop_body sbCopy = (bc_out,sbBody)
Proof
  disch_then (strip_assume_tac o REWRITE_RULE [for_nonslot_layout_def]) >>
  `MEM (mk_inst saL.cs_next_id ALLOCA [Lit (n2w capacity)] [xd])
      (fn_insts func)` by
    (drule_then (strip_assume_tac o SIMP_RULE (srw_ss()) [])
       compile_alloc_buffer_insts >>
     irule fn_has_code_current_member >>
     qexistsl [`saL`,`saA`] >> simp[]) >>
  qexistsl [`mk_inst saL.cs_next_id ALLOCA [Lit (n2w capacity)] [xd]`,
    `FST (stmts_env bc (InLoop exit incr) ret_ty loop_body sbCopy)`] >>
  simp[mk_inst_def] >>
  qpat_x_assum `compile_stmts bc _ ret_ty loop_body sbCopy = _`
    (mp_tac o REWRITE_RULE [compile_stmts_env]) >>
  simp[] >> metis_tac[pairTheory.PAIR]
QED
