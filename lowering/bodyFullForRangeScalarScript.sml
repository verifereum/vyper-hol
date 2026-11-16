(* Independent concrete increment producer, relocated unchanged from Range.
   Scalar ghost frame producers already live in forPtrCheckedScalar. *)
Theory bodyFullForRangeScalar
Ancestors
  fragGasOriginPtrLoop fragGasSeqPtr fragGasSeqMem fragExecMem
  instMemFrontier venomExecSemantics venomExecProofs venomInst venomState
  ptrDiscipline list words fragExec exprLoweringProps memSafeRun
  fragGasEmitCtrl exprPtrUnwrapCopyEdges emitHelperProps fragGasOriginPtr
  vyperStorageFootprint ptrSafeRun forPtrCheckedScalar finite_map codegenRel contextCodegenRel

Theorem for_range_incr_path_full_valid:
  code = [mk_inst i1 ADD [Var cv; Lit 1w] [nv];
          mk_inst i2 ASSIGN [Var nv] [cv]] /\
  bb = <|bb_label := lbl; bb_instructions :=
          code ++ [mk_inst i3 JMP [Label cond_lbl] []]|> /\
  lookup_block lbl func.fn_blocks = SOME bb /\
  dd.vs_current_bb = lbl /\ dd.vs_inst_idx = 0 /\ ~dd.vs_halted /\
  lookup_var cv dd = SOME c /\
  ~ctx_has_dalloca ctx /\ allocas_from lo dd /\
  (!H. valid_horizon cx st0 H es.storage_trace ==>
       inst_seq_ptr (DF H) lo ctx func PG G tn code dd Gf tf) ==>
  !H. valid_horizon cx st0 H es.storage_trace ==>
    gas_origin_ptr_path (DF H,lo,explicit,ctx,func,PG) (dd,G,tn) []
      (OK (jump_to cond_lbl
        (update_var cv (c+1w) (update_var nv (c+1w) dd))),Gf,tf)
Proof
  strip_tac >> gen_tac >> strip_tac >>
  qpat_x_assum `!H. valid_horizon _ _ H _ ==> _` drule >> strip_tac >>
  qabbrev_tac `u = update_var cv (c+1w) (update_var nv (c+1w) dd)` >>
  `run_inst_seq code dd = OK u` by
    simp[run_inst_seq_def,step_inst_base_opcode_eqs,mk_inst_def,
         eval_operand_def,exec_pure2_def,lookup_var_def,update_var_def,
         finite_mapTheory.FLOOKUP_UPDATE,Abbr `u`] >>
  `run_inst_seq_mem_ok code dd` by
    (irule run_inst_seq_mem_ok_every >>
     gvs[mk_inst_def,below_frontier_no_ranges,inst_dload_in_section_other]) >>
  `gas_origin_ptr_path (DF H,lo,explicit,ctx,func,PG) (dd,G,tn) []
     (OK (u with vs_inst_idx := 2),Gf,tf)` by
    (drule_at (Pat `run_inst_seq _ _ = _`) run_inst_seq_gas_origin_ptr_path >>
     simp[mk_inst_def,is_terminator_def] >>
     disch_then irule >> gvs[mk_inst_def,is_terminator_def]) >>
  `gas_origin_ptr_path (DF H,lo,explicit,ctx,func,PG)
     (u with vs_inst_idx := 2,Gf,tf) []
     (OK (jump_to cond_lbl (u with vs_inst_idx := 2)),Gf,tf)` by
    (irule jmp_origin_ptr_path >>
     simp[Abbr `u`,update_var_def,get_instruction_def,allocas_from_def] >>
     conj_tac >- (qexists_tac `i3` >> simp[]) >> gvs[allocas_from_def]) >>
  drule_all gas_origin_ptr_path_trans >> simp[jump_to_def,Abbr `u`]
QED

(* The increment ghosts are computed once, before a horizon is supplied. *)
Theorem for_range_increment_sequence_full:
  allocas_from lo s /\ ~ctx_has_dalloca ctx /\
  FLOOKUP G cv = NONE /\ op_taint tn (Var cv) = {} /\
  lookup_var cv s = SOME c ==>
  !D. inst_seq_ptr D lo ctx func PG G tn
    [mk_inst i1 ADD [Var cv; Lit 1w] [nv];
     mk_inst i2 ASSIGN [Var nv] [cv]] s
    (step_prov PG
      (step_prov PG G (mk_inst i1 ADD [Var cv; Lit 1w] [nv])
        (update_var nv (c+1w) s))
      (mk_inst i2 ASSIGN [Var nv] [cv])
      (update_var cv (c+1w)
        (update_var nv (c+1w) s with vs_inst_idx := SUC s.vs_inst_idx)))
    (step_taint (mk_inst i2 ASSIGN [Var nv] [cv])
      (update_var nv (c+1w) s with vs_inst_idx := SUC s.vs_inst_idx)
      (update_var cv (c+1w)
        (update_var nv (c+1w) s with vs_inst_idx := SUC s.vs_inst_idx))
      (step_taint (mk_inst i1 ADD [Var cv; Lit 1w] [nv]) s
        (update_var nv (c+1w) s) tn))
Proof
  strip_tac >> simp_tac bool_ss [LET_THM] >> gen_tac >>
  simp[inst_seq_ptr_def,step_inst_base_opcode_eqs,mk_inst_def,
       eval_operand_def,exec_pure2_def,lookup_var_def,update_var_def,
       FLOOKUP_UPDATE] >>
  rpt conj_tac >>
  simp[ptr_inst_ok_def,access_ok_def,taint_ok_def,
       mk_inst_def,source_memory_write_ranges_def,source_memory_read_ranges_def,
       step_inst_non_invoke,
       op_taint_def,op_prov_def,allocas_from_def,
       step_prov_def,out_prov_def,set_prov_def,first_prov_def,
       step_taint_def,out_taint_def,set_var_taint_def,update_var_def,
       new_site_bytes_def,mem_taint_def,step_writes_def,store_taint_def,
       written_taint_def,adopt_reset_def,imm_taint_def,range_bytes_def,
       step_inst_base_opcode_eqs,eval_operand_def,exec_pure2_def,
       lookup_var_def,FLOOKUP_UPDATE] >>
  gvs[op_taint_def,allocas_from_def] >>
  gen_tac >> Cases_on `op = Var cv` >- gvs[] >>
  Cases_on `op = Lit 1w` >> gvs[]
QED

(* The concrete successful backedge chooses both ghost updates before D. *)
Theorem for_range_increment_path_full:
  bb = <|bb_label := lbl; bb_instructions :=
    [mk_inst i1 ADD [Var cv; Lit 1w] [nv];
     mk_inst i2 ASSIGN [Var nv] [cv];
     mk_inst i3 JMP [Label cond_lbl] []]|> /\
  lookup_block lbl func.fn_blocks = SOME bb /\
  s.vs_current_bb = lbl /\ s.vs_inst_idx = 0 /\ ~s.vs_halted /\
  allocas_from lo s /\ ~ctx_has_dalloca ctx /\
  FLOOKUP G cv = NONE /\ op_taint tn (Var cv) = {} /\
  lookup_var cv s = SOME c ==>
  ?Gf tf. !H. valid_horizon cx st0 H es.storage_trace ==>
    gas_origin_ptr_path (DF H,lo,explicit,ctx,func,PG) (s,G,tn) []
      (OK (jump_to cond_lbl
        (update_var cv (c+1w) (update_var nv (c+1w) s))),Gf,tf)
Proof
  strip_tac >>
  drule_all for_range_increment_sequence_full >>
  simp_tac bool_ss [LET_THM] >> strip_tac >>
  first_x_assum (qspecl_then [`nv`,`i2`,`i1`,`func`,`PG`] assume_tac) >>
  qmatch_asmsub_abbrev_tac `inst_seq_ptr _ _ _ _ _ _ _ _ _ Gf tf` >>
  qexistsl_tac [`Gf`,`tf`] >>
  gen_tac >> strip_tac >>
  irule for_range_incr_path_full_valid >> simp[] >>
  metis_tac[]
QED
