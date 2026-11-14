(* Runtime-count memory-to-slot loops with uniform joint endpoints. *)
Theory fullStoreSlotsWordLoop
Ancestors
  fullStoreSlotsWordCode fullStoreSlotsWordBody fullStoreSlotsUniformLoop
  placeStoreCopyPath fragGasCopyLoop fragGasSeqAbort bodyMemAssignTopCopyPaths
  codegenRel ptrDiscipline bodyPtrDefs memSafeRun venomState venomInst venomExecSemantics
  words finite_map pred_set list rich_list arithmetic

Theorem store_slots_word_init:
  ~ctx_has_dalloca ctx /\ allocas_from lo s /\ ~s.vs_halted /\
  lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
  isPREFIX [mk_inst id ASSIGN [Lit 0w] [cv];
    mk_inst (id+1) JMP [Label hdr] []]
    (DROP s.vs_inst_idx bb.bb_instructions) /\
  (!y. not_fresh_at sa y ==> y <> cv) ==>
  ?u Gf tnf.
    (!D explicit PG. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG)
       (s,G,tn) [] (OK u,Gf,tnf)) /\
    store_copy_frame sa loc b k s 0 u /\
    eval_operand (Var cv) u = SOME 0w /\ op_prov Gf (Var cv) = NONE /\
    op_taint tnf (Var cv) = {} /\ allocas_from lo u /\ ~u.vs_halted /\
    u.vs_current_bb = hdr /\ u.vs_inst_idx = 0 /\
    (!y. not_fresh_at sa y ==> FLOOKUP Gf y = FLOOKUP G y /\
       op_taint tnf (Var y) = op_taint tn (Var y)) /\
    tnf.t_mem = tn.t_mem /\ tnf.t_stor = tn.t_stor /\
    tnf.t_trans = tn.t_trans /\ tnf.t_imm = tn.t_imm
Proof
  strip_tac >>
  drule instruction_prefix_cursor >> strip_tac >>
  drule instruction_prefix_cursor >> strip_tac >>
  `isPREFIX [mk_inst id ASSIGN [Lit 0w] [cv]]
     (DROP s.vs_inst_idx bb.bb_instructions)` by
    (qpat_x_assum `isPREFIX (_::_::_) _` mp_tac >>
     Cases_on `DROP s.vs_inst_idx bb.bb_instructions` >> simp[]) >>
  `get_instruction bb (s.vs_inst_idx+1) =
     SOME (mk_inst (id+1) JMP [Label hdr] [])` by gvs[ADD1] >>
  drule_all copy_init_origin_ptr >>
  simp[step_prov_def,out_prov_def,first_prov_def,op_prov_def,set_prov_def,
    step_taint_def,set_var_taint_def,out_taint_def,mem_taint_def,
    imm_taint_def,store_taint_def,adopt_reset_def,step_writes_def,
    source_memory_write_ranges_def,written_taint_def,range_bytes_def,
    new_site_bytes_def,eval_operand_def,mk_inst_def,update_var_def,
    op_taint_def,FLOOKUP_DEF,SF CONJ_ss,taint_component_equality] >> strip_tac >>
  qexistsl_tac [`jump_to hdr (update_var cv 0w s with vs_inst_idx := s.vs_inst_idx+1)`,
    `DRESTRICT G (COMPL {cv})`,
    `<|t_mem := tn.t_mem; t_var := tn.t_var |+ (cv,{});
       t_stor := tn.t_stor; t_trans := tn.t_trans; t_imm := tn.t_imm|>`] >>
  conj_tac >- simp[update_var_def] >>
  conj_tac >- (simp[] >> irule topcopy_frame_update >> simp[] >> metis_tac[]) >>
  simp[jump_to_def,update_var_def,eval_operand_def,lookup_var_def,
    FLOOKUP_UPDATE,op_prov_def,op_taint_def,FLOOKUP_DRESTRICT] >>
  gvs[allocas_from_def,FDOM_DRESTRICT,DRESTRICT_DEF,FAPPLY_FUPDATE_THM] >>
  metis_tac[]
QED

Theorem store_slots_word_header_frame:
  lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
  get_instruction bb s.vs_inst_idx = SOME (mk_inst id EQ [Var cv;cnt] [tv]) /\
  get_instruction bb (SUC s.vs_inst_idx) =
    SOME (mk_inst jid JNZ [Var tv;Label yes;Label no] []) /\
  eval_operand (Var cv) s = SOME (n2w j) /\ eval_operand cnt s = SOME (n2w n) /\
  op_taint tn (Var cv) = {} /\ op_taint tn cnt = {} /\
  op_prov G (Var cv) = NONE /\ op_prov G cnt = NONE /\
  ~ctx_has_dalloca ctx /\ allocas_from lo s /\ ~s.vs_halted /\
  cv <> tv /\ (!y. not_fresh_at sa y ==> y <> tv) /\
  store_copy_frame sa loc b k sbase j s /\ j <= n /\ n < dimword (:256) ==>
  ?u Gf tnf.
    (!D explicit PG. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG)
      (s,G,tn) [] (OK u,Gf,tnf)) /\
    store_copy_frame sa loc b k sbase j u /\
    eval_operand (Var cv) u = SOME (n2w j) /\
    op_prov Gf (Var cv) = NONE /\ op_taint tnf (Var cv) = {} /\
    allocas_from lo u /\ ~u.vs_halted /\ u.vs_inst_idx = 0 /\
    u.vs_current_bb = (if j=n then yes else no) /\
    (!y. not_fresh_at sa y ==> FLOOKUP Gf y = FLOOKUP G y /\
      op_taint tnf (Var y) = op_taint tn (Var y)) /\
    tnf.t_mem = tn.t_mem /\ tnf.t_imm = tn.t_imm /\
    tnf.t_stor = tn.t_stor /\ tnf.t_trans = tn.t_trans
Proof
  strip_tac >>
  drule_all store_slots_word_header_origin_ptr >>
  `((n2w j):bytes32 = n2w n) <=> j=n` by simp[n2w_11,LESS_MOD] >>
  simp[] >> strip_tac >>
  qexistsl [`jump_to (if j=n then yes else no)
    (update_var tv (bool_to_word (j=n)) s with vs_inst_idx := SUC s.vs_inst_idx)`,
    `DRESTRICT G (COMPL {tv})`, `tn with t_var := tn.t_var |+ (tv,{})`] >>
  conj_tac >- simp[] >>
  conj_tac >- (simp[] >> irule topcopy_frame_update >> simp[] >> metis_tac[]) >>
  gvs[jump_to_def,update_var_def,eval_operand_def,lookup_var_def,
    FLOOKUP_UPDATE,op_prov_def,op_taint_def,FLOOKUP_DRESTRICT,allocas_from_def] >>
  conj_tac >- metis_tac[] >> rpt strip_tac >>
  `y <> tv` by metis_tac[] >> simp[]
QED

