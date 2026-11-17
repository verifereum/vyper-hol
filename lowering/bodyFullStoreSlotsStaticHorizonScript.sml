Theory bodyFullStoreSlotsStaticHorizon
Ancestors
  bodyFullStoreSlotsStaticTransfer fragGasOriginPtr fragGasOrigin fragGasPathPtr
  ptrSafeRun gasCount gasEvents venomExecSemantics venomState venomInst
  list arithmetic

Theorem slots_readonly_ptr_horizon[local]:
  MEM i.inst_opcode [ASSIGN;ADD;MUL;EQ;LT;ISZERO;SHR;MLOAD;JMP;JNZ] /\
  ptr_safe_step D0 lo fuel ctx func PG G tn i s ==>
  !D. ptr_safe_step D lo fuel ctx func PG G tn i s
Proof
  strip_tac >> drule slots_readonly_step_frame >> strip_tac >>
  gvs[ptr_safe_step_def, ptr_inst_ok_def, MEM] >>
  metis_tac[prim_recTheory.LESS_REFL]
QED

Theorem store_slots_readonly_edge_horizon:
  lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
  get_instruction bb s.vs_inst_idx = SOME i /\
  MEM i.inst_opcode [ASSIGN;ADD;MUL;EQ;LT;ISZERO;SHR;MLOAD;JMP;JNZ] /\
  gas_origin_ptr_edge (D0,lo,explicit,ctx,func,PG) (s,G,tn) [] (OK u,G',tn') ==>
  !D. gas_origin_ptr_edge (D,lo,explicit,ctx,func,PG) (s,G,tn) [] (OK u,G',tn')
Proof
  disch_then (REPEAT_TCL CONJUNCTS_THEN assume_tac) >>
  drule gas_origin_ptr_edge_common_fuel >>
  disch_then (CONJUNCTS_THEN2 assume_tac
    (qx_choose_then `fuel` (qx_choose_then `bb1` (qx_choose_then `inst`
      (qx_choose_then `middle` (REPEAT_TCL CONJUNCTS_THEN assume_tac)))))) >>
  gnvs[Excl "MEM"] >>
  drule_all (SRULE[MEM] slots_readonly_ptr_horizon) >> strip_tac >>
  gen_tac >>
  rewrite_tac[gas_origin_ptr_edge_def] >>
  conj_tac >- (gvs[gas_origin_ptr_edge_def]) >>
  rewrite_tac[gas_path_ptr_edge_def] >> simp[] >>
  qexists_tac `fuel` >>
  simp[] >>
  `gas_count_step fuel ctx i s = 0` by
    (gvs[MEM] >> simp[gas_count_step_def]) >>
  simp[]
QED

Theorem store_slots_readonly_list_horizon:
  (!n a Ga tna b Gb tnb.
    SUC n < LENGTH L /\ EL n L = (a,Ga,tna) /\
    EL (SUC n) L = (b,Gb,tnb) ==>
    ?bb i. lookup_block a.vs_current_bb func.fn_blocks = SOME bb /\
      get_instruction bb a.vs_inst_idx = SOME i /\
      MEM i.inst_opcode [ASSIGN;ADD;MUL;EQ;LT;ISZERO;SHR;MLOAD;JMP;JNZ] /\
      gas_origin_ptr_edge (D0,lo,explicit,ctx,func,PG)
        (a,Ga,tna) [] (OK b,Gb,tnb)) ==>
  !D n a Ga tna b Gb tnb.
    SUC n < LENGTH L /\ EL n L = (a,Ga,tna) /\
    EL (SUC n) L = (b,Gb,tnb) ==>
    ?bb i. lookup_block a.vs_current_bb func.fn_blocks = SOME bb /\
      get_instruction bb a.vs_inst_idx = SOME i /\
      MEM i.inst_opcode [ASSIGN;ADD;MUL;EQ;LT;ISZERO;SHR;MLOAD;JMP;JNZ] /\
      gas_origin_ptr_edge (D,lo,explicit,ctx,func,PG)
        (a,Ga,tna) [] (OK b,Gb,tnb)
Proof
  rpt strip_tac >> first_x_assum drule_all >> strip_tac >>
  drule_all store_slots_readonly_edge_horizon >> metis_tac[]
QED
