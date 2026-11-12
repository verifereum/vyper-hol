(* Read-only memory instructions of the FMP stage simulation. *)
Theory fmpStageOpSimMemReads
Ancestors
  fmpStageOpSimMemSupport fmpStageOpBase fmpStageRel o1LowerDloadRangeTransport
  o1LowerDloadShared o1PassContract rich_list byte
  ptrDiscipline ptrStaticDiscipline contextCodegenRel unitShapeDefs venomExecSemantics
  venomState venomInst memLocDefs pointerConfinedDefs words finite_map pred_set list

Theorem fmp_mem_operand_non_retpc:
  fmp_stage_ctx rpolicy D C C' vs vs' fmp eom /\
  frame_reachable vs C stk PG G tn fn inst s /\ active_inst fn inst s /\
  MEM op inst.inst_operands /\ (!v. ~retpc_use_ok inst v) ==>
  (!v. op = Var v ==> ~retpc_var fn v)
Proof
  strip_tac >>
  `o1_fn_shape C fn /\ MEM inst (fn_insts fn)` by
    metis_tac[fmp_stage_frame_facts] >>
  fs[o1_fn_shape_def, fn_shape_ok_def, opaque_use_ok_def] >>
  metis_tac[]
QED

Theorem fmp_mem_word_read:
  fmp_stage_ctx rpolicy D C C' vs vs' fmp eom /\
  frame_reachable vs C stk PG G tn fn inst s /\ active_inst fn inst s /\
  fmp_stage_rel D C' sm fmp0 raw0 eom restored stk PG G tn fn s lo t ts /\
  ~in_revert_forward fn s /\ MEM inst.inst_opcode [MLOAD;ILOAD] /\
  inst.inst_operands = [p] /\ eval_operand p s = SOME x ==>
  ?y. eval_operand p t = SOME y /\
    word_agree_except (mem_word_taint tn.t_mem (w2n x))
      (mload (w2n x) s) (mload (w2n y) t)
Proof
  strip_tac >>
  `taint_ok fn tn inst s /\ o1_fn_shape C fn` by
    metis_tac[fmp_stage_frame_facts] >>
  `op_taint tn p = {}` by
    (fs[taint_ok_def] >> gvs[] >> metis_tac[]) >>
  `!v. p = Var v ==> ~retpc_var fn v` by
    (`!v. ~retpc_use_ok inst v` by gvs[retpc_use_ok_def] >>
     `MEM p inst.inst_operands` by simp[] >>
     metis_tac[fmp_mem_operand_non_retpc]) >>
  `?y. eval_operand p t = SOME y /\
    (32=0 \/ (w2n x=w2n y /\ w2n x+32<=eom) \/
     (?id b c z j. FLOOKUP (fmp_ld_sites sm) id = SOME (b,c,z) /\
       j+32<=z /\ w2n x=b+j /\ w2n y=c+j))` by
    (`mem_read_ops inst = SOME <|iao_ofst := p; iao_size := SOME (Lit 32w); iao_max_size := SOME (Lit 32w)|>` by
       gvs[mem_read_ops_def] >>
     `MEM (w2n x,32) (source_memory_read_ranges inst s)` by
       gvs[source_memory_read_ranges_def, memory_range_of_operands_def, eval_operand_def] >>
     `inst.inst_opcode <> PHI /\ MEM p inst.inst_operands` by gvs[] >>
     `(<|iao_ofst := p; iao_size := SOME (Lit 32w); iao_max_size := SOME (Lit 32w)|> : inst_access_ops).iao_ofst = p` by simp[] >>
     drule_all fmp_mem_read_operand_range >> simp[]) >>
  qexists_tac `y` >> gvs[] >>
  simp[word_agree_except_def, mload_def] >> rpt strip_tac >>
  simp[word_to_bytes_def, EL_word_to_bytes_aux,
       get_byte_word_of_bytes_be, LENGTH_TAKE_EQ, first_byte_at_0w, dimword_def] >>
  pure_rewrite_tac[GSYM read_memory_def] >>
  irule ld_memory_agree_slice_element >> simp[] >>
  qexistsl_tac [`eom`,`tn.t_mem`,`fmp_ld_sites sm`] >>
  gvs[fmp_stage_rel_def, mem_word_taint_def] >> metis_tac[]
QED

Theorem fmp_mem_sha3_size_prov[local]:
  fmp_stage_ctx rpolicy D C C' vs vs' fmp eom /\
  frame_reachable vs C stk PG G tn fn inst s /\ active_inst fn inst s /\
  inst.inst_opcode = SHA3 /\ inst.inst_operands = [p;sz] ==>
  op_prov G sz = NONE
Proof
  strip_tac >>
  `MEM fn C.ctx_functions /\ MEM inst (fn_insts fn) /\
   ?P. EVERY (fn_static_ptr_ok P) C.ctx_functions` by
    metis_tac[fmp_stage_frame_facts] >>
  `FDOM G SUBSET fn_pv P fn` by metis_tac[fmp_stage_prov_support] >>
  `ptr_use_static_ok P (fn_pv P fn) inst` by
    fs[EVERY_MEM, fn_static_ptr_ok_def] >>
  Cases_on `sz` >> simp[op_prov_def] >>
  rename1 `FLOOKUP G v` >> Cases_on `FLOOKUP G v` >> simp[] >>
  `v IN fn_pv P fn` by (fs[SUBSET_DEF, FLOOKUP_DEF] >> metis_tac[]) >>
  gvs[ptr_use_static_ok_def, is_pointer_preserving_op_def,
      mem_read_ops_def, mem_write_ops_def] >>
  Cases_on `p = Var v` >> gvs[]
QED

Theorem fmp_mem_sha3_size[local]:
  fmp_stage_ctx rpolicy D C C' vs vs' fmp eom /\
  frame_reachable vs C stk PG G tn fn inst s /\ active_inst fn inst s /\
  fmp_stage_rel D C' sm fmp0 raw0 eom restored stk PG G tn fn s lo t ts /\
  inst.inst_opcode = SHA3 /\ inst.inst_operands = [p;sz] /\
  eval_operand sz s = SOME l ==> eval_operand sz t = SOME l
Proof
  strip_tac >>
  `op_prov G sz = NONE` by metis_tac[fmp_mem_sha3_size_prov] >>
  `taint_ok fn tn inst s` by metis_tac[fmp_stage_frame_facts] >>
  `op_taint tn sz = {}` by (fs[taint_ok_def] >> gvs[] >> metis_tac[]) >>
  `MEM sz inst.inst_operands /\ inst.inst_opcode <> PHI /\
   (!v. ~retpc_use_ok inst v)` by simp[retpc_use_ok_def] >>
  `!v. sz = Var v ==> ~retpc_var fn v` by
    metis_tac[fmp_mem_operand_non_retpc] >>
  drule_all fmp_mem_operand_clean >> simp[]
QED

Theorem fmp_mem_sha3_read:
  fmp_stage_ctx rpolicy D C C' vs vs' fmp eom /\
  frame_reachable vs C stk PG G tn fn inst s /\ active_inst fn inst s /\
  fmp_stage_rel D C' sm fmp0 raw0 eom restored stk PG G tn fn s lo t ts /\
  ~in_revert_forward fn s /\ inst.inst_opcode = SHA3 /\
  inst.inst_operands = [p;sz] /\
  eval_operand p s = SOME x /\ eval_operand sz s = SOME l ==>
  ?y. eval_operand p t = SOME y /\ eval_operand sz t = SOME l /\
    read_memory (w2n x) (w2n l) s = read_memory (w2n y) (w2n l) t
Proof
  strip_tac >>
  `eval_operand sz t = SOME l` by metis_tac[fmp_mem_sha3_size] >>
  `taint_ok fn tn inst s` by metis_tac[fmp_stage_frame_facts] >>
  `op_taint tn p = {}` by (fs[taint_ok_def] >> gvs[] >> metis_tac[]) >>
  `MEM p inst.inst_operands /\ inst.inst_opcode <> PHI /\
   (!v. ~retpc_use_ok inst v)` by simp[retpc_use_ok_def] >>
  `!v. p = Var v ==> ~retpc_var fn v` by
    metis_tac[fmp_mem_operand_non_retpc] >>
  `MEM (w2n x,w2n l) (source_memory_read_ranges inst s)` by
    simp[source_memory_read_ranges_def, memory_range_of_operands_def] >>
  `mem_read_ops inst = SOME <|iao_ofst := p; iao_size := SOME sz; iao_max_size := SOME sz|> /\
   (<|iao_ofst := p; iao_size := SOME sz; iao_max_size := SOME sz|> : inst_access_ops).iao_ofst = p` by
    simp[mem_read_ops_def] >>
  drule_all fmp_mem_read_operand_range >> strip_tac >>
  qexists_tac `y` >> simp[] >>
  irule LIST_EQ >> simp[ld_read_memory_length] >> rpt strip_tac >>
  `w2n x+x' NOTIN tn.t_mem` by
    (qpat_x_assum `taint_ok _ _ _ _` mp_tac >>
     gvs[taint_ok_def, about_to_revert_def] >>
     strip_tac >>
     qpat_x_assum `!off len i. _` (qspecl_then [`w2n x`,`w2n l`,`w2n x+x'`] mp_tac) >>
     asm_simp_tac (srw_ss()) [arithmeticTheory.ADD_ASSOC] >> simp[]) >>
  irule ld_memory_agree_slice_element >> simp[] >>
  qexistsl_tac [`eom`,`tn.t_mem`,`fmp_ld_sites sm`] >>
  gvs[fmp_stage_rel_def] >> metis_tac[]
QED
