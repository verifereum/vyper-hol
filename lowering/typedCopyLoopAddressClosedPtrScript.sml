Theory typedCopyLoopAddressClosedPtr
Ancestors
 typedCopyLoopAddressPathPtr

Theorem typed_copy_loop_dynamic_offset_covers_closed:
 !PG G tn s root offset out id a off total n.
 lookup_var root s = SOME a /\
 eval_operand offset s = SOME (n2w off) /\
 ptr_covers G tn root s total /\ off + n <= total /\
 w2n a + off < dimword(:256) /\ root <> out ==>
 ptr_covers
   (step_prov PG G (mk_inst id ADD [Var root; offset] [out])
     (update_var out (a + n2w off) s))
   (step_taint (mk_inst id ADD [Var root; offset] [out]) s
     (update_var out (a + n2w off) s) tn)
   out (update_var out (a + n2w off) s) n
Proof
 rpt strip_tac >>
 `op_taint (step_taint (mk_inst id ADD [Var root; offset] [out]) s
   (update_var out (a + n2w off) s) tn) (Var out) = {}` by
   simp[typedCopyPtrTheory.copy_len_binop_ghost_frame] >>
 gvs[bodyPtrDefsTheory.ptr_covers_def] >>
 `off < dimword(:256)` by decide_tac >>
 simp[ptrDisciplineTheory.step_prov_def, ptrDisciplineTheory.set_prov_def,
   ptrDisciplineTheory.out_prov_def, ptrDisciplineTheory.first_prov_def,
   ptrDisciplineTheory.op_prov_def, venomInstTheory.mk_inst_def,
   finite_mapTheory.FLOOKUP_UPDATE, venomStateTheory.lookup_var_def,
   venomStateTheory.update_var_def, wordsTheory.w2n_add_2,
   wordsTheory.w2n_n2w, arithmeticTheory.LESS_MOD] >> decide_tac
QED

Theorem typed_copy_loop_address_path_ptr_closed:
 !D ctx fn PG G tn s bb pre post ctr so doff sp dp sr dr id i ss ds a b S T.
 ~s.vs_halted /\ ~ctx_has_dalloca ctx /\
 lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
 bb.bb_instructions = pre ++
 [mk_inst id MUL [Var ctr;Lit (n2w ss)] [so];
  mk_inst (id+1) MUL [Var ctr;Lit (n2w ds)] [doff];
  mk_inst (id+2) ADD [Var sr;Var so] [sp];
  mk_inst (id+3) ADD [Var dr;Var doff] [dp]] ++ post /\
 s.vs_inst_idx = LENGTH pre /\
 lookup_var ctr s = SOME (n2w i) /\ op_taint tn (Var ctr) = {} /\
 lookup_var sr s = SOME a /\ lookup_var dr s = SOME b /\
 ptr_covers G tn sr s S /\ ptr_covers G tn dr s T /\
 ALL_DISTINCT [so;doff;sp;dp] /\
 (!v. MEM v [so;doff;sp;dp] ==> ctr <> v /\ sr <> v /\ dr <> v) /\
 i*ss+ss <= S /\ i*ds+ds <= T /\
 w2n a+i*ss < dimword(:256) /\ w2n b+i*ds < dimword(:256) ==>
 ?Gf tnf sf.
 gas_path_ptr D 0 ctx fn PG G tn s 0 Gf tnf (OK sf) /\
 sf.vs_current_bb = s.vs_current_bb /\ sf.vs_inst_idx = LENGTH pre + 4 /\
 ~sf.vs_halted /\ sf.vs_allocas = s.vs_allocas /\
 sf.vs_fmp = s.vs_fmp /\ sf.vs_requests = s.vs_requests /\
 tnf.t_imm = tn.t_imm /\
 lookup_var sp sf = SOME (n2w (w2n a+i*ss)) /\
 lookup_var dp sf = SOME (n2w (w2n b+i*ds)) /\
 ptr_covers Gf tnf sp sf ss /\ ptr_covers Gf tnf dp sf ds /\
 sf.vs_memory=s.vs_memory /\ tnf.t_mem=tn.t_mem /\
 tnf.t_stor=tn.t_stor /\ tnf.t_trans=tn.t_trans /\
 (!p. ~MEM p [so;doff;sp;dp] ==>
 lookup_var p sf=lookup_var p s /\ FLOOKUP Gf p=FLOOKUP G p /\
 op_taint tnf (Var p)=op_taint tn (Var p))
Proof
 typedCopyLoopAmbientLib.address_witnesses >>
 conj_tac >- suspend "path" >>
 `s4.vs_current_bb = s.vs_current_bb /\ s4.vs_inst_idx = LENGTH pre + 4 /\
  ~s4.vs_halted /\ s4.vs_allocas = s.vs_allocas /\
  s4.vs_fmp = s.vs_fmp /\ s4.vs_requests = s.vs_requests /\
  tn4.t_imm = tn.t_imm` by
  simp[Abbr `s4`, Abbr `t4`, Abbr `s3`, Abbr `t3`, Abbr `s2`, Abbr `s1`,
   venomStateTheory.update_var_def, Abbr `tn4`, Abbr `tn3`, Abbr `tn2`, Abbr `tn1`,
   ptrDisciplineTheory.step_taint_def, ptrDisciplineTheory.imm_taint_def,
   venomInstTheory.mk_inst_def] >>
 simp[] >> suspend "resources"
QED

Resume typed_copy_loop_address_path_ptr_closed[path]:
 typedCopyLoopAmbientLib.address_path
   typedCopyLoopControlPathPtrTheory.typed_copy_control_arith_path_ptr
   annAssignPtrLengthTheory.annassign_copy_len_binop_path_ptr
   fragGasPathPtrTheory.gas_path_ptr_then
QED

Resume typed_copy_loop_address_path_ptr_closed[resources]:
 typedCopyLoopAmbientLib.address_resources typed_copy_loop_dynamic_offset_covers_closed
QED

Finalise typed_copy_loop_address_path_ptr_closed
