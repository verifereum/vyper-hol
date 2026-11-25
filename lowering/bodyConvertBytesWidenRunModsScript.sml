(* The widening bytestring Convert suffix: one reached source buffer and
   one concrete ALLOCA/MCOPY endpoint. *)
Theory bodyConvertBytesWidenRunMods
Ancestors
  bodyFullConvertCopyRun bodyConvertBytesEntryMods exprSimConvertBytes
  exprSimConvert bodyFullPredsMods bodyFullShared
  bodyFullHashKeccakFixed bodyPtrDefs loweringPosts loweringStateRelDefs
  venomState venomExecSemantics vyperAST vyperState compileEnv

Theorem bytes_convert_widen_run_mods:
  is_bytestring_type (expr_type e) /\ is_bytestring_type dst /\
  is_bytestring_type (lowered_value_type ce e) /\
  evaluate_type (get_tenv cx) (expr_type e) = SOME tv /\
  evaluate_type (get_tenv cx) dst = SOME tout /\
  value_has_type tv v /\
  val_footprint tv v <= type_memory_bytes ce (lowered_value_type ce e) /\
  type_memory_bytes ce (lowered_value_type ce e) < type_memory_bytes ce dst /\
  compile_bytestring_widen_copy (type_memory_bytes ce dst) (Var src)
    (type_memory_bytes ce (lowered_value_type ce e)) sm = (out,sb) /\
  0 < type_memory_bytes ce (lowered_value_type ce e) /\
  type_memory_bytes ce dst < dimword(:256) /\
  fn_has_code sm sb func /\ fn_inst_ids_distinct func /\
  stmt_state_rel H ctx func ce cx es s /\
  local_ptrs_reserved ce sm /\ alloca_history func s /\
  allocas_from lo s /\ lo <= s.vs_alloca_next /\
  not_fresh_at sm src /\ lookup_var src s = SOME a /\
  ptr_covers G tn src s (type_memory_bytes ce (lowered_value_type ce e)) /\
  w2n a + type_memory_bytes ce (lowered_value_type ce e) <= s.vs_alloca_next /\
  ~s.vs_halted /\ s.vs_current_bb = sm.cs_current_bb /\
  s.vs_inst_idx = LENGTH sm.cs_current_insts ==>
  ?vout.
    convert_result cx (expr_type e) dst v = INL vout /\
    val_wf tout vout /\
    val_footprint tout vout <=
      type_memory_bytes ce (lowered_value_type ce e) /\
    (?u q Gf tnf dstvar dw z Ga tna sc buf r.
      out = Var dstvar /\
      q = u with vs_inst_idx := LENGTH sb.cs_current_insts /\
      run_inst_seq (emitted_insts sm sb) s = OK u /\
      (!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG)
        (s,G,tn) [] (OK q,Gf,tnf)) /\
      q.vs_current_bb = sb.cs_current_bb /\
      q.vs_inst_idx = LENGTH sb.cs_current_insts /\
      alloca_history func q /\ s.vs_alloca_next <= q.vs_alloca_next /\
      allocas_from lo q /\ lookup_var dstvar q = SOME dw /\
      FLOOKUP q.vs_allocas sm.cs_next_id =
        SOME (w2n dw,type_memory_bytes ce dst) /\
      w2n dw + type_memory_bytes ce dst < dimword(:256) /\
      w2n dw + type_memory_bytes ce dst <= q.vs_alloca_next /\
      ptr_covers Gf tnf dstvar q (type_memory_bytes ce dst) /\
      q.vs_memory = (mcopy (w2n dw) (w2n a)
        (type_memory_bytes ce (lowered_value_type ce e)) s).vs_memory /\
      q.vs_accounts = s.vs_accounts /\ q.vs_transient = s.vs_transient /\
      q.vs_call_ctx = s.vs_call_ctx /\ q.vs_requests = s.vs_requests /\
      q.vs_immutables = s.vs_immutables /\
      tnf.t_stor = tn.t_stor /\ tnf.t_trans = tn.t_trans /\
      tnf.t_imm = tn.t_imm /\
      (!x. not_fresh_at sm x ==> lookup_var x q = lookup_var x s /\
        FLOOKUP Gf x = FLOOKUP G x /\
        op_taint tnf (Var x) = op_taint tn (Var x)) /\
      compile_alloc_buffer (type_memory_bytes ce dst) sm = (buf,sc) /\
      buf.buf_operand = Var dstvar /\ not_fresh_at sc dstvar /\
      emit_void MCOPY [Var dstvar;Var src;
        Lit (n2w (type_memory_bytes ce (lowered_value_type ce e)))] sc = ((),sb) /\
      run_inst_seq (emitted_insts sm sc) s = OK r /\
      z = r with vs_inst_idx := LENGTH sc.cs_current_insts /\
      Ga = step_prov PG G
        (mk_inst sm.cs_next_id ALLOCA [Lit (n2w (type_memory_bytes ce dst))]
          [dstvar]) r /\
      tna = step_taint
        (mk_inst sm.cs_next_id ALLOCA [Lit (n2w (type_memory_bytes ce dst))]
          [dstvar]) s r tn /\
      (!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG)
        (s,G,tn) [] (OK z,Ga,tna)) /\
      z.vs_current_bb = sc.cs_current_bb /\
      z.vs_inst_idx = LENGTH sc.cs_current_insts /\
      z with <|vs_vars := s.vs_vars; vs_allocas := s.vs_allocas;
               vs_alloca_next := s.vs_alloca_next; vs_inst_idx := s.vs_inst_idx|> = s /\
      (!H'. stmt_state_rel H' ctx func ce cx es s ==>
        stmt_state_rel H' ctx func ce cx es z) /\
      alloca_history func z /\ allocas_from lo z /\
      s.vs_alloca_next <= z.vs_alloca_next /\
      lookup_var dstvar z = SOME dw /\
      ptr_covers Ga tna dstvar z (type_memory_bytes ce dst) /\
      FLOOKUP z.vs_allocas sm.cs_next_id =
        SOME (w2n dw,type_memory_bytes ce dst) /\
      w2n dw + type_memory_bytes ce dst < dimword(:256) /\
      w2n dw + type_memory_bytes ce dst <= z.vs_alloca_next /\
      (!aid e. FLOOKUP s.vs_allocas aid = SOME e ==>
        FLOOKUP z.vs_allocas aid = SOME e) /\
      (!aid b len. aid < sm.cs_next_id /\
        FLOOKUP s.vs_allocas aid = SOME (b,len) ==>
        regions_disjoint (w2n dw) (type_memory_bytes ce dst) b len) /\
      (!name b len. local_region ce es.scopes z name b len ==>
        regions_disjoint (w2n dw) (type_memory_bytes ce dst) b len) /\
      tna.t_stor = tn.t_stor /\ tna.t_trans = tn.t_trans /\
      tna.t_imm = tn.t_imm /\
      (!i. i IN tna.t_mem <=> i IN tn.t_mem \/
        (s.vs_alloca_next <= i /\
         i < w2n dw + type_memory_bytes ce dst)) /\
      (!x. not_fresh_at sm x ==> lookup_var x z = lookup_var x s /\
        FLOOKUP Ga x = FLOOKUP G x /\
        op_taint tna (Var x) = op_taint tn (Var x)) /\
      Gf = step_prov PG Ga
        (mk_inst sc.cs_next_id MCOPY
          [Var dstvar;Var src;
           Lit (n2w (type_memory_bytes ce (lowered_value_type ce e)))] [])
        (mcopy (w2n dw) (w2n a)
          (type_memory_bytes ce (lowered_value_type ce e)) z) /\
      tnf = step_taint
        (mk_inst sc.cs_next_id MCOPY
          [Var dstvar;Var src;
           Lit (n2w (type_memory_bytes ce (lowered_value_type ce e)))] []) z
        (mcopy (w2n dw) (w2n a)
          (type_memory_bytes ce (lowered_value_type ce e)) z) tna)
Proof
  strip_tac >>
  drule_all convert_bytestring_lowered_widen_success >>
  disch_then (qx_choose_then `vout` assume_tac) >>
  drule_all convert_bytestring_wf >> strip_tac >>
  `val_footprint tout vout <=
     type_memory_bytes ce (lowered_value_type ce e)` by
    (drule_all convert_bytestring_memory >>
     disch_then (qspecl_then [`0`,`s.vs_memory`] strip_assume_tac) >> simp[]) >>
  qexists_tac `vout` >>
  conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac >- first_assum ACCEPT_TAC >>
  `type_memory_bytes ce (lowered_value_type ce e) <=
     type_memory_bytes ce dst` by
    (irule arithmeticTheory.LESS_IMP_LESS_OR_EQ >> first_assum ACCEPT_TAC) >>
  (* Keep the physical packet polymorphic, as in the conclusion here. *)
  MATCH_MP_TAC convert_widen_copy_origin_ptr_path >>
  rpt conj_tac >> first_assum ACCEPT_TAC
QED
