(* The existing SOME-base endpoint follows from the counted optional path. *)
Theory immutableAssignBytesMem
Ancestors immutableAssignBytesPathMem

Theorem immutable_assign_bytes_mem_endpoint:
  compile_assign_value ce dst LocCode src F sl dty sty memsz sm = ((),sb) /\
  is_bytestring_type dty /\ is_bytestring_type sty /\
  ce.ce_imm_alloca = SOME region /\ fn_has_code sm sb func /\
  eval_operand region s = SOME 0w /\ eval_operand dst s = SOME b /\
  eval_operand src s = SOME a /\ mload (w2n a) s = n2w len /\
  len + 63 < dimword (:256) /\
  evaluate_type (get_tenv cx) dty = SOME dtv /\
  immutable_value_admissible dtv v /\
  val_in_memory dtv v (w2n a) s.vs_memory /\
  32 * (1 + word_size len) <= type_memory_size dtv /\
  w2n a + 32 * (1 + word_size len) < dimword (:256) /\
  w2n b + type_memory_size dtv < dimword (:256) /\
  regions_disjoint (w2n b) (type_memory_size dtv)
    (w2n a) (val_footprint dtv v) /\
  (!x. src = Var x \/ dst = Var x \/ region = Var x ==> not_fresh_at sm x) /\
  (!j. j < 1 + word_size len ==>
    w2n (a+n2w (32*j)) + 32 <= s.vs_alloca_next /\
    w2n (b+n2w (32*j)) + 32 <= s.vs_alloca_next) /\
  ~s.vs_halted /\ s.vs_current_bb = sm.cs_current_bb /\
  s.vs_inst_idx = LENGTH sm.cs_current_insts ==>
  ?t. mem_cont_sim ctx func s t /\
    t.vs_allocas = s.vs_allocas /\ t.vs_alloca_next = s.vs_alloca_next /\
    (!x. not_fresh_at sm x ==> lookup_var x t = lookup_var x s) /\
    (t with <|vs_vars := s.vs_vars; vs_current_bb := s.vs_current_bb;
      vs_prev_bb := s.vs_prev_bb; vs_inst_idx := s.vs_inst_idx|>) =
      immutable_transfers T T a b (1 + word_size len) 0 s /\
    val_in_memory dtv v (w2n b) t.vs_memory /\
    immutable_value_bytes_rel dtv v
      (mem_bytes_at (w2n b) (type_memory_size dtv) t.vs_memory) /\
    (!q k. q+k <= w2n b \/ w2n b+type_memory_size dtv <= q ==>
      mem_bytes_at q k t.vs_memory = mem_bytes_at q k s.vs_memory) /\
    ~t.vs_halted /\ t.vs_current_bb = sb.cs_current_bb /\
    t.vs_inst_idx = LENGTH sb.cs_current_insts
Proof
  strip_tac >>
  mp_tac (Q.INST [`imm` |-> `SOME region`]
    (SPEC_ALL immutable_assign_bytes_mem_path_endpoint)) >>
  impl_tac >- (simp[] >> metis_tac[]) >>
  strip_tac >> qexists_tac `t` >> rpt conj_tac >> first_assum ACCEPT_TAC
QED
