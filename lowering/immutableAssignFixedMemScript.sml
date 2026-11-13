(* Existing SOME-base assignment contract follows from the counted endpoint. *)
Theory immutableAssignFixedMem
Ancestors
  immutableAssignFixedPathMem loweringStateRelDefs

Theorem immutable_assign_fixed_mem_endpoint:
  compile_assign_value ce dst LocCode src F sl dty dty
    (type_memory_bytes ce dty) sm = ((),sb) /\
  ~is_word_type dty /\ ~is_bytestring_type dty /\
  ce.ce_imm_alloca = SOME region /\ fn_has_code sm sb func /\
  eval_operand region s = SOME 0w /\ eval_operand dst s = SOME (n2w off) /\
  eval_operand src s = SOME (n2w a) /\
  (!x. src = Var x \/ dst = Var x \/ region = Var x ==> not_fresh_at sm x) /\
  evaluate_type (get_tenv cx) dty = SOME dtv /\
  type_memory_bytes ce dty = type_memory_size dtv /\
  immutable_value_admissible dtv v /\ val_in_memory dtv v a s.vs_memory /\
  0 < type_memory_size dtv /\ type_memory_size dtv MOD 32 = 0 /\
  a + type_memory_size dtv <= s.vs_alloca_next /\
  off + type_memory_size dtv <= s.vs_alloca_next /\
  a + type_memory_size dtv < dimword (:256) /\
  off + type_memory_size dtv < dimword (:256) /\
  regions_disjoint off (type_memory_size dtv) a (type_memory_size dtv) /\
  ~s.vs_halted /\ s.vs_current_bb = sm.cs_current_bb /\
  s.vs_inst_idx = LENGTH sm.cs_current_insts ==>
  ?t. mem_cont_sim ctx func s t /\
    t.vs_allocas = s.vs_allocas /\ t.vs_alloca_next = s.vs_alloca_next /\
    val_in_memory dtv v off t.vs_memory /\
    immutable_value_bytes_rel dtv v (mem_bytes_at off (type_memory_size dtv) t.vs_memory) /\
    (!q k. q+k <= off \/ off+type_memory_size dtv <= q ==>
      mem_bytes_at q k t.vs_memory = mem_bytes_at q k s.vs_memory) /\
    (!x. not_fresh_at sm x ==> lookup_var x t = lookup_var x s) /\
    t = s with <|vs_vars := t.vs_vars; vs_memory := t.vs_memory;
      vs_immutables := t.vs_immutables; vs_inst_idx := LENGTH sb.cs_current_insts|> /\
    ~t.vs_halted /\ t.vs_current_bb = sb.cs_current_bb /\
    t.vs_inst_idx = LENGTH sb.cs_current_insts
Proof
  strip_tac >>
  `!base. ce.ce_imm_alloca = SOME base ==> eval_operand base s = SOME 0w` by
    simp[] >>
  `!x. src = Var x \/ dst = Var x \/
      (?r. ce.ce_imm_alloca = SOME r /\ r = Var x) ==> not_fresh_at sm x` by
    (simp[] >> metis_tac[]) >>
  drule_all immutable_assign_fixed_mem_path_endpoint >> metis_tac[]
QED
