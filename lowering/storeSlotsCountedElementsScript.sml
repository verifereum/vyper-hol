(* Counted sparse array-loop boundaries. *)
Theory storeSlotsCountedElements
Ancestors
  storeSlotsCountedControl storeSlotsCountedBase placeStoreSlots
  context compileEnv fragExec fragGasMode venomState venomInst emitHelperProps
  valueEncoding valueEncodingProps words arithmetic list rich_list finite_map
  storeSlotsMemoryPaths fragExecMem instMemFrontier venomExecSemantics
  emitHelper exprLoweringProps memSafeRun

Theorem store_slots_loop_init_mem[local]:
  !cenv src slot elem cnt tr sa sb func hdr body exit cv lv dv iv bs sc sd sp dp
   s ctx etv el sw dw.
  store_slots_loop_code cenv src slot elem cnt tr sa sb func
    (hdr,body,exit,cv,lv,dv,iv,bs,sc,sd,sp,dp) /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?u. gas_marked_path T ctx func s 0 (OK u) /\
    store_slots_prefix sa etv el tr sw dw s 0 [] u /\
    u.vs_alloca_next = s.vs_alloca_next /\
    lookup_var cv u = SOME 0w /\ u.vs_current_bb = hdr /\ u.vs_inst_idx = 0
Proof
  rpt gen_tac >> strip_tac >> fs[store_slots_loop_code_def] >>
  `lookup_block s.vs_current_bb func.fn_blocks = SOME ibb /\
   DROP s.vs_inst_idx ibb.bb_instructions =
     [mk_inst id1 ASSIGN [Lit 0w] [cv]; mk_inst id2 JMP [Label hdr] []]` by simp[] >>
  drule_all store_slots_array_init_mem >> strip_tac >>
  qexists_tac `jump_to hdr ((update_var cv 0w s) with
    vs_inst_idx := s.vs_inst_idx + 1)` >>
  conj_tac >- simp[] >>
  reverse conj_tac
  >- simp[jump_to_def, lookup_var_def, update_var_def, FLOOKUP_UPDATE] >>
  irule store_slots_prefix_init_control >>
  simp[store_slots_prefix_empty] >> metis_tac[]
QED

Theorem store_slots_loop_exit_mem[local]:
  !cenv src slot elem cnt tr sa sb func hdr body exit cv lv dv iv bs sc sd sp dp
   s ctx etv el sw dw N ks u.
  store_slots_loop_code cenv src slot elem cnt tr sa sb func
    (hdr,body,exit,cv,lv,dv,iv,bs,sc,sd,sp,dp) /\
  store_slots_prefix sa etv el tr sw dw s N ks u /\
  (!x. cnt = Var x ==> not_fresh_at sa x) /\
  eval_operand cnt s = SOME (n2w N) /\ N < dimword (:256) /\
  lookup_var cv u = SOME (n2w N) /\ u.vs_current_bb = hdr /\ u.vs_inst_idx = 0 ==>
  ?t. gas_marked_path T ctx func u 0 (OK t) /\
    store_slots_prefix sa etv el tr sw dw s N ks t /\
    t.vs_alloca_next = u.vs_alloca_next /\
    t.vs_current_bb = sb.cs_current_bb /\ t.vs_inst_idx = LENGTH sb.cs_current_insts
Proof
  rpt gen_tac >> strip_tac >> fs[store_slots_loop_code_def] >>
  `~u.vs_halted /\ eval_operand cnt u = SOME (n2w N)` by
    (fs[store_slots_prefix_def] >> Cases_on `cnt` >>
     gvs[eval_operand_def] >> metis_tac[]) >>
  `lookup_block u.vs_current_bb func.fn_blocks = SOME hbb /\
   eval_operand (Var cv) u = SOME (n2w N)` by simp[eval_operand_def] >>
  `N <= N` by simp[] >>
  drule_all store_slots_array_condition_mem >> simp[] >> strip_tac >>
  qexists_tac `jump_to exit ((update_var dv (bool_to_word T)
    (update_var lv (bool_to_word F) u)) with vs_inst_idx := 2)` >>
  conj_tac >- simp[] >>
  reverse conj_tac >- simp[jump_to_def, update_var_def] >>
  irule store_slots_prefix_control >> simp[] >> metis_tac[]
QED

Theorem store_slots_addresses_mem_ok[local]:
  (do so <- emit_op MUL [Var counter; Lit (n2w ss)];
      sp <- emit_op ADD [src; so];
      doff <- emit_op MUL [Var counter; Lit (n2w ds)];
      dp <- emit_op ADD [dst; doff]; comp_return (sp,dp)
   od) sa = ((sp,dp),sb) ==>
  run_inst_seq_mem_ok (emitted_insts sa sb) s
Proof
  simp[comp_bind_def, comp_return_def, emit_op_def, fresh_var_def,
       emit_inst_def, fresh_id_def, emit_def, comp_ignore_bind_def] >>
  strip_tac >> gvs[] >>
  irule run_inst_seq_mem_ok_every >>
  simp[emitted_insts_def] >>
  pure_rewrite_tac[GSYM APPEND_ASSOC] >>
  simp[DROP_LENGTH_APPEND] >>
  rpt conj_tac >> gen_tac >>
  irule below_frontier_no_ranges >> simp[mk_inst_def]
QED

Theorem store_slots_addresses_forward_mem[local]:
  (do so <- emit_op MUL [Var counter; Lit (n2w ss)];
      sp <- emit_op ADD [src; so];
      doff <- emit_op MUL [Var counter; Lit (n2w ds)];
      dp <- emit_op ADD [dst; doff]; comp_return (sp,dp)
   od) sa = ((sp,dp),sb) /\
  not_fresh_at sa counter /\
  (!x. src = Var x ==> not_fresh_at sa x) /\
  (!x. dst = Var x ==> not_fresh_at sa x) /\
  eval_operand src s = SOME sw /\ eval_operand dst s = SOME dw /\
  lookup_var counter s = SOME (n2w i) /\ fn_has_code sa sb func /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?u. gas_marked_path T ctx func s 0 (OK u) /\
      eval_operand sp u = SOME (sw + n2w (i * ss)) /\
      eval_operand dp u = SOME (dw + n2w (i * ds)) /\
      (u with <|vs_vars := s.vs_vars; vs_inst_idx := s.vs_inst_idx|>) = s /\
      (!x. not_fresh_at sa x ==> lookup_var x u = lookup_var x s) /\
      ~u.vs_halted /\ u.vs_current_bb = sb.cs_current_bb /\
      u.vs_inst_idx = LENGTH sb.cs_current_insts
Proof
  strip_tac >> drule_all store_slots_addresses_sequence >> strip_tac >>
  `run_inst_seq_mem_ok (emitted_insts sa sb) s` by
    (drule store_slots_addresses_mem_ok >> simp[]) >>
  `LENGTH (FILTER (\j. j.inst_opcode = GAS) (emitted_insts sa sb)) = 0` by
    (qpat_x_assum `EVERY (\j. j.inst_opcode <> GAS) _` mp_tac >>
     simp[LENGTH_NIL, FILTER_EQ_NIL]) >>
  `gas_marked_path T ctx func s 0
     (OK (u with vs_inst_idx := LENGTH sb.cs_current_insts))` by
    (irule store_slots_emitted_seq_path_mem >> simp[] >>
     qexists_tac `sa` >> gvs[]) >>
  qexists_tac `u with vs_inst_idx := LENGTH sb.cs_current_insts` >>
  gvs[eval_operand_def, lookup_var_def, same_blocks_def] >>
  qpat_x_assum `u with vs_vars := _ = s` mp_tac >>
  simp[venom_state_component_equality] >> strip_tac >> simp[]
QED
