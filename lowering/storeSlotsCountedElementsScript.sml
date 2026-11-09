(* Counted sparse array-loop boundaries. *)
Theory storeSlotsCountedElements
Ancestors
  storeSlotsCountedControl storeSlotsCountedBase placeStoreSlots
  context compileEnv fragExec fragGasMode venomState venomInst emitHelperProps
  valueEncoding valueEncodingProps words arithmetic list rich_list finite_map

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
