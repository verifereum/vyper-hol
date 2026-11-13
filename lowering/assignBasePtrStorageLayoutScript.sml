(* Compiler boundary for the counted memory-to-storage loop. *)
Theory assignBasePtrStorageLayout
Ancestors assignBasePtrStorageLoop assignBasePtrStoragePath context compileEnv loweringStateRelDefs emitHelper emitHelperProps
  stateFrame fragExec venomInst venomState venomExecSemantics ptrSafeRun ptrDiscipline
  fragGasSeqPtr fragGasPathPtr bodyPtrDefs finite_map pred_set list rich_list arithmetic combin

Theorem assign_base_store_compile_shape:
  !tr root k n sa u sb.
    compile_word_copy_loop (Var root) (Lit k) n LocMemory
      (if tr then LocTransient else LocStorage) F sa = (u,sb) ==>
    ?hdr bodylbl exit ctr done mv sv vv dv nv.
      sb.cs_current_bb = exit /\ sb.cs_current_insts = [] /\
      sb.cs_blocks =
        <| bb_label := bodylbl; bb_instructions :=
          [mk_inst (sa.cs_next_id+4) MUL [Var ctr;Lit 32w] [mv];
           mk_inst (sa.cs_next_id+5) ADD [Var root;Var mv] [sv];
           mk_inst (sa.cs_next_id+6) MLOAD [Var sv] [vv];
           mk_inst (sa.cs_next_id+7) ADD [Lit k;Var ctr] [dv];
           mk_inst (sa.cs_next_id+8) (if tr then TSTORE else SSTORE) [Var dv;Var vv] [];
           mk_inst (sa.cs_next_id+9) ADD [Var ctr;Lit 1w] [nv];
           mk_inst (sa.cs_next_id+10) ASSIGN [Var nv] [ctr];
           mk_inst (sa.cs_next_id+11) JMP [Label hdr] []] |> ::
        <| bb_label := hdr; bb_instructions :=
          [mk_inst (sa.cs_next_id+2) EQ [Var ctr;Lit (n2w n)] [done];
           mk_inst (sa.cs_next_id+3) JNZ [Var done;Label exit;Label bodylbl] []] |> ::
        <| bb_label := sa.cs_current_bb; bb_instructions := sa.cs_current_insts ++
          [mk_inst sa.cs_next_id ASSIGN [Lit 0w] [ctr];
           mk_inst (sa.cs_next_id+1) JMP [Label hdr] []] |> :: sa.cs_blocks /\
      ALL_DISTINCT [ctr;done;mv;sv;vv;dv;nv] /\
      (!x. not_fresh_at sa x ==> ~MEM x [ctr;done;mv;sv;vv;dv;nv])
Proof
  rpt gen_tac >>
  Cases_on `tr` >>
  simp[compile_word_copy_loop_def, compile_word_copy_loop_op_def,
    compile_word_copy_loop_base_def, word_scale_def, compile_ptr_load_def,
    compile_ptr_store_def, emit_op_def, emit_void_def, emit_inst_def,
    comp_ignore_bind_def, comp_bind_def, comp_return_def, fresh_label_def,
    fresh_var_def, fresh_id_def, emit_def, new_block_def] >> strip_tac >> gvs[] >>
  rpt (goal_assum (drule_at Any)) >>
  simp[mk_inst_def, ALL_DISTINCT, fresh_var_distinct] >>
  rw[not_fresh_at_def] >> first_x_assum irule >> simp[]
QED

Theorem assign_base_store_compile_code:
  !tr root k n sa u sb fn.
    compile_word_copy_loop (Var root) (Lit k) n LocMemory
      (if tr then LocTransient else LocStorage) F sa = (u,sb) /\
    fn_has_code sa sb fn ==>
    ?hdr bodylbl ctr done mv sv vv dv nv ib hb bb.
      sb.cs_current_insts = [] /\
      lookup_block sa.cs_current_bb fn.fn_blocks = SOME ib /\
      ib.bb_instructions = sa.cs_current_insts ++
        [mk_inst sa.cs_next_id ASSIGN [Lit 0w] [ctr];
         mk_inst (sa.cs_next_id+1) JMP [Label hdr] []] /\
      lookup_block hdr fn.fn_blocks = SOME hb /\
      hb.bb_instructions =
        [mk_inst (sa.cs_next_id+2) EQ [Var ctr;Lit (n2w n)] [done];
         mk_inst (sa.cs_next_id+3) JNZ [Var done;Label sb.cs_current_bb;Label bodylbl] []] /\
      lookup_block bodylbl fn.fn_blocks = SOME bb /\
      bb.bb_instructions =
        [mk_inst (sa.cs_next_id+4) MUL [Var ctr;Lit 32w] [mv];
         mk_inst (sa.cs_next_id+5) ADD [Var root;Var mv] [sv];
         mk_inst (sa.cs_next_id+6) MLOAD [Var sv] [vv];
         mk_inst (sa.cs_next_id+7) ADD [Lit k;Var ctr] [dv];
         mk_inst (sa.cs_next_id+8) (if tr then TSTORE else SSTORE) [Var dv;Var vv] [];
         mk_inst (sa.cs_next_id+9) ADD [Var ctr;Lit 1w] [nv];
         mk_inst (sa.cs_next_id+10) ASSIGN [Var nv] [ctr];
         mk_inst (sa.cs_next_id+11) JMP [Label hdr] []] /\
      ALL_DISTINCT [ctr;done;mv;sv;vv;dv;nv] /\
      (!x. not_fresh_at sa x ==> ~MEM x [ctr;done;mv;sv;vv;dv;nv])
Proof
  rpt gen_tac >> strip_tac >> drule assign_base_store_compile_shape >> strip_tac >>
  gvs[fn_has_code_def, emitted_blocks_def, DISJ_IMP_THM, FORALL_AND_THM] >>
  qexistsl_tac [`hdr`, `bodylbl`, `ctr`, `done`, `mv`, `sv`, `vv`, `dv`, `nv`] >>
  simp[]
QED

Theorem assign_base_storage_literal_counted:
  !s fn bb id w out tn G ctx D PG.
    ~s.vs_halted /\ lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
    get_instruction bb s.vs_inst_idx = SOME (mk_inst id ASSIGN [Lit w] [out]) /\
    ~ctx_has_dalloca ctx ==>
    gas_path_ptr D 0 ctx fn PG G tn s 0 (DRESTRICT G (COMPL {out}))
      (tn with t_var := tn.t_var |+ (out,{}))
      (OK ((update_var out w s) with vs_inst_idx := SUC s.vs_inst_idx))
Proof
  rpt gen_tac >> strip_tac >>
  `step_inst_base (mk_inst id ASSIGN [Lit w] [out]) s = OK (update_var out w s)` by
    (asm_simp_tac bool_ss [step_inst_base_opcode_eqs, mk_inst_def, instruction_accessors, instruction_accfupds,
       K_THM, opcode_case_def] >> simp[eval_operand_def]) >>
  `ptr_inst_ok D 0 0 ctx fn G tn (mk_inst id ASSIGN [Lit w] [out]) s` by
    (simp[ptr_inst_ok_def, access_ok_def, taint_ok_def, allocas_from_def,
       mk_inst_def, codegenRelTheory.source_memory_write_ranges_def,
       contextCodegenRelTheory.source_memory_read_ranges_def] >>
     simp[GSYM mk_inst_def, step_inst_non_invoke, update_var_def]) >>
  `step_prov PG G (mk_inst id ASSIGN [Lit w] [out]) (update_var out w s) =
      DRESTRICT G (COMPL {out}) /\
   step_taint (mk_inst id ASSIGN [Lit w] [out]) s (update_var out w s) tn =
      (tn with t_var := tn.t_var |+ (out,{}))` by
    (simp[step_prov_def, set_prov_def, out_prov_def, op_prov_def,
       step_taint_def, set_var_taint_def, out_taint_def, mk_inst_def,
       mem_taint_def, step_writes_def, codegenRelTheory.source_memory_write_ranges_def,
       written_taint_def, range_bytes_def, store_taint_def, adopt_reset_def,
       imm_taint_def, new_site_bytes_def, update_var_def, FLOOKUP_DEF,
       first_prov_def, eval_operand_def, op_taint_def, EXTENSION,
       taint_component_equality] >> metis_tac[]) >>
  irule (SRULE [mk_inst_def, is_terminator_def]
    (Q.INST [`n` |-> `0`, `lo` |-> `0`,
      `i` |-> `mk_inst id ASSIGN [Lit w] [out]`] gas_path_ptr_step)) >>
  simp[GSYM mk_inst_def] >> goal_assum (drule_at Any) >> simp[] >>
  irule (cj 1 gas_path_ptr_rules) >> simp[update_var_def]
QED

Theorem assign_base_storage_init_counted:
  !s fn bb id ctr hdr tn G ctx D PG.
    ~s.vs_halted /\ lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
    get_instruction bb s.vs_inst_idx = SOME (mk_inst id ASSIGN [Lit 0w] [ctr]) /\
    get_instruction bb (SUC s.vs_inst_idx) = SOME (mk_inst (id+1) JMP [Label hdr] []) /\
    ~ctx_has_dalloca ctx ==>
    gas_path_ptr D 0 ctx fn PG G tn s 0 (DRESTRICT G (COMPL {ctr}))
      (tn with t_var := tn.t_var |+ (ctr,{}))
      (OK (jump_to hdr ((update_var ctr 0w s) with vs_inst_idx := SUC s.vs_inst_idx)))
Proof
  rpt gen_tac >> strip_tac >> drule_all assign_base_storage_literal_counted >>
  disch_then (qspecl_then [`tn`, `G`, `D`, `PG`] mp_tac) >> strip_tac >>
  `~((update_var ctr 0w s) with vs_inst_idx := SUC s.vs_inst_idx).vs_halted /\
   lookup_block ((update_var ctr 0w s) with vs_inst_idx := SUC s.vs_inst_idx).vs_current_bb
     fn.fn_blocks = SOME bb /\
   get_instruction bb ((update_var ctr 0w s) with vs_inst_idx := SUC s.vs_inst_idx).vs_inst_idx =
     SOME (mk_inst (id+1) JMP [Label hdr] [])` by simp[update_var_def] >>
  drule_all assign_base_storage_jump_counted >>
  disch_then (qspecl_then [`tn with t_var := tn.t_var |+ (ctr,{})`,
    `DRESTRICT G (COMPL {ctr})`, `D`, `PG`] mp_tac) >> strip_tac >>
  qpat_x_assum `gas_path_ptr _ _ _ _ _ G tn s _ _ _ _`
    (mp_then Any mp_tac gas_path_ptr_then) >> disch_then drule >> simp[]
QED

Theorem assign_base_storage_init_frame:
  !s fn bb id ctr hdr tn G ctx D PG loc a k root capacity.
    ~s.vs_halted /\ lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
    get_instruction bb s.vs_inst_idx = SOME (mk_inst id ASSIGN [Lit 0w] [ctr]) /\
    get_instruction bb (SUC s.vs_inst_idx) = SOME (mk_inst (id+1) JMP [Label hdr] []) /\
    ~ctx_has_dalloca ctx /\ root <> ctr /\
    ptr_covers G tn root s capacity /\ lookup_var root s = SOME a ==>
    ?Gf tf u.
      gas_path_ptr D 0 ctx fn PG G tn s 0 Gf tf (OK u) /\
      execution_frame u = execution_frame s /\
      assign_base_store_frame loc a k s tn 0 u tf /\
      ptr_covers Gf tf root u capacity /\ lookup_var root u = SOME a /\
      lookup_var ctr u = SOME 0w /\ FLOOKUP Gf ctr = NONE /\ op_taint tf (Var ctr) = {} /\
      u.vs_current_bb = hdr /\ u.vs_inst_idx = 0 /\ ~u.vs_halted /\
      (!x. x <> ctr ==> lookup_var x u = lookup_var x s /\
        FLOOKUP Gf x = FLOOKUP G x /\ op_taint tf (Var x) = op_taint tn (Var x))
Proof
  rpt gen_tac >> strip_tac >> drule_all assign_base_storage_init_counted >>
  disch_then (qspecl_then [`tn`, `G`, `D`, `PG`] mp_tac) >> strip_tac >>
  qexistsl_tac [`DRESTRICT G (COMPL {ctr})`, `tn with t_var := tn.t_var |+ (ctr,{})`,
    `jump_to hdr ((update_var ctr 0w s) with vs_inst_idx := SUC s.vs_inst_idx)`] >>
  simp[assign_base_store_frame_def, assign_base_store_prefix_zero,
    assign_base_store_taint_prefix_def, execution_frame_def, jump_to_def, update_var_def,
    lookup_var_def, FLOOKUP_UPDATE, FLOOKUP_DRESTRICT, op_taint_def] >>
  gvs[ptr_covers_def, jump_to_def, update_var_def, lookup_var_def,
    FLOOKUP_UPDATE, FLOOKUP_DRESTRICT, op_taint_def]
QED

Theorem assign_base_storage_compiled_counted:
  !tr root k n sa z sb fn s G tn ctx D PG a capacity.
    compile_word_copy_loop (Var root) (Lit k) n LocMemory
      (if tr then LocTransient else LocStorage) F sa = (z,sb) /\
    fn_has_code sa sb fn /\ not_fresh_at sa root /\
    ptr_covers G tn root s capacity /\ lookup_var root s = SOME a /\
    ~s.vs_halted /\ ~s.vs_call_ctx.cc_static /\ ~ctx_has_dalloca ctx /\
    s.vs_current_bb = sa.cs_current_bb /\ s.vs_inst_idx = LENGTH sa.cs_current_insts /\
    n < dimword (:256) /\ 32*n <= capacity /\
    w2n a+32*(n-1) < dimword (:256) ==>
    ?Gf tf u.
      gas_path_ptr D 0 ctx fn PG G tn s 0 Gf tf (OK u) /\
      execution_frame u = execution_frame (store_copy_prefix (if tr then LocTransient else LocStorage) a k s n) /\
      assign_base_store_frame (if tr then LocTransient else LocStorage) a k s tn n u tf /\
      ptr_covers Gf tf root u capacity /\ lookup_var root u = SOME a /\
      u.vs_current_bb = sb.cs_current_bb /\
      u.vs_inst_idx = LENGTH sb.cs_current_insts /\ ~u.vs_halted /\
      (!x. not_fresh_at sa x ==> lookup_var x u = lookup_var x s /\
        FLOOKUP Gf x = FLOOKUP G x /\ op_taint tf (Var x) = op_taint tn (Var x))
Proof
  rpt gen_tac >> strip_tac >> drule_all assign_base_store_compile_code >> strip_tac >>
  `root <> ctr /\ ALL_DISTINCT [root;ctr;done;mv;sv;vv;dv;nv]` by
    (gvs[ALL_DISTINCT] >> metis_tac[]) >>
  `get_instruction ib s.vs_inst_idx = SOME (mk_inst sa.cs_next_id ASSIGN [Lit 0w] [ctr]) /\
   get_instruction ib (SUC s.vs_inst_idx) = SOME (mk_inst (sa.cs_next_id+1) JMP [Label hdr] [])` by
    simp[get_instruction_def, EL_APPEND_EQN, ADD1] >>
  `lookup_block s.vs_current_bb fn.fn_blocks = SOME ib` by simp[] >>
  drule_all assign_base_storage_init_frame >>
  disch_then (qspecl_then [`D`, `PG`, `if tr then LocTransient else LocStorage`, `k`] mp_tac) >>
  disch_then (qx_choose_then `g1` (qx_choose_then `t1` (qx_choose_then `s1` strip_assume_tac))) >>
  `?gf tf u.
    gas_path_ptr D 0 ctx fn PG g1 t1 s1 0 gf tf (OK u) /\
    execution_frame u = execution_frame (store_copy_prefix (if tr then LocTransient else LocStorage) a k s n) /\
    assign_base_store_frame (if tr then LocTransient else LocStorage) a k s tn n u tf /\
    ptr_covers gf tf root u capacity /\ lookup_var root u = SOME a /\
    lookup_var ctr u = SOME (n2w n) /\ FLOOKUP gf ctr = NONE /\ op_taint tf (Var ctr) = {} /\
    u.vs_current_bb = sb.cs_current_bb /\ u.vs_inst_idx = 0 /\ ~u.vs_halted /\
    (!x. ~MEM x [ctr;done;mv;sv;vv;dv;nv] ==> lookup_var x u = lookup_var x s1 /\
      FLOOKUP gf x = FLOOKUP g1 x /\ op_taint tf (Var x) = op_taint t1 (Var x))` by
    (irule (Q.SPEC `0` assign_base_storage_loop_counted) >>
     simp[get_instruction_def, mk_inst_def] >>
     rpt (goal_assum (drule_at Any)) >>
     gvs[assign_base_store_prefix_zero, execution_frame_def]) >>
  qexistsl_tac [`gf`, `tf`, `u`] >> conj_tac >-
    (qpat_x_assum `gas_path_ptr _ _ _ _ _ G tn s _ _ _ _`
      (mp_then Any mp_tac gas_path_ptr_then) >> disch_then drule >> simp[]) >>
  asm_rewrite_tac[] >> simp[] >> metis_tac[MEM]
QED
