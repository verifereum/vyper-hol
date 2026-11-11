(* Conditional fixed-array normalization with counted pointer execution. *)
Theory annAssignTypedCopyFixedPtr
Ancestors
  annAssignTypedCopyFixedMetadataPtr annAssignTypedCopyFixedControlPtr
  annAssignTypedCopyArrayTraversalPtr annAssignTypedCopyAtomsPtr
  typedMemoryCopy bodyPtrStructLitMonotoneRepresentation typedCopyLoopLayoutPtr
  exprLoweringProps emitHelper venomExecSemantics venomInst
  context compileEnv fragExec fragGasPathPtr valueEncodingDefs valueEncoding
  venomState words arithmetic list bodyPtrDefs

(* The bulk compiler branch is a single memory copy, with its complete
   ambient resource frame.  tv describes the represented whole object. *)
Theorem annassign_sarray_bulk_counted[local]:
  !ce dst dt src st n sa sb fn s b a G tn D ctx PG tv v.
    compile_copy_sarray_typed ce (Var dst) dt (Var src) st n sa = ((),sb) /\
    type_memory_bytes ce dt = type_memory_bytes ce st /\
    ~is_abi_dynamic ce.ce_struct_fields dt /\
    n * type_memory_bytes ce dt < dimword (:256) /\
    fn_has_code sa sb fn /\ s.vs_current_bb = sa.cs_current_bb /\
    s.vs_inst_idx = LENGTH sa.cs_current_insts /\ ~s.vs_halted /\
    ~ctx_has_dalloca ctx /\
    ptr_covers G tn dst s (n * type_memory_bytes ce dt) /\
    ptr_covers G tn src s (n * type_memory_bytes ce dt) /\
    lookup_var dst s = SOME b /\ lookup_var src s = SOME a /\
    val_wf tv v /\ val_footprint tv v <= n * type_memory_bytes ce dt /\
    (!m. mem_agree_outside tn.t_mem s.vs_memory m ==>
      val_in_memory tv v (w2n a) m) ==>
    ?H tm t.
      gas_path_ptr D 0 ctx fn PG G tn s 0 H tm (OK t) /\
      t.vs_current_bb = sb.cs_current_bb /\
      t.vs_inst_idx = LENGTH sb.cs_current_insts /\ ~t.vs_halted /\
      typed_copy_state_frame sa (w2n b) (n * type_memory_bytes ce dt) s t /\
      (!m. mem_agree_outside tm.t_mem t.vs_memory m ==>
        val_in_memory tv v (w2n b) m) /\
      tm.t_stor = tn.t_stor /\ tm.t_trans = tn.t_trans /\ tm.t_imm = tn.t_imm /\
      (!x. lookup_var x t = lookup_var x s /\ FLOOKUP H x = FLOOKUP G x /\
        op_taint tm (Var x) = op_taint tn (Var x)) /\
      (!i. ~(w2n b <= i /\ i < w2n b + n * type_memory_bytes ce dt) ==>
        mem_bytes_at i 1 t.vs_memory = mem_bytes_at i 1 s.vs_memory /\
        (i IN tm.t_mem <=> i IN tn.t_mem))
Proof
  rpt gen_tac >> strip_tac >>
  `compile_copy_memory (Var dst) (Var src) (n * type_memory_bytes ce dt) sa = ((),sb)` by
    (qpat_x_assum `compile_copy_sarray_typed _ _ _ _ _ _ _ = _` mp_tac >>
     simp[Once compile_store_memory_typed_def]) >>
  drule_all annassign_copy_memory_counted_ambient_ptr >>
  disch_then (qspecl_then [`D`,`PG`] strip_assume_tac) >>
  qexistsl_tac [`Gf`,`tf`,`u`] >> simp[]
QED

(* Resolve compiler layout once, before reasoning about runtime segments. *)
Theorem annassign_sarray_loop_instruction_locations[local]:
  !ce dst dt src st n sa sz fn.
    ~(type_memory_bytes ce dt = type_memory_bytes ce st /\
      ~is_abi_dynamic ce.ce_struct_fields dt) /\
    compile_copy_sarray_typed ce dst dt src st n sa = ((),sz) /\
    fn_has_code sa sz fn ==>
    ?si se entry test body back ctr lt done so doff sp dp cond bodylbl exit.
      compile_store_memory_typed ce (Var dp) dt (Var sp) st si = ((),se) /\
      fn_has_code si se fn /\ cs_extends sa si /\ cs_extends si se /\
      cs_extends se sz /\ si.cs_next_var = sa.cs_next_var+7 /\
      si.cs_current_bb = bodylbl /\ LENGTH si.cs_current_insts = 4 /\
      sz.cs_current_bb = exit /\ sz.cs_current_insts = [] /\
      ctr = "%" ++ toString sa.cs_next_var /\
      lt = "%" ++ toString (sa.cs_next_var+1) /\
      done = "%" ++ toString (sa.cs_next_var+2) /\
      so = "%" ++ toString (sa.cs_next_var+3) /\
      doff = "%" ++ toString (sa.cs_next_var+4) /\
      sp = "%" ++ toString (sa.cs_next_var+5) /\
      dp = "%" ++ toString (sa.cs_next_var+6) /\
      lookup_block sa.cs_current_bb fn.fn_blocks = SOME entry /\
      get_instruction entry (LENGTH sa.cs_current_insts) =
        SOME (mk_inst sa.cs_next_id ASSIGN [Lit 0w] [ctr]) /\
      get_instruction entry (SUC (LENGTH sa.cs_current_insts)) =
        SOME (mk_inst (sa.cs_next_id+1) JMP [Label cond] []) /\
      lookup_block cond fn.fn_blocks = SOME test /\
      get_instruction test 0 =
        SOME (mk_inst (sa.cs_next_id+2) LT [Var ctr;Lit (n2w n)] [lt]) /\
      get_instruction test 1 =
        SOME (mk_inst (sa.cs_next_id+3) ISZERO [Var lt] [done]) /\
      get_instruction test 2 =
        SOME (mk_inst (sa.cs_next_id+4) JNZ
          [Var done;Label exit;Label bodylbl] []) /\
      lookup_block bodylbl fn.fn_blocks = SOME body /\
      get_instruction body 0 =
        SOME (mk_inst (sa.cs_next_id+5) MUL
          [Var ctr;Lit (n2w (type_memory_bytes ce st))] [so]) /\
      get_instruction body 1 =
        SOME (mk_inst (sa.cs_next_id+6) MUL
          [Var ctr;Lit (n2w (type_memory_bytes ce dt))] [doff]) /\
      get_instruction body 2 =
        SOME (mk_inst (sa.cs_next_id+7) ADD [src;Var so] [sp]) /\
      get_instruction body 3 =
        SOME (mk_inst (sa.cs_next_id+8) ADD [dst;Var doff] [dp]) /\
      lookup_block se.cs_current_bb fn.fn_blocks = SOME back /\
      get_instruction back (LENGTH se.cs_current_insts) =
        SOME (mk_inst se.cs_next_id ADD [Var ctr;Lit 1w]
          ["%" ++ toString se.cs_next_var]) /\
      get_instruction back (SUC (LENGTH se.cs_current_insts)) =
        SOME (mk_inst (se.cs_next_id+1) ASSIGN
          [Var ("%" ++ toString se.cs_next_var)] [ctr]) /\
      get_instruction back (LENGTH se.cs_current_insts+2) =
        SOME (mk_inst (se.cs_next_id+2) JMP [Label cond] [])
Proof
  rpt gen_tac >> strip_tac >>
  drule_all compile_copy_sarray_typed_loop_layout >> strip_tac >>
  `cs_extends si se` by
    (mp_tac (cj 1 ci_mono_typed_memory_family) >>
     disch_then (qspecl_then [`ce`, `Var dp`, `dt`, `Var sp`, `st`, `si`] mp_tac) >>
     pure_asm_rewrite_tac [pairTheory.SND] >>
     rewrite_tac[ci_mono_def] >> metis_tac[]) >>
  `cs_extends sa si /\ cs_extends se sz` by
    simp[cs_extends_def] >>
  qabbrev_tac `entry = HD sc.cs_blocks` >>
  qabbrev_tac `test = HD sb.cs_blocks` >>
  qabbrev_tac `back = HD sz.cs_blocks` >>
  `si.cs_blocks = test::entry::sa.cs_blocks /\
   entry.bb_label = sa.cs_current_bb /\
   isPREFIX sa.cs_current_insts entry.bb_instructions /\
   sz.cs_blocks = back::se.cs_blocks /\
   back.bb_label = se.cs_current_bb /\
   isPREFIX se.cs_current_insts back.bb_instructions` by
    simp[Abbr `entry`, Abbr `test`, Abbr `back`] >>
  drule_all typed_copy_loop_slice_locations >> strip_tac >>
  qexistsl_tac [`si`, `se`, `entry`, `test`, `bb`, `back`,
    `ctr`, `lt`, `done`, `so`, `doff`, `sp`, `dp`, `cond`, `body'`, `exit`] >>
  simp[Abbr `entry`, Abbr `test`, Abbr `back`, get_instruction_def, EL_APPEND_EQN] >>
  qpat_x_assum `isPREFIX si.cs_current_insts bb.bb_instructions` mp_tac >>
  simp[rich_listTheory.IS_PREFIX_APPEND] >> strip_tac >>
  gvs[get_instruction_def, EL_APPEND_EQN]
QED
