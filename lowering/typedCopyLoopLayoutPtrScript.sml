(* Concrete layout of the typed fixed-array loop.  The recursive child's
   final block is deliberately independent of the body-entry block. *)
Theory typedCopyLoopLayoutPtr
Ancestors typedCopyArrayPtr exprLoweringProps fragExec compileEnv emitHelper list
  abiEncoderExitPhi venomExecSemantics

Theorem compile_copy_sarray_typed_loop_layout:
  !ce dst dty src sty count sa sz.
    ~(type_memory_bytes ce dty = type_memory_bytes ce sty /\
      ~is_abi_dynamic ce.ce_struct_fields dty) /\
    compile_copy_sarray_typed ce dst dty src sty count sa = ((),sz) ==>
    ?cond body exit ctr lt done so doff sp dp sc sb si se tail.
      cond = fresh_label_output "typed_sa_cond" sa.cs_next_label /\
      body = fresh_label_output "typed_sa_body" (sa.cs_next_label + 1) /\
      exit = fresh_label_output "typed_sa_exit" (sa.cs_next_label + 2) /\
      ctr = "%" ++ toString sa.cs_next_var /\
      lt = "%" ++ toString (sa.cs_next_var + 1) /\
      done = "%" ++ toString (sa.cs_next_var + 2) /\
      so = "%" ++ toString (sa.cs_next_var + 3) /\
      doff = "%" ++ toString (sa.cs_next_var + 4) /\
      sp = "%" ++ toString (sa.cs_next_var + 5) /\
      dp = "%" ++ toString (sa.cs_next_var + 6) /\
      sc = sa with <|
        cs_next_label := sa.cs_next_label + 3;
        cs_next_var := sa.cs_next_var + 1;
        cs_next_id := sa.cs_next_id + 2;
        cs_blocks := <|bb_label := sa.cs_current_bb;
          bb_instructions := sa.cs_current_insts ++
            [mk_inst sa.cs_next_id ASSIGN [Lit 0w] [ctr];
             mk_inst (sa.cs_next_id+1) JMP [Label cond] []]|> :: sa.cs_blocks;
        cs_current_bb := cond; cs_current_insts := [] |> /\
      sb = sc with <|
        cs_next_var := sc.cs_next_var + 2;
        cs_next_id := sc.cs_next_id + 3;
        cs_blocks := <|bb_label := cond; bb_instructions :=
          [mk_inst sc.cs_next_id LT [Var ctr; Lit (n2w count)] [lt];
           mk_inst (sc.cs_next_id+1) ISZERO [Var lt] [done];
           mk_inst (sc.cs_next_id+2) JNZ
             [Var done; Label exit; Label body] []]|> :: sc.cs_blocks;
        cs_current_bb := body; cs_current_insts := [] |> /\
      si = sb with <|
        cs_next_var := sb.cs_next_var + 4;
        cs_next_id := sb.cs_next_id + 4;
        cs_current_insts :=
          [mk_inst sb.cs_next_id MUL
             [Var ctr; Lit (n2w (type_memory_bytes ce sty))] [so];
           mk_inst (sb.cs_next_id+1) MUL
             [Var ctr; Lit (n2w (type_memory_bytes ce dty))] [doff];
           mk_inst (sb.cs_next_id+2) ADD [src; Var so] [sp];
           mk_inst (sb.cs_next_id+3) ADD [dst; Var doff] [dp]] |> /\
      compile_store_memory_typed ce (Var dp) dty (Var sp) sty si = ((),se) /\
      tail = se with <|
        cs_next_var := se.cs_next_var + 1;
        cs_next_id := se.cs_next_id + 3;
        cs_current_insts := se.cs_current_insts ++
          [mk_inst se.cs_next_id ADD [Var ctr; Lit 1w]
             ["%" ++ toString se.cs_next_var];
           mk_inst (se.cs_next_id+1) ASSIGN
             [Var ("%" ++ toString se.cs_next_var)] [ctr];
           mk_inst (se.cs_next_id+2) JMP [Label cond] []] |> /\
      sz = tail with <|
        cs_blocks := <|bb_label := se.cs_current_bb;
          bb_instructions := tail.cs_current_insts|> :: se.cs_blocks;
        cs_current_bb := exit; cs_current_insts := [] |>
Proof
  rpt gen_tac >> strip_tac >>
  rename1 `compile_copy_sarray_typed ce dst dty src sty n sa = ((),sz)` >>
  drule compile_copy_sarray_typed_slow >>
  disch_then (qspecl_then [`dst`, `src`, `n`, `sa`, `sz`] mp_tac) >>
  asm_rewrite_tac[] >>
  simp[comp_bind_def, comp_ignore_bind_def, comp_return_def,
       fresh_label_def, fresh_var_def, fresh_id_def,
       emit_inst_def, emit_op_def, emit_def, new_block_def, APPEND_ASSOC] >>
  strip_tac >>
  qpat_x_assum `compile_copy_sarray_typed _ _ _ _ _ _ _ = _` kall_tac >>
  qmatch_asmsub_abbrev_tac `compile_store_memory_typed ce dop dty sop sty child` >>
  simp[APPEND_ASSOC] >>
  pairarg_tac >> gvs[] >>
  qexists_tac `cs'` >>
  fs[Abbr `child`] >>
  rule_assum_tac (PURE_REWRITE_RULE [GSYM APPEND_ASSOC, APPEND]) >>
  pure_rewrite_tac[GSYM APPEND_ASSOC, APPEND] >>
  asm_rewrite_tac[]
QED

(* Only the block-list spine is needed to locate the recursive child. *)
Theorem typed_copy_loop_slice_locations:
  !ce dst dty src sty sa si se sz entry test back fn.
    si.cs_blocks = test :: entry :: sa.cs_blocks /\
    entry.bb_label = sa.cs_current_bb /\
    isPREFIX sa.cs_current_insts entry.bb_instructions /\
    compile_store_memory_typed ce dst dty src sty si = ((),se) /\
    sz.cs_blocks = back :: se.cs_blocks /\
    back.bb_label = se.cs_current_bb /\
    isPREFIX se.cs_current_insts back.bb_instructions /\
    fn_has_code sa sz fn ==>
    lookup_block entry.bb_label fn.fn_blocks = SOME entry /\
    lookup_block test.bb_label fn.fn_blocks = SOME test /\
    lookup_block back.bb_label fn.fn_blocks = SOME back /\
    fn_has_code si se fn /\
    (?bb. lookup_block si.cs_current_bb fn.fn_blocks = SOME bb /\
          isPREFIX si.cs_current_insts bb.bb_instructions)
Proof
  rpt strip_tac >>
  `cs_extends si se` by
    (mp_tac (cj 1 ci_mono_typed_memory_family) >>
     disch_then (qspecl_then [`ce`, `dst`, `dty`, `src`, `sty`, `si`] mp_tac) >>
     asm_rewrite_tac[] >> simp[ci_mono_def]) >>
  `cs_extends sa si` by
    (simp[cs_extends_def] >> qexists_tac `[test;entry]` >> simp[]) >>
  `cs_extends se sz` by
    (simp[cs_extends_def] >> qexists_tac `[back]` >> simp[]) >>
  `cs_extends si sz` by metis_tac[cs_extends_trans] >>
  drule_all fn_has_code_split >> strip_tac >>
  `fn_has_code si se fn` by metis_tac[fn_has_code_split] >>
  `?children. se.cs_blocks = children ++ si.cs_blocks` by fs[cs_extends_def] >>
  `emitted_blocks sa sz = back :: children ++ [test;entry]` by
    (irule emitted_blocks_append >> simp[]) >>
  `lookup_block entry.bb_label fn.fn_blocks = SOME entry /\
   lookup_block test.bb_label fn.fn_blocks = SOME test /\
   lookup_block back.bb_label fn.fn_blocks = SOME back` by
    (fs[fn_has_code_def] >> metis_tac[MEM_APPEND, MEM]) >>
  metis_tac[fn_has_code_start]
QED

(* The generated condition and body entries have concrete non-PHI heads,
   even when a recursive element copy finishes in a different block. *)
Theorem compile_copy_sarray_typed_loop_no_phi:
  !ce dst dty src sty n sa sz fn.
    ~(type_memory_bytes ce dty = type_memory_bytes ce sty /\
      ~is_abi_dynamic ce.ce_struct_fields dty) /\
    compile_copy_sarray_typed ce dst dty src sty n sa = ((),sz) /\
    fn_has_code sa sz fn ==>
    (?test. lookup_block (fresh_label_output "typed_sa_cond" sa.cs_next_label)
              fn.fn_blocks = SOME test /\
            phi_prefix_length test.bb_instructions = 0) /\
    (?bb. lookup_block (fresh_label_output "typed_sa_body" (sa.cs_next_label+1))
              fn.fn_blocks = SOME bb /\
          phi_prefix_length bb.bb_instructions = 0)
Proof
  rpt gen_tac >> strip_tac >>
  drule_all compile_copy_sarray_typed_loop_layout >>
  strip_tac >>
  rename1 `compile_store_memory_typed ce (Var dp) dty (Var sp) sty si = ((),se)` >>
  `cs_extends si se` by
    (mp_tac (cj 1 ci_mono_typed_memory_family) >>
     disch_then (qspecl_then [`ce`, `Var dp`, `dty`, `Var sp`, `sty`, `si`] mp_tac) >>
     asm_rewrite_tac[] >> simp[ci_mono_def]) >>
  `cs_extends sa si` by
    (simp[cs_extends_def] >>
     qexists_tac `TAKE 2 si.cs_blocks` >>
     simp[]) >>
  `cs_extends se sz` by
    (simp[cs_extends_def] >> qexists_tac `[HD sz.cs_blocks]` >> simp[]) >>
  `cs_extends si sz` by metis_tac[cs_extends_trans] >>
  `fn_has_code sa si fn /\ fn_has_code si sz fn` by
    metis_tac[fn_has_code_split] >>
  `fn_has_code si se fn` by metis_tac[fn_has_code_split] >>
  `emitted_blocks sa si = TAKE 2 si.cs_blocks` by
    (irule emitted_blocks_append >> simp[]) >>
  `MEM (HD si.cs_blocks) (emitted_blocks sa si)` by
    (qpat_assum `emitted_blocks sa si = _` (fn th => rewrite_tac[th]) >>
     qpat_assum `si = _` (fn th => simp_tac (srw_ss()) [th]) >>
     qpat_assum `sb = _` (fn th => simp_tac (srw_ss()) [th])) >>
  `(HD si.cs_blocks).bb_label = cond /\
   phi_prefix_length (HD si.cs_blocks).bb_instructions = 0 /\
   si.cs_current_bb = body' /\ si.cs_current_insts <> [] /\
   phi_prefix_length si.cs_current_insts = 0` by
    (qpat_assum `si = _` (fn th => simp_tac (srw_ss())
       [th, phi_prefix_length_def, venomInstTheory.mk_inst_def]) >>
     qpat_assum `sb = _` (fn th => simp_tac (srw_ss())
       [th, phi_prefix_length_def, venomInstTheory.mk_inst_def])) >>
  qpat_x_assum `sc = _` kall_tac >>
  qpat_x_assum `sb = _` kall_tac >>
  qpat_x_assum `si = _` kall_tac >>
  qpat_x_assum `tail = _` kall_tac >>
  qpat_x_assum `sz = _` kall_tac >>
  conj_tac
  >- (qexists_tac `HD si.cs_blocks` >>
      fs[fn_has_code_def] >> metis_tac[]) >>
  mp_tac (Q.SPECL [`si`, `se`, `fn`] fn_has_code_start) >>
  asm_rewrite_tac[] >> strip_tac >>
  qexists_tac `bb` >> conj_tac >- metis_tac[] >>
  irule abi_encoder_nonempty_prefix_phi >>
  qexists_tac `si.cs_current_insts` >> simp[]
QED
