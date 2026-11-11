(*
 * Fuel bound for the dynamic-element dynamic-array ABI encode loop.
 *
 * TOP-LEVEL:
 *   fuel_okS_compile_abi_encode_dyn_loop
 *)

Theory fragFuelLoopAbiEncDyn
Ancestors
  fragFuel fragFuelContextBase abiEncoder compileEnv emitHelper context
  venomInst venomExecSemantics venomState
Libs
  fragFuelLib monadsyntax

(* Opening every jump target is useful only for compiler-state facts; the
   closed-exit runtime bound is established separately below. *)
Theorem abi_encode_dyn_loop_open_exits[local]:
  (!d s Wv E. fuel_ok Wv {} E (compile_abi_encode_to_buf d s ei)) ==>
  fuel_ok {} {} UNIV
    (compile_abi_encode_dyn_loop dst src ei asz msz len_op)
Proof
  strip_tac >>
  simp_tac std_ss [Once (List.last (CONJUNCTS compile_abi_encode_child_def))] >>
  fuel_auto [fuel_ok_compile_alloc_buffer, fuel_ok_emit_op,
             fuel_ok_emit_void, fuel_ok_emit_inst_jmp,
             fuel_ok_emit_inst_jnz] >>
  simp[is_terminator_def]
QED

(* Six phases.  The recursive action is deliberately not unfolded. *)
Theorem abi_encode_dyn_loop_layout[local]:
  compile_abi_encode_dyn_loop dst src ei asz msz len_op =
  do p <-
       (do ia <- compile_alloc_buffer 32;
           let ip = ia.buf_operand in
           do emit_void MSTORE [ip; Lit 0w];
              da <- compile_alloc_buffer 32;
              let dp = da.buf_operand in
              do init <- emit_op MUL [len_op; Lit (n2w asz)];
                 emit_void MSTORE [dp; init];
                 hdr <- fresh_label "enc_dyn_hdr";
                 body <- fresh_label "enc_dyn_body";
                 exit <- fresh_label "enc_dyn_exit";
                 emit_inst JMP [Label hdr] [];
                 new_block hdr;
                 return (ip, dp, hdr, body, exit)
              od
           od
        od);
     let (ip, dp, hdr, body, exit) = p in
     do (do i <- emit_op MLOAD [ip];
            cmp <- emit_op LT [i; len_op];
            done <- emit_op ISZERO [cmp];
            emit_inst JNZ [done; Label exit; Label body] [];
            new_block body
         od);
        q <-
          (do i2 <- emit_op MLOAD [ip];
              sd <- emit_op ADD [src; Lit 32w];
              so <- emit_op MUL [i2; Lit (n2w msz)];
              cs <- emit_op ADD [sd; so];
              dd <- emit_op ADD [dst; Lit 32w];
              ho <- emit_op MUL [i2; Lit (n2w asz)];
              hp <- emit_op ADD [dd; ho];
              off <- emit_op MLOAD [dp];
              cd <- emit_op ADD [dd; off];
              return (i2, hp, off, cd, cs)
           od);
        let (i2, hp, off, cd, cs) = q in
        do cl <- compile_abi_encode_to_buf cd cs ei;
           (do emit_void MSTORE [hp; off];
               nd <- emit_op ADD [off; cl];
               emit_void MSTORE [dp; nd];
               ni <- emit_op ADD [i2; Lit 1w];
               emit_void MSTORE [ip; ni];
               emit_inst JMP [Label hdr] [];
               new_block exit
            od);
           (do emit_op MLOAD [src];
               fd <- emit_op MLOAD [dp];
               emit_op ADD [Lit 32w; fd]
            od)
        od
     od
  od
Proof
  simp_tac std_ss
    [Once (List.last (CONJUNCTS compile_abi_encode_child_def)),
     comp_ignore_bind_def, LET_THM, comp_bind_assoc, comp_bind_return]
QED

(* Concrete straight-line body boundary, including instruction identifiers.
   fn_has_code_same_block can be used directly with this appended code. *)
Theorem abi_encode_dyn_body_prefix[local]:
  let v = (\k. Var ("%" ++ toString (st.cs_next_var + k)));
      ins = (\k opc ops. mk_inst (st.cs_next_id + k) opc ops
                           ["%" ++ toString (st.cs_next_var + k)]);
      code = [ins 0 MLOAD [ip];
              ins 1 ADD [src; Lit 32w];
              ins 2 MUL [v 0; Lit (n2w msz)];
              ins 3 ADD [v 1; v 2];
              ins 4 ADD [dst; Lit 32w];
              ins 5 MUL [v 0; Lit (n2w asz)];
              ins 6 ADD [v 4; v 5];
              ins 7 MLOAD [dp];
              ins 8 ADD [v 4; v 7]]
  in
    (do i2 <- emit_op MLOAD [ip];
        sd <- emit_op ADD [src; Lit 32w];
        so <- emit_op MUL [i2; Lit (n2w msz)];
        cs <- emit_op ADD [sd; so];
        dd <- emit_op ADD [dst; Lit 32w];
        ho <- emit_op MUL [i2; Lit (n2w asz)];
        hp <- emit_op ADD [dd; ho];
        off <- emit_op MLOAD [dp];
        cd <- emit_op ADD [dd; off];
        return (i2, hp, off, cd, cs)
     od) st =
    ((v 0, v 6, v 7, v 8, v 3),
     st with <|cs_next_var := st.cs_next_var + 9;
               cs_next_id := st.cs_next_id + 9;
               cs_current_insts := st.cs_current_insts ++ code|>)
Proof
  simp[LET_THM, emit_op_def, fresh_id_def, fresh_var_def, emit_def,
       comp_bind_def, comp_ignore_bind_def, comp_return_def] >>
  pure_rewrite_tac [GSYM listTheory.APPEND_ASSOC, listTheory.APPEND] >>
  simp[]
QED

Theorem abi_encode_dyn_setup[local]:
  let ip = Var ("%" ++ toString st.cs_next_var);
      dp = Var ("%" ++ toString (st.cs_next_var + 1));
      init = Var ("%" ++ toString (st.cs_next_var + 2));
      hdr = fresh_label_output "enc_dyn_hdr" st.cs_next_label;
      body = fresh_label_output "enc_dyn_body" (st.cs_next_label + 1);
      exit = fresh_label_output "enc_dyn_exit" (st.cs_next_label + 2);
      code = [mk_inst st.cs_next_id ALLOCA [Lit 32w]
                ["%" ++ toString st.cs_next_var];
              mk_inst (st.cs_next_id + 1) MSTORE [ip; Lit 0w] [];
              mk_inst (st.cs_next_id + 2) ALLOCA [Lit 32w]
                ["%" ++ toString (st.cs_next_var + 1)];
              mk_inst (st.cs_next_id + 3) MUL [len_op; Lit (n2w asz)]
                ["%" ++ toString (st.cs_next_var + 2)];
              mk_inst (st.cs_next_id + 4) MSTORE [dp; init] [];
              mk_inst (st.cs_next_id + 5) JMP [Label hdr] []]
  in
  (do ia <- compile_alloc_buffer 32;
      let ip = ia.buf_operand in
      do emit_void MSTORE [ip; Lit 0w];
         da <- compile_alloc_buffer 32;
         let dp = da.buf_operand in
         do init <- emit_op MUL [len_op; Lit (n2w asz)];
            emit_void MSTORE [dp; init];
            hdr <- fresh_label "enc_dyn_hdr";
            body <- fresh_label "enc_dyn_body";
            exit <- fresh_label "enc_dyn_exit";
            emit_inst JMP [Label hdr] [];
            new_block hdr;
            return (ip, dp, hdr, body, exit)
         od
      od
   od) st =
  ((ip, dp, hdr, body, exit),
   st with <|cs_next_var := st.cs_next_var + 3;
             cs_next_id := st.cs_next_id + 6;
             cs_next_label := st.cs_next_label + 3;
             cs_blocks :=
               <|bb_label := st.cs_current_bb;
                 bb_instructions := st.cs_current_insts ++ code|> :: st.cs_blocks;
             cs_current_bb := hdr; cs_current_insts := []|>)
Proof
  simp[LET_THM, compile_alloc_buffer_def, emit_op_def, emit_void_def,
       emit_inst_def, fresh_id_def, fresh_var_def, fresh_label_def,
       emit_def, new_block_def, comp_bind_def, comp_ignore_bind_def,
       comp_return_def] >>
  pure_rewrite_tac [GSYM listTheory.APPEND_ASSOC, listTheory.APPEND] >>
  simp[]
QED

Theorem abi_encode_dyn_header[local]:
  !st ip len_op exit body.
  let v = (\k. Var ("%" ++ toString (st.cs_next_var + k)));
      ins = (\k opc ops. mk_inst (st.cs_next_id + k) opc ops
                           ["%" ++ toString (st.cs_next_var + k)]);
      code = [ins 0 MLOAD [ip]; ins 1 LT [v 0; len_op];
              ins 2 ISZERO [v 1];
              mk_inst (st.cs_next_id + 3) JNZ
                [v 2; Label exit; Label body] []]
  in
  (do i <- emit_op MLOAD [ip];
      cmp <- emit_op LT [i; len_op];
      done <- emit_op ISZERO [cmp];
      emit_inst JNZ [done; Label exit; Label body] [];
      new_block body
   od) st =
  (st.cs_current_bb,
   st with <|cs_next_var := st.cs_next_var + 3;
             cs_next_id := st.cs_next_id + 4;
             cs_blocks :=
               <|bb_label := st.cs_current_bb;
                 bb_instructions := st.cs_current_insts ++ code|> :: st.cs_blocks;
             cs_current_bb := body; cs_current_insts := []|>)
Proof
  simp[LET_THM, emit_op_def, emit_inst_def, fresh_id_def, fresh_var_def,
       emit_def, new_block_def, comp_bind_def, comp_ignore_bind_def,
       comp_return_def] >>
  pure_rewrite_tac [GSYM listTheory.APPEND_ASSOC, listTheory.APPEND] >>
  simp[]
QED

Theorem abi_encode_dyn_body_suffix[local]:
  let nd = Var ("%" ++ toString st.cs_next_var);
      ni = Var ("%" ++ toString (st.cs_next_var + 1));
      code = [mk_inst st.cs_next_id MSTORE [hp; off] [];
              mk_inst (st.cs_next_id + 1) ADD [off; cl]
                ["%" ++ toString st.cs_next_var];
              mk_inst (st.cs_next_id + 2) MSTORE [dp; nd] [];
              mk_inst (st.cs_next_id + 3) ADD [i2; Lit 1w]
                ["%" ++ toString (st.cs_next_var + 1)];
              mk_inst (st.cs_next_id + 4) MSTORE [ip; ni] [];
              mk_inst (st.cs_next_id + 5) JMP [Label hdr] []]
  in
  (do emit_void MSTORE [hp; off];
      nd <- emit_op ADD [off; cl];
      emit_void MSTORE [dp; nd];
      ni <- emit_op ADD [i2; Lit 1w];
      emit_void MSTORE [ip; ni];
      emit_inst JMP [Label hdr] [];
      new_block exit
   od) st =
  (st.cs_current_bb,
   st with <|cs_next_var := st.cs_next_var + 2;
             cs_next_id := st.cs_next_id + 6;
             cs_blocks :=
               <|bb_label := st.cs_current_bb;
                 bb_instructions := st.cs_current_insts ++ code|> :: st.cs_blocks;
             cs_current_bb := exit; cs_current_insts := []|>)
Proof
  simp[LET_THM, emit_op_def, emit_void_def, emit_inst_def,
       fresh_id_def, fresh_var_def, emit_def, new_block_def,
       comp_bind_def, comp_ignore_bind_def, comp_return_def] >>
  pure_rewrite_tac [GSYM listTheory.APPEND_ASSOC, listTheory.APPEND] >>
  simp[]
QED

Theorem abi_encode_dyn_exit[local]:
  let v = (\k. Var ("%" ++ toString (st.cs_next_var + k)));
      ins = (\k opc ops. mk_inst (st.cs_next_id + k) opc ops
                           ["%" ++ toString (st.cs_next_var + k)]);
      code = [ins 0 MLOAD [src]; ins 1 MLOAD [dp];
              ins 2 ADD [Lit 32w; v 1]]
  in
  (do emit_op MLOAD [src];
      fd <- emit_op MLOAD [dp];
      emit_op ADD [Lit 32w; fd]
   od) st =
  (v 2, st with <|cs_next_var := st.cs_next_var + 3;
                 cs_next_id := st.cs_next_id + 3;
                 cs_current_insts := st.cs_current_insts ++ code|>)
Proof
  simp[LET_THM, emit_op_def, fresh_id_def, fresh_var_def, emit_def,
       comp_bind_def, comp_ignore_bind_def, comp_return_def] >>
  pure_rewrite_tac [GSYM listTheory.APPEND_ASSOC, listTheory.APPEND] >>
  simp[]
QED
(* Saved operands all precede the child.  These are precisely the variables
   the suffix needs; no memory preservation hypothesis is involved. *)
Theorem abi_encode_dyn_saved_vars[local]:
  (!x. len_op = Var x ==> var_below n x) /\ n + 15 <= nc ==>
  (!x. len_op = Var x ==> var_below nc x) /\
  EVERY (var_below nc)
    ["%" ++ toString n; "%" ++ toString (n + 1);
     "%" ++ toString (n + 6); "%" ++ toString (n + 12);
     "%" ++ toString (n + 13)]
Proof
  strip_tac >> conj_tac
  >- (rpt strip_tac >> first_x_assum drule >>
      simp[var_below_def] >> metis_tac[arithmeticTheory.LESS_EQ_TRANS,
                                     arithmeticTheory.LESS_EQ_ADD]) >>
  simp[listTheory.EVERY_DEF, var_below_def,
       ASCIInumbersTheory.toString_inj] >> rpt strip_tac >> decide_tac
QED

Theorem abi_encode_dyn_setup_fuel[local]:
  fuel_ok {} {} {}
    (do ia <- compile_alloc_buffer 32;
        let ip = ia.buf_operand in
        do emit_void MSTORE [ip; Lit 0w];
           da <- compile_alloc_buffer 32;
           let dp = da.buf_operand in
           do init <- emit_op MUL [len_op; Lit (n2w asz)];
              emit_void MSTORE [dp; init];
              hdr <- fresh_label "enc_dyn_hdr";
              body <- fresh_label "enc_dyn_body";
              exit <- fresh_label "enc_dyn_exit";
              emit_inst JMP [Label hdr] [];
              new_block hdr;
              return (ip, dp, hdr, body, exit)
           od
        od
     od)
Proof
  fuel_auto [fuel_ok_compile_alloc_buffer, fuel_ok_emit_op,
             fuel_ok_emit_void, fuel_ok_emit_inst_jmp] >>
  simp[is_terminator_def]
QED

Theorem abi_encode_dyn_header_fuel[local]:
  !ip len_op exit body.
  fuel_ok {} {} {exit; body}
    (do i <- emit_op MLOAD [ip];
        cmp <- emit_op LT [i; len_op];
        done <- emit_op ISZERO [cmp];
        emit_inst JNZ [done; Label exit; Label body] [];
        new_block body
     od)
Proof
  rpt gen_tac >>
  fuel_auto [fuel_ok_emit_op, fuel_ok_emit_inst_jnz] >>
  simp[is_terminator_def]
QED

Theorem abi_encode_dyn_body_prefix_fuel[local]:
  fuel_ok {} {} {}
    (do i2 <- emit_op MLOAD [ip];
        sd <- emit_op ADD [src; Lit 32w];
        so <- emit_op MUL [i2; Lit (n2w msz)];
        cs <- emit_op ADD [sd; so];
        dd <- emit_op ADD [dst; Lit 32w];
        ho <- emit_op MUL [i2; Lit (n2w asz)];
        hp <- emit_op ADD [dd; ho];
        off <- emit_op MLOAD [dp];
        cd <- emit_op ADD [dd; off];
        return (i2, hp, off, cd, cs)
     od)
Proof
  fuel_auto [fuel_ok_emit_op] >> simp[is_terminator_def]
QED

Theorem abi_encode_dyn_body_suffix_fuel[local]:
  fuel_ok {} {} {hdr}
    (do emit_void MSTORE [hp; off];
        nd <- emit_op ADD [off; cl];
        emit_void MSTORE [dp; nd];
        ni <- emit_op ADD [i2; Lit 1w];
        emit_void MSTORE [ip; ni];
        emit_inst JMP [Label hdr] [];
        new_block exit
     od)
Proof
  fuel_auto [fuel_ok_emit_op, fuel_ok_emit_void, fuel_ok_emit_inst_jmp] >>
  simp[is_terminator_def]
QED

Theorem abi_encode_dyn_exit_fuel[local]:
  fuel_ok {} {} {}
    (do emit_op MLOAD [src];
        fd <- emit_op MLOAD [dp];
        emit_op ADD [Lit 32w; fd]
     od)
Proof
  fuel_auto [fuel_ok_emit_op] >> simp[is_terminator_def]
QED


(* Interface notes:
   - abi_encode_dyn_loop_layout splits the six phases without unfolding the
     recursive child.  Use comp_bind_def to name their intermediate states.
   - The concrete phase equations supply appended instruction lists and
     completed blocks.  Reuse fn_has_code_mid, fn_has_code_same_block and
     fn_has_code_new_block for their lookup facts.
   - Instantiate the child hypothesis at Wv = {} and E = {}, then use
     fuel_ok_def for its extension, variable monotonicity and frag_fuel bound.
     The open-exits lemma similarly supplies the whole action's structural
     properties; it is not a closed-exit runtime bound.
   - Setup, header and prefix allocate 3 + 3 + 9 variables.  The saved-vars
     lemma lists ip, dp, i2, hp and off, all below the child's entry counter.
     The phase fuel lemmas supply the non-recursive fragment bounds. *)

(* header_semantics: the header observes memory without modifying it. *)
Theorem abi_encode_dyn_header_semantics[local]:
  !id ip x y z len_op exit body G ctx fn s bb N.
  let code = [mk_inst id MLOAD [ip] [x];
              mk_inst (id+1) LT [Var x; len_op] [y];
              mk_inst (id+2) ISZERO [Var y] [z];
              mk_inst (id+3) JNZ [Var z; Label exit; Label body] []]
  in
  no_phi_fn fn /\ callees_stable G ctx fn /\
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  get_instruction bb s.vs_inst_idx = SOME (EL 0 code) /\
  get_instruction bb (s.vs_inst_idx+1) = SOME (EL 1 code) /\
  get_instruction bb (s.vs_inst_idx+2) = SOME (EL 2 code) /\
  get_instruction bb (s.vs_inst_idx+3) = SOME (EL 3 code) /\
  ALL_DISTINCT [x;y;z] /\
  EVERY (\v. ~var_below N v /\ ip <> Var v /\ len_op <> Var v) [x;y;z]
  ==>
  fuel_outcome G ctx fn s 1
    (\t. vars_kept N {} s t /\
      ((t.vs_current_bb = exit /\ t.vs_inst_idx = 0) \/
       (t.vs_current_bb = body /\ t.vs_inst_idx = 0 /\
        ?a b. eval_operand ip s = SOME a /\
              eval_operand len_op s = SOME b /\
              eval_operand ip t = SOME a /\
              mload (w2n a) t = mload (w2n a) s /\
              w2n (mload (w2n a) s) < w2n b)))
Proof
  rpt gen_tac >>
  simp_tac std_ss [LET_THM, listTheory.EVERY_DEF,
                    listTheory.ALL_DISTINCT, listTheory.EL,
                    listTheory.HD, listTheory.TL] >> strip_tac >>
  rename1 `[Var z; Label exit; Label body_lbl]` >>
  `~is_terminator (mk_inst id MLOAD [ip] [x]).inst_opcode`
    by simp[mk_inst_def, is_terminator_def] >>
  drule_all run_from_nonterm_stable >> reverse strip_tac
  >- (simp[fuel_outcome_def] >> disj2_tac >> rpt strip_tac >>
      `G <= f+1 /\ G <= G+1` by decide_tac >> metis_tac[]) >>
  gvs[mk_inst_def, step_inst_non_invoke, step_inst_base_opcode_eqs,
      exec_read1_def, AllCaseEqs()] >>
  rename1 `eval_operand ip s = SOME a` >>
  qabbrev_tac `u = update_var x (mload (w2n a) s) s with
                   vs_inst_idx := SUC s.vs_inst_idx` >>
  `lookup_block u.vs_current_bb fn.fn_blocks = SOME bb`
    by simp[Abbr `u`, update_var_def] >>
  `get_instruction bb u.vs_inst_idx =
     SOME (mk_inst (id+1) LT [Var x; len_op] [y])`
    by simp[Abbr `u`, mk_inst_def, arithmeticTheory.ADD1] >>
  qpat_x_assum `get_instruction bb s.vs_inst_idx = _` kall_tac >>
  `~is_terminator (mk_inst (id+1) LT [Var x; len_op] [y]).inst_opcode`
    by simp[mk_inst_def, is_terminator_def] >>
  drule_all run_from_nonterm_stable >> reverse strip_tac
  >- (simp[fuel_outcome_def] >> disj2_tac >> rpt strip_tac >>
      `G <= f+1 /\ G <= G+1` by decide_tac >> metis_tac[]) >>
  gvs[mk_inst_def, step_inst_non_invoke, step_inst_base_opcode_eqs,
      exec_pure2_def, AllCaseEqs()] >>
  `eval_operand (Var x) u = SOME (mload (w2n a) s)`
    by gvs[Abbr `u`, eval_operand_def, update_var_def, lookup_var_def,
             finite_mapTheory.FLOOKUP_UPDATE] >>
  `eval_operand len_op u = eval_operand len_op s`
    by (Cases_on `len_op` >>
        gvs[Abbr `u`, eval_operand_def, update_var_def, lookup_var_def,
             finite_mapTheory.FLOOKUP_UPDATE]) >>
  gvs[] >>
  rename1 `eval_operand len_op s = SOME b` >>
  qabbrev_tac `v = update_var y
    (bool_to_word (w2n (mload (w2n a) s) < w2n b)) u
    with vs_inst_idx := SUC u.vs_inst_idx` >>
  `lookup_block v.vs_current_bb fn.fn_blocks = SOME bb`
    by simp[Abbr `v`, update_var_def] >>
  `get_instruction bb v.vs_inst_idx =
    SOME (mk_inst (id+2) ISZERO [Var y] [z])`
    by simp[Abbr `v`, Abbr `u`, mk_inst_def, arithmeticTheory.ADD1] >>
  qpat_x_assum `get_instruction bb u.vs_inst_idx = _` kall_tac >>
  `~is_terminator (mk_inst (id+2) ISZERO [Var y] [z]).inst_opcode`
    by simp[mk_inst_def, is_terminator_def] >>
  drule_all run_from_nonterm_stable >> reverse strip_tac
  >- (simp[fuel_outcome_def] >> disj2_tac >> rpt strip_tac >>
      `G <= f+1 /\ G <= G+1` by decide_tac >> metis_tac[]) >>
  gvs[mk_inst_def, step_inst_non_invoke, step_inst_base_opcode_eqs,
      exec_pure1_def, AllCaseEqs()] >>
  `eval_operand (Var y) v = SOME
     (bool_to_word (w2n (mload (w2n a) s) < w2n b))`
    by gvs[Abbr `v`, eval_operand_def, update_var_def, lookup_var_def,
           finite_mapTheory.FLOOKUP_UPDATE] >>
  gvs[] >>
  qabbrev_tac `w = update_var z
    (bool_to_word (bool_to_word (w2n (mload (w2n a) s) < w2n b) = 0w)) v
    with vs_inst_idx := SUC v.vs_inst_idx` >>
  `lookup_block w.vs_current_bb fn.fn_blocks = SOME bb`
    by simp[Abbr `w`, update_var_def] >>
  `get_instruction bb w.vs_inst_idx =
    SOME (mk_inst (id+3) JNZ [Var z; Label exit; Label body_lbl] [])`
    by simp[Abbr `w`, Abbr `v`, Abbr `u`, mk_inst_def,
            arithmeticTheory.ADD1] >>
  qmatch_goalsub_abbrev_tac `fuel_outcome G ctx fn s 1 post` >>
  `fuel_outcome G ctx fn w 1 post` suffices_by
    (simp[fuel_outcome_def] >>
     `!f. G <= f ==> run_from (f+1) ctx fn s = run_from (f+1) ctx fn w`
       by (rpt strip_tac >> first_x_assum irule >> decide_tac) >>
     metis_tac[]) >>
  irule fuel_outcome_jump >> conj_tac >- simp[] >>
  qexistsl_tac [`bb`, `mk_inst (id+3) JNZ [Var z; Label exit; Label body_lbl] []`,
    `if w2n (mload (w2n a) s) < w2n b then body_lbl else exit`] >>
  simp[mk_inst_def, is_terminator_def] >>
  conj_tac
  >- (Cases_on `w2n (mload (w2n a) s) < w2n b` >>
      simp[step_inst_base_opcode_eqs, Abbr `w`, eval_operand_def,
           update_var_def, lookup_var_def, finite_mapTheory.FLOOKUP_UPDATE,
           bool_to_word_def]) >>
  strip_tac >> simp[Abbr `post`, jump_to_def] >>
  conj_tac
  >- (simp[vars_kept_def, Abbr `w`, Abbr `v`, Abbr `u`,
           update_var_def, lookup_var_def, finite_mapTheory.FLOOKUP_UPDATE] >>
      rpt strip_tac >> metis_tac[]) >>
  Cases_on `w2n (mload (w2n a) s) < w2n b` >>
  simp[Abbr `w`, Abbr `v`, Abbr `u`, update_var_def, mload_def] >>
  Cases_on `ip` >>
  gvs[eval_operand_def, update_var_def, lookup_var_def,
      finite_mapTheory.FLOOKUP_UPDATE]
QED

(* The body saves the counter in i2 before the recursive encoder.  Its last
   memory write restores i2+1, even if the child overwrites the counter's
   memory.  A continuing round has i2 < len_op and thus cannot wrap. *)
Theorem fuel_okS_compile_abi_encode_dyn_loop:
  !dst src elem_info elem_abi_sz elem_mem_sz len_op.
    (!d s Wv E. fuel_ok Wv {} E (compile_abi_encode_to_buf d s elem_info)) ==>
    !Wv E.
      fuel_okS (\st. !x. len_op = Var x ==> var_below st.cs_next_var x)
        Wv {} E
        (compile_abi_encode_dyn_loop dst src elem_info elem_abi_sz
           elem_mem_sz len_op)
Proof
  cheat
QED
