(*
 * Fuel bound for the dynamic-element dynamic-array ABI encode loop.
 *
 * TOP-LEVEL:
 *   fuel_okS_compile_abi_encode_dyn_loop
 *)

Theory fragFuelLoopAbiEncDyn
Ancestors
  fragFuel fragFuelContextBase abiEncoder compileEnv emitHelper context
  venomInst venomExecSemantics venomState ssaOperandFrame venomMemProps
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

(* prefix_semantics: address computations do not change memory. *)
Theorem abi_encode_dyn_prefix_semantics[local]:
  !id ip src dst dp msz asz x0 x1 x2 x3 x4 x5 x6 x7 x8
   G ctx fn s bb N a.
  let outputs = [x0;x1;x2;x3;x4;x5;x6;x7;x8];
      code = [mk_inst id MLOAD [ip] [x0];
              mk_inst (id+1) ADD [src; Lit 32w] [x1];
              mk_inst (id+2) MUL [Var x0; Lit (n2w msz)] [x2];
              mk_inst (id+3) ADD [Var x1; Var x2] [x3];
              mk_inst (id+4) ADD [dst; Lit 32w] [x4];
              mk_inst (id+5) MUL [Var x0; Lit (n2w asz)] [x5];
              mk_inst (id+6) ADD [Var x4; Var x5] [x6];
              mk_inst (id+7) MLOAD [dp] [x7];
              mk_inst (id+8) ADD [Var x4; Var x7] [x8]]
  in
  callees_stable G ctx fn /\
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  (!i. i < 9 ==> get_instruction bb (s.vs_inst_idx+i) = SOME (EL i code)) /\
  ALL_DISTINCT outputs /\
  EVERY (\v. ~var_below N v /\ ip <> Var v) outputs /\
  eval_operand ip s = SOME a ==>
  fuel_outcome G ctx fn s 0
    (\t. t.vs_current_bb = s.vs_current_bb /\
         t.vs_inst_idx = s.vs_inst_idx+9 /\ vars_kept N {} s t /\
         eval_operand ip t = SOME a /\
         eval_operand (Var x0) t = SOME (mload (w2n a) s) /\
         (!p. mload p t = mload p s) /\
         (!x. ~MEM x outputs ==> lookup_var x t = lookup_var x s))
Proof
  rpt gen_tac >> simp_tac std_ss [LET_THM] >> strip_tac >>
  qmatch_goalsub_abbrev_tac `fuel_outcome G ctx fn s 0 post` >>
  `get_instruction bb s.vs_inst_idx = SOME (mk_inst id MLOAD [ip] [x0])`
    by (first_x_assum (qspec_then `0` mp_tac) >> simp[]) >>
  `~is_terminator (mk_inst id MLOAD [ip] [x0]).inst_opcode`
    by simp[mk_inst_def, is_terminator_def] >>
  drule_all run_from_nonterm_stable >> reverse strip_tac
  >- (simp[fuel_outcome_def] >> metis_tac[]) >>
  gvs[mk_inst_def, step_inst_non_invoke, step_inst_base_opcode_eqs,
      exec_read1_def] >>
  qabbrev_tac `u1 = update_var x0 (mload (w2n a) s) s with
                    vs_inst_idx := SUC s.vs_inst_idx` >>
  `fuel_outcome G ctx fn u1 0 post` suffices_by
    (simp[fuel_outcome_def] >> metis_tac[]) >>
  `lookup_block u1.vs_current_bb fn.fn_blocks = SOME bb`
    by simp[Abbr `u1`, update_var_def] >>
  `get_instruction bb u1.vs_inst_idx =
     SOME (mk_inst (id+1) ADD [src; Lit 32w] [x1])`
    by (qpat_x_assum `!i. i < 9 ==> _` (qspec_then `1` mp_tac) >>
        simp[Abbr `u1`, mk_inst_def, arithmeticTheory.ADD1]) >>
  qpat_x_assum `get_instruction bb s.vs_inst_idx = _` kall_tac >>
  `~is_terminator (mk_inst (id+1) ADD [src; Lit 32w] [x1]).inst_opcode`
    by simp[mk_inst_def, is_terminator_def] >>
  drule_all run_from_nonterm_stable >> reverse strip_tac
  >- (simp[fuel_outcome_def] >> metis_tac[]) >>
  `?w. s1 = update_var x1 w u1` by
    (qpat_x_assum `step_inst _ _ _ _ = OK _` mp_tac >>
     simp[mk_inst_def, step_inst_non_invoke, step_inst_base_opcode_eqs,
          exec_pure2_def, AllCaseEqs()] >> metis_tac[]) >>
  qpat_x_assum `step_inst _ _ _ _ = OK _` kall_tac >>
  gvs[] >>
  qabbrev_tac `u2 = update_var x1 w u1 with vs_inst_idx := SUC u1.vs_inst_idx` >>
  `fuel_outcome G ctx fn u2 0 post` suffices_by
    (simp[fuel_outcome_def] >> metis_tac[]) >>
  `lookup_block u2.vs_current_bb fn.fn_blocks = SOME bb`
    by simp[Abbr `u2`, update_var_def] >>
  `get_instruction bb u2.vs_inst_idx =
     SOME (mk_inst (id+2) MUL [Var x0; Lit (n2w msz)] [x2])`
    by (qpat_x_assum `!i. i < 9 ==> _` (qspec_then `2` mp_tac) >>
        simp[Abbr `u2`, Abbr `u1`, mk_inst_def, arithmeticTheory.ADD1]) >>
  qpat_x_assum `get_instruction bb u1.vs_inst_idx = _` kall_tac >>
  `~is_terminator (mk_inst (id+2) MUL [Var x0; Lit (n2w msz)] [x2]).inst_opcode`
    by simp[mk_inst_def, is_terminator_def] >>
  drule_all run_from_nonterm_stable >> reverse strip_tac
  >- (simp[fuel_outcome_def] >> metis_tac[]) >>
  `?w2. s1 = update_var x2 w2 u2` by
    (qpat_x_assum `step_inst _ _ _ _ = OK _` mp_tac >>
     simp[mk_inst_def, step_inst_non_invoke, step_inst_base_opcode_eqs,
          exec_pure2_def, AllCaseEqs()] >> metis_tac[]) >>
  qpat_x_assum `step_inst _ _ _ _ = OK _` kall_tac >> gvs[] >>
  qabbrev_tac `u3 = update_var x2 w2 u2 with vs_inst_idx := SUC u2.vs_inst_idx` >>
  `fuel_outcome G ctx fn u3 0 post` suffices_by
    (simp[fuel_outcome_def] >> metis_tac[]) >>
  `lookup_block u3.vs_current_bb fn.fn_blocks = SOME bb`
    by simp[Abbr `u3`, update_var_def] >>
  `get_instruction bb u3.vs_inst_idx =
     SOME (mk_inst (id+3) ADD [Var x1; Var x2] [x3])`
    by (qpat_x_assum `!i. i < 9 ==> _` (qspec_then `3` mp_tac) >>
        simp[Abbr `u3`, Abbr `u2`, Abbr `u1`, mk_inst_def, arithmeticTheory.ADD1]) >>
  qpat_x_assum `get_instruction bb u2.vs_inst_idx = _` kall_tac >>
  `~is_terminator (mk_inst (id+3) ADD [Var x1; Var x2] [x3]).inst_opcode`
    by simp[mk_inst_def, is_terminator_def] >>
  drule_all run_from_nonterm_stable >> reverse strip_tac
  >- (simp[fuel_outcome_def] >> metis_tac[]) >>
  `?w3. s1 = update_var x3 w3 u3` by
    (qpat_x_assum `step_inst _ _ _ _ = OK _` mp_tac >>
     simp[mk_inst_def, step_inst_non_invoke, step_inst_base_opcode_eqs,
          exec_pure2_def, AllCaseEqs()] >> metis_tac[]) >>
  qpat_x_assum `step_inst _ _ _ _ = OK _` kall_tac >> gvs[] >>
  qabbrev_tac `u4 = update_var x3 w3 u3 with vs_inst_idx := SUC u3.vs_inst_idx` >>
  `fuel_outcome G ctx fn u4 0 post` suffices_by
    (simp[fuel_outcome_def] >> metis_tac[]) >>
  `lookup_block u4.vs_current_bb fn.fn_blocks = SOME bb`
    by simp[Abbr `u4`, update_var_def] >>
  `get_instruction bb u4.vs_inst_idx =
     SOME (mk_inst (id+4) ADD [dst; Lit 32w] [x4])`
    by (qpat_x_assum `!i. i < 9 ==> _` (qspec_then `4` mp_tac) >>
        simp[Abbr `u4`, Abbr `u3`, Abbr `u2`, Abbr `u1`,
             mk_inst_def, arithmeticTheory.ADD1]) >>
  qpat_x_assum `get_instruction bb u3.vs_inst_idx = _` kall_tac >>
  `~is_terminator (mk_inst (id+4) ADD [dst; Lit 32w] [x4]).inst_opcode`
    by simp[mk_inst_def, is_terminator_def] >>
  drule_all run_from_nonterm_stable >> reverse strip_tac
  >- (simp[fuel_outcome_def] >> metis_tac[]) >>
  `?w4. s1 = update_var x4 w4 u4` by
    (qpat_x_assum `step_inst _ _ _ _ = OK _` mp_tac >>
     simp[mk_inst_def, step_inst_non_invoke, step_inst_base_opcode_eqs,
          exec_pure2_def, AllCaseEqs()] >> metis_tac[]) >>
  qpat_x_assum `step_inst _ _ _ _ = OK _` kall_tac >> gvs[] >>
  qabbrev_tac `u5 = update_var x4 w4 u4 with vs_inst_idx := SUC u4.vs_inst_idx` >>
  `fuel_outcome G ctx fn u5 0 post` suffices_by
    (simp[fuel_outcome_def] >> metis_tac[]) >>
  `lookup_block u5.vs_current_bb fn.fn_blocks = SOME bb`
    by simp[Abbr `u5`, update_var_def] >>
  `get_instruction bb u5.vs_inst_idx =
     SOME (mk_inst (id+5) MUL [Var x0; Lit (n2w asz)] [x5])`
    by (qpat_x_assum `!i. i < 9 ==> _` (qspec_then `5` mp_tac) >>
        simp[Abbr `u5`, Abbr `u4`, Abbr `u3`, Abbr `u2`, Abbr `u1`,
             mk_inst_def, arithmeticTheory.ADD1]) >>
  qpat_x_assum `get_instruction bb u4.vs_inst_idx = _` kall_tac >>
  `~is_terminator (mk_inst (id+5) MUL [Var x0; Lit (n2w asz)] [x5]).inst_opcode`
    by simp[mk_inst_def, is_terminator_def] >>
  drule_all run_from_nonterm_stable >> reverse strip_tac
  >- (simp[fuel_outcome_def] >> metis_tac[]) >>
  `?w5. s1 = update_var x5 w5 u5` by
    (qpat_x_assum `step_inst _ _ _ _ = OK _` mp_tac >>
     simp[mk_inst_def, step_inst_non_invoke, step_inst_base_opcode_eqs,
          exec_pure2_def, AllCaseEqs()] >> metis_tac[]) >>
  qpat_x_assum `step_inst _ _ _ _ = OK _` kall_tac >> gvs[] >>
  qabbrev_tac `u6 = update_var x5 w5 u5 with vs_inst_idx := SUC u5.vs_inst_idx` >>
  `fuel_outcome G ctx fn u6 0 post` suffices_by
    (simp[fuel_outcome_def] >> metis_tac[]) >>
  `lookup_block u6.vs_current_bb fn.fn_blocks = SOME bb`
    by simp[Abbr `u6`, update_var_def] >>
  `get_instruction bb u6.vs_inst_idx =
     SOME (mk_inst (id+6) ADD [Var x4; Var x5] [x6])`
    by (qpat_x_assum `!i. i < 9 ==> _` (qspec_then `6` mp_tac) >>
        simp[Abbr `u6`, Abbr `u5`, Abbr `u4`, Abbr `u3`, Abbr `u2`, Abbr `u1`,
             mk_inst_def, arithmeticTheory.ADD1]) >>
  qpat_x_assum `get_instruction bb u5.vs_inst_idx = _` kall_tac >>
  `~is_terminator (mk_inst (id+6) ADD [Var x4; Var x5] [x6]).inst_opcode`
    by simp[mk_inst_def, is_terminator_def] >>
  drule_all run_from_nonterm_stable >> reverse strip_tac
  >- (simp[fuel_outcome_def] >> metis_tac[]) >>
  `?w6. s1 = update_var x6 w6 u6` by
    (qpat_x_assum `step_inst _ _ _ _ = OK _` mp_tac >>
     simp[mk_inst_def, step_inst_non_invoke, step_inst_base_opcode_eqs,
          exec_pure2_def, AllCaseEqs()] >> metis_tac[]) >>
  qpat_x_assum `step_inst _ _ _ _ = OK _` kall_tac >> gvs[] >>
  qabbrev_tac `u7 = update_var x6 w6 u6 with vs_inst_idx := SUC u6.vs_inst_idx` >>
  `fuel_outcome G ctx fn u7 0 post` suffices_by
    (simp[fuel_outcome_def] >> metis_tac[]) >>
  `lookup_block u7.vs_current_bb fn.fn_blocks = SOME bb`
    by simp[Abbr `u7`, update_var_def] >>
  `get_instruction bb u7.vs_inst_idx = SOME (mk_inst (id+7) MLOAD [dp] [x7])`
    by (qpat_x_assum `!i. i < 9 ==> _` (qspec_then `7` mp_tac) >>
        simp[Abbr `u7`, Abbr `u6`, Abbr `u5`, Abbr `u4`, Abbr `u3`, Abbr `u2`,
             Abbr `u1`, mk_inst_def, arithmeticTheory.ADD1]) >>
  qpat_x_assum `get_instruction bb u6.vs_inst_idx = _` kall_tac >>
  `~is_terminator (mk_inst (id+7) MLOAD [dp] [x7]).inst_opcode`
    by simp[mk_inst_def, is_terminator_def] >>
  drule_all run_from_nonterm_stable >> reverse strip_tac
  >- (simp[fuel_outcome_def] >> metis_tac[]) >>
  `?w7. s1 = update_var x7 w7 u7` by
    (qpat_x_assum `step_inst _ _ _ _ = OK _` mp_tac >>
     simp[mk_inst_def, step_inst_non_invoke, step_inst_base_opcode_eqs,
          exec_read1_def, AllCaseEqs()] >> metis_tac[]) >>
  qpat_x_assum `step_inst _ _ _ _ = OK _` kall_tac >> gvs[] >>
  qabbrev_tac `u8 = update_var x7 w7 u7 with vs_inst_idx := SUC u7.vs_inst_idx` >>
  `fuel_outcome G ctx fn u8 0 post` suffices_by
    (simp[fuel_outcome_def] >> metis_tac[]) >>
  `lookup_block u8.vs_current_bb fn.fn_blocks = SOME bb`
    by simp[Abbr `u8`, update_var_def] >>
  `get_instruction bb u8.vs_inst_idx =
     SOME (mk_inst (id+8) ADD [Var x4; Var x7] [x8])`
    by (qpat_x_assum `!i. i < 9 ==> _` (qspec_then `8` mp_tac) >>
        simp[Abbr `u8`, Abbr `u7`, Abbr `u6`, Abbr `u5`, Abbr `u4`, Abbr `u3`,
             Abbr `u2`, Abbr `u1`, mk_inst_def, arithmeticTheory.ADD1]) >>
  qpat_x_assum `get_instruction bb u7.vs_inst_idx = _` kall_tac >>
  `~is_terminator (mk_inst (id+8) ADD [Var x4; Var x7] [x8]).inst_opcode`
    by simp[mk_inst_def, is_terminator_def] >>
  drule_all run_from_nonterm_stable >> reverse strip_tac
  >- (simp[fuel_outcome_def] >> metis_tac[]) >>
  `?w8. s1 = update_var x8 w8 u8` by
    (qpat_x_assum `step_inst _ _ _ _ = OK _` mp_tac >>
     simp[mk_inst_def, step_inst_non_invoke, step_inst_base_opcode_eqs,
          exec_pure2_def, AllCaseEqs()] >> metis_tac[]) >>
  qpat_x_assum `step_inst _ _ _ _ = OK _` kall_tac >> gvs[] >>
  qabbrev_tac `u9 = update_var x8 w8 u8 with vs_inst_idx := SUC u8.vs_inst_idx` >>
  `fuel_outcome G ctx fn u9 0 post` suffices_by
    (simp[fuel_outcome_def] >> metis_tac[]) >>
  irule fuel_outcome_refl >>
  rpt (qpat_x_assum `!f. G <= f ==> _` kall_tac) >>
  rpt (qpat_x_assum `!x. _ ==> lookup_var x _ = _` kall_tac) >>
  rpt (qpat_x_assum `_.vs_current_bb = _` kall_tac) >>
  rpt (qpat_x_assum `lookup_block _ _ = _` kall_tac) >>
  qpat_x_assum `!i. i < 9 ==> _` kall_tac >>
  qpat_x_assum `get_instruction _ _ = _` kall_tac >>
  simp[Abbr `post`, Abbr `u9`, Abbr `u8`, Abbr `u7`, Abbr `u6`, Abbr `u5`,
       Abbr `u4`, Abbr `u3`, Abbr `u2`, Abbr `u1`, update_var_def,
       lookup_var_def, finite_mapTheory.FLOOKUP_UPDATE, mload_def,
       vars_kept_def] >>
  conj_tac
  >- (rpt strip_tac >>
      `x <> x0 /\ x <> x1 /\ x <> x2 /\ x <> x3 /\ x <> x4 /\
       x <> x5 /\ x <> x6 /\ x <> x7 /\ x <> x8` by metis_tac[] >> simp[]) >>
  Cases_on `ip` >>
  gvs[eval_operand_def, lookup_var_def, finite_mapTheory.FLOOKUP_UPDATE]
QED

(* suffix_semantics: the last store dominates every prior memory write. *)
Theorem abi_encode_dyn_suffix_semantics[local]:
  !id ip i2 hp off cl dp nd ni hdr G ctx fn s bb N a c.
  let code = [mk_inst id MSTORE [hp; off] [];
              mk_inst (id+1) ADD [off; cl] [nd];
              mk_inst (id+2) MSTORE [dp; Var nd] [];
              mk_inst (id+3) ADD [i2; Lit 1w] [ni];
              mk_inst (id+4) MSTORE [ip; Var ni] [];
              mk_inst (id+5) JMP [Label hdr] []]
  in
  no_phi_fn fn /\ callees_stable G ctx fn /\
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  (!i. i < 6 ==> get_instruction bb (s.vs_inst_idx+i) = SOME (EL i code)) /\
  nd <> ni /\
  EVERY (\v. ~var_below N v /\ ip <> Var v /\ i2 <> Var v) [nd;ni] /\
  eval_operand ip s = SOME a /\ eval_operand i2 s = SOME c ==>
  fuel_outcome G ctx fn s 1
    (\t. t.vs_current_bb = hdr /\ t.vs_inst_idx = 0 /\
         vars_kept N {} s t /\ eval_operand ip t = SOME a /\
         mload (w2n a) t = c+1w)
Proof
  rpt gen_tac >> simp_tac std_ss [LET_THM] >> strip_tac >>
  qmatch_goalsub_abbrev_tac `fuel_outcome G ctx fn s 1 post` >>
  `get_instruction bb s.vs_inst_idx = SOME (mk_inst id MSTORE [hp; off] [])`
    by (qpat_x_assum `!i. i < 6 ==> _` (qspec_then `0` mp_tac) >> simp[]) >>
  `~is_terminator (mk_inst id MSTORE [hp; off] []).inst_opcode`
    by simp[mk_inst_def, is_terminator_def] >>
  drule_all run_from_nonterm_stable >> reverse strip_tac
  >- (simp[fuel_outcome_def] >> disj2_tac >> rpt strip_tac >>
      `G <= f+1 /\ G <= G+1` by decide_tac >> metis_tac[]) >>
  gvs[mk_inst_def, step_inst_non_invoke, step_inst_base_opcode_eqs,
      exec_write2_def, AllCaseEqs()] >>
  rename1 `eval_operand hp s = SOME p0` >>
  rename1 `eval_operand off s = SOME v0` >>
  qabbrev_tac `u1 = mstore (w2n p0) v0 s with vs_inst_idx := SUC s.vs_inst_idx` >>
  `fuel_outcome G ctx fn u1 1 post` suffices_by
    (simp[fuel_outcome_def] >>
     `!f. G <= f ==> run_from (f+1) ctx fn s = run_from (f+1) ctx fn u1`
       by (rpt strip_tac >> first_x_assum irule >> decide_tac) >> metis_tac[]) >>
  `lookup_block u1.vs_current_bb fn.fn_blocks = SOME bb`
    by simp[Abbr `u1`, mstore_def] >>
  `get_instruction bb u1.vs_inst_idx =
     SOME (mk_inst (id+1) ADD [off; cl] [nd])`
    by (qpat_x_assum `!i. i < 6 ==> _` (qspec_then `1` mp_tac) >>
        simp[Abbr `u1`, mk_inst_def, arithmeticTheory.ADD1]) >>
  qpat_x_assum `get_instruction bb s.vs_inst_idx = _` kall_tac >>
  `~is_terminator (mk_inst (id+1) ADD [off; cl] [nd]).inst_opcode`
    by simp[mk_inst_def, is_terminator_def] >>
  drule_all run_from_nonterm_stable >> reverse strip_tac
  >- (simp[fuel_outcome_def] >> disj2_tac >> rpt strip_tac >>
      `G <= f+1 /\ G <= G+1` by decide_tac >> metis_tac[]) >>
  `?w1. s1 = update_var nd w1 u1` by
    (qpat_x_assum `step_inst _ _ _ _ = OK _` mp_tac >>
     simp[mk_inst_def, step_inst_non_invoke, step_inst_base_opcode_eqs,
          exec_pure2_def, AllCaseEqs()] >> metis_tac[]) >>
  qpat_x_assum `step_inst _ _ _ _ = OK _` kall_tac >> gvs[] >>
  qabbrev_tac `u2 = update_var nd w1 u1 with vs_inst_idx := SUC u1.vs_inst_idx` >>
  `fuel_outcome G ctx fn u2 1 post` suffices_by
    (simp[fuel_outcome_def] >>
     `!f. G <= f ==> run_from (f+1) ctx fn u1 = run_from (f+1) ctx fn u2`
       by (rpt strip_tac >> first_x_assum irule >> decide_tac) >> metis_tac[]) >>
  `lookup_block u2.vs_current_bb fn.fn_blocks = SOME bb`
    by simp[Abbr `u2`, update_var_def] >>
  `get_instruction bb u2.vs_inst_idx =
     SOME (mk_inst (id+2) MSTORE [dp; Var nd] [])`
    by (qpat_x_assum `!i. i < 6 ==> _` (qspec_then `2` mp_tac) >>
        simp[Abbr `u2`, Abbr `u1`, mk_inst_def, arithmeticTheory.ADD1]) >>
  qpat_x_assum `get_instruction bb u1.vs_inst_idx = _` kall_tac >>
  `~is_terminator (mk_inst (id+2) MSTORE [dp; Var nd] []).inst_opcode`
    by simp[mk_inst_def, is_terminator_def] >>
  drule_all run_from_nonterm_stable >> reverse strip_tac
  >- (simp[fuel_outcome_def] >> disj2_tac >> rpt strip_tac >>
      `G <= f+1 /\ G <= G+1` by decide_tac >> metis_tac[]) >>
  gvs[mk_inst_def, step_inst_non_invoke, step_inst_base_opcode_eqs,
      exec_write2_def, AllCaseEqs()] >>
  rename1 `eval_operand dp u2 = SOME p2` >>
  rename1 `eval_operand (Var nd) u2 = SOME v2` >>
  qabbrev_tac `u3 = mstore (w2n p2) v2 u2 with vs_inst_idx := SUC u2.vs_inst_idx` >>
  `fuel_outcome G ctx fn u3 1 post` suffices_by
    (simp[fuel_outcome_def] >>
     `!f. G <= f ==> run_from (f+1) ctx fn u2 = run_from (f+1) ctx fn u3`
       by (rpt strip_tac >> first_x_assum irule >> decide_tac) >> metis_tac[]) >>
  `eval_operand i2 u3 = SOME c` by
    (rpt (qpat_x_assum `!f. G <= f ==> _` kall_tac) >>
     qpat_x_assum `eval_operand i2 s = SOME c` mp_tac >>
     Cases_on `i2` >>
     asm_simp_tac (srw_ss()) [Abbr `u3`, Abbr `u2`, Abbr `u1`, eval_operand_def,
               mstore_vars, update_var_def, lookup_var_def, finite_mapTheory.FLOOKUP_UPDATE] >>
     gvs[]) >>
  `lookup_block u3.vs_current_bb fn.fn_blocks = SOME bb`
    by simp[Abbr `u3`, mstore_def] >>
  `get_instruction bb u3.vs_inst_idx =
     SOME (mk_inst (id+3) ADD [i2; Lit 1w] [ni])`
    by (qpat_x_assum `!i. i < 6 ==> _` (qspec_then `3` mp_tac) >>
        simp[Abbr `u3`, Abbr `u2`, Abbr `u1`, mk_inst_def, arithmeticTheory.ADD1]) >>
  qpat_x_assum `get_instruction bb u2.vs_inst_idx = _` kall_tac >>
  `~is_terminator (mk_inst (id+3) ADD [i2; Lit 1w] [ni]).inst_opcode`
    by simp[mk_inst_def, is_terminator_def] >>
  drule_all run_from_nonterm_stable >> reverse strip_tac
  >- (simp[fuel_outcome_def] >> disj2_tac >> rpt strip_tac >>
      `G <= f+1 /\ G <= G+1` by decide_tac >> metis_tac[]) >>
  gvs[mk_inst_def, step_inst_non_invoke, step_inst_base_opcode_eqs,
      exec_pure2_def, eval_operand_def] >>
  qabbrev_tac `u4 = update_var ni (c+1w) u3 with vs_inst_idx := SUC u3.vs_inst_idx` >>
  `fuel_outcome G ctx fn u4 1 post` suffices_by
    (simp[fuel_outcome_def] >>
     `!f. G <= f ==> run_from (f+1) ctx fn u3 = run_from (f+1) ctx fn u4`
       by (rpt strip_tac >> first_x_assum irule >> decide_tac) >> metis_tac[]) >>
  `eval_operand ip u4 = SOME a` by
    (rpt (qpat_x_assum `!f. G <= f ==> _` kall_tac) >>
     qpat_x_assum `eval_operand ip s = SOME a` mp_tac >>
     Cases_on `ip` >>
     asm_simp_tac (srw_ss()) [Abbr `u4`, Abbr `u3`, Abbr `u2`, Abbr `u1`, eval_operand_def,
          mstore_vars, update_var_def, lookup_var_def, finite_mapTheory.FLOOKUP_UPDATE] >> gvs[]) >>
  `eval_operand (Var ni) u4 = SOME (c+1w)`
    by simp[Abbr `u4`, eval_operand_def, update_var_def, lookup_var_def,
            finite_mapTheory.FLOOKUP_UPDATE] >>
  `lookup_block u4.vs_current_bb fn.fn_blocks = SOME bb`
    by simp[Abbr `u4`, update_var_def] >>
  `get_instruction bb u4.vs_inst_idx =
     SOME (mk_inst (id+4) MSTORE [ip; Var ni] [])`
    by (qpat_x_assum `!i. i < 6 ==> _` (qspec_then `4` mp_tac) >>
        simp[Abbr `u4`, Abbr `u3`, Abbr `u2`, Abbr `u1`, mk_inst_def,
             arithmeticTheory.ADD1]) >>
  qpat_x_assum `get_instruction bb u3.vs_inst_idx = _` kall_tac >>
  `~is_terminator (mk_inst (id+4) MSTORE [ip; Var ni] []).inst_opcode`
    by simp[mk_inst_def, is_terminator_def] >>
  drule_all run_from_nonterm_stable >> reverse strip_tac
  >- (simp[fuel_outcome_def] >> disj2_tac >> rpt strip_tac >>
      `G <= f+1 /\ G <= G+1` by decide_tac >> metis_tac[]) >>
  gvs[mk_inst_def, step_inst_non_invoke, step_inst_base_opcode_eqs,
      exec_write2_def] >>
  qabbrev_tac `u5 = mstore (w2n a) (c+1w) u4 with vs_inst_idx := SUC u4.vs_inst_idx` >>
  `fuel_outcome G ctx fn u5 1 post` suffices_by
    (simp[fuel_outcome_def] >>
     `!f. G <= f ==> run_from (f+1) ctx fn u4 = run_from (f+1) ctx fn u5`
       by (rpt strip_tac >> first_x_assum irule >> decide_tac) >> metis_tac[]) >>
  `lookup_block u5.vs_current_bb fn.fn_blocks = SOME bb`
    by simp[Abbr `u5`, mstore_def] >>
  `get_instruction bb u5.vs_inst_idx = SOME (mk_inst (id+5) JMP [Label hdr] [])`
    by (qpat_x_assum `!i. i < 6 ==> _` (qspec_then `5` mp_tac) >>
        simp[Abbr `u5`, Abbr `u4`, Abbr `u3`, Abbr `u2`, Abbr `u1`,
             mk_inst_def, arithmeticTheory.ADD1]) >>
  irule fuel_outcome_jump >> conj_tac >- simp[] >>
  qexistsl_tac [`bb`, `mk_inst (id+5) JMP [Label hdr] []`, `hdr`] >>
  simp[mk_inst_def, is_terminator_def, step_inst_base_opcode_eqs] >>
  strip_tac >>
  rpt (qpat_x_assum `!f. G <= f ==> _` kall_tac) >>
  rpt (qpat_x_assum `!x. _ ==> lookup_var x _ = _` kall_tac) >>
  rpt (qpat_x_assum `!x. lookup_var x _ = _` kall_tac) >>
  rpt (qpat_x_assum `_.vs_current_bb = _` kall_tac) >>
  rpt (qpat_x_assum `lookup_block _ _ = _` kall_tac) >>
  qpat_x_assum `!i. i < 6 ==> _` kall_tac >>
  rpt (qpat_x_assum `get_instruction _ _ = _` kall_tac) >>
  simp[Abbr `post`, jump_to_def] >>
  conj_tac
  >- (simp[vars_kept_def, Abbr `u5`, Abbr `u4`, Abbr `u3`, Abbr `u2`, Abbr `u1`,
           lookup_var_def, mstore_vars, update_var_def, finite_mapTheory.FLOOKUP_UPDATE] >>
      rpt strip_tac >> `x <> nd /\ x <> ni` by metis_tac[] >> simp[]) >>
  reverse conj_tac
  >- (`mload (w2n a)
         (u5 with <|vs_prev_bb := SOME u5.vs_current_bb; vs_current_bb := hdr; vs_inst_idx := 0|>) =
       mload (w2n a) (mstore (w2n a) (c+1w) u4)`
        by simp[Abbr `u5`, mload_def] >>
      asm_rewrite_tac[mload_mstore_same]) >>
  qpat_x_assum `eval_operand ip u4 = SOME a` mp_tac >>
  Cases_on `ip` >>
  simp[Abbr `u5`, eval_operand_def, lookup_var_def, mstore_vars]
QED

(* round_semantics: the child's frame is used at its own allocation frontier. *)
Theorem abi_encode_dyn_child_transport[local]:
  !ca cb K fn G ctx s N p q a c.
  frag_fuel {} {} {} ca cb K /\ fn_has_code ca cb fn /\
  no_phi_fn fn /\ callees_stable G ctx fn /\ at_point ca s /\
  N <= ca.cs_next_var /\
  eval_operand (Var p) s = SOME a /\ eval_operand (Var q) s = SOME c /\
  var_below ca.cs_next_var p /\ var_below ca.cs_next_var q ==>
  ?j. j <= K /\ fuel_outcome G ctx fn s j
    (\t. at_point cb t /\ vars_kept N {} s t /\
         eval_operand (Var p) t = SOME a /\ eval_operand (Var q) t = SOME c)
Proof
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `frag_fuel _ _ _ _ _ _` mp_tac >>
  rewrite_tac[frag_fuel_def] >>
  disch_then (qspecl_then [`G`, `ca.cs_next_var`, `ctx`, `fn`, `s`] mp_tac) >>
  simp[] >> strip_tac >> qexists_tac `j` >> simp[] >>
  irule fuel_outcome_weaken >> goal_assum (drule_at Any) >>
  simp[] >> rpt strip_tac
  >- (fs[vars_kept_def] >> rpt strip_tac >> first_x_assum irule >>
      fs[var_below_def] >> metis_tac[arithmeticTheory.LESS_EQ_TRANS])
  >> gvs[eval_operand_def, vars_kept_def]
QED

Theorem abi_encode_dyn_round_core[local]:
  !G ctx fn H Q (B:bytes32 -> bytes32 -> venom_state -> bool) P R
   (counter:venom_state -> bytes32) Kb.
  (!s. H s ==> fuel_outcome G ctx fn s 1
     (\t. Q t \/ ?a c. B a c t /\ c = counter s /\ w2n c < 2**256-1)) /\
  (!a c s. B a c s ==> fuel_outcome G ctx fn s 0 (P a c)) /\
  (!a c s. P a c s ==> ?j. j <= Kb /\ fuel_outcome G ctx fn s j (R a c)) /\
  (!a c s. R a c s ==> fuel_outcome G ctx fn s 1
     (\t. H t /\ counter t = c+1w)) ==>
  !s. H s ==> ?j. j <= Kb+2 /\ fuel_outcome G ctx fn s j
    (\t. Q t \/ (H t /\ 2**256-1-w2n (counter t) < 2**256-1-w2n (counter s)))
Proof
  rpt gen_tac >> strip_tac >> rpt gen_tac >> strip_tac >>
  qmatch_goalsub_abbrev_tac `?j. j <= Kb+2 /\ fuel_outcome G ctx fn s j result` >>
  `1+(Kb+1) = Kb+2` by decide_tac >>
  pop_assum (fn th => PURE_ONCE_REWRITE_TAC [GSYM th]) >>
  qpat_x_assum `!s. H s ==> _` drule >> strip_tac >>
  irule fuel_outcome_compose >> goal_assum (drule_at Any) >>
  rpt gen_tac >> BETA_TAC >> strip_tac
  >- (qexists_tac `0` >> simp[] >> irule fuel_outcome_refl >> simp[Abbr `result`]) >>
  rename1 `B a c t` >>
  qpat_x_assum `!a c s. B a c s ==> _` drule >> strip_tac >>
  `0+(Kb+1) = Kb+1` by simp[] >>
  pop_assum (fn th => PURE_ONCE_REWRITE_TAC [GSYM th]) >>
  irule fuel_outcome_compose >> goal_assum (drule_at Any) >>
  rpt gen_tac >> BETA_TAC >> strip_tac >>
  qpat_x_assum `!a c s. P a c s ==> _` drule >> strip_tac >>
  `?jj. jj <= j+1 /\ fuel_outcome G ctx fn t' jj result` suffices_by
    (strip_tac >> qexists_tac `jj` >> simp[] >> decide_tac) >>
  irule fuel_outcome_compose >> goal_assum (drule_at Any) >>
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `!a c s. R a c s ==> _` drule >> strip_tac >>
  qexists_tac `1` >> simp[] >>
  irule fuel_outcome_weaken >> goal_assum (drule_at Any) >>
  rpt gen_tac >> BETA_TAC >> strip_tac >>
  `w2n (c+1w) = w2n c + 1` by
    (gvs[wordsTheory.dimword_def, GEN_ALL wordsTheory.w2n_add_2]) >>
  simp[Abbr `result`] >> disj2_tac >> gvs[]
QED

Theorem abi_encode_dyn_round_semantics[local]:
  !hi pid si p hx hy hz x0 x1 x2 x3 x4 x5 x6 x7 x8 nd ni
   len_op src dst dp cl msz asz hdr body exit ca cb Kb G ctx fn hb pb sb N origin.
  let ip = Var p;
      outputs = [x0;x1;x2;x3;x4;x5;x6;x7;x8];
      hcode = [mk_inst hi MLOAD [ip] [hx];
               mk_inst (hi+1) LT [Var hx; len_op] [hy];
               mk_inst (hi+2) ISZERO [Var hy] [hz];
               mk_inst (hi+3) JNZ [Var hz; Label exit; Label body] []];
      pcode = [mk_inst pid MLOAD [ip] [x0];
               mk_inst (pid+1) ADD [src; Lit 32w] [x1];
               mk_inst (pid+2) MUL [Var x0; Lit (n2w msz)] [x2];
               mk_inst (pid+3) ADD [Var x1; Var x2] [x3];
               mk_inst (pid+4) ADD [dst; Lit 32w] [x4];
               mk_inst (pid+5) MUL [Var x0; Lit (n2w asz)] [x5];
               mk_inst (pid+6) ADD [Var x4; Var x5] [x6];
               mk_inst (pid+7) MLOAD [dp] [x7];
               mk_inst (pid+8) ADD [Var x4; Var x7] [x8]];
      scode = [mk_inst si MSTORE [Var x6; Var x7] [];
               mk_inst (si+1) ADD [Var x7; cl] [nd];
               mk_inst (si+2) MSTORE [dp; Var nd] [];
               mk_inst (si+3) ADD [Var x0; Lit 1w] [ni];
               mk_inst (si+4) MSTORE [ip; Var ni] [];
               mk_inst (si+5) JMP [Label hdr] []]
  in
  no_phi_fn fn /\ callees_stable G ctx fn /\
  lookup_block hdr fn.fn_blocks = SOME hb /\
  (!i. i < 4 ==> get_instruction hb i = SOME (EL i hcode)) /\
  ALL_DISTINCT [hx;hy;hz] /\
  EVERY (\v. ~var_below N v /\ ip <> Var v /\ len_op <> Var v) [hx;hy;hz] /\
  lookup_block body fn.fn_blocks = SOME pb /\
  (!i. i < 9 ==> get_instruction pb i = SOME (EL i pcode)) /\
  ALL_DISTINCT outputs /\ EVERY (\v. ~var_below N v /\ ip <> Var v) outputs /\
  ca.cs_current_bb = body /\ LENGTH ca.cs_current_insts = 9 /\
  frag_fuel {} {} {} ca cb Kb /\ fn_has_code ca cb fn /\
  N <= ca.cs_next_var /\ var_below ca.cs_next_var p /\ var_below ca.cs_next_var x0 /\
  lookup_block cb.cs_current_bb fn.fn_blocks = SOME sb /\
  (!i. i < 6 ==> get_instruction sb (LENGTH cb.cs_current_insts+i) = SOME (EL i scode)) /\
  nd <> ni /\ EVERY (\v. ~var_below N v /\ ip <> Var v /\ Var x0 <> Var v) [nd;ni] ==>
  let counter = (\s. mload (w2n (THE (eval_operand ip s))) s);
      H = (\s. s.vs_current_bb = hdr /\ s.vs_inst_idx = 0 /\ vars_kept N {} origin s);
      Q = (\s. s.vs_current_bb = exit /\ s.vs_inst_idx = 0 /\ vars_kept N {} origin s)
  in
  (!s. 2**256-1-w2n (counter s) < 2**256) /\
  !s. H s ==> ?j. j <= Kb+2 /\ fuel_outcome G ctx fn s j
    (\t. Q t \/ (H t /\ 2**256-1-w2n (counter t) < 2**256-1-w2n (counter s)))
Proof
  rpt gen_tac >> pure_rewrite_tac [LET_THM] >> BETA_TAC >> strip_tac >>
  BETA_TAC >> conj_tac >- simp[] >>
  ho_match_mp_tac abi_encode_dyn_round_core >>
  qexistsl_tac
    [`\a c s. s.vs_current_bb = ca.cs_current_bb /\ s.vs_inst_idx = 0 /\
        vars_kept N {} origin s /\ eval_operand (Var p) s = SOME a /\ mload (w2n a) s = c`,
     `\a c s. at_point ca s /\ vars_kept N {} origin s /\
        eval_operand (Var p) s = SOME a /\ eval_operand (Var x0) s = SOME c`,
     `\a c s. at_point cb s /\ vars_kept N {} origin s /\
        eval_operand (Var p) s = SOME a /\ eval_operand (Var x0) s = SOME c`] >>
  BETA_TAC >> conj_tac
  >- (rpt gen_tac >> strip_tac >>
      irule fuel_outcome_weaken >>
      irule_at Any (BETA_RULE (PURE_REWRITE_RULE [LET_THM] abi_encode_dyn_header_semantics)) >>
      qexistsl_tac [`hz`,`hy`,`hx`,`len_op`,`Var p`,`hi`,`exit`,`ca.cs_current_bb`,`hb`,`N`] >>
      asm_simp_tac bool_ss [] >>
      ntac 4 (conj_tac >- (pure_rewrite_tac [arithmeticTheory.ADD] >> first_x_assum irule >> simp[])) >>
      rpt strip_tac >>
      `vars_kept N {} origin t` by metis_tac [vars_kept_trans] >>
      simp[] >>
      mp_tac (Q.ISPEC `b:bytes32` wordsTheory.w2n_lt) >>
      simp[wordsTheory.dimword_def] ) >>
  conj_tac
  >- (rpt gen_tac >> strip_tac >>
      irule fuel_outcome_weaken >>
      irule_at Any (BETA_RULE (PURE_REWRITE_RULE [LET_THM] abi_encode_dyn_prefix_semantics)) >>
      goal_assum (drule_at Any) >>
      asm_simp_tac bool_ss [arithmeticTheory.ADD] >>
      goal_assum (drule_at Any) >>
      qexistsl_tac [`src`,`msz`,`pid`,`dst`,`dp`,`pb`,`asz`] >>
      asm_simp_tac bool_ss [] >> rpt strip_tac >>
      simp[at_point_def] >> metis_tac[vars_kept_trans]) >>
  conj_tac
  >- (rpt gen_tac >> strip_tac >>
      `?j. j <= Kb /\ fuel_outcome G ctx fn s j
        (\t. at_point cb t /\ vars_kept N {} s t /\
             eval_operand (Var p) t = SOME a /\ eval_operand (Var x0) t = SOME c)`
        by (irule abi_encode_dyn_child_transport >> simp[] >> qexists_tac `ca` >> simp[]) >>
      qexists_tac `j` >> simp[] >>
      irule fuel_outcome_weaken >> goal_assum (drule_at Any) >>
      BETA_TAC >> rpt strip_tac >> simp[] >> metis_tac[vars_kept_trans]) >>
  rpt gen_tac >> strip_tac >>
  irule fuel_outcome_weaken >>
  irule_at Any (BETA_RULE (PURE_REWRITE_RULE [LET_THM] abi_encode_dyn_suffix_semantics)) >>
  qpat_assum `EVERY _ [nd;ni]` (irule_at Any) >>
  asm_simp_tac bool_ss [at_point_def] >>
  qpat_x_assum `at_point cb s` mp_tac >>
  pure_rewrite_tac [at_point_def] >> strip_tac >>
  asm_simp_tac bool_ss [] >>
  qexistsl_tac [`Var x7`,`si`,`Var x6`,`hdr`,`dp`,`cl`,`c`,`sb`,`a`] >>
  asm_simp_tac bool_ss [] >> rpt strip_tac >>
  simp[] >> metis_tac[vars_kept_trans]
QED

Theorem abi_encode_dyn_middle_fuel[local]:
  !st sh ca cb se ip dp hdr body exit i2 hp off cd cs cl dst src ei asz msz len_op.
  (!d s Wv E. fuel_ok Wv {} E (compile_abi_encode_to_buf d s ei)) /\
  (!x. len_op = Var x ==> var_below st.cs_next_var x) /\
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
   od) st = ((ip,dp,hdr,body,exit),sh) /\
  (do (do i <- emit_op MLOAD [ip];
          cmp <- emit_op LT [i; len_op];
          done <- emit_op ISZERO [cmp];
          emit_inst JNZ [done; Label exit; Label body] [];
          new_block body
       od);
      i2 <- emit_op MLOAD [ip];
      sd <- emit_op ADD [src; Lit 32w];
      so <- emit_op MUL [i2; Lit (n2w msz)];
      cs <- emit_op ADD [sd; so];
      dd <- emit_op ADD [dst; Lit 32w];
      ho <- emit_op MUL [i2; Lit (n2w asz)];
      hp <- emit_op ADD [dd; ho];
      off <- emit_op MLOAD [dp];
      cd <- emit_op ADD [dd; off];
      return (i2,hp,off,cd,cs)
   od) sh = ((i2,hp,off,cd,cs),ca) /\
  compile_abi_encode_to_buf cd cs ei ca = (cl,cb) /\
  (do emit_void MSTORE [hp; off];
      nd <- emit_op ADD [off; cl];
      emit_void MSTORE [dp; nd];
      ni <- emit_op ADD [i2; Lit 1w];
      emit_void MSTORE [ip; ni];
      emit_inst JMP [Label hdr] [];
      new_block exit
   od) cb = (cb.cs_current_bb,se)
  ==> ?Kmid. frag_fuel {} {} {} sh se Kmid
Proof
  rpt gen_tac >> strip_tac >>
  `fuel_ok {} {} {} (compile_abi_encode_to_buf cd cs ei)` by simp[] >>
  pop_assum mp_tac >> rewrite_tac[fuel_ok_def] >>
  disch_then drule >> strip_tac >>
  qpat_x_assum `!d s Wv E. _` kall_tac >>
  qpat_x_assum `do ia <- _; _ od st = _` mp_tac >>
  simp[LET_THM, compile_alloc_buffer_def, emit_op_def, emit_void_def,
       emit_inst_def, fresh_id_def, fresh_var_def, fresh_label_def,
       emit_def, new_block_def, comp_bind_def, comp_ignore_bind_def,
       comp_return_def] >>
  strip_tac >>
  `sh.cs_current_bb = hdr /\ sh.cs_current_insts = [] /\
   sh.cs_next_var = st.cs_next_var+3 /\ sh.cs_next_id = st.cs_next_id+6`
    by gvs[] >>
  qpat_x_assum `_ with <|cs_next_var := _; cs_next_label := _; cs_next_id := _;
    cs_current_bb := _; cs_current_insts := _; cs_blocks := _|> = sh` kall_tac >>
  qpat_x_assum `Var _ = ip` (SUBST_ALL_TAC o SYM) >>
  qpat_x_assum `Var _ = dp` (SUBST_ALL_TAC o SYM) >>
  qpat_x_assum `do do i <- _; _ od; _ od sh = _` mp_tac >>
  simp[LET_THM, emit_op_def, emit_inst_def, fresh_id_def, fresh_var_def,
       emit_def, new_block_def, comp_bind_def, comp_ignore_bind_def,
       comp_return_def] >> strip_tac >>
  `ca.cs_current_bb = body' /\ LENGTH ca.cs_current_insts = 9 /\
   ca.cs_next_var = st.cs_next_var+15 /\ cs_extends sh ca`
    by (gvs[] >> simp[cs_extends_def]) >>
  qpat_x_assum `do emit_void _ _; _ od cb = _` mp_tac >>
  simp[LET_THM, emit_op_def, emit_void_def, emit_inst_def,
       fresh_id_def, fresh_var_def, emit_def, new_block_def,
       comp_bind_def, comp_ignore_bind_def, comp_return_def] >> strip_tac >>
  `se.cs_current_bb = exit /\ se.cs_current_insts = [] /\ cs_extends cb se`
    by (gvs[] >> simp[cs_extends_def]) >>
  qexists_tac `2**256*(Kb+2)` >>
  pure_rewrite_tac [frag_fuel_def, pred_setTheory.NOT_IN_EMPTY,
             boolTheory.OR_CLAUSES, boolTheory.AND_CLAUSES] >>
  rpt gen_tac >> strip_tac >>
  `fn_has_code sh ca fn /\ fn_has_code ca cb fn /\ fn_has_code cb se fn`
    by metis_tac[fragExecTheory.fn_has_code_split, cs_extends_trans] >>
  qmatch_asmsub_abbrev_tac `sh with <|cs_next_var := _; cs_next_id := _;
    cs_current_bb := _; cs_current_insts := pcode; cs_blocks := hb::sh.cs_blocks|> = ca` >>
  qmatch_asmsub_abbrev_tac `cb with <|cs_next_var := _; cs_next_id := _;
    cs_current_bb := _; cs_current_insts := []; cs_blocks := sb::cb.cs_blocks|> = se` >>
  `lookup_block hdr fn.fn_blocks = SOME hb`
    by (qpat_x_assum `fn_has_code sh ca fn` mp_tac >>
        qpat_x_assum `_ with <|cs_next_var := _; cs_next_id := _;
          cs_current_bb := _; cs_current_insts := _; cs_blocks := _|> = ca`
          (SUBST1_TAC o SYM) >>
        simp[fragExecTheory.fn_has_code_def, fragExecTheory.emitted_blocks_def,
             Abbr `hb`]) >>
  `lookup_block cb.cs_current_bb fn.fn_blocks = SOME sb`
    by (qpat_x_assum `fn_has_code cb se fn` mp_tac >>
        qpat_x_assum `_ with <|cs_next_var := _; cs_next_id := _;
          cs_current_bb := _; cs_current_insts := _; cs_blocks := _|> = se`
          (SUBST1_TAC o SYM) >>
        simp[fragExecTheory.fn_has_code_def, fragExecTheory.emitted_blocks_def,
             Abbr `sb`]) >>
  `?pb. lookup_block body' fn.fn_blocks = SOME pb /\
        isPREFIX pcode pb.bb_instructions`
    by (mp_tac (Q.SPECL [`ca`,`cb`,`fn`] fragExecTheory.fn_has_code_start) >>
        (impl_tac >- simp[]) >>
        qpat_x_assum `_ with <|cs_next_var := _; cs_next_id := _;
          cs_current_bb := _; cs_current_insts := _; cs_blocks := _|> = ca`
          (SUBST1_TAC o SYM) >> simp[]) >>
  pop_assum strip_assume_tac >>
  `!i. i < 4 ==> get_instruction hb i = SOME (EL i hb.bb_instructions)`
    by simp[Abbr `hb`, get_instruction_def] >>
  `!i. i < 9 ==> get_instruction pb i = SOME (EL i pcode)`
    by (gvs[rich_listTheory.IS_PREFIX_APPEND, get_instruction_def] >>
        simp[rich_listTheory.EL_APPEND1, Abbr `pcode`]) >>
  qpat_x_assum `Abbrev (sb = _)` mp_tac >>
  pure_rewrite_tac [GSYM listTheory.APPEND_ASSOC, listTheory.APPEND] >> disch_tac >>
  qmatch_asmsub_abbrev_tac `sb = <|bb_label := _;
    bb_instructions := cb.cs_current_insts ++ scode|>` >>
  `!i. i < 6 ==> get_instruction sb (LENGTH cb.cs_current_insts+i) = SOME (EL i scode)`
    by (simp[Abbr `sb`, Abbr `scode`, get_instruction_def,
             GSYM listTheory.APPEND_ASSOC, rich_listTheory.EL_APPEND2]) >>
  (fn g as (asl,_) => let
    val asms = map ASSUME asl
    fun abbrev name = List.find (fn th =>
      can (fn t => if fst (dest_var (lhs (rand t))) = name then ()
                  else raise Fail "name") (concl th)) asms
    val operands = List.filter (fn th => can (fn t =>
      if fst (dest_const (rator (lhs t))) = "Var" andalso is_var (rhs t)
      then () else raise Fail "operand") (concl th)) asms
    val defs = map GSYM operands @
      map (REWRITE_RULE [markerTheory.Abbrev_def] o valOf o abbrev)
                   ["hb","pcode","scode"]
    fun range n = valOf (List.find (fn th =>
      can (fn t => if numSyntax.int_of_term (rand (fst (dest_imp
           (snd (dest_forall t)))) ) = n then () else raise Fail "range")
        (concl th)) asms)
    fun fact r i = CONV_RULE
      (RHS_CONV (SIMP_CONV (srw_ss()) defs))
      (SRULE [] (SPEC (numSyntax.term_of_int i) r))
    val round = CONV_RULE
      (REDEPTH_CONV (numLib.BOUNDED_FORALL_CONV (SIMP_CONV (srw_ss()) [])))
      (BETA_RULE (PURE_REWRITE_RULE [LET_THM] abi_encode_dyn_round_semantics))
    fun phase n last = List.tabulate (n, fn i => (last-i, fact (range n) i))
    fun specialize ((pos,f),th) = let
      val normalized = CONV_RULE (DEPTH_CONV (fn t =>
        if numSyntax.is_plus t andalso numSyntax.is_numeral (rand t)
           andalso numSyntax.is_numeral (rand (rator t))
        then numLib.REDUCE_CONV t else NO_CONV t))
        (PURE_REWRITE_RULE [GSYM arithmeticTheory.ADD_ASSOC] th)
      fun select t = el pos (strip_conj (fst (dest_imp t)))
    in
      PART_MATCH select normalized (concl f)
    end
    val facts = phase 4 7 @ phase 9 20 @ phase 6 37
    val specialized = List.foldl specialize round facts
  in
    mp_tac (Q.INST [`origin` |-> `s`]
      (SRULE (map snd facts) specialized)) g
  end) >>
  (impl_tac >- (
    `!n. st.cs_next_var <= n ==>
      len_op <> Var (STRING #"%" (toString n))`
      by metis_tac[var_below_fresh] >>
    simp[var_below_def, ASCIInumbersTheory.toString_inj] >>
    rpt strip_tac >> gvs[] >> decide_tac)) >>
  strip_tac >>
  simp[at_point_def] >>
  irule fuel_outcome_iterate >>
  qexistsl_tac
    [`\t. t.vs_current_bb = hdr /\ t.vs_inst_idx = 0 /\ vars_kept N {} s t`,
     `\t. 2**256-1-w2n (mload (w2n (THE (eval_operand
          (Var (STRING #"%" (toString st.cs_next_var))) t))) t)`] >>
  BETA_TAC >>
  conj_tac >- (fs[at_point_def] >> simp[vars_kept_refl]) >>
  reverse conj_tac >- simp[] >>
  rpt strip_tac >>
  qpat_x_assum `!t. _ ==> ?j. _` drule >>
  (impl_tac >- simp[]) >>
  disch_then (qx_choose_then `j` strip_assume_tac) >>
  qexists_tac `j` >> simp[] >>
  irule fuel_outcome_weaken >> goal_assum (drule_at Any) >>
  simp[] >> metis_tac[]
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
  rpt gen_tac >> strip_tac >> rpt gen_tac >>
  rewrite_tac[fuel_okS_def] >> rpt gen_tac >> strip_tac >>
  drule abi_encode_dyn_loop_open_exits >>
  rewrite_tac[fuel_ok_def] >> disch_then drule >> strip_tac >>
  asm_simp_tac bool_ss [] >>
  qpat_x_assum `compile_abi_encode_dyn_loop _ _ _ _ _ _ st = _` mp_tac >>
  rewrite_tac[abi_encode_dyn_loop_layout] >>
  qmatch_goalsub_abbrev_tac `comp_bind setup rest st` >>
  Cases_on `setup st` >> rename1 `setup st = (p,sh)` >>
  PairCases_on `p` >>
  asm_simp_tac std_ss [Once comp_bind_def, LET_THM, Abbr `rest`] >>
  rewrite_tac[comp_ignore_bind_def, GSYM comp_bind_assoc] >>
  qmatch_goalsub_abbrev_tac `comp_bind header hrest sh` >>
  Cases_on `header sh` >> rename1 `header sh = (hr,sp)` >>
  asm_simp_tac std_ss [Once comp_bind_def, LET_THM, Abbr `hrest`] >>
  qmatch_goalsub_abbrev_tac `comp_bind prefix prest sp` >>
  Cases_on `prefix sp` >> rename1 `prefix sp = (pr,ca)` >>
  PairCases_on `pr` >>
  asm_simp_tac std_ss [Once comp_bind_def, LET_THM, Abbr `prest`] >>
  Cases_on `compile_abi_encode_to_buf pr3 pr4 elem_info ca` >>
  rename1 `compile_abi_encode_to_buf pr3 pr4 elem_info ca = (cl,cb)` >>
  asm_simp_tac std_ss [Once comp_bind_def, LET_THM] >>
  qmatch_goalsub_abbrev_tac `comp_bind suffix erest cb` >>
  Cases_on `suffix cb` >> rename1 `suffix cb = (sr,se)` >>
  asm_simp_tac std_ss [Once comp_bind_def, LET_THM, Abbr `erest`] >>
  strip_tac >>
  `fuel_ok {} {} {} setup` by simp[Abbr `setup`, abi_encode_dyn_setup_fuel] >>
  `fuel_ok {} {} {p4;p3} header` by (simp_tac bool_ss [Abbr `header`, GSYM comp_ignore_bind_def] >>
     irule abi_encode_dyn_header_fuel) >>
  `fuel_ok {} {} {} prefix` by simp[Abbr `prefix`, abi_encode_dyn_body_prefix_fuel] >>
  `fuel_ok {} {} {p2} suffix` by (simp_tac bool_ss [Abbr `suffix`, GSYM comp_ignore_bind_def] >>
     irule abi_encode_dyn_body_suffix_fuel) >>
  `fuel_ok {} {} {} (compile_abi_encode_to_buf pr3 pr4 elem_info)` by simp[] >>
  `sr = cb.cs_current_bb` by
    (qpat_x_assum `suffix cb = _` mp_tac >>
     simp[Abbr `suffix`, emit_void_def, emit_op_def, emit_inst_def,
          fresh_id_def, fresh_var_def, emit_def, new_block_def,
          comp_bind_def, comp_ignore_bind_def, comp_return_def]) >>
  gvs[] >>
  `comp_ignore_bind header prefix sh = ((pr0,pr1,pr2,pr3,pr4),ca)` by
    (asm_simp_tac std_ss [comp_ignore_bind_def, comp_bind_def, LET_THM]) >>
  qpat_assum `fuel_ok {} {} {} setup` mp_tac >>
  rewrite_tac[fuel_ok_def] >> disch_then drule >> strip_tac >>
  qpat_assum `fuel_ok {} {} {p4;p3} header` mp_tac >>
  rewrite_tac[fuel_ok_def] >> disch_then drule >> strip_tac >>
  qpat_assum `fuel_ok {} {} {} prefix` mp_tac >>
  rewrite_tac[fuel_ok_def] >> disch_then drule >> strip_tac >>
  qpat_assum `fuel_ok {} {} {p2} suffix` mp_tac >>
  rewrite_tac[fuel_ok_def] >> disch_then drule >> strip_tac >>
  `fuel_ok {} {} {} (compile_abi_encode_to_buf pr3 pr4 elem_info)` by simp[] >>
  pop_assum mp_tac >> rewrite_tac[fuel_ok_def] >>
  disch_then drule >> strip_tac >>
  mp_tac (Q.INST [`dp` |-> `p1`] (SRULE [comp_ignore_bind_def] abi_encode_dyn_exit_fuel)) >>
  rewrite_tac[fuel_ok_def] >> disch_then drule >> strip_tac >>
  fs[Abbr `setup`, Abbr `header`, Abbr `prefix`, Abbr `suffix`, comp_ignore_bind_def] >>
  drule_all (SRULE [LET_THM, comp_ignore_bind_def] abi_encode_dyn_middle_fuel) >>
  strip_tac >>
  `cs_extends sh se` by metis_tac[cs_extends_trans] >>
  `?K. frag_fuel {} {} {} st se K` by
    metis_tac[frag_fuel_seq, pred_setTheory.UNION_EMPTY, pred_setTheory.EMPTY_SUBSET] >>
  `cs_extends st se` by metis_tac[cs_extends_trans] >>
  `st.cs_next_var <= se.cs_next_var` by decide_tac >>
  `?K. frag_fuel {} {} {} st st' K` by
    metis_tac[frag_fuel_seq, pred_setTheory.UNION_EMPTY, pred_setTheory.EMPTY_SUBSET] >>
  metis_tac[frag_fuel_mono, pred_setTheory.EMPTY_SUBSET, pred_setTheory.SUBSET_REFL, arithmeticTheory.LESS_EQ_REFL]
QED
