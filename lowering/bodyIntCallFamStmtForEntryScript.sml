(* The range body's concrete entry, with its disjoint memory frame. *)
Theory bodyIntCallFamStmtForEntry
Ancestors
  stmtSimForLoop stmtForRangeMemoryParts stmtSimDeclStore
  loweringSlice localPtrsProps valueEncodingProps stmtSimProps stmtSimForParts
  venomState venomExecSemantics venomExecProofs finite_map vyperState valueEncoding
  stmtSimDefs compileEnv vyperValue exprLoweringProps emitHelperProps
  fragGasPathMem fragGasPath fragGasMode gasCount venomInst integer_word

Theorem intcall_for_body_entry_frame:
  !ctx func cenv bc cx esk cc id tyv p sz w ainst cv ev dv n1 n2 k
   cond_lbl exit_lbl body_lbl j1 j2 j3 bbb.
    lookup_block cond_lbl func.fn_blocks =
      SOME <| bb_label := cond_lbl;
              bb_instructions :=
                [mk_inst j1 EQ [Var cv; Var ev] [dv];
                 mk_inst j2 JNZ [Var dv; Label exit_lbl; Label body_lbl] []] |> /\
    lookup_block body_lbl func.fn_blocks = SOME bbb /\
    get_instruction bbb 0 = SOME (mk_inst j3 MSTORE [Var p; Var cv] []) /\
    cc.vs_current_bb = cond_lbl /\ cc.vs_inst_idx = 0 /\ ~cc.vs_halted /\
    stmt_state_rel ctx func cenv cx esk cc /\
    lookup_var cv cc = SOME (i2w (n1 + &k)) /\
    lookup_var ev cc = SOME (i2w n2) /\ lookup_var p cc = SOME w /\
    FLOOKUP cc.vs_allocas ainst.inst_id = SOME (w2n w, sz) /\
    n1 <= n2 /\ k < Num (n2 - n1) /\ Num (n2 - n1) < dimword (:256) /\
    lookup_scopes id esk.scopes = NONE /\
    (!l. FLOOKUP cenv.ce_vars id = SOME l ==> ?q z. l = PtrVar q z) /\
    FLOOKUP bc.ce_vars id = SOME (PtrVar (Var p) sz) /\
    (!n. n <> id ==> FLOOKUP bc.ce_vars n = FLOOKUP cenv.ce_vars n) /\
    bc.ce_module_vars = cenv.ce_module_vars /\
    bc.ce_module = cenv.ce_module /\ bc.ce_is_ctor = cenv.ce_is_ctor /\
    bc.ce_imm_alloca = cenv.ce_imm_alloca /\
    not_local_ptr cenv esk.scopes dv /\
    not_local_ptr bc (FEMPTY :: esk.scopes) p /\ dv <> p /\ dv <> cv /\
    MEM ainst (fn_insts func) /\ ainst.inst_opcode = ALLOCA /\
    ainst.inst_outputs = [p] /\ fn_inst_ids_distinct func /\
    32 <= sz /\ type_memory_size tyv = 32 ==>
    ?s2. s2.vs_current_bb = body_lbl /\ s2.vs_inst_idx = 1 /\
         ~s2.vs_halted /\
         stmt_state_rel ctx func bc cx
           (esk with scopes :=
              (FEMPTY |+ (id, <| assignable := F; type := tyv;
                                 value := IntV (n1 + &k); popped := [] |>)) :: esk.scopes)
           s2 /\
         (!x. x <> dv ==> lookup_var x s2 = lookup_var x cc) /\
         s2.vs_allocas = cc.vs_allocas /\
         gas_marked_path F ctx func cc 0 (OK s2) /\
         (!a n. a + n <= w2n w \/ w2n w + 32 <= a ==>
                mem_bytes_at a n s2.vs_memory = mem_bytes_at a n cc.vs_memory) /\
         !fuel rr. run_from fuel ctx func s2 = rr /\ (!e. rr <> Error e) ==>
                   ?fuel'. run_from fuel' ctx func cc = rr
Proof
  rpt gen_tac >> strip_tac >>
  `(i2w (n1 + &k) : bytes32) <> i2w n2` by metis_tac[i2w_counter_ne] >>
  qabbrev_tac `s1 = jump_to body_lbl (update_var dv (bool_to_word F) cc)` >>
  `gas_path ctx func cc 0 (OK s1)` by
    (drule_all for_cond_zero_path_mem >> simp[Abbr `s1`] >>
     metis_tac[gas_path_mem_exec]) >>
  `lookup_var p s1 = SOME w /\ lookup_var cv s1 = SOME (i2w (n1 + &k)) /\
   s1.vs_current_bb = body_lbl /\ s1.vs_inst_idx = 0 /\ ~s1.vs_halted /\
   s1.vs_allocas = cc.vs_allocas /\
   (!x. x <> dv ==> lookup_var x s1 = lookup_var x cc)` by
    (simp[Abbr `s1`, jump_to_def, update_var_def, lookup_var_def,
          FLOOKUP_UPDATE] >> fs[lookup_var_def]) >>
  qabbrev_tac `s2 = mstore (w2n w) (i2w (n1 + &k)) s1 with vs_inst_idx := 1` >>
  `stmt_state_rel ctx func cenv cx (esk with scopes := FEMPTY :: esk.scopes) s1` by
    (simp[Abbr `s1`, stmt_state_rel_jump_to, stmt_state_rel_push_scope] >>
     irule stmt_state_rel_update_var >> simp[]) >>
  `stmt_state_rel ctx func bc cx (esk with scopes := FEMPTY :: esk.scopes) s1` by
    (irule stmt_state_rel_cenv_cong >> qexists_tac `cenv` >> simp[] >>
     rpt strip_tac >> Cases_on `n = id` >> gvs[lookup_scopes_def] >>
     res_tac >> gvs[]) >>
  `stmt_state_rel ctx func bc cx
     (esk with scopes :=
       (FEMPTY |+ (id, <| assignable := F; type := tyv;
                          value := IntV (n1 + &k); popped := [] |>)) :: esk.scopes)
     (mstore (w2n w) (i2w (n1 + &k)) s1)` by
    suspend "declare" >>
  `gas_path ctx func s1 0 (OK s2)` by suspend "store" >>
  `gas_path ctx func cc 0 (OK s2)` by
    (qpat_x_assum `gas_path ctx func cc _ _` mp_tac >>
     disch_then (mp_then Any mp_tac gas_path_then) >>
     disch_then drule >> simp[]) >>
  qexists_tac `s2` >>
  simp[Abbr `s2`, stmt_state_rel_inst_idx, gas_marked_path_def] >>
  rpt conj_tac
  >- simp[mstore_def]
  >- simp[mstore_def]
  >- (rpt strip_tac >> fs[mstore_def, lookup_var_def])
  >- simp[mstore_def]
  >- (rpt strip_tac >>
      `mem_bytes_at a n (mstore (w2n w) (i2w (n1 + &k)) s1).vs_memory =
       mem_bytes_at a n s1.vs_memory` by
        (irule mstore_mem_bytes_at_disjoint >> simp[]) >>
      simp[Abbr `s1`, jump_to_def, update_var_def]) >>
  metis_tac[gas_path_normal]
QED

Resume intcall_for_body_entry_frame[declare]:
  `immutables_rel bc cx.txn.target bc.ce_module bc.ce_is_ctor
     (esk with scopes := FEMPTY :: esk.scopes)
     (mstore (w2n w) (i2w (n1 + &k)) s1)` by
    (irule immutables_rel_mstore_alloca >>
     reverse conj_tac >- fs[stmt_state_rel_def, state_rel_def] >>
     qexistsl_tac [`w2n w`, `func`, `ainst`, `sz`] >>
     fs[stmt_state_rel_def, state_rel_def]) >>
  `val_in_memory tyv (IntV (n1 + &k)) (w2n w)
     (mstore (w2n w) (i2w (n1 + &k)) s1).vs_memory` by
    (rewrite_tac[GSYM val_to_w256_def] >>
     irule word_value_in_memory >> simp[word_value_def]) >>
  `!n b sz'. n <> id /\ local_region bc (FEMPTY :: esk.scopes) s1 n b sz' ==>
     mem_bytes_at b sz' s1.vs_memory =
     mem_bytes_at b sz' (mstore (w2n w) (i2w (n1 + &k)) s1).vs_memory` by
    (rpt strip_tac >>
     `regions_disjoint (w2n w) sz b sz'` by
       (irule local_ptrs_rel_alloca_disjoint >>
        qexistsl_tac [`bc`, `func`, `ainst`, `n`, `p`,
                     `FEMPTY :: esk.scopes`, `s1`] >>
        fs[stmt_state_rel_def, state_rel_def]) >>
     irule EQ_SYM >> irule mstore_mem_bytes_at_disjoint >>
     fs[regions_disjoint_def] >> decide_tac) >>
  irule (SRULE [] (Q.SPECL [`func`, `bc`, `cx`,
    `esk with scopes := FEMPTY :: esk.scopes`] stmt_state_rel_declare_memory)) >>
  simp[lookup_scopes_def] >>
  conj_tac >- metis_tac[word_value_wf, word_value_def] >>
  qexistsl_tac [`ainst`, `s1`, `w`] >>
  simp[lookup_scopes_def] >>
  fs[mstore_def, lookup_var_def] >> metis_tac[]
QED

Resume intcall_for_body_entry_frame[store]:
  `step_inst_base (mk_inst j3 MSTORE [Var p; Var cv] []) s1 =
     OK (mstore (w2n w) (i2w (n1 + &k)) s1)` by
    (irule step_MSTORE >> simp[eval_operand_def]) >>
  `gas_path_edge ctx func s1 0 (OK s2)` by
    (simp[gas_path_edge_def] >> qexists_tac `0` >>
     simp[step_inst_non_invoke, gas_count_step_def, mk_inst_def,
          is_terminator_def, Abbr `s2`] >>
     gvs[mk_inst_def, mstore_def]) >>
  `gas_path ctx func s2 0 (OK s2)` by
    (irule (cj 1 gas_path_rules) >> simp[Abbr `s2`, mstore_def]) >>
  drule (cj 2 gas_path_rules) >> disch_then drule >> simp[]
QED

Finalise intcall_for_body_entry_frame
