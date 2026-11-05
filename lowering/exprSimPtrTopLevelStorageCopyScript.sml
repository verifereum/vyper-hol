(* Ghost interface probes for the concrete storage-copy loop. *)
Theory exprSimPtrTopLevelStorageCopy
Ancestors
  exprSimPtrTopLevelCopy typedCopyPtr decoderGhostFramePtr bodyPtrDefs
  fragGasPathPtr ptrDiscipline ptrSafeRun gasCount venomExecSemantics venomState venomInst
  words finite_map pred_set list

Theorem toplevel_counter_increment_ghost:
  FLOOKUP G cv = NONE /\ op_taint tn (Var cv) = {} ==>
  FLOOKUP (step_prov PG G (mk_inst id ADD [Var cv; Lit 1w] [nv]) t) nv = NONE /\
  op_taint (step_taint (mk_inst id ADD [Var cv; Lit 1w] [nv]) s t tn)
    (Var nv) = {}
Proof
  strip_tac >>
  simp[step_prov_def, set_prov_def, out_prov_def, first_prov_def,
       op_prov_def, mk_inst_def, FLOOKUP_DRESTRICT,
       step_taint_def, set_var_taint_def, out_taint_def, op_taint_def,
       FLOOKUP_UPDATE] >>
  Cases_on `eval_operand (Var cv) s` >> simp[]
QED

Theorem toplevel_counter_assign_ghost:
  FLOOKUP G nv = NONE /\ op_taint tn (Var nv) = {} ==>
  FLOOKUP (step_prov PG G (mk_inst id ASSIGN [Var nv] [cv]) t) cv = NONE /\
  op_taint (step_taint (mk_inst id ASSIGN [Var nv] [cv]) s t tn)
    (Var cv) = {}
Proof
  strip_tac >>
  simp[step_prov_def, set_prov_def, out_prov_def, first_prov_def,
       op_prov_def, mk_inst_def, FLOOKUP_DRESTRICT,
       step_taint_def, set_var_taint_def, out_taint_def, op_taint_def,
       FLOOKUP_UPDATE] >>
  Cases_on `eval_operand (Var nv) s` >> gvs[op_taint_def]
QED

Theorem toplevel_counter_offset_ghost:
  FLOOKUP (step_prov PG G (mk_inst id MUL [Var cv; Lit 32w] [mv]) t) mv = NONE /\
  op_taint (step_taint (mk_inst id MUL [Var cv; Lit 32w] [mv]) s t tn)
    (Var mv) = {}
Proof
  simp[step_prov_def, set_prov_def, out_prov_def, mk_inst_def,
       FLOOKUP_DRESTRICT, step_taint_def, set_var_taint_def,
       out_taint_def, op_taint_def, FLOOKUP_UPDATE] >>
  Cases_on `eval_operand (Var cv) s` >> simp[]
QED

Theorem toplevel_entry_non_phi_ghost:
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  bb.bb_instructions = i::rest /\ i.inst_opcode <> PHI ==>
  entry_prov fn s G = G /\ entry_taint_vars fn s tn = tn
Proof
  simp[entry_prov_def, entry_taint_vars_def, phis_prov_def, phis_taint_def]
QED

(* Both arithmetic inputs have their actual pre-step values here. *)
Theorem toplevel_destination_offset_covers:
  ptr_covers G tn dst s (32*n) /\ lookup_var dst s = SOME w /\
  k < n /\ w2n w + 32*n < dimword (:256) ==>
  ptr_covers
    (step_prov PG G (mk_inst id ADD [Var dst; Var mv] [dv])
      (update_var dv (w + n2w (32*k)) s))
    (step_taint (mk_inst id ADD [Var dst; Var mv] [dv]) s
      (update_var dv (w + n2w (32*k)) s) tn)
    dv (update_var dv (w + n2w (32*k)) s) 32
Proof
  strip_tac >> gvs[ptr_covers_def] >>
  simp[step_prov_def, set_prov_def, out_prov_def, first_prov_def,
       op_prov_def, mk_inst_def, FLOOKUP_UPDATE,
       lookup_var_def, update_var_def] >>
  conj_tac
  >- (simp[step_taint_def, set_var_taint_def, out_taint_def, op_taint_def,
           mk_inst_def, FLOOKUP_UPDATE] >>
      Cases_on `eval_operand (Var dst) s` >> simp[]) >>
  `w2n (w + n2w (32*k)) = w2n w + 32*k` by
    (`w2n w + 32*k < dimword (:256)` by decide_tac >>
     Cases_on `w` >> gvs[wordsTheory.word_add_n2w] >> decide_tac) >>
  simp[] >> decide_tac
QED

(* The counted fragment relation also has a raw-jump edge: no entry
   transformation is needed when stopping at a block's index-zero frontier. *)
Theorem toplevel_copy_raw_jump_path:
  ~s.vs_halted /\
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  get_instruction bb s.vs_inst_idx = SOME inst /\
  MEM inst.inst_opcode [JMP;JNZ] /\
  ptr_inst_ok D 0 0 ctx fn G tn inst s /\
  step_inst_base inst s = OK (jump_to lbl s) ==>
  gas_path_ptr D 0 ctx fn PG G tn s 0 G tn (OK (jump_to lbl s))
Proof
  strip_tac >>
  `inst.inst_opcode <> INVOKE` by gvs[] >>
  `step_inst 0 ctx inst s = OK (jump_to lbl s)` by
    (simp[step_inst_non_invoke] >> gvs[]) >>
  `ptr_safe_step D 0 0 ctx fn PG G tn inst s` by
    (simp[ptr_safe_step_def] >> gvs[]) >>
  `gas_path_ptr_edge D 0 ctx fn PG G tn s 0 G tn (OK (jump_to lbl s))` by
    (pure_rewrite_tac[gas_path_ptr_edge_def] >> conj_tac >- simp[] >>
     qexists_tac `0` >>
     simp[] >> gvs[gas_count_step_def, is_terminator_def] >> metis_tac[]) >>
  `~(jump_to lbl s).vs_halted` by simp[jump_to_def] >>
  metis_tac[gas_path_ptr_rules, arithmeticTheory.ADD_CLAUSES]
QED
