(* Checked finite prefixes of the array loop, ending at the actual body
   compilation point rather than at an erased S1 execution. *)
Theory forPtrArrayPrepare
Ancestors forPtrRangePrepare forPtrAddress forPtrWriteScope forPtrArraySnapshot
  forPtrWord forPtrBulk forPtrBytes forPtrCopyInterface stmtSimForArrayLoop
  fragExec emitHelperProps finite_map list forPtrControl venomState ptrDiscipline

Theorem for_array_header_test_path_ptr:
  lookup_block cond_lbl func.fn_blocks =
    SOME <| bb_label := cond_lbl;
      bb_instructions := [mk_inst j1 EQ [Var idx; Lit (n2w n)] [dv];
        mk_inst j2 JNZ [Var dv; Label exit_lbl; Label stmts_lbl] []] |> /\
  ~ctx_has_dalloca ctx /\ ~s.vs_halted /\
  s.vs_current_bb = cond_lbl /\ s.vs_inst_idx = 0 /\
  lookup_var idx s = SOME (n2w k) /\
  op_taint tn (Var idx) = {} /\ op_prov G (Var idx) = NONE ==>
  gas_path_ptr D 0 ctx func PG G tn s 0
    (DRESTRICT G (COMPL {dv}))
    (tn with t_var := tn.t_var |+ (dv,{}))
    (OK (jump_to (if (n2w k : bytes32) = n2w n then exit_lbl else stmts_lbl)
      (update_var dv (if (n2w k : bytes32) = n2w n then 1w else 0w) s)))
Proof
  strip_tac >> irule for_counter_test_path_ptr >> simp[] >>
  qexistsl_tac [`Lit (n2w n)`, `idx`, `j1`,
    `(ARB:compile_state) with <| cs_blocks := []; cs_current_bb := cond_lbl;
       cs_current_insts := []; cs_next_id := j1 |>`,
    `(ARB:compile_state) with <| cs_blocks := []; cs_current_bb := cond_lbl;
       cs_current_insts := [mk_inst j1 EQ [Var idx; Lit (n2w n)] [dv];
         mk_inst j2 JNZ [Var dv; Label exit_lbl; Label stmts_lbl] []] |>`,
    `(ARB:compile_state) with <| cs_blocks := []; cs_current_bb := cond_lbl;
       cs_current_insts := [mk_inst j1 EQ [Var idx; Lit (n2w n)] [dv]];
       cs_next_id := j2 |>`] >>
  simp[fn_has_code_def, emitted_blocks_def, eval_operand_def,
       op_taint_def, op_prov_def]
QED

(* The current word-copy interface's four primitive value constructors do
   not cover AddressT (or fixed byte words). This checked probe records the
   missing branch without changing the frozen For theorem. *)
Theorem for_array_address_word_copy_gap:
  is_word_type (BaseT AddressT) /\
  evaluate_type FEMPTY (BaseT AddressT) = SOME (BaseTV AddressT) /\
  value_has_type (BaseTV AddressT) (BytesV (REPLICATE 20 0w)) /\
  ~((?x. BytesV (REPLICATE 20 0w) = BoolV x) \/
    (?x. BytesV (REPLICATE 20 0w) = IntV x) \/
    (?x. BytesV (REPLICATE 20 0w) = FlagV x) \/
    (?x. BytesV (REPLICATE 20 0w) = DecimalV x))
Proof
  EVAL_TAC >> simp[]
QED
