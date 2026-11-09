(* Signed range counters are words, not the natural iteration index.
   The general control paths live in forPtrControl; use the existing
   i2w_counter_suc arithmetic boundary rather than a second arithmetic proof. *)
Theory forPtrRangeControl
Ancestors forPtrControl stmtSimForParts

Theorem for_range_counter_backedge_path_ptr:
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  get_instruction bb s.vs_inst_idx =
    SOME (mk_inst id ADD [Var ctr; Lit 1w] [tmp]) /\
  get_instruction bb (SUC s.vs_inst_idx) =
    SOME (mk_inst id2 ASSIGN [Var tmp] [ctr]) /\
  sb.cs_blocks = sa.cs_blocks /\ sb.cs_current_bb = sa.cs_current_bb /\
  sb.cs_current_insts = sa.cs_current_insts ++
    [mk_inst sa.cs_next_id JMP [Label lbl] []] /\
  fn_has_code sa sb fn /\ s.vs_current_bb = sa.cs_current_bb /\
  LENGTH sa.cs_current_insts = SUC (SUC s.vs_inst_idx) /\
  ~ctx_has_dalloca ctx /\ ~s.vs_halted /\
  lookup_var ctr s = SOME (i2w (n1 + &j)) /\
  FLOOKUP G ctr = NONE /\ op_taint tn (Var ctr) = {} ==>
  gas_path_ptr D 0 ctx fn PG G tn s 0
    (DRESTRICT (DRESTRICT G (COMPL {tmp})) (COMPL {ctr}))
    (tn with t_var := (tn.t_var |+ (tmp,{})) |+ (ctr,{}))
    (OK (jump_to lbl (update_var ctr (i2w (n1 + &(j+1)))
      (update_var tmp (i2w (n1 + &(j+1))) s))))
Proof
  strip_tac >> rewrite_tac[GSYM i2w_counter_suc] >>
  irule for_counter_backedge_path_ptr >>
  goal_assum (drule_at Any) >> simp[] >> metis_tac[]
QED
