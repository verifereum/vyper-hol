(* ptr_discipline with its per-function part weakened to fn_ptr_ok of
   each function, the form the LowerDload leaves use. *)
Theory o1LowerDloadPtrDiscipline
Ancestors
  ptrDiscipline list

Theorem ptr_discipline_fn_ptr_ok:
  ptr_discipline lo ctx vs ==>
  lo <= vs.vs_alloca_next /\
  ?P. EVERY (fn_ptr_ok P) ctx.ctx_functions /\
      !stk PG G tn fn inst s.
        frame_reachable vs ctx stk PG G tn fn inst s ==>
        access_ok lo G fn inst s /\ taint_ok fn tn inst s /\
        allocas_from lo s /\
        (ctx_has_dalloca ctx ==> allocas_below_fmp s)
Proof
  rewrite_tac[ptr_discipline_def] >> strip_tac >> asm_rewrite_tac[] >>
  qexists_tac `P` >> asm_rewrite_tac[] >>
  fs[EVERY_MEM]
QED

Theorem ptr_discipline_inst_opcode_exclusions:
  ptr_discipline lo C vs /\ MEM fn C.ctx_functions /\
  MEM inst (fn_insts fn) /\ ~ctx_has_dalloca C ==>
  ~MEM inst.inst_opcode [MEMTOP; DRET; GETFMP; SETFMP; RETFMP; FMP_PARAM; DALLOCA]
Proof
  strip_tac >>
  `?P. EVERY (fn_ptr_ok P) C.ctx_functions` by
    metis_tac[ptr_discipline_fn_ptr_ok] >>
  `~MEM inst.inst_opcode [MEMTOP; DRET; GETFMP; SETFMP; RETFMP; FMP_PARAM]` by
    (fs[EVERY_MEM] >> first_x_assum drule >>
     simp[fn_ptr_ok_def] >> strip_tac >> first_x_assum drule >> simp[MEM]) >>
  `inst.inst_opcode <> DALLOCA` by
    (fs[ctx_has_dalloca_def, EXISTS_MEM] >> metis_tac[]) >>
  fs[MEM]
QED
