Theory bodyPtrPrecompileBuiltinsPlacement
Ancestors fragExec exprLoweringProps list rich_list

(* Instruction membership is already exported as exprSimHash.hash_emitted_inst_mem. *)
Theorem precompile_tail_placement:
  fn_has_code sf sb fn /\ same_blocks sf sb /\
  sb.cs_current_insts = sf.cs_current_insts ++ emitted_insts sf sb /\
  s.vs_current_bb = sf.cs_current_bb /\
  s.vs_inst_idx = LENGTH sf.cs_current_insts ==>
  ?bb. lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
       isPREFIX (emitted_insts sf sb) (DROP s.vs_inst_idx bb.bb_instructions)
Proof
  rw[fn_has_code_def, same_blocks_def] >> qexists `bb` >>
  gvs[IS_PREFIX_APPEND] >>
  qexists `l` >> pure_rewrite_tac[GSYM APPEND_ASSOC, DROP_LENGTH_APPEND] >> simp[]
QED
