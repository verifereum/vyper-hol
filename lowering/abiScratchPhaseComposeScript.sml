(* Compose initializer, recursive body and bookkeeping effects over one owner.
   TOP-LEVEL: abi_scratch_phase_compose retains the initial physical footprint
   while widening compiler intervals and preserving older operand values. *)
Theory abiScratchPhaseCompose
Ancestors
  abiScratchEncoderContract abiScratchEffectWiden abiScratchEffectCompose
  compileEnv venomState arithmetic

Theorem abi_scratch_phase_compose:
  abi_scratch_effect first last st.cs_next_id prepared.cs_next_id st.cs_next_var
    limit_st d sz b cap initial ready /\
  abi_scratch_effect first last prepared.cs_next_id middle.cs_next_id prepared.cs_next_var
    limit_st d sz b cap ready encoded /\
  abi_scratch_effect first last st.cs_next_id end_st.cs_next_id middle.cs_next_var
    limit_st d sz b cap encoded actual /\
  first <= st.cs_next_id /\ end_st.cs_next_id <= last /\
  st.cs_next_id <= prepared.cs_next_id /\ prepared.cs_next_id <= middle.cs_next_id /\
  middle.cs_next_id <= end_st.cs_next_id /\
  st.cs_next_var <= prepared.cs_next_var /\ prepared.cs_next_var <= middle.cs_next_var ==>
  abi_scratch_effect first last st.cs_next_id end_st.cs_next_id st.cs_next_var
    limit_st d sz b cap initial actual
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  `abi_scratch_effect first last st.cs_next_id end_st.cs_next_id st.cs_next_var
    limit_st d sz b cap initial ready` by
    (irule abi_scratch_effect_widen >>
     qexistsl_tac [`d`, `prepared.cs_next_id`, `st.cs_next_id`, `st.cs_next_var`, `sz`] >>
     asm_simp_tac bool_ss [LESS_EQ_REFL] >> decide_tac) >>
  `abi_scratch_effect first last st.cs_next_id end_st.cs_next_id st.cs_next_var
    limit_st d sz b cap ready encoded` by
    (irule abi_scratch_effect_widen >>
     qexistsl_tac [`d`, `middle.cs_next_id`, `prepared.cs_next_id`, `prepared.cs_next_var`, `sz`] >>
     asm_simp_tac bool_ss [] >> decide_tac) >>
  `abi_scratch_effect first last st.cs_next_id end_st.cs_next_id st.cs_next_var
    limit_st d sz b cap encoded actual` by
    (irule abi_scratch_effect_widen >>
     qexistsl_tac [`d`, `end_st.cs_next_id`, `st.cs_next_id`, `middle.cs_next_var`, `sz`] >>
     asm_simp_tac bool_ss [LESS_EQ_REFL] >> decide_tac) >>
  `abi_scratch_effect first last st.cs_next_id end_st.cs_next_id st.cs_next_var
    limit_st d sz b cap initial encoded` by
    (irule abi_scratch_effect_trans >> asm_simp_tac bool_ss [] >>
     qexists_tac `ready` >> asm_simp_tac bool_ss []) >>
  irule abi_scratch_effect_trans >> asm_simp_tac bool_ss [] >>
  qexists_tac `encoded` >> asm_simp_tac bool_ss []
QED

val () = List.app (fn (n,th) =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th) in
    if null (Thm.hyp th) andalso null axioms andalso
       List.all (fn s => s = "DISK_THM") oracles then
      print ("ABI_SCRATCH_PHASE_COMPOSE_KERNEL_CLOSED " ^ n ^ "\n")
    else raise Fail ("ABI scratch recursive phase composition not kernel closed: " ^ n)
  end) (DB.thms "abiScratchPhaseCompose");
