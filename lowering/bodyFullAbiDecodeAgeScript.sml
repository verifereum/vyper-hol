Theory bodyFullAbiDecodeAge
Ancestors
  abiBuiltinDecodeSetup loweringHalt freshWrites list

(* Live snapshots retain their variable age as compilation advances.  The
   other snapshot fields are deliberately polymorphic. *)
Theorem abi_decode_live_age_mono:
  sa.cs_next_var <= sb.cs_next_var /\
  EVERY (\(aid,p,b,k,bytes). not_fresh_at sa p) live ==>
  EVERY (\(aid,p,b,k,bytes). not_fresh_at sb p) live
Proof
  simp[EVERY_MEM] >> rpt strip_tac >>
  first_x_assum drule >>
  PairCases_on `e` >> simp[] >> strip_tac >>
  irule freshWritesTheory.not_fresh_at_mono >>
  goal_assum (drule_at Any) >> simp[]
QED

(* The root header and output allocation advance the variable counter. *)
Theorem abi_decode_setup_age:
  abi_builtin_decode_setup data min_size max_size outsz st = (ops,ready) /\
  origin.cs_next_var <= st.cs_next_var ==>
  origin.cs_next_var <= ready.cs_next_var
Proof
  rpt strip_tac >> drule abi_builtin_decode_setup_shape >>
  strip_tac >> simp[]
QED

(* Scratch ownership alone says nothing about variable age: use the actual
   allocation result, whose variable was introduced before sb. *)
Theorem abi_decode_scratch_age:
  compile_alloc_buffer n sa = (buf,sb) /\
  buf.buf_operand = Var p /\
  sb.cs_next_var <= child.cs_next_var ==>
  not_fresh_at child p
Proof
  rpt strip_tac >> drule compile_alloc_buffer_parts >> strip_tac >>
  gvs[] >> metis_tac[freshWritesTheory.not_fresh_at_mono]
QED
