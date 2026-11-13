(* Executed pointer offsets, preserving the exterior semantic state. *)
Theory typedCopyOffsetPtr
Ancestors typedCopyOffsetEffectsPtr typedCopyPtr exprLoweringProps context compileEnv loweringStateRelDefs emitHelper
  contextCodegenRelProps bodyPtrDefs fragExecPtr words venomState finite_map
  ptrDiscipline venomInst

Theorem compile_with_byte_offset_frag_ptr:
  !cx ctx PG R root off sa op sb G tn s a total n.
    compile_with_byte_offset (Var root) off sa = (op,sb) /\
    not_fresh_at sa root /\ lookup_var root s = SOME a /\
    ptr_covers G tn root s total /\ off < total /\ off+n <= total /\
    w2n a + off < dimword(:256) ==>
    cs_extends sa sb /\
    ?p Gf tnf sf.
      op = Var p /\ lookup_var p sf = SOME (n2w (w2n a+off)) /\
      ptr_covers Gf tnf p sf n /\ not_fresh_at sb p /\
      frag_exec_ptr cx ctx PG sa sb
        (\g t v. g = G /\ t = tn /\ v = s)
        (\g t v. g = Gf /\ t = tnf /\ v = sf) R /\
      sf.vs_memory = s.vs_memory /\ tnf.t_mem = tn.t_mem /\
      tnf.t_stor = tn.t_stor /\ tnf.t_trans = tn.t_trans /\
      (!q. not_fresh_at sa q ==>
        lookup_var q sf = lookup_var q s /\ FLOOKUP Gf q = FLOOKUP G q /\
        op_taint tnf (Var q) = op_taint tn (Var q))
Proof
  rpt strip_tac >> drule_all compile_with_byte_offset_effects_frag_ptr >>
  metis_tac[]
QED
