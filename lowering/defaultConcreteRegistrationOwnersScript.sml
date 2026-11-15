(* Owner transport and extension, independent of compiler/resource staging. *)
Theory defaultConcreteRegistrationOwners
Ancestors defaultConcreteWordRegistration defaultConcreteRegistrationDefs
  rich_list list arithmetic

Theorem default_registration_owners_advance:
  LENGTH (args:(string # 'a) list) = LENGTH tvs /\
  DROP (LENGTH owners) args = next :: remaining /\
  DROP (LENGTH owners) tvs = tv :: more /\
  LIST_REL (default_registration_owner fn ce st s G tn)
    (ZIP (TAKE (LENGTH owners) args, TAKE (LENGTH owners) tvs)) owners /\
  (!name ty tv x dst p id.
    default_registration_owner fn ce st s G tn ((name,(ty:'a)),tv) (x,dst,p,id) ==>
    FLOOKUP ce1.ce_vars name = FLOOKUP ce.ce_vars name /\
    FLOOKUP t.vs_allocas id = FLOOKUP s.vs_allocas id) /\
  st.cs_next_id <= st1.cs_next_id /\
  (!v. not_fresh_at st v ==> not_fresh_at st1 v /\
    FLOOKUP H v = FLOOKUP G v /\
    op_taint u (Var v) = op_taint tn (Var v) /\
    eval_operand (Var v) t = eval_operand (Var v) s) /\
  s.vs_alloca_next <= t.vs_alloca_next /\
  abi_decode_frame s.vs_alloca_next n s t /\
  default_registration_owner fn ce1 st1 t H u (next,tv) newowner ==>
  LIST_REL (default_registration_owner fn ce1 st1 t H u)
    (ZIP (TAKE (LENGTH (owners ++ [newowner])) args,
          TAKE (LENGTH (owners ++ [newowner])) tvs)) (owners ++ [newowner])
Proof
  strip_tac >>
  `LIST_REL (default_registration_owner fn ce1 st1 t H u)
    (ZIP (TAKE (LENGTH owners) args, TAKE (LENGTH owners) tvs)) owners` by
    (irule LIST_REL_mono >>
     goal_assum $ drule_at Any >>
     rpt gen_tac >> PairCases_on `x` >> PairCases_on `y` >>
     strip_tac >>
     first_x_assum drule >> strip_tac >>
     irule default_registration_owner_frame >>
     goal_assum $ drule_at (Pat `default_registration_owner _ _ _ _ _ _ _ _`) >>
     simp[] >> metis_tac[]) >>
  simp[LENGTH_APPEND, GSYM ADD1, TAKE_SUC] >>
  `ZIP (TAKE (LENGTH owners) args ++ [next],
        TAKE (LENGTH owners) tvs ++ [tv]) =
   ZIP (TAKE (LENGTH owners) args, TAKE (LENGTH owners) tvs) ++ [(next,tv)]` by
    (qspecl_then [`TAKE (LENGTH owners) args`, `TAKE (LENGTH owners) tvs`,
       `[next]`, `[tv]`] mp_tac rich_listTheory.ZIP_APPEND >>
     simp[LENGTH_TAKE_EQ] >> metis_tac[]) >>
  simp[LIST_REL_APPEND]
QED

Theorem default_registration_bytes_owner:
  FLOOKUP ce.ce_vars name = SOME (PtrVar (Var dst) (type_memory_size tv)) /\
  val_wf tv x /\ val_in_memory tv x s.vs_alloca_next t.vs_memory /\
  eval_operand (Var dst) t = SOME (n2w s.vs_alloca_next) /\
  ptr_covers H u dst t (type_memory_size tv) /\
  FLOOKUP t.vs_allocas st.cs_next_id =
    SOME (s.vs_alloca_next,type_memory_size tv) /\
  t.vs_alloca_next = s.vs_alloca_next + type_memory_size tv /\
  s.vs_alloca_next + type_memory_size tv < dimword (:256) /\
  st.cs_next_id < st1.cs_next_id /\ not_fresh_at st1 dst /\
  MEM ins (fn_insts fn) /\ ins.inst_opcode = ALLOCA /\
  ins.inst_outputs = [dst] /\ ins.inst_id = st.cs_next_id ==>
  default_registration_owner fn ce st1 t H u ((name,ty),tv)
    (x,Var dst,s.vs_alloca_next,st.cs_next_id)
Proof
  simp[default_registration_owner_def] >> strip_tac >>
  qexists `ins` >> simp[]
QED
