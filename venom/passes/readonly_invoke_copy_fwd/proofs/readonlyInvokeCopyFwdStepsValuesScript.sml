Theory readonlyInvokeCopyFwdStepsValues
Ancestors
  readonlyInvokeCopyFwdStepsCore readonlyInvokeCopyFwdValues
  readonlyInvokeCopyFwdRel venomExecSemantics venomState ptrDiscipline
  taintAgree finite_map words list

(* Value-only coverage of step_inst_base:
   ASSIGN and PARAM/FMP_PARAM are handled below. ADD/OFFSET/SUB on inherited
   relocated pointers use the affine rule; EQ/LT/GT use the comparison rule.
   GETFMP/INITIAL_FMP/RETPC_PARAM and BUMP have concrete rules below.
   Core's ricf_cert_exec_pure{1,2,3} applies after opcode reduction to:
     pure1: ISZERO, NOT;
     pure2: ADD, SUB, MUL, Div, Mod, SDIV, SMOD, Exp, EQ, LT, GT, SLT, SGT,
            AND, OR, XOR, SHL, SHR, SAR, SIGNEXTEND, BYTE, OFFSET;
     pure3: ADDMOD, MULMOD.
   Core's ricf_cert_exec_read{0,1} similarly applies to:
     read0: CALLER, ADDRESS, CALLVALUE, ORIGIN, GASPRICE, CHAINID, COINBASE,
            TIMESTAMP, NUMBER, PREVRANDAO, GASLIMIT, BASEFEE, BLOBBASEFEE,
            SELFBALANCE, CALLDATASIZE, RETURNDATASIZE, MEMTOP, CODESIZE;
     read1: MLOAD, SLOAD, TLOAD, BLOCKHASH, BLOBHASH, BALANCE, CALLDATALOAD,
            EXTCODESIZE, EXTCODEHASH, ILOAD, DLOAD.
   Those primitive rules retain masked output agreement as a value-level
   obligation, not a post-certificate. PHIs and translated MLOAD are already
   covered by Core and are not reproved here. *)

Theorem ricf_cert_assign:
  ricf_cert_core D ids stk PG G tn fn sites maps targets G0 tn0 cur curs s t /\
  inst.inst_opcode = ASSIGN /\ inst.inst_operands = [a] /\
  inst.inst_outputs = [out] /\ eval_operand a s = SOME x ==>
  ?y. let u = update_var out x s;
          v = update_var out y t;
          H = set_prov G0 [out] (op_prov G0 a);
          un = tn0 with t_var := set_var_taint tn0.t_var [out] (op_taint tn0 a)
      in step_inst_base inst s = OK u /\ step_inst_base inst t = OK v /\
         ricf_cert_core D ids stk PG
           (ricf_effective_prov fn u H) (ricf_effective_taint fn u un)
           fn sites maps targets H un cur curs u v
Proof
  strip_tac >>
  `?y. eval_operand a t = SOME y /\
       ricf_value_agree sites (op_prov G0 a) (op_taint tn0 a) x y` by
    (fs[ricf_cert_core_def, ricf_live_boundary_core_def] >>
     metis_tac[ricf_frame_agree_operand]) >>
  qexists_tac `y` >> simp[step_inst_base_opcode_eqs] >>
  irule ricf_cert_bind >>
  simp[ricf_effective_prov_def, ricf_effective_taint_def] >> metis_tac[]
QED

Theorem ricf_cert_param:
  ricf_cert_core D ids stk PG G tn fn sites maps targets G0 tn0 cur curs s t /\
  (inst.inst_opcode = PARAM \/ inst.inst_opcode = FMP_PARAM) /\
  inst.inst_operands = [Lit idx] /\ inst.inst_outputs = [out] /\
  w2n idx < LENGTH s.vs_params ==>
  let u = update_var out (EL (w2n idx) s.vs_params) s;
      v = update_var out (EL (w2n idx) t.vs_params) t;
      H = set_prov G0 [out] (EL (w2n idx) (ricf_complete_params PG s.vs_params));
      un = tn0 with t_var := set_var_taint tn0.t_var [out] {}
  in step_inst_base inst s = OK u /\ step_inst_base inst t = OK v /\
     ricf_cert_core D ids stk PG
       (ricf_effective_prov fn u H) (ricf_effective_taint fn u un)
       fn sites maps targets H un cur curs u v
Proof
  strip_tac >>
  `LENGTH s.vs_params = LENGTH t.vs_params /\
   ricf_value_agree sites (EL (w2n idx) (ricf_complete_params PG s.vs_params)) {}
     (EL (w2n idx) s.vs_params) (EL (w2n idx) t.vs_params)` by
    (fs[ricf_cert_core_def, ricf_live_boundary_core_def] >>
     metis_tac[ricf_frame_agree_param, ricf_frame_agree_params,
               ricf_params_agree_def]) >>
  simp[step_inst_base_opcode_eqs] >>
  irule ricf_cert_bind >>
  simp[ricf_effective_prov_def, ricf_effective_taint_def] >>
  goal_assum (drule_at Any) >> simp[] >> metis_tac[]
QED

Theorem ricf_cert_affine:
  ricf_cert_core D ids stk PG G tn fn sites maps targets G0 tn0 cur curs s t /\
  FLOOKUP sites (db,sz) = SOME (db,sb,sz) /\
  ricf_value_agree sites (SOME (db,sz)) {} x y /\
  ((inst.inst_opcode = ADD /\ f = word_add) \/
   (inst.inst_opcode = OFFSET /\ f = word_add) \/
   (inst.inst_opcode = SUB /\ f = word_sub)) /\
  inst.inst_operands = [a;b] /\ inst.inst_outputs = [out] /\
  eval_operand a s = SOME x /\ eval_operand a t = SOME y /\
  eval_operand b s = SOME z /\ eval_operand b t = SOME z ==>
  let u = update_var out (f x z) s;
      v = update_var out (f y z) t;
      H = set_prov G0 [out] (SOME (db,sz));
      un = tn0 with t_var := set_var_taint tn0.t_var [out] {}
  in step_inst_base inst s = OK u /\ step_inst_base inst t = OK v /\
     ricf_cert_core D ids stk PG
       (ricf_effective_prov fn u H) (ricf_effective_taint fn u un)
       fn sites maps targets H un cur curs u v
Proof
  strip_tac >>
  `ricf_sites_ok sites` by
    fs[ricf_cert_core_def, ricf_live_boundary_core_def, ricf_frame_agree_def] >>
  `ricf_value_agree sites (SOME (db,sz)) {} (f x z) (f y z)` by
    metis_tac[ricf_value_agree_add, ricf_value_agree_sub] >>
  simp[step_inst_base_opcode_eqs, exec_pure2_def] >>
  irule ricf_cert_bind >>
  simp[ricf_effective_prov_def, ricf_effective_taint_def] >> metis_tac[]
QED

Theorem ricf_cert_comparison:
  ricf_cert_core D ids stk PG G tn fn sites maps targets G0 tn0 cur curs s t /\
  FLOOKUP sites (db,sz) = SOME (db,sb,sz) /\
  ricf_value_agree sites (SOME (db,sz)) {} x x' /\
  ricf_value_agree sites (SOME (db,sz)) {} y y' /\
  db <= w2n x /\ w2n x <= db+sz /\ db <= w2n y /\ w2n y <= db+sz /\
  db+sz < dimword (:256) /\ sb+sz < dimword (:256) /\
  ((inst.inst_opcode = EQ /\ f = (\x y. bool_to_word (x = y))) \/
   (inst.inst_opcode = LT /\ f = (\x y. bool_to_word (w2n x < w2n y))) \/
   (inst.inst_opcode = GT /\ f = (\x y. bool_to_word (w2n y < w2n x)))) /\
  inst.inst_operands = [a;b] /\ inst.inst_outputs = [out] /\
  eval_operand a s = SOME x /\ eval_operand a t = SOME x' /\
  eval_operand b s = SOME y /\ eval_operand b t = SOME y' ==>
  let u = update_var out (f x y) s;
      v = update_var out (f x' y') t;
      H = set_prov G0 [out] NONE;
      un = tn0 with t_var := set_var_taint tn0.t_var [out] {}
  in step_inst_base inst s = OK u /\ step_inst_base inst t = OK v /\
     ricf_cert_core D ids stk PG
       (ricf_effective_prov fn u H) (ricf_effective_taint fn u un)
       fn sites maps targets H un cur curs u v
Proof
  strip_tac >>
  `ricf_sites_ok sites` by
    fs[ricf_cert_core_def, ricf_live_boundary_core_def, ricf_frame_agree_def] >>
  `((x = y) <=> (x' = y')) /\
   ((w2n x < w2n y) <=> (w2n x' < w2n y')) /\
   ((w2n y < w2n x) <=> (w2n y' < w2n x'))` by
    metis_tac[ricf_value_agree_comparisons] >>
  simp[step_inst_base_opcode_eqs, exec_pure2_def, arithmeticTheory.GREATER_DEF] >>
  irule ricf_cert_bind >>
  simp[ricf_effective_prov_def, ricf_effective_taint_def] >>
  `ricf_value_agree sites NONE {} (f x y) (f x' y')` by
    simp[ricf_value_agree_inactive, word_agree_except_def] >>
  gvs[] >> metis_tac[]
QED

(* The non-exec_read0 spellings of local state reads.  The input value
   premise is at the primitive-read boundary, not a post-certificate. *)
Theorem ricf_cert_local_read:
  ricf_cert_core D ids stk PG G tn fn sites maps targets G0 tn0 cur curs s t /\
  ((inst.inst_opcode = GETFMP /\ inst.inst_operands = [] /\ f = (\s. s.vs_fmp)) \/
   (inst.inst_opcode = INITIAL_FMP /\ inst.inst_operands = [] /\ f = (\s. s.vs_initial_fmp)) \/
   (inst.inst_opcode = RETPC_PARAM /\ inst.inst_operands = [Lit idx] /\
      f = (\s. s.vs_return_pc_token))) /\ inst.inst_outputs = [out] /\
  ricf_value_agree sites NONE {} (f s) (f t) ==>
  let u = update_var out (f s) s;
      v = update_var out (f t) t;
      H = set_prov G0 [out] NONE;
      un = tn0 with t_var := set_var_taint tn0.t_var [out] {}
  in step_inst_base inst s = OK u /\ step_inst_base inst t = OK v /\
     ricf_cert_core D ids stk PG
       (ricf_effective_prov fn u H) (ricf_effective_taint fn u un)
       fn sites maps targets H un cur curs u v
Proof
  strip_tac >> simp[step_inst_base_opcode_eqs] >>
  irule ricf_cert_bind >>
  simp[ricf_effective_prov_def, ricf_effective_taint_def] >> gvs[] >> metis_tac[]
QED

(* BUMP is a pair of local bindings; it changes no allocation or FMP field.
   The two output agreements permit scalar or inherited-pointer uses. *)
Theorem ricf_cert_bump:
  ricf_cert_core D ids stk PG G tn fn sites maps targets G0 tn0 cur curs s t /\
  inst.inst_opcode = BUMP /\ inst.inst_operands = [a;b] /\
  inst.inst_outputs = [out;next] /\
  eval_operand a s = SOME x /\ eval_operand a t = SOME y /\
  eval_operand b s = SOME z /\ eval_operand b t = SOME z' /\
  ricf_value_agree sites p m x y /\
  ricf_value_agree sites q n (x+z) (y+z') ==>
  let u = update_var next (x+z) (update_var out x s);
      v = update_var next (y+z') (update_var out y t);
      H = set_prov (set_prov G0 [out] p) [next] q;
      un = (tn0 with t_var := set_var_taint tn0.t_var [out] m) with t_var :=
        set_var_taint (set_var_taint tn0.t_var [out] m) [next] n
  in step_inst_base inst s = OK u /\ step_inst_base inst t = OK v /\
     ricf_cert_core D ids stk PG
       (ricf_effective_prov fn u H) (ricf_effective_taint fn u un)
       fn sites maps targets H un cur curs u v
Proof
  strip_tac >>
  `ricf_cert_core D ids stk PG
     (ricf_effective_prov fn (update_var out x s) (set_prov G0 [out] p))
     (ricf_effective_taint fn (update_var out x s)
       (tn0 with t_var := set_var_taint tn0.t_var [out] m)) fn sites maps targets
     (set_prov G0 [out] p) (tn0 with t_var := set_var_taint tn0.t_var [out] m)
     cur curs (update_var out x s) (update_var out y t)` by
    (irule ricf_cert_bind >>
     simp[ricf_effective_prov_def, ricf_effective_taint_def] >> metis_tac[]) >>
  simp[step_inst_base_opcode_eqs] >>
  irule ricf_cert_bind >>
  simp[ricf_effective_prov_def, ricf_effective_taint_def] >>
  goal_assum (drule_at Any) >> simp[] >> metis_tac[]
QED
