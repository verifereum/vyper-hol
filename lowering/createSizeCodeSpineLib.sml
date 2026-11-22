structure createSizeCodeSpineLib =
struct

open HolKernel boolLib bossLib
open compileEnvTheory exprLoweringTheory fragExecTheory

(* Split a known code interval successively along a chain of adjacent
   extensions. The remaining tail always ends at the original boundary. *)
fun split_code_spine f (a::b::(tail as _::_)) =
    let
      val z = List.last tail
      fun extends [_] = first_assum ACCEPT_TAC
        | extends (c::cs) =
          irule cs_extends_trans >> qexists_tac [QUOTE c] >>
          conj_tac >- first_assum ACCEPT_TAC >> extends cs
        | extends [] = NO_TAC
    in
      [QUOTE ("cs_extends " ^ b ^ " " ^ z)] by extends tail >>
      [QUOTE ("fn_has_code " ^ a ^ " " ^ b ^ " " ^ f ^ " /\\ fn_has_code " ^ b ^ " " ^ z ^ " " ^ f)] by
        (irule fn_has_code_split >> rpt conj_tac >> first_assum ACCEPT_TAC) >>
      pop_assum (map_every assume_tac o CONJUNCTS) >> split_code_spine f (b::tail)
    end
  | split_code_spine _ _ = all_tac;

(* Specialize the compiler's shadow rule to caller-frame salt evaluation. *)
val shadow_create_salt =
  let
    val rule = Q.INST [`sd` |-> `T`, `sh` |-> `T`,
        `f` |-> `compile_expr`, `g` |-> `compile_expr`]
      gasShadowCompileHelpersTheory.gas_shadow_compiles_create_salt
  in
    Q.GENL [`cenv`, `salt_e`]
      (MATCH_MP rule (CONJUNCT1
        (Q.INST [`sd` |-> `T`] gasShadowCompileTheory.gas_shadow_compile_expr_env)))
  end;

end
