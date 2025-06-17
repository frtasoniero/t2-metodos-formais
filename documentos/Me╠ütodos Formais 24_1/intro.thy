theory intro
imports Main
begin

(* definição indutiva do tipo dos naturais *)
datatype Nat = Z | suc Nat

(* verificando termos do tipo Nat*)
term Z
term "Z"
term "suc Z"

(* regra de indução para provas nos naturais, criada pelo sistema *)
thm "Nat.induct"
(* uma forma sintática mais elegante da regra de indução *)
print_statement "Nat.induct"

(* adição *)
primrec add::"Nat \<Rightarrow> Nat \<Rightarrow> Nat" where
    add01: "add x Z = x" |
    add02: "add x (suc y) = suc (add x y)"

term "add (suc (suc Z)) (suc (suc Z))"
value "add (suc (suc Z)) (suc (suc Z))"
term "add (suc Z)"
value "add (suc Z)"

(* nat é o tipo indutivo dos naturais definidos pelo Isabelle *)
thm "nat.induct"
print_statement "nat.induct"

(* verificando termos do tipo nat *)
term "12::nat"
term "Suc(5)"
value "Suc(5)"

theorem th_add01as:"\<forall>x y. add (add x y) z = add x (add y z)"
apply(induct_tac z)
apply(simp)
apply(simp)
done

value "(6 div 2)::nat"
  
value "\<Prod>{1..3::nat}"

end
