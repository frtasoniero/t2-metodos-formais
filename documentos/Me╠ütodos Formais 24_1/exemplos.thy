theory exemplos
imports Main
begin

type_synonym string = "char list"

datatype Nat = Z | suc Nat

print_theorems

inductive par::"nat \<Rightarrow> bool" where
"par 0" |
"par x \<Longrightarrow> par (Suc(Suc x))"

thm "Nat.induct"
thm "nat.induct"
thm "par.induct"

(*funcao nao-recursiva*)
definition sq::"nat \<Rightarrow> nat" where
"sq n = n*n"

value "sq 2"

(*funcao recursiva*)
fun parn::"nat \<Rightarrow> bool" where
"parn 0 = True"|
"parn (Suc 0) = False"|
"parn (Suc(Suc x)) = parn x"

value "parn (Suc 0)"
value "parn 8"

thm "parn.simps"
thm "parn.induct"

fun pelomenosdois :: "nat \<Rightarrow> bool" where
"pelomenosdois (Suc(Suc _)) = True"|
"pelomenosdois _ = False"

thm "pelomenosdois.simps"

value "pelomenosdois 0"
value "pelomenosdois 2"
value "pelomenosdois 3"

(*funcao recursiva*)
primrec add::"nat \<Rightarrow> nat \<Rightarrow> nat" where
"add x 0 = x"|
"add x (Suc y) = Suc (add x y)"

value "add (Suc 0) (Suc (Suc 0))"
value "add 1 2"

thm "add.simps"

(*funcao recursiva*)
(*cuja definicao falha na prova automatica das obrigacoes*)
fun sum::"nat \<Rightarrow> nat \<Rightarrow> nat" where
"sum i n = (if i>n then 0 else i + sum (Suc i) n)"

end