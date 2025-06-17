theory t1

imports Main
begin

thm "nat.induct"
(* Alunos: Laura Caetano, Arthur Amestere, Mathias Kauffmann *)
primrec soma::"nat \<Rightarrow> nat \<Rightarrow> nat" where
 soma01: "soma x 0 = x" |
 soma02: "soma x (Suc y) = Suc (soma x y)"

primrec mult::"nat \<Rightarrow> nat \<Rightarrow> nat" where
mult01: "mult x 0 = 0"|
mult02: "mult x (Suc y) = soma x (mult x y)"

(* Propriedade 1: \<forall>x \<in> \<nat>. \<forall>y \<in> \<nat>: mult(x, y) = x * y  *)

(*Auxiliar para prop 1*)
(*usando exemplo do exerciciosoma*)
theorem somav1:"soma x 0 = x"
  by (auto)

(*Auxiliar para prop 1*)
theorem somav2:"soma x 0 = x"
proof (induction x)
  show "soma 0 0 = 0" by (simp only: soma01)
next
  fix a::nat
  assume HI: "soma a 0 = a"
  show "soma (Suc a) 0 = Suc a" by (simp only: soma01)
qed

(*Auxiliar para prop 1*)
theorem somav3:"\<forall>x::nat. soma x y = x + y"
proof (induction y)
  show "\<forall>x::nat. soma x 0 = x + 0"
  proof (rule allI)
    fix a::nat
    have "soma a 0 = a" by (simp only: soma01)
    also have "... = a + 0" by (arith)
    finally show "soma a 0 = a + 0" by (simp)
  qed
next
  fix b::nat
  assume HI: "\<forall>x::nat. soma x b = x + b"
  show "\<forall>x::nat. soma x (Suc b) = x + Suc b"
  proof (rule allI)
    fix a::nat
    have "soma a (Suc b) = Suc (soma a b)" by (simp only: soma02)
    also have "... = Suc (a + b)" by (simp only: HI)
    also have "... = a + Suc b" by (arith)
    finally show "soma a (Suc b) = a + Suc b" by (simp)
  qed
qed

theorem prop_1: "\<forall>x::nat. mult x y = x * y"
proof (induction y)
  show "\<forall>x. mult x 0 = x * 0"
    by simp
next
  fix y::nat
  assume HI: "\<forall>x::nat. mult x y = x * y"
  show "\<forall>x. mult x (Suc y) = x * Suc y"
  proof (rule allI)
  fix z::nat
  have "mult z (Suc y) = soma z (mult z y)" by (simp only: mult02)
  also have "... =  z + (mult z y)" by (simp only:somav3)
  also have "... = z + (z *y)" by (simp only:HI)
  finally show "mult z (Suc y) = z * Suc y" by (simp)
  qed
qed

(* Propriedade 2: \<forall>x,y \<in> \<nat>.mult(x,y) = mult(y,x)  *)
theorem prop_2: "\<forall>x::nat. mult x y = mult y x"
proof (induction y)
show "\<forall>x. mult x 0 = mult 0 x"
proof(rule allI)
  fix x0::nat
  have "mult x0 0 = 0"
    by (simp only:mult01)
  also have "... = mult 0 x0"
    by (simp only:prop_1)
  finally show "mult x0 0 = mult 0 x0"
    by simp
qed
next
  fix y::nat
  assume HI: "\<forall>x::nat. mult x y = mult y x"
  show "\<forall>x. mult x (Suc y) = mult (Suc y) x"
  proof(rule allI)
  fix x0::nat 
  have "mult x0 (Suc y)= soma x0 (mult x0 y)"  by (simp only:mult02)
  also have "... = x0 + mult x0 y" by (simp only:somav3)
  also have "... = mult y x0 + x0" by (simp only:HI)
  also have "... = y * x0 + x0" by (simp only:prop_1)
  also have "... = (Suc y) * x0" by simp
  also have "... = mult (Suc y) x0" by (simp only:prop_1)
    finally show "mult x0 (Suc y) = mult (Suc y) x0" by simp
  qed
qed

(* Propriedade 3: \<forall>x \<in> \<nat>.mult(x,1) = x  *)
theorem prop_3: "\<forall>x::nat. mult x 1 = x"
proof
  fix x::nat
  have "mult x 1 = soma x (mult x 0)" using mult02 by simp
  also have "... = soma x 0" using mult01 by simp
  also have "... = x" using soma01 by simp
  finally show "mult x 1 = x" .
qed


(* Propriedade 4: \<forall>x \<in> \<nat>.mult(1,x) = x  *)
theorem prop_4: "\<forall>x::nat. mult 1 x = x"
proof
  fix x::nat
  show "mult 1 x = x"
  proof (induction x)
    show "mult 1 0 = 0" by (simp only: mult01)
  next
    fix y::nat
    assume HI: "mult 1 y = y"
    have "mult 1 (Suc y) = soma 1 (mult 1 y)" by (simp only: mult02)
    also have "... = 1 + y" by (simp only: somav3 HI)
    finally show "mult 1 (Suc y) = Suc y" by simp
  qed
qed


(* Propriedade 5: \<forall>x,y,z \<in> \<nat>.mult(x,mult(y,z)) = mult(mult(x,y),z)  *)
theorem prop_5: "\<forall>x y::nat. mult x (mult y z) = mult (mult x y) z"
proof (induction z)
  show "\<forall>x y. mult x (mult y 0) = mult (mult x y) 0"
  proof(rule allI, rule allI)
    fix x0::nat and y0::nat
    have "mult x0 (mult y0 0) = 0"
      by (simp only:mult01)
    also have "... = mult (mult x0 y0) 0"
      by (simp only:mult01)
    finally show "mult x0 (mult y0 0) = mult (mult x0 y0) 0"
      by simp
  qed
next
  fix z0::nat
  assume HI:"\<forall>x y. mult x (mult y z0) = mult (mult x y) z0"
  show "\<forall>x y. mult x (mult y (Suc z0)) = mult (mult x y)(Suc z0)"
  proof(rule allI, rule allI)
    fix x0::nat and y0::nat
    have "mult x0 (mult y0 (Suc z0)) = soma x0 (mult z0(mult x0 y0)) " by (simp only:mult02)
    qed
  qed
qed
(* alterar somente o pedaco da esquerda *)
ir abrindo e depois ir fechando
transformar em operacoes aritmeticas
precisa provar as anteriores para provar essa
(*mult02: "mult x (Suc y) = soma x (mult x y)"*)
(*mult01: "mult x 0 = 0*)
(*prop_2: mult(x,y) = mult(y,x)*)
(*using as reference provas.thy
proof(rule allI, rule allI)
fix x0::nat and y0::nat
have "add (add x0 y0)(Suc z0) = Suc(add (add x0 y0) z0)" by (simp only:add02)
also have "... = Suc(add x0 (add y0 z0))" by (simp only:HI)
also have "... = add x0 (Suc (add y0 z0))" by (simp only:add02)
also have "... = add x0 (add y0 (Suc z0))" by (simp only:add02)
finally show "add (add x0 y0)(Suc z0) = add x0 (add y0 (Suc z0))" by simp
qed
qed *)

end