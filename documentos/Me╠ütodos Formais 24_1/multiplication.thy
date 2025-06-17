theory multiplication
imports Main
begin

thm "nat.induct"

primrec mult :: "nat \<Rightarrow> nat \<Rightarrow> nat"
where
 mult01: "mult x 0 = 0" |
 mult02: "mult x (Suc y) = x + mult x y"

(* Propriedade 1: \<forall>x \<in> \<nat>. \<forall>y \<in> \<nat>: mult(x, y) = x * y  *)
theorem mult_prop_1: "\<forall>x::nat. mult x y = x * y"
proof (induction y)
show "\<forall>x. mult x 0 = x * 0"
by simp
next
fix y::nat
assume HI: "\<forall>x::nat. mult x y = x * y"
show "\<forall>x. mult x (Suc y) = x * Suc y"
by (simp add:HI)
qed


(* Propriedade 2: \<forall>x \<in> \<nat>. \<forall>y \<in> \<nat>: mult(x, y) = mult(y, x) *)
theorem mult_prop_2: "\<forall>x::nat. mult x y = mult y x"
proof (induction y)
show "\<forall>x. mult x 0 = mult 0 x"
proof(rule allI)
fix x0::nat
have "mult x0 0 = 0"
by (simp only:mult01)
also have "... = mult 0 x0"
by (simp only:mult_prop_1)
finally show "mult x0 0 = mult 0 x0"
by simp
qed
next
fix y::nat
assume HI: "\<forall>x::nat. mult x y = mult y x"
show "\<forall>x. mult x (Suc y) = mult (Suc y) x"
proof(rule allI)
fix x0::nat 
have "mult x0 (Suc y) = x0 + mult x0 y" by (simp only:mult02)
also have "... = mult y x0 + x0" by (simp only:HI)
also have "... = y * x0 + x0" by (simp only:mult_prop_1)
also have "... = (Suc y) * x0" by simp
also have "... = mult (Suc y) x0" by (simp only:mult_prop_1)
finally show "mult x0 (Suc y) = mult (Suc y) x0" by simp
qed
qed

(*Auxiliar para prop 3*)
theorem mult_add_prop: "\<forall>x y::nat. mult x (y + z) = mult x y + mult x z"
proof (induction z)
show "\<forall>x y. mult x (y + 0) = mult x y + mult x 0"
by simp
next
fix z0::nat
assume HI: "\<forall>x y. mult x (y + z0) = mult x y + mult x z0"
show "\<forall>x y. mult x (y + (Suc z0)) = mult x y + mult x (Suc z0)"
by (simp add:HI)
qed


(* Propriedade 3: \<forall>x \<in> \<nat>. \<forall>y \<in> \<nat>. \<forall>z \<in> \<nat>: mult(x, mult(y, z)) = mult(mult(x, y), z) *)
theorem mult_prop_3: "\<forall>x y::nat. mult x (mult y z) = mult (mult x y) z"
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
have "mult x0 (mult y0 (Suc z0)) = mult x0 (y0 + mult y0 z0)" by (simp only:mult02)
also have "... = mult x0 y0 + mult x0 (mult y0 z0)" by (simp only:mult_add_prop)
also have "... = mult x0 y0 + mult (mult x0 y0) z0" by (simp only:HI)
also have "... = mult (mult x0 y0) (Suc z0)" by (simp only:mult02)
finally show "mult x0 (mult y0 (Suc z0)) = mult (mult x0 y0) (Suc z0)" by simp
qed
qed
(* mult02: "mult x (Suc y) = x + mult x y"*)

end
