theory exerciciosoma
  imports Main
begin

primrec soma::"nat \<Rightarrow> nat \<Rightarrow> nat" where
somaeq1: "soma x 0 = x" |
somaeq2: "soma x (Suc y) = Suc (soma x y)"

theorem somav1:"soma x 0 = x"
  by (auto)

theorem somav2:"soma x 0 = x"
proof (induction x)
  show "soma 0 0 = 0" by (simp only: somaeq1)
next
  fix a::nat
  assume HI: "soma a 0 = a"
  show "soma (Suc a) 0 = Suc a" by (simp only: somaeq1)
qed

theorem somav3:"\<forall>x::nat. soma x y = x + y"
proof (induction y)
  show "\<forall>x::nat. soma x 0 = x + 0"
  proof (rule allI)
    fix a::nat
    have "soma a 0 = a" by (simp only: somaeq1)
    also have "... = a + 0" by (arith)
    finally show "soma a 0 = a + 0" by (simp)
  qed
next
  fix b::nat
  assume HI: "\<forall>x::nat. soma x b = x + b"
  show "\<forall>x::nat. soma x (Suc b) = x + Suc b"
  proof (rule allI)
    fix a::nat
    have "soma a (Suc b) = Suc (soma a b)" by (simp only: somaeq2)
    also have "... = Suc (a + b)" by (simp only: HI)
    also have "... = a + Suc b" by (arith)
    finally show "soma a (Suc b) = a + Suc b" by (simp)
  qed
qed









end